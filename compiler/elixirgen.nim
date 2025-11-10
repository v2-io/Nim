# Nim Elixir Backend (JSON AST prototype)

import
  ast, types, modulegraphs, options, msgs, idents, lineinfos

import pipelineutils

import std/[strutils, sequtils, os, json]

when defined(nimPreviewSlimSystem):
  import std/syncio

const
  artifactVersion = 1

type
  TElixirGen = object of PPassContext
    module: PSym
    graph: ModuleGraph
    config: ConfigRef
    moduleName: string
    elixirModuleName: string
    sourcePath: string
    sourceDisplayPath: string
    projectDir: string
    forms: seq[JsonNode]
    moduleStmts: seq[JsonNode]  # Module-level statements for __sar_main__/0
    importedModules: seq[string]  # Elixir modules to alias (e.g., ["File", "Jason"])

  BModule = ref TElixirGen

# ---------------------------------------------------------------------------
# JSON helpers

proc jArray(nodes: seq[JsonNode]): JsonNode =
  result = newJArray()
  for node in nodes:
    result.add(node)

proc addAll(dest: var seq[JsonNode]; nodes: seq[JsonNode]) =
  for node in nodes:
    dest.add(node)

proc makeTuple(elems: seq[JsonNode]): JsonNode =
  result = newJObject()
  result["$tuple"] = jArray(elems)

template elixirTuple(args: varargs[JsonNode]): JsonNode =
  makeTuple(@args)

proc keyword(pairs: seq[(string, JsonNode)]): JsonNode =
  var arr = newJArray()
  for (key, value) in pairs:
    var pairObj = newJObject()
    pairObj["key"] = %* key
    pairObj["value"] = value
    arr.add(pairObj)
  result = newJObject()
  result["$keyword"] = arr

proc emptyKeyword(): JsonNode =
  keyword(@[])

proc atom(name: string): JsonNode =
  result = newJObject()
  result["$atom"] = %* name

proc list(nodes: seq[JsonNode]): JsonNode = jArray(nodes)

proc makeBlock(stmts: seq[JsonNode]): JsonNode =
  let body = if stmts.len > 0: stmts else: @[newJNull()]
  elixirTuple(atom("__block__"), emptyKeyword(), list(body))

# ---------------------------------------------------------------------------
# Naming helpers

proc toElixirModuleName(name: string): string =
  result = ""
  var capitalize = true
  for ch in name:
    if ch in {'_', '-', '.', ' '}:
      capitalize = true
    else:
      if capitalize:
        result.add(ch.toUpperAscii)
        capitalize = false
      else:
        result.add(ch.toLowerAscii)
  if result.len == 0:
    result = "SarModule"
  elif not result[0].isUpperAscii:
    result[0] = result[0].toUpperAscii

proc aliasSegments(name: string): seq[string] =
  if name.contains('.'):
    result = name.split('.')
  else:
    result = @[name]

# ---------------------------------------------------------------------------
# Metadata helpers

proc relativize(m: BModule; absPath: string): string =
  if absPath.len == 0:
    return absPath
  if m.projectDir.len == 0:
    return absPath
  try:
    result = relativePath(absPath, m.projectDir)
  except OSError:
    result = absPath

proc metaFromInfo(m: BModule; info: TLineInfo): JsonNode =
  var pairs: seq[(string, JsonNode)] = @[]
  if info.line.int > 0:
    pairs.add(("line", %* info.line.int))
  if info.col.int > 0:
    pairs.add(("column", %* info.col.int))
  let relPath = toFilename(m.config, info)
  let fileValue =
    if relPath.len > 0:
      relPath
    else:
      relativize(m, toFullPath(m.config, info))
  if fileValue.len > 0:
    pairs.add(("file", %* fileValue))
  keyword(pairs)

proc metaFromNode(m: BModule; n: PNode): JsonNode =
  if n.isNil:
    emptyKeyword()
  else:
    metaFromInfo(m, n.info)

# ---------------------------------------------------------------------------
# AST constructors

proc varNode(name: string): JsonNode =
  elixirTuple(atom(name), emptyKeyword(), atom("Elixir"))

proc callNode(m: BModule; name: string; args: seq[JsonNode]; origin: PNode): JsonNode =
  elixirTuple(atom(name), metaFromNode(m, origin), list(args))

proc opNode(m: BModule; op: string; args: seq[JsonNode]; origin: PNode): JsonNode =
  elixirTuple(atom(op), metaFromNode(m, origin), list(args))

# ---------------------------------------------------------------------------
# Expression translation

proc mapOperator(name: string): string =
  case name
  of "+", "-", "*", "/", "<", "<=", ">", ">=", "==", "!=": name
  of "&": "<>"
  of "mod": "rem"  # Nim mod → Elixir rem
  of "div": "div"  # Integer division
  of "and": "and"  # Logical and
  of "or": "or"    # Logical or
  else: name

proc translateExpr(m: BModule; n: PNode): JsonNode
proc translateStmt(m: BModule; node: PNode): seq[JsonNode]

proc translateIfExpr(m: BModule; node: PNode): JsonNode =
  if node.len == 0:
    return %* "# unsupported empty if"

  # Handle if/elif/else chains by nesting them
  proc buildIfChain(branches: seq[PNode]; startIdx: int): JsonNode =
    if startIdx >= branches.len:
      return newJNull()

    let branch = branches[startIdx]

    if branch.kind in {nkElifBranch, nkElifExpr} and branch.len >= 2:
      # elif or initial if branch
      let condition = translateExpr(m, branch[0])
      var thenStmts: seq[JsonNode] = @[]
      for i in 1 ..< branch.len:
        thenStmts.addAll(translateStmt(m, branch[i]))

      # Check if there are more branches
      let restChain = buildIfChain(branches, startIdx + 1)
      var clauses: seq[(string, JsonNode)] = @[("do", makeBlock(thenStmts))]
      if not restChain.isNil and restChain.kind != JNull:
        clauses.add(("else", restChain))

      elixirTuple(atom("if"), metaFromNode(m, branch), list(@[condition, keyword(clauses)]))

    elif branch.kind in {nkElse, nkElseExpr}:
      # else branch - return the block directly
      var elseStmts: seq[JsonNode] = @[]
      for child in branch:
        elseStmts.addAll(translateStmt(m, child))
      makeBlock(elseStmts)
    else:
      newJNull()

  var branches: seq[PNode] = @[]
  for i in 0 ..< node.len:
    branches.add(node[i])

  buildIfChain(branches, 0)

proc remoteCallNode(m: BModule; moduleName, funcName: string; args: seq[JsonNode]; origin: PNode): JsonNode =
  let aliasNode = elixirTuple(atom("__aliases__"), emptyKeyword(), list(@[atom(moduleName)]))
  let dotNode = elixirTuple(atom("."), emptyKeyword(), list(@[aliasNode, atom(funcName)]))
  elixirTuple(dotNode, metaFromNode(m, origin), list(args))

proc mapBuiltinFunction(name: string): (string, string) =
  ## Maps Nim built-in function names to (module, function) pairs
  ## Returns ("", "") if not a built-in
  case name
  of "len": ("Kernel", "length")
  of "min": ("Kernel", "min")
  of "max": ("Kernel", "max")
  of "abs": ("Kernel", "abs")
  of "contains": ("Enum", "member?")
  # String operations
  of "toUpperAscii", "toUpper": ("String", "upcase")
  of "toLowerAscii", "toLower": ("String", "downcase")
  of "strip": ("String", "trim")
  of "startsWith": ("String", "starts_with?")
  of "endsWith": ("String", "ends_with?")
  of "split": ("String", "split")
  of "join": ("Enum", "join")
  of "replace": ("String", "replace")
  # Special cases high/low handled separately in translateCall
  else: ("", "")

proc translateCall(m: BModule; n: PNode): JsonNode =
  if n.len == 0 or n[0].kind != nkSym or n[0].sym.isNil:
    return %* "# unsupported call"

  let name = n[0].sym.name.s
  var args: seq[JsonNode] = @[]
  for i in 1 ..< n.len:
    # Flatten varargs (nkBracket) nodes, including when wrapped in nkHiddenStdConv
    var argNode = n[i]
    # Unwrap hidden conversions to check for nkBracket
    if argNode.kind in {nkHiddenStdConv, nkHiddenCallConv, nkHiddenSubConv} and argNode.len > 1:
      argNode = argNode[1]

    if argNode.kind == nkBracket:
      # Flatten bracket (varargs) into individual args
      for child in argNode:
        args.add(translateExpr(m, child))
    else:
      # Regular arg
      args.add(translateExpr(m, n[i]))

  # Handle special commands
  case name
  of "echo":
    # echo maps to IO.puts with string coalescing
    if args.len == 0:
      return remoteCallNode(m, "IO", "puts", @[%* ""], n)
    elif args.len == 1:
      return remoteCallNode(m, "IO", "puts", args, n)
    else:
      # Multiple args: coalesce with Kernel.to_string
      var coalesced: seq[JsonNode] = @[]
      for arg in args:
        let toString = remoteCallNode(m, "Kernel", "to_string", @[arg], n)
        coalesced.add(toString)
      # Build string concatenation
      var result = coalesced[0]
      for i in 1 ..< coalesced.len:
        result = opNode(m, "<>", @[result, coalesced[i]], n)
      return remoteCallNode(m, "IO", "puts", @[result], n)
  of "inc":
    # inc(x, step) -> x = x + step
    if args.len >= 1:
      let target = args[0]
      let step = if args.len >= 2: args[1] else: %* 1
      return opNode(m, "=", @[target, opNode(m, "+", @[target, step], n)], n)
  of "dec":
    # dec(x, step) -> x = x - step
    if args.len >= 1:
      let target = args[0]
      let step = if args.len >= 2: args[1] else: %* 1
      return opNode(m, "=", @[target, opNode(m, "-", @[target, step], n)], n)
  of "high":
    # high(arr) -> length(arr) - 1
    if args.len >= 1:
      let lengthCall = remoteCallNode(m, "Kernel", "length", @[args[0]], n)
      return opNode(m, "-", @[lengthCall, %* 1], n)
  of "low":
    # low(arr) -> 0
    return %* 0
  of "sarAssert":
    # sarAssert(cond) → if not(cond), do: raise "Assertion failed"
    if args.len >= 1:
      let condition = args[0]
      let negatedCond = elixirTuple(atom("not"), metaFromNode(m, n), list(@[condition]))
      let raiseCall = remoteCallNode(m, "Kernel", "raise", @[%* "Assertion failed"], n)
      let ifKeyword = keyword(@[("do", raiseCall)])
      return elixirTuple(atom("if"), metaFromNode(m, n), list(@[negatedCond, ifKeyword]))
  of "sarAssertMsg":
    # sarAssertMsg(cond, msg) → if not(cond), do: raise "Assertion failed: #{msg}"
    if args.len >= 2:
      let condition = args[0]
      let message = args[1]
      let negatedCond = elixirTuple(atom("not"), metaFromNode(m, n), list(@[condition]))
      # Create interpolated string: "Assertion failed: " <> msg
      let prefix = %* "Assertion failed: "
      let interpolated = opNode(m, "<>", @[prefix, message], n)
      let raiseCall = remoteCallNode(m, "Kernel", "raise", @[interpolated], n)
      let ifKeyword = keyword(@[("do", raiseCall)])
      return elixirTuple(atom("if"), metaFromNode(m, n), list(@[negatedCond, ifKeyword]))
  else:
    # Check if this is a built-in function
    let (modName, funcName) = mapBuiltinFunction(name)
    if modName.len > 0:
      # Filter arguments for functions that need it
      # Nim passes default parameter values that Elixir functions don't accept
      var filteredArgs = args
      if modName == "String":
        case funcName
        of "trim", "upcase", "downcase":
          # Only pass the string argument
          if args.len > 0:
            filteredArgs = @[args[0]]
        of "starts_with?", "ends_with?", "split":
          # Pass first 2 arguments (string, pattern/suffix/delimiter)
          if args.len > 1:
            filteredArgs = @[args[0], args[1]]
        of "replace":
          # Pass first 3 arguments (string, old, new)
          if args.len > 2:
            filteredArgs = @[args[0], args[1], args[2]]
        else:
          discard
      elif modName == "Enum" and funcName == "join":
        # join takes (list, separator)
        if args.len > 1:
          filteredArgs = @[args[0], args[1]]
      return remoteCallNode(m, modName, funcName, filteredArgs, n)

  # Check for cross-module calls
  # When a function is imported from another module, its owner will be different
  let funcSym = n[0].sym
  if not funcSym.owner.isNil and funcSym.owner != m.module:
    # This is a cross-module call - generate remote call
    let moduleName = funcSym.owner.name.s
    # Capitalize module name for Elixir (math -> Math)
    let elixirModuleName = moduleName[0].toUpperAscii & moduleName[1..^1]
    return remoteCallNode(m, elixirModuleName, name, args, n)

  callNode(m, name, args, n)

proc translateInfix(m: BModule; n: PNode): JsonNode =
  if n.len < 3:
    return %* "# unsupported infix"

  let left = translateExpr(m, n[1])
  let right = translateExpr(m, n[2])
  var opName = "+"
  if n[0].kind == nkSym and not n[0].sym.isNil:
    opName = mapOperator(n[0].sym.name.s)
  elif n[0].kind == nkIdent:
    opName = mapOperator(n[0].ident.s)
  elif n[0].kind == nkOpenSymChoice:
    # Overloaded operator before resolution - use first choice
    if n[0].len > 0 and not n[0][0].sym.isNil:
      opName = mapOperator(n[0][0].sym.name.s)
  else:
    opName = "+"
  opNode(m, opName, @[left, right], n)

proc translateExpr(m: BModule; n: PNode): JsonNode =
  if n.isNil:
    return newJNull()

  case n.kind
  of nkIdent:
    # Identifier before semantic analysis (or in type annotations)
    # Just treat as a variable reference
    let name = n.ident.s
    if name == "true":
      %* true
    elif name == "false":
      %* false
    else:
      varNode(name)
  of nkSym:
    if n.sym.isNil:
      %* "# sym"
    else:
      let name = n.sym.name.s
      if name == "true":
        %* true
      elif name == "false":
        %* false
      elif n.sym.kind == skEnumField:
        # Enum field → atom (strip "atom" prefix)
        if name.startsWith("atom") and name.len > 4:
          let atomName = name[4..^1].toLowerAscii
          atom(atomName)
        else:
          atom(name.toLowerAscii)
      else:
        varNode(name)
  of nkIntLit..nkInt64Lit:
    %* n.intVal
  of nkUIntLit..nkUInt64Lit:
    %* n.intVal
  of nkFloatLit..nkFloat128Lit:
    %* n.floatVal
  of nkStrLit, nkTripleStrLit:
    %* n.strVal
  of nkCharLit:
    var s = newString(1)
    s[0] = char(n.intVal.int)
    %* s
  of nkNilLit:
    newJNull()
  of nkInfix:
    translateInfix(m, n)
  of nkCall, nkCommand:
    # nkCommand is like nkCall but for statements at module level
    translateCall(m, n)
  of nkIfExpr, nkIfStmt:
    translateIfExpr(m, n)
  of nkPar:
    # Tuples: (a, b) → {:{},[],[a,b]} or single element (a) → a (grouping)
    if n.len == 0:
      %* "# empty tuple"
    elif n.len == 1:
      # Single element in parens is just grouping
      translateExpr(m, n[0])
    else:
      # Multiple elements = tuple
      var elements: seq[JsonNode] = @[]
      for child in n:
        elements.add(translateExpr(m, child))
      elixirTuple(atom("{}"), metaFromNode(m, n), list(elements))
  of nkExprEqExpr, nkHiddenAddr, nkHiddenDeref:
    if n.len > 0: translateExpr(m, n[0]) else: %* "# empty"
  of nkHiddenStdConv, nkHiddenCallConv, nkHiddenSubConv:
    # Hidden conversions: child[0] is calling convention/type, child[1] is the actual expression
    if n.len > 1: translateExpr(m, n[1])
    elif n.len > 0: translateExpr(m, n[0])
    else: %* "# empty"
  of nkBracket:
    # List literal [a, b, c] → Elixir list
    var elements: seq[JsonNode] = @[]
    for child in n:
      elements.add(translateExpr(m, child))
    list(elements)
  of nkTupleConstr:
    # Tuple construction after semantic analysis (x, y) → {:{},[],[x,y]}
    var elements: seq[JsonNode] = @[]
    for child in n:
      if child.kind != nkEmpty:
        elements.add(translateExpr(m, child))
    elixirTuple(atom("{}"), metaFromNode(m, n), list(elements))
  of nkObjConstr:
    # Object construction → Elixir map: Point(x: 1, y: 2) → %{x: 1, y: 2}
    var pairs: seq[(string, JsonNode)] = @[]
    # First child is the type, rest are field assignments
    for i in 1 ..< n.len:
      let fieldNode = n[i]
      if fieldNode.kind == nkExprColonExpr and fieldNode.len >= 2:
        let fieldName =
          if fieldNode[0].kind == nkSym and not fieldNode[0].sym.isNil:
            fieldNode[0].sym.name.s
          else:
            "field"
        let fieldValue = translateExpr(m, fieldNode[1])
        pairs.add((fieldName, fieldValue))
    # Generate %{...} map structure
    var mapPairs: seq[JsonNode] = @[]
    for (key, value) in pairs:
      let keyAtom = atom(key)
      let pairTuple = elixirTuple(keyAtom, value)
      mapPairs.add(pairTuple)
    elixirTuple(atom("%{}"), metaFromNode(m, n), list(mapPairs))
  of nkDotExpr:
    # Field access: obj.field → Map.get(obj, :field)
    if n.len >= 2:
      let obj = translateExpr(m, n[0])
      let fieldName =
        if n[1].kind == nkSym and not n[1].sym.isNil:
          n[1].sym.name.s
        else:
          "field"
      let fieldAtom = atom(fieldName)
      remoteCallNode(m, "Map", "get", @[obj, fieldAtom], n)
    else:
      %* "# invalid dot expression"
  of nkEmpty:
    # Empty nodes should return null instead of unsupported warnings
    newJNull()
  of nkAsgn:
    # Assignment as expression: x = value (returns value in Elixir)
    # This handles cases where assignment appears in expression context
    if n.len >= 2:
      let target = n[0]
      let value = translateExpr(m, n[1])
      # In Elixir, assignment is an expression that returns the value
      # Generate: (var = value) which is the pattern match form
      if target.kind == nkSym and not target.sym.isNil:
        let varName = target.sym.name.s
        opNode(m, "=", @[varNode(varName), value], n)
      else:
        %* "# unsupported nkAsgn target"
    else:
      %* "# invalid nkAsgn"
  of nkStmtListExpr:
    # Statement list as expression (e.g., in let bindings or block returns)
    # Last statement is the value, earlier statements are for side effects
    var stmts: seq[JsonNode] = @[]
    for child in n:
      stmts.addAll(translateStmt(m, child))
    makeBlock(stmts)
  of nkBlockExpr, nkBlockStmt:
    # Block expressions: block: stmts or block label: stmts → __block__
    # Labels are ignored (Elixir doesn't have labeled blocks)
    let bodyNode =
      if n.len == 1:
        # Unlabeled block: child[0] is body
        n[0]
      elif n.len == 2:
        # Labeled block: child[0] is label, child[1] is body
        n[1]
      else:
        # Shouldn't happen, but handle gracefully
        n[n.len - 1]
    let bodyStatements = translateStmt(m, bodyNode)
    makeBlock(bodyStatements)
  of nkRange:
    # Range expression: a..b → Elixir range start..end
    if n.len >= 2:
      let start = translateExpr(m, n[0])
      let endVal = translateExpr(m, n[1])
      # Elixir range: {:.., [], [start, end]}
      elixirTuple(atom(".."), metaFromNode(m, n), list(@[start, endVal]))
    else:
      %* "# invalid range"
  of nkBracketExpr:
    # Array/list/tuple indexing: arr[index]
    # Tuples use elem(tuple, index), lists use Enum.at(list, index)
    if n.len >= 2:
      let container = translateExpr(m, n[0])
      let index = translateExpr(m, n[1])
      # Check if container is a tuple type
      if not n[0].typ.isNil and n[0].typ.kind == tyTuple:
        # Tuple indexing: elem(tuple, index)
        remoteCallNode(m, "Kernel", "elem", @[container, index], n)
      else:
        # List/array indexing: Enum.at(list, index)
        remoteCallNode(m, "Enum", "at", @[container, index], n)
    else:
      %* "# invalid bracket expression"
  of nkPrefix:
    # Prefix operators: not x → not(x)
    if n.len >= 2:
      let op = n[0]
      let operand = translateExpr(m, n[1])
      if op.kind == nkSym and not op.sym.isNil:
        let opName = op.sym.name.s
        if opName == "not":
          # Unary not operator
          elixirTuple(atom("not"), metaFromNode(m, n), list(@[operand]))
        else:
          # Other prefix operators
          opNode(m, opName, @[operand], n)
      else:
        %* "# unsupported prefix operator"
    else:
      %* "# invalid prefix expression"
  of nkLambda, nkDo:
    # Anonymous function: proc(x: int): int = x + 1 → fn x -> x + 1 end
    let paramsNode = n[paramsPos]
    var params: seq[JsonNode] = @[]
    for i in 1 ..< paramsNode.len:
      let identDef = paramsNode[i]
      if identDef.kind == nkIdentDefs:
        for j in 0 ..< identDef.len - 2:  # -2 to skip type and default value
          if identDef[j].kind == nkSym and identDef[j].sym.kind == skParam:
            # Inline parameter node construction
            params.add(elixirTuple(atom(identDef[j].sym.name.s), emptyKeyword(), atom("Elixir")))
    let bodyNode = n[bodyPos]
    let bodyStatements = translateStmt(m, bodyNode)
    let bodyExpr = makeBlock(bodyStatements)
    # Elixir fn: {:fn, [], [{:->, [], [[params], body]}]}
    let arrow = elixirTuple(atom("->"), metaFromNode(m, n),
                            list(@[list(params), bodyExpr]))
    elixirTuple(atom("fn"), metaFromNode(m, n), list(@[arrow]))
  else:
    %* ("# unsupported " & $n.kind)

# ---------------------------------------------------------------------------
# Statement translation

proc translateAssignment(m: BModule; stmt: PNode): seq[JsonNode] =
  result = @[]
  if stmt.len < 2:
    result.add(%* ("# unsupported assignment: " & $stmt.kind))
    return

  let target = stmt[0]
  let expr = stmt[1]
  if target.kind == nkSym and not target.sym.isNil and target.sym.name.s == "result":
    result.add(translateExpr(m, expr))
  else:
    let lhs = translateExpr(m, target)
    let rhs = translateExpr(m, expr)
    result.add(opNode(m, "=", @[lhs, rhs], stmt))

proc translateStmt(m: BModule; node: PNode): seq[JsonNode] =
  result = @[]
  case node.kind
  of nkStmtList:
    for child in node:
      result.addAll(translateStmt(m, child))
  of nkStmtListExpr:
    # Statement list as expression in statement context (function bodies with blocks)
    for child in node:
      result.addAll(translateStmt(m, child))
  of nkEmpty:
    # Empty statements - do nothing
    discard
  of nkBlockExpr, nkBlockStmt:
    # Block statements - translate body
    let bodyNode =
      if node.len == 1:
        node[0]
      elif node.len == 2:
        node[1]  # Labeled block, skip label
      else:
        node[node.len - 1]
    result.addAll(translateStmt(m, bodyNode))
  of nkAsgn:
    result.addAll(translateAssignment(m, node))
  of nkIfStmt:
    result.add(translateIfExpr(m, node))
  of nkCall, nkCommand:
    # Commands and calls at statement level
    result.add(translateCall(m, node))
  of nkLetSection, nkVarSection:
    # Handle let/var bindings: let x = 5 or var y = 10
    # Note: Nim's semantic analysis converts `let (a, b) = tup` into separate
    # assignments using tmpTuple and nkBracketExpr, which we translate to Enum.at().
    # This is correct but not optimal - future optimization could detect this pattern
    # and generate Elixir pattern matching: {a, b} = tup
    for child in node:
      if child.kind == nkIdentDefs and child.len >= 3:
        # child[0] is the identifier, child[^2] is the type, child[^1] is the value
        let nameNode = child[0]
        let valueNode = child[^1]
        if nameNode.kind == nkSym and not nameNode.sym.isNil:
          let varName = nameNode.sym.name.s
          let value = translateExpr(m, valueNode)
          result.add(opNode(m, "=", @[varNode(varName), value], child))
  of nkReturnStmt:
    # Explicit return statement
    if node.len > 0 and node[0].kind != nkEmpty:
      result.add(translateExpr(m, node[0]))
  of nkDiscardStmt:
    # Discard statement: discard expr OR just discard
    # In Elixir, we translate the expression but don't use the result
    # For bare 'discard', we do nothing (it's a no-op)
    if node.len > 0 and node[0].kind != nkEmpty:
      # discard expr - evaluate the expression (may have side effects) but ignore result
      result.add(translateExpr(m, node[0]))
    # else: bare 'discard' - no-op, add nothing
  of nkCaseStmt:
    # Case statement: case x of 0: ... of 1: ... else: ...
    if node.len < 2:
      result.add(%* "# unsupported case")
    else:
      let selector = translateExpr(m, node[0])
      var clauses: seq[JsonNode] = @[]

      for i in 1 ..< node.len:
        let branch = node[i]
        case branch.kind
        of nkOfBranch:
          # Pattern branch: of value: body
          if branch.len >= 2:
            # branch[0..<^1] are patterns, branch[^1] is body
            for j in 0 ..< branch.len - 1:
              let pattern = translateExpr(m, branch[j])
              var bodyStmts: seq[JsonNode] = @[]
              bodyStmts.addAll(translateStmt(m, branch[^1]))
              let arrow = elixirTuple(atom("->"), emptyKeyword(),
                                     list(@[list(@[pattern]), makeBlock(bodyStmts)]))
              clauses.add(arrow)
        of nkElse:
          # Else branch with catch-all pattern
          var bodyStmts: seq[JsonNode] = @[]
          for child in branch:
            bodyStmts.addAll(translateStmt(m, child))
          let catchAll = varNode("_")
          let arrow = elixirTuple(atom("->"), emptyKeyword(),
                                 list(@[list(@[catchAll]), makeBlock(bodyStmts)]))
          clauses.add(arrow)
        else:
          discard

      let caseNode = elixirTuple(atom("case"), metaFromNode(m, node),
                                list(@[selector, keyword(@[("do", list(clauses))])]))
      result.add(caseNode)
  of nkWhileStmt:
    # While loops are NOT SUPPORTED in Elixir backend
    # Reason: Elixir's immutable variables break closure-based while loop helpers
    # Workaround: Use recursion or Enum functions instead
    result.add(%* "# ERROR: while loops not supported - use recursion or Enum functions")
  of nkImportStmt:
    # Import statement: import Elixir.File, Elixir.Jason
    # Extract module names and add to importedModules for alias generation
    for i in 0 ..< node.len:
      let importNode = node[i]
      # Handle different import forms:
      # - Simple: import File (nkIdent)
      # - Qualified: import Elixir.File (nkInfix with ".")
      if importNode.kind == nkInfix:
        # Check if it's "Elixir.ModuleName" pattern
        if importNode.len >= 3 and importNode[0].kind == nkSym:
          let op = importNode[0].sym.name.s
          if op == ".":
            # Get the module name (rightmost part)
            if importNode[2].kind == nkIdent:
              let moduleName = importNode[2].ident.s
              # Only add Elixir.* imports
              if importNode[1].kind == nkIdent and importNode[1].ident.s == "Elixir":
                if moduleName notin m.importedModules:
                  m.importedModules.add(moduleName)
      # For now, emit comment in generated code (imports handled via alias)
      result.add(%* ("# import processed: " & $importNode.kind))
  of nkCommentStmt:
    discard
  of nkInfix:
    # Infix expressions in statement context (e.g., last expr in block)
    result.add(translateInfix(m, node))
  of nkPrefix:
    # Prefix expressions in statement context
    if node.len >= 2:
      let op = node[0]
      let operand = translateExpr(m, node[1])
      if op.kind == nkSym and not op.sym.isNil:
        let opName = op.sym.name.s
        if opName == "not":
          result.add(elixirTuple(atom("not"), metaFromNode(m, node), list(@[operand])))
        else:
          result.add(opNode(m, opName, @[operand], node))
      else:
        result.add(%* "# unsupported prefix operator")
    else:
      result.add(%* "# invalid prefix expression")
  of nkTryStmt:
    # Try/except/finally → try/rescue/after
    # node[0]: try body
    # node[1..n]: except branches (nkExceptBranch) and/or finally (nkFinally)
    var tryBody: seq[JsonNode] = @[]
    var rescueClauses: seq[JsonNode] = @[]
    var afterBody: seq[JsonNode] = @[]

    # Extract try body
    if node.len > 0:
      tryBody = translateStmt(m, node[0])

    # Process except/finally branches
    for i in 1 ..< node.len:
      case node[i].kind
      of nkExceptBranch:
        # Except branch: except: body
        # Create rescue clause with error variable pattern
        var exceptBody: seq[JsonNode] = @[]
        for j in 0 ..< node[i].len:
          exceptBody.addAll(translateStmt(m, node[i][j]))

        # Create rescue clause: error -> body
        # Pattern is a variable that catches the exception
        let errorVar = elixirTuple(atom("error"), emptyKeyword(), atom("Elixir"))
        let arrow = elixirTuple(atom("->"), emptyKeyword(),
                               list(@[list(@[errorVar]), makeBlock(exceptBody)]))
        rescueClauses.add(arrow)
      of nkFinally:
        # Finally branch: finally: body
        if node[i].len > 0:
          afterBody = translateStmt(m, node[i][0])
      else:
        discard

    # Build try expression with do/rescue/after keyword list
    var tryParts: seq[(string, JsonNode)] = @[]
    tryParts.add(("do", makeBlock(tryBody)))

    if rescueClauses.len > 0:
      tryParts.add(("rescue", list(rescueClauses)))

    if afterBody.len > 0:
      tryParts.add(("after", makeBlock(afterBody)))

    let tryExpr = elixirTuple(atom("try"), metaFromNode(m, node),
                             list(@[keyword(tryParts)]))
    result.add(tryExpr)
  of nkTupleConstr, nkPar:
    # Tuple/parenthesized expressions in statement context (e.g., return values)
    result.add(translateExpr(m, node))
  of nkIdent, nkSym, nkIntLit..nkInt64Lit, nkUIntLit..nkUInt64Lit,
     nkFloatLit..nkFloat128Lit, nkStrLit, nkTripleStrLit, nkCharLit,
     nkNilLit:
    # Literal expressions in statement context
    result.add(translateExpr(m, node))
  else:
    result.add(%* ("# unsupported node: " & $node.kind))

# ---------------------------------------------------------------------------
# Procedure generation

proc buildParam(name: string): JsonNode =
  elixirTuple(atom(name), emptyKeyword(), atom("Elixir"))

proc tryGenerateMultipleClauses(m: BModule; procNode: PNode): bool =
  ## Try to generate multiple function clauses when the body is a single case statement on a parameter.
  ## Returns true if successful, false if normal single-clause generation should be used.

  let procSym = procNode[namePos].sym
  if procSym.isNil:
    return false

  let procName = procSym.name.s
  let paramsNode = procNode[paramsPos]
  let bodyNode = procNode[bodyPos]

  # Collect parameter names
  var paramNames: seq[string] = @[]
  for i in 1 ..< paramsNode.len:
    let identDef = paramsNode[i]
    if identDef.kind != nkIdentDefs:
      continue
    for child in identDef:
      if child.kind == nkSym and child.sym.kind == skParam:
        paramNames.add(child.sym.name.s)

  # Try to extract a case statement from the body
  var caseStmt: PNode = nil

  # Check if body is nkStmtList with single case statement
  if bodyNode.kind == nkStmtList and bodyNode.len == 1:
    if bodyNode[0].kind == nkCaseStmt:
      caseStmt = bodyNode[0]

  # Check if body is nkAsgn (result = case ...)
  elif bodyNode.kind == nkAsgn and bodyNode.len >= 2:
    if bodyNode[1].kind == nkCaseStmt:
      caseStmt = bodyNode[1]

  # If no case statement found, use normal generation
  if caseStmt.isNil or caseStmt.len < 2:
    return false

  # Check if case selector is a parameter
  let selectorNode = caseStmt[0]
  var paramIndex = -1
  if selectorNode.kind == nkSym and not selectorNode.sym.isNil:
    let selectorName = selectorNode.sym.name.s
    for i, pname in paramNames:
      if pname == selectorName:
        paramIndex = i
        break

  # If selector is not a parameter, use normal generation
  if paramIndex < 0:
    return false

  # Generate multiple clauses!
  for branchIdx in 1 ..< caseStmt.len:
    let branch = caseStmt[branchIdx]

    case branch.kind
    of nkOfBranch:
      # Pattern branch: of value: body
      if branch.len >= 2:
        # Each pattern becomes a separate clause
        for patIdx in 0 ..< branch.len - 1:
          var params: seq[JsonNode] = @[]
          for i, pname in paramNames:
            if i == paramIndex:
              # This parameter position gets the pattern
              let pattern = translateExpr(m, branch[patIdx])
              params.add(pattern)
            else:
              # Other parameters stay as variables
              params.add(buildParam(pname))

          # Translate body
          let bodyNode = branch[^1]
          let blockNode =
            if bodyNode.kind in {nkIntLit, nkFloatLit, nkStrLit, nkSym, nkCall, nkInfix, nkPrefix}:
              # Single expression - translate as expression
              translateExpr(m, bodyNode)
            else:
              # Multiple statements - translate as statement list
              let bodyStatements = translateStmt(m, bodyNode)
              makeBlock(bodyStatements)
          let fnHead = elixirTuple(atom(procName), emptyKeyword(), list(params))
          let fnKeyword = keyword(@[("do", blockNode)])
          let defNode = elixirTuple(atom("def"), metaFromNode(m, procNode), list(@[fnHead, fnKeyword]))
          m.forms.add(defNode)

    of nkElse:
      # Else branch: use catch-all variable in parameter position
      var params: seq[JsonNode] = @[]
      for i, pname in paramNames:
        if i == paramIndex:
          # Use the original parameter name as catch-all
          params.add(buildParam(pname))
        else:
          params.add(buildParam(pname))

      # Translate body
      var bodyStatements: seq[JsonNode] = @[]
      for child in branch:
        bodyStatements.addAll(translateStmt(m, child))
      let blockNode =
        if bodyStatements.len == 1:
          # Single statement/expression - return as-is
          bodyStatements[0]
        else:
          # Multiple statements - wrap in block
          makeBlock(bodyStatements)
      let fnHead = elixirTuple(atom(procName), emptyKeyword(), list(params))
      let fnKeyword = keyword(@[("do", blockNode)])
      let defNode = elixirTuple(atom("def"), metaFromNode(m, procNode), list(@[fnHead, fnKeyword]))
      m.forms.add(defNode)

    else:
      discard

  return true

proc getElixirPragma(procNode: PNode): string =
  ## Check if proc has {.elixir: "Module.function".} pragma and return the value
  ## Returns empty string if no elixir pragma found
  if procNode.len <= pragmasPos:
    return ""

  let pragmaNode = procNode[pragmasPos]
  if pragmaNode.kind == nkEmpty or pragmaNode.kind != nkPragma:
    return ""

  # Search through pragma list for "elixir" pragma
  for pragma in pragmaNode:
    if pragma.kind == nkExprColonExpr and pragma.len >= 2:
      # pragma[0] is the pragma name, pragma[1] is the value
      if pragma[0].kind == nkIdent and pragma[0].ident.s == "elixir":
        # Extract string literal value
        if pragma[1].kind == nkStrLit:
          return pragma[1].strVal

  return ""

proc parseElixirCall(callSpec: string): (string, string) =
  ## Parse "Module.function" into (module, function) tuple
  ## e.g., "File.read!" → ("File", "read!")
  let parts = callSpec.split('.')
  if parts.len == 2:
    return (parts[0], parts[1])
  elif parts.len == 1:
    return ("", parts[0])  # Just function name, no module
  else:
    # Handle multi-part modules like "Elixir.File.read!"
    if parts.len > 2:
      return (parts[0 .. ^2].join("."), parts[^1])
    return ("", "")

proc genElixirWrapperProc(m: BModule; procNode: PNode; elixirCall: string) =
  ## Generate a wrapper function that calls an Elixir function
  ## e.g., proc read_file(path: string): string {.elixir: "File.read!".}
  ## becomes: def read_file(path), do: File.read!(path)

  let procSym = procNode[namePos].sym
  if procSym.isNil:
    return

  let procName = procSym.name.s

  # Extract parameters
  let paramsNode = procNode[paramsPos]
  var params: seq[JsonNode] = @[]
  var paramNames: seq[string] = @[]
  for i in 1 ..< paramsNode.len:
    let identDef = paramsNode[i]
    if identDef.kind != nkIdentDefs:
      continue
    for child in identDef:
      if child.kind == nkSym and child.sym.kind == skParam:
        let paramName = child.sym.name.s
        params.add(buildParam(paramName))
        paramNames.add(paramName)

  # Parse Elixir function call
  let (moduleName, functionName) = parseElixirCall(elixirCall)

  # Build the remote call: Module.function(args...)
  var callArgs: seq[JsonNode] = @[]
  for paramName in paramNames:
    callArgs.add(buildParam(paramName))

  let callNode = if moduleName.len > 0:
    remoteCallNode(m, moduleName, functionName, callArgs, procNode)
  else:
    # Local function call (no module)
    let fnAtom = atom(functionName)
    elixirTuple(fnAtom, metaFromNode(m, procNode), list(callArgs))

  # Generate: def procName(params), do: Module.function(params)
  let fnHead = elixirTuple(atom(procName), emptyKeyword(), list(params))
  let fnKeyword = keyword(@[("do", callNode)])
  let defNode = elixirTuple(atom("def"), metaFromNode(m, procNode), list(@[fnHead, fnKeyword]))
  m.forms.add(defNode)

proc genProc(m: BModule; procNode: PNode) =
  # Check for {.elixir: "Module.function".} pragma first
  let elixirCall = getElixirPragma(procNode)
  if elixirCall.len > 0:
    genElixirWrapperProc(m, procNode, elixirCall)
    return  # Wrapper generated, we're done

  # Try to generate multiple clauses from case-on-parameter pattern
  if tryGenerateMultipleClauses(m, procNode):
    return  # Multiple clauses generated, we're done

  # Normal single-clause generation
  let procSym = procNode[namePos].sym
  if procSym.isNil:
    return

  let procName = procSym.name.s
  let paramsNode = procNode[paramsPos]
  var params: seq[JsonNode] = @[]
  for i in 1 ..< paramsNode.len:
    let identDef = paramsNode[i]
    if identDef.kind != nkIdentDefs:
      continue
    for child in identDef:
      if child.kind == nkSym and child.sym.kind == skParam:
        params.add(buildParam(child.sym.name.s))

  let bodyNode = procNode[bodyPos]
  let bodyStatements = translateStmt(m, bodyNode)
  let blockNode = makeBlock(bodyStatements)
  let fnHead = elixirTuple(atom(procName), emptyKeyword(), list(params))
  let fnKeyword = keyword(@[("do", blockNode)])

  let defNode = elixirTuple(atom("def"), metaFromNode(m, procNode), list(@[fnHead, fnKeyword]))
  m.forms.add(defNode)

# ---------------------------------------------------------------------------
# Module assembly

proc moduleAst(m: BModule): JsonNode =
  let aliasList = aliasSegments(m.elixirModuleName).mapIt(atom(it))
  let aliasNode = elixirTuple(atom("__aliases__"), emptyKeyword(), list(aliasList))

  # Generate alias statements for imported Elixir modules
  var allForms: seq[JsonNode] = @[]
  for moduleName in m.importedModules:
    # Generate: alias Elixir.ModuleName
    let elixirAlias = @[atom("Elixir"), atom(moduleName)]
    let elixirAliasNode = elixirTuple(atom("__aliases__"), emptyKeyword(), list(elixirAlias))
    let aliasStmt = elixirTuple(atom("alias"), emptyKeyword(), list(@[elixirAliasNode]))
    allForms.add(aliasStmt)

  # Add the rest of the module forms (functions, etc.)
  allForms.addAll(m.forms)

  let blockNode = makeBlock(allForms)
  let kw = keyword(@[("do", blockNode)])
  var moduleMetaPairs: seq[(string, JsonNode)] = @[]
  if m.sourceDisplayPath.len > 0:
    moduleMetaPairs.add(("file", %* m.sourceDisplayPath))
  elixirTuple(atom("defmodule"), keyword(moduleMetaPairs), list(@[aliasNode, kw]))

proc writeArtifact(m: BModule) =
  let moduleNode = moduleAst(m)
  let artifact = %* {
    "version": artifactVersion,
    "module": m.elixirModuleName,
    "sar_file": m.sourceDisplayPath,
    "quoted": moduleNode
  }

  let baseDir = getNimcacheDir(m.config)
  let outDirPath = joinPath(baseDir.string, "elixir")
  createDir(outDirPath)
  let outFilePath = joinPath(outDirPath, m.elixirModuleName & ".elixir_ast.json")
  try:
    writeFile(outFilePath, pretty(artifact, 2) & "\n")
  except IOError:
    rawMessage(m.config, errCannotOpenFile, outFilePath)

# ---------------------------------------------------------------------------
# Pipeline hooks

proc setupElixirgen*(graph: ModuleGraph; module: PSym; idgen: IdGenerator): PPassContext =
  result = BModule(module: module, graph: graph, config: graph.config)
  result.idgen = idgen
  let rawName = if module != nil: module.name.s else: graph.config.projectName
  let sourcePath = if module != nil: toFullPath(graph.config, module.info) else: graph.config.projectFull.string
  let projectDir = parentDir(graph.config.projectFull.string)
  var displayPath = sourcePath
  if projectDir.len > 0 and sourcePath.len > 0:
    try:
      displayPath = relativePath(sourcePath, projectDir)
    except OSError:
      discard
  BModule(result).moduleName = rawName
  BModule(result).elixirModuleName = toElixirModuleName(rawName)
  BModule(result).sourcePath = sourcePath
  BModule(result).sourceDisplayPath = displayPath
  BModule(result).projectDir = projectDir
  BModule(result).importedModules = @[]  # Initialize empty list of imported modules

proc processTypeSection(m: BModule; typeSection: PNode) =
  ## Process type section to detect {.elixirModule.} pragma
  ## Extracts type names and adds them to importedModules for alias generation
  for typeDef in typeSection:
    if typeDef.kind == nkTypeDef and typeDef.len >= 3:
      # typeDef[0] is the type name (possibly with pragma)
      # typeDef[1] is generic params (if any)
      # typeDef[2] is the type definition

      let nameNode = typeDef[0]
      var typeName = ""
      var hasElixirModulePragma = false

      # Extract type name and check for pragma
      if nameNode.kind == nkPragmaExpr and nameNode.len >= 2:
        # Type has pragma: TypeName {.pragma.}
        # nameNode[0] is the name, nameNode[1] is the pragma list
        if nameNode[0].kind == nkPostfix and nameNode[0].len >= 2:
          # Exported type: TypeName*
          if nameNode[0][1].kind == nkIdent:
            typeName = nameNode[0][1].ident.s
          elif nameNode[0][1].kind == nkSym:
            # Symbol node instead of ident (after semantic analysis)
            typeName = nameNode[0][1].sym.name.s
        elif nameNode[0].kind == nkIdent:
          typeName = nameNode[0].ident.s
        elif nameNode[0].kind == nkSym:
          # Symbol node (after semantic analysis)
          typeName = nameNode[0].sym.name.s

        # Check pragma list for elixirModule
        let pragmaList = nameNode[1]
        if pragmaList.kind == nkPragma:
          for pragma in pragmaList:
            if pragma.kind == nkIdent and pragma.ident.s == "elixirModule":
              hasElixirModulePragma = true
              break

      # If we found elixirModule pragma, add to importedModules
      if hasElixirModulePragma and typeName.len > 0:
        if typeName notin m.importedModules:
          m.importedModules.add(typeName)

proc processElixirCodeGen*(b: PPassContext, n: PNode): PNode =
  if b.isNil:
    return n
  let m = BModule(b)
  if m.module.isNil or sfMainModule notin m.module.flags:
    return n

  case n.kind
  of nkStmtList:
    for child in n:
      if child.kind == nkProcDef:
        genProc(m, child)
      elif child.kind == nkTypeSection:
        # Process type section to detect {.elixirModule.} pragmas
        processTypeSection(m, child)
      else:
        # Collect non-proc module-level statements for __sar_main__/0
        let stmts = translateStmt(m, child)
        m.moduleStmts.addAll(stmts)
  of nkProcDef:
    genProc(m, n)
  of nkTypeSection:
    # Process type section to detect {.elixirModule.} pragmas
    processTypeSection(m, n)
  else:
    # Collect non-proc module-level statements
    let stmts = translateStmt(m, n)
    m.moduleStmts.addAll(stmts)
  result = n

proc finalElixirCodeGen*(graph: ModuleGraph; b: PPassContext, n: PNode): PNode =
  result = n
  if b.isNil:
    return n

  let m = BModule(b)
  if m.module.isNil or sfMainModule notin m.module.flags:
    return n

  if pipelineutils.skipCodegen(m.config, n):
    return n

  # Generate __sar_main__/0 if there are module-level statements
  if m.moduleStmts.len > 0:
    let blockNode = makeBlock(m.moduleStmts)
    let fnHead = elixirTuple(atom("__sar_main__"), emptyKeyword(), list(@[]))
    let fnKeyword = keyword(@[("do", blockNode)])
    let defNode = elixirTuple(atom("def"), emptyKeyword(), list(@[fnHead, fnKeyword]))
    m.forms.add(defNode)

  if m.forms.len == 0:
    m.forms.add(%* "# module has no translated procedures")

  m.writeArtifact()
  result = n
