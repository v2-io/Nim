# Nim Elixir Backend (JSON AST prototype)

import
  ast, modulegraphs, options, msgs, idents, lineinfos

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

    if branch.kind == nkElifBranch and branch.len >= 2:
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

    elif branch.kind == nkElse:
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
    # Flatten varargs (nkBracket) nodes
    if n[i].kind == nkBracket:
      for child in n[i]:
        args.add(translateExpr(m, child))
    else:
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

  callNode(m, name, args, n)

proc translateInfix(m: BModule; n: PNode): JsonNode =
  if n.len < 3:
    return %* "# unsupported infix"

  let left = translateExpr(m, n[1])
  let right = translateExpr(m, n[2])
  var opName = "+"
  if n[0].kind == nkSym and not n[0].sym.isNil:
    opName = mapOperator(n[0].sym.name.s)
  else:
    opName = "+"
  opNode(m, opName, @[left, right], n)

proc translateExpr(m: BModule; n: PNode): JsonNode =
  if n.isNil:
    return newJNull()

  case n.kind
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
  of nkBracketExpr:
    # Array/list indexing: arr[index] → Enum.at(arr, index)
    if n.len >= 2:
      let container = translateExpr(m, n[0])
      let index = translateExpr(m, n[1])
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
  else:
    result.add(%* ("# unsupported node: " & $node.kind))

# ---------------------------------------------------------------------------
# Procedure generation

proc buildParam(name: string): JsonNode =
  elixirTuple(atom(name), emptyKeyword(), atom("Elixir"))

proc genProc(m: BModule; procNode: PNode) =
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
  let blockNode = makeBlock(m.forms)
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
      else:
        # Collect non-proc module-level statements for __sar_main__/0
        let stmts = translateStmt(m, child)
        m.moduleStmts.addAll(stmts)
  of nkProcDef:
    genProc(m, n)
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
