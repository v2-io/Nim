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
  else: name

proc translateExpr(m: BModule; n: PNode): JsonNode
proc translateStmt(m: BModule; node: PNode): seq[JsonNode]

proc translateIfExpr(m: BModule; node: PNode): JsonNode =
  if node.len == 0:
    return %* "# unsupported empty if"

  let firstBranch = node[0]
  if firstBranch.kind != nkElifBranch or firstBranch.len < 2:
    return %* "# unsupported if structure"

  let condition = translateExpr(m, firstBranch[0])
  var thenStmts: seq[JsonNode] = @[]
  for i in 1 ..< firstBranch.len:
    thenStmts.addAll(translateStmt(m, firstBranch[i]))

  var elseStmts: seq[JsonNode] = @[]
  for branch in node:
    if branch.kind == nkElse:
      for child in branch:
        elseStmts.addAll(translateStmt(m, child))

  var clauses: seq[(string, JsonNode)] = @[("do", makeBlock(thenStmts))]
  if elseStmts.len > 0:
    clauses.add(("else", makeBlock(elseStmts)))

  elixirTuple(atom("if"), metaFromNode(m, node), list(@[condition, keyword(clauses)]))

proc translateCall(m: BModule; n: PNode): JsonNode =
  if n.len == 0 or n[0].kind != nkSym or n[0].sym.isNil:
    return %* "# unsupported call"

  let name = n[0].sym.name.s
  var args: seq[JsonNode] = @[]
  for i in 1 ..< n.len:
    args.add(translateExpr(m, n[i]))
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
  of nkCall:
    translateCall(m, n)
  of nkIfExpr, nkIfStmt:
    translateIfExpr(m, n)
  of nkPar, nkExprEqExpr, nkHiddenAddr, nkHiddenDeref:
    if n.len > 0: translateExpr(m, n[0]) else: %* "# empty"
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
  of nkAsgn:
    result.addAll(translateAssignment(m, node))
  of nkIfStmt:
    result.add(translateIfExpr(m, node))
  of nkCommentStmt:
    discard
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
  of nkProcDef:
    genProc(m, n)
  else:
    discard
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

  if m.forms.len == 0:
    m.forms.add(%* "# module has no translated procedures")

  m.writeArtifact()
  result = n
