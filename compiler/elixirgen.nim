#
# Nim Elixir Backend (minimal prototype)

import
  ast, modulegraphs, options, msgs, idents, lineinfos

import pipelineutils

import std/[strutils, sequtils, os]

when defined(nimPreviewSlimSystem):
  import std/syncio

type
  TElixirGen = object of PPassContext
    module: PSym
    graph: ModuleGraph
    config: ConfigRef
    moduleName: string
    elixirModuleName: string
    lines: seq[string]

  BModule = ref TElixirGen

proc indent(level: int): string =
  result = repeat("  ", level)

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

proc mapTypeName(typeName: string): string =
  case typeName
  of "int", "int32", "int64", "int8", "int16", "Natural": "integer()"
  of "float", "float32", "float64": "float()"
  of "bool": "boolean()"
  of "string": "String.t()"
  else: "any()"

proc mapTypeSym(sym: PSym): string =
  if sym == nil: return "any()"
  mapTypeName(sym.name.s)

proc escapeElixirString(s: string): string =
  result = s
  result = result.replace("\\", "\\\\")
  result = result.replace("\"", "\\\"")
  result = result.replace("\n", "\\n")

proc mapOperator(name: string): string =
  case name
  of "+", "-", "*", "/", "<", "<=", ">", ">=", "==", "!=": name
  of "&": "<>"
  else: name

proc addLine(m: BModule, line: string) =
  m.lines.add(line)

proc addLines(target: var seq[string]; lines: seq[string]) =
  for line in lines:
    target.add(line)

proc translateExpr(m: BModule; n: PNode): string

proc translateCall(m: BModule; n: PNode): string =
  if n.len == 0: return "/* unsupported call */"
  let callee = translateExpr(m, n[0])
  var args: seq[string] = @[]
  for i in 1 ..< n.len:
    args.add(translateExpr(m, n[i]))
  result = callee & "(" & args.join(", ") & ")"

proc translateInfix(m: BModule; n: PNode): string =
  if n.len < 3: return "/* unsupported infix */"
  let opSym = n[0]
  let left = translateExpr(m, n[1])
  let right = translateExpr(m, n[2])
  var opName = ""
  if opSym.kind == nkSym:
    opName = mapOperator(opSym.sym.name.s)
  else:
    opName = "/*op*/"
  result = "(" & left & " " & opName & " " & right & ")"

proc translateExpr(m: BModule; n: PNode): string =
  case n.kind
  of nkSym:
    let sym = n.sym
    if sym.isNil:
      result = "/*sym*/"
    else:
      result = sym.name.s
  of nkIntLit..nkInt64Lit:
    result = $n.intVal
  of nkUIntLit..nkUInt64Lit:
    result = $n.intVal
  of nkFloatLit..nkFloat128Lit:
    result = repr(n.floatVal)
  of nkStrLit, nkTripleStrLit:
    result = "\"" & escapeElixirString(n.strVal) & "\""
  of nkInfix:
    result = translateInfix(m, n)
  of nkCall:
    result = translateCall(m, n)
  of nkPar, nkExprEqExpr, nkHiddenAddr, nkHiddenDeref:
    if n.len > 0:
      result = translateExpr(m, n[0])
    else:
      result = "/*unsupported*/"
  else:
    result = "/* " & $n.kind & " */"

proc translateAssignment(m: BModule; stmt: PNode; indentLevel: int): seq[string] =
  result = @[]
  if stmt.kind != nkAsgn or stmt.len < 2:
    result.add(indent(indentLevel) & "# unsupported assignment: " & $stmt.kind)
    return

  let target = stmt[0]
  let expr = stmt[1]
  if target.kind == nkSym and target.sym.name.s == "result":
    result.add(indent(indentLevel) & translateExpr(m, expr))
  else:
    let lhs = translateExpr(m, target)
    let rhs = translateExpr(m, expr)
    result.add(indent(indentLevel) & lhs & " = " & rhs)

proc translateStmt(m: BModule; node: PNode; indentLevel: int): seq[string]

proc translateIf(m: BModule; node: PNode; indentLevel: int): seq[string] =
  result = @[]
  if node.len == 0:
    return @[indent(indentLevel) & "# unsupported empty if"]

  let firstBranch = node[0]
  if firstBranch.kind != nkElifBranch or firstBranch.len < 2:
    return @[indent(indentLevel) & "# unsupported if structure"]

  let condition = translateExpr(m, firstBranch[0])
  result.add(indent(indentLevel) & "if " & condition & " do")

  for i in 1 ..< firstBranch.len:
    result.addLines(translateStmt(m, firstBranch[i], indentLevel + 1))

  var elseNode: PNode = nil
  for branch in node:
    if branch.kind == nkElse:
      elseNode = branch
      break
  if elseNode != nil:
    result.add(indent(indentLevel) & "else")
    for child in elseNode:
      result.addLines(translateStmt(m, child, indentLevel + 1))

  result.add(indent(indentLevel) & "end")

proc translateStmt(m: BModule; node: PNode; indentLevel: int): seq[string] =
  result = @[]
  case node.kind
  of nkStmtList:
    for child in node:
      result.addLines(translateStmt(m, child, indentLevel))
  of nkAsgn:
    result.addLines(translateAssignment(m, node, indentLevel))
  of nkIfStmt:
    result.addLines(translateIf(m, node, indentLevel))
  of nkCommentStmt:
    discard
  else:
    result.add(indent(indentLevel) & "# unsupported node: " & $node.kind)

proc extractReturnType(procNode: PNode): string =
  if procNode[paramsPos].len == 0: return "any()"
  let retNode = procNode[paramsPos][0]
  if retNode.kind == nkSym:
    return mapTypeSym(retNode.sym)
  result = "any()"

proc extractParams(procNode: PNode): seq[(string, string)] =
  result = @[]
  let paramsNode = procNode[paramsPos]
  for i in 1 ..< paramsNode.len:
    let paramNode = paramsNode[i]
    if paramNode.kind != nkIdentDefs:
      continue
    var names: seq[string] = @[]
    var typeSpec = "any()"
    for child in paramNode:
      if child.kind == nkSym:
        case child.sym.kind
        of skParam:
          names.add(child.sym.name.s)
        of skType:
          typeSpec = mapTypeSym(child.sym)
        else:
          discard
    if names.len == 0:
      continue
    for name in names:
      result.add((name, typeSpec))

proc genProc(m: BModule; procNode: PNode) =
  let procSym = procNode[namePos].sym
  if procSym.isNil:
    return
  let procName = procSym.name.s
  let returnType = extractReturnType(procNode)
  let params = extractParams(procNode)

  let specParams = params.mapIt(it[1])
  let specLine = indent(1) & "@spec " & procName & "(" & specParams.join(", ") & ") :: " & returnType
  addLine(m, specLine)

  let paramNames = params.mapIt(it[0])
  let defLine = indent(1) & "def " & procName & "(" & paramNames.join(", ") & ") do"
  addLine(m, defLine)

  let bodyNode = procNode[bodyPos]
  var bodyLines = translateStmt(m, bodyNode, 2)
  if bodyLines.len == 0:
    bodyLines.add(indent(2) & "nil")
  for line in bodyLines:
    addLine(m, line)

  addLine(m, indent(1) & "end")
  addLine(m, "")

proc setupElixirgen*(graph: ModuleGraph; module: PSym; idgen: IdGenerator): PPassContext =
  result = BModule(module: module, graph: graph, config: graph.config)
  result.idgen = idgen
  let rawName = if module != nil: module.name.s else: graph.config.projectName
  BModule(result).moduleName = rawName
  BModule(result).elixirModuleName = toElixirModuleName(rawName)

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

  var lines: seq[string] = @[]
  lines.add("# Generated by Nim -> Elixir experimental backend")
  lines.add("defmodule " & m.elixirModuleName & " do")

  if m.lines.len == 0:
    lines.add(indent(1) & "# TODO: No procedures translated")
    lines.add(indent(1) & "def main do")
    lines.add(indent(2) & "IO.puts(\"stub: " & m.elixirModuleName & "\")")
    lines.add(indent(1) & "end")
  else:
    for line in m.lines:
      lines.add(line)

  lines.add("end")

  let code = lines.join("\n") & "\n"

  let baseDir = getNimcacheDir(m.config)
  let outDirPath = joinPath(baseDir.string, "elixir")
  createDir(outDirPath)
  let outFilePath = joinPath(outDirPath, m.elixirModuleName & ".exs")
  try:
    writeFile(outFilePath, code)
  except IOError:
    rawMessage(m.config, errCannotOpenFile, outFilePath)
