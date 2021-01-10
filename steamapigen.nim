import compiler/[ast, idents, renderer, lineinfos, parser, options]
import json, tables, sets, strutils, os


let identCache = newIdentCache()
let typeMap = {
    "bool": "bool",
    "void": "void",
    "int": "cint",
    "int32": "int32",
    "uint32": "uint32",
    "unsigned int": "cuint",
    "unsigned char": "cuchar",
    "char": "cchar",
    "signed char": "cschar",
    "short": "cshort",
    "unsigned short": "cushort",
    "long long": "clonglong",
    "unsigned long long": "culonglong",
    "uint16": "uint16",
    "uint8": "uint8",
    "uint64": "uint64",
    "float": "cfloat",
    "double": "cdouble",
    "int64_t": "int64",
}.toTable()

var importedTypes: HashSet[string]
var unknownTypes: HashSet[string]
var typedefMap: Table[string, string]

proc empty(): Pnode = newNode(nkEmpty)

proc strLit(str: string): Pnode =
    result = newNode(nkStrLit)
    result.strVal = str

proc intLit(n: int): Pnode =
    result = newNode(nkIntLit)
    result.intVal = n

proc getIdent(name: string): PIdent =
    # TODO: Need to use the original name with .cimport
    identCache.getIdent(name.multiReplace(("__", "_"), ("::", "_NESTED_")))

proc ident(name: string): PNode =
    var lineInfo: TLineInfo
    newIdentNode(getIdent(name), lineInfo)

type UndefinedTypeException = object of CatchAbleError

proc nimTypeName(typeName: string): string =
    if typeName in importedTypes:
        typeName
    elif typeName in typeMap:
        typeMap[typeName]
    else:
        unknownTypes.incl(typeName)
        typeName

proc nimType(typeName: string): PNode

proc arrayType(typeName: string, length: int): PNode =
    result = newNode(nkBracketExpr)
    result.add(ident("array"))
    result.add(intLit(length))
    result.add(nimType(typeName))

proc arrayType(typeStr: string): PNode =
    let parsed = typeStr.split({'[', ']'})
    if parsed.len > 1:
        assert parsed.len == 3
        arrayType(parsed[0], parseInt(parsed[1]))
    else:
        nil

proc procType(returnTypeStr: string, paramTypeNames: openArray[string]): PNode =
    let params = newNode(nkFormalParams)
    params.add(nimType(returnTypeStr))
    for i, typeName in paramTypeNames:
        let defs = newNode(nkIdentDefs)
        defs.add(ident("arg" & $i))
        defs.add(nimType(typeName))
        defs.add(empty())
        params.add(defs)

    result = newNode(nkProcTy)
    result.add(params)
    result.add(empty())

proc procType(typeStr: string): PNode =
    # e.g.
    # void (*)(const char *, const char *)
    let parsed = typeStr.split({'(', ')'})
    if parsed.len > 1:
        assert parsed.len == 5
        var params = parsed[3].split(',')
        if params.len == 1 and params[0] == "":
            params = @[]

        procType(parsed[0], params)
    else:
        nil

proc pointerType(typeStr: string): PNode =
    if typeStr[^1] != '*':
        return nil

    let innerTypeStr = typeStr[0 ..< ^1].strip()
    if innerTypeStr == "void":
        return ident("pointer")

    result = newNode(nkPtrTy)
    result.add(nimType(innerTypeStr))


proc nimType(typeName: string): PNode =
    var typeName = typeName.strip()
    typeName.removePrefix("const")
    typeName = typeName.strip()
    let asPointer = pointerType(typeName)
    if asPointer != nil:
        return asPointer

    let asArray = arrayType(typeName)
    if asArray != nil:
        return asArray

    let asProc = procType(typeName)
    if asProc != nil:
        return asProc

    ident(nimTypeName(typeName))

proc resolveTypedef(typeName: string): string =
    if typeMap.contains(typeName):
        typeMap[typeName]
    elif typedefMap.contains(typeName):
        resolveTypedef(typedefMap[typeName])
    else:
        raise newException(Exception, "Unknown typedef: " & typeName)

proc newConstDef(name: string, typeName: string, valueExpr: Pnode): PNode =
    result = newNode(nkConstDef)
    result.add(ident(name))

    let nimType = nimType(typeName)
    result.add(nimType)

    let castNode = newNode(nkCast)
    castNode.add(ident(resolveTypedef(typeName)))
    castNode.add(valueExpr)
    result.add(castNode)

proc createConstDef(constDef: JsonNode, valueExpr: PNode): PNode =
    newConstDef(
        constDef["constname"].str,
        constDef["consttype"].str,
        valueExpr)

proc newTypedef(aliasName: string, typeName: string): PNode =
    result = newNode(nkTypeDef)
    result.add(ident(aliasName))
    result.add(empty())
    result.add(nimType(typeName))

proc createStructDef(structDef: JsonNode): PNode =
    let typeName = structDef["struct"].str
    let recList = newNode(nkRecList)
    for fieldDef in structDef["fields"]:
        let defs = newNode(nkIdentDefs)
        defs.add(ident(fieldDef["fieldname"].str))
        defs.add(nimType(fieldDef["fieldtype"].str))
        defs.add(empty())
        recList.add(defs)

    # TODO: Add methods

    let objectTy = newNode(nkObjectTy)
    objectTy.add(empty())
    objectTy.add(empty())
    objectTy.add(recList)
    result = newNode(nkTypeDef)
    result.add(ident(typeName))
    result.add(empty())
    result.add(objectTy)

proc createTypeDef(typedef: JsonNode): PNode =
    let typeName = typedef["typedef"].str
    let typeStr = typedef["type"].str
    importedTypes.incl(typeName)
    typedefMap[typeName] = typeStr
    newTypedef(typeName, typeStr)

iterator createEnumDef(enumDef: JsonNode): PNode =
    # C++ enums don't correspond to Nim enums
    # Instead, use distinct int type with constant values
    let typeName = enumDef["enumname"].str
    let values = enumDef["values"]

    importedTypes.incl(typeName)
    let typeSection = newNode(nkTypeSection)
    let typeDef = newNode(nkTypeDef)
    typeSection.add(typeDef)
    typeDef.add(ident(typeName))
    typeDef.add(empty())
    let distinctTy = newNode(nkDistinctTy)
    distinctTy.add(ident("cint"))
    typeDef.add(distinctTy)
    yield typeSection

    let constSection = newNode(nkConstSection)
    for val in values:
        let constDef = newNode(nkConstDef)
        constDef.add(ident(val["name"].str))
        constDef.add(ident(typeName))
        let call = newNode(nkCall)
        call.add(ident(typeName))
        call.add(intLit(val["value"].str.parseInt()))
        constDef.add(call)
        constSection.add(constDef)

    yield constSection

proc printTree(ast: PNode, indentLevel: int = 0) =
    var s = ""
    for i in 1 .. indentLevel:
        s &= "   "

    s &= $ast.kind
    if ast.kind == nkIdent:
        s &= ": " & ast.ident.s
    echo s
    for child in ast:
        printTree(child, indentLevel + 1)

proc parseNim(s: string): PNode =
    parseString(s, identCache, newPartialConfigRef())

proc translateConstExpressions(constDefs: JsonNode): seq[PNode] =
    createDir("tmp")
    let cPath = "tmp/consts.c"
    removeFile(cPath)
    var file: File
    if not open(file, cPath, fmAppend):
        raise newException(IOError, "Could not open file " & cPath)

    for constDef in constDefs:
        var expressionStr = constDef["constval"].str

        # Kludge to work around c2nim being unable to parse `( SteamItemInstanceID_t ) ~ 0`
        expressionStr = expressionStr.replace("~", "1 * ~")
        file.write(expressionStr & ";\n")

    file.close()
    if execShellCmd("c2nim " & cPath) != 0:
        raise newException(Exception, "c2nim failed")
    let nimPath = cPath.changeFileExt("nim")
    if not open(file, nimPath):
        raise newException(IOError, "Could not open file " & nimPath)

    defer: file.close()
    parseNim(file.readAll()).sons

proc printAst(s: string) =
    printTree(parseNim(s))

proc main() =
    let jsonNode = parseFile("C:/lib/steamworks-150/public/steam/steam_api.json")
    let ast = newNode(nkStmtList)

    for enumDef in jsonNode["enums"]:
        for statement in createEnumDef(enumDef):
            ast.add(statement)

    let typeSection = newNode(nkTypeSection)
    ast.add(typeSection)

    for structDef in jsonNode["structs"]:
        typeSection.add(createStructDef(structDef))

    for structDef in jsonNode["callback_structs"]:
        typeSection.add(createStructDef(structDef))

    for typedef in jsonNode["typedefs"]:
        typeSection.add(createTypedef(typedef))

    let constSection = newNode(nkConstSection)
    ast.add(constSection)

    echo "Translating"
    let translations = translateConstExpressions(jsonNode["consts"])
    echo "Translated"
    for i, constDef in jsonNode["consts"].elems:
        constSection.add(createConstDef(constDef, translations[i]))

    for typeName in unknownTypes:
        if not importedTypes.contains(typeName):
            echo "Missing definition for " & typeName

    echo "Writing"
    createDir("gen")
    writeFile("gen/steamworks.nim", renderTree(ast))

when isMainModule:
    main()