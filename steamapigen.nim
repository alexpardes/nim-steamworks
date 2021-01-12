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
    "int32_t": "int32",
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
    identCache.getIdent(name.multiReplace(("__", "_"), ("::", "_")))

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

proc identDefs(name: string, typeDesc: PNode, defaultValue: PNode = empty()): PNode =
    result = newNode(nkIdentDefs)
    result.add(ident(name))
    result.add(typeDesc)
    result.add(defaultValue)

proc procType(returnTypeStr: string, paramTypeNames: openArray[string]): PNode =
    let params = newNode(nkFormalParams)
    params.add(nimType(returnTypeStr))
    for i, typeName in paramTypeNames:
        params.add(identDefs("arg" & $i, nimType(typeName)))

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

proc ptrTy(typeDesc: PNode): PNode =
    result = newNode(nkPtrTy)
    result.add(typeDesc)

proc pointerType(typeStr: string): PNode =
    if typeStr[^1] != '*':
        return nil

    let innerTypeStr = typeStr[0 ..< ^1].strip()
    if innerTypeStr == "void":
        return ident("pointer")

    result = ptrTy(nimType(innerTypeStr))

proc varTy(typeDesc: PNode): Pnode =
    result = newNode(nkVarTy)
    result.add(typeDesc)

proc refType(typeStr: string): PNode =
    if typeStr[^1] == '&':
        let innerTypeStr = typeStr[0 ..< ^1].strip()
        varTy(nimType(innerTypeStr))
    else:
        nil

proc nimType(typeName: string): PNode =
    var typeName = typeName.strip()
    typeName.removePrefix("const")
    typeName = typeName.strip()
    let asPointer = pointerType(typeName)
    if asPointer != nil:
        return asPointer

    let asRef = refType(typeName)
    if asRef != nil:
        return asRef

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

proc createTypeDef(typedef: JsonNode): PNode =
    let typeName = typedef["typedef"].str
    let typeStr = typedef["type"].str
    importedTypes.incl(typeName)
    typedefMap[typeName] = typeStr
    newTypedef(typeName, typeStr)

proc newDistinctTypeDef(typeName: string, typeDesc: PNode): PNode =
    result = newNode(nkTypeSection)
    let typeDef = newNode(nkTypeDef)
    result.add(typeDef)
    typeDef.add(ident(typeName))
    typeDef.add(empty())
    let distinctTy = newNode(nkDistinctTy)
    distinctTy.add(typeDesc)
    typeDef.add(distinctTy)

iterator createEnumDef(enumDef: JsonNode, namespace: string = ""): PNode =
    # C++ enums don't follow all restrictions of Nim enums
    # We represent a C++ enum as a distinct int type and a block of constants of that type
    let unqualifiedName = enumDef["enumname"].str
    let typeName = if namespace == "":
        unqualifiedName
    else:
        namespace & "_" & unqualifiedName

    let values = enumDef["values"]

    importedTypes.incl(typeName)
    yield newDistinctTypeDef(typeName, ident("cint"))

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

proc createMethodDef(methodDef: JsonNode, typeName: string): PNode =
    result = newNode(nkProcDef)
    result.add(ident(methodDef["methodname_flat"].str))
    result.add(empty()) # Only used for macros
    result.add(empty()) # Generic parameters

    let formalParams = newNode(nkFormalParams)
    formalParams.add(nimType(methodDef["returntype"].str))
    formalParams.add(identDefs("this", ptrTy(nimType(typeName))))

    for paramDef in methodDef["params"]:
        formalParams.add(
            identDefs(
                paramDef["paramname"].str,
                nimType(paramDef["paramtype"].str)))

    result.add(formalParams)
    result.add(empty()) # Pragmas
    result.add(empty()) # Reserved
    result.add(empty()) # Statements

iterator createStructDef(structDef: JsonNode): PNode =
    let typeName = structDef["struct"].str
    let recList = newNode(nkRecList)
    for fieldDef in structDef["fields"]:
        recList.add(
            identDefs(
                fieldDef["fieldname"].str,
                nimType(fieldDef["fieldtype"].str)))

    let enumDefs = structDef{"enums"}
    if not enumDefs.isNil:
        for enumDef in enumDefs:
            for node in createEnumDef(enumDef, typeName):
                yield node

    let objectTy = newNode(nkObjectTy)
    objectTy.add(empty())
    objectTy.add(empty())
    objectTy.add(recList)
    let typeDef = newNode(nkTypeDef)
    typeDef.add(ident(typeName))
    typeDef.add(empty())
    typeDef.add(objectTy)
    let typeSection = newNode(nkTypeSection)
    typeSection.add(typeDef)
    yield typeSection

    let methodDefs = structDef{"methods"}
    if not methodDefs.isNil:
        for methodDef in methodDefs:
            yield createMethodDef(methodDef, typeName)

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

    let colonExpr = newNode(nkExprColonExpr)
    colonExpr.add(ident("experimental"))
    colonExpr.add(strLit("codeReordering"))
    let pragma = newNode(nkPragma)
    pragma.add(colonExpr)
    ast.add(pragma)
    ast.add(newDistinctTypeDef("CSteamID", ident("uint64")))
    ast.add(newDIstinctTypeDef("CGameID", ident("uint64")))

    for enumDef in jsonNode["enums"]:
        for statement in createEnumDef(enumDef):
            ast.add(statement)

    let typeSection = newNode(nkTypeSection)
    ast.add(typeSection)

    for structDef in jsonNode["structs"]:
        for statement in createStructDef(structDef):
            ast.add(statement)

    for structDef in jsonNode["callback_structs"]:
        for statement in createStructDef(structDef):
            ast.add(statement)

    for typedef in jsonNode["typedefs"]:
        typeSection.add(createTypedef(typedef))

    let constSection = newNode(nkConstSection)
    ast.add(constSection)

    let translations = translateConstExpressions(jsonNode["consts"])
    for i, constDef in jsonNode["consts"].elems:
        constSection.add(createConstDef(constDef, translations[i]))

    for typeName in unknownTypes:
        if not importedTypes.contains(typeName):
            echo "Missing definition for " & typeName

    createDir("gen")
    writeFile("gen/steamworks.nim", renderTree(ast))

when isMainModule:
    main()