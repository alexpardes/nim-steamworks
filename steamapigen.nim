import compiler/[ast, idents, renderer, lineinfos, parser, options]
import json, tables, sets, strutils, os, sugar

let jsonPath = "../steamworks-sdk/public/steam/steam_api.json"  

when system.hostOS == "windows":
    let libPath = "win64/steam_api64.dll"
elif system.hostOS == "linux":
    let libPath = "linux64/libsteam_api.so"

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
    "size_t": "csize_t",
    "intptr_t": "pointer",
}.toTable()

var importedTypes: HashSet[string]
var unknownTypes: HashSet[string]
var typedefMap: Table[string, string]
var interfaceVersionStrings: Table[string, string]

proc empty(): Pnode = newNode(nkEmpty)

proc strLit(str: string): Pnode =
    result = newNode(nkStrLit)
    result.strVal = str

proc intLit(n: int): Pnode =
    result = newNode(nkIntLit)
    result.intVal = n

proc cleanIdentifier(id: string): string =
    id.multiReplace(("__", "_"), ("::", "_"))

proc getIdent(name: string): PIdent =
    # TODO: Need to use the original name with .cimport
    identCache.getIdent(cleanIdentifier(name))

proc ident(name: string): PNode =
    var lineInfo: TLineInfo
    newIdentNode(getIdent(name), lineInfo)

proc nimTypeName(typeName: string): string =
    let typeName = cleanIdentifier(typeName)
    if typeName in importedTypes:
        typeName
    elif typeName in typeMap:
        typeMap[typeName]
    else:
        unknownTypes.incl(typeName)
        typeName

proc nimType(typeName: string): PNode

proc exportedIdent(name: string): PNode =
    result = newNode(nkPostfix)
    result.add(ident("*"))
    result.add(ident(name))

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
    var name = name
    if name in ["addr", "type"]:
        name &= '1'

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

    if innerTypeStr == "char":
        return ident("cstring")

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
    typeName.removeSuffix("const")
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

proc newTypeSection(typeDefs: varargs[PNode]): PNode =
    result = newNode(nkTypeSection)
    for typeDef in typeDefs:
        result.add(typeDef)

proc newConstDef(name: string, typeDesc: PNode, value: PNode): PNode =
    result = newNode(nkConstDef)
    result.add(exportedIdent(name))
    result.add(typeDesc)
    result.add(value)

proc newConstDef(name: string, typeName: string, valueExpr: PNode): PNode =
    let castNode = newNode(nkCast)
    castNode.add(ident(resolveTypedef(typeName)))
    castNode.add(valueExpr)
    newConstDef(
        name,
        nimType(typeName),
        castNode)

proc createConstDef(constDef: JsonNode, valueExpr: PNode): PNode =
    newConstDef(
        constDef["constname"].str,
        constDef["consttype"].str,
        valueExpr)

proc newTypeDef(name: string, typeDesc: PNode): PNode =
    importedTypes.incl(name)
    result = newNode(nkTypeDef)
    result.add(exportedIdent(name))
    result.add(empty()) # Generic parameters
    result.add(typeDesc)

proc newTypedef(aliasName: string, typeStr: string): PNode =
    importedTypes.incl(aliasName)
    typedefMap[aliasName] = typeStr
    newTypeDef(aliasName, nimType(typeStr))

proc createTypeDef(typedef: JsonNode): PNode =
    let typeName = typedef["typedef"].str
    let typeStr = typedef["type"].str
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

proc newConstSection(constDefs: varargs[PNode]): PNode =
    result = newNode(nkConstSection)
    for constDef in constDefs:
        result.add(constDef)

proc newCall(procName: string, args: varargs[PNode]): PNode =
    result = newNode(nkCall)
    result.add(ident(procName))
    for arg in args:
        result.add(arg)

proc createEnumDef(enumDef: JsonNode, namespace: string = ""): seq[PNode] =
    # C++ enums don't follow all restrictions of Nim enums
    # We represent a C++ enum as a distinct int type and a block of constants of that type
    let unqualifiedName = enumDef["enumname"].str
    let typeName = if namespace == "":
        unqualifiedName
    else:
        namespace & "_" & unqualifiedName

    let values = enumDef["values"]

    importedTypes.incl(typeName)
    result.add(newTypeSection(newTypeDef(typeName, ident("cint"))))

    let constSection = newNode(nkConstSection)
    for val in values:
        let constDef = newNode(nkConstDef)
        constDef.add(exportedIdent(val["name"].str))
        constDef.add(ident(typeName))
        let intLit = intLit(val["value"].str.parseInt())
        constDef.add(newCall(typeName, intLit))
        constSection.add(constDef)

    result.add(constSection)

proc newPragma(pragmas: varargs[PNode]): PNode =
    result = newNode(nkPragma)
    for pragma in pragmas:
        result.add(pragma)

proc newExprColonExpr(a: PNode, b: PNode): Pnode =
    result = newNode(nkExprColonExpr)
    result.add(a)
    result.add(b)

proc newProcDef(
    name: string,
    returnType: PNode,
    params: openArray[PNode],
    pragmas: PNode = empty(),
    statements: PNode = empty()
): PNode =

    let formalParams = newNode(nkFormalParams)
    formalParams.add(returnType)
    for param in params:
        formalParams.add(param)

    result = newNode(nkProcDef)
    result.add(exportedIdent(name))
    result.add(empty()) # Only used for macros
    result.add(empty()) # Generic parameters
    result.add(formalParams)
    result.add(pragmas)
    result.add(empty()) # Reserved
    result.add(statements)

proc newImportedProcDef(name: string, returnTypeDesc: PNode, params: varargs[PNode]): PNode =
    let pragmas = newPragma(
        ident("importc"),
        ident("cdecl"),
        newExprColonExpr(
            ident("dynlib"),
            ident("steamworksLib")))

    newProcDef(name, returnTypeDesc, params, pragmas)

proc createMethodDef(methodDef: JsonNode, typeName: string): PNode =
    let thisParam = identDefs("this", ptrTy(nimType(typeName)))
    let paramDefs = collect(newSeq):
        for paramDef in methodDef["params"]:
            identDefs(
                paramDef["paramname"].str,
                nimType(paramDef["paramtype"].str))

    newImportedProcDef(
        methodDef["methodname_flat"].str,
        nimType(methodDef["returntype"].str),
        thisParam & paramDefs)

# proc createInterfaceMethodDef(methodDef: JsonNode, typeName: string, versionString: string): seq[PNode] =
#     let paramDefs = methodDef["params"].getElems
#     let thisParam = identDefs("this", ptrTy(nimType(typeName)))
#     var versionParam: PNode
#     var params = collect(newSeq):
#         for i, paramDef in paramDefs:
#             let paramName = paramDef["paramname"].str
#             let identDefs = identDefs(
#                 paramName,
#                 nimType(paramDef["paramtype"].str))

#             if paramName == "pchVersion":
#                 versionParam = identDefs
#                 assert i == high(paramDefs)
#                 break

#             identDefs

#     let methodName = methodDef["methodname_flat"].str
#     let returnType = nimType(methodDef["returntype"].str)
#     params = thisParam & params
#     if not versionParam.isNil:
#         assert versionString != "", typeName
#         params &= versionParam

#     let procDef = newImportedProcDef(
#         methodName,
#         returnType,
#         params)

#     result.add(procDef)

#     if not versionParam.isNil:
#         let body = newNode(nkStmtList)
#         let args = collect(newSeq):
#             for paramDef in paramDefs:
#                 let paramName = paramDef["paramname"].str
#                 if paramName == "pchVersion":
#                     break

#                 ident(paramName)

#         body.add(newCall(methodName, args))
#         let wrapperDef = newProcDef(methodName, returnType, params, empty(), body)
#         result.add(wrapperDef)

# Each field is typically an IdentDefs
proc newObjectTy(fields: varargs[PNode]): PNode =
    result = newNode(nkObjectTy)
    result.add(empty()) # Pragmas
    result.add(empty()) # Base object

    let recList = newNode(nkRecList)
    for field in fields:
        recList.add(field)

    result.add(recList)

proc newObjectDef(name: string, fields: varargs[PNode]): PNode =
    newTypeDef(name, newObjectTy(fields))

proc createStructDef(typeName: string, structDef: JsonNode): seq[PNode] =
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
                result.add(node)

    let objectTy = newNode(nkObjectTy)
    objectTy.add(empty())
    objectTy.add(empty())
    objectTy.add(recList)
    result.add(newTypeSection(newTypeDef(typeName, objectTy)))

    let methodDefs = structDef{"methods"}
    if not methodDefs.isNil:
        for methodDef in methodDefs:
            result.add(createMethodDef(methodDef, typeName))

proc createStructDef(structDef: JsonNode): seq[Pnode] =
    createStructDef(structDef["struct"].str, structDef)

proc createInterfaceDef(interfaceDef: JsonNode): seq[PNode] =
    let typeName = interfaceDef["classname"].str
    result.add(newTypeSection(newObjectDef(typeName)))
    let accessors = interfaceDef{"accessors"}
    if not accessors.isNil:
        for accessor in accessors:
            result.add(
                newImportedProcDef(
                    accessor["name_flat"].str,
                    nimType(typeName)))

    let enumDefs = interfaceDef{"enums"}
    if not enumDefs.isNil:
        for enumDef in enumDefs:
            for node in createEnumDef(enumDef, typeName):
                result.add(node)

    let versionNode = interfaceDef{"version_string"}
    if not versionNode.isNil:
        interfaceVersionStrings[typeName] = versionNode.str

    for methodDef in interfaceDef["methods"]:
        result.add(createMethodDef(methodDef, typeName))

proc createVersionlessMethodWrapper(methodDef: JsonNode): PNode =
    let procName = methodDef["methodname_flat"].str
    if procName == "SteamAPI_ISteamClient_GetISteamGenericInterface":
        return nil

    let returnTypestr = methodDef["returntype"].str
    let returnType = nimType(returnTypestr)
    let thisParam = identDefs("this", ptrTy(nimType("ISteamClient")))
    let paramDefs = methodDef["params"].getElems()
    if paramDefs.len == 0 or paramDefs[^1]["paramname"].str != "pchVersion":
        return nil

    var args = @[ident("this")]
    var params = @[thisParam]
    for paramDef in paramDefs[0 ..< ^1]:
        let paramName = paramDef["paramname"].str
        args.add(ident(paramName))
        params.add(
            identDefs(
                paramName,
                nimType(paramDef["paramtype"].str)))

    var interfaceName = returnTypeStr
    interfaceName.removeSuffix("*")
    interfaceName = interfaceName.strip()
    if not interfaceVersionStrings.contains(interfaceName):
        echo "No entry for " & interfaceName & " in " & procName

    args.add(strlit(interfaceVersionStrings[interfaceName]))
    let call = newCall(procName, args)
    let statements = newNode(nkStmtList)
    statements.add(call)
    newProcDef(procName, returnType, params, statements = statements)

proc createVersionlessMethodWrappers(methodDefs: JsonNode): seq[PNode] =
    for methodDef in methodDefs:
        let wrapper = createVersionlessMethodWrapper(methodDef)
        if wrapper != nil:
            result.add(wrapper)

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
    echo renderTree(parseNim(s))

proc findISteamClientDef(interfaceDefs: JsonNode): JsonNode =
    for def in interfaceDefs:
        if def["classname"].str == "ISteamClient":
            return def

proc main() =
    let jsonNode = parseFile(jsonPath)
    let ast = newNode(nkStmtList)

    let colonExpr = newNode(nkExprColonExpr)
    colonExpr.add(ident("experimental"))
    colonExpr.add(strLit("codeReordering"))
    let pragma = newNode(nkPragma)
    pragma.add(colonExpr)
    ast.add(pragma)

    ast.add(
        newConstSection(
            newConstDef(
                "steamworksLib",
                empty(),
                strLit(libPath))))

    ast.add(newDistinctTypeDef("CSteamID", ident("uint64")))
    importedTypes.incl("CSteamID")
    ast.add(newDIstinctTypeDef("CGameID", ident("uint64")))
    importedTypes.incl("CGameID")

    for enumDef in jsonNode["enums"]:
        for statement in createEnumDef(enumDef):
            ast.add(statement)

    let typeSection = newNode(nkTypeSection)
    ast.add(typeSection)

    for typedef in jsonNode["typedefs"]:
        typeSection.add(createTypedef(typedef))

    for structDef in jsonNode["structs"]:
        for statement in createStructDef(structDef):
            ast.add(statement)

    for structDef in jsonNode["callback_structs"]:
        for statement in createStructDef(structDef):
            ast.add(statement)

    for interfaceDef in jsonNode["interfaces"]:
        for statement in createInterfaceDef(interfaceDef):
            ast.add(statement)

    for statement in createVersionlessMethodWrappers(findISteamClientDef(jsonNode["interfaces"])["methods"]):
        ast.add(statement)            

    let constSection = newNode(nkConstSection)
    ast.add(constSection)

    let translations = translateConstExpressions(jsonNode["consts"])
    for i, constDef in jsonNode["consts"].elems:
        constSection.add(createConstDef(constDef, translations[i]))

    for typeName in unknownTypes:
        if not importedTypes.contains(typeName):
            echo "Missing definition for " & typeName
            typeSection.add(newObjectDef(typeName))

    ast.add(newImportedProcDef("SteamAPI_Init", nimType("bool")))
    ast.add(newImportedProcDef("SteamAPI_ReleaseCurrentThreadMemory", nimType("void")))
    ast.add(newImportedProcDef("SteamAPI_RestartAppIfNecessary", nimType("bool"), identDefs("unOwnAppID", nimType("uint32"))))
    ast.add(newImportedProcDef("SteamAPI_RunCallbacks", nimType("void")))
    ast.add(newImportedProcDef("SteamAPI_SetMiniDumpComment", nimType("void"), identDefs("pchMsg", nimType("const char *"))))
    ast.add(newImportedProcDef("SteamAPI_Shutdown", nimType("void")))
    ast.add(
        newImportedProcDef(
            "SteamAPI_WriteMiniDump",
            nimType("void"),
            identDefs("uStructuredExceptionCode", nimType("uint32")),
            identDefs("pvExceptionInfo", nimType("void *")),
            identDefs("uBuildID", nimType("uint32"))))

    ast.add(
        newTypeSection(
            newObjectDef(
                "CallbackMsg_t",
                identDefs("steamUser", nimType("HSteamUser")),
                identDefs("callbackId", nimType("int")),
                identDefs("pData", ident("pointer")),
                identDefs("dataSize", nimType("int")))))

    ast.add(newImportedProcDef("SteamClient", nimType("ISteamClient *")))
    ast.add(newImportedProcDef("SteamAPI_ManualDispatch_Init", empty()))
    ast.add(newImportedProcDef("SteamAPI_ManualDispatch_RunFrame", empty(), identDefs("hSteamPipe", nimType("HSteamPipe"))))
    ast.add(
        newImportedProcDef(
            "SteamAPI_ManualDispatch_GetNextCallback",
            nimType("bool"),
            identDefs("hSteamPipe", nimType("HSteamPipe")),
            identDefs("message", varTy(ident("CallbackMsg_t")))))

    ast.add(newImportedProcDef("SteamAPI_ManualDispatch_FreeLastCallback", empty(), identDefs("hSteamPipe", nimType("HSteamPipe"))))
    ast.add(
        newImportedProcDef(
            "SteamAPI_ManualDispatch_GetAPICallResult",
            nimType("bool"),
            identDefs("hSteamPipe", nimType("HSteamPipe")),
            identDefs("steamApiCall", nimType("SteamAPICall_t")),
            identDefs("pCallback", ident("pointer")),
            identDefs("cubCallback", nimType("int")),
            identDefs("iCallbackExpected", nimType("int")),
            identDefs("pbFailed", nimType("bool*"))))

    createDir("gen")
    writeFile("gen/steamworks.nim", renderTree(ast))

# TODO:
#   Either make enums not distinct types, or figure out correct types for procs
#   Different Nim names and C names
#   Use short names in camel/Pascal case for Nim
#   Support callback registration
#   .cimport structs?
#   Are global accessors like SteamFriends() available in C?
#   Create getSteamPipe and getSteamUser
#   Make accessor wrappers take no parameters by getting ISteamClient, HSteamPipe, HSteamUser directly
#   Investigate caching Steam singletons
when isMainModule:
    main()