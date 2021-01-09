import compiler/[ast, idents, renderer, lineinfos, parser, options]
import json, tables, sets, strutils


let identCache = newIdentCache()
var sameTypes = toHashSet(["int32", "uint32", "int64", "uint64", "void", "bool"])
let typeMap = {
    "int": "cint",
    "unsigned int": "cuint",
    "unsigned char": "cuchar",
    "char": "cchar",
    "signed char": "cschar",
    "short": "cshort",
    "unsigned short": "cushort",
    "long long": "clonglong",
    "unsigned long long": "culonglong",
}.toTable()



proc strLit(str: string): Pnode =
    result = newNode(nkStrLit)
    result.strVal = str

proc empty(): Pnode = newNode(nkEmpty)

proc intLit(i: int): Pnode =
    result = newNode(nkIntLit)
    result.intVal = i

proc getIdent(name: string): PIdent =
    identCache.getIdent(name)

proc ident(name: string): PNode =
    var lineInfo: TLineInfo
    newIdentNode(getIdent(name), lineInfo)

proc nimTypeName(typeName: string): string =
    if typeName in sameTypes:
        typeName
    elif typeName in typeMap:
        typeMap[typeName]
    else:
        # raise newException(Exception, "Unknown type: " & typeName)
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
    let defs = newNode(nkIdentDefs)
    for typeName in paramTypeNames:
        defs.add(nimType(typeName))

    defs.add(empty())
    defs.add(empty())
    let params = newNode(nkFormalParams)
    params.add(nimType(returnTypeStr))
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

proc newConstDef(name: string, typeName: string, valString: string): PNode =
    result = newNode(nkConstDef)
    result.add(ident(name))
    result.add(nimType(name))
    result.add(strLit(valString))

proc newTypedef(aliasName: string, typeName: string): PNode =
    result = newNode(nkTypeDef)
    result.add(ident(aliasName))
    result.add(empty())
    result.add(nimType(typeName))

proc main() =
    let jsonNode = parseFile("C:/lib/steamworks-150/public/steam/steam_api.json")
    var ast = newNode(nkStmtList)
    for typedef in jsonNode["typedefs"]:
        let typeName = typedef["typedef"].str
        ast.add(newTypedef(typeName, typedef["type"].str))
        sameTypes.incl(typeName)

    echo renderTree(ast)


main()