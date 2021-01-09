import compiler/[ast, idents, renderer, lineinfos, parser, options]
import json, tables, sets, strutils, os


let identCache = newIdentCache()
let typeMap = {
    "bool": "bool",
    "void": "void",
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

var importedTypes: HashSet[string]



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
    if typeName in importedTypes:
        typeName
    elif typeName in typeMap:
        typeMap[typeName]
    else:
        typeName
        # raise newException(Exception, "Unknown type: " & typeName)

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

proc createStructDef(structDef: JsonNode): PNode =
    let typeName = structDef["struct"].str
    let recList = newNode(nkRecList)
    for fieldDef in structDef["fields"]:
        let defs = newNode(nkIdentDefs)
        defs.add(ident(fieldDef["fieldname"].str))
        defs.add(nimType(fieldDef["fieldtype"].str))
        defs.add(empty())
        recList.add(defs)

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
    importedTypes.incl(typeName)
    newTypedef(typeName, typedef["type"].str)

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

proc main() =
    let jsonNode = parseFile("C:/lib/steamworks-150/public/steam/steam_api.json")
    let ast = newNode(nkStmtList)
    let typeSection = newNode(nkTypeSection)
    ast.add(typeSection)
    for structDef in jsonNode["callback_structs"]:
        typeSection.add(createStructDef(structDef))

    for typedef in jsonNode["typedefs"]:
        typeSection.add(createTypedef(typedef))

    createDir("gen")
    writeFile("gen/steamworks.nim", renderTree(ast))

main()

# let tree = parseString("""
# type X = object
#     f1: int
#     f2: string
# """, identCache, newPartialConfigRef())

# printTree(tree)