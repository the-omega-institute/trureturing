import Lean.Environment
import Lean.CoreM
import Lean.PrivateName
import Lean.Util.CollectAxioms

open Lean

structure ModuleInput where
  moduleName : String
  sourcePath : String
  sourceSha256 : String

structure DeclarationReport where
  axioms : Array String
  includeInStatement : Bool
  kind : String
  name : String
  nameKey : String
  type : String

structure ModuleReport where
  declarations : Array DeclarationReport
  imports : Array String
  moduleName : String
  sourcePath : String
  sourceSha256 : String

def atom (value : String) : String := s!"{value.utf8ByteSize}:{value}"

partial def encodeName : Name → String
  | .anonymous => "n0"
  | .str parent value => s!"ns({encodeName parent},{atom value})"
  | .num parent value => s!"nn({encodeName parent},{value})"

partial def encodeLevel : Level → String
  | .zero => "l0"
  | .succ level => s!"ls({encodeLevel level})"
  | .max left right => s!"lm({encodeLevel left},{encodeLevel right})"
  | .imax left right => s!"li({encodeLevel left},{encodeLevel right})"
  | .param name => s!"lp({encodeName name})"
  | .mvar id => s!"lv({encodeName id.name})"

def encodeBinderInfo : BinderInfo → String
  | .default => "bd"
  | .implicit => "bi"
  | .strictImplicit => "bs"
  | .instImplicit => "bc"

def encodeLiteral : Literal → String
  | .natVal value => s!"ln({value})"
  | .strVal value => s!"lt({atom value})"

partial def encodeExpr : Expr → String
  | .bvar index => s!"eb({index})"
  | .fvar id => s!"ef({encodeName id.name})"
  | .mvar id => s!"em({encodeName id.name})"
  | .sort level => s!"es({encodeLevel level})"
  | .const name levels =>
      s!"ec({encodeName name},[{String.intercalate "," (levels.map encodeLevel)}])"
  | .app function argument => s!"ea({encodeExpr function},{encodeExpr argument})"
  | .lam _ type body binderInfo =>
      s!"el({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
  | .forallE _ type body binderInfo =>
      s!"ep({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
  | .letE _ type value body nondependent =>
      s!"ee({if nondependent then "1" else "0"},{encodeExpr type},{encodeExpr value},{encodeExpr body})"
  | .lit literal => s!"ei({encodeLiteral literal})"
  | .mdata _ body => s!"ed({encodeExpr body})"
  | .proj name index body => s!"ej({encodeName name},{index},{encodeExpr body})"

def encodeStatement (info : ConstantInfo) : String :=
  let parameters := info.levelParams.map encodeName
  let header :=
    s!"statement-v1(uparams=[{String.intercalate "," parameters}],type={encodeExpr info.type}"
  match info with
  | .defnInfo _ | .opaqueInfo _ =>
      match info.value? (allowOpaque := true) with
      | some value => header ++ s!",value={encodeExpr value})"
      | none => header ++ ",value=missing)"
  | _ => header ++ ")"

def includeInStatement (name : Name) : ConstantInfo → Bool
  | .thmInfo _ => !(privateToUserName name).isInternalDetail
  | _ => true

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def sortedUnique (values : Array String) : Array String :=
  (values.qsort (· < ·)).foldl (init := #[]) fun result value =>
    if result.back? == some value then result else result.push value

def inspectModule (env : Environment) (input : ModuleInput) : IO ModuleReport := do
  let moduleName := input.moduleName.toName
  let some moduleIdx := env.getModuleIdx? moduleName
    | throw <| IO.userError s!"module not loaded: {input.moduleName}"
  let moduleData := env.header.moduleData[moduleIdx]!
  let context : Lean.Core.Context := { fileName := "", fileMap := default, options := {} }
  let state : Lean.Core.State := { env }
  let action : Lean.Core.CoreM (Array DeclarationReport) := moduleData.constNames.mapM fun name => do
    let env ← getEnv
    let some info := env.setExporting false |>.find? name
      | throwError "declaration missing: {name}"
    let axioms ← Lean.collectAxioms name
    return {
      axioms := sortedUnique (axioms.map Name.toString)
      includeInStatement := includeInStatement name info
      kind := kindOf info
      name := name.toString
      nameKey := encodeName name
      type := encodeStatement info
    }
  let declarations ← Prod.fst <$> Lean.Core.CoreM.toIO action context state
  return {
    declarations := declarations.qsort (fun left right => left.nameKey < right.nameKey)
    imports := sortedUnique (moduleData.imports.map (fun item => item.module.toString))
    moduleName := input.moduleName
    sourcePath := input.sourcePath
    sourceSha256 := input.sourceSha256
  }

def hexDigit (value : Nat) : Char :=
  Char.ofNat <| if value < 10 then '0'.toNat + value else 'A'.toNat + value - 10

def hex4 (value : Nat) : String :=
  String.ofList [
    hexDigit ((value / 4096) % 16),
    hexDigit ((value / 256) % 16),
    hexDigit ((value / 16) % 16),
    hexDigit (value % 16)
  ]

def jsonCharacter (character : Char) : String :=
  let scalar := character.toNat
  if scalar ≤ 0xffff then
    let encoded := (toJson (String.ofList [character])).compress
    ((encoded.drop 1).dropEnd 1).toString
  else
    let offset := scalar - 0x10000
    let high := 0xd800 + offset / 0x400
    let low := 0xdc00 + offset % 0x400
    "\\u" ++ hex4 high ++ "\\u" ++ hex4 low

def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonCharacter) ++ "\""

def renderStrings (values : Array String) : String :=
  "[" ++ String.intercalate ", " (values.toList.map jsonString) ++ "]"

def renderDeclaration (declaration : DeclarationReport) : String :=
  "{\"axioms\": " ++ renderStrings declaration.axioms
    ++ ", \"include_in_statement\": "
    ++ (if declaration.includeInStatement then "true" else "false")
    ++ ", \"kind\": " ++ jsonString declaration.kind
    ++ ", \"name\": " ++ jsonString declaration.name
    ++ ", \"name_key\": " ++ jsonString declaration.nameKey
    ++ ", \"type\": " ++ jsonString declaration.type ++ "}"

def renderModule (report : ModuleReport) : String :=
  "{\"declarations\": ["
    ++ String.intercalate ", " (report.declarations.toList.map renderDeclaration)
    ++ "], \"imports\": " ++ renderStrings report.imports
    ++ ", \"module\": " ++ jsonString report.moduleName
    ++ ", \"source_path\": " ++ jsonString report.sourcePath
    ++ ", \"source_sha256\": " ++ jsonString report.sourceSha256 ++ "}"

def renderReport (reports : Array ModuleReport) : String :=
  "{\"modules\": [" ++ String.intercalate ", " (reports.toList.map renderModule)
    ++ "], \"schema\": \"stratalint-raw-lean-report-v1\"}\n"

def parseModuleInputs : List String → Except String (Array ModuleInput)
  | [] => .ok #[]
  | moduleName :: sourcePath :: sourceSha256 :: rest => do
      let tail ← parseModuleInputs rest
      return #[{ moduleName, sourcePath, sourceSha256 }] ++ tail
  | _ => .error "module arguments must be repeated triples: MODULE SOURCE_PATH SOURCE_SHA256"

def parseArguments : List String → Except String (System.FilePath × Array ModuleInput)
  | "--output" :: output :: rest => do
      let inputs ← parseModuleInputs rest
      if inputs.isEmpty then
        throw "at least one module is required"
      return (output, inputs.qsort (fun left right => left.moduleName < right.moduleName))
  | _ => .error "usage: Inspector.lean --output FILE MODULE SOURCE_PATH SOURCE_SHA256 [...]"

unsafe def main (args : List String) : IO Unit := do
  let (output, inputs) ← match parseArguments args with
    | .ok parsed => pure parsed
    | .error message => throw <| IO.userError message
  initSearchPath (← findSysroot)
  let imports := inputs.map fun input => { module := input.moduleName.toName }
  let env ← importModules imports {} (trustLevel := 0)
  let reports ← inputs.mapM (inspectModule env)
  IO.FS.writeFile output (renderReport reports)
