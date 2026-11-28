module
public import Lean
import Lean.Compiler.LCNF.PhaseExt
import all Lean.Environment

open Lean

namespace OmegaChecks.InitInventory

public def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

public def nativeSignatures (env : Environment) (idx : ModuleIdx) : NameSet :=
  (Compiler.LCNF.impureSigExt.getModuleEntries env idx).foldl (fun acc sig => acc.insert sig.name) {}

/-- One entry per public declaration with a body and an official native signature. -/
public structure NativeSite where
  strictDeclaration : Bool
  strictSignature : Bool

public def nativeSummary (sites : Array NativeSite) : Json :=
  Json.mkObj [("officialSignatures", toJson sites.size),
    ("strictDeclarations", toJson (sites.filter (·.strictDeclaration)).size),
    ("strictSignatures", toJson (sites.filter (·.strictSignature)).size)]

/-- A name in the unchanged official type that the kernel reports missing after
erasing exactly that axiom. An equivalent reformulation can use different proof terms. -/
public def checkedTypeAxioms (official : Environment) (info : ConstantInfo)
    (closure : Array Name) : CoreM (Array Name) := do
  if closure.isEmpty then return #[]
  let used := info.type.getUsedConstants
  let direct := closure.filter fun name => used.contains name && (official.find? name).any (·.isAxiom)
  if direct.isEmpty then return #[]
  let _ ← ofExceptKernelException (Kernel.check official {} info.type)
  let core := official.toKernelEnv
  let constants := core.constants
  for name in direct do
    let without := Environment.ofKernelEnv {core with constants := {constants with
        map₁ := constants.map₁.erase name, map₂ := constants.map₂.erase name}}
    match Kernel.check without {} info.type with
    | .error (.unknownConstant _ missing) =>
      unless missing == name do throwError "checking {info.name} without {name} missed {missing}"
    | .error err => throwError "checking {info.name} without {name}: {err.toMessageData {}}"
    | .ok _ => throwError "the unchanged type of {info.name} checked without {name}"
  return direct

end OmegaChecks.InitInventory
