import D5.S3.ConceptDynamics.ZfcTermRewriting.RewThreeCompat
import Lean

open Lean Elab Command

/- Bounded review evidence, not the repository extractor or an admission judge.
   Capture every constant in the two target modules and every auxiliary reached
   from their value/type constants, stopping at nonauxiliary external constants.
   Names remain exact kernel names; excluded/generated declarations get no
   invented statement identity. No live-path or full transitive-closure claim. -/
namespace CurrentPrerequisites

def deps (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]

def isAux (n : Name) : Bool := (privateToUserName n).isInternalDetail

def endpoint (env : Environment) (n : Name) : Json := Json.mkObj [
  ("name", toJson n.toString),
  ("user_name", toJson (privateToUserName n).toString),
  ("module", toJson ((env.getModuleFor? n).map Name.toString)),
  ("auxiliary", toJson (isAux n))]

elab "#current_prerequisites" : command => do
  let env ← getEnv
  let mut pending : Array Name := #[]
  for mod in #[`D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree,
      `D5.S3.ConceptDynamics.ZfcTermRewriting.RewThreeCompat] do
    let some idx := env.getModuleIdx? mod | throwError "module not loaded: {mod}"
    pending := pending ++ env.header.moduleData[idx.toNat]!.constNames
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "constant not found: {n}"
    let ds := (deps info).qsort (fun a b => a.toString < b.toString)
    let axs ← collectAxioms n
    logInfo m!"CURRENT_DEP {Json.compress (Json.mkObj [
      ("constant", endpoint env n),
      ("dependencies", toJson (ds.map (endpoint env))),
      ("axioms", toJson ((axs.map Name.toString).qsort (· < ·)))])}"
    pending := pending ++ ds.filter isAux

end CurrentPrerequisites
#current_prerequisites
