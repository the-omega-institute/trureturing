module
public import Lean

open Lean
namespace OmegaChecks.InitPort

/-- Check both complete functions in the pinned reference environment, including the
owner, universes and assumptions of the comparison proof. The caller audits the
returned strict dependencies in the generated library. -/
public def checkCertifiedFunction (strict standard : Environment) (translateTerm : Expr → Expr)
    (owner strictHelper reference agreement : Name) : IO (Array Name) := do
  let some (.defnInfo actual) := strict.find? strictHelper | throw <| IO.userError s!"missing strict function {strictHelper}"
  let some (.defnInfo ref) := standard.find? reference | throw <| IO.userError s!"missing reference function {reference}"
  let some (.thmInfo proof) := standard.find? agreement | throw <| IO.userError s!"missing equality {agreement}"
  let levels := actual.levelParams.map Level.param
  let mappedType := translateTerm actual.type
  let body := translateTerm actual.value
  let refTerm := mkConst ref.name levels
  let .ok (.sort u) := Kernel.check standard {} mappedType | throw <| IO.userError s!"invalid type for {strictHelper}"
  let equation := mkApp3 (mkConst `Eq [u]) mappedType refTerm body
  unless actual.safety == .safe && actual.all == [strictHelper] && levels.length == ref.levelParams.length &&
      proof.levelParams.length == levels.length &&
      strict.getModuleIdxFor? strictHelper == strict.getModuleIdx? (owner.replacePrefix `Init `OmegaInit) &&
      Kernel.isDefEqGuarded standard {} mappedType (ref.type.instantiateLevelParams ref.levelParams levels) &&
      Kernel.isDefEqGuarded standard {} equation (proof.type.instantiateLevelParams proof.levelParams levels) do
    throw <| IO.userError s!"{strictHelper} does not implement {reference}"
  let axs ← (collectAxioms proof.name : CoreM _).toIO' {fileName := "<function correspondence>", fileMap := default} {env := standard}
  unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throw <| IO.userError s!"unexpected assumption in {agreement}"
  return actual.type.getUsedConstants ++ actual.value.getUsedConstants

end OmegaChecks.InitPort
