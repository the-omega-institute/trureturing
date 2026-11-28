import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Typed registration of source operands for the root and optical models. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.UnitSixO

abbrev operandSignature (X Y : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => X) (fun _ => Y)

macro "unitFamily% " arena:term:max source:term:max actual:term:max
    bad:term:max rejected:term:max witness:term:max : term =>
  `({ actual := $actual
      bridge := Iff.rfl
      variation := ⟨$source, $bad, $rejected⟩
      sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
        ($arena).Law $actual $bad $rejected
      dependence := fun _ => $witness })

macro "unitBindE8% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max readouts:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.E8RootSystemUnification4D
        definition := none
        coordinates := $coordinates
        readouts := $readouts }
      continuation := .unknown
      familyRecord := none
      options := #[] })

macro "unitBindOptics% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max readouts:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
        definition := none
        coordinates := $coordinates
        readouts := $readouts }
      continuation := .unknown
      familyRecord := none
      options := #[] })

end Reg.Support.UnitSixO

open Lean Elab Term in
/-- Locate a selected occurrence in the elaborated theorem telescope. -/
elab "unitPath% " source:ident head:ident arity:num occurrence:num : term => do
  let sourceName ← resolveGlobalConstNoOverload source
  let headName ← resolveGlobalConstNoOverload head
  let info ← getConstInfo sourceName
  let wantedArity := arity.getNat
  let wantedOccurrence := occurrence.getNat
  let rec search (e : Expr) (path : Array String) (fuel seen : Nat) :
      Option (Array String) × Nat := match fuel with
    | 0 => (none, seen)
    | fuel + 1 => Id.run do
      let mut seen := seen
      if e.getAppFn.constName? == some headName && e.getAppNumArgs == wantedArity then
        if seen == wantedOccurrence then return (some path, seen)
        seen := seen + 1
      let children := match e with
        | .app f a => #[("fn", f), ("arg", a)]
        | .lam _ d b _ | .forallE _ d b _ => #[("domain", d), ("body", b)]
        | .letE _ d v b _ => #[("type", d), ("value", v), ("body", b)]
        | .mdata _ b | .proj _ _ b => #[("body", b)]
        | _ => #[]
      for (step, child) in children do
        let (found, count) := search child (path.push step) fuel seen
        if found.isSome then return (found, count)
        seen := count
      return (none, seen)
  let (some path, _) := search info.type #[] 256 0
    | throwError "No matching source occurrence"
  return toExpr path

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily in
macro "unitObserve% " f:term:max : term =>
  `(realize (_root_.Reg.Support.UnitSixO.operandSignature _ _)
      (fun _ _ x => $f x) (fun e => nomatch e))
