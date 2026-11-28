import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.E6TrinificationUnification4D
import Reg.Support.SingleDependentReadout

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

macro "e6Family% " arena:term:max source:term:max actual:term:max witness:term:max
    bad:term:max rejected:term:max : term =>
  `({ actual := $actual
      bridge := Iff.rfl
      variation := ⟨$source, $bad, $rejected⟩
      sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
        ($arena).Law $actual $bad $rejected
      dependence := fun _ => $witness })

macro "e6Bind% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max path:term:max state:term:max function:term:max
    operand:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := { stage := .evidence, objectStage := .evidence }
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.E6TrinificationUnification4D
        definition := none
        coordinates := $coordinates
        readouts := #[{
          path := $path
          stateBinder := $state
          functionOperand := $function
          stateOperand := $operand
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D

open Lean Elab Term in
/-- Select a raw compiler occurrence and emit its literal path. -/
elab "e6Path% " source:ident head:ident arity:num occurrence:num : term => do
  let sourceName ← resolveGlobalConstNoOverload source
  let headName ← resolveGlobalConstNoOverload head
  let info ← getConstInfo sourceName
  let wantedArity := arity.getNat
  let wantedOccurrence := occurrence.getNat
  let rec search (e : Expr) (path : Array String) (fuel : Nat)
      (seen : Nat) : Option (Array String) × Nat := match fuel with
    | 0 => (none, seen)
    | fuel + 1 => Id.run do
      let mut seen := seen
      if e.getAppFn.constName? == some headName && e.getAppNumArgs == wantedArity then
        if seen == wantedOccurrence then return (some path, seen)
        seen := seen + 1
      let children := match e with
        | .app f a => #[("fn", f), ("arg", a)]
        | .lam _ _ b _ | .forallE _ _ b _ => #[("body", b)]
        | .letE _ _ v b _ => #[("value", v), ("body", b)]
        | .mdata _ b | .proj _ _ b => #[("body", b)]
        | _ => #[]
      for (step, child) in children do
        let (found, count) := search child (path.push step) fuel seen
        seen := count
        if found.isSome then return (found, seen)
      return (none, seen)
  let (some path, _) := search info.type #[] 256 0
    | throwError "The requested raw source occurrence was not found"
  return toExpr path
