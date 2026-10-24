import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe
import Reg.Support.SingleDependentReadout

/-! The full original maximum and probe law under variation of its actual height readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open Observer.Acquisition.GlobalPortFringe
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The state is the actual register; the coordinate is the single global map. -/
abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Bool ≃ Bool) (fun _ => Source) (fun _ => Nat)

def actual : Realization signature :=
  realize signature (fun _ pi v => physicalHeight pi v)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the chosen source occurrence is abstracted; the entire source law is retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : Source) (j : Nat) (_hj : 2 ≤ j) (pi : Bool ≃ Bool),
    let v := substitution^[2*j] u
    let h := R.readout () pi v
    IsGreatest {s : Nat | physicalPresence pi (List.replicate s false) v = true} h ∧
    (∀ s : Nat, physicalPresence pi (List.replicate s false) v = true ↔ s ≤ h) ∧
    2 ≤ h ∧ h ≤ 2*j+u.length-1 ∧
    (physicalPresence pi (List.replicate (h-2) false ++ [true,false]) v = false ↔
      pi false = false) ∧
    (physicalPresence pi (List.replicate (h-2) false ++ [true,false]) v = true ↔
      pi false = true)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (.of true) 2 (by decide) (Equiv.refl Bool)).2.2.1
  change 2 ≤ 0 at he
  exact (by decide : ¬ (2 : Nat) ≤ 0) he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨Equiv.refl Bool, substitution^[4] (.of true),
    substitution^[4] (.mul (.of true) (.of true)), ?_⟩
  change (3 : Nat) ≠ 4
  decide

def family : Registration arena (type_of% (@global_port_fringe)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨global_port_fringe, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def global_port_fringe_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@global_port_fringe) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe.global_port_fringe.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms global_port_fringe_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe
