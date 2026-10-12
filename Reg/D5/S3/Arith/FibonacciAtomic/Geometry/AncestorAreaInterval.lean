import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import Reg.Support.DependentFamily

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The two interval-sum occurrences share their actual native readout.
Parameters and states are infinite; only the two observation roles are finite. -/
@[reducible] def signature : Signature where
  Params := ℕ × ℕ
  State _ := Source
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => area t p.1 p.2) (fun e => nomatch e)

def lowerBad : Realization signature :=
  realize signature (fun i p t => if i then area t p.1 p.2 else 0) (fun e => nomatch e)

def equalityBad : Realization signature :=
  realize signature (fun i p t => if i then area t p.1 p.2+1 else area t p.1 p.2)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (t : Source) (a b : ℕ), 1 ≤ a → a ≤ b → b ≤ t.length →
    Nat.choose (b-a+1) 2 ≤ R.readout false (a,b) t ∧
    (R.readout true (a,b) t = Nat.choose (b-a+1) 2 ↔ CompleteSubtree t a b)

def familyRegistration : Registration arena
    (∀ (t : Source) (a b : ℕ), 1 ≤ a → a ≤ b → b ≤ t.length →
      Nat.choose (b-a+1) 2 ≤ area t a b ∧
      (area t a b = Nat.choose (b-a+1) 2 ↔ CompleteSubtree t a b)) := by
  have lowerBadLaw : ¬ arena.Law lowerBad := by
    intro h
    have hh := (h (.mul (.of false) (.of false)) 1 2 (by decide) (by decide) (by decide)).1
    change Nat.choose 2 2 ≤ 0 at hh
    norm_num at hh
  have equalityBadLaw : ¬ arena.Law equalityBad := by
    intro h
    have ha := ancestor_area_interval (.of false) 1 1 (by decide) (by decide) (by decide)
    have hc : CompleteSubtree (.of false) 1 1 := ha.2.mp rfl
    have hh := (h (.of false) 1 1 (by decide) (by decide) (by decide)).2.mpr hc
    change 1 = Nat.choose 1 2 at hh
    norm_num at hh
  have dependence : ObservationalDependence signature actual := by
    intro i
    refine ⟨(1,2), .mul (.mul (.of false) (.of false)) (.of false),
      .mul (.of false) (.mul (.of false) (.of false)), ?_⟩
    exact (by decide : (1 : ℕ) ≠ 2)
  exact {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ancestor_area_interval, lowerBad, lowerBadLaw⟩
  sensitivity := ⟨by
    intro i
    cases i with
    | false =>
      refine ⟨lowerBad, ?_, rfl, lowerBadLaw⟩
      intro j hj
      cases j with
      | false => exact False.elim (hj rfl)
      | true => rfl
    | true =>
      refine ⟨equalityBad, ?_, rfl, equalityBadLaw⟩
      intro j hj
      cases j with
      | false => rfl
      | true => exact False.elim (hj rfl), fun e => nomatch e⟩
  dependence := dependence }

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.ancestor_area_interval)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.ancestor_area_interval
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval,
    definition := none,
    coordinates := #[1,2],
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","arg","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval

#print axioms Reg.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval.registration
