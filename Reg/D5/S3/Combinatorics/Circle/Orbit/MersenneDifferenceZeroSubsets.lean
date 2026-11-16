import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.MersenneDifferenceZeroSubsets
import Reg.Support.DependentFamily

/-! # Full-domain source-family audits for Mersenne-difference zero subsets

The original positive-length telescope is retained, including exponent zero
and degenerate source vectors. Only the complete actual integer source vector
is varied; the law is neither a Boolean observation nor an assumed conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets
open scoped BigOperators

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k a => actualSource k (2 ^ a - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (1 : ℤ)) (fun e => nomatch e)

abbrev classificationArena : Arena where
  signature := signature
  Law R := ∀ (k a : ℕ) (_hk : 0 < k) (A : Finset (Fin k)),
    (∑ i ∈ A, R.readout () k a i) = 0 ↔
      A.image ((finRotate k : Equiv.Perm (Fin k)) ^ a) = A

abbrev countArena : Arena where
  signature := signature
  Law R := ∀ (k a : ℕ) (_hk : 0 < k),
    (Finset.univ.filter (fun A : Finset (Fin k) =>
      (∑ i ∈ A, R.readout () k a i) = 0)).card = 2 ^ Nat.gcd a k

private theorem rejected_classification : ¬ classificationArena.Law rejected := by
  intro h
  have hz := (h 1 0 (by decide) (Finset.univ : Finset (Fin 1))).mpr (by simp)
  norm_num [rejected, realize] at hz

private theorem rejected_count : ¬ countArena.Law rejected := by
  intro h
  have hf : (Finset.univ.filter (fun A : Finset (Fin 1) =>
      (∑ i ∈ A, rejected.readout () 1 0 i) = 0)) = {∅} := by
    ext A
    simp [rejected, realize]
  have hh := h 1 0 (by decide)
  rw [hf] at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 2)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def classification_registration : Registration classificationArena
    (type_of% (@actual_zero_iff_rotation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_iff_rotation, rejected, rejected_classification⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_classification⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def count_registration : Registration countArena
    (type_of% (@actual_zero_subsets_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_subsets_card, rejected, rejected_count⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_count⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Closed original-source selection; the current report supplies binding evidence. -/
def classification_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.actual_zero_iff_rotation)
      (type_of% (realize signature
        (fun _ k a => actualSource k (2 ^ a - 1)) (fun e => nomatch e)))
      Nat Unit := {
  unitName :=
    `D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.actual_zero_iff_rotation.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.classification_registration
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classification_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ k a => actualSource k (2 ^ a - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneDifferenceZeroSubsets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
      "body", "body", "body", "body", "fn", "arg",
      "fn", "arg", "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- Closed original-source selection; the current report supplies binding evidence. -/
def count_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.actual_zero_subsets_card)
      (type_of% (realize signature
        (fun _ k a => actualSource k (2 ^ a - 1)) (fun e => nomatch e)))
      Nat Unit := {
  unitName :=
    `D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.actual_zero_subsets_card.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets.count_registration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ k a => actualSource k (2 ^ a - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneDifferenceZeroSubsets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
      "body", "body", "body", "fn", "arg", "arg",
      "fn", "fn", "arg", "body", "fn", "arg",
      "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms classification_registration
#print axioms count_registration
#print axioms classification_audit
#print axioms count_audit

end Reg.D5.S3.Combinatorics.Circle.MersenneDifferenceZeroSubsets
