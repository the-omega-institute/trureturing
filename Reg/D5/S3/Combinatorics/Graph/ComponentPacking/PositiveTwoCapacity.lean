import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity

open _root_.D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Σ C : ℕ, (Fin C → ℕ)
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => p.2 i + 1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (p : signature.Params) (_ : Fin p.1) => 4)
    (fun e => nomatch e)

/-- All original parameters and positivity hypotheses remain in the law. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (C : ℕ) (ell : Fin C → ℕ), (∀ i, 1 ≤ ell i) →
    ∃ A : Finset (Fin C),
      (∑ i ∈ A, R.readout () ⟨C, ell⟩ i) ≤ (∑ i, ell i) ∧
      (∑ i ∈ Finset.univ \ A, (ell i + 1)) ≤ (∑ i, ell i) + 1

def registration : Registration arena (type_of% (@positive_two_capacity)) := by
  classical
  have hbad : ¬ arena.Law rejected := by
    intro h
    obtain ⟨A, hA, hB⟩ := h 2 (fun _ => 1) (fun _ => Nat.le_refl 1)
    change (∑ _i ∈ A, (4 : ℕ)) ≤ (∑ _i : Fin 2, (1 : ℕ)) at hA
    change (∑ _i ∈ Finset.univ \ A, (2 : ℕ)) ≤ (∑ _i : Fin 2, (1 : ℕ)) + 1 at hB
    have count := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp at hA hB count
    omega
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨positive_two_capacity, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨2, fun j => j.val + 1⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change (0 : ℕ) + 1 + 1 ≠ 1 + 1 + 1
  decide

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positive_two_capacity)
    (type_of% (realize signature
      (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => p.2 i + 1)
      (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity.positive_two_capacity
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => p.2 i + 1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg",
        "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity
