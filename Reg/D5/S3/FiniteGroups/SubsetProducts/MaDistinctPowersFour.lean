import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
import Mathlib.Algebra.Group.PUnit
import Reg.Support.DependentFamily

namespace Reg.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

open _root_.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Type
  State G := Finset G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (G : Type) [Group G] [Finite G] (A : Finset G),
    0 < n → r.readout () G A = n →
    (∀ (x : G) (k : ℕ), 2 ≤ k → k ≤ n + 1 → orderOf x ≠ k) →
    (∀ x : G, x ∈ A →
      Nat.card {y : G // y ∈ A ∧ Subgroup.zpowers y = Subgroup.zpowers x} ≤ 4) →
    ∃ a : Fin n ≃ {x : G // x ∈ A},
      ∀ i j : Fin n, (a i : G) ^ (i.val + 1) = (a j : G) ^ (j.val + 1) → i = j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have horders (x : PUnit) (k : ℕ) (hk : 2 ≤ k) (_ : k ≤ 3) : orderOf x ≠ k := by
    rw [show x = 1 from Subsingleton.elim _ _, orderOf_one]
    omega
  have hclasses (x : PUnit) (hx : x ∈ (∅ : Finset PUnit)) :
      Nat.card {y : PUnit // y ∈ (∅ : Finset PUnit) ∧ Subgroup.zpowers y = Subgroup.zpowers x} ≤ 4 :=
    (Finset.notMem_empty x hx).elim
  obtain ⟨a, _⟩ := h 2 PUnit ∅ (by decide) rfl horders hclasses
  exact Finset.notMem_empty _ (a 0).property

def sourceRegistration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit, ∅, {1}, ?_⟩
    change (∅ : Finset PUnit).card ≠ ({1} : Finset PUnit).card
    simp

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.cardinality
  realizationName := `Reg.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
