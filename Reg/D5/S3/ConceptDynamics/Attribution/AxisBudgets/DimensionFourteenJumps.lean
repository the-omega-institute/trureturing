import D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Observe the budget charge of a fourteen-coordinate edge table. -/

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := Fin 14
  State i := AxisSubset 14 i → AxisSubset 14 i → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ i f => axisCost i f) (fun a => nomatch a)

private def zeroCharge : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i : Fin 14) (f : AxisSubset 14 i → AxisSubset 14 i → Bool) (selected : Bool),
    (∀ A, residualDegree 3 selected (decide (A = axisTop i)) (∑ B, (f A B).toNat)) →
    (∀ B, residualDegree 3 selected (decide (B = axisTop i)) (∑ A, (f A B).toNat)) →
    (∀ A B, A ≠ axisTop i → f A B = true → A.val ⊆ B.val) →
    R.readout () i f ≤ 640 →
    2 ≤ (rankJumps (fun A => A.val.card) (axisTop i) f).card

private def diagonalTable {d : ℕ} (i : Fin d) (A B : AxisSubset d i) : Bool :=
  decide (A = B ∧ A ≠ axisTop i)

private theorem diagonal_row {d : ℕ} (i : Fin d) (A : AxisSubset d i) :
    residualDegree 3 true (decide (A = axisTop i)) (∑ B, (diagonalTable i A B).toNat) := by
  by_cases hA : A = axisTop i
  · simp [diagonalTable, hA, residualDegree]
  · have weight (B : AxisSubset d i) : (diagonalTable i A B).toNat =
        if A = B then 1 else 0 := by
      by_cases equal : A = B
      · subst B
        simp [diagonalTable, hA]
      · simp [diagonalTable, equal]
    simp [weight, hA, residualDegree]

private theorem diagonal_col {d : ℕ} (i : Fin d) (B : AxisSubset d i) :
    residualDegree 3 true (decide (B = axisTop i)) (∑ A, (diagonalTable i A B).toNat) := by
  have symmetric (A : AxisSubset d i) : diagonalTable i A B = diagonalTable i B A := by
    by_cases h : A = B
    · simp [h]
    · simp [diagonalTable, h, Ne.symm h]
  simpa only [symmetric] using diagonal_row i B

private theorem diagonal_support {d : ℕ} (i : Fin d) (A B : AxisSubset d i)
    (_ : A ≠ axisTop i) (entry : diagonalTable i A B = true) : A.val ⊆ B.val := by
  simp only [diagonalTable, decide_eq_true_eq] at entry
  rw [entry.1]

private theorem diagonal_jumps_empty {d : ℕ} (i : Fin d) :
    rankJumps (fun A : AxisSubset d i => A.val.card) (axisTop i) (diagonalTable i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨A, B⟩ entry
  have h := (mem_filter.mp entry).2
  have support := h.2.2
  simp only [diagonalTable, decide_eq_true_eq] at support
  have span := h.2.1
  change A.val.card + 1 < B.val.card at span
  rw [support.1] at span
  omega

private theorem zero_charge_fails : ¬ arena.Law zeroCharge := by
  intro law
  let i : Fin 14 := 0
  have budget : zeroCharge.readout () i (diagonalTable i) ≤ 640 := by
    change 0 ≤ 640
    decide
  have failure := law i (diagonalTable i) true (diagonal_row i) (diagonal_col i)
    (diagonal_support i) budget
  rw [diagonal_jumps_empty, card_empty] at failure
  omega

private theorem actual_cost_changes {d : ℕ} (i : Fin d) (x : AxisSubset d i)
    (rank_x : x.val.card = 1) (not_top : x ≠ axisTop i) :
    axisCost i (fun _ _ => false) ≠ axisCost i (fun _ _ => true) := by
  let charge (a b : AxisSubset d i) : ℕ :=
    if a ≠ axisTop i ∧ a.val.card % 2 = 1 ∧ b.val.card % 2 = 1 then 1 else 0
  have positive : 1 ≤ ∑ a, ∑ b, charge a b := by
    calc
      1 = charge x x := by simp [charge, not_top, rank_x]
      _ ≤ ∑ b, charge x b := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)
      _ ≤ ∑ a, ∑ b, charge a b :=
        single_le_sum (f := fun a => ∑ b, charge a b) (fun _ _ => Nat.zero_le _) (mem_univ x)
  have noCost : axisCost i (fun _ _ => false) = 4 := by simp [axisCost]
  rw [noCost]
  change 4 ≠ 4 * (1 + ∑ a, ∑ b, charge a b)
  omega

def family : Registration arena (type_of% @two_jumps_at_640) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_jumps_at_640, zeroCharge, zero_charge_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨zeroCharge, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, zero_charge_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    intro role
    let x : AxisSubset 14 (0 : Fin 14) := ⟨{1}, by decide⟩
    have rank_x : x.val.card = 1 := by simp [x]
    have not_top : x ≠ axisTop (0 : Fin 14) := by
      intro equal
      have in_top : (2 : Fin 14) ∈ (axisTop (0 : Fin 14)).val := by simp [axisTop]
      rw [← equal] at in_top
      simp [x] at in_top
    refine ⟨(0 : Fin 14), fun _ _ => false, fun _ _ => true, ?_⟩
    change axisCost (0 : Fin 14) (fun _ _ => false) ≠ axisCost (0 : Fin 14) (fun _ _ => true)
    exact actual_cost_changes (0 : Fin 14) x rank_x not_top

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_jumps_at_640) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps.charge
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ i f => axisCost i f) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionFourteenJumps
