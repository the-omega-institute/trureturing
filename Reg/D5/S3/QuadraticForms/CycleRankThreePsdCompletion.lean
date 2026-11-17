import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.CycleRankThreePsdCompletion
import Reg.Support.DependentFamily

/-! Faithful cycle criterion source-family registration. -/

open _root_.D5.S3.QuadraticForms.CycleRankThreePsdCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real
open scoped BigOperators

namespace Reg.D5.S3.QuadraticForms.CycleRankThreePsdCompletion
noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n → ℝ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => p.2 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The complete source family, varying the angular readout only. -/
abbrev arena : Arena where
  signature := signature
  Law Z := ∀ {n : ℕ} (_hn : 3 ≤ n) (a : Fin n → ℝ)
    (_ha : ∀ i, -1 ≤ a i ∧ a i ≤ 1),
    (∃ B : Matrix (Fin n) (Fin n) ℝ,
      B.PosSemidef ∧ B.rank ≤ 3 ∧ (∀ i, B i i = 1) ∧
        ∀ i, B i (finRotate n i) = a i) ↔
    ∀ F : Finset (Fin n), Odd F.card →
      (∑ i ∈ F, arccos (Z.readout () ⟨n, a⟩ i)) -
        (∑ i ∈ Finset.univ \ F, arccos (a i)) ≤
        ((F.card : ℝ) - 1) * π

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hC : ∀ F : Finset (Fin 3), Odd F.card →
      (∑ i ∈ F, arccos ((fun _ : Fin 3 => (1 : ℝ)) i)) -
      (∑ i ∈ Finset.univ \ F, arccos ((fun _ : Fin 3 => (1 : ℝ)) i)) ≤
      ((F.card : ℝ) - 1) * π := by
    intro F hF
    have hc : 1 ≤ F.card := by obtain ⟨k, hk⟩ := hF; omega
    simp only [arccos_one, Finset.sum_const_zero, sub_self]
    have hcR : (1 : ℝ) ≤ F.card := by exact_mod_cast hc
    exact mul_nonneg (sub_nonneg.mpr hcR) pi_pos.le
  have hB := (cycle_rank_three_iff (n := 3) (by omega) (fun _ => 1)
    (by intro i; norm_num)).mpr hC
  have hz := (h (n := 3) (by omega) (fun _ => 1) (by intro i; norm_num)).mp hB
    Finset.univ (by decide)
  norm_num [rejected, realize, arccos_neg_one, Fin.sum_univ_succ] at hz
  rw [arccos_neg_one] at hz
  linarith [pi_pos]

def evidence : Registration arena (type_of% @cycle_rank_three_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cycle_rank_three_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3, fun j => if j = 0 then (0 : ℝ) else 1⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cycle_rank_three_iff) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.QuadraticForms.CycleRankThreePsdCompletion.cycle_rank_three_iff.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.CycleRankThreePsdCompletion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.CycleRankThreePsdCompletion
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "fn", "arg",
        "fn", "arg", "arg", "body", "arg"]

      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.CycleRankThreePsdCompletion
