import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
import Reg.Support.DependentFamily

/-! The stored readout is the frozen logarithmic discrepancy profile. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss


open _root_.D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => discrepancyProfile x) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R :=
    Summable (fun x : ℤ => discrepancyProfile x ^ 2) ∧
    (∀ x : ℤ, Summable (lossSummand x)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℤ, lossConvolution x ≤ B * (R.readout () () x) ^ 2

private theorem lossWeight_nonneg_for_audit (n : ℕ) : 0 ≤ lossWeight n := by
  have hs : 0 ≤ shapeWeight n := by unfold shapeWeight rho; positivity
  have hr : 0 ≤ rho := by unfold rho; positivity
  unfold lossWeight
  split_ifs <;> linarith

private theorem profile_pos (x : ℤ) : 0 < discrepancyProfile x := by
  unfold discrepancyProfile
  have h : (1 : ℝ) < 2 + |(x : ℝ)| := by linarith [abs_nonneg (x : ℝ)]
  exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos h))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hs, B, _, hB⟩ := h
  have hb : 0 < b := by
    unfold b
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hr : 0 < rho := by unfold rho; positivity
  have hzero : 0 < lossWeight 0 := by
    have hs0 : 0 ≤ shapeWeight 0 := by unfold shapeWeight rho; positivity
    simp [lossWeight]
    linarith
  have hn (n : ℕ) : 0 ≤ lossSummand 0 n := by
    unfold lossSummand
    exact add_nonneg (mul_nonneg (lossWeight_nonneg_for_audit n) (sq_nonneg _))
      (mul_nonneg (lossWeight_nonneg_for_audit n) (sq_nonneg _))
  have hp : 0 < lossSummand 0 0 := by
    unfold lossSummand
    have hp := sq_pos_of_pos (profile_pos (0 + (0 + 1 : ℤ)))
    exact add_pos_of_pos_of_nonneg (mul_pos hzero hp)
      (mul_nonneg hzero.le (sq_nonneg _))
  have hu : 0 < lossConvolution 0 := hp.trans_le ((hs 0).le_tsum 0 (fun i _ => hn i))
  have hle : lossConvolution 0 ≤ 0 := by
    simpa [rejected, realize] using hB 0
  exact (not_le_of_gt hu) hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change discrepancyProfile 0 = discrepancyProfile 1 at h
  have hd : Real.sqrt 2 * Real.log 2 < Real.sqrt 3 * Real.log 3 := by
    have hroot : Real.sqrt 2 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hlog : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    exact mul_lt_mul hroot hlog.le (Real.log_pos (by norm_num)) (Real.sqrt_nonneg _)
  have h0 : 0 < Real.sqrt 2 * Real.log 2 :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.log_pos (by norm_num))
  have hs := one_div_lt_one_div_of_lt h0 hd
  have hlt : discrepancyProfile 1 < discrepancyProfile 0 := by
    convert hs using 1 <;> norm_num [discrepancyProfile]
  exact (ne_of_lt hlt) h.symm

def family : Registration arena (type_of% @actual_loss_convolution_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_loss_convolution_bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_loss_convolution_bound) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => discrepancyProfile x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
