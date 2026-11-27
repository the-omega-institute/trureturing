import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.ThetaVerticalPositive

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.ThetaVerticalPositive
noncomputable section

abbrev heightSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def heightActual : Realization heightSignature :=
  realize heightSignature (fun _ y t => F t (1 / 2) y) (fun e => nomatch e)

def heightRejected : Realization heightSignature :=
  realize heightSignature (fun _ y _ => y) (fun e => nomatch e)

def stationaryArena : Arena where
  signature := heightSignature
  Law R := ∀ {t : ℝ}, 0 < t →
    deriv (fun y => R.readout () y t) (Real.sqrt 3 / 2) = 0

private theorem stationary_bridge : (type_of% (@hexagonal_height_stationary)) ↔
    stationaryArena.Law heightActual := Iff.rfl

private theorem half_strict : F 2 (1 / 2) 1 < F 1 (1 / 2) 1 := by
  unfold F
  apply Summable.tsum_lt_tsum (i := (1, 0))
  · intro v
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ Q (1 / 2) 1 v := by unfold Q; positivity
    nlinarith [mul_nonneg Real.pi_pos.le hq]
  · apply Real.exp_lt_exp.mpr
    norm_num [Q]
    linarith [Real.pi_pos]
  · exact summable 2 (1 / 2) (by norm_num) (by norm_num)
  · exact summable 1 (1 / 2) (by norm_num) (by norm_num)

theorem height_dependence :
    ObservationalDependence heightSignature heightActual := by
  intro i
  exact ⟨1, 2, 1, ne_of_lt half_strict⟩

private theorem stationary_rejected : ¬ stationaryArena.Law heightRejected := by
  intro h
  have h0 := h (t := 1) (by norm_num)
  change deriv id (Real.sqrt 3 / 2) = 0 at h0
  rw [(hasDerivAt_id (Real.sqrt 3 / 2)).deriv] at h0
  norm_num at h0

def stationaryRegistration : Registration stationaryArena
    (type_of% (@hexagonal_height_stationary)) where
  actual := heightActual
  bridge := stationary_bridge
  variation := ⟨@hexagonal_height_stationary, heightRejected, stationary_rejected⟩
  sensitivity := ⟨fun i => ⟨heightRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, stationary_rejected⟩, fun e => nomatch e⟩
  dependence := height_dependence


def positiveActual : Realization heightSignature :=
  realize heightSignature (fun _ y t => verticalPositive t y) (fun e => nomatch e)

def positiveRejected : Realization heightSignature :=
  realize heightSignature (fun _ _ _ => 0) (fun e => nomatch e)

def positiveArena : Arena where
  signature := heightSignature
  Law R := ∀ {t y : ℝ}, 4 / Real.sqrt 3 ≤ Real.pi * t → Real.sqrt 3 / 2 ≤ y →
    verticalScale t y * (20 * Real.pi * t / 9) ≤ R.readout () y t

private theorem positive_bridge : (type_of% (@verticalPositive_lower)) ↔
    positiveArena.Law positiveActual := Iff.rfl

private theorem positive_at_hex : 0 < verticalPositive 1 (Real.sqrt 3 / 2) := by
  have h := verticalPositive_lower (t := 1) (y := Real.sqrt 3 / 2)
    (by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
      have hs : (3 / 2 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have hm := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg 3)
      nlinarith) le_rfl
  have hp : 0 < verticalScale 1 (Real.sqrt 3 / 2) * (20 * Real.pi * 1 / 9) := by
    dsimp [verticalScale]
    positivity
  exact hp.trans_le h

private theorem positive_dependence :
    ObservationalDependence heightSignature positiveActual := by
  intro i
  refine ⟨Real.sqrt 3 / 2, 0, 1, ?_⟩
  change verticalPositive 0 (Real.sqrt 3 / 2) ≠ verticalPositive 1 (Real.sqrt 3 / 2)
  have h0 : verticalPositive 0 (Real.sqrt 3 / 2) = 0 := by simp [verticalPositive]
  rw [h0]
  exact ne_of_lt positive_at_hex

private theorem positive_rejected : ¬ positiveArena.Law positiveRejected := by
  intro h
  have h0 := h (t := 1) (y := Real.sqrt 3 / 2)
    (by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
      have hs : (3 / 2 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have hm := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg 3)
      nlinarith) le_rfl
  have hp : 0 < verticalScale 1 (Real.sqrt 3 / 2) * (20 * Real.pi * 1 / 9) := by
    dsimp [verticalScale]
    positivity
  change _ ≤ 0 at h0
  linarith

def positiveRegistration : Registration positiveArena
    (type_of% (@verticalPositive_lower)) where
  actual := positiveActual
  bridge := positive_bridge
  variation := ⟨@verticalPositive_lower, positiveRejected, positive_rejected⟩
  sensitivity := ⟨fun i => ⟨positiveRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, positive_rejected⟩, fun e => nomatch e⟩
  dependence := positive_dependence


def differentialArena : Arena where
  signature := heightSignature
  Law R := ∀ {t y : ℝ}, 0 < t → 0 < y →
    deriv (fun b => deriv (fun z => F t (1 / 2) z) b) y +
      (2 / y) * deriv (fun z => F t (1 / 2) z) y =
        R.readout () y t - verticalNegative t y

def differentialRejected : Realization heightSignature :=
  realize heightSignature (fun _ y t => verticalPositive t y + 1) (fun e => nomatch e)

private theorem differential_bridge : (type_of% (@vertical_differential_identity)) ↔
    differentialArena.Law positiveActual := Iff.rfl

private theorem differential_rejected : ¬ differentialArena.Law differentialRejected := by
  intro h
  have h0 := h (t := 1) (y := 1) (by norm_num) (by norm_num)
  have h1 := vertical_differential_identity (t := 1) (y := 1) (by norm_num) (by norm_num)
  change _ = verticalPositive 1 1 + 1 - verticalNegative 1 1 at h0
  linarith

def differentialRegistration : Registration differentialArena
    (type_of% (@vertical_differential_identity)) where
  actual := positiveActual
  bridge := differential_bridge
  variation := ⟨@vertical_differential_identity, differentialRejected, differential_rejected⟩
  sensitivity := ⟨fun i => ⟨differentialRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, differential_rejected⟩, fun e => nomatch e⟩
  dependence := positive_dependence

end
end Reg.Support.ThetaVerticalPositive

namespace Reg.Support.ThetaVerticalTail
noncomputable section

abbrev weightedSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightedActual : Realization weightedSignature :=
  realize weightedSignature (fun _ p v => (v.2 : ℝ) ^ 2 *
    Real.exp (-Real.pi * p.1 * Q (1 / 2) p.2 v)) (fun e => nomatch e)

def weightedRejected : Realization weightedSignature :=
  realize weightedSignature (fun _ _ _ => 1) (fun e => nomatch e)

def weightedArena : Arena where
  signature := weightedSignature
  Law R := ∀ {t y : ℝ}, 0 < t → 0 < y →
    Summable (fun v : ℤ × ℤ => R.readout () ⟨t, y⟩ v)

private theorem weighted_bridge : (type_of% (@weighted_gaussian_summable)) ↔
    weightedArena.Law weightedActual := Iff.rfl

private theorem weighted_dependence :
    ObservationalDependence weightedSignature weightedActual := by
  intro i
  refine ⟨⟨1, 1⟩, (0, 0), (0, 1), ?_⟩
  dsimp [weightedActual, realize]
  simp only [Int.cast_zero, Int.cast_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_mul, one_pow, one_mul]
  exact ne_of_lt (Real.exp_pos _)

private theorem weighted_rejected : ¬ weightedArena.Law weightedRejected := by
  intro h
  have h1 := h (t := 1) (y := 1) (by norm_num) (by norm_num)
  simp [weightedRejected, realize, summable_const_iff] at h1

def weightedRegistration : Registration weightedArena
    (type_of% (@weighted_gaussian_summable)) where
  actual := weightedActual
  bridge := weighted_bridge
  variation := ⟨@weighted_gaussian_summable, weightedRejected, weighted_rejected⟩
  sensitivity := ⟨fun i => ⟨weightedRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, weighted_rejected⟩, fun e => nomatch e⟩
  dependence := weighted_dependence

end
end Reg.Support.ThetaVerticalTail

namespace Reg.Support.ThetaVerticalTail
noncomputable section

abbrev negativeSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def negativeActual : Realization negativeSignature :=
  realize negativeSignature (fun _ t y => verticalNegative t y) (fun e => nomatch e)

theorem negative_dependence :
    ObservationalDependence negativeSignature negativeActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change verticalNegative 1 0 ≠ verticalNegative 1 1
  have hz : verticalNegative 1 0 = 0 := by simp [verticalNegative]
  rw [hz]
  apply ne_of_lt
  unfold verticalNegative
  apply mul_pos (by positivity)
  apply (weighted_gaussian_summable (t := 1) (y := 1) (by norm_num)
    (by norm_num)).tsum_pos (fun v => by positivity) (0, 1)
  norm_num only [Int.cast_one, one_pow, one_mul]
  exact Real.exp_pos _

end
end Reg.Support.ThetaVerticalTail
