/- GID: D5/S3/Quantum/Hiai/GeometricMeanOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/GeometricMeanOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both-input monotonicity of the genuine geometric mean by contraction Jensen. -/
module

public import D5.S3.Quantum.Lieb.OperatorGeometricMean
public import D5.S3.Quantum.Lieb.LiebConcavity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

@[expose] public section

namespace HiaiGeometricMean

open LownerHeinzTheorem GeneralizedPerspectiveFunction JensenOperatorInequality

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- The genuine mean with its base in the first argument. -/
noncomputable def mean (θ : ℝ) (B A : L H) : L H :=
  CFC.conjSqrt B ((CFC.conjSqrt (Ring.inverse B) A) ^ θ)

private lemma strict_of_pd {A : L H} (hA : A ∈ pdSet) : IsStrictlyPositive A :=
  (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos A (ha := hA.1)).2 hA.2

/-- The local perspective has its base in its second argument. -/
theorem mean_eq_operatorPowerMean (θ : ℝ) {A B : L H}
    (hB : B ∈ pdSet) (hA : 0 ≤ A) :
    mean θ B A = OperatorGeometricMean.operatorPowerMean θ 1 A B := by
  have hsB := strict_of_pd hB
  have hI : CFC.sqrt (Ring.inverse B) = B ^ (-1 / 2 : ℝ) := by
    rw [CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one hsB,
      CFC.rpow_rpow B (-1) (1 / 2) (by norm_num) hsB]
    norm_num
  have hm : 0 ≤ B ^ (-1 / 2 : ℝ) * A * B ^ (-1 / 2 : ℝ) :=
    (CFC.rpow_nonneg (a := B) (y := (-1 / 2 : ℝ))).isSelfAdjoint.conjugate_nonneg hA
  unfold mean CFC.conjSqrt
  change CFC.sqrt B * (CFC.sqrt (Ring.inverse B) * A *
    CFC.sqrt (Ring.inverse B)) ^ θ * CFC.sqrt B = _
  rw [hI, CFC.sqrt_eq_rpow]
  unfold OperatorGeometricMean.operatorPowerMean GeneralizedPerspective hSqrt hInvSqrt cfcR LownerHeinzCore.cfcR
  simp only [Real.rpow_one]
  rw [← CFC.rpow_eq_cfc_real hsB.nonneg, ← CFC.rpow_eq_cfc_real hsB.nonneg,
    ← CFC.rpow_eq_cfc_real hm]

/-- Joint concavity of the genuine mean with the classical base-first convention. -/
theorem mean_jointlyConcave {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConcaveOn (pdSet (ℋ := H)) (pdSet (ℋ := H)) (mean θ) := by
  intro B₀ B₁ A₀ A₁ t hB₀ hB₁ hA₀ hA₁ ht0 ht1
  have hBm := LiebAndoTrace.pdSet_convexCombo hB₀ hB₁ ht0 ht1
  have hAm := LiebAndoTrace.pdSet_convexCombo hA₀ hA₁ ht0 ht1
  rw [mean_eq_operatorPowerMean θ hB₀ (strict_of_pd hA₀).nonneg,
    mean_eq_operatorPowerMean θ hB₁ (strict_of_pd hA₁).nonneg,
    mean_eq_operatorPowerMean θ hBm (strict_of_pd hAm).nonneg]
  exact OperatorGeometricMean.operatorPowerMean_jointlyConcaveOn_pdSet
    hθ ⟨by norm_num, by norm_num⟩ hA₀ hA₁ hB₀ hB₁ ht0 ht1

private lemma power_contraction {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {D X : L H} (hD : 0 ≤ D) (hX : star X * X ≤ 1) :
    star X * D ^ θ * X ≤ (star X * D * X) ^ θ := by
  have hf : CondIciAll.{u} (fun x : ℝ ↦ -(x ^ θ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K _ _ _ _
      exact power_Icc_zero_one_operatorConcaveOn_Ici θ hθ
    · intro x hx
      exact ((Real.continuousAt_rpow_const x θ (Or.inr hθ.1)).neg).continuousWithinAt
    · simp only [neg_nonpos]
      positivity
  have hn : ‖X‖ ≤ 1 := by
    have hn2 := (CStarAlgebra.norm_le_one_iff_of_nonneg (star X * X)
      (star_mul_self_nonneg X)).2 hX
    rw [CStarRing.norm_star_mul_self] at hn2
    nlinarith [norm_nonneg X]
  have hj := theorem_2_5_2_i_ici_all_imp_iv (ℋ := H) hf
    (IsSelfAdjoint.of_nonneg hD)
    ((StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) D).1 hD) hn
  change cfc (fun x : ℝ ↦ -(x ^ θ)) (star X * D * X) ≤
    star X * cfc (fun x : ℝ ↦ -(x ^ θ)) D * X at hj
  rw [cfc_neg, cfc_neg, ← CFC.rpow_eq_cfc_real (star_left_conjugate_nonneg hD X),
    ← CFC.rpow_eq_cfc_real hD, mul_neg, neg_mul, neg_le_neg_iff] at hj
  exact hj

/-- Increasing the second input increases the genuine mean. -/
theorem mean_mono_right {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {B A A' : L H} (hAA' : A ≤ A') : mean θ B A ≤ mean θ B A' := by
  exact CFC.conjSqrt_le_conjSqrt
    (CFC.rpow_le_rpow hθ (CFC.conjSqrt_le_conjSqrt hAA'))

/-- Increasing the positive definite base increases the genuine mean. -/
theorem mean_mono_left {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {B B' A : L H} (hB : B ∈ pdSet) (hB' : B' ∈ pdSet)
    (hA : 0 ≤ A) (hBB' : B ≤ B') : mean θ B A ≤ mean θ B' A := by
  have hsB := strict_of_pd hB
  have hsB' := strict_of_pd hB'
  let S := CFC.sqrt B
  let T := CFC.sqrt B'
  let I := CFC.sqrt (Ring.inverse B)
  let J := CFC.sqrt (Ring.inverse B')
  let D := CFC.conjSqrt (Ring.inverse B) A
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg B).isSelfAdjoint
  have hT : IsSelfAdjoint T := (CFC.sqrt_nonneg B').isSelfAdjoint
  have hI : IsSelfAdjoint I := (CFC.sqrt_nonneg (Ring.inverse B)).isSelfAdjoint
  have hJ : IsSelfAdjoint J := (CFC.sqrt_nonneg (Ring.inverse B')).isSelfAdjoint
  have hIS : I * S = 1 := by
    dsimp [I, S]
    rw [CFC.sqrt_ringInverse]
    exact Ring.inverse_mul_cancel _ (hsB.sqrt B).isUnit
  have hSI : S * I = 1 := by
    dsimp [I, S]
    rw [CFC.sqrt_ringInverse]
    exact Ring.mul_inverse_cancel _ (hsB.sqrt B).isUnit
  have hJT : J * T = 1 := by
    dsimp [J, T]
    rw [CFC.sqrt_ringInverse]
    exact Ring.inverse_mul_cancel _ (hsB'.sqrt B').isUnit
  have hTJ : T * J = 1 := by
    dsimp [J, T]
    rw [CFC.sqrt_ringInverse]
    exact Ring.mul_inverse_cancel _ (hsB'.sqrt B').isUnit
  have hD : 0 ≤ D := by
    simpa only [map_zero] using (CFC.conjSqrt_monotone (c := Ring.inverse B) hA)
  have hcontract : star (S * J) * (S * J) ≤ 1 := by
    calc
      star (S * J) * (S * J) = CFC.conjSqrt (Ring.inverse B') B := by
        simp only [star_mul, hS.star_eq, hJ.star_eq, CFC.conjSqrt_apply]
        dsimp [S, J]
        rw [← mul_assoc, mul_assoc (CFC.sqrt (Ring.inverse B')),
          CFC.sqrt_mul_sqrt_self B hsB.nonneg]
      _ ≤ CFC.conjSqrt (Ring.inverse B') B' := CFC.conjSqrt_le_conjSqrt hBB'
      _ = 1 := CFC.conjSqrt_ringInverse_self B' hsB'
  have hmiddle : star (S * J) * D * (S * J) =
      CFC.conjSqrt (Ring.inverse B') A := by
    simp only [star_mul, hS.star_eq, hJ.star_eq]
    change J * S * (I * A * I) * (S * J) = J * A * J
    calc
      _ = J * (S * I) * A * (I * S) * J := by noncomm_ring
      _ = _ := by rw [hSI, hIS]; simp
  have hj := power_contraction hθ hD hcontract
  rw [hmiddle] at hj
  have hc := hT.conjugate_le_conjugate hj
  change mean θ B A ≤ mean θ B' A
  change S * D ^ θ * S ≤ T * (CFC.conjSqrt (Ring.inverse B') A) ^ θ * T
  convert hc using 1
  simp only [star_mul, hS.star_eq, hJ.star_eq]
  symm
  calc
    _ = (T * J) * S * D ^ θ * S * (J * T) := by noncomm_ring
    _ = _ := by rw [hTJ, hJT]; simp

/-- Joint order monotonicity; no commutation of the two inputs is required. -/
theorem mean_mono {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {B B' A A' : L H} (hB : B ∈ pdSet) (hB' : B' ∈ pdSet)
    (hA : 0 ≤ A) (hBB' : B ≤ B') (hAA' : A ≤ A') :
    mean θ B A ≤ mean θ B' A' :=
  (mean_mono_left hθ hB hB' hA hBB').trans (mean_mono_right hθ hAA')

end HiaiGeometricMean
