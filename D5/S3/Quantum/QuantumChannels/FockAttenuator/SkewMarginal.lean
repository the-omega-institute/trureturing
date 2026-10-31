/-
NONOPAQUE PRIVATE SOURCE SUPPLIER — UNCOMPILED.
Target snapshot: 3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e.
Target toolchain: leanprover/lean4:v4.35.0.
No compiler, tactic, kernel, build, gate, or CI execution was performed.

This file supplies proof bodies for the marginal obligation on completed skew vectors.
It does not supply physical one-photon skewness or the mixed-state/entropy joins.
The existing marginal, tensor, coefficient operator and completed carriers are used.
-/
import D5.S3.Quantum.QuantumChannels.FockAttenuator.CoefficientOperator
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.SkewMarginal
open BeamSplitter DisplacementCovariance

/-- Coordinates use the existing retained-inner/discarded-outer convention. -/
def IsSkew (W : TwoMode) : Prop := ∀ i j : ℕ, W j i = -W i j

private theorem tensor_apply (x y : Fock) (j : ℕ) : tensor x y j = y j • x := rfl

private theorem tensor_norm_sq (x y : Fock) :
    ‖tensor x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor x y)
  have hy := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht hy
  rw [ht]
  simp only [tensor_apply, norm_smul, mul_pow]
  rw [hy.summable.tsum_mul_right, hy.tsum_eq, mul_comm]

private theorem tensor_norm (x y : Fock) : ‖tensor x y‖ = ‖x‖ * ‖y‖ := by
  have h := tensor_norm_sq x y
  nlinarith [norm_nonneg (tensor x y), norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

private theorem tensor_inner (x y u v : Fock) :
    inner ℂ (tensor x y) (tensor u v) = inner ℂ x u * inner ℂ y v := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum y v]
  simp only [tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  ring

/-- The retained factor is fixed; the argument supplies the discarded factor. -/
private def retainedTensor (x : Fock) : Fock →L[ℂ] TwoMode :=
  LinearMap.mkContinuous
    { toFun := tensor x
      map_add' := by
        intro y z
        apply lp.ext
        funext j
        change (y j + z j) • x = y j • x + z j • x
        exact add_smul _ _ _
      map_smul' := by
        intro c y
        apply lp.ext
        funext j
        change (c * y j) • x = c • (y j • x)
        exact mul_smul _ _ _ }
    ‖x‖ (fun y => by change ‖tensor x y‖ ≤ ‖x‖ * ‖y‖; rw [tensor_norm])

/-- The discarded factor is fixed; the argument supplies the retained factor. -/
private def discardedTensor (x : Fock) : Fock →L[ℂ] TwoMode :=
  LinearMap.mkContinuous
    { toFun := fun y => tensor y x
      map_add' := by
        intro y z
        apply lp.ext
        funext j
        change x j • (y + z) = x j • y + x j • z
        exact smul_add _ _ _
      map_smul' := by
        intro c y
        apply lp.ext
        funext j
        change x j • (c • y) = c • (x j • y)
        exact smul_comm _ _ _ }
    ‖x‖ (fun y => by change ‖tensor y x‖ ≤ ‖x‖ * ‖y‖; rw [tensor_norm, mul_comm])

private theorem discardedTensor_apply (x y : Fock) : discardedTensor x y = tensor y x := rfl

private theorem tensor_single (x : Fock) (j : ℕ) :
    tensor x (lp.single 2 j (1 : ℂ)) = lp.single 2 j x := by
  classical
  apply lp.ext
  funext k
  by_cases hk : k = j
  · subst k
    simp only [tensor_apply, lp.single_apply_self, one_smul]
  · simp only [tensor_apply, lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 j (1 : ℂ) hk,
      lp.single_apply_ne (E := fun _ : ℕ => Fock) 2 j x hk, zero_smul]

/-- The actual completed contraction vector; no summability premise is imposed. -/
def slice (x : Fock) (W : TwoMode) : Fock :=
  ContinuousLinearMap.adjoint (retainedTensor x) W

@[simp] theorem slice_apply (x : Fock) (W : TwoMode) (j : ℕ) :
    slice x W j = inner ℂ x (W j) := by
  have h := ContinuousLinearMap.adjoint_inner_right (retainedTensor x)
    (lp.single 2 j (1 : ℂ)) W
  change inner ℂ (lp.single 2 j (1 : ℂ)) (slice x W) =
    inner ℂ (tensor x (lp.single 2 j (1 : ℂ))) W at h
  simpa only [tensor_single, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, mul_one] using h

/-- The opposite contraction is minus the first one on the whole skew sector.
Only a single absolutely convergent Hilbert inner-product sum is used. -/
private theorem discarded_adjoint_eq_neg_slice (W : TwoMode) (hW : IsSkew W)
    (x : Fock) : ContinuousLinearMap.adjoint (discardedTensor x) W = -slice x W := by
  apply lp.ext
  funext i
  have h := ContinuousLinearMap.adjoint_inner_right (discardedTensor x)
    (lp.single 2 i (1 : ℂ)) W
  have he : (ContinuousLinearMap.adjoint (discardedTensor x) W) i =
      inner ℂ (tensor (lp.single 2 i (1 : ℂ)) x) W := by
    simpa only [discardedTensor_apply, lp.inner_single_left, RCLike.inner_apply,
      map_one, one_mul, mul_one] using h
  change (ContinuousLinearMap.adjoint (discardedTensor x) W) i = -(slice x W i)
  rw [he, slice_apply, lp.inner_eq_tsum, lp.inner_eq_tsum x (W i)]
  simp only [tensor_apply, inner_smul_left, lp.inner_single_left,
    RCLike.inner_apply, map_one, one_mul, mul_one]
  calc
    (∑' j : ℕ, (starRingEnd ℂ) (x j) * W j i) =
        ∑' j : ℕ, -((starRingEnd ℂ) (x j) * W i j) := by
      apply tsum_congr
      intro j
      rw [hW i j, mul_neg]
    _ = -(∑' j : ℕ, W i j * (starRingEnd ℂ) (x j)) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro j
      rw [mul_comm]

private theorem inner_slice_zero (W : TwoMode) (hW : IsSkew W) (x : Fock) :
    inner ℂ x (slice x W) = 0 := by
  have h₁ := ContinuousLinearMap.adjoint_inner_right (retainedTensor x) x W
  have h₂ := ContinuousLinearMap.adjoint_inner_right (discardedTensor x) x W
  change inner ℂ x (slice x W) = inner ℂ (tensor x x) W at h₁
  rw [discarded_adjoint_eq_neg_slice W hW x, inner_neg_right] at h₂
  change -(inner ℂ x (slice x W)) = inner ℂ (tensor x x) W at h₂
  have hz : inner ℂ x (slice x W) = -(inner ℂ x (slice x W)) := h₁.trans h₂.symm
  have htwo : (2 : ℂ) * inner ℂ x (slice x W) = 0 := by
    calc
      (2 : ℂ) * inner ℂ x (slice x W) =
          inner ℂ x (slice x W) + inner ℂ x (slice x W) := two_mul _
      _ = -(inner ℂ x (slice x W)) + inner ℂ x (slice x W) :=
        congrArg (fun z : ℂ => z + inner ℂ x (slice x W)) hz
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The arbitrary-vector half estimate on the completed skew sector.
The zero contraction case is included. Neither W nor x is normalized. -/
theorem slice_norm_sq_le_half (W : TwoMode) (hW : IsSkew W) (x : Fock) :
    ‖slice x W‖ ^ 2 ≤ ‖W‖ ^ 2 * ‖x‖ ^ 2 / 2 := by
  let y := slice x W
  let T := tensor x y - tensor y x
  have hxy : inner ℂ x y = 0 := inner_slice_zero W hW x
  have hAB : inner ℂ (tensor x y) (tensor y x) = 0 := by
    rw [tensor_inner, hxy, zero_mul]
  have hTnorm : ‖T‖ ^ 2 = 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    dsimp only [T]
    rw [norm_sub_sq (𝕜 := ℂ), hAB, tensor_norm_sq, tensor_norm_sq]
    simp only [map_zero]
    ring
  have hA : inner ℂ (tensor x y) W = inner ℂ y y :=
    (ContinuousLinearMap.adjoint_inner_right (retainedTensor x) y W).symm
  have hB : inner ℂ (tensor y x) W = -(inner ℂ y y) := by
    rw [← discardedTensor_apply x y,
      ← ContinuousLinearMap.adjoint_inner_right,
      discarded_adjoint_eq_neg_slice W hW x, inner_neg_right]
  have hTW : inner ℂ T W = ((2 * ‖y‖ ^ 2 : ℝ) : ℂ) := by
    dsimp only [T]
    rw [inner_sub_left, hA, hB, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal]
    push_cast <;> ring
  have hcs := norm_inner_le_norm (𝕜 := ℂ) T W
  rw [hTW] at hcs
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖y‖ ^ 2)] at hcs
  have hsq : (2 * ‖y‖ ^ 2) ^ 2 ≤ (‖T‖ * ‖W‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hcs
  rw [mul_pow ‖T‖ ‖W‖ 2, hTnorm] at hsq
  by_cases hy : ‖y‖ ^ 2 = 0
  · change ‖y‖ ^ 2 ≤ _
    rw [hy]
    positivity
  · have hypos : 0 < ‖y‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hy)
    have hfact : (2 * ‖y‖ ^ 2) * (2 * ‖y‖ ^ 2) ≤
        (2 * ‖y‖ ^ 2) * (‖W‖ ^ 2 * ‖x‖ ^ 2) := by
      nlinarith only [hsq]
    have hc : 2 * ‖y‖ ^ 2 ≤ ‖W‖ ^ 2 * ‖x‖ ^ 2 :=
      le_of_mul_le_mul_left hfact (by positivity : 0 < 2 * ‖y‖ ^ 2)
    change ‖y‖ ^ 2 ≤ _
    linarith

/-- The coefficient-operator adjoint has the conjugate coordinates of slice. -/
private theorem adjoint_coefficient_norm_sq (W : TwoMode) (x : Fock) :
    ‖ContinuousLinearMap.adjoint (coefficientOperator W) x‖ ^ 2 = ‖slice x W‖ ^ 2 := by
  have h₁ := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (ContinuousLinearMap.adjoint (coefficientOperator W) x)
  have h₂ := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (slice x W)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h₁ h₂
  rw [h₁, h₂]
  apply tsum_congr
  intro j
  rw [adjoint_coefficient, slice_apply, norm_inner_symm (𝕜 := ℂ) (W j) x]

/-- Equality with the original purePartialTrace, before any skew hypothesis. -/
theorem pure_partial_trace_quadratic (W : TwoMode) (x : Fock) :
    inner ℂ x (purePartialTrace W x) = ((‖slice x W‖ ^ 2 : ℝ) : ℂ) := by
  calc
    inner ℂ x (purePartialTrace W x) = inner ℂ x
        (coefficientOperator W (ContinuousLinearMap.adjoint (coefficientOperator W) x)) := by
      rw [pure_partial_trace_eq]
      rfl
    _ = inner ℂ (ContinuousLinearMap.adjoint (coefficientOperator W) x)
        (ContinuousLinearMap.adjoint (coefficientOperator W) x) :=
      (ContinuousLinearMap.adjoint_inner_left (coefficientOperator W)
        (ContinuousLinearMap.adjoint (coefficientOperator W) x) x).symm
    _ = ((‖slice x W‖ ^ 2 : ℝ) : ℂ) := by
      simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow, adjoint_coefficient_norm_sq]

/-- Norm summation is over every discarded coordinate, on the completion. -/
theorem slice_square_sum (W : TwoMode) (x : Fock) :
    (∑' j : ℕ, ‖inner ℂ x (W j)‖ ^ 2) = ‖slice x W‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, slice_apply] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (slice x W)).tsum_eq

/-- All completed skew W and every test vector x; no cap premise. -/
theorem pure_partial_trace_half_bound (W : TwoMode) (hW : IsSkew W) (x : Fock) :
    (inner ℂ x (purePartialTrace W x)).re ≤ ‖W‖ ^ 2 * ‖x‖ ^ 2 / 2 := by
  rw [pure_partial_trace_quadratic]
  exact slice_norm_sq_le_half W hW x

/-- The equivalent explicit countable marginal estimate. -/
theorem marginal_square_sum_le_half (W : TwoMode) (hW : IsSkew W) (x : Fock) :
    (∑' j : ℕ, ‖inner ℂ x (W j)‖ ^ 2) ≤ ‖W‖ ^ 2 * ‖x‖ ^ 2 / 2 := by
  rw [slice_square_sum]
  exact slice_norm_sq_le_half W hW x

/-- The operator order cap for the existing physical marginal. -/
theorem pure_partial_trace_le (W : TwoMode) (hW : IsSkew W) :
    purePartialTrace W ≤ ((‖W‖ ^ 2 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  apply ContinuousLinearMap.le_def.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  let c : ℝ := ‖W‖ ^ 2 / 2
  have hright : inner ℂ x (((c : ℂ) • (1 : Fock →L[ℂ] Fock) - purePartialTrace W) x) =
      ((c * ‖x‖ ^ 2 - ‖slice x W‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, pure_partial_trace_quadratic]
    simp only [RCLike.ofReal_eq_complex_ofReal]
    push_cast <;> ring
  have hleft : inner ℂ (((c : ℂ) • (1 : Fock →L[ℂ] Fock) - purePartialTrace W) x) x =
      ((c * ‖x‖ ^ 2 - ‖slice x W‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hright, Complex.conj_ofReal]
  change (((inner ℂ (((c : ℂ) • (1 : Fock →L[ℂ] Fock) - purePartialTrace W) x) x).re : ℝ) : ℂ) =
      inner ℂ (((c : ℂ) • (1 : Fock →L[ℂ] Fock) - purePartialTrace W) x) x ∧
    0 ≤ (inner ℂ (((c : ℂ) • (1 : Fock →L[ℂ] Fock) - purePartialTrace W) x) x).re
  rw [hleft]
  constructor
  · rfl
  · change 0 ≤ c * ‖x‖ ^ 2 - ‖slice x W‖ ^ 2
    have h := slice_norm_sq_le_half W hW x
    dsimp only [c]
    nlinarith only [h]

/-- The normalized marginal is bounded by one half of the actual identity. -/
theorem pure_partial_trace_le_half (W : TwoMode) (hW : IsSkew W) (hunit : ‖W‖ = 1) :
    purePartialTrace W ≤ ((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  simpa only [hunit, one_pow] using pure_partial_trace_le W hW

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.SkewMarginal
