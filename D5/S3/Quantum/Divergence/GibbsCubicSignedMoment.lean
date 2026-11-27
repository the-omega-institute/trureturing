import D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.GibbsCubicSignedMoment

/-- The logarithmic Bregman density at unit mass, applied to a square. -/
def squareEntropyDensity (z : ℝ) : ℝ :=
  z ^ 2 * Real.log (z ^ 2) - z ^ 2 + 1

private theorem squareEntropyDensity_nonneg (z : ℝ) : 0 ≤ squareEntropyDensity z := by
  unfold squareEntropyDensity
  linarith only [Real.self_sub_one_le_mul_log (sq_nonneg z)]

private theorem squareEntropyDensity_le_cubic {z : ℝ} (hz : 0 ≤ z) :
    squareEntropyDensity z ≤ 2 * (z - 1) ^ 2 + (2 / 3 : ℝ) * (z - 1) ^ 3 := by
  let gap (y : ℝ) : ℝ :=
    (2 / 3 : ℝ) * y ^ 3 + y ^ 2 - 2 * y + 1 / 3 - y ^ 2 * Real.log (y ^ 2)
  let gap' (y : ℝ) : ℝ := 2 * y ^ 2 - 2 - 4 * (y * Real.log y)
  have hgap (y : ℝ) (hy : 0 < y) : HasDerivAt gap (gap' y) y := by
    have hsq := hasDerivAt_pow 2 y
    have hlog := (Real.hasDerivAt_mul_log (pow_ne_zero 2 hy.ne')).comp y
      (h := fun z : ℝ => z ^ 2) hsq
    have h := (((((hasDerivAt_pow 3 y).const_mul (2 / 3 : ℝ)).add hsq).sub
      ((hasDerivAt_id' y).const_mul 2)).add_const (1 / 3)).sub hlog
    convert h using 1 <;> first | rfl | (norm_num [gap', Real.log_pow] <;> ring)
  have hgap' (y : ℝ) (hy : 0 < y) :
      HasDerivAt gap' (4 * (y - 1 - Real.log y)) y := by
    have h := (((hasDerivAt_pow 2 y).const_mul (2 : ℝ)).sub_const 2).sub
      ((Real.hasDerivAt_mul_log hy.ne').const_mul 4)
    convert h using 1 <;> first | rfl | (norm_num <;> ring)
  have hcont : Continuous gap := by
    have hlog : Continuous (fun y : ℝ => y ^ 2 * Real.log (y ^ 2)) :=
      Real.continuous_mul_log.comp (continuous_id.pow 2)
    exact (by fun_prop : Continuous (fun y : ℝ =>
      (2 / 3 : ℝ) * y ^ 3 + y ^ 2 - 2 * y + 1 / 3)).sub hlog
  have hc : ConvexOn ℝ (Set.Ici 0) gap := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := gap')
      (f'' := fun y => 4 * (y - 1 - Real.log y)) (convex_Ici 0) hcont.continuousOn ?_ ?_ ?_
    · intro y hy
      rw [interior_Ici] at hy
      exact (hgap y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hgap' y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.log_le_sub_one_of_pos hy))
  have h1 : (1 : ℝ) ∈ interior (Set.Ici 0) := by
    rw [interior_Ici]
    exact Set.mem_Ioi.mpr zero_lt_one
  have hd1 : HasDerivAt gap 0 1 := by
    simpa [gap'] using hgap 1 zero_lt_one
  have hmin := hc.isMinOn_of_rightDeriv_eq_zero h1
    (hd1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 1))
  have hzero : gap 1 = 0 := by norm_num [gap, Real.log_one]
  have hnonneg : 0 ≤ gap z := by
    simpa only [hzero] using (isMinOn_iff.mp hmin z hz)
  calc
    squareEntropyDensity z ≤ squareEntropyDensity z + gap z := le_add_of_nonneg_right hnonneg
    _ = _ := by
      simp only [squareEntropyDensity, gap]
      ring

private theorem scale_log_density {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    a * ((y / a) * Real.log (y / a) - y / a + 1) =
      y * Real.log y - y * Real.log a - y + a := by
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_div hy ha]
  field_simp [ha] <;> ring

/-- Exact subtraction of the scalar mass term after rescaling by a positive reference `t`. -/
theorem squareEntropy_normalization {ι : Type*} [Fintype ι] (pi x : ι → ℝ)
    (hpi : ∀ i, 0 ≤ pi i) (hmass : (∑ i, pi i) = 1) {t : ℝ} (ht : 0 < t) :
    let S := ∑ i, pi i * x i ^ 2
    (∑ i, pi i * x i ^ 2 * Real.log (x i ^ 2)) - S * Real.log S =
      t ^ 2 * ((∑ i, pi i * squareEntropyDensity (x i / t)) -
        squareEntropyDensity (Real.sqrt S / t)) := by
  intro S
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hpi i) (sq_nonneg _)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hsum :
      t ^ 2 * (∑ i, pi i * squareEntropyDensity (x i / t)) =
        (∑ i, pi i * x i ^ 2 * Real.log (x i ^ 2)) -
          S * Real.log (t ^ 2) - S + t ^ 2 := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, (pi i * x i ^ 2 * Real.log (x i ^ 2) -
            (pi i * x i ^ 2) * Real.log (t ^ 2) - pi i * x i ^ 2 + pi i * t ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_left_comm (t ^ 2), squareEntropyDensity, div_pow, scale_log_density ht2]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          hmass, one_mul, S]
  have hscalar : t ^ 2 * squareEntropyDensity (Real.sqrt S / t) =
      S * Real.log S - S * Real.log (t ^ 2) - S + t ^ 2 := by
    rw [squareEntropyDensity, div_pow, Real.sq_sqrt hS, scale_log_density ht2]
  rw [mul_sub, hsum, hscalar]
  ring

/-- For a finite probability and a nonnegative observable of positive mean, its square
entropy is controlled by the variance and the signed third central moment. -/
theorem squareEntropy_le_signedThirdMoment {ι : Type*} [Fintype ι] (pi x : ι → ℝ)
    (hpi : ∀ i, 0 ≤ pi i) (hmass : (∑ i, pi i) = 1)
    (hx : ∀ i, 0 ≤ x i) (ht : 0 < ∑ i, pi i * x i) :
    let t := ∑ i, pi i * x i
    let S := ∑ i, pi i * x i ^ 2
    (∑ i, pi i * x i ^ 2 * Real.log (x i ^ 2)) - S * Real.log S ≤
      2 * (∑ i, pi i * (x i - t) ^ 2) + (2 / (3 * t)) * (∑ i, pi i * (x i - t) ^ 3) := by
  intro t S
  change 0 < t at ht
  have hpoint (i : ι) : t ^ 2 * squareEntropyDensity (x i / t) ≤
      2 * (x i - t) ^ 2 + (2 / (3 * t)) * (x i - t) ^ 3 := by
    calc
      _ ≤ t ^ 2 * (2 * (x i / t - 1) ^ 2 + (2 / 3 : ℝ) * (x i / t - 1) ^ 3) :=
        mul_le_mul_of_nonneg_left
          (squareEntropyDensity_le_cubic (div_nonneg (hx i) ht.le)) (sq_nonneg t)
      _ = _ := by field_simp [ht.ne'] <;> ring
  calc
    _ = t ^ 2 * ((∑ i, pi i * squareEntropyDensity (x i / t)) -
        squareEntropyDensity (Real.sqrt S / t)) :=
      squareEntropy_normalization pi x hpi hmass ht
    _ ≤ t ^ 2 * (∑ i, pi i * squareEntropyDensity (x i / t)) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (squareEntropyDensity_nonneg _)) (sq_nonneg t)
    _ ≤ ∑ i, pi i * (2 * (x i - t) ^ 2 + (2 / (3 * t)) * (x i - t) ^ 3) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [mul_left_comm (t ^ 2)]
      exact mul_le_mul_of_nonneg_left (hpoint i) (hpi i)
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring

open GibbsCubicTranslationEntropy (spectralWeight spectralRatio)
open SpectralCeilingRelativeEntropy (overlap trace_cfc_product)

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectralRatio_power_moment (B M : Matrix n n ℂ)
    (hB : B.PosDef) (hM : M.IsHermitian) (k : ℕ) (hk : k ≤ 3) :
    (∑ p, spectralWeight hB.isHermitian hM p * spectralRatio hB.isHermitian hM p ^ k) =
      (B ^ (3 - k) * M ^ k).trace.re := by
  rw [Fintype.sum_prod_type, ← cfc_pow_id (R := ℝ) B (3 - k) hB.isHermitian.isSelfAdjoint,
    ← cfc_pow_id (R := ℝ) M k hM.isSelfAdjoint,
    trace_cfc_product B M hB.isHermitian hM (fun b => b ^ (3 - k)) (fun m => m ^ k)]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  let b := hB.isHermitian.eigenvalues i
  let m := hM.eigenvalues j
  let w := overlap hB.isHermitian hM i j
  change b ^ 3 * w * (m / b) ^ k = b ^ (3 - k) * m ^ k * w
  have hb : b ≠ 0 := (hB.eigenvalues_pos i).ne'
  rw [div_pow, ← pow_sub_mul_pow b hk]
  field_simp [pow_ne_zero k hb] <;> ring

/-- The actual spectral law for `t • B + U` has mean `t`, and its centered second and
third moments are exactly the indicated real traces. The numerator may be singular. -/
theorem spectralPair_centeredMoments (B U : Matrix n n ℂ) (t : ℝ)
    (hB : B.PosDef) (hM : (t • B + U).IsHermitian)
    (hNorm : (B ^ 3).trace.re = 1) (hCenter : (B ^ 2 * U).trace.re = 0) :
    let pi := spectralWeight hB.isHermitian hM
    let x := spectralRatio hB.isHermitian hM
    (∑ p, pi p) = 1 ∧ (∑ p, pi p * x p) = t ∧
      (∑ p, pi p * (x p - t) ^ 2) = (B * U ^ 2).trace.re ∧
      (∑ p, pi p * (x p - t) ^ 3) = (U ^ 3).trace.re := by
  intro pi x
  let M := t • B + U
  have hmass : (∑ p, pi p) = 1 := by
    simpa only [pi, pow_zero, mul_one, Nat.sub_zero, hNorm] using
      spectralRatio_power_moment B M hB hM 0 (by norm_num)
  have hraw₁ := spectralRatio_power_moment B M hB hM 1 (by norm_num)
  have hraw₂ := spectralRatio_power_moment B M hB hM 2 (by norm_num)
  have hraw₃ := spectralRatio_power_moment B M hB hM 3 (by norm_num)
  change (∑ p, pi p * x p ^ 1) = (B ^ 2 * M ^ 1).trace.re at hraw₁
  change (∑ p, pi p * x p ^ 2) = (B ^ 1 * M ^ 2).trace.re at hraw₂
  change (∑ p, pi p * x p ^ 3) = (B ^ 0 * M ^ 3).trace.re at hraw₃
  simp only [pow_one] at hraw₁ hraw₂
  simp only [pow_zero, one_mul] at hraw₃
  have hBBB : (B * B * B).trace.re = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using hNorm
  have hBBU : (B * B * U).trace.re = 0 := by
    simpa only [pow_two] using hCenter
  have hmean : (∑ p, pi p * x p) = t := by
    rw [hraw₁]
    simp only [M, mul_add, mul_smul_comm, Matrix.trace_add, Complex.add_re,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul, pow_two, hBBB, hBBU, mul_one, add_zero]
  have hsecond : (B * M ^ 2).trace.re = t ^ 2 + (B * U ^ 2).trace.re := by
    simp only [M, pow_two, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul,
      ← Matrix.mul_assoc, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Complex.smul_re,
      smul_eq_mul, Matrix.trace_mul_cycle B U B, hBBB, hBBU]
    ring
  have hthird : (M ^ 3).trace.re = t ^ 3 + 3 * t * (B * U ^ 2).trace.re + (U ^ 3).trace.re := by
    simp only [M, pow_succ, pow_zero, one_mul, mul_add, add_mul, mul_smul_comm,
      smul_mul_assoc, smul_smul, ← Matrix.mul_assoc, Matrix.trace_add, Complex.add_re,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Matrix.trace_mul_cycle U B B,
      Matrix.trace_mul_cycle B U B, Matrix.trace_mul_cycle U B U, Matrix.trace_mul_cycle U U B,
      hBBB, hBBU]
    ring
  refine ⟨hmass, hmean, ?_, ?_⟩
  · calc
      _ = (∑ p, pi p * x p ^ 2) - (2 * t) * (∑ p, pi p * x p) +
          t ^ 2 * (∑ p, pi p) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
      _ = _ := by rw [hraw₂, hsecond, hmean, hmass]; ring
  · calc
      _ = (∑ p, pi p * x p ^ 3) - (3 * t) * (∑ p, pi p * x p ^ 2) +
          (3 * t ^ 2) * (∑ p, pi p * x p) - t ^ 3 * (∑ p, pi p) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
      _ = _ := by rw [hraw₃, hraw₂, hthird, hsecond, hmean, hmass]; ring

/-- The square entropy of the actual Nussbaum–Szkoła law along centered Gibbs
translation is bounded by the quadratic trace and the signed cubic trace. -/
theorem spectralPair_squareEntropy_le (B U : Matrix n n ℂ) {t : ℝ} (ht : 0 < t)
    (hB : B.PosDef) (hM : (t • B + U).PosSemidef)
    (hNorm : (B ^ 3).trace.re = 1) (hCenter : (B ^ 2 * U).trace.re = 0) :
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    let S := (B * (t • B + U) ^ 2).trace.re
    (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S ≤
      2 * (B * U ^ 2).trace.re + (2 / (3 * t)) * (U ^ 3).trace.re := by
  intro pi x S
  obtain ⟨hmass, hmean, hsecond, hthird⟩ :=
    spectralPair_centeredMoments B U t hB hM.isHermitian hNorm hCenter
  change (∑ p, pi p) = 1 at hmass
  change (∑ p, pi p * x p) = t at hmean
  change (∑ p, pi p * (x p - t) ^ 2) = (B * U ^ 2).trace.re at hsecond
  change (∑ p, pi p * (x p - t) ^ 3) = (U ^ 3).trace.re at hthird
  have hpi (p : n × n) : 0 ≤ pi p :=
    mul_nonneg (pow_nonneg (hB.eigenvalues_pos p.1).le 3) (sq_nonneg _)
  have hx (p : n × n) : 0 ≤ x p :=
    div_nonneg (hM.eigenvalues_nonneg p.2) (hB.eigenvalues_pos p.1).le
  have ht' : 0 < ∑ p, pi p * x p := by rwa [hmean]
  have hS : (∑ p, pi p * x p ^ 2) = S := by
    have h := spectralRatio_power_moment B (t • B + U) hB hM.isHermitian 2 (by norm_num)
    change (∑ p, pi p * x p ^ 2) = (B ^ 1 * (t • B + U) ^ 2).trace.re at h
    simpa only [pow_one] using h
  simpa only [hmean, hS, hsecond, hthird] using
    squareEntropy_le_signedThirdMoment pi x hpi hmass hx ht'

end D5.S3.Quantum.Divergence.GibbsCubicSignedMoment
