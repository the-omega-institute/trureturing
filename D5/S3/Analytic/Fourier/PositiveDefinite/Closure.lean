/- GID: D5/S3/Analytic/Fourier/PositiveDefinite/Closure
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefinite/Closure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap]
   utility: none
   digest: Algebraic, integral and limit closure of positive definite functions on the real line. -/

import D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Closure operations for finite translation Gram matrices. -/

noncomputable section
open Matrix Filter MeasureTheory
open scoped BigOperators Topology ComplexOrder MatrixOrder
open D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion

namespace D5.S3.Analytic.Fourier.PositiveDefinite.Closure

/-- Nonnegative real scaling preserves positive definiteness. -/
theorem smul {f : ℝ → ℂ} (hf : PositiveDefinite f) {a : ℝ} (ha : 0 ≤ a) :
    PositiveDefinite (fun t => (a : ℂ) * f t) := by
  intro m x
  exact (hf m x).smul ha

/-- Finite sums preserve positive definiteness. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, PositiveDefinite (f i)) :
    PositiveDefinite (fun t => ∑ i ∈ s, f i t) := by
  intro m x
  have he : (fun i j => ∑ k ∈ s, f k (x j - x i)) =
      ∑ k ∈ s, (fun i j => f k (x j - x i)) := by ext; simp
  rw [he]
  exact Matrix.posSemidef_sum s (fun i hi => hf i hi m x)

/-- The Schur product theorem applied to translation kernels. -/
theorem mul {f g : ℝ → ℂ} (hf : PositiveDefinite f) (hg : PositiveDefinite g) :
    PositiveDefinite (fun t => f t * g t) := fun m x => (hf m x).hadamard (hg m x)

/-- Arbitrary real dilations preserve positive definiteness. -/
theorem dilation {f : ℝ → ℂ} (hf : PositiveDefinite f) (a : ℝ) :
    PositiveDefinite (fun t => f (a * t)) := by
  intro m x
  simpa only [mul_sub] using hf m (fun i => a * x i)

/-- Pointwise limits preserve every finite Gram inequality. -/
theorem limit {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ i, PositiveDefinite (f i)) (hlim : ∀ t, Tendsto (fun i => f i t) l (𝓝 (g t))) :
    PositiveDefinite g := by
  intro m x
  apply Matrix.posSemidef_is_closed.mem_of_tendsto
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hlim (x j - x i))
  exact Filter.Eventually.of_forall fun i => hf i m x

/-- Characters are rank-one Gram kernels. -/
theorem character (s : ℝ) :
    PositiveDefinite (fun t => Complex.exp ((s * t : ℝ) * Complex.I)) := by
  intro m x
  have he : (fun i j : Fin m => Complex.exp ((s * (x j - x i) : ℝ) * Complex.I)) =
      Matrix.vecMulVec (star (fun i => Complex.exp ((s * x i : ℝ) * Complex.I)))
        (fun i => Complex.exp ((s * x i : ℝ) * Complex.I)) := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def,
      ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  rw [he]
  exact Matrix.posSemidef_vecMulVec_star_self
    (fun i : Fin m => Complex.exp ((s * x i : ℝ) * Complex.I))

/-- The real cosine is the average of two opposite characters. -/
theorem cos (s : ℝ) : PositiveDefinite (fun t => (Real.cos (s * t) : ℂ)) := by
  have h := smul (sum (Finset.univ : Finset (Fin 2))
    (f := fun i t => Complex.exp (((if i = 0 then s else -s) * t : ℝ) * Complex.I))
    (by intro i hi; exact character _)) (a := 1 / 2) (by norm_num)
  convert h using 1
  funext t
  simp only [Fin.sum_univ_two, Fin.isValue, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [show ((-s * t : ℝ) : ℂ) * Complex.I = -((s * t : ℝ) * Complex.I) by push_cast; ring]
  rw [Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast
  simp only [neg_mul]
  ring

/-- Nonnegative constants are positive definite. -/
theorem const {a : ℝ} (ha : 0 ≤ a) : PositiveDefinite (fun _ => (a : ℂ)) := by
  simpa using smul (character 0) ha

/-- Natural pointwise powers preserve positive definiteness. -/
theorem pow {f : ℝ → ℂ} (hf : PositiveDefinite f) (n : ℕ) :
    PositiveDefinite (fun t => f t ^ n) := by
  induction n with
  | zero => simpa using (const (a := 1) (by norm_num))
  | succ n ih => simpa only [pow_succ] using mul ih hf

/-- The pointwise exponential follows from nonnegative Schur powers. -/
theorem exp {f : ℝ → ℂ} (hf : PositiveDefinite f) :
    PositiveDefinite (fun t => Complex.exp (f t)) := by
  apply limit (l := atTop)
    (f := fun N t => ∑ k ∈ Finset.range N, ((k.factorial : ℝ)⁻¹ : ℂ) * f t ^ k)
  · intro N
    apply sum
    intro k hk
    simpa using smul (pow hf k) (a := (k.factorial : ℝ)⁻¹)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · intro t
    rw [Complex.exp_eq_exp_ℂ]
    have H := (NormedSpace.expSeries_div_hasSum_exp (f t)).tendsto_sum_nat
    simpa only [div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_natCast, mul_comm]
      using H

/-- Integration against a positive measure preserves positive definiteness. -/
theorem integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ → ℂ}
    (hf : ∀ᵐ a ∂μ, PositiveDefinite (f a))
    (hi : ∀ t, Integrable (fun a => f a t) μ) :
    PositiveDefinite (fun t => ∫ a, f a t ∂μ) := by
  intro m x
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (∫ a, f a (x i - x j) ∂μ) = ∫ a, f a (x j - x i) ∂μ
    change (starRingEnd ℂ) (∫ a, f a (x i - x j) ∂μ) = _
    rw [← integral_conj]
    exact integral_congr_ae (hf.mono fun a ha => (ha m x).isHermitian.apply i j)
  · intro c
    have H : 0 ≤ ∫ a, (∑ i : Fin m, ∑ j : Fin m,
        star (c i) * (f a (x j - x i) * c j)) ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hf] with a ha
      change 0 ≤ ∑ i : Fin m, ∑ j : Fin m, star (c i) * (f a (x j - x i) * c j)
      simpa only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum] using
        (ha m x).dotProduct_mulVec_nonneg c
    have hh (i j : Fin m) : Integrable
        (fun a => star (c i) * (f a (x j - x i) * c j)) μ :=
      ((hi _).mul_const _).const_mul _
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hh i j))] at H
    simp_rw [integral_finsetSum _ (fun j _ => hh _ j), integral_const_mul,
      integral_mul_const] at H
    simpa only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum] using H

end D5.S3.Analytic.Fourier.PositiveDefinite.Closure
