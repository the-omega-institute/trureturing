/- GID: D5/S3/Analytic/Laplace/ExponentialHankelPositivity
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/ExponentialHankelPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Weierstrass, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: All finite exponential Hankel matrices detect pointwise positivity of continuous signed L1 densities on an open half-line. -/

import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Positivity detected by exponential Hankel matrices

The exponential coordinate takes the open half-line into `(0,1)`.
Polynomial squares in this coordinate test the actual signed density.
Uniform approximation applies to continuous test functions on `[0,1]`,
not to an endpoint extension of the density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Laplace.ExponentialHankelPositivity

open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators

/-- The actual exponential moments, including the zeroth moment. -/
def exponentialHankel (U : ℝ) (g : ℝ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => ∫ u in Ioi U, g u * Real.exp (-((i.val + j.val : ℕ) : ℝ) * (u - U))

private def coordinate (U u : ℝ) : ℝ := Real.exp (-(u - U))

private theorem continuous_coordinate (U : ℝ) : Continuous (coordinate U) := by
  unfold coordinate
  fun_prop

private theorem coordinate_mem {U u : ℝ} (hu : U < u) :
    coordinate U u ∈ Icc (0 : ℝ) 1 := by
  exact ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (by linarith)⟩

private theorem exponential_eq_pow (U u : ℝ) (k : ℕ) :
    Real.exp (-(k : ℝ) * (u - U)) = coordinate U u ^ k := by
  rw [coordinate, ← Real.exp_nat_mul]
  congr 1
  ring

private theorem integrable_weight {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U)) {w : ℝ → ℝ} (hw : Continuous w)
    {B : ℝ} (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ ≤ B) :
    IntegrableOn (fun u => g u * w (coordinate U u)) (Ioi U) := by
  exact hg.mul_bdd (c := B)
    (hw.comp (continuous_coordinate U)).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hB _ (coordinate_mem hu))

private theorem integrable_power {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U)) (k : ℕ) :
    IntegrableOn (fun u => g u * coordinate U u ^ k) (Ioi U) := by
  apply integrable_weight hg (continuous_id.pow k) (B := 1)
  intro t ht
  change ‖t ^ k‖ ≤ 1
  rw [Real.norm_of_nonneg (pow_nonneg ht.1 _)]
  exact pow_le_one₀ ht.1 ht.2

private def coefficientPolynomial {N : ℕ} (c : Fin (N + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (c i) * Polynomial.X ^ i.val

private theorem eval_coefficientPolynomial {N : ℕ} (c : Fin (N + 1) → ℝ) (t : ℝ) :
    (coefficientPolynomial c).eval t = ∑ i, c i * t ^ i.val := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum]

private theorem polynomial_bound (p : Polynomial ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖p.eval t‖ ≤ B := by
  refine ⟨∑ i ∈ p.support, ‖p.coeff i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro t ht
  rw [Polynomial.eval_eq_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ht.1 _)]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht.1 ht.2)

private theorem integrable_polynomial_square {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U)) (p : Polynomial ℝ) :
    IntegrableOn (fun u => g u * (p.eval (coordinate U u)) ^ 2) (Ioi U) := by
  obtain ⟨B, hB, hp⟩ := polynomial_bound p
  apply integrable_weight hg (p.continuous.pow 2) (B := B ^ 2)
  intro t ht
  change ‖p.eval t ^ 2‖ ≤ B ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hp t ht) 2

private theorem quadratic_integral {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U)) (N : ℕ) (c : Fin (N + 1) → ℝ) :
    star c ⬝ᵥ (exponentialHankel U g N *ᵥ c) =
      ∫ u in Ioi U, g u * (∑ i, c i * coordinate U u ^ i.val) ^ 2 := by
  classical
  have hterm (i j : Fin (N + 1)) : IntegrableOn
      (fun u => c i * c j * (g u * coordinate U u ^ (i.val + j.val))) (Ioi U) :=
    (integrable_power hg _).const_mul _
  calc
    _ = ∑ i, ∑ j, c i * c j *
        (∫ u in Ioi U, g u * coordinate U u ^ (i.val + j.val)) := by
      simp only [dotProduct, mulVec, exponentialHankel, star_trivial,
        exponential_eq_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ∫ u in Ioi U,
        c i * c j * (g u * coordinate U u ^ (i.val + j.val)) := by
      simp_rw [integral_const_mul]
    _ = ∫ u in Ioi U, ∑ i, ∑ j,
        c i * c j * (g u * coordinate U u ^ (i.val + j.val)) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        exact (integral_finsetSum _ (fun j hj => hterm i j)).symm
      · intro i hi
        exact integrable_finsetSum _ (fun j hj => hterm i j)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, pow_add]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem polynomial_square_nonneg {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U))
    (hH : ∀ N : ℕ, (exponentialHankel U g N).PosSemidef) (p : Polynomial ℝ) :
    0 ≤ ∫ u in Ioi U, g u * (p.eval (coordinate U u)) ^ 2 := by
  have heval (t : ℝ) : p.eval t =
      ∑ i : Fin (p.natDegree + 1), p.coeff i.val * t ^ i.val := by
    rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simpa only [quadratic_integral hg, ← heval] using
    (hH p.natDegree).dotProduct_mulVec_nonneg (fun i => p.coeff i.val)

/-- Polynomial-square positivity extends to bounded continuous test squares.
Only the test function is approximated at the compactification endpoints. -/
private theorem continuous_square_nonneg {U : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi U))
    (hp : ∀ p : Polynomial ℝ,
      0 ≤ ∫ u in Ioi U, g u * (p.eval (coordinate U u)) ^ 2)
    (φ : ℝ → ℝ) (hφ : Continuous φ) {B : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t‖ ≤ B) :
    0 ≤ ∫ u in Ioi U, g u * φ (coordinate U u) ^ 2 := by
  have hex (n : ℕ) : ∃ p : Polynomial ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      |p.eval t - φ t| < 1 / ((n : ℝ) + 1) :=
    exists_polynomial_near_of_continuousOn 0 1 φ hφ.continuousOn _ (by positivity)
  choose p hnear using hex
  have hε : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => (p n).eval t) atTop (𝓝 (φ t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    exact (hnear n t ht).le
  have hpb (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(p n).eval t‖ ≤ B + 1 := by
    have he : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith [Nat.cast_nonneg (R := ℝ) n]
    calc
      ‖(p n).eval t‖ ≤ ‖(p n).eval t - φ t‖ + ‖φ t‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + B := add_le_add ((hnear n t ht).le.trans he) (hbound t ht)
      _ = _ := by ring
  have hlim : Tendsto
      (fun n => ∫ u in Ioi U, g u * ((p n).eval (coordinate U u)) ^ 2)
      atTop (𝓝 (∫ u in Ioi U, g u * φ (coordinate U u) ^ 2)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun u => ‖g u‖ * (B + 1) ^ 2)
    · intro n
      exact (integrable_polynomial_square hg (p n)).aestronglyMeasurable
    · exact hg.norm.mul_const _
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hpb n _ (coordinate_mem hu)) 2)
        (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact tendsto_const_nhds.mul ((hpt _ (coordinate_mem hu)).pow 2)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => hp (p n))

/-- A negative interior point has a continuous test square of negative integral.
Its pullback is supported where the original density is negative. -/
private theorem nonneg_of_polynomial_squares {U : ℝ} {g : ℝ → ℝ}
    (hc : ContinuousOn g (Ioi U)) (hg : IntegrableOn g (Ioi U))
    (hp : ∀ p : Polynomial ℝ,
      0 ≤ ∫ u in Ioi U, g u * (p.eval (coordinate U u)) ^ 2) :
    ∀ u ∈ Ioi U, 0 ≤ g u := by
  intro u₀ hu₀
  by_contra hn
  have hneg : g u₀ < 0 := lt_of_not_ge hn
  let t₀ := coordinate U u₀
  have ht₀ : 0 < t₀ := Real.exp_pos _
  have hinverse (u : ℝ) : U - Real.log (coordinate U u) = u := by
    rw [coordinate, Real.log_exp]
    ring
  have hcont : ContinuousAt (fun t => g (U - Real.log t)) t₀ := by
    apply (hc.continuousAt (isOpen_Ioi.mem_nhds hu₀)).comp_of_eq
      (continuousAt_const.sub (Real.continuousAt_log ht₀.ne'))
    exact hinverse u₀
  have hev : ∀ᶠ t in 𝓝 t₀, g (U - Real.log t) < 0 := by
    apply hcont (isOpen_Iio.mem_nhds ?_)
    simpa only [t₀, hinverse, mem_Iio] using hneg
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let φ : ℝ → ℝ := fun t => max 0 (δ - |t - t₀|)
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have hφnonneg (t : ℝ) : 0 ≤ φ t := le_max_left _ _
  have hφbound (t : ℝ) : ‖φ t‖ ≤ δ := by
    rw [Real.norm_of_nonneg (hφnonneg t)]
    exact max_le hδ.le (sub_le_self _ (abs_nonneg _))
  have htest := continuous_square_nonneg hg hp φ hφ
    (fun t _ => hφbound t)
  let w : ℝ → ℝ := fun u => g u * φ (coordinate U u) ^ 2
  have hwcont : ContinuousOn w (Ioi U) :=
    hc.mul ((hφ.comp (continuous_coordinate U)).continuousOn.pow 2)
  have hwint : IntegrableOn w (Ioi U) := by
    apply integrable_weight hg (hφ.pow 2) (B := δ ^ 2)
    intro t ht
    change ‖φ t ^ 2‖ ≤ δ ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hφbound t) 2
  have hwnonpos (u : ℝ) : w u ≤ 0 := by
    by_cases hzero : φ (coordinate U u) = 0
    · simp [w, hzero]
    · have hd : |coordinate U u - t₀| < δ := by
        have hpos : 0 < φ (coordinate U u) :=
          lt_of_le_of_ne (hφnonneg _) (Ne.symm hzero)
        have : 0 < δ - |coordinate U u - t₀| := by
          simpa only [φ, lt_max_iff, lt_self_iff_false, false_or] using hpos
        linarith
      have hgu : g u < 0 := by
        have h := hnear (show dist (coordinate U u) t₀ < δ by simpa [Real.dist_eq] using hd)
        simpa only [hinverse] using h
      exact mul_nonpos_of_nonpos_of_nonneg hgu.le (sq_nonneg _)
  have hnae : ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ -w u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact neg_nonneg.mpr (hwnonpos u)
  have hzero : ∫ u in Ioi U, -w u = 0 := by
    rw [integral_neg]
    have hlow : 0 ≤ ∫ u in Ioi U, w u := htest
    have hhigh : (∫ u in Ioi U, w u) ≤ 0 :=
      integral_nonpos_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hwnonpos u)
    linarith
  have hae : (fun u => -w u) =ᵐ[volume.restrict (Ioi U)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnae hwint.neg).mp hzero
  have hz := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hwcont.neg continuousOn_const hu₀
  have hφ₀ : φ (coordinate U u₀) = δ := by simp [φ, t₀, hδ.le]
  have hneq : w u₀ ≠ 0 := by
    dsimp only [w]
    rw [hφ₀]
    exact mul_ne_zero hneg.ne (pow_ne_zero _ hδ.ne')
  exact hneq (neg_eq_zero.mp hz)

/-- For the original continuous signed L1 source, all finite exponential Hankel
matrices are positive semidefinite exactly when the source is pointwise
nonnegative. Every moment and every finite square integral actually converges. -/
theorem exponential_hankel_positivity (U : ℝ) (g : ℝ → ℝ)
    (hc : ContinuousOn g (Ioi U)) (hg : IntegrableOn g (Ioi U)) :
    (∀ k : ℕ, IntegrableOn
      (fun u => g u * Real.exp (-(k : ℝ) * (u - U))) (Ioi U)) ∧
    (∀ (N : ℕ) (c : Fin (N + 1) → ℝ),
      IntegrableOn (fun u => g u *
        (∑ i, c i * Real.exp (-(i.val : ℝ) * (u - U))) ^ 2) (Ioi U) ∧
      star c ⬝ᵥ (exponentialHankel U g N *ᵥ c) =
        ∫ u in Ioi U, g u *
          (∑ i, c i * Real.exp (-(i.val : ℝ) * (u - U))) ^ 2) ∧
    ((∀ u ∈ Ioi U, 0 ≤ g u) ↔ ∀ N : ℕ, (exponentialHankel U g N).PosSemidef) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simpa only [exponential_eq_pow] using integrable_power hg k
  · intro N c
    constructor
    · simpa only [eval_coefficientPolynomial, exponential_eq_pow] using
        integrable_polynomial_square hg (coefficientPolynomial c)
    · simpa only [exponential_eq_pow] using quadratic_integral hg N c
  · constructor
    · intro hpos N
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j
        simp [conjTranspose_apply, exponentialHankel, Nat.add_comm]
      · intro c
        rw [quadratic_integral hg]
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (hpos u hu) (sq_nonneg _)
    · intro hH
      exact nonneg_of_polynomial_squares hc hg (polynomial_square_nonneg hg hH)

#print axioms exponential_hankel_positivity

end D5.S3.Analytic.Laplace.ExponentialHankelPositivity
