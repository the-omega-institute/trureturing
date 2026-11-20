/- GID: D5/S3/Analytic/Probability/MomentPerturbation
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/MomentPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Adjugate]
   utility: none
   digest: An adjugate tilt preserves low-order moments and separates Gaussian weak limits. -/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A compactly supported polynomial correction gives a positive change of density that
preserves all integrable polynomial moments through a fixed order. The adjugate gives
the same formula for every baseline, including those with a singular moment matrix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace D5.S3.Analytic.Probability.MomentPerturbation

/-- The triangular window supported on the closed unit interval about zero. -/
def window (x : ℝ) : ℝ := max (1 - |x|) 0

private theorem continuous_window : Continuous window :=
  (continuous_const.sub continuous_abs).max continuous_const

private theorem window_nonneg (x : ℝ) : 0 ≤ window x := le_max_right _ _

private theorem window_eq_zero_outside (x : ℝ) (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    window x = 0 := by
  apply max_eq_right
  by_contra! h
  have hb := abs_lt.mp (show |x| < 1 by linarith)
  exact hx ⟨hb.1.le, hb.2.le⟩

private theorem window_pow_bound (k : ℕ) (x : ℝ) : ‖window x * x ^ k‖ ≤ 1 := by
  by_cases hx : |x| ≤ 1
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (window_nonneg x), abs_pow]
    calc
      window x * |x| ^ k ≤ window x :=
        mul_le_of_le_one_right (window_nonneg x) (pow_le_one₀ (abs_nonneg x) hx)
      _ ≤ 1 := max_le (by linarith [abs_nonneg x]) zero_le_one
  · have hw : window x = 0 := max_eq_right (by linarith [lt_of_not_ge hx])
    simp [hw]

private def basis (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => window x * x ^ k)
    (continuous_window.mul (continuous_id.pow k)) 1 (window_pow_bound k)

private theorem basis_apply (k : ℕ) (x : ℝ) : basis k x = window x * x ^ k := rfl

/-- The windowed Gram matrix of the powers indexed by `Fin (R + 1)`. -/
def gram (R : ℕ) (μ : ProbabilityMeasure ℝ) : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ :=
  fun i j => ∫ x, basis (i.val + j.val) x ∂(μ : Measure ℝ)

private def cross (R : ℕ) (μ : ProbabilityMeasure ℝ) : Fin (R + 1) → ℝ :=
  fun i => ∫ x, basis (i.val + (R + 1)) x ∂(μ : Measure ℝ)

private def correction (R : ℕ) (μ : ProbabilityMeasure ℝ) : Fin (R + 1) → ℝ :=
  (gram R μ).adjugate *ᵥ cross R μ

/-- The adjugate correction multiplied by the triangular window. -/
def perturbation (R : ℕ) (μ : ProbabilityMeasure ℝ) : ℝ →ᵇ ℝ :=
  (gram R μ).det • basis (R + 1) -
    ∑ j : Fin (R + 1), correction R μ j • basis j.val

private theorem perturbation_apply (R : ℕ) (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    perturbation R μ x = (gram R μ).det * basis (R + 1) x -
      ∑ j : Fin (R + 1), correction R μ j * basis j.val x := by
  simp [perturbation, smul_eq_mul]

private def size (R : ℕ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  |(gram R μ).det| + ∑ j : Fin (R + 1), |correction R μ j|

private theorem size_nonneg (R : ℕ) (μ : ProbabilityMeasure ℝ) : 0 ≤ size R μ :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private def step (R : ℕ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  1 / (2 * (1 + size R μ))

/-- The normalized positive density relative to the baseline. -/
def density (R : ℕ) (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  1 + step R μ * perturbation R μ x

/-- The change of density is continuous in the observation. -/
theorem continuous_density (R : ℕ) (μ : ProbabilityMeasure ℝ) :
    Continuous (density R μ) :=
  continuous_const.add (continuous_const.mul (perturbation R μ).continuous)

private theorem abs_perturbation_le (R : ℕ) (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    |perturbation R μ x| ≤ size R μ := by
  have hb (k : ℕ) : |basis k x| ≤ 1 := by
    simpa only [basis_apply, Real.norm_eq_abs] using window_pow_bound k x
  rw [perturbation_apply, size]
  calc
    |(gram R μ).det * basis (R + 1) x -
        ∑ j : Fin (R + 1), correction R μ j * basis j.val x| ≤
        |(gram R μ).det * basis (R + 1) x| +
          |∑ j : Fin (R + 1), correction R μ j * basis j.val x| := abs_sub _ _
    _ ≤ |(gram R μ).det| + ∑ j : Fin (R + 1), |correction R μ j| := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb _)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

/-- The density lies between one half and three halves at every point of every baseline. -/
theorem density_bounds (R : ℕ) (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    (1 / 2 : ℝ) ≤ density R μ x ∧ density R μ x ≤ 3 / 2 := by
  have hd : 0 < 2 * (1 + size R μ) := by linarith [size_nonneg R μ]
  have h : |step R μ * perturbation R μ x| ≤ 1 / 2 := by
    rw [abs_mul, step, abs_of_pos (one_div_pos.mpr hd), one_div_mul_eq_div]
    apply (div_le_iff₀ hd).2
    linarith [abs_perturbation_le R μ x]
  unfold density
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

private theorem gram_mul_correction (R : ℕ) (μ : ProbabilityMeasure ℝ) :
    gram R μ *ᵥ correction R μ = (gram R μ).det • cross R μ := by
  rw [correction, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

private theorem integral_pow_mul_perturbation (R : ℕ) (μ : ProbabilityMeasure ℝ)
    (i : Fin (R + 1)) :
    (∫ x, x ^ i.val * perturbation R μ x ∂(μ : Measure ℝ)) = 0 := by
  have he (x : ℝ) : x ^ i.val * perturbation R μ x =
      (gram R μ).det * basis (i.val + (R + 1)) x -
        ∑ j : Fin (R + 1), correction R μ j * basis (i.val + j.val) x := by
    rw [perturbation_apply, mul_sub, Finset.mul_sum]
    congr 1
    · simp only [basis_apply, pow_add]
      ring
    · apply Finset.sum_congr rfl
      intro j _
      simp only [basis_apply, pow_add]
      ring
  simp_rw [he]
  have hlead := ((basis (i.val + (R + 1))).integrable (μ := (μ : Measure ℝ))).const_mul
    (gram R μ).det
  have hterm (j : Fin (R + 1)) :=
    ((basis (i.val + j.val)).integrable (μ := (μ : Measure ℝ))).const_mul (correction R μ j)
  rw [integral_sub hlead (integrable_finsetSum _ fun j _ => hterm j),
    integral_finsetSum _ (fun j _ => hterm j)]
  simp_rw [integral_const_mul]
  apply sub_eq_zero.mpr
  have hm := congrFun (gram_mul_correction R μ) i
  refine hm.symm.trans ?_
  change ∑ j, gram R μ i j * correction R μ j = _
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem perturbation_compactSupport (R : ℕ) (μ : ProbabilityMeasure ℝ) :
    HasCompactSupport (perturbation R μ) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp [perturbation_apply, basis_apply, window_eq_zero_outside x hx]

private theorem integrable_mul_perturbation (R : ℕ) (μ : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun x => f x * perturbation R μ x) (μ : Measure ℝ) :=
  (hf.mul (perturbation R μ).continuous).integrable_of_hasCompactSupport
    (perturbation_compactSupport R μ).mul_left

private theorem integral_eval_mul_perturbation (R : ℕ) (μ : ProbabilityMeasure ℝ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ R) :
    (∫ x, p.eval x * perturbation R μ x ∂(μ : Measure ℝ)) = 0 := by
  have he (x : ℝ) : p.eval x * perturbation R μ x =
      ∑ i : Fin (R + 1), p.coeff i.val * (x ^ i.val * perturbation R μ x) := by
    have h : p.eval x = ∑ i : Fin (R + 1), p.coeff i.val * x ^ i.val := by
      conv_lhs => rw [p.as_sum_range' (R + 1) (Nat.lt_succ_of_le hp)]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => p.coeff i * x ^ i) (R + 1)).symm
    rw [h, Finset.sum_mul]
    simp only [mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_mul_perturbation R μ (continuous_id.pow i.val)).const_mul _)]
  simp_rw [integral_const_mul, integral_pow_mul_perturbation, mul_zero, Finset.sum_const_zero]

/-- The signed change of density integrates to zero against every polynomial of degree at
most `R`, including the constant polynomial. The signed integrand is compactly supported. -/
theorem integral_eval_mul_density_sub_one (R : ℕ) (μ : ProbabilityMeasure ℝ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ R) :
    (∫ x, p.eval x * (density R μ x - 1) ∂(μ : Measure ℝ)) = 0 := by
  have he (x : ℝ) : p.eval x * (density R μ x - 1) =
      step R μ * (p.eval x * perturbation R μ x) := by
    unfold density
    ring
  simp_rw [he, integral_const_mul, integral_eval_mul_perturbation R μ p hp, mul_zero]

private theorem integrable_density (R : ℕ) (μ : ProbabilityMeasure ℝ) :
    Integrable (density R μ) (μ : Measure ℝ) :=
  (integrable_const _).add
    (((perturbation R μ).integrable (μ := (μ : Measure ℝ))).const_mul (step R μ))

/-- The constant polynomial identity makes the change of density integrate to one. -/
theorem integral_density (R : ℕ) (μ : ProbabilityMeasure ℝ) :
    (∫ x, density R μ x ∂(μ : Measure ℝ)) = 1 := by
  have h := integral_eval_mul_density_sub_one R μ 1 (by simp)
  simp only [Polynomial.eval_one, one_mul] at h
  rw [integral_sub (integrable_density R μ) (integrable_const _)] at h
  simpa using sub_eq_zero.mp h

/-- The probability law with the adjugate density relative to the baseline law. -/
def tilted (R : ℕ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (density R μ x)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (integrable_density R μ)
        (ae_of_all _ fun x => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (density_bounds R μ x).1),
      integral_density, ENNReal.ofReal_one]⟩

private theorem integral_tilted (R : ℕ) (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(tilted R μ : Measure ℝ)) =
      ∫ x, density R μ x * f x ∂(μ : Measure ℝ) := by
  change (∫ x, f x ∂(μ : Measure ℝ).withDensity _) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((continuous_density R μ).measurable.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (density_bounds R μ x).1)]

/-- An integrable baseline polynomial of degree at most `R` stays integrable
and has the same expectation under the tilted law. -/
theorem integral_eval_tilted (R : ℕ) (μ : ProbabilityMeasure ℝ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ R)
    (hint : Integrable (fun x => p.eval x) (μ : Measure ℝ)) :
    Integrable (fun x => p.eval x) (tilted R μ : Measure ℝ) ∧
    (∫ x, p.eval x ∂(tilted R μ : Measure ℝ)) = ∫ x, p.eval x ∂(μ : Measure ℝ) := by
  have he (x : ℝ) : density R μ x * p.eval x =
      p.eval x + step R μ * (p.eval x * perturbation R μ x) := by
    unfold density
    ring
  have hcorr := (integrable_mul_perturbation R μ p.continuous).const_mul (step R μ)
  constructor
  · change Integrable (fun x => p.eval x) ((μ : Measure ℝ).withDensity _)
    rw [integrable_withDensity_iff_integrable_smul'
      ((continuous_density R μ).measurable.ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply (hint.add hcorr).congr
    exact ae_of_all _ fun x => by
      simp only [smul_eq_mul, ENNReal.toReal_ofReal
        ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (density_bounds R μ x).1), he, Pi.add_apply]
  · rw [integral_tilted]
    simp_rw [he]
    rw [integral_add hint hcorr, integral_const_mul, integral_eval_mul_perturbation R μ p hp,
      mul_zero, add_zero]

/-- The real Gaussian with mean zero and variance one, as a probability measure. -/
def standardGaussian : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩

private theorem gaussian_isOpenPosMeasure :
    (standardGaussian : Measure ℝ).IsOpenPosMeasure :=
  (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure

private theorem exists_eval_ne_zero_in_window (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, p.eval x ≠ 0 := by
  by_contra! h
  apply hp (Polynomial.eq_zero_of_infinite_isRoot p ?_)
  exact (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun x hx => h x hx

private theorem window_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < window x :=
  lt_of_lt_of_le (sub_pos.mpr (abs_lt.mpr hx)) (le_max_left _ _)

private theorem window_compactSupport : HasCompactSupport window := by
  exact HasCompactSupport.intro isCompact_Icc window_eq_zero_outside

private theorem gram_energy (R : ℕ) (μ : ProbabilityMeasure ℝ)
    (u : Fin (R + 1) → ℝ) :
    u ⬝ᵥ (gram R μ *ᵥ u) =
      ∫ x, window x * (∑ j : Fin (R + 1), u j * x ^ j.val) ^ 2 ∂(μ : Measure ℝ) := by
  have he (x : ℝ) : window x * (∑ j : Fin (R + 1), u j * x ^ j.val) ^ 2 =
      ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), (u i * u j) * basis (i.val + j.val) x := by
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [basis_apply, pow_add]
    ring
  have hterm (i j : Fin (R + 1)) :=
    ((basis (i.val + j.val)).integrable (μ := (μ : Measure ℝ))).const_mul (u i * u j)
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hterm i j)]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hterm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  unfold gram
  ring

private theorem eval_ofFn (R : ℕ) (u : Fin (R + 1) → ℝ) (x : ℝ) :
    (Polynomial.ofFn (R + 1) u).eval x = ∑ j : Fin (R + 1), u j * x ^ j.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- The standard Gaussian gives a strictly positive definite windowed Gram matrix
in every finite dimension. -/
theorem gaussian_gram_posDef (R : ℕ) : (gram R standardGaussian).PosDef := by
  have := gaussian_isOpenPosMeasure
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [gram, Nat.add_comm]
  · intro u hu
    simp only [star_trivial]
    rw [gram_energy]
    let p := Polynomial.ofFn (R + 1) u
    have hp : p ≠ 0 := by
      intro h
      apply hu (Polynomial.injective_ofFn (R + 1) (h.trans (map_zero _).symm))
    obtain ⟨x, hx, hpx⟩ := exists_eval_ne_zero_in_window p hp
    simp_rw [← eval_ofFn]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
      (continuous_window.mul (p.continuous.pow 2)) window_compactSupport.mul_right
      (fun y => mul_nonneg (window_nonneg y) (sq_nonneg _)) ?_
    exact (mul_pos (window_pos hx) (sq_pos_of_ne_zero hpx)).ne'

private theorem continuous_gram (R : ℕ) : Continuous (gram R) :=
  continuous_matrix fun i j =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (basis (i.val + j.val))

private theorem continuous_correction (R : ℕ) : Continuous (correction R) :=
  (continuous_gram R).matrix_adjugate.matrix_mulVec
    (continuous_pi fun i =>
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction (basis (i.val + (R + 1))))

private theorem continuous_step (R : ℕ) : Continuous (step R) := by
  have hsize : Continuous (size R) :=
    (continuous_gram R).matrix_det.abs.add (continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp (continuous_correction R)).abs)
  exact continuous_const.div
    (continuous_const.mul (continuous_const.add hsize))
    (fun μ => by linarith [size_nonneg R μ])

private theorem integral_tilted_bounded (R : ℕ) (μ : ProbabilityMeasure ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(tilted R μ : Measure ℝ)) =
      (∫ x, f x ∂(μ : Measure ℝ)) + step R μ *
        ((gram R μ).det * (∫ x, (basis (R + 1) * f) x ∂(μ : Measure ℝ)) -
          ∑ j : Fin (R + 1), correction R μ j *
            (∫ x, (basis j.val * f) x ∂(μ : Measure ℝ))) := by
  rw [integral_tilted]
  have he (x : ℝ) : density R μ x * f x =
      f x + step R μ * ((gram R μ).det * (basis (R + 1) * f) x -
        ∑ j : Fin (R + 1), correction R μ j * (basis j.val * f) x) := by
    simp only [density, add_mul, one_mul, mul_assoc, perturbation_apply, sub_mul,
      Finset.sum_mul, BoundedContinuousFunction.mul_apply]
  have hlead := ((basis (R + 1) * f).integrable (μ := (μ : Measure ℝ))).const_mul
    (gram R μ).det
  have hterm (j : Fin (R + 1)) :=
    ((basis j.val * f).integrable (μ := (μ : Measure ℝ))).const_mul (correction R μ j)
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have hdiff : Integrable (fun x => (gram R μ).det * (basis (R + 1) * f) x -
      ∑ j : Fin (R + 1), correction R μ j * (basis j.val * f) x) (μ : Measure ℝ) :=
    hlead.sub hsum
  simp_rw [he]
  rw [integral_add (f.integrable _) (hdiff.const_mul (step R μ)), integral_const_mul,
    integral_sub hlead hsum, integral_finsetSum _ (fun j _ => hterm j)]
  simp_rw [integral_const_mul]

/-- Tilting preserves weak convergence, to the tilt of the limiting law. -/
theorem continuous_tilted (R : ℕ) : Continuous (tilted R) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [integral_tilted_bounded]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).add
    ((continuous_step R).mul
      (((continuous_gram R).matrix_det.mul
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (basis (R + 1) * f))).sub
          (continuous_finsetSum _ fun j _ =>
            ((continuous_apply j).comp (continuous_correction R)).mul
              (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (basis j.val * f)))))

/-- The Gaussian correction itself is a bounded continuous test whose expectation
strictly increases under the tilt. In particular the two probability laws differ. -/
theorem tilted_gaussian_separation (R : ℕ) :
    (∫ x, perturbation R standardGaussian x ∂(standardGaussian : Measure ℝ)) <
      (∫ x, perturbation R standardGaussian x ∂(tilted R standardGaussian : Measure ℝ)) ∧
    tilted R standardGaussian ≠ standardGaussian := by
  let μ := standardGaussian
  have : (μ : Measure ℝ).IsOpenPosMeasure := gaussian_isOpenPosMeasure
  let p : Polynomial ℝ :=
    Polynomial.monomial (R + 1) (gram R μ).det - Polynomial.ofFn (R + 1) (correction R μ)
  have hd : 0 < (gram R μ).det := (gaussian_gram_posDef R).det_pos
  have hcoef : p.coeff (R + 1) = (gram R μ).det := by
    simp [p, Polynomial.ofFn_coeff_eq_zero_of_ge]
  have hp : p ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hcoef
    exact hd.ne' hcoef.symm
  obtain ⟨x, hx, hpx⟩ := exists_eval_ne_zero_in_window p hp
  have heval (y : ℝ) : perturbation R μ y = window y * p.eval y := by
    simp only [p, Polynomial.eval_sub, Polynomial.eval_monomial, eval_ofFn, perturbation_apply,
      basis_apply, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun _ _ => by ring
  have hnz : perturbation R μ x ≠ 0 := by
    rw [heval]
    exact mul_ne_zero (window_pos hx).ne' hpx
  have hsupp : HasCompactSupport (fun y => (perturbation R μ y) ^ 2) := by
    simp only [pow_two]
    exact (perturbation_compactSupport R μ).mul_right
  have hsq : 0 < ∫ y, (perturbation R μ y) ^ 2 ∂(μ : Measure ℝ) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      ((perturbation R μ).continuous.pow 2) hsupp (fun _ => sq_nonneg _)
      ((sq_pos_of_ne_zero hnz).ne')
  have hstep : 0 < step R μ := by
    unfold step
    apply one_div_pos.mpr
    linarith [size_nonneg R μ]
  have htest :
      (∫ y, perturbation R μ y ∂(μ : Measure ℝ)) <
        (∫ y, perturbation R μ y ∂(tilted R μ : Measure ℝ)) := by
    rw [integral_tilted]
    have he (y : ℝ) : density R μ y * perturbation R μ y =
        perturbation R μ y + step R μ * (perturbation R μ y) ^ 2 := by
      unfold density
      ring
    simp_rw [he]
    rw [integral_add ((perturbation R μ).integrable _)
      ((integrable_mul_perturbation R μ (perturbation R μ).continuous).const_mul (step R μ)
        |>.congr (ae_of_all _ fun y => by simp only [pow_two])),
      integral_const_mul]
    exact lt_add_of_pos_right _ (mul_pos hstep hsq)
  refine ⟨htest, fun h => ?_⟩
  change tilted R μ = μ at h
  rw [h] at htest
  exact lt_irrefl _ htest

end D5.S3.Analytic.Probability.MomentPerturbation
