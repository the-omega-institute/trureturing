/- GID: D5/S3/Arith/Robin/FullZeroGaussianResponse
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/FullZeroGaussianResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An off-line zero gives a positive full Gaussian response at a controlled scale. -/

import D5.S3.Arith.Robin.ZeroCoefficientBudget
import D5.S3.Arith.Robin.ZeroPowerSum
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Exact Gaussian moments and an inverse-height budget control the complete signed zero response. -/

namespace D5.S3.Arith.Robin.FullZeroGaussianResponse

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Topology

noncomputable section

def density (m M y : ℝ) : ℝ :=
  Real.exp (-(y - M) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m)

def coordinate (m M y : ℝ) : ℝ := (y - M) / (2 * m)

def transform (m M : ℝ) (w : ℂ) : ℂ := Complex.exp (m * w ^ 2 + M * w)

def polynomial (m M γ y : ℝ) : ℂ :=
  (coordinate m M y + Complex.I * γ) *
    (coordinate m M y + Complex.I * γ - 1) - 1 / (2 * (m : ℂ))

def kernel (m M γ y : ℝ) : ℝ :=
  -(Complex.exp (-Complex.I * γ * y) * polynomial m M γ y).re * density m M y

def envelope (m M γ y : ℝ) : ℝ :=
  2 * (coordinate m M y ^ 2 + γ ^ 2 + 1) * density m M y

private theorem raw_moments (m M : ℝ) (hm : 0 < m) (w : ℂ) :
    (∀ n : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ n * Complex.exp (w * y) *
      density m M y)) ∧
    (∫ y : ℝ, Complex.exp (w * y) * density m M y) = transform m M w ∧
    (∫ y : ℝ, (y : ℂ) * Complex.exp (w * y) * density m M y) =
      (2 * m * w + M) * transform m M w ∧
    (∫ y : ℝ, (y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y) =
      (2 * m + (2 * m * w + M) ^ 2) * transform m M w := by
  let v : ℝ≥0 := ⟨2 * m, by positivity⟩
  let μ := gaussianReal M v
  have hvcoe : (v : ℝ) = 2 * m := rfl
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    rw [hvcoe] at this
    norm_num at this
    linarith
  have hdensity (y : ℝ) : gaussianPDFReal M v y = density m M y := by
    simp only [gaussianPDFReal, density, hvcoe]
    rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
      show 2 * (2 * m) = 4 * m by ring]
    ring
  have hset (z : ℂ) : z.re ∈ interior (integrableExpSet id μ) := by
    simp [μ]
  have hF (z : ℂ) : complexMGF id μ z = transform m M z := by
    change complexMGF id (gaussianReal M v) z = _
    rw [complexMGF_id_gaussianReal]
    change Complex.exp (z * M + ((v : ℝ) : ℂ) * z ^ 2 / 2) = _
    rw [hvcoe]
    simp only [ofReal_mul, ofReal_ofNat, transform]
    congr 1
    ring
  have hD (z : ℂ) : HasDerivAt (transform m M)
      ((2 * m * z + M) * transform m M z) z := by
    convert ((((hasDerivAt_id z).pow 2).const_mul (m : ℂ)).add
      ((hasDerivAt_id z).const_mul (M : ℂ))).cexp using 1
    · funext x
      change Complex.exp ((m : ℂ) * x ^ 2 + M * x) = _
      congr 1
    · simp only [transform, Pi.add_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
      ring
  have hfirst (z : ℂ) : (∫ y : ℝ, (y : ℂ) * Complex.exp (z * y) ∂μ) =
      (2 * m * z + M) * transform m M z := by
    have h := hasDerivAt_complexMGF (hset z)
    rw [show complexMGF id μ = transform m M from funext hF] at h
    exact h.unique (hD z)
  have hsecond : (∫ y : ℝ, (y : ℂ) ^ 2 * Complex.exp (w * y) ∂μ) =
      (2 * m + (2 * m * w + M) ^ 2) * transform m M w := by
    have h := hasDerivAt_integral_pow_mul_exp (hset w) 1
    simp only [id_eq, pow_one, Nat.reduceAdd] at h
    simp_rw [hfirst] at h
    have h' := ((((hasDerivAt_id w).const_mul (2 * (m : ℂ))).add_const
      (M : ℂ)).mul (hD w))
    convert h.unique h' using 1 <;> dsimp only [id_eq] <;> ring
  have hi (n : ℕ) : Integrable (fun y : ℝ => (y : ℂ) ^ n * Complex.exp (w * y)) μ := by
    simpa only [id_eq, ofReal_pow] using
      integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hset w) n
  have htransfer (f : ℝ → ℂ) :
      (∫ y, f y ∂μ) = ∫ y, f y * density m M y := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [hdensity, Complex.real_smul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h := hi n
    change Integrable _ (gaussianReal M v) at h
    rw [gaussianReal_of_var_ne_zero M hv] at h
    have h' := (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF M v) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp h
    simpa only [toReal_gaussianPDF, hdensity, Complex.real_smul, mul_comm] using h'
  · rw [← htransfer]
    exact hF w
  · rw [← htransfer]
    exact hfirst w
  · rw [← htransfer]
    exact hsecond

private theorem moments (m M : ℝ) (hm : 0 < m) (w : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (w * y) * density m M y) ∧
    Integrable (fun y : ℝ => (coordinate m M y : ℂ) * Complex.exp (w * y) *
      density m M y) ∧
    Integrable (fun y : ℝ => (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) *
      density m M y) ∧
    (∫ y : ℝ, Complex.exp (w * y) * density m M y) = transform m M w ∧
    (∫ y : ℝ, (coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y) =
      w * transform m M w ∧
    (∫ y : ℝ, (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y) =
      (w ^ 2 + 1 / (2 * (m : ℂ))) * transform m M w := by
  obtain ⟨hi, h0, h1, h2⟩ := raw_moments m M hm w
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  simp only [pow_zero, one_mul] at hi0
  simp only [pow_one] at hi1
  have he1 (y : ℝ) : (coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y =
      (1 / (2 * (m : ℂ))) * ((y : ℂ) * Complex.exp (w * y) * density m M y -
        (M : ℂ) * (Complex.exp (w * y) * density m M y)) := by
    simp only [coordinate, ofReal_div, ofReal_sub, ofReal_mul, ofReal_ofNat]
    ring
  have he2 (y : ℝ) : (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y =
      (1 / (2 * (m : ℂ)) ^ 2) *
        ((y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y -
          (2 * (M : ℂ)) * ((y : ℂ) * Complex.exp (w * y) * density m M y) +
          (M : ℂ) ^ 2 * (Complex.exp (w * y) * density m M y)) := by
    simp only [coordinate, ofReal_div, ofReal_sub, ofReal_mul, ofReal_ofNat]
    ring
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hi0, ?_, ?_, h0, ?_, ?_⟩
  · simp_rw [he1]
    exact (hi1.sub (hi0.const_mul (M : ℂ))).const_mul _
  · simp_rw [he2]
    exact ((hi2.sub (hi1.const_mul (2 * (M : ℂ)))).add
      (hi0.const_mul ((M : ℂ) ^ 2))).const_mul _
  · simp_rw [he1]
    rw [integral_const_mul, integral_sub hi1 (hi0.const_mul (M : ℂ)),
      integral_const_mul, h0, h1]
    field_simp [hmc]
    <;> ring
  · simp_rw [he2]
    rw [integral_const_mul, integral_add
      (f := fun y : ℝ => (y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y -
        (2 * (M : ℂ)) * ((y : ℂ) * Complex.exp (w * y) * density m M y))
      (hi2.sub (hi1.const_mul (2 * (M : ℂ))))
      (hi0.const_mul ((M : ℂ) ^ 2)), integral_sub hi2 (hi1.const_mul (2 * (M : ℂ))),
      integral_const_mul, integral_const_mul, h0, h1, h2]
    field_simp [hmc]
    <;> ring

private theorem quadratic_moment (m M : ℝ) (hm : 0 < m) (w b c : ℂ) :
    Integrable (fun y : ℝ =>
      ((coordinate m M y : ℂ) ^ 2 + b * coordinate m M y + c) *
        Complex.exp (w * y) * density m M y) ∧
    (∫ y : ℝ, ((coordinate m M y : ℂ) ^ 2 + b * coordinate m M y + c) *
      Complex.exp (w * y) * density m M y) =
      (w ^ 2 + b * w + c + 1 / (2 * (m : ℂ))) * transform m M w := by
  obtain ⟨hi0, hi1, hi2, h0, h1, h2⟩ := moments m M hm w
  have he (y : ℝ) :
      ((coordinate m M y : ℂ) ^ 2 + b * coordinate m M y + c) *
        Complex.exp (w * y) * density m M y =
      (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y +
        b * ((coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y) +
        c * (Complex.exp (w * y) * density m M y) := by ring
  simp_rw [he]
  refine ⟨(hi2.add (hi1.const_mul b)).add (hi0.const_mul c), ?_⟩
  rw [integral_add
    (f := fun y : ℝ => (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y +
      b * ((coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y))
    (hi2.add (hi1.const_mul b)) (hi0.const_mul c),
    integral_add hi2 (hi1.const_mul b), integral_const_mul, integral_const_mul, h0, h1, h2]
  ring

private theorem kernel_bound (m M γ : ℝ) (hm : 1 ≤ m) (y : ℝ) :
    |kernel m M γ y| ≤ envelope m M γ y ∧
    ‖Complex.exp (-Complex.I * γ * y) * polynomial m M γ y‖ * density m M y ≤
      envelope m M γ y := by
  let z : ℂ := coordinate m M y + Complex.I * γ
  have hz : ‖z‖ ^ 2 = coordinate m M y ^ 2 + γ ^ 2 := by
    simp [z, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring
  have hc0 : 0 ≤ 1 / (2 * m) := by positivity
  have hc : 1 / (2 * m) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hp : ‖polynomial m M γ y‖ ≤ 2 * (coordinate m M y ^ 2 + γ ^ 2 + 1) := by
    have htri : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z 1
    have h := norm_sub_le (z * (z - 1)) (1 / (2 * (m : ℂ)))
    have hec : ‖(1 / (2 * (m : ℂ)))‖ = 1 / (2 * m) := by
      rw [show (1 / (2 * (m : ℂ))) = ((1 / (2 * m) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    rw [norm_mul, hec] at h
    have hprod := mul_le_mul_of_nonneg_left htri (norm_nonneg z)
    change ‖z * (z - 1) - 1 / (2 * (m : ℂ))‖ ≤ _
    nlinarith [sq_nonneg (‖z‖ - 1 / 2)]
  have hg : 0 ≤ density m M y := by unfold density; positivity
  have he : ‖Complex.exp (-Complex.I * γ * y)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hk : |(Complex.exp (-Complex.I * γ * y) * polynomial m M γ y).re| ≤
      2 * (coordinate m M y ^ 2 + γ ^ 2 + 1) := by
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, he, one_mul]; exact hp)
  constructor
  · simpa only [kernel, envelope, abs_mul, abs_neg, abs_of_nonneg hg] using
      mul_le_mul_of_nonneg_right hk hg
  · rw [norm_mul, he, one_mul]
    exact mul_le_mul_of_nonneg_right hp hg

/-- The Gaussian polynomial has exact responses to every exponential and a
nonnegative envelope when `m ≥ 1`. All the exponential moments are integrable. -/
private theorem gaussian_zero_kernel (m M γ : ℝ) (hm : 0 < m) :
    (∀ w : ℂ,
      Integrable (fun y : ℝ => Complex.exp (w * y) * density m M y) ∧
      Integrable (fun y : ℝ => (coordinate m M y : ℂ) * Complex.exp (w * y) *
        density m M y) ∧
      Integrable (fun y : ℝ => (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) *
        density m M y) ∧
      (∫ y : ℝ, Complex.exp (w * y) * density m M y) = transform m M w ∧
      (∫ y : ℝ, (coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y) =
        w * transform m M w ∧
      (∫ y : ℝ, (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y) =
        (w ^ 2 + 1 / (2 * (m : ℂ))) * transform m M w) ∧
    (∀ ρ : ℂ, ρ ≠ 0 → ρ ≠ 1 →
      let a := (ρ * (1 - ρ))⁻¹
      Integrable (fun y : ℝ => a * Complex.exp (ρ * y) *
        (Complex.exp (-Complex.I * γ * y) * polynomial m M γ y) * density m M y) ∧
      Integrable (fun y : ℝ => a * Complex.exp (ρ * y) * envelope m M γ y) ∧
      (∫ y : ℝ, a * Complex.exp (ρ * y) *
        (Complex.exp (-Complex.I * γ * y) * polynomial m M γ y) * density m M y) =
        -transform m M (ρ - Complex.I * γ) ∧
      (∫ y : ℝ, a * Complex.exp (ρ * y) * envelope m M γ y) =
        2 * a * (ρ ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m M ρ) ∧
    (∀ y : ℝ, 0 ≤ envelope m M γ y) ∧
    (1 ≤ m → ∀ y : ℝ, |kernel m M γ y| ≤ envelope m M γ y ∧
      ‖Complex.exp (-Complex.I * γ * y) * polynomial m M γ y‖ * density m M y ≤
        envelope m M γ y) := by
  refine ⟨moments m M hm, ?_, ?_, kernel_bound m M γ⟩
  case refine_2 =>
    intro y
    unfold envelope density
    positivity
  intro ρ hρ0 hρ1
  dsimp only
  let a := (ρ * (1 - ρ))⁻¹
  let w := ρ - Complex.I * γ
  let b : ℂ := 2 * (Complex.I * γ) - 1
  let c : ℂ := (Complex.I * γ) * (Complex.I * γ - 1) - 1 / (2 * (m : ℂ))
  obtain ⟨hip, hp⟩ := quadratic_moment m M hm w b c
  obtain ⟨hiv, hv⟩ := quadratic_moment m M hm ρ 0 ((γ : ℂ) ^ 2 + 1)
  have hep (y : ℝ) : a * Complex.exp (ρ * y) *
      (Complex.exp (-Complex.I * γ * y) * polynomial m M γ y) * density m M y =
      a * (((coordinate m M y : ℂ) ^ 2 + b * coordinate m M y + c) *
        Complex.exp (w * y) * density m M y) := by
    dsimp only [w, b, c, polynomial]
    rw [show (ρ - Complex.I * γ) * (y : ℂ) =
      ρ * y + (-Complex.I * γ * y) by ring, Complex.exp_add]
    ring
  have hev (y : ℝ) : a * Complex.exp (ρ * y) * envelope m M γ y =
      (2 * a) * (((coordinate m M y : ℂ) ^ 2 + 0 * coordinate m M y +
        ((γ : ℂ) ^ 2 + 1)) * Complex.exp (ρ * y) * density m M y) := by
    simp only [envelope, ofReal_mul, ofReal_add, ofReal_pow, ofReal_ofNat, ofReal_one]
    ring
  have ha : a * (ρ * (ρ - 1)) = -1 := by
    have hn : ρ * (1 - ρ) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
    dsimp [a]
    field_simp [hn]
    <;> ring
  dsimp only [a] at hep hev
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hep]
    exact hip.const_mul a
  · simp_rw [hev]
    exact hiv.const_mul (2 * a)
  · simp_rw [hep]
    rw [integral_const_mul, hp]
    have hpoly : w ^ 2 + b * w + c + 1 / (2 * (m : ℂ)) = ρ * (ρ - 1) := by
      dsimp [w, b, c]
      ring
    rw [hpoly, ← mul_assoc, ha, neg_one_mul]
  · simp_rw [hev]
    rw [integral_const_mul, hv]
    ring


private theorem exponential_strip_bound (z : ℂ) (hz : 0 < z.re ∧ z.re < 1) (y : ℝ) :
    ‖Complex.exp (z * y)‖ ≤ Real.exp (max y 0) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hy)]
    exact mul_nonpos_of_nonneg_of_nonpos hz.1.le (le_of_not_ge hy)

private theorem weighted_envelope_integrable (m M γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * envelope m M γ y) := by
  have he (t : ℝ) : Integrable (fun y : ℝ => Real.exp (t * y) * envelope m M γ y) := by
    have h := (quadratic_moment m M hm (t : ℂ) 0 ((γ : ℂ) ^ 2 + 1)).1.const_mul (2 : ℂ)
    have heq (y : ℝ) :
        2 * (((coordinate m M y : ℂ) ^ 2 + (0 : ℂ) * coordinate m M y +
          ((γ : ℂ) ^ 2 + 1)) * Complex.exp ((t : ℂ) * y) * density m M y) =
        ((Real.exp (t * y) * envelope m M γ y : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
      simp only [envelope, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
        Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    simp_rw [heq] at h
    exact h.re
  have hmajor : Integrable (fun y : ℝ => envelope m M γ y +
      Real.exp y * envelope m M γ y) := by
    exact ((he 0).add (he 1)).congr
      (Filter.Eventually.of_forall fun y => by simp)
  refine hmajor.mono' (by unfold envelope density coordinate; fun_prop)
    (Filter.Eventually.of_forall fun y => ?_)
  have hv : 0 ≤ envelope m M γ y := by unfold envelope density; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hv)]
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy]
    linarith
  · rw [max_eq_right (le_of_not_ge hy), Real.exp_zero, one_mul]
    exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos y).le hv)

private theorem integrate_exponential_series {ι : Type*} [Countable ι]
    (ρ c : ι → ℂ) (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hc : Summable (fun i => ‖c i‖))
    (v : ℝ → ℝ) (hv : ∀ y, 0 ≤ v y)
    (hweight : Integrable (fun y : ℝ => Real.exp (max y 0) * v y))
    (φ : ℝ → ℂ) (hφ : AEStronglyMeasurable φ volume)
    (hφv : ∀ y, ‖φ y‖ ≤ v y) :
    Integrable (fun y : ℝ => (∑' i, c i * Complex.exp (ρ i * y)) * φ y) ∧
      (∫ y : ℝ, (∑' i, c i * Complex.exp (ρ i * y)) * φ y) =
        ∑' i, ∫ y : ℝ, c i * Complex.exp (ρ i * y) * φ y := by
  let W : ℝ → ℝ := fun y => Real.exp (max y 0) * v y
  let F : ι → ℝ → ℂ := fun i y => c i * Complex.exp (ρ i * y) * φ y
  have hF (i : ι) (y : ℝ) : ‖F i y‖ ≤ ‖c i‖ * W y := by
    dsimp [F, W]
    simp only [norm_mul]
    calc
      _ ≤ (‖c i‖ * Real.exp (max y 0)) * v y := mul_le_mul
        (mul_le_mul_of_nonneg_left (exponential_strip_bound (ρ i) (hstrip i) y)
          (norm_nonneg _))
        (hφv y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hFi (i : ι) : Integrable (F i) := by
    exact (hweight.const_mul ‖c i‖).mono'
      (((continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable).mul hφ)
      (Filter.Eventually.of_forall (hF i))
  have hFn (y : ℝ) : Summable (fun i => ‖F i y‖) := by
    exact (hc.mul_right (W y)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hF i y)
  have hnorm (y : ℝ) : ‖∑' i, F i y‖ ≤ (∑' i, ‖c i‖) * W y := by
    calc
      _ ≤ ∑' i, ‖F i y‖ := norm_tsum_le_tsum_norm (hFn y)
      _ ≤ ∑' i, ‖c i‖ * W y := (hFn y).tsum_le_tsum (fun i => hF i y) (hc.mul_right _)
      _ = _ := tsum_mul_right
  have hsum : Summable (fun i => ∫ y : ℝ, ‖F i y‖) := by
    apply (hc.mul_right (∫ y, W y)).of_nonneg_of_le
      (fun i => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    calc
      _ ≤ ∫ y : ℝ, ‖c i‖ * W y :=
        integral_mono (hFi i).norm (hweight.const_mul _) (hF i)
      _ = _ := integral_const_mul _ _
  have htotal : Integrable (fun y => ∑' i, F i y) :=
    (hweight.const_mul (∑' i, ‖c i‖)).mono'
      (AEStronglyMeasurable.tsum (fun i => (hFi i).aestronglyMeasurable))
      (Filter.Eventually.of_forall hnorm)
  have heq (y : ℝ) : (∑' i, F i y) = (∑' i, c i * Complex.exp (ρ i * y)) * φ y := by
    exact tsum_mul_right
  simp_rw [heq] at htotal
  refine ⟨htotal, ?_⟩
  have hi := (integral_tsum_of_summable_integral_norm hFi hsum).symm
  simpa only [heq] using hi


private theorem zero_family_integrals {ι : Type*} [Countable ι]
    (ρ : ι → ℂ) (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hc : Summable (fun i => ‖(ρ i * (1 - ρ i))⁻¹‖))
    (H : ℝ → ℝ)
    (hreal : ∀ y : ℝ, (∑' i, (ρ i * (1 - ρ i))⁻¹ * Complex.exp (ρ i * y)) =
      (H y : ℂ))
    (m M γ : ℝ) (hm : 1 ≤ m) :
    Integrable (fun y : ℝ => H y * kernel m M γ y) ∧
    Integrable (fun y : ℝ => H y * envelope m M γ y) ∧
    (∫ y : ℝ, H y * kernel m M γ y) =
      (∑' i, transform m M (ρ i - Complex.I * γ)).re ∧
    (∫ y : ℝ, H y * envelope m M γ y) =
      (∑' i, 2 * (ρ i * (1 - ρ i))⁻¹ *
        (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m M (ρ i)).re := by
  have hm0 : 0 < m := by linarith
  obtain ⟨_, hsingle, hv, hk⟩ := gaussian_zero_kernel m M γ hm0
  have hw := weighted_envelope_integrable m M γ hm0
  let φ : ℝ → ℂ := fun y =>
    Complex.exp (-Complex.I * γ * y) * polynomial m M γ y * density m M y
  have hφ (y : ℝ) : ‖φ y‖ ≤ envelope m M γ y := by
    have hd : 0 ≤ density m M y := by unfold density; positivity
    simpa only [φ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
      using (hk hm y).2
  obtain ⟨hiK, heK⟩ := integrate_exponential_series ρ
    (fun i => (ρ i * (1 - ρ i))⁻¹) hstrip hc (envelope m M γ) hv hw φ
    (by dsimp [φ, polynomial, coordinate, density]; fun_prop) hφ
  obtain ⟨hiV, heV⟩ := integrate_exponential_series ρ
    (fun i => (ρ i * (1 - ρ i))⁻¹) hstrip hc (envelope m M γ) hv hw
    (fun y => (envelope m M γ y : ℂ))
    (by dsimp [envelope, coordinate, density]; fun_prop)
    (fun y => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv y)])
  have hρ (i : ι) : ρ i ≠ 0 ∧ ρ i ≠ 1 := by
    constructor
    · intro he
      have h := (hstrip i).1
      simp [he] at h
    · intro he
      have h := (hstrip i).2
      simp [he] at h
  have hsingleK (i : ι) :
      (∫ y : ℝ, (ρ i * (1 - ρ i))⁻¹ * Complex.exp (ρ i * y) * φ y) =
        -transform m M (ρ i - Complex.I * γ) := by
    convert (hsingle (ρ i) (hρ i).1 (hρ i).2).2.2.1 using 1
    congr 1
    funext y
    dsimp only [φ]
    ring
  have hsingleV (i : ι) :
      (∫ y : ℝ, (ρ i * (1 - ρ i))⁻¹ * Complex.exp (ρ i * y) *
        (envelope m M γ y : ℂ)) =
        2 * (ρ i * (1 - ρ i))⁻¹ *
          (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m M (ρ i) :=
    (hsingle (ρ i) (hρ i).1 (hρ i).2).2.2.2
  simp_rw [hsingleK, tsum_neg, hreal] at heK
  simp_rw [hsingleV, hreal] at heV
  simp_rw [hreal] at hiK hiV
  have heKpoint (y : ℝ) : H y * kernel m M γ y = -((H y : ℂ) * φ y).re := by
    simp only [φ, kernel, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, mul_zero, sub_zero]
    ring
  have heVpoint (y : ℝ) : H y * envelope m M γ y =
      ((H y : ℂ) * (envelope m M γ y : ℂ)).re := by simp
  have hintK : Integrable (fun y : ℝ => H y * kernel m M γ y) := by
    simp_rw [heKpoint]
    exact hiK.re.neg
  have hintV : Integrable (fun y : ℝ => H y * envelope m M γ y) := by
    simp_rw [heVpoint]
    exact hiV.re
  refine ⟨hintK, hintV, ?_, ?_⟩
  · simp_rw [heKpoint]
    have hKR : (∫ y : ℝ, ((H y : ℂ) * φ y).re) =
        (∫ y : ℝ, (H y : ℂ) * φ y).re := integral_re hiK
    rw [integral_neg, hKR, heK, Complex.neg_re, neg_neg]
  · simp_rw [heVpoint]
    have hVR : (∫ y : ℝ, ((H y : ℂ) * (envelope m M γ y : ℂ)).re) =
        (∫ y : ℝ, (H y : ℂ) * (envelope m M γ y : ℂ)).re := integral_re hiV
    rw [hVR, heV]


private theorem envelope_factor_bound (z : ℂ) (hstrip : 0 < z.re ∧ z.re < 1)
    (hlow : 10 < |z.im|) (ha : ‖(z * (1 - z))⁻¹‖ ≤ (z.im ^ 2)⁻¹)
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 0 ≤ γ) :
    ‖(z * (1 - z))⁻¹ * (z ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ)))‖ ≤
      (γ + 10) ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hη : 100 < z.im ^ 2 := by nlinarith [sq_abs z.im]
  have hη0 : 0 < z.im ^ 2 := by linarith
  have hhalf : 1 / (2 * m) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * m) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply]
    ring
  have hnormreal : ‖(1 / (2 * (m : ℂ)))‖ = 1 / (2 * m) := by
    rw [show (1 / (2 * (m : ℂ))) = ((1 / (2 * m) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hγreal : ‖(γ : ℂ) ^ 2‖ = γ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hp : ‖z ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))‖ ≤
      z.im ^ 2 + γ ^ 2 + 3 := by
    have h1 := norm_add_le (z ^ 2) ((γ : ℂ) ^ 2)
    have h2 := norm_add_le (z ^ 2 + γ ^ 2) 1
    have h3 := norm_add_le (z ^ 2 + γ ^ 2 + 1) (1 / (2 * (m : ℂ)))
    rw [norm_pow, hz, hγreal] at h1
    rw [norm_one] at h2
    rw [hnormreal] at h3
    nlinarith [sq_nonneg (1 - z.re)]
  rw [norm_mul]
  calc
    _ ≤ (z.im ^ 2)⁻¹ * (z.im ^ 2 + γ ^ 2 + 3) :=
      mul_le_mul ha hp (norm_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ γ ^ 2 + 3 := by
      rw [inv_mul_eq_div, div_le_iff₀ hη0]
      nlinarith [mul_nonneg (sq_nonneg γ) (show 0 ≤ z.im ^ 2 - 1 by linarith)]
    _ ≤ (γ + 10) ^ 2 := by nlinarith


private theorem envelope_series_bound {ι : Type*} [Countable ι]
    (ρ : ι → ℂ) (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (ha : ∀ i, ‖(ρ i * (1 - ρ i))⁻¹‖ ≤ ((ρ i).im ^ 2)⁻¹)
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 0 ≤ γ)
    (hs : Summable (fun i => Real.exp (-m * (ρ i).im ^ 2)))
    (hgauss : (∑' i, Real.exp (-m * (ρ i).im ^ 2)) ≤ 500 * Real.exp (-100 * m)) :
    ‖∑' i, 2 * (ρ i * (1 - ρ i))⁻¹ *
      (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m (16 * m) (ρ i)‖ ≤
        1000 * (γ + 10) ^ 2 * Real.exp (-83 * m) := by
  let F : ι → ℂ := fun i => 2 * (ρ i * (1 - ρ i))⁻¹ *
    (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m (16 * m) (ρ i)
  let B : ℝ := 2 * (γ + 10) ^ 2 * Real.exp (17 * m)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (i : ι) : ‖F i‖ ≤ B * Real.exp (-m * (ρ i).im ^ 2) := by
    have hF : ‖transform m (16 * m) (ρ i)‖ ≤
        Real.exp (17 * m) * Real.exp (-m * (ρ i).im ^ 2) := by
      rw [← Real.exp_add, transform, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul,
        pow_two, Complex.mul_re, Complex.mul_im]
      have hi := hstrip i
      have hb : (ρ i).re ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ m)
        (show 0 ≤ 17 - ((ρ i).re ^ 2 + 16 * (ρ i).re) by nlinarith)]
    have hfac := envelope_factor_bound (ρ i) (hstrip i) (hlow i) (ha i) m γ hm hγ
    dsimp only [F, B]
    rw [show 2 * (ρ i * (1 - ρ i))⁻¹ *
        (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m (16 * m) (ρ i) =
      (2 : ℂ) * ((ρ i * (1 - ρ i))⁻¹ *
        (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ)))) * transform m (16 * m) (ρ i) by ring]
    rw [norm_mul, norm_mul, norm_ofNat]
    calc
      _ ≤ (2 * (γ + 10) ^ 2) * (Real.exp (17 * m) * Real.exp (-m * (ρ i).im ^ 2)) :=
        mul_le_mul (by linarith : 2 * ‖(ρ i * (1 - ρ i))⁻¹ *
          (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ)))‖ ≤ 2 * (γ + 10) ^ 2)
          hF (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hnorm : Summable (fun i => ‖F i‖) :=
    (hs.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  calc
    _ ≤ ∑' i, ‖F i‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, B * Real.exp (-m * (ρ i).im ^ 2) :=
      hnorm.tsum_le_tsum hpoint (hs.mul_left B)
    _ = B * ∑' i, Real.exp (-m * (ρ i).im ^ 2) := tsum_mul_left
    _ ≤ B * (500 * Real.exp (-100 * m)) := mul_le_mul_of_nonneg_left hgauss hB
    _ = _ := by
      dsimp [B]
      rw [show -83 * m = 17 * m + -100 * m by ring, Real.exp_add]
      ring


private theorem gaussian_weighted_tail {x c m : ℝ}
    (hc : 0 < c) (hxc : c ≤ x) (hm : 1 ≤ c * m) :
    Real.exp (-m * x) ≤ c * Real.exp (-m * c) * x⁻¹ := by
  have hx : 0 < x := hc.trans_le hxc
  have hlinear : x ≤ c * (m * (x - c) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxc) (sub_nonneg.mpr hm)]
  have hexp : x ≤ c * Real.exp (m * (x - c)) :=
    hlinear.trans (mul_le_mul_of_nonneg_left (by
      simpa [add_comm] using Real.add_one_le_exp (m * (x - c))) hc.le)
  have hmul := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-m * x))
  have heq : c * Real.exp (m * (x - c)) * Real.exp (-m * x) =
      c * Real.exp (-m * c) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hmul
  have hdiv := (le_div_iff₀ hx).mpr (by simpa [mul_comm] using hmul)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

private theorem low_gaussian_sum {ι : Type*} (η : ι → ℝ)
    (hlow : ∀ i, 10 < |η i|)
    (hs : Summable (fun i => (η i ^ 2)⁻¹))
    (hbudget : ∑' i, (η i ^ 2)⁻¹ ≤ 2) {m : ℝ} (hm : 1 ≤ m) :
    Summable (fun i => Real.exp (-m * η i ^ 2)) ∧
      ∑' i, Real.exp (-m * η i ^ 2) ≤ 500 * Real.exp (-100 * m) := by
  have hterm (i : ι) : Real.exp (-m * η i ^ 2) ≤
      (100 * Real.exp (-100 * m)) * (η i ^ 2)⁻¹ := by
    have hsq : (100 : ℝ) ≤ η i ^ 2 := by nlinarith [sq_abs (η i), hlow i]
    simpa [mul_comm] using gaussian_weighted_tail (by norm_num : (0 : ℝ) < 100)
      hsq (by linarith : 1 ≤ 100 * m)
  have hsum := (hs.mul_left (100 * Real.exp (-100 * m))).of_nonneg_of_le
    (fun _ => Real.exp_nonneg _) hterm
  refine ⟨hsum, ?_⟩
  calc
    ∑' i, Real.exp (-m * η i ^ 2) ≤
        ∑' i, (100 * Real.exp (-100 * m)) * (η i ^ 2)⁻¹ :=
      hsum.tsum_le_tsum hterm (hs.mul_left _)
    _ = (100 * Real.exp (-100 * m)) * (∑' i, (η i ^ 2)⁻¹) := tsum_mul_left
    _ ≤ (100 * Real.exp (-100 * m)) * 2 :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ ≤ 500 * Real.exp (-100 * m) := by nlinarith [Real.exp_nonneg (-100 * m)]

private noncomputable def spectralTerm {ι : Type*} (ρ : ι → ℂ) (γ m : ℝ) (i : ι) : ℂ :=
  Complex.exp ((m : ℂ) * (ρ i - γ * Complex.I) ^ 2 +
    (16 * m : ℝ) * (ρ i - γ * Complex.I))

private theorem spectralTerm_norm {ι : Type*} (ρ : ι → ℂ) (γ m : ℝ) (i : ι) :
    ‖spectralTerm ρ γ m i‖ =
      Real.exp (m * ((ρ i).re ^ 2 + 16 * (ρ i).re - ((ρ i).im - γ) ^ 2)) := by
  rw [spectralTerm, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

private theorem shifted_gaussian_tail {η γ m : ℝ} (hγ : 0 ≤ γ) (hm : 1 ≤ m)
    (hη : η ≠ 0) (hfar : 6 ≤ |η - γ|) :
    Real.exp (-m * (η - γ) ^ 2) ≤
      (γ + 10) ^ 2 * Real.exp (-36 * m) * (η ^ 2)⁻¹ := by
  have ht : 36 ≤ (η - γ) ^ 2 := by nlinarith [sq_abs (η - γ)]
  have hmul := gaussian_weighted_tail (by norm_num : (0 : ℝ) < 36)
    ht (by linarith : 1 ≤ 36 * m)
  have habs : |η| ≤ (γ + 10) / 6 * |η - γ| := by
    have htri : |η| ≤ |η - γ| + γ := by
      simpa [abs_of_nonneg hγ] using (abs_add_le (η - γ) γ)
    have hgap : 0 ≤ (γ + 4) * (|η - γ| - 6) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsq : η ^ 2 ≤ (γ + 10) ^ 2 / 36 * (η - γ) ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg η) (by positivity :
      0 ≤ (γ + 10) / 6 * |η - γ|) |>.mpr habs,
      sq_abs η, sq_abs (η - γ)]
  have hpos : 0 < (η - γ) ^ 2 := by linarith
  have hpη : 0 < η ^ 2 := sq_pos_of_ne_zero hη
  calc
    Real.exp (-m * (η - γ) ^ 2) ≤
        36 * Real.exp (-36 * m) * ((η - γ) ^ 2)⁻¹ := by
      simpa [mul_comm] using hmul
    _ ≤ (γ + 10) ^ 2 * Real.exp (-36 * m) * (η ^ 2)⁻¹ := by
      apply (le_div_iff₀ hpη).mpr
      have hrat : 36 * η ^ 2 ≤ (γ + 10) ^ 2 * (η - γ) ^ 2 := by
        nlinarith [hsq]
      have hrat2 : 36 * ((η - γ) ^ 2)⁻¹ * η ^ 2 ≤ (γ + 10) ^ 2 := by
        have hh := (div_le_iff₀ hpos).mpr hrat
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
      nlinarith [mul_le_mul_of_nonneg_right hrat2 (Real.exp_nonneg (-36 * m))]

private theorem finite_spectral_selection {ι : Type*} (ρ : ι → ℂ)
    (i₀ : ι) (s : Finset ι) (hi₀ : i₀ ∈ s) (m₀ : ℝ) :
    ∃ ν : ℕ, 1 ≤ ν ∧ ν ≤ 2 * s.card + 1 ∧
      Real.exp (((ρ i₀).re ^ 2 + 16 * (ρ i₀).re) * ((ν : ℝ) * m₀)) ≤
        (∑ i ∈ s, spectralTerm ρ (ρ i₀).im ((ν : ℝ) * m₀) i).re := by
  classical
  let a := (ρ i₀).re ^ 2 + 16 * (ρ i₀).re
  let q : ι → ℂ := fun i =>
    (ρ i - (ρ i₀).im * Complex.I) ^ 2 + 16 * (ρ i - (ρ i₀).im * Complex.I)
  let z : ι → ℂ := fun i => Complex.exp ((m₀ : ℂ) * (q i - a))
  have hq : q i₀ = (a : ℂ) := by
    have hw : ρ i₀ - (ρ i₀).im * Complex.I = ((ρ i₀).re : ℂ) := by
      apply Complex.ext <;> simp
    dsimp [q]
    rw [hw]
    simp [a, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_mul]
  have hz : z i₀ = 1 := by simp [z, hq]
  obtain ⟨ν, hν, hνbound, hνsum⟩ :=
    D5.S3.Arith.Robin.ZeroPowerSum.exists_pow_sum_re_ge_one
      (fun j : Fin s.card => z (s.equivFin.symm j))
      ⟨s.equivFin ⟨i₀, hi₀⟩, by simpa using hz⟩
  have hsum : ∑ j : Fin s.card, z (s.equivFin.symm j) ^ ν = ∑ i ∈ s, z i ^ ν := by
    calc
      _ = ∑ i : s, z i ^ ν := s.equivFin.symm.sum_comp (fun i : s => z i ^ ν)
      _ = _ := Finset.sum_coe_sort s (fun i => z i ^ ν)
  rw [hsum] at hνsum
  refine ⟨ν, hν, hνbound, ?_⟩
  have hterm (i : ι) : spectralTerm ρ (ρ i₀).im ((ν : ℝ) * m₀) i =
      (Real.exp (a * ((ν : ℝ) * m₀)) : ℂ) * z i ^ ν := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    dsimp [spectralTerm, q]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa [a] using mul_le_mul_of_nonneg_left hνsum
    (Real.exp_nonneg (a * ((ν : ℝ) * m₀)))

private theorem spectral_far_bound {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (hs : Summable (fun i => ((ρ i).im ^ 2)⁻¹))
    (hbudget : ∑' i, ((ρ i).im ^ 2)⁻¹ ≤ 2)
    (γ m : ℝ) (hγ : 0 ≤ γ) (hm : 1 ≤ m) (s : Finset ι)
    (hfar : ∀ i, i ∉ s → 6 ≤ |(ρ i).im - γ|) :
    Summable (fun i : {i // i ∉ s} => ‖spectralTerm ρ γ m i‖) ∧
      ‖∑' i : {i // i ∉ s}, spectralTerm ρ γ m i‖ ≤
        2 * (γ + 10) ^ 2 * Real.exp (-19 * m) := by
  have hterm (i : {i // i ∉ s}) : ‖spectralTerm ρ γ m i‖ ≤
      ((γ + 10) ^ 2 * Real.exp (-19 * m)) * ((ρ i).im ^ 2)⁻¹ := by
    have hb : (ρ i).re ^ 2 + 16 * (ρ i).re ≤ 17 := by
      nlinarith [mul_nonneg (hstrip i).1.le (sub_nonneg.mpr (hstrip i).2.le)]
    have hη : (ρ i).im ≠ 0 := by
      intro heq
      have := hlow i
      norm_num [heq] at this
    have ht := shifted_gaussian_tail hγ hm hη (hfar i i.property)
    calc
      ‖spectralTerm ρ γ m i‖ =
          Real.exp (m * ((ρ i).re ^ 2 + 16 * (ρ i).re - ((ρ i).im - γ) ^ 2)) :=
        spectralTerm_norm ρ γ m i
      _ ≤ Real.exp (m * (17 - ((ρ i).im - γ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb _) (by linarith)
      _ = Real.exp (17 * m) * Real.exp (-m * ((ρ i).im - γ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (17 * m) *
          ((γ + 10) ^ 2 * Real.exp (-36 * m) * ((ρ i).im ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
      _ = (γ + 10) ^ 2 *
          (Real.exp (17 * m) * Real.exp (-36 * m)) * ((ρ i).im ^ 2)⁻¹ := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 3
        ring
  have hmajor : Summable (fun i : {i // i ∉ s} =>
      ((γ + 10) ^ 2 * Real.exp (-19 * m)) * ((ρ i).im ^ 2)⁻¹) :=
    (hs.subtype (fun i => i ∉ s)).mul_left _
  have hnorm := hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  refine ⟨hnorm, ?_⟩
  have hsubbudget : ∑' i : {i // i ∉ s}, ((ρ i).im ^ 2)⁻¹ ≤ 2 := by
    exact (tsum_comp_le_tsum_of_inj hs (fun i => by positivity)
      (Subtype.coe_injective : Function.Injective (fun i : {i // i ∉ s} => (i : ι)))).trans
      hbudget
  calc
    ‖∑' i : {i // i ∉ s}, spectralTerm ρ γ m i‖ ≤
        ∑' i : {i // i ∉ s}, ‖spectralTerm ρ γ m i‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : {i // i ∉ s},
        ((γ + 10) ^ 2 * Real.exp (-19 * m)) * ((ρ i).im ^ 2)⁻¹ :=
      hnorm.tsum_le_tsum hterm hmajor
    _ = ((γ + 10) ^ 2 * Real.exp (-19 * m)) *
        ∑' i : {i // i ∉ s}, ((ρ i).im ^ 2)⁻¹ := tsum_mul_left
    _ ≤ ((γ + 10) ^ 2 * Real.exp (-19 * m)) * 2 :=
      mul_le_mul_of_nonneg_left hsubbudget (by positivity)
    _ = _ := by ring

private theorem full_spectral_selection {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (hs : Summable (fun i => ((ρ i).im ^ 2)⁻¹))
    (hbudget : ∑' i, ((ρ i).im ^ 2)⁻¹ ≤ 2)
    (hheight : ∀ T : ℝ, 0 < T → Set.Finite {i | |(ρ i).im| ≤ T} ∧
      (({i | |(ρ i).im| ≤ T} : Set ι).ncard : ℝ) ≤ 2 * T ^ 2)
    (i₀ : ι) (hβ : (1 / 2 : ℝ) < (ρ i₀).re) (hγ : 0 < (ρ i₀).im) :
    let β := (ρ i₀).re
    let γ := (ρ i₀).im
    let δ := β - 1 / 2
    let D := γ + 10
    let m₀ := 100 * D ^ 2 * (δ ^ 2)⁻¹
    let m₁ := 500 * D ^ 4 * (δ ^ 2)⁻¹
    let a := β ^ 2 + 16 * β
    ∃ m : ℝ, m₀ ≤ m ∧ m ≤ m₁ ∧ 1 ≤ m ∧
      Summable (spectralTerm ρ γ m) ∧
      Real.exp (a * m) / 2 ≤ (∑' i, spectralTerm ρ γ m i).re := by
  classical
  dsimp only
  let β := (ρ i₀).re
  let γ := (ρ i₀).im
  let δ := β - 1 / 2
  let D := γ + 10
  let m₀ := 100 * D ^ 2 * (δ ^ 2)⁻¹
  let a := β ^ 2 + 16 * β
  have hβ0 : 0 < β := (hstrip i₀).1
  have hβ1 : β < 1 := (hstrip i₀).2
  have hδ0 : 0 < δ := by dsimp [δ, β]; linarith
  have hδ1 : δ < 1 / 2 := by dsimp [δ]; linarith
  have hγ10 : 10 < γ := by
    simpa only [abs_of_pos hγ] using hlow i₀
  have hD : 20 < D := by dsimp [D]; linarith
  have hDsq : 1 ≤ D ^ 2 := by nlinarith
  have hinv : 1 ≤ (δ ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hδ0)).mpr (by nlinarith)
  have hm₀D : D ^ 2 ≤ m₀ := by
    dsimp [m₀]
    nlinarith [mul_le_mul_of_nonneg_left hinv (show 0 ≤ 100 * D ^ 2 by positivity)]
  have hm₀ : 1 ≤ m₀ := hDsq.trans hm₀D
  have hT : 0 < γ + 6 := by linarith
  obtain ⟨ht, htcard⟩ := hheight (γ + 6) hT
  let t := ht.toFinset
  let s := t.filter (fun i => |(ρ i).im - γ| ≤ 6)
  have hnear (i : ι) : i ∈ s ↔ |(ρ i).im - γ| ≤ 6 := by
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      apply Finset.mem_filter.mpr
      refine ⟨?_, hi⟩
      apply ht.mem_toFinset.mpr
      have htri : |(ρ i).im| ≤ |(ρ i).im - γ| + γ := by
        simpa only [sub_add_cancel, abs_of_nonneg (show 0 ≤ γ from hγ.le)] using
          (abs_add_le ((ρ i).im - γ) γ)
      exact htri.trans (by linarith)
  have hi₀ : i₀ ∈ s := (hnear i₀).mpr (by simp [γ])
  have hscard : (s.card : ℝ) ≤ 2 * D ^ 2 := by
    have hst : (s.card : ℝ) ≤ (t.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    have htc : (t.card : ℝ) ≤ 2 * (γ + 6) ^ 2 := by
      simpa only [Set.ncard_eq_toFinset_card _ ht] using htcard
    have hcomp : 2 * (γ + 6) ^ 2 ≤ 2 * D ^ 2 := by dsimp [D]; nlinarith
    exact hst.trans (htc.trans hcomp)
  obtain ⟨ν, hν, hνbound, hmain⟩ := finite_spectral_selection ρ i₀ s hi₀ m₀
  let m := (ν : ℝ) * m₀
  have hνR : 1 ≤ (ν : ℝ) := by exact_mod_cast hν
  have hmm₀ : m₀ ≤ m := by dsimp [m]; nlinarith
  have hm : 1 ≤ m := hm₀.trans hmm₀
  have hmD : D ^ 2 ≤ m := hm₀D.trans hmm₀
  have hνupper : (ν : ℝ) ≤ 5 * D ^ 2 := by
    have hνb : (ν : ℝ) ≤ 2 * (s.card : ℝ) + 1 := by exact_mod_cast hνbound
    linarith
  have hupper : m ≤ 500 * D ^ 4 * (δ ^ 2)⁻¹ := by
    calc
      m ≤ (5 * D ^ 2) * m₀ := mul_le_mul_of_nonneg_right hνupper (by linarith)
      _ = _ := by dsimp [m₀]; ring
  have hfar : ∀ i, i ∉ s → 6 ≤ |(ρ i).im - γ| := by
    intro i hi
    exact (lt_of_not_ge (fun hh => hi ((hnear i).mpr hh))).le
  obtain ⟨hfarSum, hfarBound⟩ := spectral_far_bound ρ hstrip hlow hs hbudget
    γ m hγ.le hm s hfar
  have hfull : Summable (spectralTerm ρ γ m) := by
    apply (summable_subtype_and_compl (s := (s : Set ι))).mp
    exact ⟨(hasSum_fintype _).summable, hfarSum.of_norm⟩
  have htailSmall : 2 * D ^ 2 * Real.exp (-19 * m) ≤ 1 / 2 := by
    have hlarge : 4 * D ^ 2 ≤ Real.exp (19 * m) := by
      nlinarith [Real.add_one_le_exp (19 * m)]
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg (-19 * m))
    have hcancel : Real.exp (19 * m) * Real.exp (-19 * m) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hcancel] at hh
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : 1 ≤ Real.exp (a * m) := Real.one_le_exp (mul_nonneg ha (by linarith))
  have htailre : -(1 / 2 : ℝ) ≤
      (∑' i : {i // i ∉ s}, spectralTerm ρ γ m i).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm
      (∑' i : {i // i ∉ s}, spectralTerm ρ γ m i))).1
    have hfb : ‖∑' i : {i // i ∉ s}, spectralTerm ρ γ m i‖ ≤ 1 / 2 := by
      exact hfarBound.trans htailSmall
    linarith
  refine ⟨m, hmm₀, hupper, hm, hfull, ?_⟩
  have heq := congrArg Complex.re (hfull.sum_add_tsum_subtype_compl s)
  simp only [Complex.add_re] at heq
  dsimp only [m, a, γ, β] at *
  linarith


/-- A zero to the right of the critical line gives a positive full Gaussian response
at a controlled scale, with exact signed integration and a small envelope integral. -/
theorem full_zero_gaussian_response {ι : Type*} [Countable ι] (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (conjIndex : ι ≃ ι) (hconj : ∀ i, ρ (conjIndex i) = star (ρ i))
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (hmass : HasSum (fun i => (ρ i * (1 - ρ i))⁻¹)
      (ZeroCoefficientBudget.massConstant : ℂ))
    (i₀ : ι) (hβ : (1 / 2 : ℝ) < (ρ i₀).re) (hγ : 0 < (ρ i₀).im) :
    let β := (ρ i₀).re
    let γ := (ρ i₀).im
    let δ := β - 1 / 2
    let D := γ + 10
    let m₀ := 100 * D ^ 2 * (δ ^ 2)⁻¹
    let m₁ := 500 * D ^ 4 * (δ ^ 2)⁻¹
    let a := β ^ 2 + 16 * β
    ∃ m : ℝ, m₀ ≤ m ∧ m ≤ m₁ ∧ 1 ≤ m ∧
      Summable (fun i => transform m (16 * m) (ρ i - Complex.I * γ)) ∧
      Integrable (fun y : ℝ => Real.exp (max y 0) * envelope m (16 * m) γ y) ∧
      Integrable (fun y : ℝ => ZeroCoefficientBudget.H ρ y * kernel m (16 * m) γ y) ∧
      Integrable (fun y : ℝ => ZeroCoefficientBudget.H ρ y * envelope m (16 * m) γ y) ∧
      (∫ y : ℝ, ZeroCoefficientBudget.H ρ y * kernel m (16 * m) γ y) =
        (∑' i, transform m (16 * m) (ρ i - Complex.I * γ)).re ∧
      Real.exp (a * m) / 2 ≤ (∑' i, transform m (16 * m) (ρ i - Complex.I * γ)).re ∧
      |∫ y : ℝ, ZeroCoefficientBudget.H ρ y * envelope m (16 * m) γ y| ≤
        1000 * D ^ 2 * Real.exp (-83 * m) ∧
      (∫ y : ℝ, ZeroCoefficientBudget.H ρ y * envelope m (16 * m) γ y) =
        (∑' i, 2 * (ρ i * (1 - ρ i))⁻¹ *
          (ρ i ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m (16 * m) (ρ i)).re ∧
      (∀ y : ℝ, 0 ≤ envelope m (16 * m) γ y ∧
        |kernel m (16 * m) γ y| ≤ envelope m (16 * m) γ y) := by
  obtain ⟨hc, hs, hsum, hC, _, hheight, hH, hpoint⟩ :=
    ZeroCoefficientBudget.zero_coefficient_budget ρ hstrip conjIndex hconj hlow hmass
  have hb : (∑' i, ((ρ i).im ^ 2)⁻¹) ≤ 2 := hsum.trans hC.le
  obtain ⟨m, hm₀, hm₁, hm, hE, hmain⟩ :=
    full_spectral_selection ρ hstrip hlow hs hb hheight i₀ hβ hγ
  have heq (i : ι) : spectralTerm ρ (ρ i₀).im m i =
      transform m (16 * m) (ρ i - Complex.I * (ρ i₀).im) := by
    dsimp [spectralTerm, transform]
    congr 1
    ring
  have hEs := hE.congr heq
  simp_rw [heq] at hmain
  have hreal (y : ℝ) :
      (∑' i, (ρ i * (1 - ρ i))⁻¹ * Complex.exp (ρ i * y)) =
        (ZeroCoefficientBudget.H ρ y : ℂ) := by
    simpa only [ZeroCoefficientBudget.Hc, ZeroCoefficientBudget.coefficient] using (hH y).2.1
  have hcoeff : Summable (fun i => ‖(ρ i * (1 - ρ i))⁻¹‖) := hc
  obtain ⟨hiK, hiV, hK, hV⟩ := zero_family_integrals ρ hstrip hcoeff
    (ZeroCoefficientBudget.H ρ) hreal m (16 * m) (ρ i₀).im hm
  obtain ⟨hgs, hgb⟩ := low_gaussian_sum (fun i => (ρ i).im) hlow hs hb hm
  have hfac : ∀ i, ‖(ρ i * (1 - ρ i))⁻¹‖ ≤ ((ρ i).im ^ 2)⁻¹ :=
    fun i => (hpoint i).2
  have hsmall := envelope_series_bound ρ hstrip hlow hfac m (ρ i₀).im hm hγ.le hgs hgb
  refine ⟨m, hm₀, hm₁, hm, hEs, weighted_envelope_integrable m (16 * m) (ρ i₀).im
    (by linarith), hiK, hiV, hK, hmain, ?_, hV, ?_⟩
  · rw [hV]
    exact (Complex.abs_re_le_norm _).trans hsmall
  · intro y
    have hg := gaussian_zero_kernel m (16 * m) (ρ i₀).im (by linarith)
    exact ⟨hg.2.2.1 y, (hg.2.2.2 hm y).1⟩

end

end D5.S3.Arith.Robin.FullZeroGaussianResponse
