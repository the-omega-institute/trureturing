/- GID: D5/S3/Arith/Robin/GaussianZeroKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GaussianZeroKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments give the polynomial zero response and its positive envelope. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic

/-! The normal density, its centered moments, and the signed polynomial response. -/

namespace D5.S3.Arith.Robin.GaussianZeroKernel

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
theorem gaussian_zero_kernel (m M γ : ℝ) (hm : 0 < m) :
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

end

end D5.S3.Arith.Robin.GaussianZeroKernel
