/- GID: D5/S3/Fourier/MatrixGaussianSecondMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussianSecondMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial Gaussian Fourier integration and inverse-form second moments. -/

import D5.S3.Fourier.MatrixGaussianTheta
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Quadratic Gaussian weights and inverse-form theta moments -/

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators Topology

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section

variable {r : ℕ}

private def pairing (A : Matrix (Fin r) (Fin r) ℝ) (u x : Fin r → ℝ) : ℝ :=
  u ⬝ᵥ A *ᵥ x

private lemma quadratic_nonneg (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (x : Fin r → ℝ) : 0 ≤ quadratic A x := by
  simpa [quadratic] using hA.posSemidef.dotProduct_mulVec_nonneg x

private lemma pairing_sq_le (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u x : Fin r → ℝ) : pairing A u x ^ 2 ≤ quadratic A u * quadratic A x := by
  simpa [pairing, quadratic, pow_two] using hA.star_dotProduct_mulVec_mul_le u x

private lemma quadratic_exp_bound (s p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    p * Real.exp (-s * p) ≤ (2 / s) * Real.exp (-(s / 2) * p) := by
  have he : s / 2 * p ≤ Real.exp (s / 2 * p) := by
    linarith [Real.add_one_le_exp (s / 2 * p)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-s * p)).le
  rw [← Real.exp_add] at hm
  have hx : s / 2 * p + -s * p = -(s / 2) * p := by ring
  rw [hx] at hm
  apply le_of_mul_le_mul_left _ hs
  calc
    s * (p * Real.exp (-s * p)) = 2 * (s / 2 * p * Real.exp (-s * p)) := by ring
    _ ≤ 2 * Real.exp (-(s / 2) * p) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = s * (2 / s * Real.exp (-(s / 2) * p)) := by field_simp

private lemma norm_gaussian (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (x : Fin r → ℝ) :
    ‖gaussianMap A b x‖ = Real.exp (-(Real.pi * b.re) * quadratic A x) := by
  change ‖Complex.exp (-Real.pi * b * (quadratic A x : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

private lemma weighted_bound (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v x : Fin r → ℝ) :
    ‖(pairing A u x : ℂ) * (pairing A v x : ℂ) * gaussianMap A b x‖ ≤
      ((quadratic A u + quadratic A v) / (Real.pi * b.re)) *
        ‖gaussianMap A (b / 2) x‖ := by
  let s := Real.pi * b.re
  have hs : 0 < s := mul_pos Real.pi_pos hb
  have hq := quadratic_nonneg A hA x
  have hu := pairing_sq_le A hA u x
  have hv := pairing_sq_le A hA v x
  have huv : |pairing A u x| * |pairing A v x| ≤
      (quadratic A u + quadratic A v) / 2 * quadratic A x := by
    nlinarith [sq_nonneg (|pairing A u x| - |pairing A v x|), sq_abs (pairing A u x),
      sq_abs (pairing A v x)]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, norm_gaussian, norm_gaussian]
  have hn : 0 ≤ (quadratic A u + quadratic A v) / 2 := by
    exact div_nonneg (add_nonneg (quadratic_nonneg A hA u) (quadratic_nonneg A hA v)) (by norm_num)
  calc
    _ ≤ ((quadratic A u + quadratic A v) / 2 * quadratic A x) *
        Real.exp (-s * quadratic A x) := mul_le_mul_of_nonneg_right huv (Real.exp_pos _).le
    _ = (quadratic A u + quadratic A v) / 2 *
        (quadratic A x * Real.exp (-s * quadratic A x)) := by ring
    _ ≤ (quadratic A u + quadratic A v) / 2 *
        (2 / s * Real.exp (-(s / 2) * quadratic A x)) :=
      mul_le_mul_of_nonneg_left (quadratic_exp_bound s _ hs hq) hn
    _ = _ := by dsimp [s]; simp [Complex.div_re]; ring

private lemma linear_bound (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u x : Fin r → ℝ) :
    ‖(pairing A u x : ℂ) * gaussianMap A b x‖ ≤
      (1 + 2 * quadratic A u / (Real.pi * b.re)) * ‖gaussianMap A (b / 2) x‖ := by
  let s := Real.pi * b.re
  have hs : 0 < s := mul_pos Real.pi_pos hb
  have hq := quadratic_nonneg A hA x
  have hu := quadratic_nonneg A hA u
  have hw := pairing_sq_le A hA u x
  have ha : |pairing A u x| ≤ 1 + quadratic A u * quadratic A x := by
    nlinarith [sq_nonneg (|pairing A u x| - 1 / 2), sq_abs (pairing A u x)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussian, norm_gaussian]
  have he : Real.exp (-s * quadratic A x) ≤ Real.exp (-(s / 2) * quadratic A x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (1 + quadratic A u * quadratic A x) * Real.exp (-s * quadratic A x) :=
      mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le
    _ = Real.exp (-s * quadratic A x) + quadratic A u *
        (quadratic A x * Real.exp (-s * quadratic A x)) := by ring
    _ ≤ Real.exp (-(s / 2) * quadratic A x) + quadratic A u *
        (2 / s * Real.exp (-(s / 2) * quadratic A x)) :=
      add_le_add he (mul_le_mul_of_nonneg_left (quadratic_exp_bound s _ hs hq) hu)
    _ = _ := by dsimp [s]; simp [Complex.div_re]; ring

private lemma integrable_gaussian (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) : Integrable (gaussianMap A b) := by
  convert integrable_gaussian_linear A hA ((Real.pi : ℂ) * b)
    (by simpa using mul_pos Real.pi_pos hb) 0 0 using 1
  funext x
  simp [gaussianMap, neg_mul]

private def weightedMap (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (u v : Fin r → ℝ) : C(Fin r → ℝ, ℂ) where
  toFun x := (pairing A u x : ℂ) * (pairing A v x : ℂ) * gaussianMap A b x
  continuous_toFun := by unfold pairing gaussianMap quadratic dotProduct Matrix.mulVec; fun_prop

private lemma integrable_weighted (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v : Fin r → ℝ) :
    Integrable (weightedMap A b u v) := by
  refine ((integrable_gaussian A hA (b / 2) (by simpa using half_pos hb)).norm.const_mul
    ((quadratic A u + quadratic A v) / (Real.pi * b.re))).mono'
    (weightedMap A b u v).continuous.aestronglyMeasurable ?_
  exact ae_of_all _ (weighted_bound A hA b hb u v)

private lemma integrable_linear (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u : Fin r → ℝ) :
    Integrable (fun x => (pairing A u x : ℂ) * gaussianMap A b x) := by
  refine ((integrable_gaussian A hA (b / 2) (by simpa using half_pos hb)).norm.const_mul
    (1 + 2 * quadratic A u / (Real.pi * b.re))).mono' (by
      have hc : Continuous (fun x => (pairing A u x : ℂ) * gaussianMap A b x) := by
        unfold pairing gaussianMap quadratic dotProduct Matrix.mulVec; fun_prop
      exact hc.aestronglyMeasurable) ?_
  exact ae_of_all _ (linear_bound A hA b hb u)

private lemma summable_norm_weighted (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v : Fin r → ℝ) :
    Summable (fun n : Fin r → ℤ => ‖weightedMap A b u v (fun i => (n i : ℝ))‖) := by
  refine ((summable_norm_gaussian A hA (b / 2) (by simpa using half_pos hb)).mul_left
    ((quadratic A u + quadratic A v) / (Real.pi * b.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  exact weighted_bound A hA b hb u v _

private lemma locally_summable_norm_weighted (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v : Fin r → ℝ)
    (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun n : Fin r → ℤ =>
      ‖((weightedMap A b u v).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖) := by
  let c := (quadratic A u + quadratic A v) / (Real.pi * b.re)
  have hc : 0 ≤ c := div_nonneg
    (add_nonneg (quadratic_nonneg A hA u) (quadratic_nonneg A hA v))
    (mul_pos Real.pi_pos hb).le
  refine ((locally_summable_norm_gaussian A hA (b / 2)
    (by simpa using half_pos hb) K).mul_left c).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  apply (ContinuousMap.norm_le _ (mul_nonneg hc (norm_nonneg _))).mpr
  intro x
  exact (weighted_bound A hA b hb u v _).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm
      (((gaussianMap A (b / 2)).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K) x) hc)

private def phase (w x : Fin r → ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ))

private lemma norm_phase (w x : Fin r → ℝ) : ‖phase w x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private lemma integrable_phase_mul {f : (Fin r → ℝ) → ℂ} (hf : Integrable f)
    (w : Fin r → ℝ) : Integrable (fun x => phase w x * f x) := by
  apply hf.norm.mono' (by
    have hc : Continuous (phase w) := by unfold phase dotProduct; fun_prop
    exact hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with x
  simp [norm_mul, norm_phase]

private lemma phase_deriv (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u w x : Fin r → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phase (w + s • (A *ᵥ u)) x)
      ((-2 * Real.pi * Complex.I) * (pairing A u x : ℂ) *
        phase (w + t • (A *ᵥ u)) x) t := by
  have he : ∀ s : ℝ, (w + s • (A *ᵥ u)) ⬝ᵥ x =
      w ⬝ᵥ x + s * pairing A u x := by
    intro s
    rw [add_dotProduct, smul_dotProduct]
    have hh : (A *ᵥ u) ⬝ᵥ x = pairing A u x := by
      rw [dotProduct_comm]
      simpa [pairing] using hA.isHermitian.star_dotProduct_mulVec_comm x u
    simp [smul_eq_mul, hh]
  simp_rw [phase, he]
  have hd := (((hasDerivAt_id t).mul_const (pairing A u x)).const_add (w ⬝ᵥ x)).ofReal_comp
  convert (hd.const_mul (-2 * Real.pi * Complex.I)).cexp using 1 <;>
    simp only [id_eq, one_mul] <;> ring

private lemma fourier_deriv (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u w : Fin r → ℝ) (f : (Fin r → ℝ) → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hu : Integrable (fun x => (pairing A u x : ℂ) * f x)) :
    HasDerivAt (fun t : ℝ => ∫ x, phase (w + t • (A *ᵥ u)) x * f x)
      ((-2 * Real.pi * Complex.I) * ∫ x, phase w x * (pairing A u x : ℂ) * f x) 0 := by
  let F := fun t : ℝ => fun x : Fin r → ℝ => phase (w + t • (A *ᵥ u)) x * f x
  let F' := fun t : ℝ => fun x : Fin r → ℝ =>
    (-2 * Real.pi * Complex.I) * (pairing A u x : ℂ) * phase (w + t • (A *ᵥ u)) x * f x
  have hm : ∀ t, Continuous (F t) := by
    intro t
    dsimp [F]
    have hp : Continuous (phase (w + t • (A *ᵥ u))) := by unfold phase dotProduct; fun_prop
    exact hp.mul hc
  have hm' : Continuous (F' 0) := by
    dsimp [F']
    have hl : Continuous (fun x => (pairing A u x : ℂ)) := by
      unfold pairing dotProduct Matrix.mulVec; fun_prop
    have hp : Continuous (phase (w + (0 : ℝ) • (A *ᵥ u))) := by
      unfold phase dotProduct; fun_prop
    exact ((continuous_const.mul hl).mul hp).mul hc
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x => (2 * Real.pi) * ‖(pairing A u x : ℂ) * f x‖)
    (s := Set.univ) (by simp)
    (Eventually.of_forall fun t => (hm t).aestronglyMeasurable)
    (by simpa [F] using integrable_phase_mul hf w)
    hm'.aestronglyMeasurable
    (ae_of_all _ (fun x t _ => by
      dsimp [F']
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, norm_phase, mul_one]
      norm_num
      ring_nf
      exact le_rfl))
    (hu.norm.const_mul (2 * Real.pi))
    (ae_of_all _ (fun x t _ => (phase_deriv A hA u w x t).mul_const (f x)))
  convert hd.2 using 1
  simp only [F', zero_smul, add_zero]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

private lemma pairing_symm (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u v : Fin r → ℝ) : pairing A u v = pairing A v u := by
  simpa [pairing] using hA.isHermitian.star_dotProduct_mulVec_comm u v

private lemma pairing_transport (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u w : Fin r → ℝ) : pairing A⁻¹ (A *ᵥ u) w = u ⬝ᵥ w := by
  rw [pairing_symm A⁻¹ hA.inv]
  unfold pairing
  rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec,
    dotProduct_comm]

private lemma quadratic_shift_inverse (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u w : Fin r → ℝ) (t : ℝ) :
    quadratic A⁻¹ (w + t • (A *ᵥ u)) = quadratic A⁻¹ w +
      2 * t * (u ⬝ᵥ w) + t ^ 2 * quadratic A u := by
  have hm : A⁻¹ *ᵥ (A *ᵥ u) = u := by
    rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  unfold quadratic
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hm]
  have ht := pairing_transport A hA u w
  change (A *ᵥ u) ⬝ᵥ A⁻¹ *ᵥ w = u ⬝ᵥ w at ht
  rw [ht, dotProduct_comm w u, dotProduct_comm (A *ᵥ u) u]
  ring

private lemma gaussian_answer_deriv (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (u w : Fin r → ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp
      (-Real.pi / b * (quadratic A⁻¹ (w + t • (A *ᵥ u)) : ℂ)))
      (Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ)) *
        (-2 * Real.pi / b * (u ⬝ᵥ w : ℝ))) 0 := by
  simp_rw [quadratic_shift_inverse A hA]
  have h := ((hasDerivAt_const (0 : ℝ) (quadratic A⁻¹ w)).add
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (u ⬝ᵥ w))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (quadratic A u))
  convert (h.ofReal_comp.const_mul (-(Real.pi : ℂ) / b)).cexp using 1 <;>
    simp <;> ring

private lemma integral_fourier_linear (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u w : Fin r → ℝ) :
    (∫ x, phase w x * (pairing A u x : ℂ) * gaussianMap A b x) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        (-(Complex.I) / b * (u ⬝ᵥ w : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ)) := by
  let c := (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2)
  have hd := fourier_deriv A hA u w (gaussianMap A b) (gaussianMap A b).continuous
    (integrable_gaussian A hA b hb) (integrable_linear A hA b hb u)
  have he : (fun t : ℝ => ∫ x, phase (w + t • (A *ᵥ u)) x * gaussianMap A b x) =
      (fun t : ℝ => c * Complex.exp
        (-Real.pi / b * (quadratic A⁻¹ (w + t • (A *ᵥ u)) : ℂ))) := by
    funext t
    simpa [c, phase, gaussianMap] using integral_fourier_gaussian A hA b hb (w + t • (A *ᵥ u))
  rw [he] at hd
  have hh := hd.unique ((gaussian_answer_deriv A hA b u w).const_mul c)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (mul_left_cancel₀ (show -2 * (Real.pi : ℂ) * Complex.I ≠ 0 by simp [hp]))
  rw [hh]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  <;> ring

/-- The quadratic-weight Fourier transform, with coordinate Lebesgue measure.
The covariance term is positive and the frequency product is negative. -/
theorem integral_fourier_second_moment (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      ((u ⬝ᵥ A *ᵥ x : ℝ) : ℂ) * ((v ⬝ᵥ A *ᵥ x : ℝ) : ℂ) *
      Complex.exp (-Real.pi * b * (quadratic A x : ℂ))) =
    (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      (((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) / (2 * Real.pi * b) -
        ((u ⬝ᵥ w : ℝ) : ℂ) * ((v ⬝ᵥ w : ℝ) : ℂ) / b ^ 2) *
      Complex.exp (-Real.pi / b * (quadratic A⁻¹ w : ℂ)) := by
  let c := (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2)
  let f := fun x : Fin r → ℝ => (pairing A u x : ℂ) * gaussianMap A b x
  have hc : Continuous f := by
    dsimp [f]; unfold pairing gaussianMap quadratic dotProduct Matrix.mulVec; fun_prop
  have hf : Integrable f := integrable_linear A hA b hb u
  have hv : Integrable (fun x => (pairing A v x : ℂ) * f x) := by
    convert integrable_weighted A hA b hb u v using 1
    funext x
    simp only [f, weightedMap, ContinuousMap.coe_mk]
    ring
  have hd := fourier_deriv A hA v w f hc hf hv
  have he : (fun t : ℝ => ∫ x, phase (w + t • (A *ᵥ v)) x * f x) =
      (fun t : ℝ => c * (-(Complex.I) / b *
        ((u ⬝ᵥ w + t * pairing A u v : ℝ) : ℂ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ (w + t • (A *ᵥ v)) : ℂ))) := by
    funext t
    rw [show (∫ x, phase (w + t • (A *ᵥ v)) x * f x) =
      (∫ x, phase (w + t • (A *ᵥ v)) x * (pairing A u x : ℂ) * gaussianMap A b x) by
        apply integral_congr_ae; filter_upwards with x; dsimp [f]; ring]
    rw [integral_fourier_linear A hA b hb]
    simp [c, dotProduct_add, dotProduct_smul, smul_eq_mul, pairing]
  rw [he] at hd
  have hl := (((hasDerivAt_id (0 : ℝ)).mul_const (pairing A u v)).const_add
    (u ⬝ᵥ w)).ofReal_comp
  have hh := hd.unique (((hl.const_mul (-Complex.I / b)).const_mul c).mul
    (gaussian_answer_deriv A hA b v w))
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  apply (mul_left_cancel₀ (show -2 * (Real.pi : ℂ) * Complex.I ≠ 0 by simp [hp]))
  have hi : (∫ x, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      ((u ⬝ᵥ A *ᵥ x : ℝ) : ℂ) * ((v ⬝ᵥ A *ᵥ x : ℝ) : ℂ) *
      Complex.exp (-Real.pi * b * (quadratic A x : ℂ))) =
    (∫ x, phase w x * (pairing A v x : ℂ) * f x) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [phase, pairing, f, gaussianMap]
    ring
  rw [hi, hh]
  simp only [zero_mul, add_zero, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_one, mul_zero, zero_add, Complex.ofReal_zero] 
  dsimp [c, pairing]
  field_simp
  simp [Complex.I_sq]
  <;> ring

/-- The two bilinear current weights on the original integer-coordinate lattice. -/
def momentTerm (A : Matrix (Fin r) (Fin r) ℝ) (u v : Fin r → ℝ)
    (τ : ℂ) (n : Fin r → ℤ) : ℂ :=
  ((u ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  ((v ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  Complex.exp (Real.pi * Complex.I * τ * (quadratic A (fun i => (n i : ℝ)) : ℂ))

/-- The absolutely convergent second-moment series when the Gram matrix is
positive definite and the parameter is in the upper half-plane. -/
def secondMoment (A : Matrix (Fin r) (Fin r) ℝ) (u v : Fin r → ℝ) (τ : ℂ) : ℂ :=
  ∑' n : Fin r → ℤ, momentTerm A u v τ n

private lemma weighted_poisson (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (u v : Fin r → ℝ) :
    (∑' n : Fin r → ℤ, weightedMap A b u v (fun i => (n i : ℝ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      (((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) / (2 * Real.pi * b) *
        (∑' n : Fin r → ℤ, gaussianMap A⁻¹ b⁻¹ (fun i => (n i : ℝ))) -
        1 / b ^ 2 * ∑' n : Fin r → ℤ,
          weightedMap A⁻¹ b⁻¹ (A *ᵥ u) (A *ᵥ v) (fun i => (n i : ℝ))) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  let c := (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2)
  let g := ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) / (2 * Real.pi * b)
  have hs : Summable (fun n : Fin r → ℤ => gaussianMap A⁻¹ b⁻¹ (fun i => (n i : ℝ))) :=
    (summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi).of_norm
  have hw := (summable_norm_weighted A⁻¹ hA.inv b⁻¹ hbi (A *ᵥ u) (A *ᵥ v)).of_norm
  have hft (k : Fin r → ℤ) :
    (∫ x, Complex.exp (-2 * Real.pi * Complex.I *
      (∑ i, (k i : ℝ) * x i : ℝ)) * weightedMap A b u v x) =
      c * (g * gaussianMap A⁻¹ b⁻¹ (fun i => (k i : ℝ)) -
        (1 / b ^ 2) * weightedMap A⁻¹ b⁻¹ (A *ᵥ u) (A *ᵥ v) (fun i => (k i : ℝ))) := by
    have h := integral_fourier_second_moment A hA b hb u v (fun i => (k i : ℝ))
    convert h using 1
    · apply integral_congr_ae
      filter_upwards with x
      simp only [weightedMap, gaussianMap, ContinuousMap.coe_mk, pairing, dotProduct]
      ring
    · dsimp [c, g, weightedMap]
      rw [pairing_transport A hA, pairing_transport A hA]
      dsimp [gaussianMap]
      simp only [div_eq_mul_inv, neg_mul, mul_sub, sub_mul]
      ring
  have hsf := ((hs.mul_left g).sub (hw.mul_left (1 / b ^ 2))).mul_left c
  have hp := CoordinatePoisson.tsum_eq_tsum_integral (integrable_weighted A hA b hb u v)
    (locally_summable_norm_weighted A hA b hb u v) (hsf.congr (fun k => (hft k).symm))
  rw [hp]
  simp_rw [hft]
  rw [tsum_mul_left, (hs.mul_left g).tsum_sub (hw.mul_left (1 / b ^ 2)),
    tsum_mul_left, tsum_mul_left]
  rfl

/-- Principal-branch second-moment inversion for every finite real positive
Gram matrix. Inversion transports the polarizations by A and adds the metric
correction; no integrality or determinant-unit hypothesis is imposed. -/
theorem second_moment_inversion (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (u v : Fin r → ℝ) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : Fin r → ℤ => ‖momentTerm A u v (-1 / τ) n‖) ∧
    HasSum (momentTerm A u v (-1 / τ))
      (((-Complex.I * τ) ^ ((r : ℂ) / 2) / (Real.sqrt A.det : ℂ)) *
        (τ ^ 2 * secondMoment A⁻¹ (A *ᵥ u) (A *ᵥ v) τ +
          τ / (2 * Real.pi * Complex.I) * ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) * theta A⁻¹ τ)) := by
  let z := -Complex.I * τ
  have hz : 0 < z.re := by simpa [z] using hτ
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hτ0 : τ ≠ 0 := by intro h; simpa [h] using hτ
  have hzi : 0 < (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have harg : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hleft : -(Real.pi : ℂ) * z⁻¹ = Real.pi * Complex.I * (-1 / τ) := by
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hright : -(Real.pi : ℂ) * (z⁻¹)⁻¹ = Real.pi * Complex.I * τ := by
    dsimp [z]
    rw [inv_inv]
    ring
  have hs : Summable (fun n : Fin r → ℤ => ‖momentTerm A u v (-1 / τ) n‖) := by
    simpa [weightedMap, gaussianMap, pairing, momentTerm, hleft] using
      summable_norm_weighted A hA z⁻¹ hzi u v
  refine ⟨hs, ?_⟩
  suffices heq : secondMoment A u v (-1 / τ) =
      (((-Complex.I * τ) ^ ((r : ℂ) / 2) / (Real.sqrt A.det : ℂ)) *
        (τ ^ 2 * secondMoment A⁻¹ (A *ᵥ u) (A *ᵥ v) τ +
          τ / (2 * Real.pi * Complex.I) * ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) * theta A⁻¹ τ)) by
    rw [← heq]
    exact hs.of_norm.hasSum
  have h := weighted_poisson A hA z⁻¹ hzi u v
  have he : -(-(r : ℂ) / 2) = (r : ℂ) / 2 := by ring
  simp only [weightedMap, ContinuousMap.coe_mk, gaussianMap, pairing, hleft, hright] at h
  change secondMoment A u v (-1 / τ) = _ at h
  rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, he] at h
  rw [h]
  change _ = _
  unfold secondMoment momentTerm theta
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [z]
  field_simp
  simp [Complex.I_sq]
  <;> ring

#print axioms integral_fourier_second_moment
#print axioms second_moment_inversion

end
end D5.S3.Fourier.MatrixGaussian
