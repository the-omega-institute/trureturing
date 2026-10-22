/- GID: D5/S3/Fourier/MatrixGaussianPoisson
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussianPoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate lattice summability and Fourier periodization for positive matrix Gaussians. -/

import D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.CoordinatePoisson
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Matrix
open scoped BigOperators

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section

private lemma summable_fin_prod {r : ℕ} (f : Fin r → ℤ → ℝ)
    (hf : ∀ i, Summable (f i)) (hn : ∀ i a, 0 ≤ f i a) :
    Summable (fun a : Fin r → ℤ => ∏ i, f i (a i)) := by
  induction r with
  | zero => exact (hasSum_fintype _).summable
  | succ r ih =>
    have hi := ih (fun i => f i.succ) (fun i => hf i.succ) (fun i => hn i.succ)
    have h := (hf 0).mul_of_nonneg hi (hn 0) (fun a => Finset.prod_nonneg (fun i _ => hn i.succ _))
    exact (Fin.insertNthEquiv (fun _ : Fin (r + 1) => ℤ) 0).summable_iff.mp
      (by simpa [Function.comp_def, Fin.prod_univ_succ, Fin.insertNth_zero] using h)

private lemma summable_scalar_gaussian (t : ℝ) (ht : 0 < t) :
    Summable (fun a : ℤ => Real.exp (-t * (a : ℝ)^2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0
    (div_pos ht Real.pi_pos) 0
  convert h using 1
  ext a
  congr 1
  simp
  field_simp

/-- A positive real matrix controls the squared coordinate norm; the empty
coordinate space is included without using a positive inverse trace. -/
theorem exists_quadratic_lower_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : Fin r → ℝ, t * (∑ i, x i ^ 2) ≤ quadratic A x := by
  by_cases hr : r = 0
  · subst r
    exact ⟨1, zero_lt_one, fun x => by simp [quadratic, dotProduct]⟩
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
  have ht : 0 < A⁻¹.trace := hA.inv.trace_pos
  refine ⟨A⁻¹.trace⁻¹, inv_pos.mpr ht, fun x => ?_⟩
  have hm : A⁻¹ *ᵥ (A *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  have hs (i : Fin r) : x i ^ 2 ≤ A⁻¹ i i * quadratic A x := by
    have h := hA.inv.star_dotProduct_mulVec_mul_le (Pi.single i 1) (A *ᵥ x)
    simpa [hm, quadratic, pow_two, dotProduct_comm] using h
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  rw [← Finset.sum_mul] at h
  change (∑ i, x i ^ 2) ≤ A⁻¹.trace * quadratic A x at h
  calc
    A⁻¹.trace⁻¹ * (∑ i, x i ^ 2) ≤ A⁻¹.trace⁻¹ * (A⁻¹.trace * quadratic A x) :=
      mul_le_mul_of_nonneg_left h (inv_pos.mpr ht).le
    _ = quadratic A x := by field_simp

/-- The integer-vector Gaussian is absolutely summable in every finite rank. -/
theorem summable_norm_gaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) :
    Summable (fun a : Fin r → ℤ =>
      ‖Complex.exp (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖) := by
  obtain ⟨t, ht, hq⟩ := exists_quadratic_lower_bound A hA
  have h := summable_fin_prod (fun _ : Fin r =>
    fun a : ℤ => Real.exp (-(Real.pi * b.re * t) * (a : ℝ)^2))
    (fun _ => summable_scalar_gaussian _ (by positivity)) (fun _ _ => (Real.exp_pos _).le)
  refine h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
  rw [← Real.exp_sum, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul]
  apply Real.exp_le_exp.mpr
  simp only [← Finset.mul_sum]
  nlinarith [hq (fun i => (a i : ℝ)), mul_pos Real.pi_pos hb]

#print axioms exists_quadratic_lower_bound
#print axioms summable_norm_gaussian

/-- The Gaussian as a continuous function on its real coordinate space. -/
def gaussianMap {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ) :
    C(Fin r → ℝ, ℂ) where
  toFun x := Complex.exp (-Real.pi * b * (quadratic A x : ℂ))
  continuous_toFun := by unfold quadratic dotProduct Matrix.mulVec; fun_prop

/-- Integer translates have summable compact sup norms, so their periodization
converges locally uniformly in the original real coordinates. -/
theorem locally_summable_norm_gaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re) (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun a : Fin r → ℤ =>
      ‖((gaussianMap A b).comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  obtain ⟨t, ht, hq⟩ := exists_quadratic_lower_bound A hA
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let s := Real.pi * b.re * t
  have hs : 0 < s := by dsimp [s]; positivity
  let u := fun a : Fin r → ℤ =>
    Real.exp (s * (r : ℝ) * R ^ 2) * ∏ i, Real.exp (-(s / 2) * (a i : ℝ)^2)
  have hu : Summable u := (summable_fin_prod
    (fun _ : Fin r => fun a : ℤ => Real.exp (-(s / 2) * (a : ℝ)^2))
    (fun _ => summable_scalar_gaussian _ (by positivity))
    (fun _ _ => (Real.exp_pos _).le)).mul_left _
  refine hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (by dsimp [u]; positivity)).mpr
  intro x
  have hx : ‖(x : Fin r → ℝ)‖ ≤ R := by simpa using hR x.property
  have hxx : (∑ i, (x : Fin r → ℝ) i ^ 2) ≤ (r : ℝ) * R ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin r, R ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |(x : Fin r → ℝ) i| ≤ R := (norm_le_pi_norm _ i).trans hx
        have hr0 : 0 ≤ R := (norm_nonneg _).trans hx
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).mpr hi
      _ = _ := by simp
  have hss : (∑ i, ((x : Fin r → ℝ) i + (a i : ℝ)) ^ 2) ≥
      (∑ i, (a i : ℝ) ^ 2) / 2 - ∑ i, (x : Fin r → ℝ) i ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
      show (a i : ℝ)^2 / 2 - (x : Fin r → ℝ) i ^ 2 ≤
        ((x : Fin r → ℝ) i + (a i : ℝ)) ^ 2 by
        nlinarith [sq_nonneg ((a i : ℝ) + 2 * (x : Fin r → ℝ) i)])
    simpa only [Finset.sum_sub_distrib, Finset.sum_div] using h
  change ‖Complex.exp (-Real.pi * b *
    (quadratic A (fun i => (x : Fin r → ℝ) i + (a i : ℝ)) : ℂ))‖ ≤ u a
  rw [Complex.norm_exp]
  dsimp [u]
  rw [← Real.exp_sum, ← Real.exp_add]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, neg_zero]
  apply Real.exp_le_exp.mpr
  rw [← Finset.mul_sum]
  have hquad := hq (fun i => (x : Fin r → ℝ) i + (a i : ℝ))
  have h1 := mul_le_mul_of_nonneg_left hquad (mul_pos Real.pi_pos hb).le
  have h2 := mul_le_mul_of_nonneg_left hss hs.le
  have h3 := mul_le_mul_of_nonneg_left hxx hs.le
  dsimp [s] at *
  nlinarith

#print axioms locally_summable_norm_gaussian

/-- Poisson summation for every real positive definite coordinate matrix and
every complex Gaussian parameter in the right half-plane. -/
theorem poisson_gaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) :
    Summable (fun a : Fin r → ℤ => ‖Complex.exp
      (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖) ∧
    Summable (fun k : Fin r → ℤ => ‖Complex.exp
      (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) ∧
    (∑' a : Fin r → ℤ, Complex.exp
      (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        ∑' k : Fin r → ℤ, Complex.exp
          (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  refine ⟨summable_norm_gaussian A hA b hb, ?_, ?_⟩
  · simpa [div_eq_mul_inv, neg_mul] using summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi
  ·
    have hf : Integrable (gaussianMap A b) := by
      convert integrable_gaussian_linear A hA ((Real.pi : ℂ) * b)
        (by simpa using mul_pos Real.pi_pos hb) 0 0 using 1
      funext x
      simp [gaussianMap, neg_mul]
    have hFT (k : Fin r → ℤ) :
        (∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
          (∑ i, (k i : ℝ) * x i : ℝ)) * gaussianMap A b x) =
        (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) := by
      simpa [gaussianMap, dotProduct] using
        integral_fourier_gaussian A hA b hb (fun i => (k i : ℝ))
    have hs : Summable (fun k : Fin r → ℤ => Complex.exp
        (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))) := by
      simpa [div_eq_mul_inv, neg_mul] using (summable_norm_gaussian A⁻¹ hA.inv b⁻¹ hbi).of_norm
    have hsf := hs.mul_left ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2))
    have hp := CoordinatePoisson.tsum_eq_tsum_integral hf
      (locally_summable_norm_gaussian A hA b hb) (hsf.congr (fun k => (hFT k).symm))
    calc
      _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
          (∑ i, (k i : ℝ) * x i : ℝ)) * gaussianMap A b x := hp
      _ = ∑' k : Fin r → ℤ, (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ)) :=
        tsum_congr hFT
      _ = _ := tsum_mul_left

#print axioms poisson_gaussian

example (b : ℂ) (hb : 0 < b.re) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
    A.det = 3 ∧ A.PosDef ∧
      Summable (fun a : Fin 2 → ℤ =>
        ‖Complex.exp (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖) := by
  dsimp
  have hA : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
    · intro x hx
      have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (by ext i; fin_cases i <;> simp [h])
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rcases hn with h | h
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 1), sq_nonneg (x 0 + x 1)]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 0 + x 1)]
  refine ⟨by norm_num [Matrix.det_fin_two], hA, summable_norm_gaussian _ hA b hb⟩

end
end D5.S3.Fourier.MatrixGaussian
