/- GID: D5/S3/Observer/Linear/ReflectingHeatInterpolation
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatStripBound]
   utility: none
   digest: The reflecting heat nodal factors leave square-integrable decay after cancellation. -/

import D5.S3.Observer.Linear.ReflectingHeatStripBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Lagrange

/-! # Chebyshev interpolation at the reflecting heat rates

The nodal formulas follow the reflecting-path critical crossover proof, equations
(11)–(12). The real-axis estimate for its moment interpolant follows (35)–(38).
-/

open Polynomial Polynomial.Chebyshev MeasureTheory
open scoped BigOperators

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open ReflectingHeatStripBound

private theorem mode_lt_cells {n : ℕ} (j : Mode n) : j.val + 1 < n := by
  have := j.isLt
  omega

/-- The monic nodal polynomial on the positive reflecting modes. -/
def nodalPolynomial (n : ℕ) : ℝ[X] := Lagrange.nodal Finset.univ (rate n)

/-- The complex nodal polynomial with mode `j` omitted. -/
def omittedPolynomial (n : ℕ) (j : Mode n) : ℂ[X] :=
  Lagrange.nodal (Finset.univ.erase j) (fun k => (rate n k : ℂ))

/-- The real normalization at the omitted mode. -/
def nodalDerivative (n : ℕ) (j : Mode n) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, (rate n j - rate n k)

/-- The monic nodal polynomial is the affine shift of the second-kind Chebyshev polynomial. -/
theorem nodalPolynomial_eq_chebyshev (n : ℕ) :
    nodalPolynomial n =
      (U ℝ (↑(n - 1 : ℕ))).comp (C (1 / 2) * (X - C 2)) := by
  let p : ℝ[X] := (U ℝ (↑(n - 1 : ℕ))).comp (C (1 / 2) * (X - C 2))
  let nodes := Finset.univ.image (rate n)
  have hinj : Function.Injective (rate n) := by
    intro j k h
    exact rate_injective (by have := mode_lt_cells j; omega) h
  have ha : (C (1 / 2 : ℝ) * (X - C 2)).natDegree = 1 := by
    rw [natDegree_C_mul (by norm_num), natDegree_X_sub_C]
  have hp : p.Monic := by
    unfold p Monic
    rw [leadingCoeff_comp, leadingCoeff_U_natCast, Polynomial.leadingCoeff_mul, leadingCoeff_C,
      (monic_X_sub_C (2 : ℝ)).leadingCoeff, mul_one, natDegree_U_natCast, ← mul_pow]
    · norm_num
    · rw [ha]; decide
  have hd : p.natDegree = n - 1 := by
    rw [natDegree_comp, ha, natDegree_U_natCast, mul_one]
  have hc : nodes.card = n - 1 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hr : p.roots = nodes.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero _ (hd.trans hc.symm).le hp.ne_zero
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    have hn : (n - 1).succ = n := by have := mode_lt_cells j; omega
    have hm : Real.cos (angle n j) ∈ (U ℝ (↑(n - 1 : ℕ))).roots := by
      rw [roots_U_real]
      change Real.cos (angle n j) ∈ (Finset.range (n - 1)).image _
      refine Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
      simp only [angle, ← Nat.cast_succ, hn]
    have hz := (mem_roots (U_ne_zero ℝ (↑(n - 1 : ℕ)) (by omega))).mp hm
    simp only [p, eval_comp, eval_mul, eval_C, eval_sub, eval_X]
    rw [show (1 / 2 : ℝ) * (rate n j - 2) = -Real.cos (angle n j) by
      change (1 / 2 : ℝ) * (2 - 2 * Real.cos (angle n j) - 2) = _
      ring, U_eval_neg, hz, mul_zero]
  change nodalPolynomial n = p
  have hcard : p.roots.card = p.natDegree := by
    rw [hr]
    exact hc.trans hd.symm
  rw [(splits_iff_card_roots.mpr hcard).eq_prod_roots_of_monic hp, hr]
  change nodalPolynomial n = ∏ x ∈ nodes, (X - C x)
  unfold nodalPolynomial Lagrange.nodal nodes
  rw [Finset.prod_image (fun a _ b _ h => hinj h)]

/-- The exact magnitude of the product of gaps, for every positive reflecting mode. -/
theorem abs_nodalDerivative (n : ℕ) (j : Mode n) :
    |nodalDerivative n j| = (n : ℝ) /
      (2 * Real.sin (((j.val + 1 : ℕ) : ℝ) * Real.pi / n) ^ 2) := by
  let t := angle n j
  let w : ℝ → ℝ := fun s => 2 - 2 * Real.cos s
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (angle_mem n j).1 (angle_mem n j).2
  have hw : HasDerivAt w (2 * Real.sin t) t := by
    simpa [w] using (hasDerivAt_const t (2 : ℝ)).fun_sub ((Real.hasDerivAt_cos t).const_mul 2)
  have hval : w t = rate n j := rfl
  have hderiv : (nodalPolynomial n).derivative.eval (rate n j) = nodalDerivative n j := by
    rw [nodalPolynomial, Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j),
      Lagrange.eval_nodal, nodalDerivative]
  have hf : HasDerivAt (fun s => (nodalPolynomial n).eval (w s))
      (2 * Real.sin t * nodalDerivative n j) t := by
    simpa only [Function.comp_def, hval, hderiv, mul_comm] using
      ((nodalPolynomial n).hasDerivAt (w t)).comp t hw
  have hzero : (nodalPolynomial n).eval (w t) = 0 := by
    rw [hval, nodalPolynomial]
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
  have hn : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast (show n - 1 + 1 = n by have := mode_lt_cells j; omega)
  have htrig : (fun s => (nodalPolynomial n).eval (w s) * Real.sin s) =
      fun s => ((n - 1 : ℕ) : ℤ).negOnePow * Real.sin ((n : ℝ) * s) := by
    funext s
    rw [nodalPolynomial_eq_chebyshev, eval_comp]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    rw [show (1 / 2 : ℝ) * (w s - 2) = -Real.cos s by dsimp [w]; ring,
      U_eval_neg, mul_assoc, U_real_cos, Int.cast_natCast, hn]
  have hd₁ := hf.mul (Real.hasDerivAt_sin t)
  have hd₂ := ((Real.hasDerivAt_sin ((n : ℝ) * t)).comp t
    ((hasDerivAt_id t).const_mul (n : ℝ))).const_mul
      (((n - 1 : ℕ) : ℤ).negOnePow : ℝ)
  change HasDerivAt (fun s => (nodalPolynomial n).eval (w s) * Real.sin s) _ _ at hd₁
  rw [htrig] at hd₁
  have he := hd₁.unique hd₂
  have htN : (n : ℝ) * t = ((j.val + 1 : ℕ) : ℝ) * Real.pi := angle_mul_cells n j
  rw [hzero, zero_mul, add_zero, htN, Real.cos_nat_mul_pi] at he
  have habs := congrArg abs he
  simp only [abs_mul, abs_of_nonneg hs.le, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_unit_intCast,
    abs_neg, abs_one, abs_pow, one_pow, one_mul, mul_one] at habs
  change |nodalDerivative n j| = (n : ℝ) / (2 * Real.sin t ^ 2)
  apply (eq_div_iff (by positivity)).2
  linear_combination habs

private theorem theta_endpoint_bounds {n : ℕ} (j : Mode n) :
    Real.pi / n ≤ angle n j ∧ Real.pi / n ≤ Real.pi - angle n j := by
  have hn : 0 < (n : ℝ) := by
    have := mode_lt_cells j
    exact_mod_cast (show 0 < n by omega)
  have hj : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val + 1)
  have hk : ((j.val + 1 : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (mode_lt_cells j)
  constructor <;> apply (div_le_iff₀ hn).2
  · rw [mul_comm, angle_mul_cells]
    simpa using mul_le_mul_of_nonneg_right hj Real.pi_pos.le
  · rw [sub_mul, mul_comm (angle n j), angle_mul_cells]
    nlinarith [mul_le_mul_of_nonneg_right hk Real.pi_pos.le]

private theorem rate_endpoint_bounds {n : ℕ} (j : Mode n) :
    4 / (n : ℝ) ^ 2 ≤ rate n j ∧ 4 / (n : ℝ) ^ 2 ≤ 4 - rate n j := by
  have hn : 0 < (n : ℝ) := by
    have := mode_lt_cells j
    exact_mod_cast (show 0 < n by omega)
  have hb (t : ℝ) (ht : Real.pi / n ≤ t) (ht' : t ≤ Real.pi) :
      4 / (n : ℝ) ^ 2 ≤ 2 - 2 * Real.cos t := by
    have hsin := Real.mul_le_sin (x := t / 2) (by linarith [show 0 ≤ Real.pi / n by positivity])
      (by linarith)
    have hmul := mul_le_mul_of_nonneg_left ht (show 0 ≤ Real.pi⁻¹ by positivity)
    have hnorm : Real.pi⁻¹ * (Real.pi / (n : ℝ)) = 1 / n := by
      field_simp [Real.pi_ne_zero]
    rw [hnorm] at hmul
    have hs : 1 / (n : ℝ) ≤ Real.sin (t / 2) := by
      calc
        _ ≤ Real.pi⁻¹ * t := hmul
        _ = _ := by ring
        _ ≤ _ := hsin
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (n : ℝ)) hs 2
    have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      conv_lhs => rw [show t = 2 * (t / 2) by ring]
      rw [Real.cos_two_mul_eq_one_sub]
    rw [div_pow, one_pow] at hsq
    rw [hcos, show (4 : ℝ) / n ^ 2 = 4 * (1 / n ^ 2) by ring]
    linarith
  have h := theta_endpoint_bounds j
  have hmem := angle_mem n j
  have hleft := hb (angle n j) h.1 hmem.2.le
  have hright := hb (Real.pi - angle n j) h.2 (by linarith [hmem.1])
  rw [Real.cos_pi_sub] at hright
  change _ ≤ 2 - 2 * Real.cos (angle n j) ∧ _ ≤ 4 - (2 - 2 * Real.cos (angle n j))
  exact ⟨hleft, by linarith⟩

/-- Uniform polynomial bounds on the gaps and on the distances to both spectral endpoints. -/
theorem uniform_nodal_factors (n : ℕ) (j : Mode n) :
    (n : ℝ) / 2 ≤ |nodalDerivative n j| ∧
    |nodalDerivative n j| ≤ (n : ℝ) ^ 3 / 8 ∧
    4 / (n : ℝ) ^ 2 ≤ rate n j ∧ 4 / (n : ℝ) ^ 2 ≤ 4 - rate n j := by
  have hn : 0 < (n : ℝ) := by
    have := mode_lt_cells j
    exact_mod_cast (show 0 < n by omega)
  have hedge := theta_endpoint_bounds j
  have hmem := angle_mem n j
  have hsin : 2 / (n : ℝ) ≤ Real.sin (angle n j) := by
    have hlower (t : ℝ) (ht : Real.pi / n ≤ t) (ht' : t ≤ Real.pi / 2) :
        2 / (n : ℝ) ≤ Real.sin t := by
      calc
        _ = (2 / Real.pi) * (Real.pi / n) := by field_simp [Real.pi_ne_zero]
        _ ≤ (2 / Real.pi) * t := mul_le_mul_of_nonneg_left ht (by positivity)
        _ ≤ _ := Real.mul_le_sin (by linarith [show 0 ≤ Real.pi / n by positivity]) ht'
    by_cases h : angle n j ≤ Real.pi / 2
    · exact hlower _ hedge.1 h
    · rw [← Real.sin_pi_sub]
      exact hlower _ hedge.2 (by linarith)
  have hsin_pos : 0 < Real.sin (angle n j) := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / (n : ℝ)) hsin 2
  have hsqu := pow_le_pow_left₀ hsin_pos.le (Real.sin_le_one (angle n j)) 2
  rw [abs_nodalDerivative]
  change _ ≤ (n : ℝ) / (2 * Real.sin (angle n j) ^ 2) ∧
    (n : ℝ) / (2 * Real.sin (angle n j) ^ 2) ≤ _ ∧ _
  refine ⟨div_le_div_of_nonneg_left hn.le (by positivity) (by linarith), ?_,
    rate_endpoint_bounds j⟩
  calc
    _ ≤ (n : ℝ) / (2 * (2 / (n : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_left hn.le (by positivity) (by gcongr)
    _ = _ := by field_simp; ring

/-- The physical endpoint weight converts the inverse nodal normalization
into the factor in the strip estimates, with a uniform lower bound at both edges. -/
theorem endpoint_normalization (n : ℕ) (j : Mode n) :
    (n : ℝ) / (weight n j * |nodalDerivative n j|) = rate n j * weight n j ∧
    4 / (n : ℝ) ^ 2 ≤ rate n j * weight n j := by
  have hn : 0 < (n : ℝ) := by
    have := mode_lt_cells j
    exact_mod_cast (show 0 < n by omega)
  have hn₂ : (2 : ℝ) ≤ n := by
    have := mode_lt_cells j
    exact_mod_cast (show 2 ≤ n by omega)
  have hq := rate_endpoint_bounds j
  have hb : 0 < weight n j := weight_pos n j
  have hb_sq : weight n j ^ 2 = 2 - rate n j / 2 :=
    Real.sq_sqrt (by linarith [hq.2, show 0 ≤ (4 : ℝ) / n ^ 2 by positivity])
  have hm := angle_mem n j
  have hs := Real.sin_pos_of_pos_of_lt_pi hm.1 hm.2
  constructor
  · rw [abs_nodalDerivative]
    change (n : ℝ) / (weight n j * ((n : ℝ) / (2 * Real.sin (angle n j) ^ 2))) = _
    have htrig : rate n j * weight n j ^ 2 = 2 * Real.sin (angle n j) ^ 2 := by
      rw [hb_sq]
      change (2 - 2 * Real.cos (angle n j)) * (2 - (2 - 2 * Real.cos (angle n j)) / 2) = _
      nlinarith [Real.sin_sq_add_cos_sq (angle n j)]
    field_simp [hb.ne', hn.ne', hs.ne']
    linear_combination -htrig
  · by_cases hq₂ : rate n j ≤ 2
    · have hw : 1 ≤ weight n j := by
        apply (sq_le_sq₀ zero_le_one hb.le).1
        rw [hb_sq]
        linarith
      exact hq.1.trans (le_mul_of_one_le_right (rate_pos n j).le hw)
    · have hw : 1 / (n : ℝ) ≤ weight n j := by
        apply (sq_le_sq₀ (by positivity) hb.le).1
        rw [hb_sq, div_pow, one_pow]
        linarith [show (0 : ℝ) ≤ 1 / n ^ 2 by positivity, hq.2,
          show (4 : ℝ) / n ^ 2 = 4 * (1 / n ^ 2) by ring]
      calc
        _ ≤ 2 * (1 / (n : ℝ)) := by
          apply (div_le_iff₀ (by positivity)).2
          field_simp
          nlinarith
        _ ≤ rate n j * weight n j :=
          mul_le_mul (le_of_not_ge hq₂) hw (by positivity) (rate_pos n j).le

private theorem complex_nodal_eval (n : ℕ) (w : ℂ) :
    (Lagrange.nodal Finset.univ (fun k => (rate n k : ℂ))).eval w =
      (U ℂ (↑(n - 1 : ℕ))).eval ((w - 2) / 2) := by
  have h := congrArg (Polynomial.map Complex.ofRealHom) (nodalPolynomial_eq_chebyshev n)
  have he := congrArg (Polynomial.eval w) h
  simpa only [nodalPolynomial, Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_comp, Polynomial.map_mul, map_U, eval_prod, eval_comp,
    eval_mul, eval_sub, eval_X, eval_C, Complex.ofRealHom_eq_coe, Complex.ofReal_ofNat,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_inv, div_eq_mul_inv, one_mul,
    mul_comm] using he

private theorem chebyshev_geometric (ζ : ℂ) (hζ : ζ ≠ 0) (m : ℕ) :
    (U ℂ (m : ℤ)).eval ((ζ + ζ⁻¹) / 2) =
      ∑ k ∈ Finset.range (m + 1), ζ ^ k * (ζ⁻¹) ^ (m - k) := by
  let u (k : ℕ) := (U ℂ (k : ℤ)).eval ((ζ + ζ⁻¹) / 2)
  have hstep (k : ℕ) : u (k + 1) = ζ⁻¹ * u k + ζ ^ (k + 1) := by
    induction k with
    | zero =>
      simp [u, U_one]
      ring
    | succ k ih =>
      have hrec : u (k + 2) = (ζ + ζ⁻¹) * u (k + 1) - u k := by
        dsimp [u]
        rw [U_add_two]
        simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
        have h : (2 : ℂ) * ((ζ + ζ⁻¹) / 2) = ζ + ζ⁻¹ := by ring
        rw [h]
      rw [show k.succ + 1 = k + 2 by rfl, hrec, pow_succ]
      calc
        _ = ζ⁻¹ * u (k + 1) + ζ * u (k + 1) - u k := by ring
        _ = ζ⁻¹ * u (k + 1) + ζ * (ζ⁻¹ * u k + ζ ^ (k + 1)) - u k := by
          rw [← ih]
        _ = _ := by rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hζ, one_mul]; ring
  change u m = _
  induction m with
  | zero => simp [u]
  | succ m ih =>
    rw [hstep m, ih, add_comm]
    exact ((Commute.all ζ ζ⁻¹).geom_sum₂_succ_eq (n := m + 1)).symm

/-- The full imaginary-axis growth bound, with the omitted factor retained in the denominator. -/
theorem norm_omittedPolynomial_eval (n : ℕ) (j : Mode n) (ω : ℝ) (ζ : ℂ)
    (hζ : ζ ≠ 0) (hroot : ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2) (hunit : 1 ≤ ‖ζ‖) :
    ‖(omittedPolynomial n j).eval ((ω : ℂ) * Complex.I)‖ ≤
      (n : ℝ) * ‖ζ‖ ^ (n - 1) / Real.sqrt (rate n j ^ 2 + ω ^ 2) := by
  let w := (ω : ℂ) * Complex.I
  have hfactor : (w - (rate n j : ℂ)) * (omittedPolynomial n j).eval w =
      (Lagrange.nodal Finset.univ (fun k => (rate n k : ℂ))).eval w := by
    have h := Lagrange.nodal_eq_mul_nodal_erase
      (v := fun k => (rate n k : ℂ)) (Finset.mem_univ j)
    simpa only [omittedPolynomial, eval_mul, eval_sub, eval_X, eval_C] using
      (congrArg (Polynomial.eval w) h).symm
  have hdist : ‖w - (rate n j : ℂ)‖ = Real.sqrt (rate n j ^ 2 + ω ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [w, Complex.mul_re, Complex.mul_im, ← sq]
  have hpos : 0 < Real.sqrt (rate n j ^ 2 + ω ^ 2) := by positivity [rate_pos n j]
  have hn : n - 1 + 1 = n := by have := mode_lt_cells j; omega
  apply (le_div_iff₀ hpos).2
  rw [← hdist, mul_comm, ← norm_mul, hfactor, complex_nodal_eval, ← hroot, chebyshev_geometric ζ hζ]
  calc
    _ ≤ ∑ k ∈ Finset.range (n - 1 + 1), ‖ζ ^ k * (ζ⁻¹) ^ (n - 1 - k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n - 1 + 1), ‖ζ‖ ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [norm_mul, norm_pow, norm_inv]
      have hinv : ‖ζ‖⁻¹ ^ (n - 1 - k) ≤ 1 :=
        pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hunit)
      calc
        _ ≤ ‖ζ‖ ^ k * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ ≤ _ := by rw [mul_one]; exact pow_le_pow_right₀ hunit (by omega)
    _ = _ := by simp [Finset.sum_const, hn]

/-- The Fourier-side moment interpolant formed with the omitted nodal factor. -/
def momentInterpolant (n : ℕ) (j : Mode n) (M : ℂ → ℂ) (z : ℂ) : ℂ :=
  (omittedPolynomial n j).eval (z * Complex.I) * M z

private theorem abs_le_joukowski_radius (ω : ℝ) (ζ : ℂ)
    (hroot : ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2) (hunit : 1 ≤ ‖ζ‖) :
    |ω| ≤ ‖ζ‖ := by
  have him : ζ.im + -ζ.im / Complex.normSq ζ = ω := by
    simpa [Complex.inv_im, Complex.mul_im] using congrArg Complex.im hroot
  have hr : 1 ≤ Complex.normSq ζ := Complex.one_le_normSq_iff.mpr hunit
  have hω : ω = ζ.im * (1 - (Complex.normSq ζ)⁻¹) := by rw [← him]; ring
  have hinv := inv_le_one_of_one_le₀ hr
  rw [hω, abs_mul, abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hfactor : 1 - (Complex.normSq ζ)⁻¹ ≤ 1 :=
    sub_le_self _ (inv_nonneg.mpr (zero_le_one.trans hr))
  exact (mul_le_of_le_one_right (abs_nonneg _) hfactor).trans (Complex.abs_im_le_norm ζ)

private theorem momentInterpolant_bound (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    {A B : ℝ} (ω : ℝ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hroot : ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2) (hunit : 1 ≤ ‖ζ‖)
    (hM : ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n) :
    ‖momentInterpolant n j M (ω : ℂ)‖ ≤
      (n : ℝ) * A * (1 + B * |ω|) / (‖ζ‖ * Real.sqrt (rate n j ^ 2 + ω ^ 2)) := by
  have hn : n - 1 + 1 = n := by have := mode_lt_cells j; omega
  have hr : 0 < ‖ζ‖ := zero_lt_one.trans_le hunit
  have hs : 0 < Real.sqrt (rate n j ^ 2 + ω ^ 2) := by positivity [rate_pos n j]
  simp only [momentInterpolant, norm_mul]
  calc
    _ ≤ ((n : ℝ) * ‖ζ‖ ^ (n - 1) / Real.sqrt (rate n j ^ 2 + ω ^ 2)) *
        (A * (1 + B * |ω|) / ‖ζ‖ ^ n) :=
      mul_le_mul (norm_omittedPolynomial_eval n j ω ζ hζ hroot hunit) hM
        (norm_nonneg _) (by positivity)
    _ = _ := by
      have hpow : ‖ζ‖ ^ n = ‖ζ‖ ^ (n - 1) * ‖ζ‖ :=
        hn ▸ pow_succ ‖ζ‖ (n - 1)
      rw [hpow]
      field_simp

private theorem cauchy_kernel {q : ℝ} (hq : 0 < q) :
    Integrable (fun ω : ℝ => (q ^ 2 + ω ^ 2)⁻¹) ∧
      (∫ ω : ℝ, (q ^ 2 + ω ^ 2)⁻¹) = Real.pi / q := by
  have he (ω : ℝ) : (q ^ 2)⁻¹ * (1 + (q⁻¹ * ω) ^ 2)⁻¹ = (q ^ 2 + ω ^ 2)⁻¹ := by
    have hh : 0 < 1 + (q⁻¹ * ω) ^ 2 := by positivity
    have hk : 0 < q ^ 2 + ω ^ 2 := by positivity
    field_simp
  simp_rw [← he]
  refine ⟨(integrable_inv_one_add_mul_sq (b := q⁻¹) (inv_ne_zero hq.ne')).const_mul _, ?_⟩
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr hq)]
  field_simp

/-- The real-axis multiplier envelope gives the source's squared-norm bound.
One inverse Joukowski radius remains after cancellation and controls the term
with the linear discretization loss. -/
theorem momentInterpolant_L2_bound (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (hM_meas : Measurable (fun ω : ℝ => M (ω : ℂ)))
    {A B : ℝ}
    (hM : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n) :
    MemLp (fun ω : ℝ => momentInterpolant n j M (ω : ℂ)) 2 volume ∧
    (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2) ≤
      2 * ((n : ℝ) * A) ^ 2 * Real.pi * ((n : ℝ) ^ 2 / 4 + 2 * B ^ 2) := by
  let ψ (ω : ℝ) := momentInterpolant n j M (ω : ℂ)
  let q := rate n j
  let c := 2 * ((n : ℝ) * A) ^ 2
  let g (ω : ℝ) := c * ((q ^ 2 + ω ^ 2)⁻¹ + 2 * B ^ 2 * (1 + ω ^ 2)⁻¹)
  have hmeas : Measurable ψ :=
    ((omittedPolynomial n j).continuous.comp
      (Complex.continuous_ofReal.mul continuous_const)).measurable.mul hM_meas
  have hq : 0 < q := rate_pos n j
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hg : Integrable g :=
    ((cauchy_kernel hq).1.add (integrable_inv_one_add_sq.const_mul _)).const_mul _
  have hdom (ω : ℝ) : ‖ψ ω‖ ^ 2 ≤ g ω := by
    obtain ⟨ζ, hζ, hroot, hunit, hbound⟩ := hM ω
    have hω := abs_le_joukowski_radius ω ζ hroot hunit
    have hr : 0 < ‖ζ‖ := zero_lt_one.trans_le hunit
    have hk : 0 < q ^ 2 + ω ^ 2 := by positivity
    have hs : 0 < Real.sqrt (q ^ 2 + ω ^ 2) := Real.sqrt_pos.2 hk
    have hr_sq : 1 ≤ ‖ζ‖ ^ 2 := by
      simpa using pow_le_pow_left₀ zero_le_one hunit 2
    have hω_sq : ω ^ 2 ≤ ‖ζ‖ ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg ω) hω 2
    have hbound_sq := pow_le_pow_left₀ (norm_nonneg _)
      (momentInterpolant_bound n j M ω ζ hζ hroot hunit hbound) 2
    have hsum : (1 + B * |ω|) ^ 2 ≤ 2 * (1 + B ^ 2 * ω ^ 2) := by
      have hsq : |ω| ^ 2 = ω ^ 2 := sq_abs ω
      nlinarith [sq_nonneg (1 - B * |ω|), congrArg (fun x => B ^ 2 * x) hsq]
    have hfirst : (‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2))⁻¹ ≤ (q ^ 2 + ω ^ 2)⁻¹ := by
      apply inv_anti₀ hk
      simpa using mul_le_mul_of_nonneg_right hr_sq hk.le
    have hsecond : ω ^ 2 / (‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2)) ≤ 2 * (1 + ω ^ 2)⁻¹ := by
      have he : ω ^ 2 ≤ q ^ 2 + ω ^ 2 := by linarith [sq_nonneg q]
      have ht : 1 + ω ^ 2 ≤ 2 * ‖ζ‖ ^ 2 := by linarith
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      calc
        _ ≤ (q ^ 2 + ω ^ 2) * (2 * ‖ζ‖ ^ 2) := mul_le_mul he ht (by positivity) hk.le
        _ = _ := by ring
    change ‖ψ ω‖ ^ 2 ≤ _
    calc
      _ ≤ (((n : ℝ) * A * (1 + B * |ω|)) /
          (‖ζ‖ * Real.sqrt (q ^ 2 + ω ^ 2))) ^ 2 := hbound_sq
      _ = ((n : ℝ) * A) ^ 2 * (1 + B * |ω|) ^ 2 /
          (‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2)) := by
        simp only [div_pow, mul_pow, Real.sq_sqrt hk.le]
      _ ≤ c * (1 + B ^ 2 * ω ^ 2) / (‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [c]
        calc
          _ ≤ ((n : ℝ) * A) ^ 2 * (2 * (1 + B ^ 2 * ω ^ 2)) :=
            mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ = _ := by ring
      _ = c * ((‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2))⁻¹ +
          B ^ 2 * (ω ^ 2 / (‖ζ‖ ^ 2 * (q ^ 2 + ω ^ 2)))) := by
        simp only [div_eq_mul_inv]; ring
      _ ≤ g ω := mul_le_mul_of_nonneg_left
        (add_le_add hfirst (by simpa [mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_left hsecond (sq_nonneg B))) hc
  have hsq : Integrable (fun ω : ℝ => ‖ψ ω‖ ^ 2) :=
    hg.mono' (hmeas.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hdom ω)
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 hsq, ?_⟩
  have hn : 0 < (n : ℝ) := by
    have := mode_lt_cells j
    exact_mod_cast (show 0 < n by omega)
  have hq_inv : q⁻¹ ≤ (n : ℝ) ^ 2 / 4 := by
    calc
      _ ≤ (4 / (n : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) (uniform_nodal_factors n j).2.2.1
      _ = _ := inv_div _ _
  calc
    (∫ ω : ℝ, ‖ψ ω‖ ^ 2) ≤ ∫ ω : ℝ, g ω := integral_mono hsq hg hdom
    _ = c * (Real.pi / q + 2 * B ^ 2 * Real.pi) := by
      simp only [g, integral_const_mul]
      rw [integral_add (cauchy_kernel hq).1 (integrable_inv_one_add_sq.const_mul _),
        (cauchy_kernel hq).2, integral_const_mul, integral_univ_inv_one_add_sq]
    _ = c * Real.pi * (q⁻¹ + 2 * B ^ 2) := by rw [div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left hq_inv _) (mul_nonneg hc Real.pi_pos.le)

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
