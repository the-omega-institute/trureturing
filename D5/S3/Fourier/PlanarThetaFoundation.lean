/- GID: D5/S3/Fourier/PlanarThetaFoundation
   generality: G
   mirror-B: D5/B/S3/Fourier/PlanarThetaFoundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian convergence and coordinate symmetries of unit-area planar theta series. -/

import D5.S3.Fourier.MatrixGaussianTheta
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OmegaBuild.Commands

/-! # Unit-area planar theta series in real coordinates -/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- The unit-determinant binary form in shear and height coordinates. -/
def Q (x y : ℝ) (v : ℤ × ℤ) : ℝ :=
  ((v.1 : ℝ) + v.2 * x) ^ 2 / y + y * (v.2 : ℝ) ^ 2

/-- The theta series, indexed by the actual integer coordinate pairs. -/
def F (t x y : ℝ) : ℝ := ∑' v : ℤ × ℤ, Real.exp (-Real.pi * t * Q x y v)

private def gram (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / y, x / y; x / y, x ^ 2 / y + y]

private lemma quadratic_gram (x y : ℝ) (v : Fin 2 → ℝ) :
    MatrixGaussian.quadratic (gram x y) v = (v 0 + v 1 * x) ^ 2 / y + y * v 1 ^ 2 := by
  simp [MatrixGaussian.quadratic, gram, dotProduct, mulVec, Fin.sum_univ_two]
  ring

private lemma gram_posDef (x : ℝ) {y : ℝ} (hy : 0 < y) : (gram x y).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, Matrix.conjTranspose]
  · intro v hv
    change 0 < MatrixGaussian.quadratic (gram x y) v
    rw [quadratic_gram]
    by_cases h : v 1 = 0
    · have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        ext i
        fin_cases i <;> simp [h, h0]
      simpa [h] using div_pos (sq_pos_of_ne_zero h0) hy
    · exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hy.le)
        (mul_pos hy (sq_pos_of_ne_zero h))

private lemma gram_det (x : ℝ) {y : ℝ} (hy : y ≠ 0) : (gram x y).det = 1 := by
  simp [gram, Matrix.det_fin_two]
  field_simp
  <;> ring

/-- An explicit bound uniform in a compact shear-height rectangle. -/
theorem quadratic_control {M l u x y : ℝ} (hl : 0 < l)
    (hx : |x| ≤ M) (hly : l ≤ y) (hyu : y ≤ u) (v : ℤ × ℤ) :
    (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤
      max (2 * u) ((2 * M ^ 2 + 1) / l) * Q x y v := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have hy : 0 < y := hl.trans_le hly
  have hu : 0 < u := hy.trans_le hyu
  let C := max (2 * u) ((2 * M ^ 2 + 1) / l)
  have hC : 0 ≤ C := (show 0 ≤ 2 * u by positivity).trans (le_max_left _ _)
  have hC1 : 2 * y ≤ C := (by linarith : 2 * y ≤ 2 * u).trans (le_max_left _ _)
  have hC2 : 2 * M ^ 2 + 1 ≤ C * y := by
    have h := (div_le_iff₀ hl).mp (le_max_right (2 * u) ((2 * M ^ 2 + 1) / l))
    exact h.trans (mul_le_mul_of_nonneg_left hly hC)
  have hx2 : x ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hM).mpr hx
  have h1 := mul_le_mul_of_nonneg_right hC1
    (div_nonneg (sq_nonneg ((v.1 : ℝ) + v.2 * x)) hy.le)
  have h2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg (v.2 : ℝ))
  have he : 2 * y * (((v.1 : ℝ) + v.2 * x) ^ 2 / y) =
      2 * ((v.1 : ℝ) + v.2 * x) ^ 2 := by field_simp
  rw [he] at h1
  have h3 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg (v.2 : ℝ))
  dsimp [Q]
  change _ ≤ C * _
  nlinarith [sq_nonneg ((v.1 : ℝ) + 2 * v.2 * x)]

/-- Absolute convergence at every positive temperature and height. -/
theorem summable (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Summable (fun v : ℤ × ℤ => Real.exp (-Real.pi * t * Q x y v)) := by
  have hs := MatrixGaussian.summable_norm_gaussian (gram x y) (gram_posDef x hy)
    (t : ℂ) (by simpa using ht)
  have he (a : Fin 2 → ℤ) :
      ‖Complex.exp (-Real.pi * (t : ℂ) *
        (MatrixGaussian.quadratic (gram x y) (fun i => (a i : ℝ)) : ℂ))‖ =
      Real.exp (-Real.pi * t * Q x y (a 0, a 1)) := by
    have he : -Real.pi * (t : ℂ) *
        (MatrixGaussian.quadratic (gram x y) (fun i => (a i : ℝ)) : ℂ) =
        ((-Real.pi * t * MatrixGaussian.quadratic (gram x y)
          (fun i => (a i : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_exp, Complex.ofReal_re, quadratic_gram]
    rfl
  simp_rw [he] at hs
  exact (finTwoArrowEquiv ℤ).summable_iff.mp
    (by simpa [Function.comp_def] using hs)


private def size (v : ℤ × ℤ) : ℝ := (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2

private lemma scalar_weight (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Summable (fun n : ℤ => (n : ℝ) ^ (2 * k) * Real.exp (-a * (n : ℝ) ^ 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 (div_pos ha Real.pi_pos) (2 * k)
  refine h.congr fun n => ?_
  simp only [mul_zero, zero_mul, sub_zero]
  have he : -Real.pi * (a / Real.pi * (n : ℝ) ^ 2) = -a * (n : ℝ) ^ 2 := by
    field_simp
  rw [he]
  congr 1
  simp [pow_mul, sq_abs]

private lemma weight_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun v : ℤ × ℤ => size v * Real.exp (-a * size v)) := by
  have h0 := scalar_weight a ha 0
  have h2 := scalar_weight a ha 1
  simp only [Nat.mul_zero, pow_zero, one_mul] at h0
  norm_num only [Nat.mul_one] at h2
  have h20 := h2.mul_of_nonneg h0 (fun _ => by positivity) (fun _ => by positivity)
  have h02 := h0.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)
  convert h20.add h02 using 1
  ext v
  simp only [size, ← Real.exp_add]
  rw [show -a * ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) =
    -a * (v.1 : ℝ) ^ 2 + -a * (v.2 : ℝ) ^ 2 by ring, Real.exp_add]
  ring

private lemma square_weight_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun v : ℤ × ℤ => size v ^ 2 * Real.exp (-a * size v)) := by
  have h0 := scalar_weight a ha 0
  have h2 := scalar_weight a ha 1
  have h4 := scalar_weight a ha 2
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, pow_zero, one_mul] at h0 h2 h4
  have h40 := h4.mul_of_nonneg h0 (fun _ => by positivity) (fun _ => by positivity)
  have h04 := h0.mul_of_nonneg h4 (fun _ => by positivity) (fun _ => by positivity)
  have h22 := h2.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)
  convert (h40.add (h22.mul_left 2)).add h04 using 1
  ext v
  simp only [size]
  rw [show -a * ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) =
    -a * (v.1 : ℝ) ^ 2 + -a * (v.2 : ℝ) ^ 2 by ring, Real.exp_add]
  ring

private lemma compact_exponential_bound {M l u t x y : ℝ} (hM : 0 ≤ M)
    (hl : 0 < l) (ht : 0 < t) (hx : |x| ≤ M) (hly : l ≤ y) (hyu : y ≤ u)
    (v : ℤ × ℤ) :
    Real.exp (-Real.pi * t * Q x y v) ≤ Real.exp
      (-(Real.pi * t / max (2 * u) ((2 * M ^ 2 + 1) / l)) * size v) := by
  have hu : 0 < u := hl.trans_le (hly.trans hyu)
  have hC : 0 < max (2 * u) ((2 * M ^ 2 + 1) / l) :=
    (by positivity : 0 < 2 * u).trans_le (le_max_left _ _)
  apply Real.exp_le_exp.mpr
  have h := quadratic_control hl hx hly hyu v
  have hq : size v / max (2 * u) ((2 * M ^ 2 + 1) / l) ≤ Q x y v :=
    (div_le_iff₀ hC).mpr (by simpa [size, mul_comm] using h)
  have h := mul_le_mul_of_nonneg_left hq (mul_pos Real.pi_pos ht).le
  calc
    -Real.pi * t * Q x y v = -(Real.pi * t * Q x y v) := by ring
    _ ≤ -(Real.pi * t * (size v /
        max (2 * u) ((2 * M ^ 2 + 1) / l))) := neg_le_neg h
    _ = _ := by ring

private lemma shifted_square_bound {M x : ℝ} (hM : 0 ≤ M) (hx : |x| ≤ M)
    (v : ℤ × ℤ) :
    ((v.1 : ℝ) + v.2 * x) ^ 2 ≤ 2 * (1 + M ^ 2) * size v := by
  have hx2 : x ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hM).mpr hx
  have h := mul_le_mul_of_nonneg_right hx2 (sq_nonneg (v.2 : ℝ))
  dsimp [size]
  nlinarith [sq_nonneg ((v.1 : ℝ) - v.2 * x),
    mul_nonneg (sq_nonneg M) (sq_nonneg (v.1 : ℝ))]

private lemma shear_derivative_bound {M l x y : ℝ} (hM : 0 ≤ M) (hl : 0 < l)
    (hx : |x| ≤ M) (hly : l ≤ y) (v : ℤ × ℤ) :
    |2 * (v.2 : ℝ) * ((v.1 : ℝ) + v.2 * x) / y| ≤
      ((1 + 2 * (1 + M ^ 2)) / l) * size v := by
  have hy : 0 < y := hl.trans_le hly
  have hs := shifted_square_bound hM hx v
  have hn : 0 ≤ size v := by dsimp [size]; positivity
  have h : |2 * (v.2 : ℝ) * ((v.1 : ℝ) + v.2 * x)| ≤
      (1 + 2 * (1 + M ^ 2)) * size v := by
    apply abs_le.mpr
    dsimp [size] at *
    constructor <;> nlinarith [sq_nonneg ((v.2 : ℝ) - ((v.1 : ℝ) + v.2 * x)),
      sq_nonneg ((v.2 : ℝ) + ((v.1 : ℝ) + v.2 * x))]
  rw [abs_div, abs_of_pos hy]
  calc
    _ ≤ ((1 + 2 * (1 + M ^ 2)) * size v) / y := div_le_div_of_nonneg_right h hy.le
    _ ≤ ((1 + 2 * (1 + M ^ 2)) * size v) / l := by
      exact div_le_div_of_nonneg_left (by positivity) hl hly
    _ = _ := by ring

/-- Termwise differentiation of the genuine double series in the shear parameter. -/
theorem hasDerivAt_shear (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    HasDerivAt (fun a => F t a y)
      (∑' v : ℤ × ℤ, (-Real.pi * t *
        (2 * (v.2 : ℝ) * ((v.1 : ℝ) + v.2 * x) / y)) *
          Real.exp (-Real.pi * t * Q x y v)) x := by
  let M := |x| + 1
  let C := max (2 * y) ((2 * M ^ 2 + 1) / y)
  let a := Real.pi * t / C
  let B := Real.pi * t * ((1 + 2 * (1 + M ^ 2)) / y)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : 0 < C := (by positivity : 0 < 2 * y).trans_le (le_max_left _ _)
  have ha : 0 < a := div_pos (mul_pos Real.pi_pos ht) hC
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let g := fun (v : ℤ × ℤ) (z : ℝ) => Real.exp (-Real.pi * t * Q z y v)
  let g' := fun (v : ℤ × ℤ) (z : ℝ) => (-Real.pi * t *
    (2 * (v.2 : ℝ) * ((v.1 : ℝ) + v.2 * z) / y)) * g v z
  have hd (v : ℤ × ℤ) (z : ℝ) : HasDerivAt (g v) (g' v z) z := by
    have hq := (((((hasDerivAt_id z).const_mul (v.2 : ℝ)).const_add
      (v.1 : ℝ)).pow 2).div_const y).add_const (y * (v.2 : ℝ) ^ 2)
    convert (hq.const_mul (-Real.pi * t)).exp using 1
    · funext a
      simp only [g, Q]
      congr 1
    · dsimp [g, g', Q]
      ring
  have hb (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo (x - 1) (x + 1)) :
      ‖g' v z‖ ≤ B * (size v * Real.exp (-a * size v)) := by
    have hzM : |z| ≤ M := by
      apply abs_le.mpr
      dsimp [M]
      constructor <;> linarith [le_abs_self x, neg_abs_le x, hz.1, hz.2]
    have he := compact_exponential_bound hM hy ht hzM le_rfl le_rfl v
    have hq := shear_derivative_bound hM hy hzM le_rfl v
    have hn : 0 ≤ size v := by dsimp [size]; positivity
    dsimp [g', g]
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_pos Real.pi_pos, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.pi * t * (((1 + 2 * (1 + M ^ 2)) / y) * size v)) *
          Real.exp (-a * size v) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hq (mul_pos Real.pi_pos ht).le
        · exact he
        · exact (Real.exp_pos _).le
        · positivity
      _ = _ := by dsimp [B]; ring
  have hx : x ∈ Set.Ioo (x - 1) (x + 1) := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected ((weight_summable a ha).mul_left B)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected (fun v z _ => hd v z) hb hx
    (summable t x ht hy) hx

private lemma height_derivative_bound {M l x y : ℝ} (hM : 0 ≤ M) (hl : 0 < l)
    (hx : |x| ≤ M) (hly : l ≤ y) (v : ℤ × ℤ) :
    |(v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2| ≤
      (1 + 2 * (1 + M ^ 2) / l ^ 2) * size v := by
  have hy : 0 < y := hl.trans_le hly
  have h := shifted_square_bound hM hx v
  have hn : 0 ≤ size v := by dsimp [size]; positivity
  have hz : l ^ 2 ≤ y ^ 2 := by nlinarith
  have hq : ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2 ≤
      (2 * (1 + M ^ 2) * size v) / l ^ 2 := by
    exact (div_le_div_of_nonneg_right h (sq_nonneg y)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hl) hz)
  have h0 : 0 ≤ ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2 := by positivity
  have hq' : ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2 ≤
      (2 * (1 + M ^ 2) / l ^ 2) * size v := by
    convert hq using 1 <;> ring
  have hB : 0 ≤ 2 * (1 + M ^ 2) / l ^ 2 * size v := by positivity
  apply abs_le.mpr
  dsimp [size] at *
  constructor <;> nlinarith [sq_nonneg (v.1 : ℝ), sq_nonneg (v.2 : ℝ)]

/-- Termwise differentiation of the genuine double series in the height parameter. -/
theorem hasDerivAt_height (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    HasDerivAt (fun b => F t x b)
      (∑' v : ℤ × ℤ, (-Real.pi * t *
        ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2)) *
          Real.exp (-Real.pi * t * Q x y v)) y := by
  let M := |x|
  let l := y / 2
  let C := max (2 * (2 * y)) ((2 * M ^ 2 + 1) / l)
  let a := Real.pi * t / C
  let B := Real.pi * t * (1 + 2 * (1 + M ^ 2) / l ^ 2)
  have hl : 0 < l := by dsimp [l]; positivity
  have hC : 0 < C := (by positivity : 0 < 2 * (2 * y)).trans_le (le_max_left _ _)
  have ha : 0 < a := div_pos (mul_pos Real.pi_pos ht) hC
  let g := fun (v : ℤ × ℤ) (z : ℝ) => Real.exp (-Real.pi * t * Q x z v)
  let g' := fun (v : ℤ × ℤ) (z : ℝ) => (-Real.pi * t *
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / z ^ 2)) * g v z
  have hd (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo l (2 * y)) :
      HasDerivAt (g v) (g' v z) z := by
    have hz0 : z ≠ 0 := (hl.trans hz.1).ne'
    have hq := ((hasDerivAt_const z (((v.1 : ℝ) + v.2 * x) ^ 2)).div
      (hasDerivAt_id z) hz0).add ((hasDerivAt_id z).mul_const ((v.2 : ℝ) ^ 2))
    convert (hq.const_mul (-Real.pi * t)).exp using 1 <;> dsimp [g, g', Q] <;> ring
  have hb (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo l (2 * y)) :
      ‖g' v z‖ ≤ B * (size v * Real.exp (-a * size v)) := by
    have he := compact_exponential_bound (abs_nonneg x) hl ht le_rfl hz.1.le hz.2.le v
    have hq := height_derivative_bound (abs_nonneg x) hl le_rfl hz.1.le v
    dsimp [g', g]
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_pos Real.pi_pos, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.pi * t * ((1 + 2 * (1 + M ^ 2) / l ^ 2) * size v)) *
          Real.exp (-a * size v) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hq (mul_pos Real.pi_pos ht).le
        · exact he
        · exact (Real.exp_pos _).le
        · have : 0 ≤ size v := by dsimp [size]; positivity
          positivity
      _ = _ := by dsimp [B]; ring
  have hy' : y ∈ Set.Ioo l (2 * y) := by dsimp [l]; constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected ((weight_summable a ha).mul_left B)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected hd hb hy' (summable t x ht hy) hy'

private lemma second_height_bound {M l x y : ℝ} (hM : 0 ≤ M) (hl : 0 < l)
    (hx : |x| ≤ M) (hly : l ≤ y) (v : ℤ × ℤ) :
    |2 * ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 3| ≤
      (4 * (1 + M ^ 2) / l ^ 3) * size v := by
  have hy : 0 < y := hl.trans_le hly
  have h := shifted_square_bound hM hx v
  have hz : l ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hl.le hly 3
  have hn : 0 ≤ size v := by dsimp [size]; positivity
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ (4 * (1 + M ^ 2) * size v) / y ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ (4 * (1 + M ^ 2) * size v) / l ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hz
    _ = _ := by ring

/-- The second height derivative is the sum of the second Gaussian derivatives. -/
theorem hasDerivAt_height_deriv (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    HasDerivAt (fun b => deriv (fun z => F t x z) b)
      (∑' v : ℤ × ℤ, ((Real.pi * t) ^ 2 *
        ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2) ^ 2 -
        Real.pi * t * (2 * ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 3)) *
          Real.exp (-Real.pi * t * Q x y v)) y := by
  let M := |x|
  let l := y / 2
  let C := max (2 * (2 * y)) ((2 * M ^ 2 + 1) / l)
  let a := Real.pi * t / C
  let p := Real.pi * t
  let B := 1 + 2 * (1 + M ^ 2) / l ^ 2
  let D := 4 * (1 + M ^ 2) / l ^ 3
  have hl : 0 < l := by dsimp [l]; positivity
  have hp : 0 < p := mul_pos Real.pi_pos ht
  have hC : 0 < C := (by positivity : 0 < 2 * (2 * y)).trans_le (le_max_left _ _)
  have ha : 0 < a := div_pos hp hC
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let E := fun (v : ℤ × ℤ) (z : ℝ) => Real.exp (-Real.pi * t * Q x z v)
  let A := fun (v : ℤ × ℤ) (z : ℝ) =>
    (v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / z ^ 2
  let H := fun (v : ℤ × ℤ) (z : ℝ) =>
    2 * ((v.1 : ℝ) + v.2 * x) ^ 2 / z ^ 3
  let g := fun v z => (-Real.pi * t * A v z) * E v z
  let g' := fun v z => (p ^ 2 * A v z ^ 2 - p * H v z) * E v z
  have bounds (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo l (2 * y)) :
      |A v z| ≤ B * size v ∧ |H v z| ≤ D * size v ∧
        E v z ≤ Real.exp (-a * size v) := by
    exact ⟨height_derivative_bound (abs_nonneg x) hl le_rfl hz.1.le v,
      second_height_bound (abs_nonneg x) hl le_rfl hz.1.le v,
      compact_exponential_bound (abs_nonneg x) hl ht le_rfl hz.1.le hz.2.le v⟩
  have hd (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo l (2 * y)) :
      HasDerivAt (g v) (g' v z) z := by
    have hz0 : z ≠ 0 := (hl.trans hz.1).ne'
    have hq := ((hasDerivAt_const z (((v.1 : ℝ) + v.2 * x) ^ 2)).div
      (hasDerivAt_id z) hz0).add ((hasDerivAt_id z).mul_const ((v.2 : ℝ) ^ 2))
    have he : HasDerivAt (E v) ((-p * A v z) * E v z) z := by
      convert (hq.const_mul (-Real.pi * t)).exp using 1 <;> dsimp [E, A, Q, p] <;> ring
    have hd := (hasDerivAt_const z (((v.1 : ℝ) + v.2 * x) ^ 2)).div
      ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz0)
    have hdA : HasDerivAt (A v) (H v z) z := by
      convert (hasDerivAt_const z ((v.2 : ℝ) ^ 2)).sub hd using 1
      · rfl
      · dsimp [H]
        simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one]
        field_simp
        <;> ring
    convert (hdA.const_mul (-p)).mul he using 1
    · funext w
      dsimp [g, p]
      ring
    · dsimp [g']
      ring
  have hb (v : ℤ × ℤ) (z : ℝ) (hz : z ∈ Set.Ioo l (2 * y)) :
      ‖g' v z‖ ≤ (p ^ 2 * B ^ 2) * (size v ^ 2 * Real.exp (-a * size v)) +
        (p * D) * (size v * Real.exp (-a * size v)) := by
    obtain ⟨hA, hH, he⟩ := bounds v z hz
    have hn : 0 ≤ size v := by dsimp [size]; positivity
    have hs : A v z ^ 2 ≤ B ^ 2 * size v ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB hn)).mpr hA
      simpa [mul_pow] using h
    have hc : |p ^ 2 * A v z ^ 2 - p * H v z| ≤
        p ^ 2 * B ^ 2 * size v ^ 2 + p * D * size v := by
      calc
        _ ≤ |p ^ 2 * A v z ^ 2| + |p * H v z| := abs_sub _ _
        _ = p ^ 2 * A v z ^ 2 + p * |H v z| := by
          rw [abs_of_nonneg (by positivity), abs_mul, abs_of_pos hp]
        _ ≤ _ := by nlinarith
    dsimp [g']
    rw [abs_mul, abs_of_pos (show 0 < E v z from Real.exp_pos _)]
    calc
      _ ≤ (p ^ 2 * B ^ 2 * size v ^ 2 + p * D * size v) *
          Real.exp (-a * size v) := mul_le_mul hc he (by positivity) (by positivity)
      _ = _ := by ring
  have hy' : y ∈ Set.Ioo l (2 * y) := by dsimp [l]; constructor <;> linarith
  have hg : Summable (fun v => g v y) := by
    apply ((weight_summable a ha).mul_left (p * B)).of_norm_bounded
    intro v
    obtain ⟨hA, _, he⟩ := bounds v y hy'
    dsimp [g]
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos ht,
      abs_of_pos (show 0 < E v y from Real.exp_pos _)]
    have hn : 0 ≤ size v := by dsimp [size]; positivity
    calc
      _ ≤ (p * (B * size v)) * Real.exp (-a * size v) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA hp.le) he
          (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [p]; ring
  have hh := hasDerivAt_tsum_of_isPreconnected
    (((square_weight_summable a ha).mul_left (p ^ 2 * B ^ 2)).add
      ((weight_summable a ha).mul_left (p * D)))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected hd hb hy' hg hy'
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy'] with z hz
  simpa only [g, E, A] using (hasDerivAt_height t x ht (hl.trans hz.1)).deriv

private def reflect : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun v := (-v.1, v.2)
  invFun v := (-v.1, v.2)
  left_inv v := by simp
  right_inv v := by simp


private def quarterTurn : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun v := (v.2, -v.1)
  invFun v := (-v.2, v.1)
  left_inv v := by simp
  right_inv v := by simp




private lemma inverse_gram (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (gram x y)⁻¹ = !![x ^ 2 / y + y, -x / y; -x / y, 1 / y] := by
  rw [Matrix.inv_def, gram_det x hy]
  simp [gram, Matrix.adjugate_fin_two]
  <;> ring

private lemma inverse_quadratic (x : ℝ) {y : ℝ} (hy : y ≠ 0) (a : Fin 2 → ℤ) :
    MatrixGaussian.quadratic (gram x y)⁻¹ (fun i => (a i : ℝ)) =
      Q x y (a 1, -a 0) := by
  rw [inverse_gram x hy]
  simp [MatrixGaussian.quadratic, dotProduct, mulVec, Fin.sum_univ_two, Q]
  ring

/-- Dimension two and determinant one make the dual form an integer rotation of the
original form. Thus reciprocal temperature needs no change of shape. -/
theorem temperature_duality (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    F t x y = t⁻¹ * F t⁻¹ x y := by
  have hp := (MatrixGaussian.poisson_gaussian (gram x y) (gram_posDef x hy)
    (t : ℂ) (by simpa using ht)).2.2
  have hleft : (∑' a : Fin 2 → ℤ, Complex.exp
      (-Real.pi * (t : ℂ) *
        (MatrixGaussian.quadratic (gram x y) (fun i => (a i : ℝ)) : ℂ))) =
      (F t x y : ℂ) := by
    rw [F, Complex.ofReal_tsum]
    rw [← (finTwoArrowEquiv ℤ).tsum_eq]
    apply tsum_congr
    intro a
    rw [quadratic_gram, Complex.ofReal_exp]
    congr 1
    simp [Q]
  have hright : (∑' a : Fin 2 → ℤ, Complex.exp
      (-Real.pi / (t : ℂ) *
        (MatrixGaussian.quadratic (gram x y)⁻¹ (fun i => (a i : ℝ)) : ℂ))) =
      (F t⁻¹ x y : ℂ) := by
    rw [F, Complex.ofReal_tsum]
    rw [← quarterTurn.tsum_eq, ← (finTwoArrowEquiv ℤ).tsum_eq]
    apply tsum_congr
    intro a
    rw [inverse_quadratic x hy.ne', Complex.ofReal_exp]
    simp [quarterTurn, div_eq_mul_inv]
  rw [hleft, hright, gram_det x hy.ne'] at hp
  norm_num only [Nat.cast_ofNat, neg_div, div_self (two_ne_zero : (2 : ℂ) ≠ 0)] at hp
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast] at hp
  apply Complex.ofReal_injective
  simpa using hp

private lemma q_normSq (z : UpperHalfPlane) (v : ℤ × ℤ) :
    Q z.re z.im v = Complex.normSq ((v.1 : ℂ) + (v.2 : ℂ) * z) / z.im := by
  simp only [Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, zero_add, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, ← pow_two]
  field_simp [z.im_ne_zero]
  <;> ring

private lemma modular_reindex (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) : ∃ e : (ℤ × ℤ) ≃+ (ℤ × ℤ),
      ∀ v, Q (g • z).re (g • z).im v = Q z.re z.im (e v) := by
  have hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  let e : (ℤ × ℤ) ≃+ (ℤ × ℤ) := {
    toFun := fun v => (g 1 1 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 0 0 * v.2)
    invFun := fun v => (g 0 0 * v.1 - g 0 1 * v.2, -g 1 0 * v.1 + g 1 1 * v.2)
    left_inv := by
      intro v
      apply Prod.ext <;> dsimp
      · nlinarith [congrArg (fun a => a * v.1) hg]
      · nlinarith [congrArg (fun a => a * v.2) hg]
    right_inv := by
      intro v
      apply Prod.ext <;> dsimp
      · nlinarith [congrArg (fun a => a * v.1) hg]
      · nlinarith [congrArg (fun a => a * v.2) hg]
    map_add' := by
      intro v w
      apply Prod.ext <;> dsimp <;> ring }
  let d : ℂ := (g 1 0 : ℂ) * z + (g 1 1 : ℂ)
  have hd : d ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero (g : Matrix.GeneralLinearGroup (Fin 2) ℝ) z
    simpa only [ModularGroup.denom_apply, d] using h
  have hi : (g • z).im = z.im / Complex.normSq d := by
    simpa only [ModularGroup.denom_apply, d] using
      ModularGroup.im_smul_eq_div_normSq g z
  have hn (v : ℤ × ℤ) :
      (v.1 : ℂ) + (v.2 : ℂ) * (g • z : UpperHalfPlane) =
        ((e v).1 + (e v).2 * (z : ℂ)) / d := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change (v.1 : ℂ) + (v.2 : ℂ) * (_ / d) = _
    field_simp [hd]
    dsimp [e, d]
    push_cast
    ring
  have hq (v : ℤ × ℤ) : Q (g • z).re (g • z).im v = Q z.re z.im (e v) := by
    rw [q_normSq, q_normSq, hn, Complex.normSq_div, hi]
    field_simp [z.im_ne_zero, (Complex.normSq_pos.mpr hd).ne']
  exact ⟨e, hq⟩

private lemma reduced_quadratic_representative (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 / 2 ∧ 0 < b ∧ 1 ≤ a ^ 2 + b ^ 2 ∧
      Real.sqrt 3 / 2 ≤ b ∧ ∃ e : (ℤ × ℤ) ≃+ (ℤ × ℤ),
        ∀ v, Q x y v = Q a b (e v) := by
  let z : UpperHalfPlane := ⟨⟨x, y⟩, hy⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  let w := g • z
  have hw : w ∈ ModularGroup.fd := hg
  have hb := w.im_pos
  have hnorm : 1 ≤ w.re ^ 2 + w.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using hw.1
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hw
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : Real.sqrt 3 / 2 ≤ w.im := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  obtain ⟨e, hqe⟩ := modular_reindex g z
  let r : (ℤ × ℤ) ≃+ (ℤ × ℤ) := {
    toEquiv := reflect
    map_add' := by intro v u; apply Prod.ext <;> simp [reflect, add_comm] }
  let f := if 0 ≤ w.re then AddEquiv.refl (ℤ × ℤ) else r
  have hf (v : ℤ × ℤ) : Q |w.re| w.im (f v) = Q w.re w.im v := by
    by_cases h : 0 ≤ w.re
    · simp [f, h, abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      simp only [f, if_neg h]
      rw [show r v = (-v.1, v.2) from rfl]
      simp only [Q, Prod.fst, Prod.snd, Int.cast_neg]
      ring
  refine ⟨|w.re|, w.im, abs_nonneg _, hw.2, hb, ?_, hc, e.symm.trans f, ?_⟩
  · simpa using hnorm
  · intro v
    have he : Q x y v = Q w.re w.im (e.symm v) := by
      have he := (hqe (e.symm v)).symm
      rw [e.apply_symm_apply] at he
      change Q x y v = Q w.re w.im (e.symm v) at he
      exact he
    exact he.trans (hf (e.symm v)).symm


/-- Integer coordinates in the normalized complex lattice. -/
def latticePoint (x y : ℝ) (v : ℤ × ℤ) : ℂ :=
  ⟨((v.1 : ℝ) + v.2 * x) / Real.sqrt y, Real.sqrt y * v.2⟩

/-- The actual squared length of each lattice point is the binary form, and distinct
integer pairs give distinct points. -/
theorem lattice_geometry (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Function.Injective (latticePoint x y) ∧
      ∀ v : ℤ × ℤ, Complex.normSq (latticePoint x y v) = Q x y v := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  constructor
  · intro v w h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    dsimp [latticePoint] at h1 h2
    have hn : (v.2 : ℝ) = w.2 := (mul_left_cancel₀ hs h2)
    have hm : (v.1 : ℝ) = w.1 := by
      have hm := (div_left_inj' hs).mp h1
      rw [hn] at hm
      exact add_right_cancel hm
    exact Prod.ext (Int.cast_injective hm) (Int.cast_injective hn)
  · intro v
    simp only [latticePoint, Complex.normSq_mk, ← pow_two, Q, div_pow, mul_pow,
      Real.sq_sqrt hy.le]


/-- Theta in arbitrary complex basis coordinates. -/
def basisTheta (t : ℝ) (a b : ℂ) : ℝ :=
  ∑' v : ℤ × ℤ, Real.exp (-Real.pi * t *
    Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b))

/-- A unit-area basis admits reduced coordinates through an additive integer reindexing,
with equality of the actual squared lengths at every lattice point. -/
theorem basis_reduction_geometry (a b : ℂ) (hab : |a.re * b.im - a.im * b.re| = 1) :
    ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ 1 ≤ x ^ 2 + y ^ 2 ∧
      Real.sqrt 3 / 2 ≤ y ∧ ∃ e : (ℤ × ℤ) ≃+ (ℤ × ℤ), ∀ v,
        Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = Q x y (e v) := by
  have hdet : (a.re * b.im - a.im * b.re) ^ 2 = 1 := by
    nlinarith [sq_abs (a.re * b.im - a.im * b.re)]
  have ha : 0 < Complex.normSq a := by
    by_contra h
    have hz : Complex.normSq a = 0 := le_antisymm (not_lt.mp h) (Complex.normSq_nonneg a)
    have ha0 : a = 0 := Complex.normSq_eq_zero.mp hz
    simp [ha0] at hab
  let x := (a.re * b.re + a.im * b.im) / Complex.normSq a
  let y := (Complex.normSq a)⁻¹
  have hy : 0 < y := inv_pos.mpr ha
  have hq (v : ℤ × ℤ) :
      Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = Q x y v := by
    have hid : Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) * Complex.normSq a =
        (Complex.normSq a * (v.1 : ℝ) + (a.re * b.re + a.im * b.im) * v.2) ^ 2 +
          (v.2 : ℝ) ^ 2 * (a.re * b.im - a.im * b.re) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
        zero_add]
      ring
    rw [hdet, mul_one] at hid
    dsimp [Q, x, y]
    field_simp
    nlinarith [hid]
  obtain ⟨r, s, hr, hrs, hs, hnorm, hc, e, he⟩ :=
    reduced_quadratic_representative x hy
  exact ⟨r, s, hr, hrs, hs, hnorm, hc, e, fun v => (hq v).trans (he v)⟩


private def basisPointMap (a b : ℂ) : (ℤ × ℤ) →+ ℂ where
  toFun v := (v.1 : ℂ) * a + (v.2 : ℂ) * b
  map_zero' := by simp
  map_add' := by intro v w; simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

private lemma normSq_real_smul_add (p q : ℂ) (c d : ℝ) :
    Complex.normSq (c • p + d • q) = c ^ 2 * Complex.normSq p +
      d ^ 2 * Complex.normSq q + 2 * c * d * (p.re * q.re + p.im * q.im) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- Preserving the quadratic form through an additive integer equivalence preserves the
actual lattice through a real-linear orthogonal equivalence, point by point. -/
theorem basis_isometry_of_quadratic_reindex {a b : ℂ} {x y : ℝ}
    (e : (ℤ × ℤ) ≃+ (ℤ × ℤ))
    (hQ : ∀ v : ℤ × ℤ,
      Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = Q x y (e v)) :
    ∃ U : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ v : ℤ × ℤ,
      U ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = latticePoint x y (e v) := by
  by_cases hy : 0 < y
  · let B := basisPointMap a b
    let p := B (e.symm (1, 0))
    let q := B (e.symm (0, 1))
    have hcoord (v : ℤ × ℤ) : B (e.symm v) = (v.1 : ℂ) * p + (v.2 : ℂ) * q := by
      have hd : v = v.1 • ((1, 0) : ℤ × ℤ) + v.2 • ((0, 1) : ℤ × ℤ) := by
        ext <;> simp
      have h := congrArg (fun w => B (e.symm w)) hd
      simp only [map_add, map_zsmul] at h
      simpa only [zsmul_eq_mul] using h
    have hp : Complex.normSq p = 1 / y := by
      have h := hQ (e.symm (1, 0))
      change Complex.normSq p = Q x y (e (e.symm (1, 0))) at h
      rw [e.apply_symm_apply] at h
      simpa [Q] using h
    have hq : Complex.normSq q = x ^ 2 / y + y := by
      have h := hQ (e.symm (0, 1))
      change Complex.normSq q = Q x y (e (e.symm (0, 1))) at h
      rw [e.apply_symm_apply] at h
      simpa [Q] using h
    have hsum : Complex.normSq (p + q) = (1 + x) ^ 2 / y + y := by
      have h := hQ (e.symm (1, 1))
      change Complex.normSq (B (e.symm (1, 1))) = Q x y (e (e.symm (1, 1))) at h
      rw [e.apply_symm_apply] at h
      have hc := hcoord (1, 1)
      simp only [Int.cast_one, one_mul] at hc
      rw [hc] at h
      simpa [Q] using h
    have hpq : p.re * q.re + p.im * q.im = x / y := by
      have h : Complex.normSq (p + q) = Complex.normSq p + Complex.normSq q +
          2 * (p.re * q.re + p.im * q.im) := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
        ring
      rw [hp, hq, hsum] at h
      field_simp [hy.ne'] at h ⊢
      nlinarith only [h]
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    let V : ℂ →ₗ[ℝ] ℂ :=
      (Real.sqrt y • Complex.reLm - (x / Real.sqrt y) • Complex.imLm).smulRight p +
        ((1 / Real.sqrt y) • Complex.imLm).smulRight q
    have hV (z : ℂ) : V z =
        (Real.sqrt y * z.re - x / Real.sqrt y * z.im) • p +
          (z.im / Real.sqrt y) • q := by
      simp only [V, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul]
      congr 1 <;> congr 1 <;> ring
    have hnorm (z : ℂ) : Complex.normSq (V z) = Complex.normSq z := by
      rw [hV, normSq_real_smul_add, hp, hq, hpq]
      calc
        _ = (Real.sqrt y ^ 2 / y) * z.re ^ 2 +
            (y / Real.sqrt y ^ 2) * z.im ^ 2 := by
          field_simp [hs.ne', hy.ne']
          <;> ring
        _ = _ := by rw [hs2]; simp [hy.ne', Complex.normSq_apply, pow_two]
    let W : ℂ →ₗᵢ[ℝ] ℂ := {
      toLinearMap := V
      norm_map' := fun z => by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simpa only [← Complex.normSq_eq_norm_sq] using hnorm z }
    let O : ℂ ≃ₗᵢ[ℝ] ℂ := LinearIsometryEquiv.ofSurjective W
      (LinearMap.surjective_of_injective (f := V) W.injective)
    have hpoint (v : ℤ × ℤ) : O (latticePoint x y v) = B (e.symm v) := by
      change V (latticePoint x y v) = B (e.symm v)
      rw [hV, hcoord]
      have hfirst : Real.sqrt y * (latticePoint x y v).re -
          x / Real.sqrt y * (latticePoint x y v).im = (v.1 : ℝ) := by
        dsimp [latticePoint]
        field_simp [hs.ne']
        <;> ring
      have hsecond : (latticePoint x y v).im / Real.sqrt y = (v.2 : ℝ) := by
        dsimp [latticePoint]
        field_simp [hs.ne']
      rw [hfirst, hsecond]
      simp only [Complex.real_smul]
      push_cast <;> rfl
    refine ⟨O.symm, fun v => ?_⟩
    apply O.injective
    rw [O.apply_symm_apply, hpoint, e.symm_apply_apply]
    rfl
  · by_cases hz : y = 0
    · subst y
      have ha : a = 0 := Complex.normSq_eq_zero.mp (by simpa [Q] using hQ (1, 0))
      have hb : b = 0 := Complex.normSq_eq_zero.mp (by simpa [Q] using hQ (0, 1))
      subst a
      subst b
      refine ⟨LinearIsometryEquiv.refl ℝ ℂ, fun v => ?_⟩
      apply Complex.ext <;> simp [latticePoint]
    · have hyn : y < 0 := lt_of_le_of_ne (le_of_not_gt hy) hz
      have hn := Complex.normSq_nonneg
        (((e.symm (1, 0)).1 : ℂ) * a + ((e.symm (1, 0)).2 : ℂ) * b)
      rw [hQ, e.apply_symm_apply] at hn
      have hn' : 0 ≤ 1 / y := by simpa [Q] using hn
      exact False.elim ((not_le_of_gt (one_div_neg.mpr hyn)) hn')

end
end D5.S3.Fourier.PlanarTheta
