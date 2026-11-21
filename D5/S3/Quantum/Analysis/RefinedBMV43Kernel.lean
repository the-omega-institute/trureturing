/- GID: D5/S3/Quantum/Analysis/RefinedBMV43Kernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV43Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quartic refined BMV defect has a positive Gram and Cauchy kernel decomposition. -/

import D5.S3.Quantum.Analysis.RefinedBMVKernel
import Batteries.Tactic.OpenPrivate

/-! # The centered coefficient kernel for the refined BMV (4,3) bound -/

open private weighted_cauchy_psd from D5.S3.Quantum.Analysis.RefinedBMVKernel

open Matrix

noncomputable section

namespace RefinedBMV

/-- Representatives of the cyclic orbits of the three gaps between successive Bs. -/
def gapOrbits43 : List (ℕ × ℕ × ℕ) :=
  [(4, 0, 0), (3, 1, 0), (3, 0, 1), (2, 2, 0), (2, 1, 1)]

/-- The fifteen ordered triples of gaps for four As and three Bs. -/
def gaps43 : List (ℕ × ℕ × ℕ) :=
  gapOrbits43.flatMap fun (p, q, r) ↦ [(p, q, r), (q, r, p), (r, p, q)]

/-- The homogeneous symmetric polynomial of degree four on the cubed inputs,
minus fifteen times the fourth power of their product before cubing. -/
def defect43 (x y z : ℝ) : ℝ :=
  (gaps43.map fun (p, q, r) ↦ (x ^ 3) ^ p * (y ^ 3) ^ q * (z ^ 3) ^ r).sum -
    15 * (x * y * z) ^ 4

private def feature43₀ (x y : ℝ) := x ^ 6 + 2 * x ^ 5 * y + 2 * x ^ 4 * y ^ 2
private def feature43₁ (x y : ℝ) := x ^ 3 * y ^ 3
private def feature43₂ (x y : ℝ) := x ^ 2 * y ^ 4
private def feature43₃ (x y : ℝ) := 2 * x * y ^ 5 + y ^ 6

-- The four coordinates of TᵀF in the LDLᵀ factorization of the coefficient matrix.
private def gram43₀ (x y : ℝ) :=
  feature43₀ x y + 3 * feature43₁ x y + 4 * feature43₂ x y + 2 * feature43₃ x y
private def gram43₁ (x y : ℝ) :=
  feature43₁ x y + 2 * feature43₂ x y + feature43₃ x y / 6
private def gram43₂ (x y : ℝ) := feature43₂ x y
private def gram43₃ (x y : ℝ) := feature43₃ x y

private def gram43 (x y z : ℝ) :=
  gram43₀ x y * gram43₀ x z + 6 * (gram43₁ x y * gram43₁ x z) +
    5 * (gram43₂ x y * gram43₂ x z) + (5 / 6) * (gram43₃ x y * gram43₃ x z)

private def numerator43 (x y z : ℝ) := 20 * x ^ 3 * y ^ 5 * z ^ 5

/-- The kernel centered at the first spectral value. Division by zero in the
Cauchy term gives zero when the other two spectral values are both zero. -/
def centeredKernel43 (x y z : ℝ) : ℝ :=
  if x = 0 then 5 * y ^ 5 * z ^ 5
  else (gram43 x y z + numerator43 x y z / (y + z)) / ((x + y) * (x + z))

private theorem polynomial43 (x y z : ℝ) :
    (x - y) * (x - z) * ((y + z) * gram43 x y z + numerator43 x y z) +
    (y - z) * (y - x) * ((z + x) * gram43 y z x + numerator43 y z x) +
    (z - x) * (z - y) * ((x + y) * gram43 z x y + numerator43 z x y) =
      (x + y) * (y + z) * (z + x) * defect43 x y z := by
  simp only [defect43, gaps43, gapOrbits43, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, gram43, gram43₀, gram43₁, gram43₂, gram43₃, feature43₀, feature43₁,
    feature43₂, feature43₃, numerator43]
  ring

private theorem clear_centeredKernel43 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y) * (y + z) * (z + x) * centeredKernel43 x y z =
      (y + z) * gram43 x y z + numerator43 x y z := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [centeredKernel43, gram43, gram43₀, gram43₁, gram43₂, gram43₃,
      feature43₀, feature43₁, feature43₂, feature43₃, numerator43]
    ring
  · have hxy : x + y ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hx hy)
    have hxz : x + z ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hx hz)
    rw [centeredKernel43, ite_eq_right hx.ne',
      show (x + y) * (y + z) * (z + x) = (y + z) * ((x + y) * (x + z)) by ring,
      mul_assoc, mul_div_cancel₀ _ (mul_ne_zero hxy hxz), mul_add]
    by_cases hyz : y + z = 0
    · have hy₀ : y = 0 := by linarith
      have hz₀ : z = 0 := by linarith
      simp [hy₀, hz₀, numerator43]
    · rw [mul_div_cancel₀ _ hyz]

private theorem centeredKernel43_at_zeros (x : ℝ) (hx : 0 ≤ x) :
    centeredKernel43 x 0 0 = x ^ 10 := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [centeredKernel43]
  · simp [centeredKernel43, hx.ne', gram43, gram43₀, gram43₁, gram43₂, gram43₃,
      feature43₀, feature43₁, feature43₂, feature43₃, numerator43]
    field_simp [hx.ne']

private theorem defect43_at_zeros (x : ℝ) (hx : 0 ≤ x) :
    defect43 x 0 0 =
      (x - 0) * (x - 0) * centeredKernel43 x 0 0 +
      (0 - 0) * (0 - x) * centeredKernel43 0 0 x +
      (0 - x) * (0 - 0) * centeredKernel43 0 x 0 := by
  rw [centeredKernel43_at_zeros x hx]
  norm_num [defect43, gaps43, gapOrbits43]
  ring

private theorem defect43_rotate (x y z : ℝ) : defect43 y z x = defect43 x y z := by
  simp only [defect43, gaps43, gapOrbits43, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- The exact centered-kernel decomposition, including vanishing and repeated inputs. -/
theorem defect43_eq_cyclic (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    defect43 x y z =
      (x - y) * (x - z) * centeredKernel43 x y z +
      (y - z) * (y - x) * centeredKernel43 y z x +
      (z - x) * (z - y) * centeredKernel43 z x y := by
  by_cases hxy : x + y = 0
  · have hx₀ : x = 0 := by linarith
    have hy₀ : y = 0 := by linarith
    subst x y
    rw [defect43_rotate z 0 0, defect43_at_zeros z hz]
    ring
  by_cases hyz : y + z = 0
  · have hy₀ : y = 0 := by linarith
    have hz₀ : z = 0 := by linarith
    subst y z
    exact defect43_at_zeros x hx
  by_cases hzx : z + x = 0
  · have hx₀ : x = 0 := by linarith
    have hz₀ : z = 0 := by linarith
    subst x z
    rw [← defect43_rotate 0 y 0, defect43_at_zeros y hy]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hxy hyz) hzx)
  calc
    _ = (x - y) * (x - z) * ((x + y) * (y + z) * (z + x) * centeredKernel43 x y z) +
        (y - z) * (y - x) * ((y + z) * (z + x) * (x + y) * centeredKernel43 y z x) +
        (z - x) * (z - y) * ((z + x) * (x + y) * (y + z) * centeredKernel43 z x y) := by
          rw [clear_centeredKernel43 x y z hx hy hz, clear_centeredKernel43 y z x hy hz hx,
            clear_centeredKernel43 z x y hz hx hy]
          exact (polynomial43 x y z).symm
    _ = _ := by ring

/-- Every finite matrix cut out of a centered kernel at nonnegative inputs is PSD. -/
theorem centeredKernel43_psd {ι : Type*} [Finite ι]
    (x : ℝ) (hx : 0 ≤ x) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (Matrix.of fun i j ↦ centeredKernel43 x (a i) (a j) : Matrix ι ι ℝ).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι
  rcases hx.eq_or_lt with rfl | hx
  · let v (i : ι) := a i ^ 5
    convert (posSemidef_vecMulVec_self_star v).smul (show (0 : ℝ) ≤ 5 by norm_num) using 1
    ext i j
    simp [centeredKernel43, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul, v, mul_assoc]
  · let d (f : ℝ → ℝ) (i : ι) := f (a i) / (x + a i)
    let w := d (fun y ↦ y ^ 5)
    have hC := (weighted_cauchy_psd a w ha (by intro i hi; simp [w, d, hi])).smul
      (show 0 ≤ 20 * x ^ 3 by positivity)
    have h₀ := posSemidef_vecMulVec_self_star (d (gram43₀ x))
    have h₁ := (posSemidef_vecMulVec_self_star (d (gram43₁ x))).smul (show (0 : ℝ) ≤ 6 by norm_num)
    have h₂ := (posSemidef_vecMulVec_self_star (d (gram43₂ x))).smul (show (0 : ℝ) ≤ 5 by norm_num)
    have h₃ := (posSemidef_vecMulVec_self_star (d (gram43₃ x))).smul
      (show (0 : ℝ) ≤ 5 / 6 by norm_num)
    convert (((h₀.add h₁).add h₂).add h₃).add hC using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      star_trivial, smul_eq_mul, centeredKernel43, ite_eq_right hx.ne', gram43, numerator43, w, d,
      div_eq_mul_inv, mul_inv]
    ring

end RefinedBMV
