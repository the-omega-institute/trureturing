/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative near-node Schur remainder for arbitrary actual arithmetic Gram configurations. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Matrix
open scoped BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode

/-- The literal real arithmetic Gram matrix. -/
def H {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i k => K (x i - x k)

/-- Correlations with the new point x j+h. -/
def b {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : ℝ) : Fin n → ℝ :=
  fun i => K (x i - x j - h)

/-- The actual scalar Schur remainder. -/
def S {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : ℝ) : ℝ :=
  firstLiMass - b x j h ⬝ᵥ ((H x)⁻¹ *ᵥ b x j h)

/-- Departure from the anchor column. -/
def u {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : ℝ) : Fin n → ℝ :=
  b x j h - H x *ᵥ Pi.single j 1

/-- Entrywise inverse mass, enlarged by one to remain positive. -/
def q {n : ℕ} (x : Fin n → ℝ) : ℝ := 1 + ∑ i, ∑ k, |(H x)⁻¹ i k|

/-- The logarithmic scale of the insertion. -/
def scale (r : ℝ) : ℝ := Real.log (1 / r)

/-- A conditioning-dependent, explicit insertion radius. -/
def rho {n : ℕ} (x : Fin n → ℝ) (g ell : ℝ) : ℝ :=
  min (g / 2) (min (Real.exp (-4 * (|c| + ell + 1))) ((8 * q x)⁻¹ ^ 2))

private lemma even_abs (t : ℝ) : K t = K |t| := by simp [K]

private lemma column {n : ℕ} (x : Fin n → ℝ) (j i : Fin n) :
    (H x *ᵥ Pi.single j 1) i = K (x i - x j) := by simp [H, Matrix.mulVec_single_one]

private lemma q_ge_one {n : ℕ} (x : Fin n → ℝ) : 1 ≤ q x := by
  dsimp [q]
  positivity

private lemma L_nonneg {a d : ℝ} {N : ℕ} (ha : 0 ≤ a) (had : a ≤ d) :
    0 ≤ L a d N := by
  have hA : 0 ≤ A N := Finset.sum_nonneg (fun _ _ => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  have hP : 0 ≤ P N := Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  dsimp only [L]
  have hd : 0 ≤ d := ha.trans had
  positivity

private lemma schur_identity {n : ℕ} (x : Fin n → ℝ) (j : Fin n)
    (hH : (H x).PosDef) (h : ℝ) :
    S x j h = 2 * (firstLiMass - K |h|) - u x j h ⬝ᵥ ((H x)⁻¹ *ᵥ u x j h) := by
  letI := hH.isUnit.invertible
  let v : Fin n → ℝ := H x *ᵥ Pi.single j 1
  have hi : (H x)⁻¹ *ᵥ v = Pi.single j 1 := by
    dsimp [v]
    rw [← Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hs : ((H x)⁻¹).IsSymm := by
    exact hH.isHermitian.inv.isSymm
  have hu : b x j h = v + u x j h := by dsimp [u, v]; abel
  have hj : u x j h j = K |h| - firstLiMass := by
    simp only [u, Pi.sub_apply, b, sub_self, zero_sub, column, K_zero]
    rw [even_abs (-h), abs_neg]
  have hv : v j = firstLiMass := by simp [v, column, K_zero]
  have hc₁ : v ⬝ᵥ ((H x)⁻¹ *ᵥ u x j h) = u x j h j := by
    rw [hs.dotProduct_mulVec_comm, hi, dotProduct_single_one]
  have hc₂ : u x j h ⬝ᵥ ((H x)⁻¹ *ᵥ v) = u x j h j := by
    rw [hi, dotProduct_single_one]
  dsimp only [S]
  rw [hu]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    hi, dotProduct_single_one, hv, hc₁, hc₂, hj]
  ring

private lemma inverse_quadratic_bound {n : ℕ} (x : Fin n → ℝ) (w : Fin n → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i, |w i| ≤ B) :
    |w ⬝ᵥ ((H x)⁻¹ *ᵥ w)| ≤ q x * B ^ 2 := by
  calc
    _ = |∑ i, ∑ k, w i * ((H x)⁻¹ i k * w k)| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |w i * ((H x)⁻¹ i k * w k)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ k, |(H x)⁻¹ i k| * B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul]
      calc
        _ = |(H x)⁻¹ i k| * (|w i| * |w k|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          simpa only [pow_two] using mul_le_mul (hw i) (hw k) (abs_nonneg _) hB) (abs_nonneg _)
    _ ≤ _ := by
      simp only [← Finset.sum_mul]
      dsimp only [q]
      nlinarith [sq_nonneg B]

private lemma log_scale {r : ℝ} (hr : 0 < r) : scale r = -Real.log r := by
  simp [scale, Real.log_div, hr.ne']

private lemma component_bound {n : ℕ} (x : Fin n → ℝ) (j : Fin n)
    {g d : ℝ} {N : ℕ} (hg : 0 < g) (hgd : g / 2 ≤ d)
    (hgap : ∀ i, i ≠ j → g ≤ |x i - x j|)
    (hwindow : ∀ i, |x i - x j| + g / 2 ≤ d) (hN : Real.exp d < N)
    {h : ℝ} (hr : 0 < |h|) (hrhalf : |h| ≤ 1 / 2) (hrg : |h| ≤ g / 2) :
    ∀ i, |u x j h i| ≤ |h| * (scale |h| / 2 + |c| + L (g / 2) d N + 2 * |h|) := by
  have hL := L_nonneg (a := g / 2) (N := N) (by linarith) hgd
  have hs : 0 ≤ scale |h| := Real.log_nonneg ((one_le_div hr).mpr (by linarith))
  intro i
  by_cases hij : i = j
  · subst i
    have hcusp := cusp_remainder_bound hr hrhalf
    have he : u x j h j = K |h| - firstLiMass := by
      simp only [u, Pi.sub_apply, b, sub_self, zero_sub, column, K_zero]
      rw [even_abs (-h), abs_neg]
    rw [he]
    have ht : |K |h| - firstLiMass| ≤
        |h| * (scale |h| / 2 + |c| + 2 * |h|) := by
      calc
        _ = |-(|h| / 2) * scale |h| + c * |h| + R |h|| := by
          rw [log_scale hr]; congr 1; dsimp [R]; ring
        _ ≤ |-(|h| / 2) * scale |h|| + |c * |h|| + |R |h|| :=
          (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ _ := by
          rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |h| / 2),
            abs_of_nonneg hs, abs_mul, abs_abs]
          nlinarith [hcusp]
    nlinarith [mul_nonneg hr.le hL]
  · have hdif : ||x i - x j - h| - |x i - x j|| ≤ |h| := by
      simpa only [sub_sub_cancel_left, abs_neg] using
        abs_abs_sub_abs_le_abs_sub (x i - x j - h) (x i - x j)
    have hv : |x i - x j| ∈ Icc (g / 2) d := by
      constructor <;> linarith [hgap i hij, hwindow i]
    have hw : |x i - x j - h| ∈ Icc (g / 2) d := by
      constructor <;> linarith [hgap i hij, hwindow i, (abs_le.mp hdif).1, (abs_le.mp hdif).2]
    have hlip := kernel_lipschitz (by linarith : 0 < g / 2) hgd hN hw hv
    have he : |u x j h i| = |K |x i - x j - h| - K |x i - x j|| := by
      simp only [u, Pi.sub_apply, b, column]
      rw [even_abs (x i - x j - h), even_abs (x i - x j)]
    rw [he]
    calc
      _ ≤ L (g / 2) d N * ||x i - x j - h| - |x i - x j|| := hlip
      _ ≤ L (g / 2) d N * |h| := mul_le_mul_of_nonneg_left hdif hL
      _ ≤ _ := by nlinarith [abs_nonneg c]

/-- The actual finite configuration has an explicit quadratic Schur error on a fixed window. -/
theorem near_node_remainder {n : ℕ} (x : Fin n → ℝ) (j : Fin n)
    (hH : (H x).PosDef) {g d : ℝ} {N : ℕ} (hg : 0 < g) (hgd : g / 2 ≤ d)
    (hgap : ∀ i, i ≠ j → g ≤ |x i - x j|)
    (hwindow : ∀ i, |x i - x j| + g / 2 ≤ d) (hN : Real.exp d < N)
    {h : ℝ} (hr : 0 < |h|) (hrhalf : |h| ≤ 1 / 2) (hrg : |h| ≤ g / 2) :
    |S x j h - (|h| * scale |h| - 2 * c * |h|)| ≤
      |h| ^ 2 * (4 + q x * (scale |h| / 2 + |c| + L (g / 2) d N + 2 * |h|) ^ 2) := by
  have hs : 0 ≤ scale |h| := Real.log_nonneg ((one_le_div hr).mpr (by linarith))
  have hL := L_nonneg (a := g / 2) (N := N) (by linarith) hgd
  have hB : 0 ≤ |h| * (scale |h| / 2 + |c| + L (g / 2) d N + 2 * |h|) := by positivity
  have hQ := inverse_quadratic_bound x (u x j h) hB
    (component_bound x j hg hgd hgap hwindow hN hr hrhalf hrg)
  have he : S x j h - (|h| * scale |h| - 2 * c * |h|) =
      -(2 * R |h|) - u x j h ⬝ᵥ ((H x)⁻¹ *ᵥ u x j h) := by
    rw [schur_identity x j hH h, log_scale hr]
    dsimp only [R]
    ring
  rw [he]
  calc
    _ ≤ |2 * R |h|| + |u x j h ⬝ᵥ ((H x)⁻¹ *ᵥ u x j h)| := by
      simpa only [abs_neg] using abs_sub (-(2 * R |h|)) (u x j h ⬝ᵥ ((H x)⁻¹ *ᵥ u x j h))
    _ ≤ 2 * (2 * |h| ^ 2) + q x *
        (|h| * (scale |h| / 2 + |c| + L (g / 2) d N + 2 * |h|)) ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (cusp_remainder_bound hr hrhalf) (by norm_num)) hQ
    _ = _ := by ring

private lemma radius_controls {C ell Q r : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ ell)
    (hQ : 1 ≤ Q) (hr : 0 < r) (hre : r ≤ Real.exp (-4 * (C + ell + 1)))
    (hrq : r ≤ (8 * Q)⁻¹ ^ 2) :
    4 * (C + ell + 1) ≤ scale r ∧ r ≤ 1 / 64 ∧
      r ^ 2 * (4 + Q * (scale r / 2 + C + ell + 2 * r) ^ 2) ≤
        (11 / 128) * (r * scale r) := by
  have hQ0 : 0 < Q := by linarith
  have hs : 4 * (C + ell + 1) ≤ scale r := by
    have hh := Real.log_le_log hr hre
    rw [Real.log_exp] at hh
    rw [log_scale hr]
    linarith
  have hs4 : 4 ≤ scale r := by linarith
  have hden : 8 * Q ≠ 0 := by positivity
  have hmul : r * (8 * Q) ^ 2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hrq (sq_nonneg (8 * Q))
    have he : (8 * Q)⁻¹ ^ 2 * (8 * Q) ^ 2 = 1 := by field_simp
    rwa [he] at hh
  have hr64 : r ≤ 1 / 64 := by
    have hq2 : 1 ≤ Q ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hq2 hr.le
    nlinarith
  have hsqrt := Real.sq_sqrt hr.le
  have hsqrt0 := Real.sqrt_nonneg r
  have hqs : Q * Real.sqrt r ≤ 1 / 8 := by
    have hsq : (Q * Real.sqrt r) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
      calc
        _ = Q ^ 2 * r := by rw [mul_pow, hsqrt]
        _ ≤ _ := by nlinarith [hmul]
    nlinarith [mul_nonneg hQ0.le hsqrt0]
  have he : Real.exp (scale r / 2) ^ 2 = 1 / r := by
    rw [pow_two, ← Real.exp_add, show scale r / 2 + scale r / 2 = scale r by ring]
    exact Real.exp_log (one_div_pos.mpr hr)
  have heprod : Real.exp (scale r / 2) * Real.sqrt r = 1 := by
    have hh : (Real.exp (scale r / 2) * Real.sqrt r) ^ 2 = 1 := by
      rw [mul_pow, he, hsqrt, one_div_mul_cancel hr.ne']
    have hpos : 0 ≤ Real.exp (scale r / 2) * Real.sqrt r :=
      mul_nonneg (Real.exp_nonneg _) hsqrt0
    nlinarith
  have hsexp : scale r ≤ Real.exp (scale r / 2) := by
    have ht : 1 + scale r / 4 ≤ Real.exp (scale r / 4) := by
      linarith [Real.add_one_le_exp (scale r / 4)]
    have hh := mul_le_mul ht ht (by linarith : (0 : ℝ) ≤ 1 + scale r / 4)
      (Real.exp_nonneg _)
    have heq : Real.exp (scale r / 4) * Real.exp (scale r / 4) =
        Real.exp (scale r / 2) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    nlinarith [sq_nonneg (scale r - 4)]
  have hss : scale r * Real.sqrt r ≤ 1 := by
    simpa only [heprod] using mul_le_mul_of_nonneg_right hsexp hsqrt0
  have hqrs : Q * r * scale r ≤ 1 / 8 := by
    calc
      _ = Q * (Real.sqrt r) ^ 2 * scale r := by rw [hsqrt]
      _ = (Q * Real.sqrt r) * (scale r * Real.sqrt r) := by ring
      _ ≤ (1 / 8 : ℝ) * 1 := mul_le_mul hqs hss
        (mul_nonneg (by linarith : (0 : ℝ) ≤ scale r) hsqrt0) (by norm_num)
      _ = _ := by ring
  have hB0 : 0 ≤ scale r / 2 + C + ell + 2 * r := by positivity
  have hB : scale r / 2 + C + ell + 2 * r ≤ 3 * scale r / 4 := by linarith
  have hBsq := mul_le_mul hB hB hB0 (by linarith : (0 : ℝ) ≤ 3 * scale r / 4)
  have hbig : Q * r ^ 2 * (scale r / 2 + C + ell + 2 * r) ^ 2 ≤
      (9 / 128) * (r * scale r) := by
    calc
      _ ≤ Q * r ^ 2 * (3 * scale r / 4) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [pow_two] using hBsq
      _ = (9 / 16) * (Q * r * scale r) * (r * scale r) := by ring
      _ ≤ (9 / 16) * (1 / 8) * (r * scale r) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqrs (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hsmall : 4 * r ^ 2 ≤ (1 / 64) * (r * scale r) := by
    have hh : 4 * r ≤ scale r / 64 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh hr.le]
  exact ⟨hs, hr64, by nlinarith [hbig, hsmall]⟩

/-- The explicit radius makes the actual Schur remainder strictly positive. -/
theorem near_node_positive {n : ℕ} (x : Fin n → ℝ) (j : Fin n)
    (hH : (H x).PosDef) {g d : ℝ} {N : ℕ} (hg : 0 < g) (hgd : g / 2 ≤ d)
    (hgap : ∀ i, i ≠ j → g ≤ |x i - x j|)
    (hwindow : ∀ i, |x i - x j| + g / 2 ≤ d) (hN : Real.exp d < N)
    {h : ℝ} (hr : 0 < |h|) (hrho : |h| ≤ rho x g (L (g / 2) d N)) :
    |h| * scale |h| / 4 ≤ S x j h ∧ 0 < |h| * scale |h| / 4 := by
  have hL := L_nonneg (a := g / 2) (N := N) (by linarith) hgd
  have hrg : |h| ≤ g / 2 := hrho.trans (min_le_left _ _)
  have hre : |h| ≤ Real.exp (-4 * (|c| + L (g / 2) d N + 1)) :=
    hrho.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrq : |h| ≤ (8 * q x)⁻¹ ^ 2 :=
    hrho.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hs, hr64, he⟩ := radius_controls (abs_nonneg c) hL (q_ge_one x) hr hre hrq
  have hrem := near_node_remainder x j hH hg hgd hgap hwindow hN hr (by linarith) hrg
  have hlow := (abs_le.mp hrem).1
  have hcr : 2 * c * |h| ≤ |h| * scale |h| / 2 := by
    have hc : c ≤ |c| := le_abs_self c
    have hh : 2 * c ≤ scale |h| / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh hr.le]
  have hrs : 0 < |h| * scale |h| := mul_pos hr (by linarith [abs_nonneg c])
  exact ⟨by nlinarith [he], by positivity⟩

/-- The augmented matrix is still the literal kernel at all old and new points. -/
def augmented {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (h : ℝ) :
    Matrix (Sum (Fin n) Unit) (Sum (Fin n) Unit) ℝ :=
  fun i k => K (Sum.elim x (fun _ => x j + h) i - Sum.elim x (fun _ => x j + h) k)

private lemma augmented_posDef {n : ℕ} (x : Fin n → ℝ) (j : Fin n)
    (hH : (H x).PosDef) {h : ℝ} (hS : 0 < S x j h) : (augmented x j h).PosDef := by
  letI := hH.isUnit.invertible
  let B : Matrix (Fin n) Unit ℝ := fun i _ => b x j h i
  let D : Matrix Unit Unit ℝ := fun _ _ => firstLiMass
  have hschur : D - Bᴴ * (H x)⁻¹ * B = Matrix.diagonal (fun _ : Unit => S x j h) := by
    rw [Matrix.mul_assoc]
    ext i k
    cases i
    cases k
    simp [B, D, S, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  have hPD : (D - Bᴴ * (H x)⁻¹ * B).PosDef := by
    rw [hschur]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hS)
  have hPSD : (Matrix.fromBlocks (H x) B Bᴴ D).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hH).mpr hPD.posSemidef
  have hunit : IsUnit (Matrix.fromBlocks (H x) B Bᴴ D) := by
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
    rw [Matrix.invOf_eq_nonsing_inv]
    exact hPD.isUnit
  have hp := hPSD.posDef_iff_isUnit.mpr hunit
  have he : augmented x j h = Matrix.fromBlocks (H x) B Bᴴ D := by
    ext i k
    cases i with
    | inl i =>
      cases k with
      | inl k => rfl
      | inr k => simp [augmented, B, b, sub_add_eq_sub_sub]
    | inr i =>
      cases k with
      | inl k =>
        simp only [augmented, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply,
          star_trivial, B, b]
        rw [even_abs, even_abs (x k - x j - h)]
        congr 1
        exact abs_eq_abs.mpr (Or.inr (by ring))
      | inr k => simp [augmented, D, K_zero]
  rwa [he]

private lemma finite_window {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (j : Fin n) :
    ∃ g d : ℝ, ∃ N : ℕ, 0 < g ∧ g / 2 ≤ d ∧
      (∀ i, i ≠ j → g ≤ |x i - x j|) ∧
      (∀ i, |x i - x j| + g / 2 ≤ d) ∧ Real.exp d < N := by
  classical
  let f : Fin n → ℝ := fun i => if i = j then 1 else |x i - x j|
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  let g := Finset.univ.inf' hne f / 2
  have hf (i : Fin n) : 0 < f i := by
    dsimp only [f]
    split_ifs with hij
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hij (hx h)))
  have hinf : 0 < Finset.univ.inf' hne f := Finset.lt_inf'_iff.mpr (fun i _ => hf i)
  have hg : 0 < g := half_pos hinf
  let d := g + ∑ i, |x i - x j|
  have hsum : 0 ≤ ∑ i, |x i - x j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let N : ℕ := ⌈Real.exp d⌉₊ + 1
  refine ⟨g, d, N, hg, ?_, ?_, ?_, ?_⟩
  · dsimp [d]; linarith
  · intro i hij
    have hh := Finset.inf'_le f (Finset.mem_univ i)
    have hfval : f i = |x i - x j| := if_neg hij
    rw [hfval] at hh
    dsimp [g]
    linarith
  · intro i
    have hh : |x i - x j| ≤ ∑ k, |x k - x j| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (x k - x j)) (Finset.mem_univ i)
    dsimp [d]
    linarith
  · have hh := Nat.le_ceil (Real.exp d)
    dsimp only [N]
    push_cast
    linarith

/-- Every injective actual positive definite configuration admits a constructive positive radius.
The displayed radius retains its arithmetic window and inverse-matrix conditioning. -/
theorem explicit_near_node_posDef {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (j : Fin n) (hH : (H x).PosDef) :
    ∃ g d : ℝ, ∃ N : ℕ, 0 < g ∧ g / 2 ≤ d ∧
      (∀ i, i ≠ j → g ≤ |x i - x j|) ∧
      (∀ i, |x i - x j| + g / 2 ≤ d) ∧ Real.exp d < N ∧
      0 < rho x g (L (g / 2) d N) ∧
      ∀ h : ℝ, 0 < |h| → |h| ≤ rho x g (L (g / 2) d N) →
        (|h| * scale |h| / 4 ≤ S x j h ∧ 0 < |h| * scale |h| / 4) ∧
        (augmented x j h).PosDef := by
  obtain ⟨g, d, N, hg, hgd, hgap, hwindow, hN⟩ := finite_window x hx j
  have hq : 0 < q x := by linarith [q_ge_one x]
  have hrho : 0 < rho x g (L (g / 2) d N) := by
    dsimp [rho]
    exact lt_min (by linarith) (lt_min (Real.exp_pos _) (sq_pos_of_pos (by positivity)))
  refine ⟨g, d, N, hg, hgd, hgap, hwindow, hN, hrho, ?_⟩
  intro h hr hrh
  have hp := near_node_positive x j hH hg hgd hgap hwindow hN hr hrh
  exact ⟨hp, augmented_posDef x j hH (hp.2.trans_le hp.1)⟩

#print axioms near_node_remainder
#print axioms near_node_positive
#print axioms explicit_near_node_posDef

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
