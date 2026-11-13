/- GID: D5/S3/Quantum/Approximate/FiniteStarNewton
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/FiniteStarNewton
   mirror-E: none(waiver:analytic-correction)
   anchors: []
   utility: none
   digest: Finite contractive diagonals give star-preserving Newton corrections. -/

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-! # A finite-diagonal Newton correction

The source and target are associative complex C-star algebras. A contractive
algebraic diagonal supplies the averaging identity. Only the multiplicative
defect contracts; no contraction of the map-valued Newton operator is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct
open Filter Topology

namespace D5.S3.Quantum.Approximate

variable {B A J : Type*} [CStarAlgebra B] [CStarAlgebra A] [Fintype J]

/-- An explicitly finite diagonal, with its projective norm budget. -/
structure FiniteDiagonal (B J : Type*) [CStarAlgebra B] [Fintype J] where
  left : J → B
  right : J → B
  product : ∑ j, left j * right j = 1
  central (x : B) :
    ∑ j, (x * left j) ⊗ₜ[ℂ] right j = ∑ j, left j ⊗ₜ[ℂ] (right j * x)
  budget : ∑ j, ‖left j‖ * ‖right j‖ ≤ 1

/-- The actual all-input multiplicative defect. -/
def defect (u : B →L[ℂ] A) (x y : B) : A := u (x * y) - u x * u y

/-- A uniform bound on the bilinear defect. -/
def DefectBound (u : B →L[ℂ] A) (r : ℝ) : Prop :=
  ∀ x y, ‖defect u x y‖ ≤ r * ‖x‖ * ‖y‖

/-- Exact star preservation, without a multiplicativity assumption. -/
def PreservesStar (u : B →L[ℂ] A) : Prop := ∀ x, u (star x) = star (u x)

private lemma initial_norm_bound (u : B →L[ℂ] A) {d : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 32) (hs : PreservesStar u)
    (hg : DefectBound u d) : ‖u‖ ≤ 3 / 2 := by
  have hp (x : B) : ‖u x‖ ^ 2 ≤ (‖u‖ + d) * ‖x‖ ^ 2 := by
    have ht := norm_sub_le (u (star x * x)) (defect u (star x) x)
    have he : u (star x * x) - defect u (star x) x = star (u x) * u x := by
      simp [defect, hs x]
    rw [he, CStarRing.norm_star_mul_self] at ht
    have h := hg (star x) x
    rw [norm_star] at h
    have h' := u.le_opNorm (star x * x)
    rw [CStarRing.norm_star_mul_self] at h'
    nlinarith
  have hn : ‖u‖ ≤ Real.sqrt (‖u‖ + d) := by
    apply u.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa [mul_pow, Real.sq_sqrt (add_nonneg (norm_nonneg u) hd)] using hp x
  have hq := Real.sq_sqrt (add_nonneg (norm_nonneg u) hd)
  have hsq : ‖u‖ ^ 2 ≤ (Real.sqrt (‖u‖ + d)) ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hn
  nlinarith [norm_nonneg u]

/-- The unsymmetrized finite-diagonal correction, as a continuous linear map. -/
def rawCorrection (D : FiniteDiagonal B J) (u : B →L[ℂ] A) : B →L[ℂ] A :=
  ∑ j, ((ContinuousLinearMap.mul ℂ A) (u (D.left j))).comp
    (u.comp ((ContinuousLinearMap.mul ℂ B) (D.right j)) -
      ((ContinuousLinearMap.mul ℂ A) (u (D.right j))).comp u)

private lemma raw_apply (D : FiniteDiagonal B J) (u : B →L[ℂ] A) (x : B) :
    rawCorrection D u x = ∑ j, u (D.left j) * defect u (D.right j) x := by
  simp [rawCorrection, defect, mul_sub, Finset.sum_sub_distrib]

/-- Reflection by the source and target involutions is complex-linear. -/
def starReflect (w : B →L[ℂ] A) : B →L[ℂ] A :=
  (starL ℂ : A ≃L⋆[ℂ] A).toContinuousLinearMap.comp
    (w.comp (starL ℂ : B ≃L⋆[ℂ] B).toContinuousLinearMap)

private lemma reflect_apply (w : B →L[ℂ] A) (x : B) :
    starReflect w x = star (w (star x)) := rfl

/-- The correction is symmetrized before each step, so star is exact at every iterate. -/
def correction (D : FiniteDiagonal B J) (u : B →L[ℂ] A) : B →L[ℂ] A :=
  (1 / 2 : ℝ) • (rawCorrection D u + starReflect (rawCorrection D u))

private lemma correction_star (D : FiniteDiagonal B J) (u : B →L[ℂ] A) :
    PreservesStar (correction D u) := by
  intro x
  simp [correction, reflect_apply, star_smul, star_add, add_comm]

private lemma raw_norm (D : FiniteDiagonal B J) (u : B →L[ℂ] A)
    {r : ℝ} (hr : 0 ≤ r) (hg : DefectBound u r) :
    ‖rawCorrection D u‖ ≤ ‖u‖ * r := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hr)
  intro x
  rw [raw_apply]
  calc
    ‖∑ j, u (D.left j) * defect u (D.right j) x‖ ≤
        ∑ j, ‖u (D.left j) * defect u (D.right j) x‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖u‖ * r * ‖x‖) * (‖D.left j‖ * ‖D.right j‖) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖u (D.left j)‖ * ‖defect u (D.right j) x‖ := norm_mul_le _ _
        _ ≤ (‖u‖ * ‖D.left j‖) * (r * ‖D.right j‖ * ‖x‖) := by
          gcongr
          exact u.le_opNorm _
          exact hg _ _
        _ = _ := by ring
    _ = (‖u‖ * r * ‖x‖) * ∑ j, ‖D.left j‖ * ‖D.right j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖u‖ * r * ‖x‖ := by
      simpa using mul_le_mul_of_nonneg_left D.budget (by positivity : 0 ≤ ‖u‖ * r * ‖x‖)

private lemma correction_norm (D : FiniteDiagonal B J) (u : B →L[ℂ] A)
    {r : ℝ} (hr : 0 ≤ r) (hg : DefectBound u r) :
    ‖correction D u‖ ≤ ‖u‖ * r := by
  have hb := raw_norm D u hr hg
  have hb' : ‖starReflect (rawCorrection D u)‖ ≤ ‖u‖ * r := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    simpa [reflect_apply] using (rawCorrection D u).le_of_opNorm_le hb (star x)
  calc
    ‖correction D u‖ = (1 / 2 : ℝ) * ‖rawCorrection D u + starReflect (rawCorrection D u)‖ := by
      rw [correction, norm_smul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖rawCorrection D u‖ + ‖starReflect (rawCorrection D u)‖) := by
      gcongr; exact norm_add_le _ _
    _ ≤ ‖u‖ * r := by linarith

private lemma transport (D : FiniteDiagonal B J) (p : B →ₗ[ℂ] B →ₗ[ℂ] A) (x : B) :
    ∑ j, p (x * D.left j) (D.right j) = ∑ j, p (D.left j) (D.right j * x) := by
  have h := congrArg (TensorProduct.lift p) (D.central x)
  simpa only [map_sum, TensorProduct.lift.tmul] using h

/-- The linearized multiplicativity operator. -/
def linearized (u w : B →L[ℂ] A) (x y : B) : A :=
  u x * w y - w (x * y) + w x * u y

private lemma raw_identity (D : FiniteDiagonal B J) (u : B →L[ℂ] A) (x y : B) :
    linearized u (rawCorrection D u) x y =
      (u 1 - ∑ j, defect u (D.left j) (D.right j)) * defect u x y -
        ∑ j, defect u x (D.left j) * defect u (D.right j) y := by
  let p : B →ₗ[ℂ] B →ₗ[ℂ] A := LinearMap.mk₂ ℂ
    (fun a b => u a * defect u b y)
    (by intros; simp [map_add, add_mul])
    (by intros; simp [map_smul, smul_mul_assoc])
    (by intros; simp [defect, add_mul, map_add, mul_add]; noncomm_ring)
    (by intros; simp only [defect, smul_mul_assoc, map_smul, mul_smul_comm, RingHom.id_apply, ← smul_sub])
  have ht := transport D p x
  change (∑ j, u (x * D.left j) * defect u (D.right j) y) =
    ∑ j, u (D.left j) * defect u (D.right j * x) y at ht
  have hsum : ∑ j, u (D.left j) * u (D.right j) =
      u 1 - ∑ j, defect u (D.left j) (D.right j) := by
    simp only [defect, Finset.sum_sub_distrib, ← map_sum, D.product]
    abel
  simp only [linearized, raw_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have he (a b : B) :
      u x * (u a * defect u b y) - u a * defect u b (x * y) +
        (u a * defect u b x) * u y -
        (u a * u b * defect u x y - defect u x a * defect u b y) =
      u (x * a) * defect u b y - u a * defect u (b * x) y := by
    simp only [defect, mul_assoc]
    noncomm_ring
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ht, sub_self]

private lemma raw_residual (D : FiniteDiagonal B J) (u : B →L[ℂ] A)
    {r : ℝ} (hr : 0 ≤ r) (hg : DefectBound u r) (x y : B) :
    ‖defect u x y - linearized u (rawCorrection D u) x y‖ ≤
      (‖u 1 - 1‖ * r + 2 * r ^ 2) * ‖x‖ * ‖y‖ := by
  have hsum : ‖∑ j, defect u (D.left j) (D.right j)‖ ≤ r := by
    calc
      _ ≤ ∑ j, ‖defect u (D.left j) (D.right j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, r * (‖D.left j‖ * ‖D.right j‖) := by
        apply Finset.sum_le_sum; intro j _; convert hg (D.left j) (D.right j) using 1 <;> ring
      _ ≤ r := by simpa [← Finset.mul_sum] using mul_le_mul_of_nonneg_left D.budget hr
  have hp : ‖∑ j, defect u x (D.left j) * defect u (D.right j) y‖ ≤
      r ^ 2 * ‖x‖ * ‖y‖ := by
    calc
      _ ≤ ∑ j, ‖defect u x (D.left j) * defect u (D.right j) y‖ := norm_sum_le _ _
      _ ≤ ∑ j, (r ^ 2 * ‖x‖ * ‖y‖) * (‖D.left j‖ * ‖D.right j‖) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ‖defect u x (D.left j)‖ * ‖defect u (D.right j) y‖ := norm_mul_le _ _
          _ ≤ (r * ‖x‖ * ‖D.left j‖) * (r * ‖D.right j‖ * ‖y‖) := by
            gcongr <;> exact hg _ _
          _ = _ := by ring
      _ ≤ r ^ 2 * ‖x‖ * ‖y‖ := by
        simpa [← Finset.mul_sum] using
          mul_le_mul_of_nonneg_left D.budget (by positivity : 0 ≤ r ^ 2 * ‖x‖ * ‖y‖)
  rw [raw_identity]
  have he : defect u x y -
      ((u 1 - ∑ j, defect u (D.left j) (D.right j)) * defect u x y -
        ∑ j, defect u x (D.left j) * defect u (D.right j) y) =
      (1 - u 1 + ∑ j, defect u (D.left j) (D.right j)) * defect u x y +
        ∑ j, defect u x (D.left j) * defect u (D.right j) y := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(1 - u 1 + ∑ j, defect u (D.left j) (D.right j)) * defect u x y‖ +
        ‖∑ j, defect u x (D.left j) * defect u (D.right j) y‖ := norm_add_le _ _
    _ ≤ (‖u 1 - 1‖ + r) * (r * ‖x‖ * ‖y‖) + r ^ 2 * ‖x‖ * ‖y‖ := by
      gcongr
      · calc
          _ ≤ ‖1 - u 1 + ∑ j, defect u (D.left j) (D.right j)‖ * ‖defect u x y‖ := norm_mul_le _ _
          _ ≤ (‖u 1 - 1‖ + r) * (r * ‖x‖ * ‖y‖) := by
            gcongr
            · exact (norm_add_le _ _).trans (add_le_add (by rw [norm_sub_rev]) hsum)
            · exact hg _ _
    _ = _ := by ring

private lemma reflect_residual (u w : B →L[ℂ] A) (hs : PreservesStar u) (x y : B) :
    defect u x y - linearized u (starReflect w) x y =
      star (defect u (star y) (star x) - linearized u w (star y) (star x)) := by
  have hs' : ∀ a, star (u (star a)) = u a := fun a => by rw [hs a, star_star]
  have hxy : star y * star x = star (x * y) := (star_mul x y).symm
  simp only [defect, linearized, reflect_apply, star_sub, star_add, star_mul]
  rw [hxy, hs' (x * y), hs' x, hs' y]
  abel

private lemma correction_residual (D : FiniteDiagonal B J) (u : B →L[ℂ] A)
    {r : ℝ} (hr : 0 ≤ r) (hs : PreservesStar u) (hg : DefectBound u r) (x y : B) :
    ‖defect u x y - linearized u (correction D u) x y‖ ≤
      (‖u 1 - 1‖ * r + 2 * r ^ 2) * ‖x‖ * ‖y‖ := by
  have h := raw_residual D u hr hg x y
  have h' : ‖defect u x y - linearized u (starReflect (rawCorrection D u)) x y‖ ≤
      (‖u 1 - 1‖ * r + 2 * r ^ 2) * ‖x‖ * ‖y‖ := by
    rw [reflect_residual u _ hs, norm_star]
    simpa [norm_star, mul_right_comm] using raw_residual D u hr hg (star y) (star x)
  have he : defect u x y - linearized u (correction D u) x y =
      (1 / 2 : ℝ) • ((defect u x y - linearized u (rawCorrection D u) x y) +
        (defect u x y - linearized u (starReflect (rawCorrection D u)) x y)) := by
    simp only [correction, linearized, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
    module
  rw [he, norm_smul]
  have hn := norm_add_le
    (defect u x y - linearized u (rawCorrection D u) x y)
    (defect u x y - linearized u (starReflect (rawCorrection D u)) x y)
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

private lemma unit_error_bound [NormOneClass B] (u : B →L[ℂ] A)
    {r : ℝ} (hg : DefectBound u r) (hu : ‖u 1 - 1‖ < 1 / 2) : ‖u 1 - 1‖ ≤ 2 * r := by
  have he : u 1 - 1 = -defect u 1 1 - (u 1 - 1) * (u 1 - 1) := by
    simp only [defect, one_mul]; noncomm_ring
  have hn := norm_sub_le (-defect u 1 1) ((u 1 - 1) * (u 1 - 1))
  rw [← he, norm_neg] at hn
  have hg' := hg 1 1
  simp only [norm_one, mul_one] at hg'
  have hm := norm_mul_le (u 1 - 1) (u 1 - 1)
  nlinarith [norm_nonneg (u 1 - 1)]

/-- One prescribed Newton step. -/
def newton (D : FiniteDiagonal B J) (u : B →L[ℂ] A) : B →L[ℂ] A := u + correction D u

private lemma newton_defect [NormOneClass B] (D : FiniteDiagonal B J) (u : B →L[ℂ] A)
    {r : ℝ} (hr : 0 ≤ r) (hs : PreservesStar u) (hg : DefectBound u r)
    (hn : ‖u‖ ≤ 2) (hu : ‖u 1 - 1‖ < 1 / 2) :
    DefectBound (newton D u) (8 * r ^ 2) := by
  have hs' := unit_error_bound u hg hu
  have hw := correction_norm D u hr hg
  have hw' : ‖correction D u‖ ≤ 2 * r := hw.trans (mul_le_mul_of_nonneg_right hn hr)
  intro x y
  have he : defect (newton D u) x y =
      (defect u x y - linearized u (correction D u) x y) -
        correction D u x * correction D u y := by
    simp only [defect, newton, linearized, ContinuousLinearMap.add_apply]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖defect u x y - linearized u (correction D u) x y‖ +
        ‖correction D u x * correction D u y‖ := norm_sub_le _ _
    _ ≤ (‖u 1 - 1‖ * r + 2 * r ^ 2) * ‖x‖ * ‖y‖ +
        (2 * r * ‖x‖) * (2 * r * ‖y‖) := by
      apply add_le_add (correction_residual D u hr hs hg x y)
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((correction D u).le_of_opNorm_le hw' x)
        ((correction D u).le_of_opNorm_le hw' y) (norm_nonneg _) (by positivity))
    _ ≤ 8 * r ^ 2 * ‖x‖ * ‖y‖ := by
      have h := mul_le_mul_of_nonneg_right hs' hr
      have h' : ‖u 1 - 1‖ * r + 2 * r ^ 2 ≤ 4 * r ^ 2 := by nlinarith
      calc
        _ ≤ (4 * r ^ 2) * ‖x‖ * ‖y‖ + (2 * r * ‖x‖) * (2 * r * ‖y‖) := by gcongr
        _ = _ := by ring

/-- The numerical radius obeys the quadratic recursion exactly. -/
def newtonRadius (d : ℝ) : ℕ → ℝ
  | 0 => d
  | k + 1 => 8 * newtonRadius d k ^ 2

/-- The actual star-preserving orbit in the complete operator-norm space. -/
def newtonOrbit (D : FiniteDiagonal B J) (f : B →L[ℂ] A) : ℕ → B →L[ℂ] A
  | 0 => f
  | k + 1 => newton D (newtonOrbit D f k)

private lemma orbit_neighborhood [NormOneClass B] (f u : B →L[ℂ] A)
    {d : ℝ} (hd : d ≤ 1 / 32) (hf : ‖f‖ ≤ 3 / 2)
    (hunit : ‖f 1 - 1‖ ≤ 1 / 4) (hclose : ‖u - f‖ ≤ 8 * d / 3) :
    ‖u‖ ≤ 2 ∧ ‖u 1 - 1‖ < 1 / 2 := by
  have hn : ‖u‖ ≤ ‖u - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (u - f) f
  have hu : ‖u 1 - 1‖ ≤ ‖u - f‖ + ‖f 1 - 1‖ := by
    have he : u 1 - 1 = (u - f) 1 + (f 1 - 1) := by simp
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (by simpa using (u - f).le_opNorm 1) le_rfl)
  constructor <;> linarith

private lemma orbit_invariant [NormOneClass B] (D : FiniteDiagonal B J)
    (f : B →L[ℂ] A) {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 32)
    (hs : PreservesStar f) (hg : DefectBound f d) (hu : ‖f 1 - 1‖ ≤ 1 / 4) (k : ℕ) :
    PreservesStar (newtonOrbit D f k) ∧
      0 ≤ newtonRadius d k ∧
      newtonRadius d k ≤ d * (1 / 4 : ℝ) ^ k ∧
      DefectBound (newtonOrbit D f k) (newtonRadius d k) ∧
      ‖newtonOrbit D f k - f‖ ≤ 8 * d / 3 * (1 - (1 / 4 : ℝ) ^ k) := by
  have hf := initial_norm_bound f hd hd' hs hg
  induction k with
  | zero =>
    simpa [newtonOrbit, newtonRadius] using
      (show PreservesStar f ∧ 0 ≤ d ∧ DefectBound f d from ⟨hs, hd, hg⟩)
  | succ k ih =>
    obtain ⟨hsn, hr, hrg, hgn, hclose⟩ := ih
    have hq0 : 0 ≤ (1 / 4 : ℝ) ^ k := by positivity
    have hq1 : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hc : ‖newtonOrbit D f k - f‖ ≤ 8 * d / 3 :=
      hclose.trans (by nlinarith)
    obtain ⟨hn, hun⟩ := orbit_neighborhood f (newtonOrbit D f k) hd' hf hu hc
    have hrd : newtonRadius d k ≤ d := hrg.trans (by nlinarith)
    have hquad : 8 * newtonRadius d k ^ 2 ≤ newtonRadius d k / 4 := by
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hrd)]
    have hw := correction_norm D (newtonOrbit D f k) hr hgn
    have hw' : ‖correction D (newtonOrbit D f k)‖ ≤ 2 * newtonRadius d k :=
      hw.trans (mul_le_mul_of_nonneg_right hn hr)
    refine ⟨?_, by simp only [newtonRadius]; positivity, ?_, ?_, ?_⟩
    · intro x
      change newtonOrbit D f k (star x) + correction D (newtonOrbit D f k) (star x) =
        star (newtonOrbit D f k x + correction D (newtonOrbit D f k) x)
      rw [hsn x, correction_star D _ x, star_add]
    · change 8 * newtonRadius d k ^ 2 ≤ d * (1 / 4 : ℝ) ^ (k + 1)
      rw [pow_succ (1 / 4 : ℝ) k]
      nlinarith
    · exact newton_defect D (newtonOrbit D f k) hr hsn hgn hn hun
    · have he : newtonOrbit D f (k + 1) - f =
          (newtonOrbit D f k - f) + correction D (newtonOrbit D f k) := by
        simp only [newtonOrbit, newton]; abel
      rw [he]
      calc
        _ ≤ ‖newtonOrbit D f k - f‖ + ‖correction D (newtonOrbit D f k)‖ := norm_add_le _ _
        _ ≤ 8 * d / 3 * (1 - (1 / 4 : ℝ) ^ k) + 2 * (d * (1 / 4 : ℝ) ^ k) := by
          linarith
        _ = _ := by rw [pow_succ (1 / 4 : ℝ) k]; ring

/-- A dimension-free exact unital star-algebra homomorphism is constructed from
an all-input small multiplicative defect and an exact star law. -/
theorem exists_star_hom_close [Nontrivial B] [Nontrivial A]
    (D : FiniteDiagonal B J) (f : B →L[ℂ] A) {d : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 32) (hs : PreservesStar f)
    (hg : DefectBound f d) (hu : ‖f 1 - 1‖ ≤ 1 / 4) :
    ∃ ρ : B →⋆ₐ[ℂ] A, ∀ x, ‖ρ x - f x‖ ≤ (8 * d / 3) * ‖x‖ := by
  have hi := orbit_invariant D f hd hd' hs hg hu
  have hstep (k : ℕ) : dist (newtonOrbit D f k) (newtonOrbit D f (k + 1)) ≤
      (2 * d) * (1 / 4 : ℝ) ^ k := by
    obtain ⟨hsk, hr, hrg, hgk, hc⟩ := hi k
    have hc' : ‖newtonOrbit D f k - f‖ ≤ 8 * d / 3 := hc.trans (by
      have : 0 ≤ (1 / 4 : ℝ) ^ k := by positivity
      nlinarith)
    have hn := (orbit_neighborhood f _ hd' (initial_norm_bound f hd hd' hs hg) hu hc').1
    rw [dist_comm, dist_eq_norm]
    change ‖newtonOrbit D f k + correction D (newtonOrbit D f k) - newtonOrbit D f k‖ ≤ _
    rw [add_sub_cancel_left]
    exact (correction_norm D _ hr hgk).trans (by nlinarith)
  obtain ⟨ρ, hρ⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 4 : ℝ) (2 * d) (by norm_num) hstep)
  have hclose : ‖ρ - f‖ ≤ 8 * d / 3 := by
    have h := dist_le_of_le_geometric_of_tendsto₀ (1 / 4 : ℝ) (2 * d)
      (by norm_num) hstep hρ
    rw [newtonOrbit, dist_eq_norm, norm_sub_rev] at h
    exact h.trans_eq (by ring)
  have heval (x : B) : Tendsto (fun k => newtonOrbit D f k x) atTop (𝓝 (ρ x)) :=
    ((ContinuousLinearMap.apply ℂ A x).continuous.tendsto ρ).comp hρ
  have hmul (x y : B) : ρ (x * y) = ρ x * ρ y := by
    have hzero : Tendsto (fun k => defect (newtonOrbit D f k) x y) atTop (𝓝 0) := by
      have hb (k : ℕ) : ‖defect (newtonOrbit D f k) x y‖ ≤
          (d * (1 / 4 : ℝ) ^ k) * ‖x‖ * ‖y‖ := by
        exact ((hi k).2.2.2.1 x y).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hi k).2.2.1 (norm_nonneg _)) (norm_nonneg _))
      apply squeeze_zero_norm hb
      have ht : Tendsto (fun k : ℕ => (1 / 4 : ℝ) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using ((tendsto_const_nhds.mul ht).mul_const ‖x‖).mul_const ‖y‖
    have hl : Tendsto (fun k => defect (newtonOrbit D f k) x y) atTop
        (𝓝 (ρ (x * y) - ρ x * ρ y)) :=
      (heval (x * y)).sub ((heval x).mul (heval y))
    exact sub_eq_zero.mp (tendsto_nhds_unique hl hzero)
  have hstar : PreservesStar ρ := by
    intro x
    have h := (heval x).star
    have h' := heval (star x)
    have he : (fun k => newtonOrbit D f k (star x)) =
        (fun k => star (newtonOrbit D f k x)) := funext (fun k => (hi k).1 x)
    rw [he] at h'
    exact tendsto_nhds_unique h' h
  have hunit : ρ 1 = 1 := by
    have hn := (orbit_neighborhood f ρ hd' (initial_norm_bound f hd hd' hs hg) hu hclose).2
    have hid : (ρ 1 - 1) * (ρ 1 - 1) = -(ρ 1 - 1) := by
      have hm := hmul 1 1
      simp only [one_mul] at hm
      noncomm_ring [← hm]
    have hnorm := norm_mul_le (ρ 1 - 1) (ρ 1 - 1)
    rw [hid, norm_neg] at hnorm
    have hz : ‖ρ 1 - 1‖ = 0 := by nlinarith [norm_nonneg (ρ 1 - 1)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  let ρhom : B →⋆ₐ[ℂ] A := {
    toFun := ρ
    map_one' := hunit
    map_mul' := hmul
    map_zero' := map_zero ρ
    map_add' := map_add ρ
    commutes' := fun c => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hunit, Algebra.algebraMap_eq_smul_one]
    map_star' := hstar }
  refine ⟨ρhom, fun x => ?_⟩
  exact (ρ - f).le_of_opNorm_le hclose x

end D5.S3.Quantum.Approximate
