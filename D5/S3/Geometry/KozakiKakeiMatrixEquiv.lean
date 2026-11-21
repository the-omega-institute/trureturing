/- GID: D5/S3/Geometry/KozakiKakeiMatrixEquiv
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiMatrixEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invertible row multiplication and diagonal column scaling preserve the level equation and commute with reordering. -/
import D5.S3.Geometry.KozakiKakeiPreservation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.BigOperators

namespace D5.S3.Geometry.KozakiKakei
open scoped BigOperators
noncomputable section

abbrev Square := Matrix (Fin 2) (Fin 2) K

def scaled {m : ℕ} (L : Square) (d : Col m → K) (Z : Chart K m) : Chart K m :=
  (L * Z) * Matrix.diagonal d

theorem scaled_apply {m : ℕ} (L : Square) (d : Col m → K) (Z : Chart K m)
    (a : Fin 2) (i : Col m) :
    scaled L d Z a i = (L a 0 * Z 0 i + L a 1 * Z 1 i) * d i := by
  rw [scaled, Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem minor_scaled {m : ℕ} (L : Square) (d : Col m → K) (Z : Chart K m) (i j : Col m) :
    minor (scaled L d Z) i j = L.det * d i * d j * minor Z i j := by
  simp only [minor, scaled_apply, Matrix.det_fin_two]
  ring

theorem scaled_admissible {m : ℕ} {L : Square} (hL : L.det ≠ 0)
    {d : Col m → K} (hd : ∀ i, d i ≠ 0) {Z : Chart K m} (hZ : Admissible Z) :
    Admissible (scaled L d Z) := by
  intro i j hij
  rw [minor_scaled]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hL (hd i)) (hd j)) (hZ i j hij)

theorem unit_det_ne_zero (L : Squareˣ) : L.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp L.isUnit).ne_zero

private theorem prod_pair_scales {m : ℕ} (M : Fin m × Bool ≃ Col m) (d : Col m → K) :
    (∏ e : Fin m, d (M (e, false)) * d (M (e, true))) = ∏ i : Col m, d i := by
  calc
    _ = ∏ q : Fin m × Bool, d (M q) := by
      rw [Fintype.prod_prod_type]
      simp only [Fintype.prod_bool, mul_comm]
    _ = _ := Fintype.prod_equiv M _ _ (fun _ => rfl)

private theorem product_scaled {m : ℕ} (M : Fin m × Bool ≃ Col m)
    (L : Square) (d : Col m → K) (Z : Chart K m) :
    (∏ e : Fin m, minor (scaled L d Z) (M (e, false)) (M (e, true))) =
      (L.det ^ m * ∏ i : Col m, d i) *
        ∏ e : Fin m, minor Z (M (e, false)) (M (e, true)) := by
  simp only [minor_scaled]
  have factor (e : Fin m) :
      L.det * d (M (e, false)) * d (M (e, true)) * minor Z (M (e, false)) (M (e, true)) =
      (L.det * (d (M (e, false)) * d (M (e, true)))) *
        minor Z (M (e, false)) (M (e, true)) := by ac_rfl
  simp_rw [factor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, prod_pair_scales]

theorem level_scaled_iff {m : ℕ} {L : Square} (hL : L.det ≠ 0)
    {d : Col m → K} (hd : ∀ i, d i ≠ 0) (Z : Chart K m) :
    evenProduct (scaled L d Z) = oddProduct (scaled L d Z) ↔ evenProduct Z = oddProduct Z := by
  change (∏ e : Fin m, minor (scaled L d Z) ((evenMatching m) (e, false)) ((evenMatching m) (e, true))) =
      (∏ e : Fin m, minor (scaled L d Z) ((oddMatching m) (e, false)) ((oddMatching m) (e, true))) ↔ _
  rw [product_scaled, product_scaled]
  have h : L.det ^ m * ∏ i : Col m, d i ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  exact ⟨mul_left_cancel₀ h, congrArg (_ * ·)⟩

theorem scaled_comp {m : ℕ} (L₁ L₂ : Square) (d₁ d₂ : Col m → K) (Z : Chart K m) :
    scaled L₁ d₁ (scaled L₂ d₂ Z) = scaled (L₁ * L₂) (fun i => d₂ i * d₁ i) Z := by
  simp only [scaled, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

theorem matEquivalent_symm {m : ℕ} {Z W : Chart K m} (h : MatEquivalent W Z) :
    MatEquivalent Z W := by
  obtain ⟨L, d, h⟩ := h
  change W = scaled L.val (fun i => (d i).val) Z at h
  refine ⟨L⁻¹, fun i => (d i)⁻¹, ?_⟩
  change Z = scaled (L⁻¹).val (fun i => ((d i)⁻¹).val) W
  rw [h, scaled_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [scaled, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.diagonal_one,
    Matrix.one_mul, Matrix.mul_one]

theorem matEquivalent_trans {m : ℕ} {X Y Z : Chart K m}
    (h₁ : MatEquivalent X Y) (h₂ : MatEquivalent Y Z) : MatEquivalent X Z := by
  obtain ⟨L₁, d₁, h₁⟩ := h₁
  obtain ⟨L₂, d₂, h₂⟩ := h₂
  change X = scaled L₁.val (fun i => (d₁ i).val) Y at h₁
  change Y = scaled L₂.val (fun i => (d₂ i).val) Z at h₂
  refine ⟨L₁ * L₂, fun i => d₂ i * d₁ i, ?_⟩
  change X = scaled (L₁ * L₂).val (fun i => (d₂ i * d₁ i).val) Z
  rw [h₁, h₂, scaled_comp]
  rfl

theorem reorder_equiv {m : ℕ} {Z W : Chart K m} (σ : Equiv.Perm (Col m))
    (h : MatEquivalent W Z) : MatEquivalent (reorder σ W) (reorder σ Z) := by
  obtain ⟨L, d, h⟩ := h
  change W = scaled L.val (fun i => (d i).val) Z at h
  refine ⟨L, fun i => d (σ i), ?_⟩
  change reorder σ W = scaled L.val (fun i => (d (σ i)).val) (reorder σ Z)
  rw [h]
  ext a i
  change scaled L.val (fun j => (d j).val) Z a (σ i) = _
  simp [scaled_apply, reorder]

theorem reorder_admissible {m : ℕ} {Z : Chart K m} (σ : Equiv.Perm (Col m))
    (h : Admissible Z) : Admissible (reorder σ Z) := by
  intro i j hij
  exact h (σ i) (σ j) (σ.injective.ne hij)

theorem level_equiv {m : ℕ} {Z W : Chart K m} (h : MatEquivalent W Z) :
    evenProduct W = oddProduct W ↔ evenProduct Z = oddProduct Z := by
  obtain ⟨L, d, h⟩ := h
  change W = scaled L.val (fun i => (d i).val) Z at h
  rw [h]
  exact level_scaled_iff (unit_det_ne_zero L) (fun i => (d i).ne_zero) Z

end
end D5.S3.Geometry.KozakiKakei
