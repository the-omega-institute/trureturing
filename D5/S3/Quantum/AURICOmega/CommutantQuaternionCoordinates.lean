/- GID: D5/S3/Quantum/AURICOmega/CommutantQuaternionCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/CommutantQuaternionCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quaternionic coordinates from a noncommutative commutant in dimension at most four. -/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Quaternion

/-! Quaternionic coordinates from a noncommutative commutant.

Let `𝒰` be a set of linear isometries acting irreducibly on a real inner product space `E` of
dimension at most four, and let `𝒱` be a set of linear isometries containing two noncommuting
elements and commuting elementwise with `𝒰`. Then `E` is four-dimensional, and every unit
vector `e` is the unit `1` of quaternionic coordinates on `E` in which `𝒱` acts by left and `𝒰`
by right multiplication by unit quaternions.

Outline. A symmetric operator commuting with `𝒰` has an eigenspace invariant under `𝒰`, so it
is a scalar. Hence every element of `𝒱` is a scalar plus a skew operator commuting with `𝒰`,
anticommutators of such skew operators are scalars, and two noncommuting elements of `𝒱`
yield, after normalization and orthogonalization, two anticommuting complex structures `J`,
`K` commuting with `𝒰`. The vectors `e, J e, K e, J (K e)` form an orthonormal basis, sent to
`1, i, j, k`; in these coordinates `J` and `K` are left multiplication by `i` and `j`. Elements
of `𝒰` commute with `J` and `K`, so they act by right multiplication; for an element of `𝒱`,
the vectors on which it acts as left multiplication by its value at `e` form a `𝒰`-invariant
subspace containing `e`, hence the whole space. -/

open scoped RealInnerProductSpace
open Quaternion

namespace D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates

section Commutant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric operator commuting with a set of linear isometries acting irreducibly on a
nontrivial finite-dimensional space is a scalar multiple of the identity. -/
private lemma exists_eq_smul_of_isSymmetric [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (hAc : ∀ S ∈ 𝒰, ∀ x, A (S x) = S (A x)) :
    ∃ c : ℝ, ∀ x, A x = c • x := by
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, Module.End.HasEigenvalue A μ :=
    ⟨_, hA.hasEigenvalue_iSup_of_finiteDimensional⟩
  have hinv : ∀ S ∈ 𝒰, ∀ x ∈ Module.End.eigenspace A μ, S x ∈ Module.End.eigenspace A μ := by
    intro S hS x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hAc S hS, hx, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hμ)
  · refine ⟨μ, fun x => Module.End.mem_eigenspace_iff.mp ?_⟩
    rw [h]
    exact Submodule.mem_top

/-- The anticommutator of two skew operators commuting with an irreducible set of linear
isometries is a scalar multiple of the identity. -/
private lemma exists_anticomm_eq_smul [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (A B : E →ₗ[ℝ] E) (hAc : ∀ S ∈ 𝒰, ∀ x, A (S x) = S (A x))
    (hBc : ∀ S ∈ 𝒰, ∀ x, B (S x) = S (B x))
    (hAs : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hBs : ∀ x y, ⟪B x, y⟫ = -⟪x, B y⟫) :
    ∃ c : ℝ, ∀ x, A (B x) + B (A x) = c • x := by
  have hsym : (A ∘ₗ B + B ∘ₗ A).IsSymmetric := by
    intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_left, inner_add_right]
    rw [hAs (B x) y, hBs x (A y), hBs (A x) y, hAs x (B y)]
    ring
  have hc : ∀ S ∈ 𝒰, ∀ x, (A ∘ₗ B + B ∘ₗ A) (S x) = S ((A ∘ₗ B + B ∘ₗ A) x) := by
    intro S hS x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    rw [hBc S hS, hAc S hS, hAc S hS, hBc S hS]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSymmetric 𝒰 hirr _ hsym hc
  exact ⟨c, fun x => by simpa only [LinearMap.add_apply, LinearMap.comp_apply] using hc x⟩

/-- A nonzero skew operator commuting with an irreducible set of linear isometries has a real
multiple whose square is `-1`; that multiple is again skew and commutes with the set. -/
private lemma exists_complex_structure [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (A : E →ₗ[ℝ] E) (hAc : ∀ S ∈ 𝒰, ∀ x, A (S x) = S (A x))
    (hAs : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hA0 : ∃ x, A x ≠ 0) :
    ∃ (r : ℝ) (J : E →ₗ[ℝ] E), (∀ x, J x = r • A x) ∧
      (∀ S ∈ 𝒰, ∀ x, J (S x) = S (J x)) ∧ (∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫) ∧
      ∀ x, J (J x) = -x := by
  obtain ⟨c, hc⟩ := exists_anticomm_eq_smul 𝒰 hirr A A hAc hAc hAs hAs
  obtain ⟨x₀, hx₀⟩ := hA0
  have hneg : c < 0 := by
    refine lt_of_not_ge fun hcn => ?_
    have h1 : ⟪A (A x₀) + A (A x₀), x₀⟫ = -2 * ⟪A x₀, A x₀⟫ := by
      rw [inner_add_left, hAs (A x₀) x₀]
      ring
    rw [hc x₀, real_inner_smul_left] at h1
    have h2 : 0 < ⟪A x₀, A x₀⟫ := real_inner_self_pos.mpr hx₀
    have h3 : 0 ≤ ⟪x₀, x₀⟫ := real_inner_self_nonneg
    linarith [mul_nonneg hcn h3]
  have hpos : 0 < -2 / c := div_pos_of_neg_of_neg (by norm_num) hneg
  set r : ℝ := Real.sqrt (-2 / c)
  have hrr : r * r = -2 / c := Real.mul_self_sqrt hpos.le
  refine ⟨r, r • A, fun x => rfl, fun S hS x => ?_, fun x y => ?_, fun x => ?_⟩
  · simp only [LinearMap.smul_apply, hAc S hS, map_smul]
  · simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, hAs x y]
    ring
  · have hc0 : c ≠ 0 := hneg.ne
    simp only [LinearMap.smul_apply, map_smul, smul_smul, hrr]
    calc (-2 / c) • A (A x) = (-1 / c) • (A (A x) + A (A x)) := by module
      _ = (-1 / c) • (c • x) := by rw [hc x]
      _ = -x := by rw [smul_smul, div_mul_cancel₀ (-1 : ℝ) hc0, neg_one_smul]

/-- A linear isometry which, together with its inverse, commutes with an irreducible set of
linear isometries is a scalar plus a skew operator commuting with the set. -/
private lemma exists_smul_add_skew [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (T : E ≃ₗᵢ[ℝ] E) (hTc : ∀ S ∈ 𝒰, ∀ x, T (S x) = S (T x))
    (hTc' : ∀ S ∈ 𝒰, ∀ x, T.symm (S x) = S (T.symm x)) :
    ∃ (a : ℝ) (N : E →ₗ[ℝ] E), (∀ S ∈ 𝒰, ∀ x, N (S x) = S (N x)) ∧
      (∀ x y, ⟪N x, y⟫ = -⟪x, N y⟫) ∧ ∀ x, T x = a • x + N x := by
  set P : E →ₗ[ℝ] E := T.toLinearEquiv.toLinearMap + T.symm.toLinearEquiv.toLinearMap
  have hPx : ∀ x, P x = T x + T.symm x := fun x => rfl
  have hsym : P.IsSymmetric := by
    intro x y
    rw [hPx, hPx, inner_add_left, inner_add_right, T.inner_map_eq_flip, T.symm.inner_map_eq_flip,
      LinearIsometryEquiv.symm_symm]
    ring
  have hPc : ∀ S ∈ 𝒰, ∀ x, P (S x) = S (P x) := by
    intro S hS x
    rw [hPx, hPx, map_add, hTc S hS, hTc' S hS]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSymmetric 𝒰 hirr P hsym hPc
  have hsymm : ∀ y, T.symm y = c • y - T y := fun y => by
    rw [← hc y, hPx]
    abel
  refine ⟨c / 2, T.toLinearEquiv.toLinearMap - (c / 2) • LinearMap.id, fun S hS x => ?_,
    fun x y => ?_, fun x => ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, map_sub, map_smul, hTc S hS]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [T.inner_map_eq_flip, hsymm, inner_sub_right, real_inner_smul_right]
    ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    abel

/-- Two noncommuting elements of a set of linear isometries commuting with an irreducible set
give two noncommuting skew operators commuting with the irreducible set. The inverse of each
element also commutes with the irreducible set. -/
private lemma exists_noncomm_skew_pair [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 𝒱 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hcomm : ∀ S ∈ 𝒰, ∀ T ∈ 𝒱, S * T = T * S)
    (hnc : ∃ S ∈ 𝒱, ∃ T ∈ 𝒱, S * T ≠ T * S) :
    ∃ A B : E →ₗ[ℝ] E, (∀ S ∈ 𝒰, ∀ x, A (S x) = S (A x)) ∧
      (∀ S ∈ 𝒰, ∀ x, B (S x) = S (B x)) ∧ (∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) ∧
      (∀ x y, ⟪B x, y⟫ = -⟪x, B y⟫) ∧ ∃ x, A (B x) ≠ B (A x) := by
  have hcen : ∀ T ∈ 𝒱, ∀ S ∈ 𝒰, ∀ x, T (S x) = S (T x) := fun T hT S hS x =>
    (DFunLike.congr_fun (hcomm S hS T hT) x).symm
  have hdec : ∀ T ∈ 𝒱, ∃ (a : ℝ) (N : E →ₗ[ℝ] E), (∀ S ∈ 𝒰, ∀ x, N (S x) = S (N x)) ∧
      (∀ x y, ⟪N x, y⟫ = -⟪x, N y⟫) ∧ ∀ x, T x = a • x + N x := fun T hT =>
    exists_smul_add_skew 𝒰 hirr T (hcen T hT) (fun S hS x => by
      rw [LinearIsometryEquiv.symm_apply_eq, hcen T hT S hS, LinearIsometryEquiv.apply_symm_apply])
  obtain ⟨T₁, hT₁, T₂, hT₂, hne⟩ := hnc
  obtain ⟨a₁, N₁, hN₁c, hN₁s, hT₁N⟩ := hdec T₁ hT₁
  obtain ⟨a₂, N₂, hN₂c, hN₂s, hT₂N⟩ := hdec T₂ hT₂
  refine ⟨N₁, N₂, hN₁c, hN₂c, hN₁s, hN₂s, ?_⟩
  by_contra h
  push Not at h
  apply hne
  ext x
  change T₁ (T₂ x) = T₂ (T₁ x)
  rw [hT₁N (T₂ x), hT₂N x, hT₂N (T₁ x), hT₁N x, map_add, map_add, map_smul, map_smul, h x]
  module

/-- If a set of linear isometries acting irreducibly commutes elementwise with a set of linear
isometries containing two noncommuting elements, then there are two anticommuting skew
operators with square `-1` commuting with the irreducible set. -/
private lemma exists_quaternion_pair [FiniteDimensional ℝ E] [Nontrivial E]
    (𝒰 𝒱 : Set (E ≃ₗᵢ[ℝ] E))
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hcomm : ∀ S ∈ 𝒰, ∀ T ∈ 𝒱, S * T = T * S)
    (hnc : ∃ S ∈ 𝒱, ∃ T ∈ 𝒱, S * T ≠ T * S) :
    ∃ J K : E →ₗ[ℝ] E, (∀ S ∈ 𝒰, ∀ x, J (S x) = S (J x)) ∧
      (∀ S ∈ 𝒰, ∀ x, K (S x) = S (K x)) ∧ (∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫) ∧
      (∀ x y, ⟪K x, y⟫ = -⟪x, K y⟫) ∧ (∀ x, J (J x) = -x) ∧ (∀ x, K (K x) = -x) ∧
      ∀ x, K (J x) = -J (K x) := by
  obtain ⟨A, B, hAc, hBc, hAs, hBs, x₀, hx₀⟩ := exists_noncomm_skew_pair 𝒰 𝒱 hirr hcomm hnc
  have hA0 : ∃ x, A x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx₀ (by rw [h (B x₀), h x₀, map_zero])
  obtain ⟨r, J, hJA, hJc, hJs, hJJ⟩ := exists_complex_structure 𝒰 hirr A hAc hAs hA0
  obtain ⟨β, hβ⟩ := exists_anticomm_eq_smul 𝒰 hirr J B hJc hBc hJs hBs
  set B₀ : E →ₗ[ℝ] E := B + (β / 2) • J
  have hB₀x : ∀ x, B₀ x = B x + (β / 2) • J x := fun x => rfl
  have hB₀c : ∀ S ∈ 𝒰, ∀ x, B₀ (S x) = S (B₀ x) := by
    intro S hS x
    rw [hB₀x, hB₀x, hBc S hS, hJc S hS, map_add, map_smul]
  have hB₀s : ∀ x y, ⟪B₀ x, y⟫ = -⟪x, B₀ y⟫ := by
    intro x y
    rw [hB₀x, hB₀x, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hBs, hJs]
    ring
  have hB₀J : ∀ x, B₀ (J x) = -J (B₀ x) := by
    intro x
    rw [hB₀x, hB₀x, map_add, map_smul, hJJ]
    linear_combination (norm := module) hβ x
  have hB₀0 : ∃ x, B₀ x ≠ 0 := by
    by_contra h
    push Not at h
    have hB : ∀ y, B y = -(β / 2 * r) • A y := fun y => by
      have := h y
      rw [hB₀x, hJA, smul_smul] at this
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left this
    exact hx₀ (by rw [hB, hB, map_smul])
  obtain ⟨r', K, hKB, hKc, hKs, hKK⟩ := exists_complex_structure 𝒰 hirr B₀ hB₀c hB₀s hB₀0
  refine ⟨J, K, hJc, hKc, hJs, hKs, hJJ, hKK, fun x => ?_⟩
  rw [hKB, hKB, hB₀J, map_smul, smul_neg]

/-- For skew operators `J`, `K` with `J (J x) = -x`, `K (K x) = -x` and `K (J x) = -J (K x)`,
and a unit vector `e`, the four vectors `e, J e, K e, J (K e)` are orthonormal. -/
private lemma orthonormal_frame (J K : E →ₗ[ℝ] E) (hJs : ∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫)
    (hKs : ∀ x y, ⟪K x, y⟫ = -⟪x, K y⟫) (hJJ : ∀ x, J (J x) = -x) (hKK : ∀ x, K (K x) = -x)
    (hKJ : ∀ x, K (J x) = -J (K x)) (e : E) (he : ‖e‖ = 1) :
    Orthonormal ℝ ![e, J e, K e, J (K e)] := by
  have hskew0 : ∀ N : E → E, (∀ x y, ⟪N x, y⟫ = -⟪x, N y⟫) → ∀ x, ⟪x, N x⟫ = 0 := by
    intro N hN x
    have h := hN x x
    rw [real_inner_comm] at h
    linarith
  have hLs : ∀ x y, ⟪J (K x), y⟫ = -⟪x, J (K y)⟫ := by
    intro x y
    rw [hJs, hKs, hKJ, inner_neg_right, neg_neg]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have h01 : ⟪e, J e⟫ = 0 := hskew0 J hJs e
  have h02 : ⟪e, K e⟫ = 0 := hskew0 K hKs e
  have h03 : ⟪e, J (K e)⟫ = 0 := hskew0 (fun x => J (K x)) hLs e
  have h11 : ⟪J e, J e⟫ = 1 := by rw [hJs, hJJ, inner_neg_right, neg_neg, hee]
  have h12 : ⟪J e, K e⟫ = 0 := by rw [hJs, h03, neg_zero]
  have h13 : ⟪J e, J (K e)⟫ = 0 := by rw [hJs, hJJ, inner_neg_right, neg_neg, h02]
  have h22 : ⟪K e, K e⟫ = 1 := by rw [hKs, hKK, inner_neg_right, neg_neg, hee]
  have h23 : ⟪K e, J (K e)⟫ = 0 := hskew0 J hJs (K e)
  have h33 : ⟪J (K e), J (K e)⟫ = 1 := by rw [hJs, hJJ, inner_neg_right, neg_neg, h22]
  have h10 : ⟪J e, e⟫ = 0 := by rw [real_inner_comm, h01]
  have h20 : ⟪K e, e⟫ = 0 := by rw [real_inner_comm, h02]
  have h30 : ⟪J (K e), e⟫ = 0 := by rw [real_inner_comm, h03]
  have h21 : ⟪K e, J e⟫ = 0 := by rw [real_inner_comm, h12]
  have h31 : ⟪J (K e), J e⟫ = 0 := by rw [real_inner_comm, h13]
  have h32 : ⟪J (K e), K e⟫ = 0 := by rw [real_inner_comm, h23]
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceEq, ↓reduceIte, zero_ne_one, one_ne_zero,
      hee, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]

/-- Let `J`, `K` be skew operators on a finite-dimensional space of dimension at most four with
`J (J x) = -x`, `K (K x) = -x` and `K (J x) = -J (K x)`, and let `e` be a unit vector. Then the
dimension is four, and the linear isometric equivalence `Φ : E ≃ₗᵢ[ℝ] ℍ` sending
`e, J e, K e, J (K e)` to `1, i, j, k` turns `J` and `K` into left multiplication by `i` and
`j`. Two linear maps out of `E` agreeing on these four vectors are equal. -/
private lemma exists_frame_coordinates [FiniteDimensional ℝ E] (J K : E →ₗ[ℝ] E)
    (hJs : ∀ x y, ⟪J x, y⟫ = -⟪x, J y⟫) (hKs : ∀ x y, ⟪K x, y⟫ = -⟪x, K y⟫)
    (hJJ : ∀ x, J (J x) = -x) (hKK : ∀ x, K (K x) = -x) (hKJ : ∀ x, K (J x) = -J (K x))
    (hdim : Module.finrank ℝ E ≤ 4) (e : E) (he : ‖e‖ = 1) :
    Module.finrank ℝ E = 4 ∧ ∃ Φ : E ≃ₗᵢ[ℝ] ℍ, Φ e = 1 ∧
      (∀ w, Φ (J w) = (⟨0, 1, 0, 0⟩ : ℍ) * Φ w) ∧ (∀ w, Φ (K w) = (⟨0, 0, 1, 0⟩ : ℍ) * Φ w) ∧
      ∀ f g : E →ₗ[ℝ] ℍ, f e = g e → f (J e) = g (J e) → f (K e) = g (K e) →
        f (J (K e)) = g (J (K e)) → f = g := by
  have hon := orthonormal_frame J K hJs hKs hJJ hKK hKJ e he
  have hli := hon.linearIndependent
  have hcard : Module.finrank ℝ E = 4 :=
    le_antisymm hdim (by simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![e, J e, K e, J (K e)]) :=
    (hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hcard])).ge
  set b := OrthonormalBasis.mk hon hsp
  set Φ : E ≃ₗᵢ[ℝ] ℍ := b.repr.trans linearIsometryEquivTuple.symm
  have hΦ : ∀ w, Φ w = ⟨⟪e, w⟫, ⟪J e, w⟫, ⟪K e, w⟫, ⟪J (K e), w⟫⟩ := by
    intro w
    simp only [Φ, b, LinearIsometryEquiv.trans_apply, linearIsometryEquivTuple_symm_apply,
      Fin.isValue, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
  have hΦe : Φ e = 1 := by
    have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have h10 : ⟪J e, e⟫ = 0 := hon.2 (by decide : (1 : Fin 4) ≠ 0)
    have h20 : ⟪K e, e⟫ = 0 := hon.2 (by decide : (2 : Fin 4) ≠ 0)
    have h30 : ⟪J (K e), e⟫ = 0 := hon.2 (by decide : (3 : Fin 4) ≠ 0)
    rw [hΦ, hee, h10, h20, h30]
    rfl
  have hΦJ : ∀ w, Φ (J w) = (⟨0, 1, 0, 0⟩ : ℍ) * Φ w := by
    intro w
    have e1 := hJs e w
    have e2 := hJs e (J w)
    have e3 := hJs (K e) w
    have e4 := hJs (K e) (J w)
    rw [hJJ, inner_neg_right] at e2 e4
    rw [hΦ, hΦ]
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> linarith
  have hΦK : ∀ w, Φ (K w) = (⟨0, 0, 1, 0⟩ : ℍ) * Φ w := by
    intro w
    have e1 := hKs e w
    have e2 := hKs (J e) w
    have e3 := hKs e (K w)
    have e4 := hKs (J (K e)) w
    rw [hKJ, inner_neg_left] at e2
    rw [hKK, inner_neg_right] at e3
    rw [hKJ, hKK, map_neg, neg_neg] at e4
    rw [hΦ, hΦ]
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> linarith
  refine ⟨hcard, Φ, hΦe, hΦJ, hΦK, fun f g h0 h1 h2 h3 => b.toBasis.ext fun i => ?_⟩
  simp only [OrthonormalBasis.coe_toBasis, b, OrthonormalBasis.coe_mk]
  fin_cases i
  exacts [h0, h1, h2, h3]

end Commutant

/-- Under the hypotheses of `exists_quaternion_coordinates`, a given unit vector `e` forces
dimension four and is the unit `1` of quaternionic coordinates in which each element of `𝒱` acts
by left multiplication and each element of `𝒰` by right multiplication by a unit quaternion. -/
private theorem exists_quaternion_coordinates_of_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (𝒰 𝒱 : Set (E ≃ₗᵢ[ℝ] E))
    (hdim : Module.finrank ℝ E ≤ 4)
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hcomm : ∀ S ∈ 𝒰, ∀ T ∈ 𝒱, S * T = T * S)
    (hnc : ∃ S ∈ 𝒱, ∃ T ∈ 𝒱, S * T ≠ T * S)
    (e : E) (he : ‖e‖ = 1) :
    Module.finrank ℝ E = 4 ∧
      ∃ Φ : E ≃ₗᵢ[ℝ] ℍ, Φ e = 1 ∧
        (∀ T ∈ 𝒱, ∃ q : ℍ, ‖q‖ = 1 ∧ ∀ v : E, Φ (T v) = q * Φ v) ∧
        (∀ S ∈ 𝒰, ∃ p : ℍ, ‖p‖ = 1 ∧ ∀ v : E, Φ (S v) = Φ v * p) := by
  have he0 : e ≠ 0 := by
    rw [← norm_ne_zero_iff, he]
    exact one_ne_zero
  have : Nontrivial E := ⟨⟨e, 0, he0⟩⟩
  obtain ⟨J, K, hJc, hKc, hJs, hKs, hJJ, hKK, hKJ⟩ := exists_quaternion_pair 𝒰 𝒱 hirr hcomm hnc
  obtain ⟨hcard, Φ, hΦe, hΦJ, hΦK, hext⟩ :=
    exists_frame_coordinates J K hJs hKs hJJ hKK hKJ hdim e he
  -- elements of `𝒰` commute with `J` and `K`, hence act by right multiplication
  have hR : ∀ S ∈ 𝒰, ∀ w, Φ (S w) = Φ w * Φ (S e) := by
    intro S hS w
    refine LinearMap.congr_fun (hext (Φ.toLinearEquiv.toLinearMap ∘ₗ S.toLinearEquiv.toLinearMap)
      (LinearMap.mulRight ℝ (Φ (S e)) ∘ₗ Φ.toLinearEquiv.toLinearMap) ?_ ?_ ?_ ?_) w
    · change Φ (S e) = Φ e * Φ (S e)
      rw [hΦe, one_mul]
    · change Φ (S (J e)) = Φ (J e) * Φ (S e)
      rw [← hJc S hS, hΦJ (S e), hΦJ e, hΦe, mul_one]
    · change Φ (S (K e)) = Φ (K e) * Φ (S e)
      rw [← hKc S hS, hΦK (S e), hΦK e, hΦe, mul_one]
    · change Φ (S (J (K e))) = Φ (J (K e)) * Φ (S e)
      rw [← hJc S hS, ← hKc S hS, hΦJ (K (S e)), hΦJ (K e), hΦK (S e), hΦK e, hΦe, mul_one,
        mul_assoc]
  -- for an element of `𝒱`, the vectors on which it acts as left multiplication by its value at
  -- `e` form a `𝒰`-invariant subspace containing `e`
  have hL : ∀ T ∈ 𝒱, ∀ w, Φ (T w) = Φ (T e) * Φ w := by
    intro T hT
    have hTc : ∀ S ∈ 𝒰, ∀ x, T (S x) = S (T x) := fun S hS x =>
      (DFunLike.congr_fun (hcomm S hS T hT) x).symm
    set X : Submodule ℝ E := LinearMap.ker
      (Φ.toLinearEquiv.toLinearMap ∘ₗ T.toLinearEquiv.toLinearMap -
        LinearMap.mulLeft ℝ (Φ (T e)) ∘ₗ Φ.toLinearEquiv.toLinearMap)
    have hX : ∀ w, w ∈ X ↔ Φ (T w) = Φ (T e) * Φ w := fun w => by
      simp only [X, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.mulLeft_apply,
        sub_eq_zero]
    have hXinv : ∀ S ∈ 𝒰, ∀ w ∈ X, S w ∈ X := by
      intro S hS w hw
      rw [hX] at hw ⊢
      rw [hTc S hS, hR S hS (T w), hw, hR S hS w, mul_assoc]
    have heX : e ∈ X := (hX e).mpr (by rw [hΦe, mul_one])
    rcases hirr X hXinv with h | h
    · rw [h, Submodule.mem_bot] at heX
      exact absurd heX he0
    · intro w
      exact (hX w).mp (by rw [h]; exact Submodule.mem_top)
  refine ⟨hcard, Φ, hΦe, fun T hT => ⟨Φ (T e), ?_, hL T hT⟩, fun S hS => ⟨Φ (S e), ?_, hR S hS⟩⟩
  · rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, he]
  · rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, he]

/-- **Quaternionic coordinates from a noncommutative commutant.** Let `𝒰` be a set of linear
isometries acting irreducibly on a real inner product space `E` of dimension at most four, and
let `𝒱` be a set of linear isometries containing two noncommuting elements, each element of `𝒱`
commuting with every element of `𝒰`. Then `E` has dimension four, and for every unit vector `e`
there is a linear isometric equivalence `Φ : E ≃ₗᵢ[ℝ] ℍ` with `Φ e = 1` in which each element of
`𝒱` acts by left multiplication and each element of `𝒰` by right multiplication by a unit
quaternion. The space is nontrivial because two isometries of the zero space commute, so a unit
vector exists and gives the dimension. -/
theorem exists_quaternion_coordinates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (𝒰 𝒱 : Set (E ≃ₗᵢ[ℝ] E))
    (hdim : Module.finrank ℝ E ≤ 4)
    (hirr : ∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hcomm : ∀ S ∈ 𝒰, ∀ T ∈ 𝒱, S * T = T * S)
    (hnc : ∃ S ∈ 𝒱, ∃ T ∈ 𝒱, S * T ≠ T * S) :
    Module.finrank ℝ E = 4 ∧
      ∀ e : E, ‖e‖ = 1 →
        ∃ Φ : E ≃ₗᵢ[ℝ] ℍ, Φ e = 1 ∧
          (∀ T ∈ 𝒱, ∃ q : ℍ, ‖q‖ = 1 ∧ ∀ v : E, Φ (T v) = q * Φ v) ∧
          (∀ S ∈ 𝒰, ∃ p : ℍ, ‖p‖ = 1 ∧ ∀ v : E, Φ (S v) = Φ v * p) := by
  have : Nontrivial E := by
    obtain ⟨S, -, T, -, hST⟩ := hnc
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hST (LinearIsometryEquiv.ext fun x => Subsingleton.elim _ _)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hx1 : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  exact ⟨(exists_quaternion_coordinates_of_unit 𝒰 𝒱 hdim hirr hcomm hnc _ hx1).1, fun e he =>
    (exists_quaternion_coordinates_of_unit 𝒰 𝒱 hdim hirr hcomm hnc e he).2⟩

end D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
