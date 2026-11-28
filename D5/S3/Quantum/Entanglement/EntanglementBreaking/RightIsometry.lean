/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/RightIsometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/RightIsometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A right isometric factorization through a prescribed finite dimension. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Matrix.Spectrum

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped ComplexOrder

/-- All rows of a rectangular matrix are supported by one k-dimensional
subspace of its input space, even when the matrix has rank below k. -/
theorem exists_right_isometry_factorization {k d : ℕ} (hkd : k ≤ d)
    (A : Matrix (Fin k) (Fin d) ℂ) :
    ∃ V : Matrix (Fin d) (Fin k) ℂ, Vᴴ * V = 1 ∧ A = (A * V) * Vᴴ := by
  classical
  let K := Aᴴ * A
  have hK : K.IsHermitian := isHermitian_conjTranspose_mul_self A
  let s := Finset.univ.filter fun i => hK.eigenvalues i ≠ 0
  have hs : s.card ≤ k := by
    have hcard : K.rank = s.card := by
      rw [hK.rank_eq_card_non_zero_eigs]
      simp [s, Fintype.card_subtype]
    rw [← hcard]
    exact (rank_mul_le_right Aᴴ A).trans
      (by simpa using rank_le_card_height A)
  obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq hs (by simpa using hkd)
  let e : Fin k ≃ ↥t := Fintype.equivOfCardEq (by simp [ht])
  let f : Fin k → Fin d := fun j => (e j).val
  let U : Matrix (Fin d) (Fin d) ℂ := hK.eigenvectorUnitary
  let V := U.submatrix id f
  have hU₁ : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hU₂ : U * Uᴴ = 1 := hK.eigenvectorUnitary.2.2
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hV : Vᴴ * V = 1 := by
    dsimp [V]
    rw [conjTranspose_submatrix,
      ← Matrix.submatrix_mul Uᴴ U f id f Function.bijective_id, hU₁,
      Matrix.submatrix_one f hf]
  let B := A * U
  have hdiag : Bᴴ * B = diagonal (fun j => (hK.eigenvalues j : ℂ)) := by
    have hspec : K = U * diagonal (fun j => (hK.eigenvalues j : ℂ)) * Uᴴ :=
      hK.spectral_theorem
    change (A * U)ᴴ * (A * U) = _
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A,
      ← Matrix.mul_assoc Uᴴ]
    change Uᴴ * K * U = _
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc, hU₁, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU₁, Matrix.one_mul]
  have hz (j : Fin d) (hj : j ∉ t) : (fun i => B i j) = 0 := by
    have hjs : j ∉ s := fun h => hj (hst h)
    have he : hK.eigenvalues j = 0 := by simpa [s] using hjs
    apply dotProduct_star_self_eq_zero.mp
    have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j j) hdiag
    simpa [Matrix.mul_apply, dotProduct, diagonal_apply_eq, he, Pi.star_apply]
      using hentry
  have hA : A = B * Uᴴ := by dsimp [B]; rw [Matrix.mul_assoc, hU₂, Matrix.mul_one]
  have hBV (i : Fin k) (j : Fin k) : (A * V) i j = B i (f j) := rfl
  refine ⟨V, hV, ?_⟩
  ext i j
  nth_rw 1 [hA]
  simp only [Matrix.mul_apply, conjTranspose_apply, hBV, V, submatrix_apply, id_eq]
  let g : Fin d → ℂ := fun l => B i l * star (U j l)
  change (∑ l, g l) = ∑ l, g (f l)
  calc
    (∑ l, g l) = ∑ l ∈ t, g l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ t)
      intro l _ hl
      have hz' := congrFun (hz l hl) i
      simp [g, hz']
    _ = ∑ l : ↥t, g l.val := by simpa using (Finset.sum_attach t g).symm
    _ = ∑ l, g (f l) := (e.sum_comp (fun l => g l.val)).symm
