/- GID: D5/S3/Quantum/Measurement/Auric/ProjectionFrames
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ProjectionFrames
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary isometric frames for a first projective split. -/

import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Measurement.Auric.ProjectiveTree

/-! # Complementary isometric frames for a first projective split -/

namespace D5.S3.Quantum.Measurement.Auric.ProjectionFrames

open _root_.Matrix
open D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem coordinateEmbedding_projector {k : Type*} [Fintype k]
    (e : k ↪ n) :
    coordinateEmbedding e * (coordinateEmbedding e)ᴴ =
      diagonal (fun i => if i ∈ Set.range e then (1 : ℂ) else 0) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i ∈ Set.range e
    · obtain ⟨p, rfl⟩ := hi
      simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
        e.injective.eq_iff]
    · have hn (p : k) : i ≠ e p := fun he => hi ⟨p, he.symm⟩
      simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
        hn, fun j => (hn j).symm]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hi : i = e p
    · have hj : j ≠ e p := hi ▸ Ne.symm h
      simp [coordinateEmbedding, Matrix.conjTranspose_apply, hi, hj]
    · simp [coordinateEmbedding, Matrix.conjTranspose_apply, hi]

/-- Every proper nonzero Hermitian projection has complementary positive-rank
orthonormal frames, with their dimensions summing to the ambient dimension. -/
theorem exists_complementary_frames (E : Matrix n n ℂ) (hE : E.IsHermitian)
    (hidem : E * E = E) (hzero : E ≠ 0) (hone : E ≠ 1) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ m + k = Fintype.card n ∧
      ∃ V : Matrix n (Fin m) ℂ, ∃ W : Matrix n (Fin k) ℂ,
        Vᴴ * V = 1 ∧ Wᴴ * W = 1 ∧ V * Vᴴ = E ∧ W * Wᴴ = 1 - E := by
  classical
  let U := hE.eigenvectorUnitary.val
  let D : Matrix n n ℂ := diagonal fun i => (hE.eigenvalues i : ℂ)
  have huv : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hE.eigenvectorUnitary.prop
  have hvu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hE.eigenvectorUnitary.prop
  have hdiag : E = U * D * Uᴴ := by
    have h := hE.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
    have hD : diagonal (RCLike.ofReal ∘ hE.eigenvalues) = D := by
      ext i j
      by_cases hij : i = j <;> simp [D, Matrix.diagonal_apply, hij]
    rw [hD] at h
    exact h
  have hh : Uᴴ * E * U = D := by
    rw [hdiag]
    simp only [Matrix.mul_assoc]
    rw [hvu, Matrix.mul_one, ← Matrix.mul_assoc Uᴴ U, hvu, Matrix.one_mul]
  have hDD : D * D = D := by
    rw [← hh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, huv, Matrix.one_mul,
      ← Matrix.mul_assoc E E, hidem]
  have hvals (i : n) : hE.eigenvalues i = 0 ∨ hE.eigenvalues i = 1 := by
    have he := congrArg (fun A : Matrix n n ℂ => (A i i).re) hDD
    have hs : hE.eigenvalues i * (hE.eigenvalues i - 1) = 0 := by
      simp [D, Complex.mul_re] at he
      linarith only [he]
    rcases mul_eq_zero.mp hs with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let S : Set n := {i | hE.eigenvalues i = 1}
  let m := Fintype.card S
  let k := Fintype.card (Sᶜ : Set n)
  let v : Fin m ↪ n := (Fintype.equivFin S).symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let w : Fin k ↪ n := (Fintype.equivFin (Sᶜ : Set n)).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩
  have hv (i : n) : i ∈ Set.range v ↔ i ∈ S := by
    constructor
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin S).symm j).property
    · intro hi
      refine ⟨Fintype.equivFin S ⟨i, hi⟩, ?_⟩
      simp [v]
  have hw (i : n) : i ∈ Set.range w ↔ i ∉ S := by
    constructor
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin (Sᶜ : Set n)).symm j).property
    · intro hi
      refine ⟨Fintype.equivFin (Sᶜ : Set n) ⟨i, hi⟩, ?_⟩
      simp [w]
  let V := U * coordinateEmbedding v
  let W := U * coordinateEmbedding w
  have hvD : coordinateEmbedding v * (coordinateEmbedding v)ᴴ = D := by
    rw [coordinateEmbedding_projector]
    congr 1
    funext i
    rcases hvals i with h | h <;> simp [hv, S, h]
  have hwD : coordinateEmbedding w * (coordinateEmbedding w)ᴴ = 1 - D := by
    rw [coordinateEmbedding_projector]
    ext i j
    by_cases hij : i = j
    · subst j
      rcases hvals i with h | h <;> simp [D, hw, S, h]
    · simp [D, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hvu,
      Matrix.one_mul, coordinateEmbedding_isometry]
  have hW : Wᴴ * W = 1 := by
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hvu,
      Matrix.one_mul, coordinateEmbedding_isometry]
  have hVE : V * Vᴴ = E := by
    dsimp only [V]
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, hvD]
    exact hdiag.symm
  have hWE : W * Wᴴ = 1 - E := by
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, hwD,
      Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, huv, hdiag]
  have hm : 0 < m := by
    by_contra! hh
    have hm0 : m = 0 := by omega
    have hV0 : V * Vᴴ = 0 := by
      let : IsEmpty (Fin m) := hm0 ▸ Fin.isEmpty
      ext i j
      simp [Matrix.mul_apply]
    exact hzero (hVE.symm.trans hV0)
  have hk : 0 < k := by
    by_contra! hh
    have hk0 : k = 0 := by omega
    have hW0 : W * Wᴴ = 0 := by
      let : IsEmpty (Fin k) := hk0 ▸ Fin.isEmpty
      ext i j
      simp [Matrix.mul_apply]
    exact hone ((sub_eq_zero.mp (hWE.symm.trans hW0)).symm)
  have hmk := Fintype.card_congr (Equiv.Set.sumCompl S)
  rw [Fintype.card_sum] at hmk
  exact ⟨m, k, hm, hk, hmk, V, W, hV, hW, hVE, hWE⟩

end D5.S3.Quantum.Measurement.Auric.ProjectionFrames
