/- GID: D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMRankOneInactiveRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Active and inactive blocks at zero actual BKM gap for a rank-one observable. -/

import D5.S3.Quantum.Recovery.BKMObservableProductRigidity

/-! # Rank-one active and inactive blocks for the actual BKM gap -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open D5.S3.Quantum.Recovery.BKMObservableRigidity (mpow_add mpow_zero)
open D5.S3.Quantum.Recovery.BKMObservableProductRigidity
  (ratioPiece modularPiece relativeDensity bkmGap_eq_zero_iff_commute_ratioPieces)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_kronecker)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (partialTraceRight_posDef partialTraceRight_embed_mul partialTraceRight_mul_embed)

namespace D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity

universe u
variable {n : Type*} [Fintype n]
variable {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]

private def spectralValues (s : n → ℝ) : Finset ℝ :=
  Finset.univ.image s

private def diagonalSlice (s : n → ℝ) (w : n → ℂ) (a : ℝ) : n → ℂ :=
  fun i => if s i = a then w i else 0

/-- The component of a vector in the whole eigenspace at a retained eigenvalue. -/
def activeSpectralPiece {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) (a : ℝ) :
    R → ℂ :=
  let U : Matrix R R ℂ := hS.eigenvectorUnitary
  U *ᵥ diagonalSlice hS.eigenvalues (Uᴴ *ᵥ w) a

private def lineProjection (w : n → ℂ) : Matrix n n ℂ :=
  (star w ⬝ᵥ w)⁻¹ • vecMulVec w (star w)

/-- Orthogonal projection onto the span of the grouped spectral pieces of the vector.
A zero piece contributes the zero matrix. -/
def activeProjection {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) : Matrix R R ℂ :=
  ∑ a ∈ spectralValues hS.eigenvalues, lineProjection (activeSpectralPiece hS w a)

private theorem outer_mulVec (v w z : n → ℂ) :
    vecMulVec v w *ᵥ z = (w ⬝ᵥ z) • v := by
  rw [vecMulVec_mulVec]
  ext i
  exact mul_comm _ _

private theorem lineProjection_hermitian (w : n → ℂ) : (lineProjection w).IsHermitian := by
  change (lineProjection w)ᴴ = lineProjection w
  have h : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := (star_dotProduct w w).symm
  rw [lineProjection, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star,
    star_inv₀, h]

private theorem lineProjection_mulVec (w z : n → ℂ) :
    lineProjection w *ᵥ z = ((star w ⬝ᵥ w)⁻¹ * (star w ⬝ᵥ z)) • w := by
  rw [lineProjection, Matrix.smul_mulVec, outer_mulVec, smul_smul]

private theorem lineProjection_self (w : n → ℂ) : lineProjection w *ᵥ w = w := by
  by_cases hw : w = 0
  · simp [hw]
  have hnorm : star w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_star_self_eq_zero.mp h)
  rw [lineProjection_mulVec, inv_mul_cancel₀ hnorm, one_smul]

private theorem diagonalSlice_orthogonal (s : n → ℝ) (w : n → ℂ) {a b : ℝ} (hab : a ≠ b) :
    star (diagonalSlice s w a) ⬝ᵥ diagonalSlice s w b = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : s i = a <;> simp [diagonalSlice, h, hab]

private theorem sum_diagonalSlice (s : n → ℝ) (w : n → ℂ) :
    ∑ a ∈ spectralValues s, diagonalSlice s w a = w := by
  ext i
  simp only [Finset.sum_apply, diagonalSlice]
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · exact fun ha => (ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim

private theorem unitary_dotProduct {U : Matrix R R ℂ} (hU : Uᴴ * U = 1) (v w : R → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

private theorem activeProjection_spec {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) :
    let P := activeProjection hS w
    P.IsHermitian ∧ P * P = P ∧ P *ᵥ w = w ∧
      ∀ z, P *ᵥ z = z ↔ z ∈ Submodule.span ℂ (Set.range (activeSpectralPiece hS w)) := by
  classical
  let U : Matrix R R ℂ := hS.eigenvectorUnitary
  let s := hS.eigenvalues
  let v := Uᴴ *ᵥ w
  let z := activeSpectralPiece hS w
  let P := activeProjection hS w
  change P.IsHermitian ∧ P * P = P ∧ P *ᵥ w = w ∧
    ∀ x, P *ᵥ x = x ↔ x ∈ Submodule.span ℂ (Set.range z)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hfixed (a : ℝ) : P *ᵥ z a = z a := by
    change (∑ b ∈ spectralValues s, lineProjection (z b)) *ᵥ z a = z a
    rw [sum_mulVec, Finset.sum_eq_single a]
    · exact lineProjection_self _
    · intro b _ hb
      rw [lineProjection_mulVec, show star (z b) ⬝ᵥ z a = 0 from
        (unitary_dotProduct hU _ _).trans (diagonalSlice_orthogonal s v hb),
        mul_zero, zero_smul]
    · intro ha
      have hz : diagonalSlice s v a = 0 := by
        funext i
        have hi : s i ≠ a := fun he =>
          ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
        simp [diagonalSlice, hi]
      simp [z, activeSpectralPiece, U, s, v, hz]
  have hrange (x : R → ℂ) : P *ᵥ x ∈ Submodule.span ℂ (Set.range z) := by
    change (∑ b ∈ spectralValues s, lineProjection (z b)) *ᵥ x ∈ _
    rw [sum_mulVec]
    apply Submodule.sum_mem
    intro b _
    rw [lineProjection_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hpreserve (x : R → ℂ) (hx : x ∈ Submodule.span ℂ (Set.range z)) : P *ᵥ x = x := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hfixed a
    | zero => exact mulVec_zero _
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, hx]
  refine ⟨?_, ?_, ?_, fun x => ⟨fun hx => hx ▸ hrange x, hpreserve x⟩⟩
  · change (∑ b ∈ spectralValues s, lineProjection (z b))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun b _ => (lineProjection_hermitian (z b)).eq
  · apply Matrix.mulVec_injective
    funext x
    exact (mulVec_mulVec x P P).symm.trans (hpreserve _ (hrange x))
  · have hw : ∑ b ∈ spectralValues s, z b = w := by
      change ∑ b ∈ spectralValues s, U *ᵥ diagonalSlice s v b = w
      rw [← mulVec_sum, sum_diagonalSlice, show U *ᵥ v = w by
        rw [show v = Uᴴ *ᵥ w from rfl, mulVec_mulVec, hU', one_mulVec]]
    exact hpreserve _ (hw ▸ Submodule.sum_mem _ fun b _ =>
      Submodule.subset_span ⟨b, rfl⟩)

end D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity
