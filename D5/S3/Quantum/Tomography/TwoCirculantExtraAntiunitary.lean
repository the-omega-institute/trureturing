/- GID: D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A conjugate-block antiunitary preserves common-unbiased vectors and produces exact orthogonal partners, including partners that exchange cyclic modes. -/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/- Reuse audit, 2026-09-05.
   Repository search for antiunitary, skew partner, and the concrete block
   intertwiner found no matching theorem. Existing Clifford phase covariance
   is about scalar phase actions, not this vector-level partner construction.
   The frozen WindowRegister already owns the cyclic shift and root of unity;
   neither is redefined here. The proof uses Mathlib's Matrix.fromBlocks,
   Matrix.mulVec, dotProduct, complex star, and finite sum decomposition.
   Mathlib is pinned by the PR to db584cd6d46c92f209a44c0f1c829460d327499d.

   This file deliberately does not assert global-to-modewise orthogonality.
   The attached exact interval certificate gives a counterexample to that
   proposed implication. The analytic root enclosure is not proved here.
   Local Lean elaboration was unavailable; this source awaits admission.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.TwoCirculantExtraAntiunitary

open Matrix

private def conjugateBlock {κ : Type*} (A B : Matrix κ κ ℂ) :
    Matrix (κ ⊕ κ) (κ ⊕ κ) ℂ :=
  Matrix.fromBlocks A B (fun i j ↦ star (B i j))
    (fun i j ↦ -star (A i j))

private def partner {κ : Type*} (v : κ ⊕ κ → ℂ) : κ ⊕ κ → ℂ :=
  Sum.elim (fun i ↦ -star (v (Sum.inr i)))
    (fun i ↦ star (v (Sum.inl i)))

private theorem adjoint_inl {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℂ) (v : κ ⊕ κ → ℂ) (i : κ) :
    ((conjugateBlock A B)ᴴ *ᵥ v) (Sum.inl i) =
      (∑ j, star (A j i) * v (Sum.inl j)) +
        ∑ j, B j i * v (Sum.inr j) := by
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    conjugateBlock, Fintype.sum_sum_type]

private theorem adjoint_inr {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℂ) (v : κ ⊕ κ → ℂ) (i : κ) :
    ((conjugateBlock A B)ᴴ *ᵥ v) (Sum.inr i) =
      (∑ j, star (B j i) * v (Sum.inl j)) -
        ∑ j, A j i * v (Sum.inr j) := by
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    conjugateBlock, Fintype.sum_sum_type, sub_eq_add_neg]

private theorem adjoint_partner {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℂ) (v : κ ⊕ κ → ℂ) :
    (conjugateBlock A B)ᴴ *ᵥ partner v =
      fun i ↦ -(partner ((conjugateBlock A B)ᴴ *ᵥ v) i) := by
  funext i
  cases i with
  | inl i =>
      simp [adjoint_inl, adjoint_inr, partner, sub_eq_add_neg,
        mul_comm, add_comm, add_left_comm, add_assoc]
  | inr i =>
      simp [adjoint_inl, adjoint_inr, partner, sub_eq_add_neg,
        mul_comm, add_comm, add_left_comm, add_assoc]

private theorem partner_orthogonal {κ : Type*} [Fintype κ]
    (v : κ ⊕ κ → ℂ) :
    (fun i ↦ star (v i)) ⬝ᵥ partner v = 0 := by
  unfold dotProduct
  rw [Fintype.sum_sum_type]
  simp only [partner, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- The skew-conjugate partner of a common-unbiased vector is again
common-unbiased and is exactly orthogonal to the original vector.

The block pattern is `[A B; conjugate B -conjugate A]`. In the real-parameter
2-circulant stratum, a row permutation puts the actual Hadamard matrix into
this pattern with symmetric blocks. This extra partner can exchange the two
nontrivial cyclic modes. Consequently global orthogonality cannot by itself
be promoted to modewise orthogonality on that stratum.

No independent unitary, Hadamard, or inner-product carrier is introduced.
The conclusion concerns this explicit partner, not all orthogonal partners. -/
theorem conjugate_block_common_unbiased_orthogonal_partner
    {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℂ) (v : κ ⊕ κ → ℂ) (rho : ℝ)
    (hCoordinate : ∀ i, Complex.normSq (v i) = 1)
    (hImage : ∀ i, Complex.normSq
      (((Matrix.fromBlocks A B (fun i j ↦ star (B i j))
        (fun i j ↦ -star (A i j)))ᴴ *ᵥ v) i) = rho) :
    let H := Matrix.fromBlocks A B (fun i j ↦ star (B i j))
      (fun i j ↦ -star (A i j))
    let w := Sum.elim (fun i ↦ -star (v (Sum.inr i)))
      (fun i ↦ star (v (Sum.inl i)))
    (∀ i, Complex.normSq (w i) = 1) ∧
      (∀ i, Complex.normSq ((Hᴴ *ᵥ w) i) = rho) ∧
      (fun i ↦ star (v i)) ⬝ᵥ w = 0 := by
  change (∀ i, Complex.normSq (partner v i) = 1) ∧
    (∀ i, Complex.normSq (((conjugateBlock A B)ᴴ *ᵥ partner v) i) = rho) ∧
    (fun i ↦ star (v i)) ⬝ᵥ partner v = 0
  refine ⟨?_, ?_, partner_orthogonal v⟩
  · intro i
    cases i with
    | inl i =>
        simpa [partner, Complex.star_def] using hCoordinate (Sum.inr i)
    | inr i =>
        simpa [partner, Complex.star_def] using hCoordinate (Sum.inl i)
  · intro i
    rw [adjoint_partner]
    cases i with
    | inl i =>
        simpa [partner, conjugateBlock, Complex.star_def] using hImage (Sum.inr i)
    | inr i =>
        simpa [partner, conjugateBlock, Complex.star_def] using hImage (Sum.inl i)

#print axioms conjugate_block_common_unbiased_orthogonal_partner

end D5.S3.Quantum.Tomography.TwoCirculantExtraAntiunitary
