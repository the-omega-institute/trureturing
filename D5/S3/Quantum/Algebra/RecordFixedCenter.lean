/- GID: D5/S3/Quantum/Algebra/RecordFixedCenter
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/RecordFixedCenter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The center of a record-block algebra is exactly its block-scalar range. -/

/- Library-search audit trail (2026-08-16):
   * D5 searches found only a two-address fixed-entry characterization and no block-center theorem.
   * Loogle and local API search found `Set.center_pi` and `Matrix.center_eq_range`;
     both exact component results are imported and applied below.
   * Local pinned-Mathlib searches found no theorem identifying the center of a product of
     differently indexed matrix blocks with the range of the block-scalar map.
-/

import Mathlib.Algebra.Group.Center
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis

namespace D5.S3.Quantum.Algebra.RecordFixedCenter

/-- Put one scalar multiple of the identity in each record block. The coefficient depends only
on the classical record label, while the identity spans the unresolved internal block. -/
def recordCenterScalar {Λ : Type*} (I : Λ -> Type*) [∀ α, Fintype (I α)]
    [∀ α, DecidableEq (I α)]
    (c : Λ -> ℂ) : ∀ α, Matrix (I α) (I α) ℂ :=
  fun α => Matrix.scalar (I α) (c α)

/-- After the fixed algebra is decomposed into its record blocks, its center consists exactly
of one scalar identity on each block. For finitely many labels, the displayed product is the
finite direct sum in the source statement. -/
theorem record_fixed_center_eq_block_scalars {Λ : Type*} (I : Λ -> Type*)
    [∀ α, Fintype (I α)] [∀ α, DecidableEq (I α)] :
    Set.center (∀ α, Matrix (I α) (I α) ℂ) =
      Set.range (recordCenterScalar I) := by
  rw [Set.center_pi]
  ext A
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_range]
  constructor
  · intro hCenter
    have hScalar : ∀ α, ∃ c : ℂ, Matrix.scalar (I α) c = A α := by
      intro α
      rw [← Set.mem_range, ← Matrix.center_eq_range]
      exact hCenter α
    choose c hc using hScalar
    exact ⟨c, funext hc⟩
  · rintro ⟨c, rfl⟩ α
    rw [Matrix.center_eq_range]
    exact ⟨c α, rfl⟩

/-- The theorem's typeclass assumptions and matrix-block domain have a concrete finite model. -/
example :
    Set.center (∀ _ : Fin 2, Matrix (Fin 2) (Fin 2) ℂ) =
      Set.range (recordCenterScalar (fun _ : Fin 2 => Fin 2)) :=
  record_fixed_center_eq_block_scalars _

#print axioms record_fixed_center_eq_block_scalars

end D5.S3.Quantum.Algebra.RecordFixedCenter
