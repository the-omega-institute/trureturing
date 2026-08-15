/- GID: D5/S3/Resource/CompositeCones/StrictChain
   generality: G
   mirror-B: D5/B/S3/Resource/CompositeCones/StrictChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two-qubit separable, positive-semidefinite, and block-positive cones form a strict chain. -/

import D5.S3.Resource.CompositeConeProperness

/- Library-search audit trail (2026-08-16):
   * Repository searches for the complete strict chain found no single theorem. The frozen
     `CompositeCones` module supplies both inclusions, and the frozen
     `CompositeConeProperness` module supplies witnesses showing both are strict.
   * Loogle's exact query `Set.ssubset_iff_exists` found that pinned-Mathlib theorem.
     LeanSearch's natural-language strict-subset query returned it and
     `HasSubset.Subset.ssubset_of_mem_notMem`. The former is applied below.
   * Loogle and LeanSearch queries for the custom separable/positive-semidefinite/
     block-positive chain found no exact theorem. -/

namespace D5.S3.Resource.CompositeCones.StrictChain

open D5.S3.Resource.CompositeCones
open D5.S3.Resource.CompositeConeProperness
open scoped ComplexOrder

/-- On two two-dimensional factors, the separable cone is a proper subset of the
positive-semidefinite cone, which is a proper subset of the block-positive cone.
The final conjunct exposes the product-vector criterion defining the last cone. -/
theorem strict_composite_cone_chain_and_block_criterion :
    ({W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ | separableCone W} ⊂
        {W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ | W.PosSemidef}) ∧
      ({W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ | W.PosSemidef} ⊂
        {W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ | blockPositive W}) ∧
      ∀ W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        blockPositive W ↔
          ∀ (a : Fin 2 → ℂ) (b : Fin 2 → ℂ),
            0 ≤ RCLike.re
              (dotProduct (star (fun ij : Fin 2 × Fin 2 => a ij.1 * b ij.2))
                (Matrix.mulVec W (fun ij : Fin 2 × Fin 2 => a ij.1 * b ij.2))) := by
  constructor
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, ?_⟩
    · intro W hW
      exact separable_isPosSemidef hW
    · obtain ⟨W, hW, hnot⟩ := exists_posSemidef_not_separable
      exact ⟨W, hW, hnot⟩
  constructor
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, ?_⟩
    · intro W hW
      exact posSemidef_blockPositive hW
    · obtain ⟨W, hW, hnot⟩ := exists_blockPositive_not_posSemidef
      exact ⟨W, hW, hnot⟩
  intro W
  rfl

example : Nonempty (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := ⟨0⟩

#print axioms strict_composite_cone_chain_and_block_criterion

end D5.S3.Resource.CompositeCones.StrictChain
