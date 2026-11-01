/- GID: D5/S3/Geometry/Hyperideal/S4OppositePairKernelClassification
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/S4OppositePairKernelClassification
   mirror-E: none(waiver:finite-s4-kernel-classification)
   anchors: []
   utility: none
   digest: The kernel of the finite action on the three opposite edge pairs is exactly the Klein four set. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25023
The theorem is an exact finite action classification; the issue records the missing
four-slot realization and observational-sensitivity bridge.
-/

import D5.S3.Geometry.Hyperideal.S4OppositePairAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Geometry.Hyperideal.S4OppositePairKernelClassification

open D5.S3.Geometry.Hyperideal.S4OppositePairAction

instance pairActionDecidable (σ : Perm4) : Decidable (isTrivialPairAction σ) := by
  change Decidable (∀ p : Pair, inducedPairAction σ p = p)
  exact Fintype.decidableForallFintype

set_option maxHeartbeats 4000000 in
-- Exhaustive classification ranges over all vertex permutations and pair slots.
theorem trivial_pair_action_iff (σ : Perm4) :
    isTrivialPairAction σ ↔
      σ = (1 : Perm4) ∨ σ = doubleSwap01_23 ∨
        σ = doubleSwap02_13 ∨ σ = doubleSwap03_12 := by
  revert σ
  decide

end D5.S3.Geometry.Hyperideal.S4OppositePairKernelClassification
