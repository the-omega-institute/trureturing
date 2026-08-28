/- GID: D5/S3/Arith/Lattices/FiveModularLatticeSimilarity
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/FiveModularLatticeSimilarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Lambda-squared A4 lattice is five-modular under its Hodge map. -/

/- Library-search audit trail (2026-08-28):
* Searches for five-modular lattices, dual-lattice similarities, the concrete Gram row, and the
  determinant 125 found the frozen family owner
  `D5.S3.Arith.Lattices.ExactDualLatticeFormula`. This module imports its exact lattice, dual,
  Gram form, Hodge map, and dual-image theorem instead of redeclaring any of them.
* That frozen theorem proves only `L# = (J / 5)L`; it does not state injectivity, Gram scaling,
  dimension, or either determinant clause, so it is not an exact bind target for this atom.
* Pinned Mathlib has general dual-submodule and lattice-covolume infrastructure but no theorem for
  this concrete six-dimensional five-modular lattice. The remaining closed matrix identities are
  verified directly on the imported source matrices.
-/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula

namespace D5.S3.Arith.Lattices.FiveModularLatticeSimilarity

open D5.S3.Arith.Lattices.ExactDualLatticeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

private lemma hodge_after_one_fifth (x : AmbientSpace) :
    hodgeMatrix.mulVec (oneFifthHodgeMap x) = x := by
  funext i
  fin_cases i <;>
    simp [oneFifthHodgeMap, oneFifthHodgeMatrix, hodgeMatrix, integralHodgeMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private lemma one_fifth_hodge_injective : Function.Injective oneFifthHodgeMap := by
  intro x y hxy
  have h := congrArg (fun z => hodgeMatrix.mulVec z) hxy
  simpa only [hodge_after_one_fifth] using h

set_option maxHeartbeats 1000000 in
-- Expanding both concrete six-coordinate vectors and their Gram pairing needs a larger local bound.
private lemma one_fifth_hodge_gram_scaling (x y : AmbientSpace) :
    gramForm (oneFifthHodgeMap x) (oneFifthHodgeMap y) =
      (1 / 5 : ℝ) * gramForm x y := by
  simp [gramForm, gramMatrix, integralGramMatrix, oneFifthHodgeMap,
    oneFifthHodgeMatrix, hodgeMatrix, integralHodgeMatrix, Matrix.toBilin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/- **Five-modularity of `Lambda^2 A4`.** The canonical `J / 5` map identifies the exact dual
lattice, is injective, and scales the Gram pairing by `1 / 5`. The same public statement records
the six-dimensional carrier and both determinant forms forced by five-modularity. -/
set_option maxHeartbeats 1000000 in
-- Kernel reduction of both closed six-by-six determinant clauses needs a larger local bound.
set_option maxRecDepth 10000 in
-- The determinant decision procedure recursively unfolds all six finite dimensions.
theorem five_modular_lattice_similarity :
    dualLattice = oneFifthHodgeLattice ∧
      Function.Injective oneFifthHodgeMap ∧
      (∀ x y : AmbientSpace,
        gramForm (oneFifthHodgeMap x) (oneFifthHodgeMap y) =
          (1 / 5 : ℝ) * gramForm x y) ∧
      Module.finrank ℝ AmbientSpace = 6 ∧
      integralGramMatrix.det = (5 : ℤ) ^ 3 ∧
      integralGramMatrix.det = (5 : ℤ) ^ (6 / 2) := by
  refine ⟨dual_lattice_eq_one_fifth_hodge_lattice, one_fifth_hodge_injective,
    one_fifth_hodge_gram_scaling, ?_, ?_, ?_⟩
  · simp [AmbientSpace]
  · decide
  · decide

#print axioms five_modular_lattice_similarity

end D5.S3.Arith.Lattices.FiveModularLatticeSimilarity
