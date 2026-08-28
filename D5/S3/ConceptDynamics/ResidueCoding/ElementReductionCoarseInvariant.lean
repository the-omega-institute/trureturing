/- GID: D5/S3/ConceptDynamics/ResidueCoding/ElementReductionCoarseInvariant
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ResidueCoding/ElementReductionCoarseInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime reductions separate integral matrices while coarse invariants merge them. -/

import D5.S0.Observation.PowerTraceSimilarityCountermodel
import Mathlib.Algebra.Field.ZMod

/- Library-search audit trail (2026-08-26):
   * Exact current-tree searches for prime reductions that remain distinct while
     trace or characteristic polynomial agrees at every prime found no D5 theorem.
   * Exact D5 hit `power_traces_do_not_determine_similarity` supplies the canonical
     zero/nilpotent matrix pair and its equal-trace and equal-charpoly facts over
     every field; it is imported and applied to each prime residue field.
   * Body-shape searches for `Matrix.single 0 1 1`, entrywise maps through
     `Int.castRingHom (ZMod p)`, and prime-indexed matrix invariants found no D5
     prime-reduction bridge, so no existing family primitive is redeclared.
   * Pinned Mathlib's `Int.castRingHom`, `Matrix.map`, and prime-field instance for
     `ZMod p` are the canonical entrywise reduction construction used directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ResidueCoding.ElementReductionCoarseInvariant

open D5.S0.Observation.PowerTraceSimilarityCountermodel
open Polynomial

/-- Two distinct integral matrices have different entrywise reductions at every
prime, while the trace and characteristic polynomial extracted from those same
reductions agree at every prime. Thus arbitrarily many prime coordinates do not
make these coarser local properties faithful. -/
theorem element_reduction_coarse_invariant_fork :
    let zeroMatrix : Matrix (Fin 2) (Fin 2) Int := 0
    let nilpotentMatrix : Matrix (Fin 2) (Fin 2) Int := Matrix.single 0 1 1
    zeroMatrix ≠ nilpotentMatrix ∧
      ∀ p : Nat, p.Prime →
        let reduction := Int.castRingHom (ZMod p)
        zeroMatrix.map reduction ≠ nilpotentMatrix.map reduction ∧
          Matrix.trace (zeroMatrix.map reduction) =
              Matrix.trace (nilpotentMatrix.map reduction) ∧
          (zeroMatrix.map reduction).charpoly =
            (nilpotentMatrix.map reduction).charpoly := by
  dsimp only
  constructor
  · intro sameMatrix
    have sameEntry := congrFun (congrFun sameMatrix 0) 1
    simp at sameEntry
  · intro p prime
    letI : Fact (Nat.Prime p) := ⟨prime⟩
    have countermodel :=
      power_traces_do_not_determine_similarity (K := ZMod p)
    dsimp only at countermodel
    have distinctReductions :
        (0 : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠
          Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod p) := by
      intro sameMatrix
      have sameEntry := congrFun (congrFun sameMatrix 0) 1
      simp at sameEntry
    have equalTraces :
        Matrix.trace (0 : Matrix (Fin 2) (Fin 2) (ZMod p)) =
          Matrix.trace
            (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod p)) := by
      simpa only [pow_one] using (countermodel.1 1 (by omega)).1.trans
        (countermodel.1 1 (by omega)).2.symm
    have equalCharacteristicPolynomials :
        (0 : Matrix (Fin 2) (Fin 2) (ZMod p)).charpoly =
          (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod p)).charpoly :=
      countermodel.2.1.trans countermodel.2.2.1.symm
    have reducedZero :
        (0 : Matrix (Fin 2) (Fin 2) Int).map
            (Int.castRingHom (ZMod p)) =
          (0 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      ext i j
      simp
    have reducedNilpotent :
        (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : Int)).map
            (Int.castRingHom (ZMod p)) =
          Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod p) := by
      ext i j
      simp [Matrix.single_apply]
    rw [reducedZero, reducedNilpotent]
    exact ⟨distinctReductions, equalTraces, equalCharacteristicPolynomials⟩

#print axioms element_reduction_coarse_invariant_fork

end D5.S3.ConceptDynamics.ResidueCoding.ElementReductionCoarseInvariant
