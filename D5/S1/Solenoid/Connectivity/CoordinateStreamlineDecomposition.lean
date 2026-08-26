/- GID: D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition
   generality: I
   mirror-B: D5/B/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every interval solenoid path has one compatible coordinate offset family. -/

/- Library-search audit trail (2026-08-26):
   * `IntervalStreamlineDecomposition.exists_interval_streamline_decomposition`
     is the frozen repository theorem supplying the real lift and kernel offset.
   * `ExactSequence.congruence_embedding_exact_projection` is the exact
     repository primitive identifying kernel offsets with compatible residues.
   * Pinned Mathlib has no universal-solenoid coordinate decomposition theorem.
-/

import D5.S1.Solenoid.ExactSequence
import D5.S1.Solenoid.IntervalStreamlineDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Solenoid.Connectivity.CoordinateStreamlineDecomposition

open Set
open D5.S1.Dynamics
open D5.S1.Solenoid

/-- Every continuous unit-interval solenoid path is reconstructed at each
positive modulus by one continuous real lift and one time-independent
compatible residue family. -/
theorem exists_coordinate_streamline_decomposition
    (path : C(Set.Icc (0 : Real) 1, UniversalSolenoid)) :
    ∃ visibleLift : C(Set.Icc (0 : Real) 1, Real),
      ∃ compatibleOffset : ExactSequence.CongruenceData,
        ∀ (m : ℕ+) (t : Set.Icc (0 : Real) 1),
          (path t).1 m =
            (((visibleLift t / m.1 : Real) : AddCircle (1 : Real)) +
              (ExactSequence.congruenceEmbedding compatibleOffset).1 m) := by
  rcases
      IntervalStreamlineDecomposition.exists_interval_streamline_decomposition path with
    ⟨visibleLift, hiddenOffset, hdecomposition⟩
  rcases
      (ExactSequence.congruence_embedding_exact_projection hiddenOffset.1).mp
        hiddenOffset.property with
    ⟨compatibleOffset, hoffset⟩
  refine ⟨visibleLift, compatibleOffset, ?_⟩
  intro m t
  have hcoordinate :=
    congrArg (fun theta : UniversalSolenoid => theta.1 m) (hdecomposition t)
  change (path t).1 m =
    (((visibleLift t / m.1 : Real) : AddCircle (1 : Real)) + hiddenOffset.1.1 m)
    at hcoordinate
  simpa [hoffset] using hcoordinate

#print axioms exists_coordinate_streamline_decomposition

end D5.S1.Solenoid.Connectivity.CoordinateStreamlineDecomposition
