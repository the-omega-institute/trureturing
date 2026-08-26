/- GID: D5/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition
   generality: I
   mirror-B: D5/B/S1/Solenoid/Connectivity/CoordinateStreamlineDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every compact real-interval solenoid path has one compatible coordinate offset family. -/

/- Library-search audit trail (2026-08-26):
   * `IntervalStreamlineDecomposition.exists_interval_streamline_decomposition`
     is the frozen repository theorem supplying the real lift and kernel offset.
   * Pinned Mathlib's `iccHomeoI` is the exact affine homeomorphism used to
     transport every nondegenerate real interval to the unit interval.
   * `ExactSequence.congruence_embedding_exact_projection` is the exact
     repository primitive identifying kernel offsets with compatible residues.
   * Pinned Mathlib has no universal-solenoid coordinate decomposition theorem.
-/

import D5.S1.Solenoid.ExactSequence
import D5.S1.Solenoid.IntervalStreamlineDecomposition
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Solenoid.Connectivity.CoordinateStreamlineDecomposition

open Set
open D5.S1.Dynamics
open D5.S1.Solenoid

/-- Every continuous path on a nonempty compact real interval is reconstructed
at each positive modulus by one continuous real lift and one time-independent
compatible residue family. -/
theorem exists_coordinate_streamline_decomposition
    (a b : Real) (hab : a ≤ b)
    (path : C(Set.Icc a b, UniversalSolenoid)) :
    ∃ visibleLift : C(Set.Icc a b, Real),
      ∃ compatibleOffset : ExactSequence.CongruenceData,
        ∀ (m : ℕ+) (t : Set.Icc a b),
          (path t).1 m =
            (((visibleLift t / m.1 : Real) : AddCircle (1 : Real)) +
              (ExactSequence.congruenceEmbedding compatibleOffset).1 m) := by
  have hinterval :
      ∃ visibleLift : C(Set.Icc a b, Real),
        ∃ hiddenOffset : UniversalSolenoid.projection.ker,
          ∀ t, path t =
            UniversalSolenoid.realFlow (visibleLift t) + hiddenOffset.1 := by
    rcases eq_or_lt_of_le hab with rfl | hab
    · let anchor : Set.Icc a a := ⟨a, le_rfl, le_rfl⟩
      let zero : Set.Icc (0 : Real) 1 := ⟨0, le_rfl, zero_le_one⟩
      let unitPath : C(Set.Icc (0 : Real) 1, UniversalSolenoid) :=
        ⟨fun _ => path anchor, continuous_const⟩
      rcases
          IntervalStreamlineDecomposition.exists_interval_streamline_decomposition unitPath with
        ⟨unitLift, hiddenOffset, hdecomposition⟩
      let visibleLift : C(Set.Icc a a, Real) :=
        ⟨fun _ => unitLift zero, continuous_const⟩
      refine ⟨visibleLift, hiddenOffset, ?_⟩
      intro t
      have ht : t = anchor := by
        apply Subtype.ext
        exact le_antisymm t.property.2 t.property.1
      simpa [ht, unitPath, visibleLift, anchor, zero] using hdecomposition zero
    · let unitPath : C(Set.Icc (0 : Real) 1, UniversalSolenoid) :=
        ⟨fun t => path ((iccHomeoI a b hab).symm t),
          path.continuous.comp (iccHomeoI a b hab).symm.continuous⟩
      rcases
          IntervalStreamlineDecomposition.exists_interval_streamline_decomposition unitPath with
        ⟨unitLift, hiddenOffset, hdecomposition⟩
      let visibleLift : C(Set.Icc a b, Real) :=
        ⟨fun t => unitLift (iccHomeoI a b hab t),
          unitLift.continuous.comp (iccHomeoI a b hab).continuous⟩
      refine ⟨visibleLift, hiddenOffset, ?_⟩
      intro t
      simpa [unitPath, visibleLift] using hdecomposition (iccHomeoI a b hab t)
  rcases hinterval with
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
