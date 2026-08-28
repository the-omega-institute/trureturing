/- GID: D5/S3/Observer/MetricGeometryLaws/ObserverUltrametricThresholdClosure
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/ObserverUltrametricThresholdClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounded ultrametric readouts induce an ultrapseudometric with equivalence thresholds. -/

/- Library-search audit trail (2026-08-28):
   * Repository searches found finite weighted and itinerary ultrametrics, but no existing
     primitive for the source's arbitrary observer-set supremum distance.
   * A body-shape search for `sSup (Set.range` and equivalent observer-distance forms had no
     D5 hit, so the source distance is constructed publicly with a `let` rather than named anew.
   * Pinned Mathlib supplies `le_csSup`, `csSup_le`, `Real.sSup_empty`, and the pseudometric
     self-distance, symmetry, and nonnegativity laws; all are applied directly below. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.ObserverUltrametricThresholdClosure

/-- A bounded ultrametric on the readout carrier induces the source observer supremum
ultrapseudometric. Its nonnegative threshold kernels are equivalence relations, including for
an empty observer set, where the real supremum is zero. -/
theorem observer_ultrametric_threshold_closure
    {P X Lambda : Type*} [PseudoMetricSpace Lambda]
    (Q : Set P) (readout : P -> X -> Lambda)
    (bounded : forall a b : Lambda, dist a b <= 1)
    (strongTriangle : forall a b c : Lambda,
      dist a c <= max (dist a b) (dist b c)) :
    let dQ := fun x y : X =>
      sSup (Set.range fun p : Q => dist (readout p.1 x) (readout p.1 y))
    let thresholdKernel := fun epsilon : NNReal => fun x y : X =>
      dQ x y <= (epsilon : Real)
    (forall x y, 0 <= dQ x y) /\
      (forall x, dQ x x = 0) /\
      (forall x y, dQ x y = dQ y x) /\
      (forall x y z, dQ x z <= max (dQ x y) (dQ y z)) /\
      (forall epsilon, Equivalence (thresholdKernel epsilon)) := by
  let dQ := fun x y : X =>
    sSup (Set.range fun p : Q => dist (readout p.1 x) (readout p.1 y))
  let thresholdKernel := fun epsilon : NNReal => fun x y : X =>
    dQ x y <= (epsilon : Real)
  change
    (forall x y, 0 <= dQ x y) /\
      (forall x, dQ x x = 0) /\
      (forall x y, dQ x y = dQ y x) /\
      (forall x y z, dQ x z <= max (dQ x y) (dQ y z)) /\
      (forall epsilon, Equivalence (thresholdKernel epsilon))
  have rangeBounded (x y : X) :
      BddAbove (Set.range fun p : Q => dist (readout p.1 x) (readout p.1 y)) := by
    refine ⟨1, ?_⟩
    rintro value ⟨p, rfl⟩
    exact bounded _ _
  have dQNonnegative : forall x y, 0 <= dQ x y := by
    intro x y
    by_cases hQ : Q.Nonempty
    · obtain ⟨p, hp⟩ := hQ
      exact (dist_nonneg.trans
        (le_csSup (rangeBounded x y)
          ⟨⟨p, hp⟩, rfl⟩))
    · letI : IsEmpty Q :=
        ⟨fun p => hQ ⟨p.1, p.2⟩⟩
      simp [dQ, Set.range_eq_empty]
  have dQSelf : forall x, dQ x x = 0 := by
    intro x
    by_cases hQ : Q.Nonempty
    · obtain ⟨p, hp⟩ := hQ
      have rangeSelf :
          Set.range (fun p : Q => dist (readout p.1 x) (readout p.1 x)) = {0} := by
        ext value
        constructor
        · rintro ⟨index, rfl⟩
          simp
        · intro hvalue
          have : value = 0 := by simpa using hvalue
          subst value
          exact ⟨⟨p, hp⟩, by simp⟩
      change sSup
        (Set.range fun p : Q => dist (readout p.1 x) (readout p.1 x)) = 0
      rw [rangeSelf, csSup_singleton]
    · letI : IsEmpty Q :=
        ⟨fun p => hQ ⟨p.1, p.2⟩⟩
      simp [dQ, Set.range_eq_empty]
  have dQSymmetric : forall x y, dQ x y = dQ y x := by
    intro x y
    apply congrArg sSup
    ext value
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, dist_comm _ _⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, dist_comm _ _⟩
  have dQStrongTriangle : forall x y z,
      dQ x z <= max (dQ x y) (dQ y z) := by
    intro x y z
    by_cases hQ : Q.Nonempty
    · obtain ⟨p, hp⟩ := hQ
      apply csSup_le
      · exact ⟨dist (readout p x) (readout p z), ⟨⟨p, hp⟩, rfl⟩⟩
      · rintro value ⟨index, rfl⟩
        exact (strongTriangle _ _ _).trans
          (max_le_max
            (le_csSup (rangeBounded x y) ⟨index, rfl⟩)
            (le_csSup (rangeBounded y z) ⟨index, rfl⟩))
    · letI : IsEmpty Q :=
        ⟨fun p => hQ ⟨p.1, p.2⟩⟩
      simp [dQ, Set.range_eq_empty]
  have kernelEquivalence : forall epsilon,
      Equivalence (thresholdKernel epsilon) := by
    intro epsilon
    constructor
    · intro x
      change dQ x x <= (epsilon : Real)
      rw [dQSelf]
      exact epsilon.coe_nonneg
    · intro x y hxy
      change dQ x y <= (epsilon : Real) at hxy
      change dQ y x <= (epsilon : Real)
      rwa [dQSymmetric]
    · intro x y z hxy hyz
      change dQ x y <= (epsilon : Real) at hxy
      change dQ y z <= (epsilon : Real) at hyz
      change dQ x z <= (epsilon : Real)
      exact (dQStrongTriangle x y z).trans (max_le hxy hyz)
  exact ⟨dQNonnegative, dQSelf, dQSymmetric, dQStrongTriangle, kernelEquivalence⟩

#print axioms observer_ultrametric_threshold_closure

end D5.S3.Observer.MetricGeometryLaws.ObserverUltrametricThresholdClosure
