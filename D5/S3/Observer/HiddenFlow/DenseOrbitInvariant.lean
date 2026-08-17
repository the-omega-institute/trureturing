/- GID: D5/S3/Observer/HiddenFlow/DenseOrbitInvariant
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/DenseOrbitInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A continuous observable invariant on a dense forward orbit is constant. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches found dense-orbit theorems but no equivalent D5
     declaration for continuous invariant observables.
   * Pinned-Mathlib and smart-search queries found no theorem combining
     forward iteration, invariance, and a dense orbit.
   * Mathlib's `Continuous.ext_on` exactly supplies equality extension from a
     dense set; it is applied after invariance is propagated along the orbit.
-/

import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Separation.Hausdorff

namespace D5.S3.Observer.HiddenFlow.DenseOrbitInvariant

/-- A continuous observable into a Hausdorff space that is invariant under an
update with a dense forward orbit is constant. This is the topological core of
the dense-fiber kernel characterization in residual theorem 6.31. -/
theorem continuous_invariant_of_dense_orbit_constant
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (step : X → X) (observable : X → Y) (x0 : X)
    (hcontinuous : Continuous observable)
    (hdense : DenseRange (fun n : ℕ => (step^[n]) x0))
    (hinvariant : ∀ x, observable (step x) = observable x) :
    ∀ x, observable x = observable x0 := by
  have horbit : ∀ n : ℕ, observable ((step^[n]) x0) = observable x0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hinvariant _).trans ih
  have heqOn :
      Set.EqOn observable (fun _ : X => observable x0)
        (Set.range fun n : ℕ => (step^[n]) x0) := by
    rintro _ ⟨n, rfl⟩
    exact horbit n
  have hall : observable = fun _ : X => observable x0 :=
    Continuous.ext_on hdense hcontinuous continuous_const heqOn
  exact fun x => congrFun hall x

#print axioms continuous_invariant_of_dense_orbit_constant

end D5.S3.Observer.HiddenFlow.DenseOrbitInvariant
