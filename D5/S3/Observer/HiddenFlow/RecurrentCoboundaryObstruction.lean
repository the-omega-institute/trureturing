/- GID: D5/S3/Observer/HiddenFlow/RecurrentCoboundaryObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/RecurrentCoboundaryObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A cocycle nonzero along a recurrent orbit is not a continuous coboundary. -/

import Mathlib.Dynamics.Flow
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real

/- Library-search audit trail (2026-08-18):
   * Repository searches for `coboundary`, recurrent cocycles, and equivalent `Tendsto`
     statements found no equal or stronger D5 theorem.
   * Loogle found `Continuous.tendsto` and `Filter.Tendsto.sub_const`; both exact
     supporting declarations are applied below. Full-statement searches found no match.
   * Pinned-Mathlib searches for `coboundary`, `cocycle`, and `recurrent` found only
     unrelated algebraic-cohomology declarations, not this topological obstruction.
   * LeanSearch's `/api/search` endpoint returned HTTP 404, so it yielded no result. -/

open Filter
open scoped Topology

namespace D5.S3.Observer.HiddenFlow.RecurrentCoboundaryObstruction

/-- If an orbit returns to its initial point along times tending to positive infinity while a
cocycle does not tend to zero there, the cocycle cannot be a continuous coboundary. -/
theorem recurrent_cocycle_not_continuous_coboundary
    {X V : Type*} [TopologicalSpace X] [AddGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V]
    (flow : Flow ℝ X) (cocycle : ℝ → X → V) (x : X) (times : ℕ → ℝ)
    (_htimes : Tendsto times atTop atTop)
    (hrecur : Tendsto (fun n => flow (times n) x) atTop (𝓝 x))
    (hnonzero : ¬ Tendsto (fun n => cocycle (times n) x) atTop (𝓝 0)) :
    ¬ ∃ h : X → V, Continuous h ∧
      ∀ t y, cocycle t y = h (flow t y) - h y := by
  rintro ⟨h, hcontinuous, hcoboundary⟩
  apply hnonzero
  have horbit :
      Tendsto (fun n => h (flow (times n) x)) atTop (𝓝 (h x)) :=
    (hcontinuous.tendsto x).comp hrecur
  rw [show (fun n => cocycle (times n) x) =
      (fun n => h (flow (times n) x) - h x) by
    funext n
    exact hcoboundary (times n) x]
  simpa using horbit.sub_const (h x)

example :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop ∧
      Tendsto (fun _ : ℕ => ()) atTop (𝓝 ()) ∧
        ¬ Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 0) := by
  refine ⟨tendsto_natCast_atTop_atTop, tendsto_const_nhds, ?_⟩
  intro hzero
  exact (not_tendsto_atTop_of_tendsto_nhds hzero) tendsto_natCast_atTop_atTop

#print axioms recurrent_cocycle_not_continuous_coboundary

end D5.S3.Observer.HiddenFlow.RecurrentCoboundaryObstruction
