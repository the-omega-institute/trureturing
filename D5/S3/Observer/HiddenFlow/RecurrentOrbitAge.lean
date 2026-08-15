/- GID: D5/S3/Observer/HiddenFlow/RecurrentOrbitAge
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/RecurrentOrbitAge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A recurrent real flow orbit admits no continuous clock equal to elapsed time. -/

import Mathlib.Dynamics.Flow
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed

/- Library-search audit trail (2026-08-15):
   * Repository and formalization-receipt searches found no equal or stronger
     recurrent-orbit theorem excluding a continuous real-valued age function.
   * Loogle found the exact supporting declarations `Continuous.tendsto`,
     `Filter.Tendsto.eventually`, and `Filter.Tendsto.congr'`; all are applied below.
   * LeanSearch found the exact contradiction theorem
     `not_tendsto_atTop_of_tendsto_nhds`, which is imported and applied below.
   * Full-statement Loogle and LeanSearch queries returned only generic flow-orbit
     declarations, not a theorem combining recurrence with clock nonexistence. -/

open Filter
open scoped Topology

namespace D5.S3.Observer.HiddenFlow.RecurrentOrbitAge

/-- If a real flow orbit returns to its initial point along times tending to
positive infinity, no continuous real-valued function can read every
nonnegative orbit time exactly. -/
theorem recurrent_orbit_has_no_continuous_age
    {X : Type*} [TopologicalSpace X]
    (flow : Flow ℝ X) (x₀ : X) (times : ℕ → ℝ)
    (htop : Tendsto times atTop atTop)
    (hrec : Tendsto (fun n => flow (times n) x₀) atTop (𝓝 x₀)) :
    ¬ ∃ age : X → ℝ,
      Continuous age ∧
        ∀ t, 0 ≤ t → age (flow t x₀) = t := by
  rintro ⟨age, hage, hclock⟩
  have hageLimit :
      Tendsto (fun n => age (flow (times n) x₀)) atTop (𝓝 (age x₀)) :=
    hage.continuousAt.tendsto.comp hrec
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ times n :=
    htop.eventually (eventually_ge_atTop 0)
  have heq :
      (fun n => age (flow (times n) x₀)) =ᶠ[atTop] times :=
    hnonneg.mono fun n hn => hclock (times n) hn
  have hageTop :
      Tendsto (fun n => age (flow (times n) x₀)) atTop atTop :=
    htop.congr' heq.symm
  exact (not_tendsto_atTop_of_tendsto_nhds hageLimit) hageTop

example : Unit := ()

example :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (Flow.id ℝ Unit) (n : ℝ) ())
        atTop (𝓝 ()) := by
  constructor
  · exact tendsto_natCast_atTop_atTop
  · exact tendsto_const_nhds

#print axioms recurrent_orbit_has_no_continuous_age

end D5.S3.Observer.HiddenFlow.RecurrentOrbitAge
