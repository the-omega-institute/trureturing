/- GID: D5/S3/Observer/CenterOperational
   generality: G
   mirror-B: D5/B/S3/Observer/CenterOperational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the cyclic-window operational center by constant observables. -/

import D5.S3.Observer.ObserverMetric

namespace D5.S3.Observer.CenterOperational

open D5.S3.Observer.ObserverMetric

/-- On a nonempty cyclic window, zero perturbation is equivalent to being a constant observable. -/
theorem center_iff_const {M : ℕ} [NeZero M] (f : ZMod M → ℂ) :
    perturbationSeminorm (Equiv.addRight (1 : ZMod M)) f = 0 ↔
      ∃ c : ℂ, f = Function.const (ZMod M) c := by
  rw [perturbationSeminorm_eq_zero_iff,
    ← updateDefect_eq_zero_iff_invariant]
  exact invariant_iff_const_on_cyclic_window f

end D5.S3.Observer.CenterOperational
