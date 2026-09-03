/- GID: D5/S1/Dynamics/UniversalSolenoidCoordinate
   generality: I
   mirror-B: D5/B/S1/Dynamics/UniversalSolenoidCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scaling a solenoid coordinate by its own index returns the visible projection. -/

import D5.S1.Dynamics.UniversalSolenoid

namespace D5.S1.Dynamics

namespace UniversalSolenoid

/-- Scaling the index-`m` coordinate of a compatible family by `m` returns the
visible projection.  This is the defining compatibility field read at index `1`,
and it holds at every point, with no hypothesis on the projection.

The value here is an API one, not mathematical novelty.  Three frozen modules
re-derive the `projection theta = 0` special case as a private declaration; this
is the unconditional statement those copies are instances of.  Those frozen
copies stay where they are and cannot import this module, so nothing existing is
removed here; the public name only keeps a fourth private copy from being
written. -/
@[simp] theorem nsmul_coordinate_eq_projection (theta : UniversalSolenoid) (m : ℕ+) :
    m.1 • theta.1 m = projection theta := by
  have h := theta.2 ⟨1, Nat.zero_lt_one⟩ m
  simp only [one_mul] at h
  exact h

/-- The special case that the private copies state: a point with vanishing
projection has every coordinate killed by its own index. -/
theorem nsmul_coordinate_eq_zero {theta : UniversalSolenoid}
    (htheta : projection theta = 0) (m : ℕ+) : m.1 • theta.1 m = 0 := by
  rw [nsmul_coordinate_eq_projection, htheta]

end UniversalSolenoid

end D5.S1.Dynamics
