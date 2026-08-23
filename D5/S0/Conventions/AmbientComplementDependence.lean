/- GID: D5/S0/Conventions/AmbientComplementDependence
   generality: G
   mirror-B: D5/B/S0/Conventions/AmbientComplementDependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Make subtraction complement determine and depend on its ambient total. -/

/- Library-search audit trail (2026-08-22):
   * The repository family source of truth is
     `D5.S0.Conventions.ComplementEncoding.complement`; it is imported and used directly.
   * The exact repository theorem `ComplementEncoding.complement_encoding` recovers the ambient
     total from the whole complement operation and is applied directly below.
   * Pinned Mathlib and repository searches found no `OrderUnit` or `IsOrderUnit` predicate.
     The cancellation lemma `sub_left_inj` handles dependence at a fixed argument. -/

import D5.S0.Conventions.ComplementEncoding
import Mathlib.Algebra.Group.Int.Defs

namespace D5.S0.Conventions.AmbientComplementDependence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A subtraction complement has no ambient-free value or operation: equality at any fixed
argument, and equality of the whole operations, are each equivalent to equality of their
explicitly supplied ambient totals. -/
theorem absolute_complement_requires_ambient_total
    {G : Type*} [AddCommGroup G] (u v e : G) :
    (D5.S0.Conventions.ComplementEncoding.complement u e =
        D5.S0.Conventions.ComplementEncoding.complement v e ↔ u = v) ∧
      (((fun x : G => D5.S0.Conventions.ComplementEncoding.complement u x) =
          fun x : G => D5.S0.Conventions.ComplementEncoding.complement v x) ↔ u = v) := by
  constructor
  · simp only [D5.S0.Conventions.ComplementEncoding.complement, sub_left_inj]
  · constructor
    · intro h
      have hvu : v = u :=
        (D5.S0.Conventions.ComplementEncoding.complement_encoding u e).2.2.2 v (by
          simpa only [D5.S0.Conventions.ComplementEncoding.complement] using h.symm)
      exact hvu.symm
    · rintro rfl
      rfl

/- Integer totals witness that changing the ambient total changes both outputs and operations. -/
example :
    D5.S0.Conventions.ComplementEncoding.complement (1 : ℤ) 0 ≠
        D5.S0.Conventions.ComplementEncoding.complement 2 0 ∧
      (fun x : ℤ => D5.S0.Conventions.ComplementEncoding.complement 1 x) ≠
        fun x : ℤ => D5.S0.Conventions.ComplementEncoding.complement 2 x := by
  constructor
  · decide
  · intro h
    have h0 := congrFun h 0
    exact (by decide :
      D5.S0.Conventions.ComplementEncoding.complement (1 : ℤ) 0 ≠
        D5.S0.Conventions.ComplementEncoding.complement 2 0) h0

#print axioms absolute_complement_requires_ambient_total

end D5.S0.Conventions.AmbientComplementDependence
