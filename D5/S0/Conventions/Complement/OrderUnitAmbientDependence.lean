/- GID: D5/S0/Conventions/Complement/OrderUnitAmbientDependence
   generality: G
   mirror-B: D5/B/S0/Conventions/Complement/OrderUnitAmbientDependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Order-unit complements on effect intervals depend on their ambient totals. -/

/- Library-search audit trail (2026-08-23):
   * The repository family source of truth is
     `D5.S0.Conventions.ComplementEncoding.complement`; it is imported and used directly.
   * Pinned Mathlib searches found `IsOrderedModule` in
     `Mathlib/Algebra/Order/Module/Defs.lean`, `IsOrderedAddMonoid` in
     `Mathlib/Algebra/Order/Monoid/Defs.lean`, and `Set.Icc` interval membership in
     `Mathlib/Order/Interval/Set/Basic.lean`; these supply the ordered-vector-space carrier.
   * Exact-name and case-insensitive searches found no `OrderUnit` or `IsOrderUnit` predicate in
     pinned Mathlib. The standard two-sided scalar domination property is therefore an explicit
     named public hypothesis for each ambient total.
   * The exact Mathlib cancellation lemma `sub_left_inj` proves the dependence equivalence. -/

import D5.S0.Conventions.ComplementEncoding
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.Complement.OrderUnitAmbientDependence

open D5.S0.Conventions.ComplementEncoding

/-- On a real ordered vector space, complements of an effect relative to two explicitly supplied
order units differ exactly when the ambient order units differ. The two-sided domination binders
state the order-unit role directly because pinned Mathlib has no order-unit predicate. -/
theorem order_unit_complement_depends_on_ambient
    {V : Type*}
    [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V]
    [Module ℝ V] [IsOrderedModule ℝ V]
    (u v e : V)
    (_hOrderUnitU : 0 ≤ u ∧ ∀ x : V, ∃ r : ℝ,
      0 < r ∧ (-r) • u ≤ x ∧ x ≤ r • u)
    (_hOrderUnitV : 0 ≤ v ∧ ∀ x : V, ∃ r : ℝ,
      0 < r ∧ (-r) • v ≤ x ∧ x ≤ r • v)
    (_heU : e ∈ Set.Icc (0 : V) u)
    (_heV : e ∈ Set.Icc (0 : V) v) :
    complement u e ≠ complement v e ↔ u ≠ v := by
  simp only [complement, ne_eq, not_congr sub_left_inj]

/- The explicit order-unit and effect-interval hypotheses are jointly inhabited on the real line. -/
example :
    ((0 : ℝ) ≤ 1 ∧
      ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧ (-r) • (1 : ℝ) ≤ x ∧ x ≤ r • (1 : ℝ)) ∧
      (0 : ℝ) ∈ Set.Icc 0 1 := by
  constructor
  · constructor
    · exact zero_le_one
    · intro x
      refine ⟨abs x + 1, add_pos_of_nonneg_of_pos (abs_nonneg x) zero_lt_one, ?_, ?_⟩
      · simpa only [smul_eq_mul, mul_one] using
          (show -(abs x + 1) ≤ x from
            (neg_le_neg (le_add_of_nonneg_right zero_le_one)).trans (neg_abs_le x))
      · simpa only [smul_eq_mul, mul_one] using
          ((le_abs_self x).trans (le_add_of_nonneg_right zero_le_one))
  · exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩

#print axioms order_unit_complement_depends_on_ambient

end D5.S0.Conventions.Complement.OrderUnitAmbientDependence
