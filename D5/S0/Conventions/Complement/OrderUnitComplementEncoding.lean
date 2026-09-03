/- GID: D5/S0/Conventions/Complement/OrderUnitComplementEncoding
   generality: G
   mirror-B: D5/B/S0/Conventions/Complement/OrderUnitComplementEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effect-interval subtraction complement encodes its order-unit total. -/

/- Library-search audit trail (2026-09-04):
   * The repository source of truth is `ComplementEncoding.complement`; it is imported directly.
   * The frozen `ComplementEncoding.complement_encoding` supplies the two endpoints and involution.
   * `OrderUnitAmbientDependence` establishes the local ordered-module, order-unit-domination, and
     `Set.Icc` carrier convention used here; pinned Mathlib has no `OrderUnit` predicate.
   * Loogle found `sub_sub_self` and `const_sub_involutive`; GitHub Lean code search found no
     reusable ordered-vector-space order-unit predicate. No subtraction identity is reproved. -/

import D5.S0.Conventions.ComplementEncoding
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.Complement.OrderUnitComplementEncoding

open D5.S0.Conventions.ComplementEncoding

/-- In a real ordered vector space, subtraction complement on the effect interval has both
endpoint values, is involutive, and recovers its order-unit total by evaluation at zero. -/
theorem order_unit_complement_encoding
    {V : Type*}
    [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V]
    [Module ℝ V] [IsOrderedModule ℝ V]
    (u e : V)
    (hOrderUnit : 0 ≤ u ∧ ∀ x : V, ∃ r : ℝ,
      0 < r ∧ (-r) • u ≤ x ∧ x ≤ r • u)
    (he : e ∈ Set.Icc (0 : V) u) :
    complement u 0 = u ∧
      complement u u = 0 ∧
        complement u (complement u e) = e ∧
          u = complement u 0 := by
  let typedOrderUnit : {x : V // 0 ≤ x ∧ ∀ y : V, ∃ r : ℝ,
      0 < r ∧ (-r) • x ≤ y ∧ y ≤ r • x} := ⟨u, hOrderUnit⟩
  let typedEffect : Set.Icc (0 : V) (typedOrderUnit : V) :=
    ⟨e, by simpa [typedOrderUnit] using he⟩
  have h := complement_encoding (typedOrderUnit : V) (typedEffect : V)
  change
    complement (typedOrderUnit : V) 0 = (typedOrderUnit : V) ∧
      complement (typedOrderUnit : V) (typedOrderUnit : V) = 0 ∧
        complement (typedOrderUnit : V)
          (complement (typedOrderUnit : V) (typedEffect : V)) = (typedEffect : V) ∧
          (typedOrderUnit : V) = complement (typedOrderUnit : V) 0
  exact And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.1.symm))

/- The public carrier and all four conclusions are jointly inhabited at `V = ℝ`, `u = 1`,
and the non-endpoint effect `e = 1 / 2`. -/
example :
    ∃ u e : ℝ,
      (0 ≤ u ∧ ∀ x : ℝ, ∃ r : ℝ,
        0 < r ∧ (-r) • u ≤ x ∧ x ≤ r • u) ∧
      e ∈ Set.Icc (0 : ℝ) u ∧
      (complement u 0 = u ∧
        complement u u = 0 ∧
        complement u (complement u e) = e ∧
        u = complement u 0) := by
  let u : ℝ := 1
  let e : ℝ := 1 / 2
  have hOrderUnit : 0 ≤ u ∧ ∀ x : ℝ, ∃ r : ℝ,
      0 < r ∧ (-r) • u ≤ x ∧ x ≤ r • u := by
    constructor
    · simp [u]
    · intro x
      refine ⟨abs x + 1, add_pos_of_nonneg_of_pos (abs_nonneg x) zero_lt_one, ?_, ?_⟩
      · simpa only [u, smul_eq_mul, mul_one] using
          (show -(abs x + 1) ≤ x from
            (neg_le_neg (le_add_of_nonneg_right zero_le_one)).trans (neg_abs_le x))
      · simpa only [u, smul_eq_mul, mul_one] using
          ((le_abs_self x).trans (le_add_of_nonneg_right zero_le_one))
  have he : e ∈ Set.Icc (0 : ℝ) u := by
    rw [Set.mem_Icc]
    constructor
    · change (0 : ℝ) ≤ 1 / 2
      norm_num
    · change (1 / 2 : ℝ) ≤ 1
      simpa using
        (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
          (show (1 : ℝ) ≤ 2 by norm_num))
  exact ⟨u, e, hOrderUnit, he, order_unit_complement_encoding u e hOrderUnit he⟩

/- Reverse probe for A4: the public result itself exposes recovery of the total at zero. -/
example
    {V : Type*}
    [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V]
    [Module ℝ V] [IsOrderedModule ℝ V]
    (u e : V)
    (hOrderUnit : 0 ≤ u ∧ ∀ x : V, ∃ r : ℝ,
      0 < r ∧ (-r) • u ≤ x ∧ x ≤ r • u)
    (he : e ∈ Set.Icc (0 : V) u) :
    u = complement u 0 :=
  (order_unit_complement_encoding u e hOrderUnit he).2.2.2

/- The zero total is not an order unit of the nontrivial ordered vector space `ℝ`. -/
example :
    ¬ (0 ≤ (0 : ℝ) ∧ ∀ x : ℝ, ∃ r : ℝ,
      0 < r ∧ (-r) • (0 : ℝ) ≤ x ∧ x ≤ r • (0 : ℝ)) := by
  rintro ⟨_, hDominates⟩
  obtain ⟨r, _, _, hRight⟩ := hDominates 1
  have hNot : ¬ ((1 : ℝ) ≤ 0) := by norm_num
  exact hNot (by simpa only [smul_eq_mul, mul_zero] using hRight)

#print axioms order_unit_complement_encoding

end D5.S0.Conventions.Complement.OrderUnitComplementEncoding
