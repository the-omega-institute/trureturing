/- GID: D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf names enumerate an initial Fibonacci interval and its Euler sum. -/

import D5.S0.Tower.GoldenNames
import Mathlib.Algebra.Field.GeomSum

/-!
The source indexes its word by the largest allowed Fibonacci index `N`, while
`GoldenName Q` records the `Q = N - 1` positions from index two through `N`.
Consequently the source endpoint `Fib (N + 1)` is `Fib (Q + 2)` here.

Library-search audit trail (2026-09-02):
* D5 name and body-shape searches for a finite Zeckendorf interval bijection,
  its exponent computation, and the associated Euler sum found no whole owner.
  `D5.S0.Tower.GoldenNames.goldenNameEquiv` is the canonical equivalence and
  already constructs the source exponent map; this module imports it instead
  of introducing another encoding.
* Pinned Mathlib searches for Zeckendorf generating functions found no exact
  theorem. `Equiv.sum_comp`, `Fin.sum_univ_eq_sum_range`, and `geom_sum_eq`
  supply the generic reindexing and finite geometric-series steps.
* Installed non-Mathlib packages and GitHub Lean-code searches for finite
  Zeckendorf Euler identities found no equivalent declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.FiniteZeckendorfEulerIdentity

open D5.S0.Tower.GoldenNames
open Finset

/-- The source exponent map is constructed by summing the occupied Fibonacci
weights. It is bijective onto the initial Fibonacci interval and transports
the finite Euler sum to the usual geometric sum. -/
theorem finite_zeckendorf_interval_and_euler (Q : Nat) :
    let exponent : GoldenName Q → Fin (Nat.fib (Q + 2)) := fun name =>
      ⟨(name.1.1.map Nat.fib).sum, by
        exact ((goldenNameEquiv Q).symm name).isLt⟩
    Function.Bijective exponent ∧
      ∀ x : Real, |x| < 1 →
        (∑ name : GoldenName Q,
          x ^ (exponent name : Nat)) =
            ∑ e : Fin (Nat.fib (Q + 2)), x ^ (e : Nat) ∧
        (∑ e : Fin (Nat.fib (Q + 2)), x ^ (e : Nat)) =
          (1 - x ^ Nat.fib (Q + 2)) / (1 - x) := by
  dsimp only
  refine ⟨(goldenNameEquiv Q).symm.bijective, ?_⟩
  intro x hx
  constructor
  · calc
      (∑ name : GoldenName Q, x ^ (name.1.1.map Nat.fib).sum) =
          ∑ name : GoldenName Q,
            x ^ (((goldenNameEquiv Q).symm name : Fin _) : Nat) := by
        apply Finset.sum_congr rfl
        intro name _
        congr 1
      _ = ∑ e : Fin (Nat.fib (Q + 2)), x ^ (e : Nat) := by
        simpa using
          ((goldenNameEquiv Q).sum_comp
            (fun name : GoldenName Q =>
              x ^ (((goldenNameEquiv Q).symm name : Fin _) : Nat))).symm
  · have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
    have hx1 : x ≠ 1 := ne_of_lt hxlt
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hx1]
    field_simp
    ring

#print axioms finite_zeckendorf_interval_and_euler

end D5.S3.Observer.GoldenCoding.FiniteZeckendorfEulerIdentity
