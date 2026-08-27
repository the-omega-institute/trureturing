/- GID: D5/S3/Observer/Budget/FiniteInternalProtocolNoGo
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/FiniteInternalProtocolNoGo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite internal protocol indexing cannot realize every response table. -/

import Mathlib.Data.Fintype.BigOperators

/- Library-search audit trail (2026-08-28):
   * Repository name and body-shape searches found no canonical response-completeness
     primitive and no exact theorem for the finite internal-protocol obstruction.
   * Pinned Mathlib exact hit `Nat.lt_pow_self` proves the strict exponential
     inequality, including the empty-state strengthening of the source statement.
   * Pinned Mathlib exact hits `Fintype.card_fun` and
     `Fintype.card_le_of_surjective` count the response tables realized by protocols. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.FiniteInternalProtocolNoGo

universe u v w

/-- If at least two responses are available and the finite protocol carrier is no
larger than the finite state carrier, then the space of response tables is strictly
larger than the state carrier and no evaluation channel can realize every table.
The conclusion is slightly stronger than the source: it also covers an empty state
carrier, so no nonemptiness premise is needed. -/
theorem finite_internal_protocol_no_go
    {X : Type u} {P : Type v} {Lambda : Type w}
    [Fintype X] [Fintype P] [Fintype Lambda]
    (e : X -> P -> Lambda)
    (hLambda : 2 <= Fintype.card Lambda)
    (hInternal : Fintype.card P <= Fintype.card X) :
    Fintype.card X < Fintype.card Lambda ^ Fintype.card X ∧
      ¬(forall f : X -> Lambda, exists p : P, forall x : X, e x p = f x) := by
  classical
  have hPower : Fintype.card X < Fintype.card Lambda ^ Fintype.card X :=
    Nat.lt_pow_self (lt_of_lt_of_le Nat.one_lt_two hLambda)
  refine ⟨hPower, ?_⟩
  intro hComplete
  let evaluation : P -> X -> Lambda := fun p x => e x p
  have hSurjective : Function.Surjective evaluation := by
    intro f
    rcases hComplete f with ⟨p, hp⟩
    exact ⟨p, funext hp⟩
  have hFunctions : Fintype.card (X -> Lambda) <= Fintype.card P :=
    Fintype.card_le_of_surjective evaluation hSurjective
  have hPowerLe : Fintype.card Lambda ^ Fintype.card X <= Fintype.card X := by
    simpa only [Fintype.card_fun] using hFunctions.trans hInternal
  exact (Nat.not_lt_of_ge hPowerLe) hPower

#print axioms finite_internal_protocol_no_go

end D5.S3.Observer.Budget.FiniteInternalProtocolNoGo
