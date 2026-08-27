/- GID: D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite time projections expand pointwise and restrict exactly along horizon inclusion. -/

import D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape

/- Library-search audit trail (2026-08-28):
   * The D5 query for `FiniteTimeProjectionRestrictionLaws`, `restrictTime`,
     the planned theorem name, and both complete conclusion shapes
     found no restriction operator or theorem with any of the three source
     conclusions. The exact `timeIter`, `TimeIndex`, and `timeProjection`
     definitions are frozen in `PredictionExpansionEscape` and reused here.
   * The corresponding D5 and pinned-Mathlib queries for projection equality,
     projection restriction, `timeProjection`, and `restrictTime`
     found generic inverse-system and finite-coordinate restriction machinery,
     but no finite-orbit projection expansion or horizon-restriction theorem.
   * The Loogle query `Fin.castLE` found `Fin.castLE`, `Fin.val_castLE`, and
     related coordinate lemmas. The query `timeProjection` returned unknown
     identifier, so there is no third-party declaration under the source name. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TimeProjection.FiniteTimeProjectionRestrictionLaws

open D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape

universe u v

/-- Restrict a word on a longer inclusive time horizon to a shorter one by
preserving every underlying natural-number index. -/
def restrictTime {O : Type v} {N M : Nat} (h : N <= M) :
    (TimeIndex M -> O) -> TimeIndex N -> O :=
  fun word index => word (Fin.castLE (Nat.succ_le_succ h) index)

/-- Equality of finite time projections is exactly equality at every bounded
time, longer projections restrict to shorter ones, and the zero-horizon
projection is the current readout. -/
theorem finite_time_projection_expansion_and_restriction_laws
    {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    {N M : Nat} (h : N <= M) (x y : X) :
    (timeProjection readout transition N x =
        timeProjection readout transition N y <->
      forall k : Nat, k <= N ->
        readout (timeIter transition k x) =
          readout (timeIter transition k y)) /\
      restrictTime h (timeProjection readout transition M x) =
        timeProjection readout transition N x /\
      timeProjection readout transition 0 x (0 : TimeIndex 0) = readout x := by
  constructor
  · constructor
    · intro projectionsEqual k hk
      have equalityAtK := congrFun projectionsEqual
        (⟨k, Nat.lt_succ_iff.mpr hk⟩ : TimeIndex N)
      simpa only [timeProjection] using equalityAtK
    · intro equalityAtEveryTime
      funext index
      simpa only [timeProjection] using
        equalityAtEveryTime index.1 (Nat.le_of_lt_succ index.2)
  constructor
  · funext index
    rfl
  · rfl

/- Domain-inhabitance witness for the unique index of the zero horizon. -/
example : TimeIndex 0 :=
  ⟨0, Nat.zero_lt_succ 0⟩

/- Hypothesis-satisfiability witness for a proper horizon inclusion. -/
example : (0 : Nat) <= 1 := by
  decide

/- The projection equality in the first conclusion is not automatic: two
distinct Boolean states are separated already at the zero horizon. -/
example :
    timeProjection (fun state : Bool => state) id 0 false !=
      timeProjection (fun state : Bool => state) id 0 true := by
  decide

#print axioms finite_time_projection_expansion_and_restriction_laws

end D5.S3.ConceptDynamics.TimeProjection.FiniteTimeProjectionRestrictionLaws
