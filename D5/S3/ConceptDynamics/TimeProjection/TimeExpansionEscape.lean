/- GID: D5/S3/ConceptDynamics/TimeProjection/TimeExpansionEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TimeProjection/TimeExpansionEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Escape between nested finite horizons is exactly readout expansion escape. -/

import D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape

/- Library-search audit trail (2026-08-28):
   * Two D5 collision searches found no `TimeExpansionEscape` declaration or
     theorem relating it to `ExpansionEscape`; the only hit was an earlier
     search note in the imported time-projection module.
   * The imported module supplies the canonical `timeIter`, `TimeIndex`,
     `timeProjection`, and `ExpansionEscape` definitions. They are reused
     directly rather than duplicated.
   * Pinned Mathlib supplies `Fintype.decidableExistsFintype`, which turns
     inequality of the longer finite functions into a checked coordinate
     witness under decidable equality of the output type. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TimeProjection.TimeExpansionEscape

open D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape

universe u v

set_option linter.dupNamespace false in
/-- Two states agree through the old horizon and first become distinguishable
at some coordinate added by the longer horizon. This definition is independent
of `ExpansionEscape` and uses bounded natural-number witnesses. -/
def TimeExpansionEscape
    {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    (N M : Nat) (_h : N <= M) (x y : X) : Prop :=
  (forall k : Nat, k <= N ->
      readout (timeIter transition k x) =
        readout (timeIter transition k y)) /\
    exists k : Nat, N < k /\ k <= M /\
      Not (readout (timeIter transition k x) =
        readout (timeIter transition k y))

set_option linter.unusedDecidableInType false in
/-- Extending a finite time horizon exposes exactly the pairs in the
`ExpansionEscape` relation from the shorter to the longer projection. -/
theorem time_expansion_escape_iff_expansion_escape
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X)
    (N M : Nat) (h : N <= M) (x y : X) :
    TimeExpansionEscape readout transition N M h x y <->
      ExpansionEscape
        (timeProjection readout transition N)
        (timeProjection readout transition M) x y := by
  constructor
  · rintro ⟨hOld, k, hAfterOld, hWithinNew, hDifferent⟩
    refine ⟨?_, ?_⟩
    · funext i
      exact hOld i.1 (Nat.le_of_lt_succ i.2)
    · intro hNew
      have hAtK := congrFun hNew
        (⟨k, Nat.lt_succ_iff.mpr hWithinNew⟩ : TimeIndex M)
      exact hDifferent (by simpa [timeProjection] using hAtK)
  · rintro ⟨hOld, hNew⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      have hAtK := congrFun hOld
        (⟨k, Nat.lt_succ_iff.mpr hk⟩ : TimeIndex N)
      simpa [timeProjection] using hAtK
    · let witnessDecision : Decidable
          (exists i : TimeIndex M,
            Not (timeProjection readout transition M x i =
              timeProjection readout transition M y i)) :=
        Fintype.decidableExistsFintype
      cases witnessDecision with
      | isTrue hWitness =>
          obtain ⟨i, hi⟩ := hWitness
          have hAfterOld : N < i.1 := by
            by_contra hNotAfter
            have hiWithinOld : i.1 <= N := Nat.le_of_not_gt hNotAfter
            have hAtOld := congrFun hOld
              (⟨i.1, Nat.lt_succ_iff.mpr hiWithinOld⟩ : TimeIndex N)
            exact hi (by simpa [timeProjection] using hAtOld)
          exact ⟨i.1, hAfterOld, Nat.le_of_lt_succ i.2,
            by simpa [timeProjection] using hi⟩
      | isFalse hNoWitness =>
          exfalso
          apply hNew
          funext i
          by_cases hi :
              timeProjection readout transition M x i =
                timeProjection readout transition M y i
          · exact hi
          · exact (hNoWitness ⟨i, hi⟩).elim

/-- A strict one-step extension whose new coordinate distinguishes two states. -/
example :
    let readout : Fin 3 -> Bool := fun state =>
      if state = 2 then true else false
    let transition : Fin 3 -> Fin 3 := fun state =>
      if state = 1 then 2 else state
    let h : 0 <= 1 := by decide
    TimeExpansionEscape readout transition 0 1 h 0 1 /\
      ExpansionEscape
        (timeProjection readout transition 0)
        (timeProjection readout transition 1) 0 1 := by
  dsimp
  have hTime :
      TimeExpansionEscape
        (fun state : Fin 3 => if state = 2 then true else false)
        (fun state : Fin 3 => if state = 1 then 2 else state)
        0 1 (by decide) 0 1 := by
    exact ⟨by
        intro k hk
        have hkZero : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        decide,
      1, by decide, by decide, by decide⟩
  exact ⟨hTime,
    (time_expansion_escape_iff_expansion_escape _ _ _ _ _ _ _).mp hTime⟩

#print axioms time_expansion_escape_iff_expansion_escape

end D5.S3.ConceptDynamics.TimeProjection.TimeExpansionEscape
