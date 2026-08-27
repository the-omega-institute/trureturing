/- GID: D5/S3/Observer/Completion/DoubleExtensionalQuotientUniversality
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/DoubleExtensionalQuotientUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-sided extensional quotients are uniquely equivalent to extensional factorizations. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * No exact D5 or pinned-Mathlib theorem was found for the source's two-sided
     evaluation quotient with simultaneous unique state and protocol equivalences.
   * `CompletionCriterion`, `GlobalProfileQuotientUniversality`, and
     `ControlQuotientUniversalMinimality` provide one-sided or dynamic quotient
     results, not this static dual factorization.
   * Body-shape searches for the source row and column maps found no existing
     declarations; `stateBehavior` and `protocolBehavior` below are the direct
     evaluation-row and evaluation-column primitives.
   * Pinned Mathlib supplies `Quotient.lift`, `Quotient.sound`,
     `Quotient.inductionOn'`, and `Equiv.ofBijective` for the canonical maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Completion.DoubleExtensionalQuotientUniversality

universe u

def stateBehavior {X P Lambda : Type u} (evaluation : X -> P -> Lambda) :
    X -> P -> Lambda :=
  fun state protocol => evaluation state protocol

def protocolBehavior {X P Lambda : Type u} (evaluation : X -> P -> Lambda) :
    P -> X -> Lambda :=
  fun protocol state => evaluation state protocol

/- The canonical state and protocol quotients are the equality kernels of the
   evaluation rows and columns. The supplied factorization induces equivalences
   onto any extensional target carriers, and the evaluation square commutes. -/
theorem double_extensional_quotient_universal_minimality
    {X P Lambda XPrime PPrime : Type u}
    (evaluation : X -> P -> Lambda)
    (stateMap : X -> XPrime) (protocolMap : P -> PPrime)
    (targetEvaluation : XPrime -> PPrime -> Lambda)
    (stateSurjective : Function.Surjective stateMap)
    (protocolSurjective : Function.Surjective protocolMap)
    (factorization : forall state protocol,
      evaluation state protocol =
        targetEvaluation (stateMap state) (protocolMap protocol))
    (targetStateExtensional : forall first second,
      (forall protocol, targetEvaluation first protocol =
        targetEvaluation second protocol) -> first = second)
    (targetProtocolExtensional : forall first second,
      (forall state, targetEvaluation state first =
        targetEvaluation state second) -> first = second) :
    ∃! equivalences :
      (Quotient (Setoid.ker (stateBehavior evaluation)) ≃ XPrime) ×
        (Quotient (Setoid.ker (protocolBehavior evaluation)) ≃ PPrime),
      (∀ state,
        equivalences.1
            (Quotient.mk (Setoid.ker (stateBehavior evaluation)) state) =
          stateMap state) ∧
      (∀ protocol,
        equivalences.2
            (Quotient.mk (Setoid.ker (protocolBehavior evaluation)) protocol) =
          protocolMap protocol) ∧
      (∀ state protocol,
        evaluation state protocol =
          targetEvaluation
            (equivalences.1
              (Quotient.mk (Setoid.ker (stateBehavior evaluation)) state))
            (equivalences.2
              (Quotient.mk (Setoid.ker (protocolBehavior evaluation)) protocol))) := by
  let stateQuotient : Type u :=
    Quotient (Setoid.ker (stateBehavior evaluation))
  let protocolQuotient : Type u :=
    Quotient (Setoid.ker (protocolBehavior evaluation))
  let inducedState : stateQuotient -> XPrime :=
    Quotient.lift stateMap (by
      intro first second sameRow
      apply targetStateExtensional
      intro protocol
      obtain ⟨sourceProtocol, sourceProtocolMap⟩ := protocolSurjective protocol
      calc
        targetEvaluation (stateMap first) protocol =
            targetEvaluation (stateMap first) (protocolMap sourceProtocol) := by
              rw [sourceProtocolMap]
        _ = evaluation first sourceProtocol :=
          (factorization first sourceProtocol).symm
        _ = evaluation second sourceProtocol :=
          congrFun sameRow sourceProtocol
        _ = targetEvaluation (stateMap second) (protocolMap sourceProtocol) :=
          factorization second sourceProtocol
        _ = targetEvaluation (stateMap second) protocol := by
          rw [sourceProtocolMap])
  let inducedProtocol : protocolQuotient -> PPrime :=
    Quotient.lift protocolMap (by
      intro first second sameColumn
      apply targetProtocolExtensional
      intro state
      obtain ⟨sourceState, sourceStateMap⟩ := stateSurjective state
      calc
        targetEvaluation state (protocolMap first) =
            targetEvaluation (stateMap sourceState) (protocolMap first) := by
              rw [sourceStateMap]
        _ = evaluation sourceState first :=
          (factorization sourceState first).symm
        _ = evaluation sourceState second :=
          congrFun sameColumn sourceState
        _ = targetEvaluation (stateMap sourceState) (protocolMap second) :=
          factorization sourceState second
        _ = targetEvaluation state (protocolMap second) := by
          rw [sourceStateMap])
  have inducedStateInjective : Function.Injective inducedState := by
    intro first second equalTarget
    obtain ⟨sourceFirst, rfl⟩ := Quotient.exists_rep first
    obtain ⟨sourceSecond, rfl⟩ := Quotient.exists_rep second
    have equalMap : stateMap sourceFirst = stateMap sourceSecond := by
      simpa [inducedState] using equalTarget
    apply Quotient.sound
    change stateBehavior evaluation sourceFirst =
      stateBehavior evaluation sourceSecond
    funext protocol
    calc
      evaluation sourceFirst protocol =
          targetEvaluation (stateMap sourceFirst) (protocolMap protocol) :=
        factorization sourceFirst protocol
      _ = targetEvaluation (stateMap sourceSecond) (protocolMap protocol) := by
        rw [equalMap]
      _ = evaluation sourceSecond protocol :=
        (factorization sourceSecond protocol).symm
  have inducedStateSurjective : Function.Surjective inducedState := by
    intro target
    obtain ⟨source, sourceMap⟩ := stateSurjective target
    refine ⟨Quotient.mk (Setoid.ker (stateBehavior evaluation)) source, ?_⟩
    exact sourceMap
  have inducedProtocolInjective : Function.Injective inducedProtocol := by
    intro first second equalTarget
    obtain ⟨sourceFirst, rfl⟩ := Quotient.exists_rep first
    obtain ⟨sourceSecond, rfl⟩ := Quotient.exists_rep second
    have equalMap : protocolMap sourceFirst = protocolMap sourceSecond := by
      simpa [inducedProtocol] using equalTarget
    apply Quotient.sound
    change protocolBehavior evaluation sourceFirst =
      protocolBehavior evaluation sourceSecond
    funext state
    calc
      evaluation state sourceFirst =
          targetEvaluation (stateMap state) (protocolMap sourceFirst) :=
        factorization state sourceFirst
      _ = targetEvaluation (stateMap state) (protocolMap sourceSecond) := by
        rw [equalMap]
      _ = evaluation state sourceSecond :=
        (factorization state sourceSecond).symm
  have inducedProtocolSurjective : Function.Surjective inducedProtocol := by
    intro target
    obtain ⟨source, sourceMap⟩ := protocolSurjective target
    refine ⟨Quotient.mk (Setoid.ker (protocolBehavior evaluation)) source, ?_⟩
    exact sourceMap
  let stateEquivalence : stateQuotient ≃ XPrime :=
    Equiv.ofBijective inducedState ⟨inducedStateInjective, inducedStateSurjective⟩
  let protocolEquivalence : protocolQuotient ≃ PPrime :=
    Equiv.ofBijective inducedProtocol
      ⟨inducedProtocolInjective, inducedProtocolSurjective⟩
  have stateEquation : forall state,
      stateEquivalence
          (Quotient.mk (Setoid.ker (stateBehavior evaluation)) state) =
        stateMap state := by
    intro state
    rfl
  have protocolEquation : forall protocol,
      protocolEquivalence
          (Quotient.mk (Setoid.ker (protocolBehavior evaluation)) protocol) =
        protocolMap protocol := by
    intro protocol
    rfl
  refine ⟨⟨stateEquivalence, protocolEquivalence⟩, ?_, ?_⟩
  · refine ⟨stateEquation, protocolEquation, ?_⟩
    intro state protocol
    rw [stateEquation, protocolEquation]
    exact factorization state protocol
  · intro other otherProperties
    apply Prod.ext
    · apply Equiv.ext
      intro quotientState
      refine Quotient.inductionOn' quotientState ?_
      intro state
      calc
        other.1 (Quotient.mk (Setoid.ker (stateBehavior evaluation)) state) =
            stateMap state := otherProperties.1 state
        _ = stateEquivalence
            (Quotient.mk (Setoid.ker (stateBehavior evaluation)) state) :=
          (stateEquation state).symm
    · apply Equiv.ext
      intro quotientProtocol
      refine Quotient.inductionOn' quotientProtocol ?_
      intro protocol
      calc
        other.2 (Quotient.mk (Setoid.ker (protocolBehavior evaluation)) protocol) =
            protocolMap protocol := otherProperties.2.1 protocol
        _ = protocolEquivalence
            (Quotient.mk (Setoid.ker (protocolBehavior evaluation)) protocol) :=
          (protocolEquation protocol).symm

#print axioms double_extensional_quotient_universal_minimality

end D5.S3.Observer.Completion.DoubleExtensionalQuotientUniversality
