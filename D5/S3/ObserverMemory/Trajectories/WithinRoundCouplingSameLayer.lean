/- GID: D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coupled recorded rounds are same-layer, without automatic self-description closure. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

/- Library-search audit trail (2026-09-03):
   * Repository search found the exact Definition 45.1 owners `AppendOnlyOps`,
     `RecordedObserver`, `AugmentedState`, and `step` in the imported trajectory module.
   * Repository search found `closure_nonimplication_triple` for the section-level
     three-closure countermodels; this round theorem instead uses the more general exact
     component `escaped_of_fixedPointFree` on its own joint quotient.
   * Repository search also found `SelfDescriptionClosure`, but that specialization
     requires one carrier in all three evaluator positions, whereas Section 32.10 and
     this atom have a distinct `SecondOutput` codomain.
   * Pinned Mathlib and Loogle both found `Setoid.quotientKerEquivRange`, the exact
     quotient-to-joint-readout-range equivalence used below. No pinned or third-party
     observer theorem packages within-round coupling and same-layer evaluation.
   * LeanSearch and Reservoir endpoints returned 404, while GitHub code search returned
     401 without authentication. The ordered receipt is `/tmp/SEARCH-ag.md`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Trajectories.WithinRoundCouplingSameLayer

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

noncomputable section

/-- The positive round indices `e = 1, 2, ...` from Definition 45.1.
Source: QDO lines 47042-47043. -/
abbrev RoundIndex := {e : Nat // 0 < e}

/-- Definition 45.1 at a fixed round: `q1` and `q2` stay fixed while the
controlled update is selected by the round index. Source: QDO lines 47031-47046. -/
def observerAt {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) :
    RecordedObserver State Record Reading SecondOutput recordOps where
  q1 := q1
  controlledUpdate := controlledUpdate e
  q2 := q2

/-- Definition 45.1's boxed within-round decoupling condition.
Source: QDO lines 47042-47048. -/
def WithinRoundDecoupled {State SecondOutput : Type*}
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (e : RoundIndex) : Prop :=
  forall x z z', controlledUpdate e (x, z) = controlledUpdate e (x, z')

/-- The closed-loop update of Definition 45.2 on the single augmented state
space, with `z = q2(lambda)`. Source: QDO lines 47051-47054 and 47059-47060. -/
def jointRoundUpdate {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) :
    AugmentedState State Record -> AugmentedState State Record :=
  fun current =>
    step recordOps (observerAt recordOps q1 controlledUpdate q2 e) current (q2 current.2)

/-- Definition 45.2's joint readout `(q1 o pi_X, q2 o pi_Lambda)`.
Source: QDO lines 47051-47054. -/
def jointReadout {State Record Reading SecondOutput : Type*}
    (q1 : Concept State Reading) (q2 : Concept Record SecondOutput) :
    AugmentedState State Record -> Reading × SecondOutput :=
  fun current => (q1 current.1, q2 current.2)

/-- The joint quotient from Definition 45.2, represented by the kernel of the
joint readout exactly as in Section 32.1. Source: QDO lines 47051-47054. -/
abbrev JointObservationQuotient {State Record Reading SecondOutput : Type*}
    (q1 : Concept State Reading) (q2 : Concept Record SecondOutput) :=
  Quotient (Setoid.ker (jointReadout q1 q2))

/-- The second readout descends canonically to the joint quotient because it is
the second component of the joint readout. Source: QDO lines 47051-47054. -/
def quotientSecondReadout {State Record Reading SecondOutput : Type*}
    (q1 : Concept State Reading) (q2 : Concept Record SecondOutput) :
    JointObservationQuotient q1 q2 -> SecondOutput :=
  fun point => ((Setoid.quotientKerEquivRange (jointReadout q1 q2)) point).1.2

/-- The same-typed evaluation table on the joint quotient. Its diagonal is the
second readout, which is Definition 45.2's same-layer self-application.
Source: QDO lines 47051-47054 and Section 32.1 lines 15311-15325. -/
def sameLayerEvaluation {State Record Reading SecondOutput : Type*}
    (q1 : Concept State Reading) (q2 : Concept Record SecondOutput) :
    JointObservationQuotient q1 q2 ->
      JointObservationQuotient q1 q2 -> SecondOutput :=
  fun _ target => quotientSecondReadout q1 q2 target

/-- Definition 45.2: after forming the exact augmented update, joint readout,
and joint quotient above, `q2` is the diagonal of a same-typed evaluation.
Source: QDO lines 47051-47054. -/
def IsSameLayerInRound {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) : Prop :=
  let _update := jointRoundUpdate recordOps q1 controlledUpdate q2 e
  forall point,
    sameLayerEvaluation q1 q2 point point = quotientSecondReadout q1 q2 point

/-- Automatic same-layer self-description closure would be the universal rule
that every same-layer recorded round has a surjective canonical evaluation on
its own joint quotient. Its negation is the precise non-implication used in
Proposition 45.3, not a claim that every enriched closure is impossible.
Source: QDO lines 47056-47061; Sections 32.10 and 33.10. -/
def SameLayerSelfDescriptionClosureAutomatic
    (State Record Reading SecondOutput : Type*) : Prop :=
  forall
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex),
    IsSameLayerInRound recordOps q1 controlledUpdate q2 e ->
      Function.Surjective (sameLayerEvaluation q1 q2)

/-- Proposition 45.3: failure of the boxed decoupling condition puts the two
recorded observers on one augmented layer, while same-layer typing alone does
not automatically make every self-description table closed.
Source: QDO lines 47056-47061. -/
theorem within_round_coupling_is_same_layer
    {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (coupled : ¬WithinRoundDecoupled controlledUpdate e) :
    IsSameLayerInRound recordOps q1 controlledUpdate q2 e ∧
      ¬SameLayerSelfDescriptionClosureAutomatic State Record Reading SecondOutput := by
  classical
  have sameLayer : IsSameLayerInRound recordOps q1 controlledUpdate q2 e := by
    intro point
    rfl
  constructor
  · exact sameLayer
  · intro automaticClosure
    unfold WithinRoundDecoupled at coupled
    push Not at coupled
    obtain ⟨_state, firstOutput, secondOutput, updateDiffers⟩ := coupled
    have outputsDiffer : firstOutput ≠ secondOutput := by
      intro outputsEqual
      subst secondOutput
      exact updateDiffers rfl
    let twist : SecondOutput -> SecondOutput := fun output =>
      if output = firstOutput then secondOutput else firstOutput
    have twistFixedPointFree : forall output, twist output ≠ output := by
      intro output
      by_cases outputFirst : output = firstOutput
      · subst output
        simpa only [twist, if_pos rfl] using outputsDiffer.symm
      · simpa only [twist, if_neg outputFirst] using Ne.symm outputFirst
    have escaped := escaped_of_fixedPointFree twist twistFixedPointFree
      (sameLayerEvaluation q1 q2)
    apply escaped
    exact automaticClosure recordOps q1 controlledUpdate q2 e sameLayer
      (diagonal twist (sameLayerEvaluation q1 q2))

-- P2/P3 reverse probes: replacing the whole conclusion with `True`, or deleting
-- either public leaf, makes at least one of these projections fail to elaborate.
example {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (coupled : ¬WithinRoundDecoupled controlledUpdate e) :
    IsSameLayerInRound recordOps q1 controlledUpdate q2 e :=
  (within_round_coupling_is_same_layer recordOps q1 controlledUpdate q2 e coupled).1

example {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (coupled : ¬WithinRoundDecoupled controlledUpdate e) :
    ¬SameLayerSelfDescriptionClosureAutomatic State Record Reading SecondOutput :=
  (within_round_coupling_is_same_layer recordOps q1 controlledUpdate q2 e coupled).2

-- P5a: on a one-point second-output carrier the decoupling condition always
-- holds, so the proposition's coupling premise cannot be inhabited.
example {State : Type*}
    (controlledUpdate : RoundIndex -> State × Unit -> State) (e : RoundIndex) :
    WithinRoundDecoupled controlledUpdate e := by
  intro state firstOutput secondOutput
  cases firstOutput
  cases secondOutput
  rfl

private def unitRecordOps : AppendOnlyOps Unit Unit where
  append := fun _ _ => ()
  IsPrefix := fun _ _ => True
  prefix_append := by simp

private def boolControlledUpdate : RoundIndex -> Bool × Bool -> Bool :=
  fun _ input => input.2

private def unitReading : Concept Bool Unit := fun _ => ()

private def constantSecondReadout : Concept Unit Bool := fun _ => false

private theorem boolControlledUpdate_isCoupled (e : RoundIndex) :
    ¬WithinRoundDecoupled boolControlledUpdate e := by
  intro decoupled
  have impossible := decoupled false false true
  simp [boolControlledUpdate] at impossible

-- P5b: a trivial record carrier does not make the public implication vacuous.
-- The controlled update can still distinguish two second-output values.
example (e : RoundIndex) :
    IsSameLayerInRound unitRecordOps unitReading boolControlledUpdate
        constantSecondReadout e ∧
      ¬SameLayerSelfDescriptionClosureAutomatic Bool Unit Unit Bool :=
  within_round_coupling_is_same_layer unitRecordOps unitReading boolControlledUpdate
    constantSecondReadout e (boolControlledUpdate_isCoupled e)

#print axioms within_round_coupling_is_same_layer

end

end D5.S3.ObserverMemory.Trajectories.WithinRoundCouplingSameLayer
