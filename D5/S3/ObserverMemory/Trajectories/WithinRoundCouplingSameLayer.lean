/- GID: D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Definition 45.2 is typed explicitly; Proposition 45.3 remains open. -/

import D5.S3.Observer.Completion.ClosureNonimplicationTriple
import D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

/- Library-search audit trail (2026-09-03):
   * Repository search found the exact Definition 45.1 owners `AppendOnlyOps`,
     `RecordedObserver`, `AugmentedState`, and `step` in the imported trajectory module.
   * Repository search found `closure_nonimplication_triple`, whose conclusion is the
     existing formalization of the Section 32.10 and 33.10 nonimplications. It is cited
     directly below; no new closure predicate is selected for this module.
   * Pinned Mathlib and Loogle found the quotient APIs used to descend the second
     component of the joint readout. No pinned or third-party observer theorem
     packages within-round coupling and same-layer evaluation.
   * LeanSearch and Reservoir endpoints returned 404, while GitHub code search returned
     401 without authentication. The ordered receipt is `/tmp/SEARCH-ag.md`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Trajectories.WithinRoundCouplingSameLayer

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.Observer.Completion.ClosureNonimplicationTriple
open D5.S3.Observer.WindowAlgebra.OperationalClassicalSeparation
open D5.S3.Observer.WindowAlgebra.WindowGeneration
open D5.S3.Observer.WindowRegister
open D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.Quantum.Algebra.CovariantCommutator
open D5.S3.Quantum.Measurements.DeterministicReadoutPvm
open D5.S3.Quantum.Tomography.ObserverDiagonalSeparation
open D5.S3.Quantum.Tomography.RankOneContextCommutator

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

/-- The round following `e`. Source: QDO lines 47042-47047. -/
def nextRound (e : RoundIndex) : RoundIndex :=
  ⟨e.1 + 1, Nat.zero_lt_succ e.1⟩

/-- Definition 45.1's cross-round clause. The update may change between rounds,
and the update selected for `nextRound e` is allowed to depend on `q2` applied
to the preceding round's terminal record. Source: QDO lines 47045-47047. -/
structure CrossRoundUpdateSchedule
    (State Record SecondOutput : Type*)
    (q2 : Concept Record SecondOutput) where
  controlledUpdate : RoundIndex -> State × SecondOutput -> State
  previousRecord : RoundIndex -> Record
  selectNextUpdate :
    RoundIndex -> SecondOutput -> State × SecondOutput -> State
  select_next : forall e,
    controlledUpdate (nextRound e) =
      selectNextUpdate e (q2 (previousRecord e))

/-- Definition 45.1's all-round predicate for a second-layer observer: the
boxed decoupling condition holds in every round. Source: QDO lines 47047-47048. -/
def IsSecondLayerObserver {State SecondOutput : Type*}
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State) : Prop :=
  forall e, WithinRoundDecoupled controlledUpdate e

/-- The independently supplied positions of the augmented single-system interface.
The carrier, joint-readout codomain, quotient, and evaluation codomain are separate
type parameters; in particular, `deltaEvaluation` is data rather than a definition
derived from a second readout. Source: QDO lines 15263-15326 and 47049-47054. -/
structure AugmentedSingleSystem
    (Carrier JointReading QuotientState Evaluation : Type*) where
  dynamics : Carrier -> Carrier
  readout : Carrier -> JointReading
  deltaEvaluation : QuotientState -> QuotientState -> Evaluation

/-- Definition 45.1's closed-loop update on `X x Lambda`, with
`z = q2(lambda)`. Source: QDO lines 47031-47046 and 47059. -/
def jointRoundUpdate {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) :
    AugmentedState State Record -> AugmentedState State Record :=
  fun current =>
    step recordOps (observerAt recordOps q1 controlledUpdate q2 e) current (q2 current.2)

/-- The named closed-loop update is exactly Definition 45.1's displayed step.
This equation keeps the locally named update accountable to the source formula. -/
theorem jointRoundUpdate_eq_definition451_step
    {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (current : AugmentedState State Record) :
    jointRoundUpdate recordOps q1 controlledUpdate q2 e current =
      (controlledUpdate e (current.1, q2 current.2),
        recordOps.append current.2 (q1 current.1)) := by
  rfl

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
  Quotient.lift (fun current => q2 current.2) fun _ _ sameJointReadout =>
    congrArg Prod.snd sameJointReadout

/-- Definition 45.2's same-layer predicate for an independently given augmented
single system. Its types identify the carrier with `X x Lambda`, the readout
codomain with the joint codomain, and the quotient with the kernel quotient of
`jointReadout`. The three clauses then require the given readout and dynamics to
be the source objects and the given Delta/evaluation diagonal to agree with the
descended `q2`. Source: QDO lines 47049-47054 and 15263-15326. -/
def IsSameLayerInRound {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (system : AugmentedSingleSystem
      (AugmentedState State Record)
      (Reading × SecondOutput)
      (JointObservationQuotient q1 q2)
      SecondOutput) : Prop :=
  system.readout = jointReadout q1 q2 ∧
  system.dynamics = jointRoundUpdate recordOps q1 controlledUpdate q2 e ∧
  forall point,
    system.deltaEvaluation point point = quotientSecondReadout q1 q2 point

/-- The exact already-formalized conclusions of Sections 32.10 and 33.10.
This is definitionally the proposition proved by `closure_nonimplication_triple`;
it introduces no round-specific or canonical-evaluation semantics. -/
abbrev EstablishedClosureNonimplications : Prop :=
    (predictionStableAt
        (fun state : ZMod 2 => state - 1)
        (fun _ : ZMod 2 => ()) 0 ∧
      Algebra.adjoin ℂ
        ({deterministicProjection (fun _ : ZMod 2 => ()) (), shiftMatrix 2} :
          Set (Matrix (ZMod 2) (ZMod 2) ℂ)) ≠ ⊤) ∧
    (windowGeneratedAlgebra 2 = ⊤ ∧
      IsEmpty (windowGeneratedAlgebra 2 →ₐ[ℂ] ℂ)) ∧
    ∃ context : Fin 2 -> RankOneContext 1,
      Function.Injective (contextReadout context) ∧
      ∃ (evaluation : Matrix (Fin 1) (Fin 1) ℂ ->
          Matrix (Fin 1) (Fin 1) ℂ -> Bool)
        (twist : Bool -> Bool),
        (∀ y, twist y ≠ y) ∧
          (fun a => twist (evaluation a a)) ∉ Set.range evaluation

/-- Sections 32.10 and 33.10 are reused at their already-formalized strength.
Source: QDO lines 16191-16237, 18110-18167, and 47055-47061. -/
theorem established_closure_nonimplications : EstablishedClosureNonimplications :=
  closure_nonimplication_triple

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

-- A trivial record carrier does not make the coupling premise vacuous: the
-- controlled update still distinguishes two second-output values.
example (e : RoundIndex) :
    ¬WithinRoundDecoupled boolControlledUpdate e :=
  boolControlledUpdate_isCoupled e

private def boolAugmentedSystem
    (deltaEvaluation : JointObservationQuotient unitReading constantSecondReadout ->
      JointObservationQuotient unitReading constantSecondReadout -> Bool)
    (e : RoundIndex) :
    AugmentedSingleSystem
      (AugmentedState Bool Unit)
      (Unit × Bool)
      (JointObservationQuotient unitReading constantSecondReadout)
      Bool where
  dynamics := fun current =>
    (boolControlledUpdate e (current.1, constantSecondReadout current.2),
      unitRecordOps.append current.2 (unitReading current.1))
  readout := fun current =>
    (unitReading current.1, constantSecondReadout current.2)
  deltaEvaluation := deltaEvaluation

private def matchingBoolAugmentedSystem (e : RoundIndex) :=
  boolAugmentedSystem (fun _ _ => false) e

private def mismatchingBoolAugmentedSystem (e : RoundIndex) :=
  boolAugmentedSystem (fun _ _ => true) e

-- Definition 45.2 is satisfiable when independently supplied interface data
-- meet all three source clauses. The Delta field is the explicit first argument
-- of `boolAugmentedSystem`; it is not constructed from `q2`.
example (e : RoundIndex) :
    IsSameLayerInRound unitRecordOps unitReading boolControlledUpdate
      constantSecondReadout e (matchingBoolAugmentedSystem e) := by
  refine ⟨rfl, rfl, ?_⟩
  intro point
  refine Quotient.inductionOn point ?_
  intro current
  rfl

example (e : RoundIndex) (current : AugmentedState Bool Unit) :
    jointRoundUpdate unitRecordOps unitReading boolControlledUpdate
        constantSecondReadout e current =
      (boolControlledUpdate e (current.1, constantSecondReadout current.2),
        unitRecordOps.append current.2 (unitReading current.1)) :=
  jointRoundUpdate_eq_definition451_step unitRecordOps unitReading
    boolControlledUpdate constantSecondReadout e current

/-- Coupling failure does not constrain the separately supplied Delta/evaluation.
The system below has the exact joint readout and Definition 45.1 dynamics, but
its Boolean diagonal disagrees with the descended constant-false `q2`.
This is the formal obstruction to proving Proposition 45.3 from its source
premise alone. -/
theorem coupling_does_not_force_delta_diagonal (e : RoundIndex) :
    ¬WithinRoundDecoupled boolControlledUpdate e ∧
      ¬IsSameLayerInRound unitRecordOps unitReading boolControlledUpdate
        constantSecondReadout e (mismatchingBoolAugmentedSystem e) := by
  refine ⟨boolControlledUpdate_isCoupled e, ?_⟩
  intro sameLayer
  let point : JointObservationQuotient unitReading constantSecondReadout :=
    Quotient.mk _ (false, ())
  have diagonal := sameLayer.2.2 point
  simp [mismatchingBoolAugmentedSystem, boolAugmentedSystem,
    quotientSecondReadout, constantSecondReadout, point] at diagonal

private def decoupledBoolUpdate : RoundIndex -> Bool × Bool -> Bool :=
  fun _ input => input.1

example : IsSecondLayerObserver decoupledBoolUpdate := by
  intro e state firstOutput secondOutput
  rfl

private def boolCrossRoundSchedule :
    CrossRoundUpdateSchedule Bool Unit Bool constantSecondReadout where
  controlledUpdate := boolControlledUpdate
  previousRecord := fun _ => ()
  selectNextUpdate := fun _ previousOutput input => input.2.xor previousOutput
  select_next := by
    intro e
    funext input
    simp [boolControlledUpdate, constantSecondReadout]

example : CrossRoundUpdateSchedule Bool Unit Bool constantSecondReadout :=
  boolCrossRoundSchedule

/- Proposition 45.3 remains open in this module. Its only premise says that
`controlledUpdate e` depends on its second input. Definition 32.1, however,
makes Delta an independently typed part of the observer interface, and that
premise supplies no relation between `system.deltaEvaluation` and `q2` on the
joint quotient. The theorem `coupling_does_not_force_delta_diagonal` gives a
countermodel to precisely that missing implication.

Re-entry requires additional source support that makes coupling failure imply
the diagonal agreement of the already-given Delta/evaluation with descended
`q2`, or an independently stated construction of Delta carrying that law. It
must not define Delta from `q2` merely to make the equality reflexive. Source:
QDO lines 15263-15326 and 47049-47059. -/

#print axioms coupling_does_not_force_delta_diagonal

end

end D5.S3.ObserverMemory.Trajectories.WithinRoundCouplingSameLayer
