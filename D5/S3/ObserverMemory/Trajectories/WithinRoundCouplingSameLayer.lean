/- GID: D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coupled recorded rounds are same-layer, without automatic self-description closure. -/

import D5.S3.Observer.Completion.ClosureNonimplicationTriple
import D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

/- Library-search audit trail (2026-09-03):
   * Repository search found the exact Definition 45.1 owners `AppendOnlyOps`,
     `RecordedObserver`, `AugmentedState`, and `step` in the imported trajectory module.
   * Repository search found `closure_nonimplication_triple`, whose conclusion is the
     existing formalization of the Section 32.10 and 33.10 nonimplications. It is cited
     directly below; no new closure predicate is selected for this module.
   * Pinned Mathlib and Loogle both found `Setoid.quotientKerEquivRange`, the exact
     quotient-to-joint-readout-range equivalence used below. No pinned or third-party
     observer theorem packages within-round coupling and same-layer evaluation.
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

/-- The same-typed evaluation table on the joint quotient. The evaluating
state is the first argument, so its diagonal is the second readout rather than
a constant-in-the-evaluator table.
Source: QDO lines 47051-47054 and Section 32.1 lines 15311-15325. -/
def sameLayerEvaluation {State Record Reading SecondOutput : Type*}
    (q1 : Concept State Reading) (q2 : Concept Record SecondOutput) :
    JointObservationQuotient q1 q2 ->
      JointObservationQuotient q1 q2 -> SecondOutput :=
  fun evaluator _target => quotientSecondReadout q1 q2 evaluator

/-- Definition 45.2's same-layer predicate. It keeps exactly the two source
clauses visible: equality of the named joint update with Definition 45.1's
displayed step, and the same-typed diagonal evaluation on the joint quotient.
Failure of decoupling belongs only to Proposition 45.3's premise.
Source: QDO lines 47049-47058. -/
def IsSameLayerInRound {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) : Prop :=
  (forall current,
    jointRoundUpdate recordOps q1 controlledUpdate q2 e current =
      (controlledUpdate e (current.1, q2 current.2),
        recordOps.append current.2 (q1 current.1))) ∧
  forall point,
    sameLayerEvaluation q1 q2 point point = quotientSecondReadout q1 q2 point

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

/-- The current Definition 45.2 encoding is satisfied by every round update:
both of its clauses unfold to definitional equalities. This records the actual
logical strength rather than making Proposition 45.3's premise load-bearing by
putting it into the conclusion predicate.

Fidelity remains open. Re-entry requires a source-supported formal account of
`q2` evaluation as same-layer self-application that is not definitionally true
for every update; no coupling-failure conjunct may be added to Definition 45.2.
Source: QDO lines 47049-47058. -/
theorem same_layer_in_round_unconditional
    {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex) :
    IsSameLayerInRound recordOps q1 controlledUpdate q2 e := by
  constructor
  · intro current
    rfl
  · intro point
    rfl

/-- Proposition 45.3: failure of the boxed decoupling condition puts the two
recorded observers on one augmented layer, while same-layer typing alone does
not imply the independent closure notions already separated in Sections 32.10
and 33.10. The source premise is retained in the public clause map, although
the current Definition 45.2 encoding makes the same-layer conclusion
unconditional as recorded by `same_layer_in_round_unconditional`.
Source: QDO lines 47056-47061. -/
theorem within_round_coupling_is_same_layer
    {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (q1 : Concept State Reading)
    (controlledUpdate : RoundIndex -> State × SecondOutput -> State)
    (q2 : Concept Record SecondOutput) (e : RoundIndex)
    (_coupled : ¬WithinRoundDecoupled controlledUpdate e) :
    IsSameLayerInRound recordOps q1 controlledUpdate q2 e ∧
      EstablishedClosureNonimplications := by
  exact ⟨same_layer_in_round_unconditional recordOps q1 controlledUpdate q2 e,
    established_closure_nonimplications⟩

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
    EstablishedClosureNonimplications :=
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
      EstablishedClosureNonimplications :=
  within_round_coupling_is_same_layer unitRecordOps unitReading boolControlledUpdate
    constantSecondReadout e (boolControlledUpdate_isCoupled e)

-- Contract probes for the corrected public surface.
example (e : RoundIndex) :
    ¬WithinRoundDecoupled boolControlledUpdate e :=
  boolControlledUpdate_isCoupled e

example (e : RoundIndex) (current : AugmentedState Bool Unit) :
    jointRoundUpdate unitRecordOps unitReading boolControlledUpdate
        constantSecondReadout e current =
      (boolControlledUpdate e (current.1, constantSecondReadout current.2),
        unitRecordOps.append current.2 (unitReading current.1)) :=
  (within_round_coupling_is_same_layer unitRecordOps unitReading boolControlledUpdate
    constantSecondReadout e (boolControlledUpdate_isCoupled e)).1.1 current

private def decoupledBoolUpdate : RoundIndex -> Bool × Bool -> Bool :=
  fun _ input => input.1

example : IsSecondLayerObserver decoupledBoolUpdate := by
  intro e state firstOutput secondOutput
  rfl

-- Definition 45.2 does not exclude a decoupled round: both structural clauses
-- remain satisfied. This is the permanent form of the circularity counterprobe.
example (e : RoundIndex) :
    IsSameLayerInRound unitRecordOps unitReading decoupledBoolUpdate
      constantSecondReadout e :=
  same_layer_in_round_unconditional unitRecordOps unitReading decoupledBoolUpdate
    constantSecondReadout e

private def boolCrossRoundSchedule :
    CrossRoundUpdateSchedule Bool Unit Bool constantSecondReadout where
  controlledUpdate := boolControlledUpdate
  previousRecord := fun _ => ()
  selectNextUpdate := fun _ previousOutput input => input.2.xor previousOutput
  select_next := by
    intro e
    funext input
    simp [boolControlledUpdate, constantSecondReadout]

#print axioms within_round_coupling_is_same_layer

end

end D5.S3.ObserverMemory.Trajectories.WithinRoundCouplingSameLayer
