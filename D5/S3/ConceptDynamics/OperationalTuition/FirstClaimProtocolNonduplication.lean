/- GID: D5/S3/ConceptDynamics/OperationalTuition/FirstClaimProtocolNonduplication
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/FirstClaimProtocolNonduplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Atomic T4 claim traces confine concurrency and make collision rate monotone. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Cast.Order

/- Library-search audit trail (2026-08-31):
   * Exact repository searches for first-claim allocation, T4 compliance,
     atomic claim visibility, visibility-window concurrency, and collision-rate
     monotonicity found no covering declaration.
   * Shape searches found unrelated sensor and number-theory collisions, but no
     finite operational protocol with trace delay.
   * Pinned Mathlib supplies finite `List.product`, Boolean filtering, rational
     casts, and order transport.  The protocol law itself is transcribed as
     structure evidence and a trajectory predicate, never as a Lean axiom.

   Clause echo:
   * Definition 6.1's first collision is `ClaimKind.firstCollision`; every
     implementation and every yield/reclaim readout is an event in one finite list.
   * T4's active-holder branch is `T4Compliant.activeYield`: a visible active
     holder forces the contender inactive and requires an affected-readout trace.
     Its stalled-holder branch permits `reclaimed` only after the declared
     threshold and with a matching reclaim readout.  `activeAt` is Boolean.
   * Atomic visibility is the exact equation saying a claim becomes visible at
     `claimTime + visibilityDelay`; it is a structure field, not an axiom.
   * T-F confines any concurrent pair to both visibility windows.  The uniform
     finite ordered-pair collision rate counts later claims inside the delay
     window and is monotone because enlarging delay only enlarges that filter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.FirstClaimProtocolNonduplication

/-- A claim is either the first recorded collision or an explicitly traced
reclaim from a previous holder. -/
inductive ClaimKind (Operator : Type*) where
  | firstCollision
  | reclaimed (previousHolder : Operator)
deriving DecidableEq, Repr

/-- One finite implementation interval together with its claim time and kind. -/
structure ImplementationAttempt (Operator : Type*) where
  operator : Operator
  claimTime : Nat
  implementationStart : Nat
  implementationEnd : Nat
  claimKind : ClaimKind Operator
deriving DecidableEq, Repr

/-- The readout left by an operator that yields to a visible active holder. -/
structure YieldReadout (Operator : Type*) where
  yieldingOperator : Operator
  holder : Operator
  time : Nat
deriving DecidableEq, Repr

/-- The atomic readout left when a stalled holding claim is reclaimed. -/
structure ReclaimReadout (Operator : Type*) where
  reclaimer : Operator
  previousHolder : Operator
  time : Nat
deriving DecidableEq, Repr

/-- The complete finite protocol event alphabet. -/
inductive ProtocolEvent (Operator : Type*) where
  | implementation (attempt : ImplementationAttempt Operator)
  | yieldReadout (readout : YieldReadout Operator)
  | reclaimReadout (readout : ReclaimReadout Operator)
deriving DecidableEq, Repr

/-- A finite protocol trajectory with declared visibility delay and stall
threshold.  The visibility function is constrained by `AtomicallyVisible`. -/
structure FiniteProtocol (Operator : Type*) where
  events : List (ProtocolEvent Operator)
  visibilityDelay : Nat
  stallThreshold : Nat
  claimVisible : ImplementationAttempt Operator -> Nat -> Bool

/-- Extract the finite list of implementation attempts from the event trace. -/
def attempts {Operator : Type*}
    (protocol : FiniteProtocol Operator) : List (ImplementationAttempt Operator) :=
  protocol.events.filterMap fun event =>
    match event with
    | .implementation attempt => some attempt
    | .yieldReadout _ => none
    | .reclaimReadout _ => none

/-- The source-required decidable activity test. -/
def activeAt {Operator : Type*}
    (attempt : ImplementationAttempt Operator) (time : Nat) : Bool :=
  decide (attempt.implementationStart <= time /\ time < attempt.implementationEnd)

/-- Atomic trace visibility: a recorded claim becomes visible exactly after the
declared delay. -/
def AtomicallyVisible {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) : Prop :=
  forall attempt, attempt ∈ attempts protocol -> forall time,
    protocol.claimVisible attempt time =
      decide (attempt.claimTime + protocol.visibilityDelay <= time)

/-- T4 is a trajectory predicate, not a Lean axiom.  Its first conjunct enforces
active-holder yield plus an affected readout.  Its second permits a reclaim only
after the declared stall threshold and with an atomic reclaim record. -/
def T4Compliant {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) : Prop :=
  (forall holder, holder ∈ attempts protocol ->
    forall contender, contender ∈ attempts protocol ->
    holder.operator ≠ contender.operator -> forall time,
    activeAt holder time = true ->
    protocol.claimVisible holder time = true ->
      activeAt contender time = false /\
        exists readout,
          ProtocolEvent.yieldReadout readout ∈ protocol.events /\
          readout.yieldingOperator = contender.operator /\
          readout.holder = holder.operator /\ readout.time = time) /\
  (forall contender, contender ∈ attempts protocol -> forall previousHolder,
    contender.claimKind = ClaimKind.reclaimed previousHolder ->
      exists holder, holder ∈ attempts protocol /\
        holder.operator = previousHolder /\
        holder.implementationEnd + protocol.stallThreshold <= contender.claimTime /\
        exists readout,
          ProtocolEvent.reclaimReadout readout ∈ protocol.events /\
          readout.reclaimer = contender.operator /\
          readout.previousHolder = previousHolder /\
          readout.time = contender.claimTime)

/-- The complete compliant carrier packages both defining operational laws as
proof fields. -/
structure T4CompliantTrajectory (Operator : Type*) [DecidableEq Operator]
    extends FiniteProtocol Operator where
  atomicallyVisible : AtomicallyVisible toFiniteProtocol
  t4Compliant : T4Compliant toFiniteProtocol

/-- Two distinct operators are simultaneously implementing at one time. -/
def ConcurrentImplementation {Operator : Type*} [DecidableEq Operator]
    (first second : ImplementationAttempt Operator) (time : Nat) : Prop :=
  first.operator ≠ second.operator /\
    activeAt first time = true /\ activeAt second time = true

/-- The time has not yet left one claim's atomic visibility-delay window. -/
def WithinVisibilityWindow {Operator : Type*}
    (protocol : FiniteProtocol Operator)
    (attempt : ImplementationAttempt Operator) (time : Nat) : Prop :=
  time < attempt.claimTime + protocol.visibilityDelay

/-- Pointwise no-duplication outside the visibility windows of both claims. -/
def ConcurrencyConfinedToVisibilityWindow
    {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) : Prop :=
  forall first, first ∈ attempts protocol ->
    forall second, second ∈ attempts protocol -> forall time,
      ConcurrentImplementation first second time ->
        WithinVisibilityWindow protocol first time /\
          WithinVisibilityWindow protocol second time

/-- Whether one ordered pair of distinct operators claims within the selected
visibility delay. -/
def collisionPairWithinDelay {Operator : Type*} [DecidableEq Operator]
    (delay : Nat)
    (pair : ImplementationAttempt Operator × ImplementationAttempt Operator) : Bool :=
  decide (pair.1.operator ≠ pair.2.operator /\
    pair.1.claimTime <= pair.2.claimTime /\
    pair.2.claimTime < pair.1.claimTime + delay)

/-- Number of colliding ordered attempt pairs in the finite uniform model. -/
def collisionCount {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) (delay : Nat) : Nat :=
  ((attempts protocol).product (attempts protocol) |>.filter
    (collisionPairWithinDelay delay)).length

/-- The population is the number of ordered attempt pairs, with one as the
empty-model denominator. -/
def collisionPopulation {Operator : Type*}
    (protocol : FiniteProtocol Operator) : Nat :=
  max 1 ((attempts protocol).length * (attempts protocol).length)

/-- Expected collision rate for a uniformly selected ordered attempt pair. -/
def collisionRate {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) (delay : Nat) : Rat :=
  (collisionCount protocol delay : Rat) / collisionPopulation protocol

private theorem filter_length_mono
    {Alpha : Type*} (items : List Alpha) (lower upper : Alpha -> Bool)
    (predicateMono : forall item, lower item = true -> upper item = true) :
    (items.filter lower).length <= (items.filter upper).length := by
  induction items with
  | nil => simp
  | cons item items inductionHypothesis =>
      cases lowerValue : lower item <;> cases upperValue : upper item
      · simpa [List.filter, lowerValue, upperValue] using inductionHypothesis
      · simp only [List.filter, lowerValue, upperValue, List.length_cons]
        omega
      · exact False.elim (Bool.false_ne_true
          (upperValue.symm.trans (predicateMono item lowerValue)))
      · simp [List.filter, lowerValue, upperValue, inductionHypothesis]

private theorem collision_pair_mono
    {Operator : Type*} [DecidableEq Operator]
    {lowerDelay upperDelay : Nat} (delayIncrease : lowerDelay <= upperDelay)
    (pair : ImplementationAttempt Operator × ImplementationAttempt Operator)
    (collides : collisionPairWithinDelay lowerDelay pair = true) :
    collisionPairWithinDelay upperDelay pair = true := by
  simp only [collisionPairWithinDelay, decide_eq_true_eq] at collides ⊢
  exact ⟨collides.1, collides.2.1,
    Nat.lt_of_lt_of_le collides.2.2
      (Nat.add_le_add_left delayIncrease pair.1.claimTime)⟩

private theorem collision_count_mono
    {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) : Monotone (collisionCount protocol) := by
  intro lowerDelay upperDelay delayIncrease
  exact filter_length_mono ((attempts protocol).product (attempts protocol))
    (collisionPairWithinDelay lowerDelay)
    (collisionPairWithinDelay upperDelay)
    (collision_pair_mono delayIncrease)

private theorem collision_rate_mono
    {Operator : Type*} [DecidableEq Operator]
    (protocol : FiniteProtocol Operator) : Monotone (collisionRate protocol) := by
  intro lowerDelay upperDelay delayIncrease
  have countIncrease :
      collisionCount protocol lowerDelay <= collisionCount protocol upperDelay :=
    collision_count_mono protocol delayIncrease
  have rationalCountIncrease :
      (collisionCount protocol lowerDelay : Rat) <=
        (collisionCount protocol upperDelay : Rat) := by
    exact_mod_cast countIncrease
  have positivePopulationNat : 0 < collisionPopulation protocol := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_max_left 1
        ((attempts protocol).length * (attempts protocol).length))
  have positivePopulationRat : (0 : Rat) < collisionPopulation protocol := by
    exact_mod_cast positivePopulationNat
  exact (div_le_div_iff_of_pos_right positivePopulationRat).2 rationalCountIncrease

private theorem concurrency_confined
    {Operator : Type*} [DecidableEq Operator]
    (trajectory : T4CompliantTrajectory Operator) :
    ConcurrencyConfinedToVisibilityWindow trajectory.toFiniteProtocol := by
  intro first firstMem second secondMem time concurrent
  rcases concurrent with ⟨operatorsDiffer, firstActive, secondActive⟩
  constructor
  · by_contra outsideFirstWindow
    have firstVisibleBoundary :
        first.claimTime + trajectory.visibilityDelay <= time :=
      Nat.le_of_not_gt outsideFirstWindow
    have firstVisible : trajectory.claimVisible first time = true := by
      calc
        trajectory.claimVisible first time =
            decide (first.claimTime + trajectory.visibilityDelay <= time) :=
          trajectory.atomicallyVisible first firstMem time
        _ = true := by simp [firstVisibleBoundary]
    have contenderInactive :=
      (trajectory.t4Compliant.1 first firstMem second secondMem
        operatorsDiffer time firstActive firstVisible).1
    rw [secondActive] at contenderInactive
    contradiction
  · by_contra outsideSecondWindow
    have secondVisibleBoundary :
        second.claimTime + trajectory.visibilityDelay <= time :=
      Nat.le_of_not_gt outsideSecondWindow
    have secondVisible : trajectory.claimVisible second time = true := by
      calc
        trajectory.claimVisible second time =
            decide (second.claimTime + trajectory.visibilityDelay <= time) :=
          trajectory.atomicallyVisible second secondMem time
        _ = true := by simp [secondVisibleBoundary]
    have contenderInactive :=
      (trajectory.t4Compliant.1 second secondMem first firstMem
        operatorsDiffer.symm time secondActive secondVisible).1
    rw [firstActive] at contenderInactive
    contradiction

/-- T-F: a finite T4-compliant trajectory with atomically visible traces has no
concurrent implementation outside the visibility-delay windows.  On the same
finite carrier, the expected ordered-pair collision rate is monotone in delay. -/
theorem t4_atomic_visibility_nonduplication_and_collision_rate_monotone
    {Operator : Type*} [DecidableEq Operator]
    (trajectory : T4CompliantTrajectory Operator) :
    ConcurrencyConfinedToVisibilityWindow trajectory.toFiniteProtocol /\
      Monotone (collisionRate trajectory.toFiniteProtocol) := by
  exact ⟨concurrency_confined trajectory,
    collision_rate_mono trajectory.toFiniteProtocol⟩

#print axioms t4_atomic_visibility_nonduplication_and_collision_rate_monotone

private inductive SampleOperator where
  | alice
  | bob
deriving DecidableEq, Repr

private def aliceAttempt : ImplementationAttempt SampleOperator where
  operator := .alice
  claimTime := 0
  implementationStart := 0
  implementationEnd := 1
  claimKind := .firstCollision

private def bobAttempt : ImplementationAttempt SampleOperator where
  operator := .bob
  claimTime := 0
  implementationStart := 0
  implementationEnd := 1
  claimKind := .firstCollision

/-- A nontrivial visibility-window collision: both first claims implement at time
zero, while their atomic traces become visible only at time two. -/
def sampleProtocol : FiniteProtocol SampleOperator where
  events := [.implementation aliceAttempt, .implementation bobAttempt]
  visibilityDelay := 2
  stallThreshold := 3
  claimVisible := fun attempt time => decide (attempt.claimTime + 2 <= time)

/-- The hypotheses are jointly satisfiable even with a genuine collision inside
the permitted delay window. -/
def sampleCompliantTrajectory : T4CompliantTrajectory SampleOperator where
  toFiniteProtocol := sampleProtocol
  atomicallyVisible := by
    intro attempt _ time
    rfl
  t4Compliant := by
    constructor
    · intro holder holderMem contender contenderMem operatorsDiffer time holderActive visible
      simp only [attempts, sampleProtocol, List.filterMap_cons, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at holderMem contenderMem
      rcases holderMem with rfl | rfl <;> rcases contenderMem with rfl | rfl
      all_goals simp [aliceAttempt, bobAttempt] at operatorsDiffer
      all_goals simp [activeAt, sampleProtocol, aliceAttempt, bobAttempt] at holderActive visible
      all_goals omega
    · intro contender contenderMem previousHolder reclaimed
      simp only [attempts, sampleProtocol, List.filterMap_cons, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at contenderMem
      rcases contenderMem with rfl | rfl
      all_goals simp [aliceAttempt, bobAttempt] at reclaimed

-- Domain and complete antecedent inhabitance are kernel checked.
example : T4CompliantTrajectory SampleOperator := sampleCompliantTrajectory

-- The theorem is not an unconditional no-collision claim: its allowed window is inhabited.
example : ConcurrentImplementation aliceAttempt bobAttempt 0 := by
  refine ⟨?_, rfl, rfl⟩
  decide

example :
    WithinVisibilityWindow sampleProtocol aliceAttempt 0 /\
      WithinVisibilityWindow sampleProtocol bobAttempt 0 := by
  simp [WithinVisibilityWindow, sampleProtocol, aliceAttempt, bobAttempt]

-- Increasing delay strictly exposes more colliding ordered pairs in the sample.
example :
    collisionCount sampleProtocol 0 = 0 /\
      collisionCount sampleProtocol 1 = 2 := by
  decide

end D5.S3.ConceptDynamics.OperationalTuition.FirstClaimProtocolNonduplication
