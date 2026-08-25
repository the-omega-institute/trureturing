/- GID: D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three relative witnesses include zero horizons; finite states stabilize. -/
/- Library-search audit trail (2026-08-25):
   * All eight existing modules in `ConceptDynamics/Sufficiency` were listed and read by
     digest; `UniversalSufficiencyFactorization` supplies the required sufficiency criterion.
   * `TargetKnowledgeWithoutWorldKnowledge` has an adjacent Boolean-pair example, but it
     proves failure of concept equivalence rather than target insufficiency on `Fin 2` pairs.
   * `CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer.2` is the exact
     interventional/counterfactual witness and is reused directly instead of rebuilding an SCM.
   * Repository searches for finite-window versus all-future sufficiency found no exact result.
     The exact finite-state boundary is `FiniteHistoryStability.finite_history_stability`.
   * Pinned Mathlib search found `Function.ne_iff` and `Finset.le_sup`, but no theorem packaging
     the three requested target upgrades; the infinite-stream prefix witness is proved locally. -/

import D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
import D5.S3.Observer.Separation.FiniteHistoryStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-- A two-coordinate payoff state; the first coordinate determines the chosen action. -/
abbrev PayoffState := Fin 2 × Fin 2

/-- The decision interface retains only the coarse argmax-class coordinate. -/
def decisionInterface : PayoffState → Fin 2 :=
  Prod.fst

/-- The decision target asks only for the argmax-class coordinate. -/
def decisionTarget : PayoffState → Fin 2 :=
  Prod.fst

/-- The complete payoff profile retains both coordinates. -/
def payoffProfile : PayoffState → PayoffState :=
  id

/-- On the concrete four-state payoff space, the first-coordinate interface is sufficient for
the decision target but insufficient for the complete payoff profile. -/
theorem decision_target_sufficient_but_payoff_profile_not :
    Refines (canonicalTargetReadout decisionTarget) decisionInterface ∧
      ¬Refines (canonicalTargetReadout payoffProfile) decisionInterface := by
  constructor
  · have criterion :=
      universal_sufficiency_factorization decisionInterface decisionTarget
    apply criterion.1.mpr
    apply criterion.2.mpr
    intro x y hxy
    exact hxy
  · intro profileSufficient
    have criterion :=
      universal_sufficiency_factorization decisionInterface payoffProfile
    have fiberConstant := criterion.2.mp (criterion.1.mp profileSufficient)
    have profileEquality : ((0, 0) : PayoffState) = (0, 1) :=
      fiberConstant rfl
    have zero_ne_one : (0 : Fin 2) ≠ 1 := by decide
    exact zero_ne_one (congrArg Prod.snd profileEquality)

#print axioms decision_target_sufficient_but_payoff_profile_not

/-- The single-world target is the table of interventional marginals. -/
def interventionMarginal (model : DeterministicBoolSCM) : Bool → Bool → Nat :=
  Int model

/-- The cross-world target is the unit-level counterfactual joint table. -/
def counterfactualJoint (model : DeterministicBoolSCM) : Bool → Bool → Bool → Bool :=
  CF model

/-- The interventional table is sufficient for itself but not for the counterfactual joint,
using the existing pair of deterministic Boolean causal models as the strict witness. -/
theorem interventional_marginal_sufficient_but_counterfactual_joint_not :
    Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
      ¬Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal := by
  letI : Nonempty DeterministicBoolSCM := ⟨noEffectModel⟩
  constructor
  · have criterion :=
      universal_sufficiency_factorization interventionMarginal interventionMarginal
    apply criterion.1.mpr
    apply criterion.2.mpr
    intro first second hsame
    exact hsame
  · intro jointSufficient
    have criterion :=
      universal_sufficiency_factorization interventionMarginal counterfactualJoint
    have fiberConstant := criterion.2.mp (criterion.1.mp jointSufficient)
    rcases counterfactual_kernel_strictly_finer.2 with ⟨first, second, hInt, hCF⟩
    apply hCF
    apply fiberConstant
    simpa only [interventionMarginal] using hInt

#print axioms interventional_marginal_sufficient_but_counterfactual_joint_not

/-- An infinite future is a Boolean value at every natural-numbered time. -/
abbrev InfiniteFuture := Nat → Bool

/-- The interface for horizon `n` records times zero through `n`. -/
def finiteFutureWindow (n : Nat) : InfiniteFuture → (Fin (n + 1) → Bool) :=
  fun future time => future time.1

/-- The complete-future target retains the whole infinite stream. -/
def fullFuture : InfiniteFuture → InfiniteFuture :=
  id

/-- The constantly false future used in every finite-window separation. -/
def zeroFuture : InfiniteFuture :=
  fun _ => false

/-- A future that first differs from `zeroFuture` immediately after horizon `n`. -/
def delayedPulse (n : Nat) : InfiniteFuture :=
  fun time => decide (time = n + 1)

/-- Advance an infinite future by one time step. -/
def streamShift (future : InfiniteFuture) : InfiniteFuture :=
  fun time => future (time + 1)

/-- Observe the current head of an infinite future. -/
def streamHead (future : InfiniteFuture) : Bool :=
  future 0

/-- For every fixed horizon, its finite prefix is sufficient for that prefix target but not for
the complete infinite future. The universal quantifier includes the zero horizon. -/
theorem finite_window_sufficient_but_all_future_not :
    ∀ n : Nat,
      Refines (canonicalTargetReadout (finiteFutureWindow n)) (finiteFutureWindow n) ∧
        ¬Refines (canonicalTargetReadout fullFuture) (finiteFutureWindow n) := by
  intro n
  constructor
  · have criterion :=
      universal_sufficiency_factorization (finiteFutureWindow n) (finiteFutureWindow n)
    apply criterion.1.mpr
    apply criterion.2.mpr
    intro first second hsame
    exact hsame
  · intro futureSufficient
    have criterion :=
      universal_sufficiency_factorization (finiteFutureWindow n) fullFuture
    have fiberConstant := criterion.2.mp (criterion.1.mp futureSufficient)
    have sameWindow : finiteFutureWindow n zeroFuture = finiteFutureWindow n (delayedPulse n) := by
      funext time
      simp [finiteFutureWindow, zeroFuture, delayedPulse, Nat.ne_of_lt time.isLt]
    have sameFuture := fiberConstant sameWindow
    have sameBoundary := congrFun sameFuture (n + 1)
    simp [fullFuture, zeroFuture, delayedPulse] at sameBoundary

#print axioms finite_window_sufficient_but_all_future_not

/-- Finite state spaces cannot realize the preceding strictness forever: their canonical
finite-future relation reaches the all-future relation at the existing stability depth. -/
theorem finite_state_windows_stabilize {X O : Type*} [Finite X]
    (update : X → X) (readout : X → O) :
    finiteFutureRelation update readout (observationStabilityDepth update readout) =
      infiniteFutureRelation update readout := by
  letI : Fintype X := Fintype.ofFinite X
  exact (finite_history_stability update readout).2.2.1

#print axioms finite_state_windows_stabilize

/-- The finite-state hypothesis is necessary for uniform stabilization: on the concrete
left-shift system of Boolean streams, every finite-future relation is strictly coarser than the
all-future relation. Consequently the stream state type is not finite. -/
theorem finite_state_hypothesis_is_necessary :
    (¬Finite InfiniteFuture) ∧
      ∀ n : Nat,
        finiteFutureRelation streamShift streamHead n ≠
          infiniteFutureRelation streamShift streamHead := by
  have observedAt_eq (future : InfiniteFuture) :
      ∀ time : Nat, observedAt streamShift streamHead time future = future time := by
    intro time
    induction time generalizing future with
    | zero => rfl
    | succ time ih =>
        rw [observedAt, Function.iterate_succ_apply]
        change observedAt streamShift streamHead time (streamShift future) = _
        rw [ih]
        rfl
  have strictAtEveryDepth :
      ∀ n : Nat,
        finiteFutureRelation streamShift streamHead n ≠
          infiniteFutureRelation streamShift streamHead := by
    intro n relationsEqual
    have sameFiniteWindow :
        (zeroFuture, delayedPulse n) ∈
          finiteFutureRelation streamShift streamHead n := by
      intro time htime
      rw [observedAt_eq, observedAt_eq]
      simp [zeroFuture, delayedPulse, Nat.ne_of_lt (Nat.lt_succ_of_le htime)]
    have sameAllFuture :
        (zeroFuture, delayedPulse n) ∈
          infiniteFutureRelation streamShift streamHead := by
      rw [← relationsEqual]
      exact sameFiniteWindow
    have sameBoundary := sameAllFuture (n + 1)
    rw [observedAt_eq, observedAt_eq] at sameBoundary
    simp [zeroFuture, delayedPulse] at sameBoundary
  constructor
  · intro finiteStreamState
    letI : Finite InfiniteFuture := finiteStreamState
    exact strictAtEveryDepth (observationStabilityDepth streamShift streamHead)
      (finite_state_windows_stabilize streamShift streamHead)
  · exact strictAtEveryDepth

#print axioms finite_state_hypothesis_is_necessary

/-- Sufficiency is target-relative: decision, cross-world, and infinite-horizon target upgrades
each invalidate an interface that is sufficient for the corresponding coarser target. -/
theorem sufficiency_is_target_relative :
    (Refines (canonicalTargetReadout decisionTarget) decisionInterface ∧
      ¬Refines (canonicalTargetReadout payoffProfile) decisionInterface) ∧
      (Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧
        ¬Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal) ∧
        ∀ n : Nat,
          Refines (canonicalTargetReadout (finiteFutureWindow n)) (finiteFutureWindow n) ∧
            ¬Refines (canonicalTargetReadout fullFuture) (finiteFutureWindow n) := by
  exact ⟨decision_target_sufficient_but_payoff_profile_not,
    interventional_marginal_sufficient_but_counterfactual_joint_not,
    finite_window_sufficient_but_all_future_not⟩

#print axioms sufficiency_is_target_relative

example :
    Refines (canonicalTargetReadout (finiteFutureWindow 0)) (finiteFutureWindow 0) ∧
      ¬Refines (canonicalTargetReadout fullFuture) (finiteFutureWindow 0) :=
  finite_window_sufficient_but_all_future_not 0

example :
    let update : Empty → Empty := fun state => nomatch state
    let readout : Empty → Unit := fun state => nomatch state
    finiteFutureRelation update readout (observationStabilityDepth update readout) =
      infiniteFutureRelation update readout := by
  exact finite_state_windows_stabilize _ _

example :
    let update : Unit → Unit := id
    let readout : Unit → Bool := fun _ => false
    finiteFutureRelation update readout (observationStabilityDepth update readout) =
      infiniteFutureRelation update readout := by
  exact finite_state_windows_stabilize _ _

end D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
