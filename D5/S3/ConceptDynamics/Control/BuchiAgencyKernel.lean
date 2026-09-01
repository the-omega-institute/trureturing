/- GID: D5/S3/ConceptDynamics/Control/BuchiAgencyKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/BuchiAgencyKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The nested robust Buchi kernel admits a safe policy with infinitely many renewals. -/

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
import Mathlib.Data.Fintype.Order
import Mathlib.Order.FixedPoints

/- Library-search audit trail (2026-09-01):
   * Repository searches for live agency, Buchi objectives, renewal sets,
     regional attractors, repeated robust reachability, and content-equivalent
     safety-plus-liveness statements found the reusable `ControlSystem`,
     `controlPredecessor`, and finite reachability family, but no theorem
     combining the inner attractor with an outer greatest fixed point.
   * The adjacent maximal safe controllable-domain theorem supplies only
     indefinite safety. The recovery theorem supplies only one bounded visit;
     neither entails infinitely many visits to a renewal set.
   * Pinned Mathlib supplies `OrderHom.map_lfp`, `OrderHom.map_gfp`,
     `OrderHom.lfp_le`, and `OrderHom.le_gfp`. Searches for Buchi games,
     safety games, winning strategies, and repeated attractors found no
     packaged theorem with the present adversarial control semantics.
   * NyxID-proxied ecosystem searches for Lean 4 Buchi-game and
     greatest-fixed-point winning-region formalizations found general game
     theory and combinatorial-game projects, but no reusable exact result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.BuchiAgencyKernel

open D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- Finite robust-reachability layers inside `region`. The zeroth layer is the
goal; each later layer retains all earlier states and adds regional states with
an action whose every possible successor lies in the preceding layer. -/
def regionalReachStage {State : Type*} (system : ControlSystem State)
    (region goal : Set State) : Nat → Set State
  | 0 => goal
  | n + 1 => regionalReachStage system region goal n ∪
      (region ∩ controlPredecessor system
        (regionalReachStage system region goal n))

/-- The finite-state regional attractor, presented as the union of its
finite-arrival-rank layers. -/
def regionalAttractor {State : Type*} (system : ControlSystem State)
    (region goal : Set State) : Set State :=
  ⋃ n, regionalReachStage system region goal n

/-- The monotone operator whose least fixed point is regional robust
reachability. -/
def regionalAttractorOperator {State : Type*} (system : ControlSystem State)
    (region goal : Set State) : Set State →o Set State where
  toFun reached := goal ∪ (region ∩ controlPredecessor system reached)
  monotone' := by
    intro smaller larger inclusion state membership
    rcases membership with atGoal | ⟨inRegion, action, successors⟩
    · exact Or.inl atGoal
    · exact Or.inr ⟨inRegion, action, fun next isSuccessor =>
        inclusion (successors isSuccessor)⟩

private theorem regionalReachStage_mono_index {State : Type*}
    (system : ControlSystem State) (region goal : Set State) {m n : Nat}
    (hmn : m ≤ n) :
    regionalReachStage system region goal m ⊆
      regionalReachStage system region goal n := by
  induction n generalizing m with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Set.Subset.rfl
  | succ n inductionHypothesis =>
      by_cases atTop : m = n + 1
      · subst m
        exact Set.Subset.rfl
      · have below : m ≤ n :=
          Nat.le_of_lt_succ (lt_of_le_of_ne hmn atTop)
        exact Set.Subset.trans (inductionHypothesis below)
          (fun state membership => Or.inl membership)

private theorem regionalReachStage_mono_parameters {State : Type*}
    (system : ControlSystem State)
    {smallerRegion largerRegion smallerGoal largerGoal : Set State}
    (regionInclusion : smallerRegion ⊆ largerRegion)
    (goalInclusion : smallerGoal ⊆ largerGoal) (n : Nat) :
    regionalReachStage system smallerRegion smallerGoal n ⊆
      regionalReachStage system largerRegion largerGoal n := by
  induction n with
  | zero => exact goalInclusion
  | succ n inductionHypothesis =>
      intro state membership
      rcases membership with earlier | ⟨inRegion, action, successors⟩
      · exact Or.inl (inductionHypothesis earlier)
      · exact Or.inr ⟨regionInclusion inRegion, action,
          fun next isSuccessor =>
            inductionHypothesis (successors isSuccessor)⟩

private theorem regionalReachStage_subset_operator_lfp {State : Type*}
    (system : ControlSystem State) (region goal : Set State) (n : Nat) :
    regionalReachStage system region goal n ⊆
      (regionalAttractorOperator system region goal).lfp := by
  let operator := regionalAttractorOperator system region goal
  have fixedPoint : operator operator.lfp = operator.lfp := operator.map_lfp
  induction n with
  | zero =>
      intro state atGoal
      have : state ∈ operator operator.lfp := Or.inl atGoal
      rwa [fixedPoint] at this
  | succ n inductionHypothesis =>
      intro state membership
      rcases membership with earlier | ⟨inRegion, action, successors⟩
      · exact inductionHypothesis earlier
      · have : state ∈ operator operator.lfp :=
          Or.inr ⟨inRegion, action, fun next isSuccessor =>
            inductionHypothesis (successors isSuccessor)⟩
        rwa [fixedPoint] at this

/-- On a finite state space, finite regional reachability layers realize the
least fixed point of `Y ↦ goal ∪ (region ∩ CPre(Y))`. Thus membership carries a
finite arrival rank, rather than merely an abstract fixed-point witness. -/
theorem regional_attractor_eq_lfp {State : Type*} [Fintype State]
    (system : ControlSystem State) (region goal : Set State) :
    regionalAttractor system region goal =
      (regionalAttractorOperator system region goal).lfp := by
  classical
  apply Set.Subset.antisymm
  · intro state membership
    rcases Set.mem_iUnion.mp membership with ⟨n, inStage⟩
    exact regionalReachStage_subset_operator_lfp system region goal n inStage
  · apply (regionalAttractorOperator system region goal).lfp_le
    intro state membership
    rcases membership with atGoal | ⟨inRegion, action, successors⟩
    · exact Set.mem_iUnion.mpr ⟨0, atGoal⟩
    · let successorRank : State → Nat := fun next =>
        if isSuccessor : next ∈ system.successor action then
          Nat.find (Set.mem_iUnion.mp (successors isSuccessor))
        else 0
      let bound : Nat := Finset.univ.sup successorRank
      have successorsInBound :
          system.successor action ⊆
            regionalReachStage system region goal bound := by
        intro next isSuccessor
        have rankSpec : next ∈ regionalReachStage system region goal
            (successorRank next) := by
          simp only [successorRank, dif_pos isSuccessor]
          exact Nat.find_spec (Set.mem_iUnion.mp (successors isSuccessor))
        have rankLeBound : successorRank next ≤ bound := by
          exact Finset.le_sup (s := Finset.univ) (f := successorRank)
            (Finset.mem_univ next)
        exact regionalReachStage_mono_index system region goal rankLeBound
          rankSpec
      exact Set.mem_iUnion.mpr ⟨bound + 1,
        Or.inr ⟨inRegion, action, successorsInBound⟩⟩

/-- The robust predecessor as an order homomorphism on state sets. -/
def robustPredecessor {State : Type*} (system : ControlSystem State) :
    Set State →o Set State where
  toFun := controlPredecessor system
  monotone' := by
    intro smaller larger inclusion state membership
    rcases membership with ⟨action, successors⟩
    exact ⟨action, fun next isSuccessor => inclusion (successors isSuccessor)⟩

/-- The robust freedom-preserving kernel `ν Z. CPre(Z)`. The carrier `State`
represents the agency-safe state space. -/
def robustFreedomKernel {State : Type*} (system : ControlSystem State) :
    Set State :=
  (robustPredecessor system).gfp

/-- The outer operator for repeated renewal: inside candidate `region`, reach
a renewal state that also has a robust action back into `region`. -/
def liveAgencyOperator {State : Type*} (system : ControlSystem State)
    (renew : Set State) : Set State →o Set State where
  toFun := fun region => regionalAttractor system region
    (renew ∩ controlPredecessor system region)
  monotone' := by
    intro smaller larger inclusion state membership
    rcases Set.mem_iUnion.mp membership with ⟨n, inStage⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, regionalReachStage_mono_parameters system inclusion ?_ n inStage⟩
    intro current currentGoal
    exact ⟨currentGoal.1, by
      rcases currentGoal.2 with ⟨action, successors⟩
      exact ⟨action, fun next isSuccessor =>
        inclusion (successors isSuccessor)⟩⟩

/-- The agency-liveness kernel is the greatest fixed point of repeated
regional renewal. -/
def liveAgency {State : Type*} (system : ControlSystem State)
    (renew : Set State) : Set State :=
  (liveAgencyOperator system renew).gfp

/-- A trajectory follows a policy on `domain` when every next state is an
allowed adversarial successor of the policy action. The membership argument
keeps the policy honest when actions exist only on the certified domain. -/
def FollowsWithin {State : Type*} (system : ControlSystem State)
    (domain : Set State)
    (policy : (state : {state // state ∈ domain}) → system.Action state.1)
    (trajectory : Nat → State) : Prop :=
  ∀ t (inDomain : trajectory t ∈ domain),
    trajectory (t + 1) ∈ system.successor
      (policy ⟨trajectory t, inDomain⟩)

/-- In a finite adversarial game, the nested agency-liveness kernel lies in
the robust freedom kernel. Moreover, one policy keeps every compatible
trajectory permanently in that safe kernel and visits `renew` beyond every
time bound. The supplied natural-number rank strictly decreases between
renewals and is reset only after a renewal state is reached. -/
theorem live_agency_buchi_kernel {State : Type*} [Fintype State]
    (system : ControlSystem State) (renew : Set State) :
    let live := liveAgency system renew
    let free := robustFreedomKernel system
    ∃ rank : {state // state ∈ live} → Nat,
      ∃ policy : (state : {state // state ∈ live}) →
          system.Action state.1,
        ∃ closed : ∀ state, system.successor (policy state) ⊆ live,
        live ⊆ free ∧
        (∀ state next
            (isSuccessor : next ∈ system.successor (policy state)),
          state.1 ∉ renew →
            rank ⟨next, closed state isSuccessor⟩ < rank state) ∧
        ∀ trajectory : Nat → State,
          trajectory 0 ∈ live →
          FollowsWithin system live policy trajectory →
          (∀ t, trajectory t ∈ free) ∧
            ∀ N, ∃ n, N ≤ n ∧ trajectory n ∈ renew := by
  classical
  let live := liveAgency system renew
  let free := robustFreedomKernel system
  let liveOperator := liveAgencyOperator system renew
  have liveFixed : liveOperator live = live := liveOperator.map_gfp
  have stageExists : ∀ state : {state // state ∈ live},
      ∃ n, state.1 ∈ regionalReachStage system live
        (renew ∩ controlPredecessor system live) n := by
    intro state
    have inOperator : state.1 ∈ liveOperator live := by
      rw [liveFixed]
      exact state.2
    exact Set.mem_iUnion.mp inOperator
  let rank : {state // state ∈ live} → Nat := fun state =>
    Nat.find (stageExists state)
  have rankSpec : ∀ state : {state // state ∈ live},
      state.1 ∈ regionalReachStage system live
        (renew ∩ controlPredecessor system live) (rank state) := by
    intro state
    exact Nat.find_spec (stageExists state)
  have stageSubsetLive : ∀ n,
      regionalReachStage system live
          (renew ∩ controlPredecessor system live) n ⊆ live := by
    intro n state inStage
    have inOperator : state ∈ liveOperator live :=
      Set.mem_iUnion.mpr ⟨n, inStage⟩
    rwa [liveFixed] at inOperator
  have actionExists : ∀ state : {state // state ∈ live},
      ∃ action : system.Action state.1,
        ∃ closed : system.successor action ⊆ live,
          (state.1 ∉ renew →
            ∀ next (isSuccessor : next ∈ system.successor action),
              rank ⟨next, closed isSuccessor⟩ < rank state) := by
    intro state
    have atRank := rankSpec state
    cases rankValue : rank state with
    | zero =>
        have atGoal : state.1 ∈
            renew ∩ controlPredecessor system live := by
          simpa [rankValue, regionalReachStage] using atRank
        rcases atGoal.2 with ⟨action, successors⟩
        refine ⟨action, successors, ?_⟩
        intro notRenew
        exact (notRenew atGoal.1).elim
    | succ n =>
        have notEarlier : state.1 ∉ regionalReachStage system live
            (renew ∩ controlPredecessor system live) n := by
          apply Nat.find_min (stageExists state)
          change n < rank state
          rw [rankValue]
          exact Nat.lt_succ_self n
        have atSuccessorStage : state.1 ∈
            regionalReachStage system live
                (renew ∩ controlPredecessor system live) n ∪
              (live ∩ controlPredecessor system
                (regionalReachStage system live
                  (renew ∩ controlPredecessor system live) n)) := by
          simpa [rankValue, regionalReachStage] using atRank
        rcases atSuccessorStage with earlier | ⟨_inLive, action, successors⟩
        · exact (notEarlier earlier).elim
        · have successorsLive : system.successor action ⊆ live := fun next h =>
            stageSubsetLive n (successors h)
          refine ⟨action, successorsLive, ?_⟩
          intro _notRenew next isSuccessor
          have nextRankLe :
              rank ⟨next, successorsLive isSuccessor⟩ ≤ n := by
            exact Nat.find_min' (stageExists ⟨next,
              successorsLive isSuccessor⟩) (successors isSuccessor)
          simpa [rankValue] using Nat.lt_succ_of_le nextRankLe
  let policy : (state : {state // state ∈ live}) → system.Action state.1 :=
    fun state => Classical.choose (actionExists state)
  let closed : ∀ state, system.successor (policy state) ⊆ live := fun state =>
    Classical.choose (Classical.choose_spec (actionExists state))
  have progress : ∀ state : {state // state ∈ live},
      state.1 ∉ renew →
        ∀ next (isSuccessor : next ∈ system.successor (policy state)),
          rank ⟨next, closed state isSuccessor⟩ < rank state := by
    intro state
    exact Classical.choose_spec (Classical.choose_spec (actionExists state))
  have livePostfixed : live ⊆ robustPredecessor system live := by
    intro state inLive
    exact ⟨policy ⟨state, inLive⟩, closed ⟨state, inLive⟩⟩
  have liveSubsetFree : live ⊆ free := by
    exact (robustPredecessor system).le_gfp livePostfixed
  refine ⟨rank, policy, closed, liveSubsetFree, ?_, ?_⟩
  · intro state next isSuccessor notRenew
    exact progress state notRenew next isSuccessor
  · intro trajectory startsLive follows
    have staysLive : ∀ t, trajectory t ∈ live := by
      intro t
      induction t with
      | zero => exact startsLive
      | succ t inductionHypothesis =>
          exact closed ⟨trajectory t, inductionHypothesis⟩
            (follows t inductionHypothesis)
    refine ⟨fun t => liveSubsetFree (staysLive t), ?_⟩
    let pathRank : Nat → Nat := fun t => rank ⟨trajectory t, staysLive t⟩
    have rankDescends : ∀ t, trajectory t ∉ renew →
        pathRank (t + 1) < pathRank t := by
      intro t notRenew
      have step := follows t (staysLive t)
      have decrease := progress ⟨trajectory t, staysLive t⟩
        notRenew (trajectory (t + 1)) step
      simpa only [pathRank] using decrease
    have reachesRenew : ∀ budget, ∀ t, pathRank t ≤ budget →
        ∃ offset, offset ≤ budget ∧ trajectory (t + offset) ∈ renew := by
      intro budget
      induction budget using Nat.strong_induction_on with
      | h budget inductionHypothesis =>
          intro t rankLe
          by_cases atRenew : trajectory t ∈ renew
          · exact ⟨0, Nat.zero_le budget, by simpa using atRenew⟩
          · have nextRankLt : pathRank (t + 1) < budget :=
              (rankDescends t atRenew).trans_le rankLe
            obtain ⟨offset, offsetLe, reaches⟩ :=
              inductionHypothesis (pathRank (t + 1)) nextRankLt
                (t + 1) (le_refl _)
            refine ⟨offset + 1, Nat.succ_le_of_lt
              (offsetLe.trans_lt nextRankLt), ?_⟩
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reaches
    intro N
    obtain ⟨offset, _offsetLe, atRenew⟩ :=
      reachesRenew (pathRank N) N (le_refl _)
    exact ⟨N + offset, Nat.le_add_right N offset, atRenew⟩

#print axioms regional_attractor_eq_lfp
#print axioms live_agency_buchi_kernel

end D5.S3.ConceptDynamics.Control.BuchiAgencyKernel
