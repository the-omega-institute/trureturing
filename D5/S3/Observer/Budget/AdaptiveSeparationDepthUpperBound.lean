/- GID: D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pair separation gives an adaptive tree of depth at most states minus one. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import Mathlib

/- Library-search audit trail (2026-08-28):
   * Exact repository searches for adaptive upper bounds, identifying trees, and
     `Fintype.card State - 1` found no theorem constructing the source tree.
   * The frozen `PassiveProtocol` and `runPassiveProtocol` declarations are the
     canonical dependent decision-tree carrier and executor, and are reused here.
   * `WorstCaseDepthInformationLowerBound` uses a fixed finite answer alphabet,
     while the source permits an arbitrary common answer type, so its tree is not
     the source carrier for this upper bound.
   * Exact pinned-Mathlib hits `Finset.strongInduction`, `Finset.one_lt_card`,
     `Finset.ssubset_iff_subset_ne`, and `Finset.card_lt_card` support the finite
     candidate-set recursion. No packaged separating-tree theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.AdaptiveSeparationDepthUpperBound

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

universe u v w

private theorem exists_bounded_separating_protocol
    {State : Type u} {Protocol : Type v} {Answer : Type w}
    (readout : Protocol -> State -> Answer)
    (separates : forall left right, left ≠ right ->
      exists selected, readout selected left ≠ readout selected right)
    (candidates : Finset State) :
    exists tree : PassiveProtocol Protocol (fun _ => Answer),
      (forall left right, left ∈ candidates -> right ∈ candidates ->
        runPassiveProtocol readout tree left =
          runPassiveProtocol readout tree right -> left = right) ∧
      forall state, state ∈ candidates ->
        (runPassiveProtocol readout tree state).length <= candidates.card - 1 := by
  classical
  induction candidates using Finset.strongInduction with
  | H candidates inductionHypothesis =>
      by_cases small : candidates.card <= 1
      · refine ⟨.stop, ?_, ?_⟩
        · intro left right leftMem rightMem _sameTranscript
          exact Finset.card_le_one.mp small left leftMem right rightMem
        · intro state stateMem
          simp only [runPassiveProtocol, List.length_nil]
          exact Nat.zero_le _
      · have one_lt : 1 < candidates.card := Nat.lt_of_not_ge small
        obtain ⟨left, leftMem, right, rightMem, left_ne_right⟩ :=
          Finset.one_lt_card.mp one_lt
        obtain ⟨selected, distinguishes⟩ := separates left right left_ne_right
        let fiber : Answer -> Finset State := fun answer =>
          candidates.filter fun state => readout selected state = answer
        have fiber_ssubset (answer : Answer) : fiber answer ⊂ candidates := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro state stateMem
            exact (Finset.mem_filter.mp stateMem).1
          · intro fiber_eq
            by_cases leftAnswer : readout selected left = answer
            · have rightAnswer : readout selected right ≠ answer := by
                intro equality
                exact distinguishes (leftAnswer.trans equality.symm)
              have rightNotMem : right ∉ fiber answer := by
                simp only [fiber, Finset.mem_filter, rightMem, rightAnswer,
                  and_false, not_false_eq_true]
              rw [fiber_eq] at rightNotMem
              exact rightNotMem rightMem
            · have leftNotMem : left ∉ fiber answer := by
                simp only [fiber, Finset.mem_filter, leftMem, leftAnswer,
                  and_false, not_false_eq_true]
              rw [fiber_eq] at leftNotMem
              exact leftNotMem leftMem
        have subtreeExists (answer : Answer) :=
          inductionHypothesis (fiber answer) (fiber_ssubset answer)
        let subtree : Answer -> PassiveProtocol Protocol (fun _ => Answer) :=
          fun answer => Classical.choose (subtreeExists answer)
        have subtreeSpec (answer : Answer) :=
          Classical.choose_spec (subtreeExists answer)
        refine ⟨.query selected subtree, ?_, ?_⟩
        · intro first second firstMem secondMem sameTranscript
          have headEq :
              (⟨selected, readout selected first⟩ : Sigma fun _ : Protocol => Answer) =
                ⟨selected, readout selected second⟩ := by
            exact (List.cons.inj sameTranscript).1
          have answerEq : readout selected first = readout selected second := by
            simpa using headEq
          have firstFiber : first ∈ fiber (readout selected first) := by
            simp only [fiber, Finset.mem_filter, firstMem, and_true]
          have secondFiber : second ∈ fiber (readout selected first) := by
            simp only [fiber, Finset.mem_filter, secondMem, true_and]
            exact answerEq.symm
          apply (subtreeSpec (readout selected first)).1 first second
            firstFiber secondFiber
          have tailEq := (List.cons.inj sameTranscript).2
          simpa only [answerEq] using tailEq
        · intro state stateMem
          have stateFiber : state ∈ fiber (readout selected state) := by
            simp only [fiber, Finset.mem_filter, stateMem, and_true]
          have tailBound :=
            (subtreeSpec (readout selected state)).2 state stateFiber
          change
            (runPassiveProtocol readout
              (subtree (readout selected state)) state).length <=
                (fiber (readout selected state)).card - 1 at tailBound
          have fiberPos : 0 < (fiber (readout selected state)).card :=
            Finset.card_pos.mpr ⟨state, stateFiber⟩
          have fiberCardLt :
              (fiber (readout selected state)).card < candidates.card :=
            Finset.card_lt_card (fiber_ssubset (readout selected state))
          simp only [runPassiveProtocol, List.length_cons]
          omega

/-- A pair-separating family of protocols on a finite state quotient admits an
adaptive identifying tree whose every realized branch has length at most one
less than the number of quotient states. -/
theorem adaptive_separation_depth_upper_bound
    {State : Type u} {Protocol : Type v} {Answer : Type w} [Fintype State]
    (readout : Protocol -> State -> Answer)
    (separates : forall left right, left ≠ right ->
      exists selected, readout selected left ≠ readout selected right) :
    exists tree : PassiveProtocol Protocol (fun _ => Answer),
      Function.Injective (runPassiveProtocol readout tree) ∧
        forall state,
          (runPassiveProtocol readout tree state).length <=
            Fintype.card State - 1 := by
  classical
  obtain ⟨tree, identifies, depthBound⟩ :=
    exists_bounded_separating_protocol readout separates Finset.univ
  refine ⟨tree, ?_, ?_⟩
  · intro left right sameTranscript
    exact identifies left right (Finset.mem_univ left) (Finset.mem_univ right)
      sameTranscript
  · intro state
    simpa only [Finset.card_univ] using depthBound state (Finset.mem_univ state)

#print axioms adaptive_separation_depth_upper_bound

end D5.S3.Observer.Budget.AdaptiveSeparationDepthUpperBound
