/- GID: D5/S0/Certificates/RationalMomentReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalMomentReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Certificates/RationalMomentElimination]
   digest: A structurally recursive exact checker replays rational support-elimination traces, rejects invalid steps, preserves all moments and support exclusions, and certifies a final d+1 support bound. -/

import D5.S0.Certificates.RationalMomentElimination

/- The trace is untrusted data. The checker validates every step against its
   current weights, then checks the terminal support bound. Gaussian elimination
   and pivot discovery are external producers; their outputs are never trusted.
   Structural recursion proves termination of replay on every finite trace.
   The successful trace length also has an independent support-descent bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalMomentReplay

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination

/-- Replay a finite data trace, stopping with failure at its first invalid step. -/
def replaySteps {n d : Nat} (feature : Fin n → Fin d → ℚ) :
    List (EliminationStep n) → (Fin n → ℚ) → Option (Fin n → ℚ)
  | [], weight => some weight
  | step :: remaining, weight =>
      if checkStep feature weight step = true then
        replaySteps feature remaining (eliminate weight step)
      else none

/-- Every successful trace preserves the complete feature vector and total mass,
never adds a support atom, and spends at least one support point per step. -/
theorem replaySteps_sound {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (steps : List (EliminationStep n)) (weight result : Fin n → ℚ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (success : replaySteps feature steps weight = some result) :
    (∀ i, 0 ≤ result i) ∧
    (∑ i, result i) = (∑ i, weight i) ∧
    (∀ j, linearObjective (fun i => feature i j) result =
      linearObjective (fun i => feature i j) weight) ∧
    activeAtoms result ⊆ activeAtoms weight ∧
    steps.length + (activeAtoms result).card ≤ (activeAtoms weight).card := by
  induction steps generalizing weight with
  | nil =>
      have equal : weight = result := Option.some.inj success
      subst result
      exact ⟨nonnegative, rfl, (fun _ => rfl), (fun _ hi => hi), by simp⟩
  | cons step remaining ih =>
      by_cases checked : checkStep feature weight step = true
      · have valid := (checkStep_eq_true_iff feature weight step).mp checked
        have tail_success : replaySteps feature remaining (eliminate weight step) = some result := by
          simpa only [replaySteps, if_pos checked] using success
        obtain ⟨hn, ht, hm, hs, hc⟩ :=
          ih (eliminate weight step) (validStep_nonnegative valid) tail_success
        have descent := validStep_support valid
        have strict_card := descent.2
        refine ⟨hn, ht.trans (validStep_total valid),
          (fun j => (hm j).trans (validStep_moment valid j)),
          (fun i hi => descent.1 (hs hi)), ?_⟩
        simp only [List.length_cons]
        omega
      · simp only [replaySteps, if_neg checked] at success
        cases success

/-- A normalized raw vector has nonempty active support. -/
theorem activeAtoms_card_pos_of_total_one {n : Nat} (weight : Fin n → ℚ)
    (total : (∑ i, weight i) = 1) : 0 < (activeAtoms weight).card := by
  by_contra not_positive
  have empty : activeAtoms weight = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos not_positive)
  have all_zero : ∀ i, weight i = 0 := by
    intro i
    by_contra nonzero
    have member : i ∈ activeAtoms weight :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, nonzero⟩
    simpa only [empty, Finset.not_mem_empty] using member
  have impossible : (0 : ℚ) = 1 := by simpa only [all_zero, Finset.sum_const_zero] using total
  norm_num at impossible

/-- At most N-1 accepted steps can start from a normalized vector with N active
atoms, regardless of the supplied trace length or producer strategy. -/
theorem replaySteps_length_lt_initial_support {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (steps : List (EliminationStep n))
    (weight result : Fin n → ℚ) (nonnegative : ∀ i, 0 ≤ weight i)
    (total : (∑ i, weight i) = 1)
    (success : replaySteps feature steps weight = some result) :
    steps.length < (activeAtoms weight).card := by
  obtain ⟨_, result_total, _, _, bound⟩ := replaySteps_sound feature steps weight result nonnegative success
  have positive := activeAtoms_card_pos_of_total_one result (result_total.trans total)
  omega

/-- Full certificate consumer: validate the initial probability vector, replay
all steps, and check the mathematical d+1 terminal support bound. -/
def checkCompression {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (steps : List (EliminationStep n)) : Option (Fin n → ℚ) :=
  if (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 then
    match replaySteps feature steps weight with
    | none => none
    | some result => if (activeAtoms result).card ≤ d + 1 then some result else none
  else none

/-- Acceptance certifies normalization, all moment values, support containment,
and the final dimension-dependent support bound on the returned vector. -/
theorem checkCompression_sound {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight result : Fin n → ℚ) (steps : List (EliminationStep n))
    (accepted : checkCompression feature weight steps = some result) :
    (∀ i, 0 ≤ result i) ∧ (∑ i, result i) = 1 ∧
    (∀ j, linearObjective (fun i => feature i j) result =
      linearObjective (fun i => feature i j) weight) ∧
    activeAtoms result ⊆ activeAtoms weight ∧
    (activeAtoms result).card ≤ d + 1 ∧
    steps.length < (activeAtoms weight).card := by
  by_cases initial_ok : (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1
  · cases replay_eq : replaySteps feature steps weight with
    | none => simp only [checkCompression, if_pos initial_ok, replay_eq] at accepted; cases accepted
    | some terminal =>
        by_cases small : (activeAtoms terminal).card ≤ d + 1
        · have equal : terminal = result := by
            simpa only [checkCompression, if_pos initial_ok, replay_eq, if_pos small,
              Option.some.injEq] using accepted
          subst result
          obtain ⟨hn, ht, hm, hs, _⟩ :=
            replaySteps_sound feature steps weight terminal initial_ok.1 replay_eq
          exact ⟨hn, ht.trans initial_ok.2, hm, hs, small,
            replaySteps_length_lt_initial_support feature steps weight terminal
              initial_ok.1 initial_ok.2 replay_eq⟩
        · simp only [checkCompression, if_pos initial_ok, replay_eq, if_neg small] at accepted
          cases accepted
  · simp only [checkCompression, if_neg initial_ok] at accepted
    cases accepted

/-- Any predicate already satisfied on the initial support remains satisfied on
an accepted result. The predicate itself need not be decidable or linear. -/
theorem checkCompression_preserves_support_predicate {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result : Fin n → ℚ)
    (steps : List (EliminationStep n)) (allowed : Fin n → Prop)
    (initial_allowed : ∀ i, weight i ≠ 0 → allowed i)
    (accepted : checkCompression feature weight steps = some result) :
    ∀ i, result i ≠ 0 → allowed i := by
  have subset := (checkCompression_sound feature weight result steps accepted).2.2.2.1
  intro i hi
  have member := subset (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  exact initial_allowed i (Finset.mem_filter.mp member).2

/-- Closed exact replay: the uniform law on 0,1,2 compresses to its middle point
while preserving the mean. This is a kernel-reducible example without native_decide. -/
theorem mean_preserving_replay_example :
    (checkCompression (n := 3) (d := 1) (fun i _ => (i.val : ℚ))
      (fun _ => 1 / 3)
      [{ direction := fun i => if i = 1 then -2 else 1, pivot := 0 }]).map
        (fun weight => weight 1) = some 1 := by
  decide

/-- The same null direction would revive a zero atom in the law (1/2,0,1/2),
so it is rejected even though it preserves the mean and yields nonnegative weights. -/
theorem rejects_zero_atom_reactivation :
    checkStep (n := 3) (d := 1) (fun i _ => (i.val : ℚ))
      (fun i => if i = 1 then 0 else 1 / 2)
      { direction := fun i => if i = 1 then -2 else 1, pivot := 0 } = false := by
  decide

#print axioms replaySteps_sound
#print axioms checkCompression_sound
#print axioms checkCompression_preserves_support_predicate
#print axioms mean_preserving_replay_example

end D5.S0.Certificates.RationalMomentReplay
