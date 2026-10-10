/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Matching fresh acquisition prefixes and unbounded native branch requests. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape

universe u

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
  (Address Reply Strategy leaves frontier acquisitionStep acquisitionPolicy)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open ActualExactTraceCompiler (CoarseHistory encode_projection)
open ActualCompletionPhaseReplay (PhaseLabel routePhase verifyPhase phase_replay_contract)
open ActualFiniteObserverAbsentElimination (RawHistory Observer historyAction historyState)

/-- The literal address on the all-left branch at depth n. -/
def leftAddress (n : Nat) : Address := List.replicate n false

/-- Chronological branch reports at depths zero through n-1, without a source promise. -/
def branchHistory : Nat → RawHistory
  | 0 => []
  | n + 1 => branchHistory n ++ [⟨leftAddress n, Reply.branch⟩]

private theorem branch_frontier (n : Nat) :
    ∃ rest : List Address, frontier (branchHistory n) = leftAddress n :: rest := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      obtain ⟨rest, head⟩ := ih
      refine ⟨(leftAddress n ++ [true]) :: rest, ?_⟩
      simp only [branchHistory, ActualTreeReadoutAcquisition.frontier,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      change acquisitionStep (frontier (branchHistory n)) _ = _
      rw [head]
      simp only [acquisitionStep, ↓reduceIte]
      congr 1
      simp [leftAddress, List.replicate_succ']

private theorem branch_normalized (n : Nat) :
    encodeHistory (kappa_hist (branchHistory n)) = branchHistory n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [branchHistory, kappa_hist, encodeHistory, List.map_append,
        List.map_cons, List.map_nil, kappa] using
        congrArg (fun h : RawHistory => h ++ [⟨leftAddress n, Reply.branch⟩]) ih

private theorem route_matches {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (seen : CoarseHistory) (U : Source) :
    let r := encodeHistory (runPassiveProtocol (fun q W => leafLabel W q) p U)
    ∀ k : Fin r.length, controllerPolicy (compileRaw F decode p seen) (r.take k.val) =
      Sum.inl ((r.get k).1) := by
  dsimp only
  induction p generalizing seen with
  | stop => intro k; exact Fin.elim0 k
  | query q next ih =>
      intro k
      rcases k with ⟨k, bound⟩
      cases k with
      | zero => rfl
      | succ k =>
          have smaller : k < (encodeHistory
              (runPassiveProtocol (fun q W => leafLabel W q) (next (leafLabel U q)) U)).length := by
            simpa only [runPassiveProtocol, encodeHistory, List.map_cons, List.length_cons,
              Nat.succ_lt_succ_iff] using bound
          have step := ih (leafLabel U q) (seen ++ [⟨q, leafLabel U q⟩]) ⟨k, smaller⟩
          cases label : leafLabel U q with
          | none => simpa [runPassiveProtocol, encodeHistory, compileRaw, controllerPolicy,
              kappa, label] using step
          | some b => cases b <;> simpa [runPassiveProtocol, encodeHistory, compileRaw,
              controllerPolicy, kappa, label] using step

/-- Query length is zero at either halt action. It measures every nominal query row. -/
def queryAddressLength : Sum Address Bool → Nat
  | .inl q => q.length
  | .inr _ => 0

/-- One matching raw prefix resets acquisition on every suffix. Its branch ladder
requests arbitrary literal depths and defeats each finite original Observer on that same ladder. -/
theorem counterfactual_escape {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (π : Strategy)
    (policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))) :
    ∃ pre : RawHistory,
      (∀ k : Fin pre.length, π.policy (pre.take k.val) = Sum.inl ((pre.get k).1)) ∧
      (∀ s : RawHistory, routePhase F decode p [] (kappa_hist (pre ++ s)) =
        (PhaseLabel.acquisition (kappa_hist s), acquisitionPolicy (encodeHistory (kappa_hist s)))) ∧
      (∀ n : Nat, π.policy (pre ++ branchHistory n) = Sum.inl (leftAddress n)) ∧
      (∀ (E : Type u) [Fintype E] (M : Observer E), ∃ n : Nat,
        historyAction M (pre ++ branchHistory n) ≠ π.policy (pre ++ branchHistory n)) := by
  classical
  have phases := phase_replay_contract F decode p 1 π le_rfl policy
  let g := runPassiveProtocol (fun q W => leafLabel W q) p ((FreeMagma.of false : Source))
  let r : RawHistory := encodeHistory g
  have projection : kappa_hist r = g := encode_projection g
  have matchingRoute (k : Fin r.length) : π.policy (r.take k.val) = Sum.inl ((r.get k).1) := by
    simp only [policy]
    have norm : encodeHistory (kappa_hist (r.take k.val)) = r.take k.val := by
      rw [kappa_hist, List.map_take]
      change encodeHistory ((kappa_hist r).take k.val) = _
      rw [projection]
      simp only [r, encodeHistory, List.map_take]
    rw [norm]
    exact route_matches F decode p [] (.of false) k
  have reset (s : RawHistory) : routePhase F decode p [] (kappa_hist (r ++ s)) =
      routePhase F decode .stop g (kappa_hist s) := by
    simp only [kappa_hist, List.map_append]
    change routePhase F decode p [] (kappa_hist r ++ kappa_hist s) = _
    rw [projection]
    exact phases.2.1 (.of false) (kappa_hist s)
  have fresh : ∃ pre : RawHistory,
      (∀ k : Fin pre.length, π.policy (pre.take k.val) = Sum.inl ((pre.get k).1)) ∧
      ∀ s : RawHistory, routePhase F decode p [] (kappa_hist (pre ++ s)) =
        (PhaseLabel.acquisition (kappa_hist s),
          acquisitionPolicy (encodeHistory (kappa_hist s))) := by
    cases chosen : decode g with
    | none =>
        refine ⟨r, matchingRoute, ?_⟩
        intro s
        rw [reset]
        simp only [routePhase, chosen]
        rfl
    | some i =>
        have nonempty : (leaves (F i)).toFinset.Nonempty := by
          apply Finset.card_pos.mp
          change 0 < (leafAddresses (F i)).card
          rw [(seven_leaf_separation.1 (F i)).1]
          exact FreeMagma.length_pos (F i)
        have notNil : leaves (F i) ≠ [] := by
          intro empty
          simp only [empty, List.toFinset_nil, Finset.not_nonempty_empty] at nonempty
        cases split : leaves (F i) with
        | nil => exact (notNil split).elim
        | cons q rest =>
            have member : q ∈ leafAddresses (F i) := by
              exact List.mem_toFinset.mpr (by rw [split]; exact List.mem_cons_self)
            obtain ⟨b, label⟩ := ((seven_leaf_separation.1 (F i)).2 q).mp member
            have mismatch : kappa Reply.branch ≠ leafLabel (F i) q := by simp [kappa, label]
            refine ⟨r ++ [⟨q, Reply.branch⟩], ?_, ?_⟩
            · intro k
              by_cases early : k.val < r.length
              · have taken : (r ++ [(⟨q, Reply.branch⟩ :
                    Sigma (fun _ : Address => Reply))]).take k.val = r.take k.val := by
                  exact List.take_append_of_le_length (Nat.le_of_lt early)
                rw [taken]
                simpa [List.get_eq_getElem, List.getElem_append_left early] using
                  matchingRoute ⟨k.val, early⟩
              · have last : k.val = r.length := by
                  have bound := k.isLt
                  simp only [List.length_append, List.length_singleton] at bound
                  omega
                have action : π.policy r = Sum.inl q := by
                  simp only [policy]
                  rw [← phases.1 (kappa_hist r)]
                  have atEnd : routePhase F decode p [] (kappa_hist r) =
                      routePhase F decode .stop g [] := by
                    simpa only [List.append_nil, kappa_hist, List.map_nil] using reset []
                  rw [atEnd]
                  simp [routePhase, chosen, verifyPhase, split]
                simpa [last, List.take_append, List.get_eq_getElem] using action
            · intro s
              rw [List.append_assoc, reset]
              simp only [routePhase, chosen]
              have failure := phases.2.2.1 i [] rest q Reply.branch (kappa_hist s)
                (by simpa using split) mismatch
              simpa [kappa_hist] using failure
  obtain ⟨pre, matching, fresh⟩ := fresh
  have ladder (n : Nat) : π.policy (pre ++ branchHistory n) = Sum.inl (leftAddress n) := by
    simp only [policy]
    rw [← phases.1 (kappa_hist (pre ++ branchHistory n)), fresh]
    obtain ⟨rest, head⟩ := branch_frontier n
    rw [branch_normalized]
    simp only [acquisitionPolicy, head]
  refine ⟨pre, matching, fresh, ladder, ?_⟩
  intro E _ M
  let B := Finset.univ.sup (fun e : E => queryAddressLength (M.action e))
  refine ⟨B + 1, ?_⟩
  intro equal
  have bound : queryAddressLength (historyAction M (pre ++ branchHistory (B + 1))) ≤ B :=
    Finset.le_sup (f := fun e : E => queryAddressLength (M.action e)) (Finset.mem_univ _)
  rw [equal, ladder] at bound
  simp only [queryAddressLength, leftAddress, List.length_replicate] at bound
  omega

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionCounterfactualEscape
