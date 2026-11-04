/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Arbitrary INITIAL tail thresholds force the literal root first-zero position. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels

/-! Literal root necessity for arbitrary immutable INITIAL tail thresholds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse TwoAdjacentLowTailLabels
open OriginalAcquiredTrace

/-- The threshold and band are evaluated on the INITIAL record. The band map
may repeat labels, and its image may contain the outside label. -/
def initialLabel {Y : Type u} (k a : ℕ) (labels : ZMod (k + 1) → Y)
    (outside rejected bottom : Y) : Option (LiveRecord k) → Y
  | none => bottom
  | some q => if k - a ≤ q.tail then rejected
      else if 0 < (-q.phase).val ∧ (-q.phase).val < a then labels (-q.phase)
      else outside

private theorem wrong_root_merge (k m a : ℕ) (ha : 0 < a) (ham : a < m)
    (short : m < k) (B : Fin m → Bool)
    (noCut : ¬ ∃ rest, List.ofFn B = List.replicate a true ++ false :: rest)
    (v : ZMod 2) (phase : ZMod (k + 1)) :
    runBits k B (some ⟨v, phase, k - a - 1⟩) =
      runBits k B (some ⟨v, phase, k - a⟩) := by
  have hk : 2 ≤ k := by omega
  rcases first_zero_form (List.ofFn B) with all | ⟨b, rest, cut⟩
  · have eq : B = allOneBlock m := by
      apply List.ofFn_injective
      change List.ofFn B = List.ofFn (fun _ : Fin m => true)
      simpa only [List.length_ofFn, List.ofFn_const] using all
    rw [eq]
    have ex (s : ℕ) (hs : s < k) :=
      (all_one_archive_exact k m hk (by omega) 1 v phase s hs (fun _ => 0)).2.2
    change allOneOrbit k m 1 (some ⟨v, phase, k - a - 1⟩) =
      allOneOrbit k m 1 (some ⟨v, phase, k - a⟩)
    rw [ex _ (by omega), ex _ (by omega)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · have different : b ≠ a := by intro eq; subst b; exact noCut ⟨rest, cut⟩
    rw [first_zero_block_exact k hk m b B rest cut (short_legal k m hk short B)
      v phase (k - a - 1) (by omega),
      first_zero_block_exact k hk m b B rest cut (short_legal k m hk short B)
      v phase (k - a) (by omega)]
    by_cases before : b < a
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Every eventually terminating selector correct on all actual histories in either free-value fibre
must issue a root beginning with exactly `a` ones and then zero. Its complete
root rejects precisely the high INITIAL tails; every low INITIAL tail clears
to a common current tail. Only the necessary outside/rejection inequality is
used for this root clause; no band injectivity or logarithmic guard is needed. -/
theorem forced_threshold_root {Y : Type u} (Q m a : ℕ) (hQ : 2 ≤ Q)
    (ha : 3 ≤ a) (ham : a < m) (alphabet : Bool)
    (labels : ZMod (Q * m + 1) → Y) (outside rejected bottom : Y)
    (different : outside ≠ rejected) (v : ZMod 2)
    (π : NarrowWindowCost.Selector m Y)
    (correct : ∀ history : List (AllowedBlock (Q * m) m alphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      NarrowWindowCost.output (Q * m) (by nlinarith) w = some v →
      ∃ budget c, NarrowWindowCost.execute (Q * m) (by nlinarith) π budget w (some v) [] =
        some (initialLabel (Q * m) a labels outside rejected bottom
          (OriginalRecord (Q * m) (by nlinarith) w), c)) :
    ∃ B rest, π (some v) [] = .inr B ∧
      List.ofFn B = List.replicate a true ++ false :: rest ∧
      ∀ phase s, s < Q * m →
        runBits (Q * m) B (some ⟨v, phase, s⟩) =
          if s < Q * m - a then
            some ⟨v + wordIncrement (Q * m) phase B,
              phase + (m : ℕ), tailAfter 0 B⟩ else none := by
  have short : m < Q * m := by nlinarith
  have hk : 2 ≤ Q * m := by omega
  have native (s : ℕ) (hs : s < Q * m) : ∃ budget c,
      NativeExecute (k := Q * m) π budget (some ⟨v, 0, s⟩) (some v) [] =
        some (initialLabel (Q * m) a labels outside rejected bottom
          (some ⟨v, 0, s⟩), c) := by
    obtain ⟨history, actual⟩ :=
      ((whole_first_zero_acquisition (Q * m) m hk (by omega) alphabet (fun _ => ())).1
        (some ⟨v, 0, s⟩)).mp ⟨hs, dvd_zero _⟩
    have record : OriginalRecord (Q * m) (by omega)
        (history.flatMap (fun action => List.ofFn action.val)) = some ⟨v, 0, s⟩ :=
      (OriginalExecutionBridge.record_history (Q * m) m hk alphabet history).trans actual
    have observed : NarrowWindowCost.output (Q * m) (by omega)
        (history.flatMap (fun action => List.ofFn action.val)) = some v := by
      rw [OriginalExecutionBridge.output_record]
      change endpointReading (OriginalRecord (Q * m) (by omega) _) = some v
      rw [record]
      rfl
    obtain ⟨budget, c, success⟩ := correct history observed
    rw [OriginalExecutionBridge.execute_same (Q * m) m hk] at success
    change NativeExecute π budget (OriginalRecord (Q * m) (by omega) _)
      (some v) [] = some (initialLabel (Q * m) a labels outside rejected bottom
        (OriginalRecord (Q * m) (by omega) _), c) at success
    rw [record] at success
    exact ⟨budget, c, success⟩
  obtain ⟨lowBudget, c, low⟩ := native (Q * m - a - 1) (by omega)
  obtain ⟨highBudget, e, high⟩ := native (Q * m - a) (by omega)
  let d := max lowBudget highBudget
  have enlarge (budget c : ℕ) (q : Option (LiveRecord (Q * m))) (y : Y)
      (success : NativeExecute π budget q (some v) [] = some (y, c))
      (bound : budget ≤ d) : NativeExecute π d q (some v) [] = some (y, c) := by
    obtain ⟨issued, trace, count, bounded⟩ :=
      (native_execute_paid_trace (Q * m) m π budget q (some v) [] y c).mp success
    exact (native_execute_paid_trace (Q * m) m π d q (some v) [] y c).mpr
      ⟨issued, trace, count, bounded.trans bound⟩
  have low := enlarge lowBudget c _ _ low (le_max_left _ _)
  have high := enlarge highBudget e _ _ high (le_max_right _ _)
  have lowLabel : initialLabel (Q * m) a labels outside rejected bottom
      (some ⟨v, 0, Q * m - a - 1⟩) = outside := by
    simp [initialLabel, show ¬ Q * m - a ≤ Q * m - a - 1 by omega]
  have highLabel : initialLabel (Q * m) a labels outside rejected bottom
      (some ⟨v, 0, Q * m - a⟩) = rejected := by simp [initialLabel]
  rw [lowLabel] at low
  rw [highLabel] at high
  cases d with
  | zero =>
    have same : NativeExecute (k := Q * m) π 0
        (some ⟨v, 0, Q * m - a - 1⟩) (some v) [] =
        NativeExecute (k := Q * m) π 0
        (some ⟨v, 0, Q * m - a⟩) (some v) [] := rfl
    rw [low, high] at same
    exact False.elim (different (congrArg Prod.fst (Option.some.inj same)))
  | succ b =>
    cases chosen : π (some v) [] with
    | inl y =>
      simp only [NativeExecute, chosen, Option.some.injEq, Prod.mk.injEq] at low high
      exact False.elim (different (low.1.symm.trans high.1))
    | inr B =>
      have cut : ∃ rest, List.ofFn B = List.replicate a true ++ false :: rest := by
        by_contra noCut
        have merge := wrong_root_merge (Q * m) m a (by omega) ham short B noCut v 0
        have same : NativeExecute (k := Q * m) π (b + 1)
            (some ⟨v, 0, Q * m - a - 1⟩) (some v) [] =
            NativeExecute (k := Q * m) π (b + 1)
            (some ⟨v, 0, Q * m - a⟩) (some v) [] := by
          simp only [NativeExecute, chosen, merge]
        rw [low, high] at same
        exact different (congrArg Prod.fst (Option.some.inj same))
      obtain ⟨rest, cut⟩ := cut
      refine ⟨B, rest, rfl, cut, ?_⟩
      intro phase s hs
      rw [first_zero_block_exact (Q * m) hk m a B rest cut
        (short_legal (Q * m) m hk short B) v phase s hs]
      have safe : s + a < Q * m ↔ s < Q * m - a := by omega
      simp only [safe]

#print axioms forced_threshold_root

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix
