/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InitialTailCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InitialTailCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exact initial tail budgets on all actual complete block histories. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstZeroRecursion
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition

private theorem single_execution (k : ℕ) (word : Fin 1 → Bool)
    (q : Option (LiveRecord k)) : runBits k word q = bitUpdate k (word 0) q := by
  simp [runBits, List.ofFn_succ, runWord]

/-- Before the first possible rejection, a zero merges adjacent tails and a
one advances both with the same endpoint reply. The tree may adapt arbitrarily. -/
private theorem adjacent_single {k : ℕ} {alphabet : Bool} {Y : Type*} {n : ℕ}
    (tree : AcquisitionTree k 1 alphabet Y n)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (bound : s + n + 1 < k) :
    tree.result (some ⟨v, phase, s⟩) = tree.result (some ⟨v, phase, s + 1⟩) := by
  induction tree generalizing v phase s with
  | stop label => rfl
  | @step n action next ih =>
      simp only [AcquisitionTree.result, single_execution]
      cases bit : action.val 0
      · simp [bitUpdate]
      · have safe₀ : s + 1 < k := by omega
        have safe₁ : s + 1 + 1 < k := by omega
        simp only [bitUpdate, if_pos safe₀, if_pos safe₁, endpointReading]
        exact ih (some (v + coefficient k phase)) (v + coefficient k phase) (phase + 1)
          (s + 1) (by omega)

private def single_one (k : ℕ) (hk : 2 ≤ k) (alphabet : Bool) :
    AllowedBlock k 1 alphabet :=
  ⟨fun _ => true, fun _ => by
    cases k with
    | zero => omega
    | succ r =>
        exact runAdmissible_eq_true_of_length_le r r 1 (fun _ => true) (by omega) le_rfl⟩

/-- The rejection label uses the number of ones already issued, never the
changed terminal tail. A surviving last branch labels initial tail zero. -/
private def single_tree (k : ℕ) (hk : 2 ≤ k) (alphabet : Bool) :
    (n r : ℕ) → AcquisitionTree k 1 alphabet (Option ℕ) n
  | 0, _ => .stop (some 0)
  | n + 1, r => .step (single_one k hk alphabet) (fun reply =>
      match reply with
      | none => .stop (some (k - (r + 1)))
      | some _ => single_tree k hk alphabet n (r + 1))

private theorem single_tree_result (k : ℕ) (hk : 2 ≤ k) (alphabet : Bool)
    (n r : ℕ) (balance : r + n = k - 1)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (live : s + r < k) :
    (single_tree k hk alphabet n r).result (some ⟨v, phase, s + r⟩) = some s := by
  induction n generalizing r v phase with
  | zero =>
      have zero : s = 0 := by omega
      simp [single_tree, AcquisitionTree.result, zero]
  | succ n ih =>
      simp only [single_tree, AcquisitionTree.result, single_execution, single_one]
      by_cases safe : s + r + 1 < k
      · simp only [bitUpdate, if_pos safe, endpointReading]
        exact ih (r + 1) (by omega) (v + coefficient k phase) (phase + 1) (by omega)
      · have label : k - (r + 1) = s := by omega
        simp [bitUpdate, safe, endpointReading, AcquisitionTree.result, label]

private theorem tree_mono {k m : ℕ} {alphabet : Bool} {Y : Type*} {n : ℕ}
    (tree : AcquisitionTree k m alphabet Y n) (d : ℕ) (bound : n ≤ d) :
    ∃ bigger : AcquisitionTree k m alphabet Y d, ∀ q, bigger.result q = tree.result q := by
  classical
  induction tree generalizing d with
  | stop label => exact ⟨.stop label, fun _ => rfl⟩
  | @step n action next ih =>
      cases d with
      | zero => omega
      | succ d =>
          choose larger equal using fun reply => ih reply d (by omega)
          exact ⟨.step action larger, fun q => equal (endpointReading (runBits k action.val q)) _⟩

private theorem single_upper (k : ℕ) (hk : 2 ≤ k) (alphabet : Bool) :
    RecordAcquiredAt (k := k) (m := 1) alphabet (fun q => q.map LiveRecord.tail) (k - 1) := by
  refine ⟨fun reply => match reply with
    | none => .stop none
    | some _ => single_tree k hk alphabet (k - 1) 0, ?_⟩
  intro q valid
  cases q with
  | none => rfl
  | some q =>
      simpa only [endpointReading, Nat.add_zero, Option.map_some] using
        single_tree_result k hk alphabet (k - 1) 0 (by omega)
          q.value q.phase q.tail (by simpa using valid.1)

private theorem two_upper (m : ℕ) (hm : 1 ≤ m) (alphabet : Bool) :
    RecordAcquiredAt (k := 2) (m := m) alphabet (fun q => q.map LiveRecord.tail) 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let word : Fin (r + 1) → Bool := Fin.cons true (fun _ => false)
  have legal : DBonacciAdmissible 2 (r + 1) word := by
    simpa only [DBonacciAdmissible, runAdmissible, word, Fin.cons_zero,
      Fin.tail_cons, ↓reduceIte] using
      D5.S0.Tower.DBonacci.Values.runAdmissible_all_false 1 0 r
  let action : AllowedBlock 2 (r + 1) alphabet := ⟨word, fun _ => legal⟩
  let liveTree : AcquisitionTree 2 (r + 1) alphabet (Option ℕ) 1 :=
    .step action (fun reply => match reply with
      | none => .stop (some 1)
      | some _ => .stop (some 0))
  refine ⟨fun reply => match reply with
    | none => .stop none
    | some _ => liveTree, ?_⟩
  intro q valid
  cases q with
  | none => rfl
  | some q =>
      have hs : q.tail < 2 := valid.1
      have execution := (literal_block_execution 2 (by omega) (r + 1) word
        q.value q.phase q.tail hs).1
      change runBits 2 word (some q) = if runAdmissible 1 (1 - q.tail) (r + 1) word = true then
          some ⟨q.value + wordIncrement 2 q.phase word,
            q.phase + (r + 1 : ℕ), tailAfter q.tail word⟩ else none at execution
      have casesTail : q.tail = 0 ∨ q.tail = 1 := by omega
      rcases casesTail with zero | one
      · have scanner : runAdmissible 1 (1 - q.tail) (r + 1) word = true := by
          simpa only [zero, Nat.sub_zero, runAdmissible, word, Fin.cons_zero,
            Fin.tail_cons, ↓reduceIte] using
            D5.S0.Tower.DBonacci.Values.runAdmissible_all_false 1 0 r
        rw [scanner, if_pos rfl] at execution
        simp only [endpointReading]
        change liveTree.result (some q) = some q.tail
        simp [liveTree, AcquisitionTree.result, action, execution, endpointReading, zero]
      · have scanner : runAdmissible 1 (1 - q.tail) (r + 1) word = false := by
          simp [one, runAdmissible, word]
        rw [scanner, if_neg (by decide)] at execution
        simp only [endpointReading]
        change liveTree.result (some q) = some q.tail
        simp [liveTree, AcquisitionTree.result, action, execution, endpointReading, one]

private theorem wide_impossible (k m : ℕ) (hk : 3 ≤ k) (hm : 2 ≤ m)
    (alphabet : Bool) :
    ¬ RecordAcquired (k := k) (m := m) alphabet (fun q => q.map LiveRecord.tail) := by
  classical
  intro acquired
  let target : {q : Option (LiveRecord k) // SourceRecord k m q} → Option ℕ :=
    fun q => q.val.map LiveRecord.tail
  let f := actualSourceTarget target
  have agree : ∀ q, SourceRecord k m q → f q = q.map LiveRecord.tail := by
    intro q valid
    simp only [f, actualSourceTarget, dif_pos valid, target]
  have acquired' : RecordAcquired (k := k) (m := m) alphabet f := by
    obtain ⟨n, controller, correct⟩ := acquired
    exact ⟨n, controller, fun q valid => (correct q valid).trans (agree q valid).symm⟩
  have criterion := ((whole_first_zero_acquisition k m (by omega) (by omega) alphabet
    target).2.1.mp acquired').1
  have member : (0 : ZMod (k + 1)) ∈ {phase | Nat.gcd m (k + 1) ∣ phase.val} := by simp
  have label : ∀ s, s<k → actualSourceTarget target (some ⟨0, 0, s⟩) = some s := by
    intro s hs
    exact agree _ ⟨hs, member⟩
  rw [FirstZeroCriterion] at criterion
  rcases criterion with empty | ⟨a, am, ak, rejection, survivors⟩ | recurse
  · simp [empty] at member
  · by_cases two : 2 ≤ a
    · have equal := rejection 0 member 0 member (k - 2) (by omega)
        (k - 1) (by omega) (by omega) (by omega)
      rw [label _ (by omega), label _ (by omega)] at equal
      have tails := Option.some.inj equal
      omega
    · have equal := survivors 0 member 0 (by omega) 1 (by omega)
      rw [label _ (by omega), label _ (by omega)] at equal
      cases equal
  · by_cases short : m<k
    · rw [dif_pos short] at recurse
      have equal := recurse.1 0 member 0 member (k - 2) (by omega)
        (k - 1) (by omega) (by omega) (by omega)
      rw [label _ (by omega), label _ (by omega)] at equal
      have tails := Option.some.inj equal
      omega
    · simp only [dif_neg short] at recurse

private theorem record_budget_exact (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (alphabet : Bool) (n : ℕ) :
    RecordAcquiredAt (k := k) (m := m) alphabet (fun q => q.map LiveRecord.tail) n ↔
      (m = 1 ∧ k - 1 ≤ n) ∨ (k = 2 ∧ 1 ≤ n) := by
  classical
  constructor
  · intro acquired
    have source (s : ℕ) (hs : s<k) : SourceRecord k m (some ⟨0, 0, s⟩) :=
      ⟨hs, by simp⟩
    obtain ⟨controller, correct⟩ := acquired
    have zero := correct (some ⟨0, 0, 0⟩) (source 0 (by omega))
    have one := correct (some ⟨0, 0, 1⟩) (source 1 (by omega))
    have positive : 1 ≤ n := by
      by_contra no
      have equal : n = 0 := by omega
      subst n
      have same : (controller (some 0)).result (some ⟨0, 0, 0⟩) = (controller (some 0)).result (some ⟨0, 0, 1⟩) := by
        cases controller (some 0) with
        | stop label => rfl
      simp only [endpointReading, Option.map_some] at zero one
      rw [zero, one] at same
      cases same
    by_cases width : m = 1
    · subst m
      apply Or.inl
      refine ⟨rfl, ?_⟩
      by_contra no
      have same := adjacent_single (controller (some 0)) 0 0 0 (by omega : 0 + n + 1<k)
      simp only [endpointReading, Option.map_some] at zero one
      rw [zero, one] at same
      cases same
    · apply Or.inr
      refine ⟨?_, positive⟩
      by_contra notTwo
      exact wide_impossible k m (by omega) (by omega) alphabet ⟨n, controller, correct⟩
  · rintro (⟨rfl, bound⟩ | ⟨rfl, bound⟩)
    · obtain ⟨small, correct⟩ := single_upper k hk alphabet
      choose bigger equal using fun reply => tree_mono (small reply) n bound
      exact ⟨bigger, fun q valid => (equal (endpointReading q) q).trans (correct q valid)⟩
    · obtain ⟨small, correct⟩ := two_upper m hm alphabet
      choose bigger equal using fun reply => tree_mono (small reply) n bound
      exact ⟨bigger, fun q valid => (equal (endpointReading q) q).trans (correct q valid)⟩

/-- For every uniform budget, the full initial tail (with a separate initial
rejection label) is identified on every actual history exactly in the stated
parameter and budget ranges. Only the free initial reading selects the tree. -/
theorem initial_tail_budget_exact (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (alphabet : Bool) (n : ℕ) :
    (∃ controller : Option (ZMod 2) → AcquisitionTree k m alphabet (Option ℕ) n,
      ∀ history : List (AllowedBlock k m alphabet),
        (controller (endpointReading (historyRecord history))).result (historyRecord history) = (historyRecord history).map LiveRecord.tail) ↔
      (m = 1 ∧ k - 1 ≤ n) ∨ (k = 2 ∧ 1 ≤ n) := by
  classical
  let target : {q : Option (LiveRecord k) // SourceRecord k m q} → Option ℕ :=
    fun q => q.val.map LiveRecord.tail
  have actual := (whole_first_zero_acquisition k m hk hm alphabet target).1
  rw [← record_budget_exact k m hk hm alphabet n]
  constructor
  · rintro ⟨controller, correct⟩
    refine ⟨controller, ?_⟩
    intro q valid
    obtain ⟨history, rfl⟩ := (actual q).mp valid
    exact correct history
  · rintro ⟨controller, correct⟩
    exact ⟨controller, fun history => correct _ ((actual _).mpr ⟨history, rfl⟩)⟩

#print axioms initial_tail_budget_exact

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InitialTailCost
