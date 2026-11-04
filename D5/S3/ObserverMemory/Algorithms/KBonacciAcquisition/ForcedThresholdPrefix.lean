/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Arbitrary blind bands share one actual adaptive zero archive through the first tour. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels

/-! Forced roots and coherent actual first-tour archives for immutable INITIAL labels. -/

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
  generalize horizon : d = budget at low high
  cases budget with
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


/-- The common reading branch is generated by the actual adaptive selector. -/
def zeroArchive {Y : Type u} {m : ℕ} (π : NarrowWindowCost.Selector m Y)
    (v : ZMod 2) : ℕ → NarrowWindowCost.Archive m
  | 0 => []
  | t + 1 => let ar := zeroArchive π v t
      let B := match π (some v) ar with
        | .inl _ => fun _ => false
        | .inr B => B
      ar ++ [(B, some v)]

/-- Only the word chosen on this same acquired branch is used. -/
def zeroWord {Y : Type u} {m : ℕ} (π : NarrowWindowCost.Selector m Y)
    (v : ZMod 2) (t : ℕ) : Fin m → Bool :=
  match π (some v) (zeroArchive π v t) with
  | .inl _ => fun _ => false
  | .inr B => B

private theorem eventual_unique {Y : Type u} (k m : ℕ)
    (π : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (free : Option (ZMod 2)) (ar : NarrowWindowCost.Archive m) (x y : Y)
    (hx : ∃ d c, NativeExecute π d q free ar = some (x, c))
    (hy : ∃ d c, NativeExecute π d q free ar = some (y, c)) : x = y := by
  obtain ⟨d, c, ex⟩ := hx
  obtain ⟨e, f, ey⟩ := hy
  have extend (b fee : ℕ) (label : Y)
      (success : NativeExecute π b q free ar = some (label, fee))
      (bound : b ≤ max d e) : NativeExecute π (max d e) q free ar = some (label, fee) := by
    obtain ⟨issued, trace, count, bounded⟩ :=
      (native_execute_paid_trace k m π b q free ar label fee).mp success
    exact (native_execute_paid_trace k m π (max d e) q free ar label fee).mpr
      ⟨issued, trace, count, bounded.trans bound⟩
  have same := (extend d c x ex (le_max_left _ _)).symm.trans
    (extend e f y ey (le_max_right _ _))
  exact congrArg Prod.fst (Option.some.inj same)

private theorem eventual_step {Y : Type u} (k m : ℕ)
    (π : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (free : Option (ZMod 2)) (ar : NarrowWindowCost.Archive m) (y : Y)
    (B : Fin m → Bool) (chosen : π free ar = .inr B)
    (success : ∃ d c, NativeExecute π d q free ar = some (y, c)) :
    ∃ d c, NativeExecute π d (runBits k B q) free
      (ar ++ [(B, endpointReading (runBits k B q))]) = some (y, c) := by
  obtain ⟨d, c, ex⟩ := success
  cases d with
  | zero => simp [NativeExecute, chosen] at ex
  | succ d =>
    simp only [NativeExecute, chosen] at ex
    obtain ⟨r, er, eq⟩ := Option.map_eq_some_iff.mp ex
    refine ⟨d, r.2, ?_⟩
    change NativeExecute π d (runBits k B q) free
      (ar ++ [(B, endpointReading (runBits k B q))]) = some r at er
    exact er.trans (congrArg some (Prod.ext (Prod.mk.inj eq).1 rfl))

private theorem root_band_response (Q m a : ℕ) (hQ : 2 ≤ Q) (ha : 3 ≤ a)
    (ham : a < m) (B : Fin m → Bool) (rest : List Bool)
    (cut : List.ofFn B = List.replicate a true ++ false :: rest)
    (j : ZMod (Q * m + 1)) (positive : 0 < j.val) (band : j.val < a) :
    wordIncrement (Q * m) (-j) B = 0 := by
  have bit (i : ℕ) (hi : i < a) : extendedBit B i = 1 := by
    have im : i < m := by omega
    have e := congrArg (fun w : List Bool => w[i]?) cut
    simp only [List.getElem?_ofFn, dite_eq_left im] at e
    have right : (List.replicate a true ++ false :: rest)[i]? = some true := by
      rw [List.getElem?_append_left (by simp; omega)]
      simp [hi]
    rw [right] at e
    have value : B ⟨i, im⟩ = true := Option.some.inj e
    simp [extendedBit, im, bitScalar, value]
  rw [increment_derivative (Q * m) (by nlinarith) m (by nlinarith)]
  rw [bit j.val band, ite_eq_right (by omega), bit (j.val - 1) (by omega)]
  exact CharTwo.add_self_eq_zero _

/-- Every correct actual-history controller has one coherent first-tour zero
branch. All low INITIAL tails whose literal responses are zero follow that
same branch, including outside phases; the surviving current tail is chosen
by the controller and is not asserted to be zero. -/
theorem first_tour_common_archive {Y : Type u} (Q m a : ℕ) (hQ : 2 ≤ Q)
    (ha : 3 ≤ a) (ham : a < m) (alphabet : Bool)
    (labels : ZMod (Q * m + 1) → Y) (outside rejected bottom : Y)
    (different : outside ≠ rejected)
    (nonconstant : ∃ p q : ZMod (Q * m + 1),
      (0 < p.val ∧ p.val < a) ∧ (0 < q.val ∧ q.val < a) ∧ labels p ≠ labels q)
    (v : ZMod 2) (π : NarrowWindowCost.Selector m Y)
    (correct : ∀ history : List (AllowedBlock (Q * m) m alphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      NarrowWindowCost.output (Q * m) (by nlinarith) w = some v →
      ∃ budget c, NarrowWindowCost.execute (Q * m) (by nlinarith) π budget w (some v) [] =
        some (initialLabel (Q * m) a labels outside rejected bottom
          (OriginalRecord (Q * m) (by nlinarith) w), c)) :
    (∀ t, t < Q → π (some v) (zeroArchive π v t) = .inr (zeroWord π v t)) ∧
    (∀ t j, t < Q → 0 < j.val → j.val < a →
      wordIncrement (Q * m) (-j + ((t * m : ℕ) : ZMod (Q * m + 1))) (zeroWord π v t) = 0) ∧
    ∀ t, 1 ≤ t → t ≤ Q → ∃ tail, tail < Q * m ∧
      ∀ (j : ZMod (Q * m + 1)) (s : ℕ), s < Q * m - a →
        (∀ i, i < t → wordIncrement (Q * m)
          (-j + ((i * m : ℕ) : ZMod (Q * m + 1))) (zeroWord π v i) = 0) →
        (∃ budget c, NativeExecute π budget
          (some ⟨v, -j + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩)
          (some v) (zeroArchive π v t) =
          some (initialLabel (Q * m) a labels outside rejected bottom (some ⟨v, -j, s⟩), c)) ∧
        ∀ history : List (AllowedBlock (Q * m) m alphabet),
          let w := history.flatMap (fun action => List.ofFn action.val)
          OriginalRecord (Q * m) (by nlinarith) w = some ⟨v, -j, s⟩ →
          ActualArchive (Q * m) (by nlinarith) w (zeroArchive π v t) ∧
          OriginalRecord (Q * m) (by nlinarith) (w ++ archiveWords (zeroArchive π v t)) =
            some ⟨v, -j + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩ := by
  have hk : 2 ≤ Q * m := by nlinarith
  have short : m < Q * m := by nlinarith
  have lowPositive : 0 < Q * m - a := Nat.sub_pos_of_lt (ham.trans short)
  have native (j : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m) :
      ∃ budget c, NativeExecute π budget (some ⟨v, -j, s⟩) (some v) [] =
        some (initialLabel (Q * m) a labels outside rejected bottom (some ⟨v, -j, s⟩), c) := by
    have gcdOne : Nat.gcd m (Q * m + 1) = 1 := by
      have divides : Nat.gcd m (Q * m + 1) ∣ 1 := by
        have h := Nat.dvd_sub (Nat.gcd_dvd_right m (Q * m + 1))
          (dvd_mul_of_dvd_right (Nat.gcd_dvd_left m (Q * m + 1)) Q)
        simp_all
      exact Nat.dvd_one.mp divides
    obtain ⟨history, actual⟩ :=
      ((whole_first_zero_acquisition (Q * m) m hk (by omega) alphabet (fun _ => ())).1
        (some ⟨v, -j, s⟩)).mp ⟨hs, by rw [gcdOne]; exact one_dvd _⟩
    have record : OriginalRecord (Q * m) (by omega)
        (history.flatMap (fun action => List.ofFn action.val)) = some ⟨v, -j, s⟩ :=
      (OriginalExecutionBridge.record_history (Q * m) m hk alphabet history).trans actual
    have free : NarrowWindowCost.output (Q * m) (by omega)
        (history.flatMap (fun action => List.ofFn action.val)) = some v := by
      calc
        _ = endpointReading (OriginalRecord (Q * m) (by omega) _) :=
          OriginalExecutionBridge.output_record (Q * m) (by omega) _
        _ = _ := congrArg endpointReading record
    obtain ⟨budget, c, ex⟩ := correct history free
    rw [OriginalExecutionBridge.execute_same (Q * m) m hk] at ex
    change NativeExecute π budget (OriginalRecord (Q * m) (by omega) _) (some v) [] =
      some (initialLabel (Q * m) a labels outside rejected bottom
        (OriginalRecord (Q * m) (by omega) _), c) at ex
    rw [record] at ex
    exact ⟨budget, c, ex⟩
  obtain ⟨B, rest, chosen, cut, rootExec⟩ :=
    forced_threshold_root Q m a hQ ha ham alphabet labels outside rejected bottom different v π correct
  have rootWord : zeroWord π v 0 = B := by simp [zeroWord, zeroArchive, chosen]
  have rootAr : zeroArchive π v 1 = [(B, some v)] := by simp [zeroArchive, chosen]
  have bandzero (j : ZMod (Q * m + 1)) (hj : 0 < j.val ∧ j.val < a) (t : ℕ) (ht : t < Q) :
      wordIncrement (Q * m) (-j + ((t * m : ℕ) : ZMod (Q * m + 1))) (zeroWord π v t) = 0 := by
    by_cases first : t = 0
    · subst t
      simpa only [Nat.zero_mul, Nat.cast_zero, add_zero, rootWord] using
        root_band_response Q m a hQ ha ham B rest cut j hj.1 hj.2
    · have lower : m ≤ t * m := by simpa using Nat.mul_le_mul_right m (show 1 ≤ t by omega)
      have jbound : j.val ≤ Q * m := by nlinarith
      have e := response_off Q m t j.val hQ (by omega) ht jbound
        (Or.inl (by omega)) (zeroWord π v t)
      simpa only [ZMod.natCast_zmod_val] using e
  obtain ⟨p, q, hp, hq, distinct⟩ := nonconstant
  have lowLabel (j : ZMod (Q * m + 1)) (hj : 0 < j.val ∧ j.val < a) :
      initialLabel (Q * m) a labels outside rejected bottom (some ⟨v, -j, 0⟩) = labels j := by
    simp [initialLabel, show ¬ Q * m - a ≤ 0 by omega, neg_neg, hj]
  have walk : ∀ t, 1 ≤ t → t ≤ Q → ∃ tail, tail < Q * m ∧
      (∀ i, i < t → π (some v) (zeroArchive π v i) = .inr (zeroWord π v i)) ∧
      ∀ (j : ZMod (Q * m + 1)) (s : ℕ), s < Q * m - a →
        (∀ i, i < t → wordIncrement (Q * m) (-j + ((i * m : ℕ) : ZMod (Q * m + 1))) (zeroWord π v i) = 0) →
        (∃ budget c, NativeExecute π budget (some ⟨v, -j + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩)
          (some v) (zeroArchive π v t) = some (initialLabel (Q * m) a labels outside rejected bottom (some ⟨v, -j, s⟩), c)) ∧
        ∀ history : List (AllowedBlock (Q * m) m alphabet),
          let w := history.flatMap (fun action => List.ofFn action.val)
          OriginalRecord (Q * m) (by omega) w = some ⟨v, -j, s⟩ →
          ActualArchive (Q * m) (by omega) w (zeroArchive π v t) ∧
          OriginalRecord (Q * m) (by omega) (w ++ archiveWords (zeroArchive π v t)) =
            some ⟨v, -j + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩ := by
    intro t
    induction t with
    | zero => intro positive; omega
    | succ t ih =>
      intro positive bounded
      by_cases first : t = 0
      · subst t
        have safe (j : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m - a)
            (zero : ∀ i, i < 1 → wordIncrement (Q * m)
              (-j + ((i * m : ℕ) : ZMod (Q * m + 1))) (zeroWord π v i) = 0) :
            runBits (Q * m) B (some ⟨v, -j, s⟩) = some ⟨v, -j + (m:ℕ), tailAfter 0 B⟩ := by
          have charge := zero 0 (by omega)
          simp only [Nat.zero_mul, Nat.cast_zero, add_zero, rootWord] at charge
          rw [rootExec _ s (by omega), ite_eq_left hs, charge, add_zero]
        have tailBound : tailAfter 0 B < Q * m := by
          have ex := safe p 0 (by omega) (fun i hi => bandzero p hp i (by omega))
          have model := literal_block_execution (Q * m) hk m B v (-p) 0 (by nlinarith)
          have accepted : runAdmissible (Q * m - 1) (Q * m - 1 - 0) m B = true := by
            cases h : runAdmissible (Q * m - 1) (Q * m - 1 - 0) m B with
            | false => rw [h] at model; simp only [Bool.false_eq_true, ite_false] at model; rw [ex] at model; cases model.1
            | true => rfl
          exact model.2 accepted
        refine ⟨tailAfter 0 B, tailBound, ?_, ?_⟩
        · intro i hi
          have : i = 0 := by omega
          subst i
          simpa only [zeroArchive, rootWord] using chosen
        · intro j s hs zeros
          have next := safe j s hs zeros
          have future := eventual_step (Q * m) m π (some ⟨v, -j, s⟩) (some v) []
            _ B chosen (native j s (by omega))
          rw [next] at future
          refine ⟨?_, ?_⟩
          · simpa only [rootAr, Nat.zero_add, Nat.one_mul, endpointReading, List.nil_append] using future
          · intro history w record
            have updated : OriginalRecord (Q * m) (by omega) (w ++ List.ofFn B) =
                some ⟨v, -j + (m:ℕ), tailAfter 0 B⟩ := by
              exact (OriginalExecutionBridge.record_append (Q * m) hk w (List.ofFn B)).trans
                ((congrArg (runBits (Q * m) B) record).trans next)
            rw [rootAr]
            constructor
            · refine ⟨?_, trivial⟩
              exact (OriginalExecutionBridge.output_record (Q * m) (by omega) _).trans
                (congrArg endpointReading updated)
            · simpa only [archiveWords, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.zero_add, Nat.one_mul] using updated
      · obtain ⟨tail, tailBound, before, survive⟩ := ih (by omega) (by omega)
        have bandFuture (j : ZMod (Q * m + 1)) (hj : 0 < j.val ∧ j.val < a) :
            ∃ d c, NativeExecute π d (some ⟨v, -j + ((t * m:ℕ):ZMod (Q * m + 1)), tail⟩)
              (some v) (zeroArchive π v t) = some (labels j, c) := by
          have ex := (survive j 0 (by omega) (fun i hi => bandzero j hj i (by omega))).1
          simpa only [lowLabel j hj] using ex
        have chosenNext : π (some v) (zeroArchive π v t) = .inr (zeroWord π v t) := by
          cases selected : π (some v) (zeroArchive π v t) with
          | inr C => simp only [zeroWord, selected]
          | inl y =>
            have stopLabel (j : ZMod (Q * m + 1)) (hj : 0 < j.val ∧ j.val < a) : y = labels j := by
              exact eventual_unique (Q * m) m π _ (some v) (zeroArchive π v t)
                y (labels j) ⟨0, 0, by simp [NativeExecute, selected]⟩ (bandFuture j hj)
            exact False.elim (distinct ((stopLabel p hp).symm.trans (stopLabel q hq)))
        have safe : runAdmissible (Q * m - 1) (Q * m - 1 - tail) m (zeroWord π v t) = true := by
          by_contra illegal
          have dead (j : ZMod (Q * m + 1)) : runBits (Q * m) (zeroWord π v t)
              (some ⟨v, -j + ((t * m:ℕ):ZMod (Q * m + 1)), tail⟩) = none := by
            rw [(literal_block_execution (Q * m) hk m (zeroWord π v t) v _ tail tailBound).1, ite_eq_right illegal]
          have gone (j : ZMod (Q * m + 1)) (hj : 0 < j.val ∧ j.val < a) :=
            eventual_step (Q * m) m π _ (some v) (zeroArchive π v t) (labels j)
              (zeroWord π v t) chosenNext (bandFuture j hj)
          have ep := gone p hp
          have eq := gone q hq
          rw [dead] at ep eq
          exact distinct (eventual_unique (Q * m) m π none (some v)
            (zeroArchive π v t ++ [(zeroWord π v t, endpointReading none)]) _ _ ep eq)
        have nextAr : zeroArchive π v (t + 1) = zeroArchive π v t ++ [(zeroWord π v t, some v)] := by
          rfl
        have phase (j : ZMod (Q * m + 1)) : -j + ((t * m:ℕ):ZMod (Q * m + 1)) + (m:ℕ) =
            -j + (((t + 1) * m:ℕ):ZMod (Q * m + 1)) := by push_cast; ring
        refine ⟨tailAfter tail (zeroWord π v t),
          (literal_block_execution (Q * m) hk m (zeroWord π v t) v 0 tail tailBound).2 safe, ?_, ?_⟩
        · intro i hi
          by_cases old : i < t
          · exact before i old
          · have : i = t := by omega
            subst i
            exact chosenNext
        · intro j s hs zeros
          obtain ⟨future, actual⟩ := survive j s hs (fun i hi => zeros i (by omega))
          have next : runBits (Q * m) (zeroWord π v t)
              (some ⟨v, -j + ((t * m:ℕ):ZMod (Q * m + 1)), tail⟩) =
              some ⟨v, -j + (((t + 1) * m:ℕ):ZMod (Q * m + 1)), tailAfter tail (zeroWord π v t)⟩ := by
            rw [(literal_block_execution (Q * m) hk m (zeroWord π v t) v _ tail tailBound).1,
              ite_eq_left safe, zeros t (by omega), add_zero, phase]
          have continuation := eventual_step (Q * m) m π _ (some v) (zeroArchive π v t)
            _ (zeroWord π v t) chosenNext future
          rw [next] at continuation
          refine ⟨?_, ?_⟩
          · simpa only [nextAr, endpointReading] using continuation
          · intro history w record
            obtain ⟨matched, current⟩ := actual history record
            have updated : OriginalRecord (Q * m) (by omega) ((w ++ archiveWords (zeroArchive π v t)) ++ List.ofFn (zeroWord π v t)) =
                some ⟨v, -j + (((t + 1) * m:ℕ):ZMod (Q * m + 1)), tailAfter tail (zeroWord π v t)⟩ := by
              exact (OriginalExecutionBridge.record_append (Q * m) hk
                (w ++ archiveWords (zeroArchive π v t)) (List.ofFn (zeroWord π v t))).trans
                ((congrArg (runBits (Q * m) (zeroWord π v t)) current).trans next)
            rw [nextAr]
            constructor
            · apply (actual_archive_append (Q * m) (by omega) w (zeroArchive π v t) [(zeroWord π v t, some v)]).mpr
              refine ⟨matched, ?_, trivial⟩
              exact (OriginalExecutionBridge.output_record (Q * m) (by omega) _).trans
                (congrArg endpointReading updated)
            · simpa only [archiveWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using updated
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨tail, tailBound, chosenAll, _⟩ := walk Q (by omega) le_rfl
    exact chosenAll t ht
  · intro t j ht positive band
    exact bandzero j ⟨positive, band⟩ t ht
  · intro t positive bounded
    obtain ⟨tail, tailBound, _, survive⟩ := walk t positive bounded
    exact ⟨tail, tailBound, survive⟩

#print axioms first_tour_common_archive

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix
