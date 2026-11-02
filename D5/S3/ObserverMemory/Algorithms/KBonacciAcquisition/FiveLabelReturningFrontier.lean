/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Five forced-threshold band labels and the literal width-seven returning frontier. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
/-! Exact original-history prices and a fixed literal returning-frontier stream. -/

noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open D5.S0.Automata.TypedPartialDFAOOverBase
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse PhysicalWindowDecoder OriginalAcquiredTrace
open GlobalPresetObstruction DonorCorrection
open scoped BigOperators

/-- The seven distinct legal-source labels: outside, five band labels, high tail. -/
def initialLabel {Y : Type u} (Q : ℕ) (labels : Fin 7 → Y) (bottom : Y) :
    Option (LiveRecord (7 * Q)) → Y
  | none => bottom
  | some q => if 7 * Q - 6 ≤ q.tail then labels 6 else
      if h : 1 ≤ (-q.phase).val ∧ (-q.phase).val ≤ 5 then
        labels ⟨(-q.phase).val, by omega⟩ else labels 0

/-- The complete literal stream, in the order in which its bits are issued. -/
def attainingWords (Q : ℕ) : List (Fin 7 → Bool) :=
  (fun i => decide (i.val < 6)) ::
    (List.replicate (Q - 1) (fun i => decide (i.val % 2 = 0)) ++
    (fun i => decide (i.val = 4)) ::
    (List.replicate (Q - 1) (fun _ => false) ++
      [fun i => decide (i.val = 4 ∨ i.val = 5), fun i => decide (i.val = 0)]))

private theorem derivative_at (Q : ℕ) (hQ : 2 ≤ Q) (j : ℕ) (hj : j < 7 * Q + 1)
    (B : Fin 7 → Bool) :
    wordIncrement (7 * Q) (-((j : ℕ) : ZMod (7 * Q + 1))) B =
      extendedBit B j + if j = 0 then 0 else extendedBit B (j - 1) := by
  rw [increment_derivative (7 * Q) (by omega) 7 (by omega)]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]

private theorem root_execution (Q : ℕ) (hQ : 2 ≤ Q)
    (v : ZMod 2) (phase : ZMod (7 * Q + 1)) (s : ℕ) (hs : s < 7 * Q) :
    runBits (7 * Q) (fun i : Fin 7 => decide (i.val < 6)) (some ⟨v, phase, s⟩) =
      if s < 7 * Q - 6 then
        some ⟨v + wordIncrement (7 * Q) phase (fun i : Fin 7 => decide (i.val < 6)),
          phase + 7, 0⟩ else none := by
  have cut : List.ofFn (fun i : Fin 7 => decide (i.val < 6)) =
      List.replicate 6 true ++ false :: [] := by decide
  have ex := first_zero_block_exact (7 * Q) (by omega) 7 6 _ [] cut
    (short_legal (7 * Q) 7 (by omega) (by omega) _) v phase s hs
  have tail : tailAfter 0 (fun i : Fin 7 => decide (i.val < 6)) = 0 := by decide
  simpa [tail, show s + 6 < 7 * Q ↔ s < 7 * Q - 6 by omega] using ex

private theorem root_charge (Q : ℕ) (hQ : 2 ≤ Q) (j : ℕ) (hj : j < 7 * Q + 1) :
    wordIncrement (7 * Q) (-((j : ℕ) : ZMod (7 * Q + 1)))
      (fun i : Fin 7 => decide (i.val < 6)) = if j = 0 ∨ j = 6 then 1 else 0 := by
  rw [derivative_at Q hQ j hj]
  by_cases h : j < 7
  · interval_cases j <;> norm_num [extendedBit, bitScalar] <;> decide
  · have h0 : j ≠ 0 := by omega
    have h1 : ¬j - 1 < 7 ∨ j = 7 := by omega
    rcases h1 with h1|rfl
    · simp [extendedBit, h, h0, h1, show j ≠ 6 by omega]
    · norm_num [extendedBit, bitScalar] <;> decide

private theorem gcd_one (Q : ℕ) : Nat.gcd 7 (7 * Q + 1) = 1 := by
  rw [Nat.gcd_mul_left_add_right]
  decide

private theorem root_merge (k : ℕ) (hk : 14 ≤ k) (B : Fin 7 → Bool)
    (ne : B ≠ fun i => decide (i.val < 6)) (v : ZMod 2) (phase : ZMod (k + 1)) :
    runBits k B (some ⟨v, phase, k - 7⟩) = runBits k B (some ⟨v, phase, k - 6⟩) := by
  have classify : ∀ bits : List Bool,
      bits = List.replicate bits.length true ∨
        ∃ a rest, bits = List.replicate a true ++ false :: rest := by
    intro bits
    induction bits with
    | nil => exact Or.inl rfl
    | cons bit bits ih =>
      cases bit
      · exact Or.inr ⟨0, bits, rfl⟩
      · rcases ih with all | ⟨a, rest, cut⟩
        · exact Or.inl (by simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons true) all)
        · exact Or.inr ⟨a + 1, rest, by simp [List.replicate_succ, cut]⟩
  rcases classify (List.ofFn B) with all | ⟨a, rest, cut⟩
  · have eq : B = allOneBlock 7 := by
      apply List.ofFn_injective
      simpa [allOneBlock] using all
    rw [eq]
    have ex (s : ℕ) (hs : s < k) :=
      (all_one_archive_exact k 7 (by omega) (by omega) 1 v phase s hs (fun _ => 0)).2.2
    have orbit (s : ℕ) : allOneOrbit k 7 1 (some ⟨v, phase, s⟩) =
        runBits k (allOneBlock 7) (some ⟨v, phase, s⟩) := rfl
    rw [←orbit, ex _ (by omega), ←orbit, ex _ (by omega)]
    rw [if_neg (by omega), if_neg (by omega)]
  · have length := congrArg List.length cut
    simp only [List.length_ofFn, List.length_append, List.length_replicate, List.length_cons] at length
    have a6 : a ≠ 6 := by
      intro eq
      subst a
      have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
      subst rest
      apply ne
      apply List.ofFn_injective
      rw [cut]
      decide
    have a5 : a ≤ 5 := by omega
    have low := first_zero_block_exact k (by omega) 7 a B rest cut
      (short_legal k 7 (by omega) (by omega) B) v phase (k - 7) (by omega)
    have high := first_zero_block_exact k (by omega) 7 a B rest cut
      (short_legal k 7 (by omega) (by omega) B) v phase (k - 6) (by omega)
    rw [low, high, if_pos (by omega), if_pos (by omega)]

private theorem forced_root {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (pi : NarrowWindowCost.Selector 7 Y) (d : ℕ)
    (native : ∀ phase s, s < 7 * Q → ∃ c,
      NativeExecute pi d (some ⟨0, phase, s⟩) (some 0) [] =
        some (initialLabel Q labels bottom (some ⟨0, phase, s⟩), c)) :
    ∃ b, d = b + 1 ∧ pi (some 0) [] = .inr (fun i : Fin 7 => decide (i.val < 6)) := by
  obtain ⟨c, lo⟩ := native 0 (7 * Q - 7) (by omega)
  obtain ⟨c', hi⟩ := native 0 (7 * Q - 6) (by omega)
  have lowTarget : initialLabel Q labels bottom (some ⟨0, 0, 7 * Q - 7⟩) = labels 0 := by
    simp [initialLabel, show ¬7 * Q - 6 ≤ 7 * Q - 7 by omega]
  have highTarget : initialLabel Q labels bottom (some ⟨0, 0, 7 * Q - 6⟩) = labels 6 := by
    simp [initialLabel]
  rw [lowTarget] at lo
  rw [highTarget] at hi
  have different : labels 0 ≠ labels 6 := by
    intro eq
    have := distinct eq
    norm_num at this
  cases d with
  | zero =>
    have eq : NativeExecute (k := 7 * Q) pi 0 (some ⟨0, 0, 7 * Q - 7⟩) (some 0) [] =
        NativeExecute (k := 7 * Q) pi 0 (some ⟨0, 0, 7 * Q - 6⟩) (some 0) [] := rfl
    rw [lo, hi] at eq
    exact False.elim (different (congrArg Prod.fst (Option.some.inj eq)))
  | succ b =>
    refine ⟨b, rfl, ?_⟩
    cases chosen : pi (some 0) [] with
    | inl y =>
      simp only [NativeExecute, chosen, Option.some.injEq, Prod.mk.injEq] at lo hi
      exact False.elim (different (lo.1.symm.trans hi.1))
    | inr B =>
      congr 1
      by_contra ne
      have merge := root_merge (7 * Q) (by omega) B ne 0 0
      have eq : NativeExecute (k := 7 * Q) pi (b + 1) (some ⟨0, 0, 7 * Q - 7⟩) (some 0) [] =
          NativeExecute (k := 7 * Q) pi (b + 1) (some ⟨0, 0, 7 * Q - 6⟩) (some 0) [] := by
        simp only [NativeExecute, chosen, merge]
      rw [lo, hi] at eq
      exact different (congrArg Prod.fst (Option.some.inj eq))

private theorem band_silent (Q : ℕ) (hQ : 2 ≤ Q) (t : ℕ)
    (ht : t < 2 * Q + 1) (nt : ¬Q ∣ t) (j : Fin 5) (B : Fin 7 → Bool) :
    wordIncrement (7 * Q)
      (-((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + ((t * 7 : ℕ) : ZMod (7 * Q + 1))) B = 0 := by
  have jt := j.isLt
  have zeroT : ((7 * Q + 1 : ℕ) : ZMod (7 * Q + 1)) = 0 := ZMod.natCast_self _
  have t0 : 0 < t := by
    by_contra e
    have eq : t = 0 := by omega
    exact nt (eq.symm ▸ dvd_zero Q)
  have tQ : t ≠ Q := by intro e; subst t; exact nt (dvd_refl Q)
  have t2Q : t ≠ 2 * Q := by intro e; subst t; exact nt (dvd_mul_left Q 2)
  have outside (n : ℕ) (hn : n < 7 * Q + 1) (large : 8 ≤ n)
      (eq : -((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + ((t * 7 : ℕ) : ZMod (7 * Q + 1)) =
        -((n : ℕ) : ZMod (7 * Q + 1))) :
      wordIncrement (7 * Q)
        (-((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + ((t * 7 : ℕ) : ZMod (7 * Q + 1))) B = 0 := by
    rw [eq, derivative_at Q hQ n hn]
    simp [extendedBit, show ¬n < 7 by omega, show n ≠ 0 by omega,
      show ¬n - 1 < 7 by omega]
  by_cases first : t < Q
  · let n := 7 * Q + 1 + (j.val + 1) - t * 7
    apply outside n (by dsimp [n]; omega) (by dsimp [n]; omega)
    have le : t * 7 ≤ 7 * Q + 1 + (j.val + 1) := by omega
    dsimp only [n]
    rw [Nat.cast_sub le]
    simp only [Nat.cast_add, zeroT, zero_add]
    push_cast
    ring
  · let n := 2 * (7 * Q + 1) + (j.val + 1) - t * 7
    apply outside n (by dsimp [n]; omega) (by dsimp [n]; omega)
    have le : t * 7 ≤ 2 * (7 * Q + 1) + (j.val + 1) := by omega
    dsimp only [n]
    rw [Nat.cast_sub le]
    simp only [Nat.cast_add, Nat.cast_mul, zeroT, mul_zero, zero_add]
    push_cast
    ring

private theorem two_visits (Q : ℕ) (hQ : 2 ≤ Q) :
    OriginalCommonTailCompression.count Q 1 (2 * Q) = 2 := by
  classical
  have test (i : ℕ) (hi : i < 2 * Q) : Q ∣ 1 + i ↔ i = Q - 1 ∨ i = 2 * Q - 1 := by
    constructor
    · rintro ⟨a, ha⟩
      have a0 : 0 < a := by nlinarith
      have a3 : a < 3 := by nlinarith
      interval_cases a <;> omega
    · rintro (rfl|rfl)
      · convert dvd_refl Q using 1 <;> omega
      · convert dvd_mul_left Q 2 using 1 <;> omega
  unfold OriginalCommonTailCompression.count
  have rows : ∀ i ∈ Finset.range (2 * Q),
      (if Q ∣ 1 + i then 1 else 0 : ℕ) =
        (if i = Q - 1 then 1 else 0) + (if i = 2 * Q - 1 then 1 else 0) := by
    intro i hi
    simp only [test i (Finset.mem_range.mp hi)]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl rows, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', show Q - 1 < 2 * Q by omega, show 2 * Q - 1 < 2 * Q by omega]

private theorem adaptive_lower {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (alphabet : Bool) (d : ℕ)
    (feasible : OriginalAdaptiveFeasible (7 * Q) 7 (by omega) alphabet
      (initialLabel Q labels bottom) d) : 2 * Q + 2 ≤ d := by
  classical
  by_contra small
  have hd : d ≤ 2 * Q + 1 := by omega
  obtain ⟨pi, legal, bot, correct⟩ := feasible
  have native (phase : ZMod (7 * Q + 1)) (s : ℕ) (hs : s < 7 * Q) : ∃ c,
      NativeExecute pi d (some ⟨0, phase, s⟩) (some 0) [] =
        some (initialLabel Q labels bottom (some ⟨0, phase, s⟩), c) := by
    obtain ⟨c, _, ex⟩ := OwnPathCharges.native_fiber (7 * Q) 7 (by omega) (by omega)
      alphabet (initialLabel Q labels bottom) 0 d pi
      (by
        intro history
        dsimp only
        intro obs
        obtain ⟨c, le, ex⟩ := correct history
        rw [obs] at ex
        exact ⟨c, le, ex⟩) phase s hs (by rw [gcd_one]; exact one_dvd _)
    exact ⟨c, ex⟩
  obtain ⟨b, db, chosen⟩ := forced_root Q hQ labels distinct bottom pi d native
  subst d
  have rootRecord (j : Fin 5) :
      runBits (7 * Q) (fun i : Fin 7 => decide (i.val < 6))
        (some ⟨0, -((j.val + 1 : ℕ) : ZMod (7 * Q + 1)), 0⟩) =
        some ⟨0, -((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + (7 : ℕ), 0⟩ := by
    rw [root_execution Q hQ _ _ _ (by omega), if_pos (by omega)]
    rw [root_charge Q hQ _ (by omega), if_neg (by omega)]
    simp
  have target (j : Fin 5) : initialLabel Q labels bottom
      (some ⟨0, -((j.val + 1 : ℕ) : ZMod (7 * Q + 1)), 0⟩) = labels ⟨j.val + 1, by omega⟩ := by
    simp only [initialLabel, neg_neg, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : j.val + 1 < 7 * Q + 1),
      if_neg (by omega : ¬7 * Q - 6 ≤ 0), dite_eq_left (by have := j.isLt; omega)]
    split <;> rename_i h
    · rfl
    · exact False.elim (h (by have := j.isLt; omega))
  let phase (x : ULift.{u} (Fin 5)) : ZMod (7 * Q + 1) := -((x.down.val + 1 : ℕ) : _)
  have sources (x : ULift.{u} (Fin 5)) : ∃ history : List (AllowedBlock (7 * Q) 7 alphabet),
      OriginalRecord (7 * Q) (by omega) (history.flatMap (fun a => List.ofFn a.val)) =
        some ⟨0, phase x, 0⟩ := by
    obtain ⟨history, actual⟩ :=
      ((whole_first_zero_acquisition (7 * Q) 7 (by omega) (by omega) alphabet (fun _ => ())).1
        (some ⟨0, phase x, 0⟩)).mp (by
          change 0 < 7 * Q ∧ _
          exact ⟨by omega, by rw [gcd_one]; exact one_dvd _⟩)
    exact ⟨history, (record_history _ 7 (by omega) alphabet history).trans actual⟩
  let ws (x : ULift.{u} (Fin 5)) :=
    (Classical.choose (sources x)).flatMap (fun a => List.ofFn a.val) ++
      List.ofFn (fun i : Fin 7 => decide (i.val < 6))
  have record (x : ULift.{u} (Fin 5)) : OriginalRecord (7 * Q) (by omega) (ws x) =
      some ⟨0, phase x + ((1 * 7 : ℕ) : ZMod (7 * Q + 1)), 0⟩ := by
    dsimp only [ws]
    have ex := record_append (7 * Q) (by omega)
      ((Classical.choose (sources x)).flatMap (fun a => List.ofFn a.val))
      (List.ofFn (fun i : Fin 7 => decide (i.val < 6)))
    change OriginalRecord (7 * Q) (by omega) _ =
      runBits (7 * Q) (fun i : Fin 7 => decide (i.val < 6))
        (OriginalRecord (7 * Q) (by omega) _) at ex
    rw [ex, Classical.choose_spec (sources x)]
    exact rootRecord x.down
  have success (x : ULift.{u} (Fin 5)) : ∃ c,
      NarrowWindowCost.execute (7 * Q) (by omega) pi b (ws x) (some 0)
        [((fun i : Fin 7 => decide (i.val < 6)), some 0)] =
        some (labels ⟨x.down.val + 1, by have := x.down.isLt; omega⟩, c) := by
    obtain ⟨c, ex⟩ := native (phase x) 0 (by omega)
    dsimp only [phase] at ex
    rw [target x.down] at ex
    simp only [NativeExecute, chosen, rootRecord x.down, endpointReading, List.nil_append] at ex
    obtain ⟨r, er, eq⟩ := Option.map_eq_some_iff.mp ex
    refine ⟨r.2, ?_⟩
    rw [execute_same _ 7 (by omega)]
    change NativeExecute pi b (OriginalRecord (7 * Q) (by omega) (ws x)) _ _ = _
    rw [record x]
    exact er.trans (congrArg some (show r = (labels ⟨x.down.val + 1, by have := x.down.isLt; omega⟩, r.2) from Prod.ext (Prod.mk.inj eq).1 rfl))
  obtain ⟨P, sep⟩ := OriginalCommonTailCompression.compress (7 * Q) 7 (by omega) pi
    (some 0) (fun x : ULift.{u} (Fin 5) => labels ⟨x.down.val + 1, by have := x.down.isLt; omega⟩)
    phase Q (2 * Q + 1)
    (by intro t ht nt x B; exact band_silent Q hQ t ht nt x.down B)
    b 1 (by omega) Set.univ ws 0 0 (by omega)
    [((fun i : Fin 7 => decide (i.val < 6)), some 0)]
    (by intro x _; exact record x) (by intro x _; exact success x)
  have countBound : OriginalCommonTailCompression.count Q 1 b ≤ 2 := by
    rw [←two_visits Q hQ]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have injective : Function.Injective
      (D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound.adaptiveTranscript P) := by
    intro x y eq
    have eq := distinct (sep x (Set.mem_univ _) y (Set.mem_univ _) eq)
    apply ULift.ext
    apply Fin.ext
    have e := congrArg Fin.val eq
    dsimp only at e
    omega
  have bound := D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound.exact_identification_card_le_pow
    (id : (ULift.{u} (Fin 5) → Fin 2) → ULift.{u} (Fin 5) → Fin 2)
    (by omega) ⟨P,
      D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound.adaptiveProtocol_uses_identity_readout P,
      injective⟩
  simp only [Fintype.card_ulift, Fintype.card_fin] at bound
  have power : 2^OriginalCommonTailCompression.count Q 1 b ≤ (2 : ℕ)^2 :=
    Nat.pow_le_pow_right (by omega) countBound
  omega

private def suffixKind (Q : ℕ) : List (Fin 5) :=
  List.replicate (Q - 1) 0 ++ 1 :: (List.replicate (Q - 1) 2 ++ [3, 4])

private def localRow (a : Fin 5) (i : ℕ) : ZMod 2 :=
  if a = 0 then (if i ≤ 7 then 1 else 0) else
  if a = 1 then (if i = 4 ∨ i = 5 then 1 else 0) else
  if a = 2 then 0 else
  if a = 3 then (if i = 4 ∨ i = 6 then 1 else 0) else
    (if i = 0 ∨ i = 1 then 1 else 0)

private theorem row_even (a : Fin 5) : ∑ i ∈ Finset.range 8, localRow a i = 0 := by
  fin_cases a <;> decide

private theorem row_zero (a : Fin 5) : prefixWord 7 (localRow a) 1 = false := by
  fin_cases a <;> decide

private theorem row_words :
    (fun a : Fin 5 => prefixWord 7 (localRow a)) =
      ![(fun i : Fin 7 => decide (i.val%2 = 0)),
        (fun i : Fin 7 => decide (i.val = 4)),
        (fun _ : Fin 7 => false),
        (fun i : Fin 7 => decide (i.val = 4 ∨ i.val = 5)),
        (fun i : Fin 7 => decide (i.val = 0))] := by decide

private theorem suffix_words (Q : ℕ) :
    (suffixKind Q).map (fun a => prefixWord 7 (localRow a)) = (attainingWords Q).tail := by
  simp only [suffixKind, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    row_words, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, attainingWords, List.tail_cons]
  rfl

private theorem native_suffix (Q : ℕ) (hQ : 2 ≤ Q) (v : ZMod 2)
    (j : ZMod (7 * Q + 1)) :
    (scriptArchive ((attainingWords Q).tail) (some ⟨v, -j, 0⟩)).map Prod.snd =
      chargeArchive (7 * Q) 7 ((suffixKind Q).map localRow) v j := by
  let marked : List ((ℕ → ZMod 2) × Fin 7) :=
    (suffixKind Q).map (fun a => (localRow a, 1))
  have even : ∀ entry ∈ marked, ∑ i ∈ Finset.range 8, entry.1 i = 0 := by
    rintro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    exact row_even a
  have zero : ∀ entry ∈ marked, prefixWord 7 entry.1 entry.2 = false := by
    rintro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    exact row_zero a
  have seam : marked.IsChain (fun a b => 7 + b.2.val ≤ 7 * Q + a.2.val) := by
    simp only [marked, List.isChain_map, List.isChain_iff_getElem, Fin.val_one]
    intro i hi
    omega
  have native := InternalZeroSafety.actual_internal_zero_charge_suffix
    (7 * Q) (by omega) 7 (by omega) (by omega) false marked even zero seam v j 0
    (by omega) (by intro e he; left; have := e.2.isLt; omega)
    (by rw [gcd_one]; exact one_dvd _)
  dsimp only at native
  have rows : marked.map Prod.fst = (suffixKind Q).map localRow := by
    simp [marked, List.map_map, Function.comp_def]
  rw [rows] at native
  have words : (chargeBlocks (7 * Q) 7 (by omega) (by omega) false
      ((suffixKind Q).map localRow)).map Subtype.val = (attainingWords Q).tail := by
    have erased (rows : List (ℕ → ZMod 2)) :
        (chargeBlocks (7 * Q) 7 (by omega) (by omega) false rows).map Subtype.val =
          rows.map (prefixWord 7) := by
      unfold chargeBlocks EndpointCells.AllowedBlock
      rw [List.map_map]
      rfl
    rw [erased, List.map_map]
    exact suffix_words Q
  rw [←words, script_readings]
  exact native.2.1

private theorem suffix_row_at (Q : ℕ) (hQ : 2 ≤ Q) (t : ℕ) (ht : t < Q - 1) :
    (((suffixKind Q).map localRow)[t]?) = some (localRow 0) := by
  simp [suffixKind, List.getElem?_append, ht, List.getElem?_replicate]

private theorem suffix_query_at (Q : ℕ) (hQ : 2 ≤ Q) :
    (((suffixKind Q).map localRow)[Q - 1]?) = some (localRow 1) ∧
    (((suffixKind Q).map localRow)[2 * Q - 1]?) = some (localRow 3) ∧
    (((suffixKind Q).map localRow)[2 * Q]?) = some (localRow 4) := by
  simp [suffixKind, List.getElem?_append, List.getElem?_replicate,
    show ¬Q - 1 < Q - 1 by omega, show ¬2 * Q - 1 < Q - 1 by omega,
    show ¬2 * Q < Q - 1 by omega, show 2 * Q - 1-(Q - 1) = Q by omega,
    show 2 * Q - (Q - 1) = Q + 1 by omega, show ¬Q - 1 < Q - 1 by omega,
    show Q - (Q - 1) = 1 by omega, show Q + 1 - (Q - 1) = 2 by omega]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
  simp [List.getElem?_append]

private theorem shift_query (Q : ℕ) (j : ZMod (7 * Q + 1)) :
    j - ((Q * 7 : ℕ) : ZMod (7 * Q + 1)) = j + 1 ∧
    j - (((2 * Q) * 7 : ℕ) : ZMod (7 * Q + 1)) = j + 2 ∧
    j - (((2 * Q + 1) * 7 : ℕ) : ZMod (7 * Q + 1)) = j - 5 := by
  have period : ((7 * Q : ℕ) : ZMod (7 * Q + 1)) = -1 := by
    have eq : ((7 * Q + 1 : ℕ) : ZMod (7 * Q + 1)) = 0 := ZMod.natCast_self _
    push_cast at eq
    push_cast
    linear_combination eq
  have eq : ((Q * 7 : ℕ) : ZMod (7 * Q + 1)) = -1 := by simpa [Nat.mul_comm] using period
  push_cast at eq ⊢
  constructor
  · linear_combination - eq
  constructor
  · linear_combination - 2 * eq
  · linear_combination - 2 * eq

private theorem band_code (Q : ℕ) (hQ : 2 ≤ Q) (j : Fin 5) :
    windowCharge (7 * Q) 7 (localRow 1) (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + 1) =
      (if j.val = 2 ∨ j.val = 3 then 1 else 0) ∧
    windowCharge (7 * Q) 7 (localRow 3) (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + 2) =
      (if j.val = 1 ∨ j.val = 3 then 1 else 0) ∧
    windowCharge (7 * Q) 7 (localRow 4) (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) - 5) =
      (if j.val = 4 then 1 else 0) := by
  have jt := j.isLt
  have one : (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + 1).val = j.val + 2 := by
    have e : (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + 1) = ((j.val + 2 : ℕ) : ZMod (7 * Q + 1)) := by push_cast; ring
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have two : (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) + 2).val = j.val + 3 := by
    rw [show (2 : ZMod (7 * Q + 1)) = ((2 : ℕ) : ZMod (7 * Q + 1)) by norm_num,
      ←Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have last : (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) - 5).val =
      if j.val = 4 then 0 else 7 * Q + 1 + j.val + 1 - 5 := by
    by_cases eq : j.val = 4
    · simp [eq]
    · rw [if_neg eq]
      have le : 5 ≤ 7 * Q + 1 + j.val + 1 := by omega
      have cast : (((7 * Q + 1 + j.val + 1 - 5 : ℕ) : ZMod (7 * Q + 1))) =
          ((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) - 5 := by
        rw [Nat.cast_sub le]
        push_cast
        have period : ((7 * Q + 1 : ℕ) : ZMod (7 * Q + 1)) = 0 := ZMod.natCast_self _
        push_cast at period
        linear_combination period
      rw [←cast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  simp only [windowCharge, one, two, last, localRow]
  fin_cases j <;> norm_num <;> omega

private theorem profile_band_separates (Q : ℕ) (hQ : 2 ≤ Q) (i j : Fin 5)
    (same : rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((i.val + 1 : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) =
      rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((j.val + 1 : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ))) : i = j := by
  have queries := suffix_query_at Q hQ
  have readat (t : ℕ) := congrArg (fun a => a[t]?) same
  have first := readat (Q - 1)
  have second := readat (2 * Q - 1)
  have last := readat (2 * Q)
  simp only [row_readings_index, queries.1, queries.2.1, queries.2.2, Option.map_some,
    Option.some.injEq] at first second last
  have shift (z : ZMod (7 * Q + 1)) (t : ℕ) :
      z - (7 : ℕ) - ((t * 7 : ℕ) : ZMod (7 * Q + 1)) = z - (((t + 1) * 7 : ℕ) : ZMod (7 * Q + 1)) := by
    push_cast; ring
  rw [shift, shift, show Q - 1 + 1 = Q by omega, (shift_query Q _).1, (shift_query Q _).1] at first
  rw [shift, shift, show 2 * Q - 1 + 1 = 2 * Q by omega, (shift_query Q _).2.1, (shift_query Q _).2.1] at second
  rw [shift, shift, (shift_query Q _).2.2, (shift_query Q _).2.2] at last
  rw [(band_code Q hQ i).1, (band_code Q hQ j).1] at first
  rw [(band_code Q hQ i).2.1, (band_code Q hQ j).2.1] at second
  rw [(band_code Q hQ i).2.2, (band_code Q hQ j).2.2] at last
  fin_cases i <;> fin_cases j <;> simp_all

private theorem profile_mixed (Q : ℕ) (hQ : 2 ≤ Q) (i : Fin 5)
    (j : ℕ) (hj : j < 7 * Q + 1) (large : 7 ≤ j)
    (same : rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((i.val + 1 : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) =
      rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((j : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ))) : False := by
  let t := if j = 7 * Q then Q - 1 else j/7
  have tpos : 1 ≤ t := by dsimp [t]; split_ifs <;> omega
  have tQ : t < Q := by dsimp [t]; split_ifs <;> omega
  have le : t * 7 ≤ j := by dsimp [t]; split_ifs <;> omega
  have within : j - t * 7 ≤ 7 := by dsimp [t]; split_ifs <;> omega
  have eq := congrArg (fun a => a[t - 1]?) same
  rw [row_readings_index, row_readings_index, suffix_row_at Q hQ _ (by omega)] at eq
  simp only [Option.map_some, Option.some.injEq] at eq
  have shift (z : ZMod (7 * Q + 1)) :
      z - (7 : ℕ) - (((t - 1) * 7 : ℕ) : ZMod (7 * Q + 1)) = z - ((t * 7 : ℕ) : ZMod (7 * Q + 1)) := by
    have te : t - 1 + 1 = t := by omega
    have e := congrArg (fun n : ℕ => (n * 7 : ZMod (7 * Q + 1))) te
    push_cast at e ⊢
    linear_combination - e
  rw [shift, shift] at eq
  have left : windowCharge (7 * Q) 7 (localRow 0)
      (((i.val + 1 : ℕ) : ZMod (7 * Q + 1)) - ((t * 7 : ℕ) : ZMod (7 * Q + 1))) = 0 := by
    have inv := (short_window_charge_inverse (7 * Q) (by omega) 7 (by omega)
      (by omega) (localRow 0) (row_even 0)).1
    rw [←inv]
    have phase : -(((i.val + 1 : ℕ) : ZMod (7 * Q + 1)) - ((t * 7 : ℕ) : ZMod (7 * Q + 1))) =
        -((i.val + 1 : ℕ) : ZMod (7 * Q + 1)) + ((t * 7 : ℕ) : ZMod (7 * Q + 1)) := by ring
    rw [phase]
    exact band_silent Q hQ t (by omega) (Nat.not_dvd_of_pos_of_lt (by omega) tQ) i _
  have right : windowCharge (7 * Q) 7 (localRow 0)
      (((j : ℕ) : ZMod (7 * Q + 1)) - ((t * 7 : ℕ) : ZMod (7 * Q + 1))) = 1 := by
    rw [←Nat.cast_sub le]
    have val : ((j - t * 7 : ℕ) : ZMod (7 * Q + 1)).val = j - t * 7 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp [windowCharge, val, within, localRow]
  rw [left, right] at eq
  exact zero_ne_one eq

private theorem archive_separates {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (bottom : Y) (v : ZMod 2)
    (p q : ZMod (7 * Q + 1)) (s r : ℕ) (hs : s < 7 * Q) (hr : r < 7 * Q)
    (same : scriptArchive (attainingWords Q) (some ⟨v, p, s⟩) =
      scriptArchive (attainingWords Q) (some ⟨v, q, r⟩)) :
    initialLabel Q labels bottom (some ⟨v, p, s⟩) =
      initialLabel Q labels bottom (some ⟨v, q, r⟩) := by
  let i := (-p).val
  let j := (-q).val
  have ip : -((i : ℕ) : ZMod (7 * Q + 1)) = p := by simp [i]
  have jq : -((j : ℕ) : ZMod (7 * Q + 1)) = q := by simp [j]
  have hi : i < 7 * Q + 1 := ZMod.val_lt _
  have hj : j < 7 * Q + 1 := ZMod.val_lt _
  have root := congrArg List.head? same
  change some ((fun a : Fin 7 => decide (a.val < 6)),
      endpointReading (runBits (7 * Q) (fun a : Fin 7 => decide (a.val < 6)) (some ⟨v, p, s⟩))) =
    some ((fun a : Fin 7 => decide (a.val < 6)),
      endpointReading (runBits (7 * Q) (fun a : Fin 7 => decide (a.val < 6)) (some ⟨v, q, r⟩))) at root
  have rootReply := congrArg Prod.snd (Option.some.inj root)
  rw [root_execution Q hQ _ _ _ hs, root_execution Q hQ _ _ _ hr] at rootReply
  by_cases lowS : s < 7 * Q - 6
  · have lowR : r < 7 * Q - 6 := by
      by_contra nr
      simp [lowS, nr, endpointReading] at rootReply
    rw [if_pos lowS, if_pos lowR] at rootReply
    have increment : wordIncrement (7 * Q) p (fun a : Fin 7 => decide (a.val < 6)) =
        wordIncrement (7 * Q) q (fun a : Fin 7 => decide (a.val < 6)) :=
      add_left_cancel (Option.some.inj rootReply)
    have suffix := congrArg List.tail same
    change scriptArchive ((attainingWords Q).tail)
      (runBits (7 * Q) (fun a : Fin 7 => decide (a.val < 6)) (some ⟨v, p, s⟩)) =
      scriptArchive ((attainingWords Q).tail)
      (runBits (7 * Q) (fun a : Fin 7 => decide (a.val < 6)) (some ⟨v, q, r⟩)) at suffix
    rw [root_execution Q hQ _ _ _ hs, root_execution Q hQ _ _ _ hr,
      if_pos lowS, if_pos lowR, increment] at suffix
    let z := v + wordIncrement (7 * Q) q (fun a : Fin 7 => decide (a.val < 6))
    have profiles : rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((i : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) =
      rowReadings (7 * Q) 7 ((suffixKind Q).map localRow)
        (((j : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) := by
      have e := congrArg (fun ar => endpointDifferences (some z) (ar.map Prod.snd)) suffix
      have a : p + 7 = -(((i : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) := by rw [←ip]; ring
      have b : q + 7 = -(((j : ℕ) : ZMod (7 * Q + 1)) - (7 : ℕ)) := by rw [←jq]; ring
      rw [a, b, native_suffix Q hQ, native_suffix Q hQ,
        charge_differences, charge_differences] at e
      exact e
    have rootCharges : (if i = 0 ∨ i = 6 then (1 : ZMod 2) else 0) =
        (if j = 0 ∨ j = 6 then (1 : ZMod 2) else 0) := by
      rw [←ip, ←jq, root_charge Q hQ i hi, root_charge Q hQ j hj] at increment
      exact increment
    by_cases bandI : (1 ≤ i ∧ i ≤ 5)
    · have bandJ : 1 ≤ j ∧ j ≤ 5 := by
        by_contra no
        have no0 : j ≠ 0 ∧ j ≠ 6 := by
          simp only [if_neg (by omega : ¬(i = 0 ∨ i = 6))] at rootCharges
          constructor <;> intro e <;> simp [e] at rootCharges
        exact profile_mixed Q hQ ⟨i - 1, by omega⟩ j hj (by omega)
          (by simpa only [show i - 1 + 1 = i by omega] using profiles)
      have eq : (⟨i - 1, by omega⟩ : Fin 5) = (⟨j - 1, by omega⟩ : Fin 5) :=
        profile_band_separates Q hQ _ _
          (by simpa only [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega] using profiles)
      have ij : i = j := by have := congrArg Fin.val eq; dsimp only at this; omega
      simp only [initialLabel, if_neg (by omega : ¬ (7 * Q - 6 ≤ s)),
        if_neg (by omega : ¬ (7 * Q - 6 ≤ r))]
      change (if h : (1 ≤ i ∧ i ≤ 5) then labels ⟨i, by omega⟩ else labels 0) =
        (if h : (1 ≤ j ∧ j ≤ 5) then labels ⟨j, by omega⟩ else labels 0)
      rw [dif_pos bandI, dif_pos bandJ]
      exact congrArg labels (Fin.ext ij)
    · have notBandJ : ¬(1 ≤ j ∧ j ≤ 5) := by
        intro bandJ
        have no0 : i ≠ 0 ∧ i ≠ 6 := by
          simp only [if_neg (by omega : ¬(j = 0 ∨ j = 6))] at rootCharges
          constructor <;> intro e <;> simp [e] at rootCharges
        exact profile_mixed Q hQ ⟨j - 1, by omega⟩ i hi (by omega)
          (by simpa only [show j - 1 + 1 = j by omega] using profiles.symm)
      simp only [initialLabel, if_neg (by omega : ¬ (7 * Q - 6 ≤ s)),
        if_neg (by omega : ¬ (7 * Q - 6 ≤ r))]
      change (if h : (1 ≤ i ∧ i ≤ 5) then labels ⟨i, by omega⟩ else labels 0) =
        (if h : (1 ≤ j ∧ j ≤ 5) then labels ⟨j, by omega⟩ else labels 0)
      rw [dif_neg bandI, dif_neg notBandJ]
  · have highR : ¬r < 7 * Q - 6 := by
      intro lowR
      simp [lowS, lowR, endpointReading] at rootReply
    simp [initialLabel, show (7 * Q - 6 ≤ s) by omega, show (7 * Q - 6 ≤ r) by omega]

/-- Decode an acquired archive using any compatible original legal record. -/
def archiveDecoder {Y : Type u} (Q : ℕ) (labels : Fin 7 → Y) (bottom : Y)
    (v : ZMod 2) (ar : NarrowWindowCost.Archive 7) : Y :=
  if h : ∃ (phase : ZMod (7 * Q + 1)) (s : ℕ), s < 7 * Q ∧
      scriptArchive (attainingWords Q) (some ⟨v, phase, s⟩) = ar then
    initialLabel Q labels bottom (some ⟨v, Classical.choose h,
      Classical.choose (Classical.choose_spec h)⟩)
  else bottom

private theorem archive_decode {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (bottom : Y) (v : ZMod 2)
    (phase : ZMod (7 * Q + 1)) (s : ℕ) (hs : s < 7 * Q) :
    archiveDecoder Q labels bottom v (scriptArchive (attainingWords Q) (some ⟨v, phase, s⟩)) =
      initialLabel Q labels bottom (some ⟨v, phase, s⟩) := by
  have h : ∃ (p : ZMod (7 * Q + 1)) (r : ℕ), r < 7 * Q ∧
      scriptArchive (attainingWords Q) (some ⟨v, p, r⟩) =
        scriptArchive (attainingWords Q) (some ⟨v, phase, s⟩) := ⟨phase, s, hs, rfl⟩
  rw [archiveDecoder, dif_pos h]
  have fact := Classical.choose_spec (Classical.choose_spec h)
  exact archive_separates Q hQ labels bottom v _ _ _ _ fact.1 hs fact.2

/-- Both original global worst paid-block prices equal the fee of the named
width-seven stream. Every actual original history uses its own endpoint archive. -/
theorem original_five_label_returning_frontier {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (alphabet : Bool) :
    GlobalAdaptivePrice (7 * Q) 7 (by omega) alphabet (initialLabel Q labels bottom) =
      ((2 * Q + 2 : ℕ) : ℕ∞) ∧
    GlobalPresetPrice (7 * Q) 7 (by omega) alphabet (initialLabel Q labels bottom) =
      ((2 * Q + 2 : ℕ) : ℕ∞) ∧
    (attainingWords Q).length = 2 * Q + 2 ∧
    ∀ history : List (AllowedBlock (7 * Q) 7 alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let f := initialLabel Q labels bottom
      let decode := archiveDecoder Q labels bottom
      let pi : NarrowWindowCost.Selector 7 Y := fun free ar =>
        match free with
        | none => .inl bottom
        | some v => finalSelector 0 (attainingWords Q) (decode v) free ar
      let q := OriginalRecord (7 * Q) (by omega) w
      let issued := if q = none then [] else scriptArchive (attainingWords Q) q
      PaidTrace pi (NarrowWindowCost.output (7 * Q) (by omega) w) q [] issued (f q) ∧
      issued.map Prod.fst = (if q = none then [] else attainingWords Q) ∧
      issued.length = (if q = none then 0 else 2 * Q + 2) ∧
      NarrowWindowCost.execute (7 * Q) (by omega) pi (2 * Q + 2) w
        (NarrowWindowCost.output (7 * Q) (by omega) w) [] =
          some (f q, issued.length) := by
  classical
  have len : (attainingWords Q).length = 2 * Q + 2 := by
    simp [attainingWords]
    omega
  have upper : OriginalPresetFeasible (7 * Q) 7 (by omega) alphabet
      (initialLabel Q labels bottom) (2 * Q + 2) := by
    rw [←len]
    exact script_global_preset (7 * Q) 7 (by omega) (by omega) alphabet
      (initialLabel Q labels bottom) (attainingWords Q) (archiveDecoder Q labels bottom)
      (archive_decode Q hQ labels bottom)
  refine ⟨FullPositiveWindowPrice.price_exact _ _
    (preset_inclusion _ _ _ _ _ _ upper) (adaptive_lower Q hQ labels distinct bottom alphabet),
    FullPositiveWindowPrice.price_exact _ _ upper
      (fun d h => adaptive_lower Q hQ labels distinct bottom alphabet d
        (preset_inclusion _ _ _ _ _ _ h)), len, ?_⟩
  intro history
  dsimp only
  let w := history.flatMap (fun a => List.ofFn a.val)
  let f := initialLabel Q labels bottom
  let decode := archiveDecoder Q labels bottom
  let pi : NarrowWindowCost.Selector 7 Y := fun free ar =>
    match free with
    | none => .inl bottom
    | some v => finalSelector 0 (attainingWords Q) (decode v) free ar
  have output : NarrowWindowCost.output (7 * Q) (by omega) w =
      endpointReading (OriginalRecord (7 * Q) (by omega) w) := output_record _ _ _
  cases initial : OriginalRecord (7 * Q) (by omega) w with
  | none =>
    simp only [initial, ite_true, endpointReading] at output ⊢
    rw [output]
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    rw [execute_same _ 7 (by omega)]
    change NativeExecute pi (2 * Q + 2) (OriginalRecord (7 * Q) (by omega) w) none [] = some (f none, 0)
    rw [initial]
    rfl
  | some q =>
    have hs : q.tail < 7 * Q := by
      unfold OriginalRecord at initial
      cases scan : (NarrowWindowCost.scanner (7 * Q) (by omega)).eval w with
      | none => simp [scan] at initial
      | some tail =>
        simp only [scan, Option.map_some, Option.some.injEq] at initial
        have eq := congrArg LiveRecord.tail initial
        simpa only [←eq] using tail.isLt
    have qe : (⟨q.value, q.phase, q.tail⟩ : LiveRecord (7 * Q)) = q := by cases q; rfl
    have decoded := archive_decode Q hQ labels bottom q.value q.phase q.tail hs
    rw [qe] at decoded
    have script := original_final_script (7 * Q) 7 (by omega) (attainingWords Q)
      (decode q.value) w (some q.value) []
    dsimp only at script
    rw [initial] at script
    have same (ar : NarrowWindowCost.Archive 7) :
        pi (some q.value) ar = finalSelector 0 (attainingWords Q) (decode q.value) (some q.value) ar := rfl
    have trace := (FullPositiveWindowPrice.trace_congr _ _ (some q.value) same _ _ [] _).mpr script.1
    change decode q.value (scriptArchive (attainingWords Q) (some q)) = f (some q) at decoded
    rw [decoded] at trace
    simp only [initial, Option.some_ne_none, ite_false, endpointReading] at output ⊢
    rw [output]
    refine ⟨trace, script.2.1, script.2.2.1.trans len, ?_⟩
    rw [execute_paid_trace _ 7 (by omega), initial]
    exact ⟨_, trace, rfl, by rw [script.2.2.1, len]⟩

#print axioms original_five_label_returning_frontier

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier
