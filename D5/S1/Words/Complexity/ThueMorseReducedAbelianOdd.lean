/- GID: D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ThueMorseReducedAbelianOdd
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=bounded-enumeration; basis=terminal=atom:33a0c49c89088efa8b9fcdd754c415e0d143feae6a059675163315c207b996f2; result=D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_two_pow_add_one
   digest: Odd Thue-Morse reduced abelian complexity reflects to half length. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Destutter

namespace D5.S1.Words.Complexity

/-- The zero-indexed Thue-Morse word: parity of the binary digits. -/
def thueMorse : Nat -> Bool :=
  Nat.binaryRec false fun bit _ parity => bit != parity

/-- The literal factor at an arbitrary natural start, in left-to-right order. -/
def factor (length start : Nat) : List Bool :=
  (List.range length).map (fun i => thueMorse (start + i))

/-- Collapse each maximal constant run to one letter, including the empty word. -/
def runCompress (w : List Bool) : List Bool :=
  w.destutter (fun a b => a ≠ b)

/-- Counts of false and true, in that coordinate order. -/
def parikh (word : List Bool) : Nat × Nat :=
  (word.count false, word.count true)

@[simp] private theorem thueMorse_zero : thueMorse 0 = false := rfl

@[simp] private theorem thueMorse_two_mul (n : Nat) :
    thueMorse (2 * n) = thueMorse n := by
  rw [show 2 * n = Nat.bit false n by simp [Nat.bit]]
  rw [thueMorse, Nat.binaryRec_eq]
  · change (false != thueMorse n) = thueMorse n
    cases thueMorse n <;> rfl
  · exact Or.inl rfl

@[simp] private theorem thueMorse_two_mul_add_one (n : Nat) :
    thueMorse (2 * n + 1) = !thueMorse n := by
  rw [show 2 * n + 1 = Nat.bit true n by simp [Nat.bit]]
  rw [thueMorse, Nat.binaryRec_eq]
  · change (true != thueMorse n) = !thueMorse n
    cases thueMorse n <;> rfl
  · exact Or.inr (fun _ => rfl)

private def transition (start : Nat) : Nat :=
  if thueMorse start = thueMorse (start + 1) then 0 else 1

private def alternations : Nat -> Nat -> Nat
  | 0, _ => 0
  | edgeCount + 1, start => transition start + alternations edgeCount (start + 1)

private theorem alternations_le (edgeCount start : Nat) :
    alternations edgeCount start <= edgeCount := by
  induction edgeCount generalizing start with
  | zero => simp [alternations]
  | succ edgeCount ih =>
      simp only [alternations]
      have ht : transition start <= 1 := by
        simp only [transition]
        split <;> omega
      have ha := ih (start + 1)
      omega

@[simp] private theorem transition_two_mul (n : Nat) : transition (2 * n) = 1 := by
  simp [transition]

@[simp] private theorem transition_two_mul_add_one (n : Nat) :
    transition (2 * n + 1) = 1 - transition n := by
  simp only [transition, thueMorse_two_mul_add_one]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, thueMorse_two_mul]
  cases thueMorse n <;> cases thueMorse (n + 1) <;> decide

private theorem alternations_double_even (n q : Nat) :
    alternations (2 * n) (2 * q) = 2 * n - alternations n q := by
  induction n generalizing q with
  | zero => simp [alternations]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [alternations, transition_two_mul]
      rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega, ih]
      rw [transition_two_mul_add_one]
      have ha := alternations_le n (q + 1)
      have ht : transition q <= 1 := by
        simp only [transition]
        split <;> omega
      omega

private theorem alternations_double_odd (n q : Nat) :
    alternations (2 * n) (2 * q + 1) = 2 * n - alternations n q := by
  induction n generalizing q with
  | zero => simp [alternations]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [alternations, transition_two_mul_add_one]
      rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega]
      simp only [transition_two_mul]
      rw [show 2 * (q + 1) + 1 = 2 * (q + 1) + 1 by rfl, ih]
      have ha := alternations_le n (q + 1)
      have ht : transition q <= 1 := by
        simp only [transition]
        split <;> omega
      omega

private theorem thueMorse_two_pow_add (k x : Nat) (hx : x < 2 ^ k) :
    thueMorse (2 ^ k + x) = !thueMorse x := by
  induction k generalizing x with
  | zero =>
      have : x = 0 := by simpa using hx
      subst x
      decide
  | succ k ih =>
      obtain ⟨q, hq | hq⟩ := x.even_or_odd'
      · subst x
        have hq_lt : q < 2 ^ k := by
          simp only [Nat.pow_succ] at hx
          omega
        rw [show 2 ^ (k + 1) + 2 * q = 2 * (2 ^ k + q) by
          simp only [Nat.pow_succ]
          omega]
        simp [ih q hq_lt]
      · subst x
        have hq_lt : q < 2 ^ k := by
          simp only [Nat.pow_succ] at hx
          omega
        rw [show 2 ^ (k + 1) + (2 * q + 1) = 2 * (2 ^ k + q) + 1 by
          simp only [Nat.pow_succ]
          omega]
        simp [ih q hq_lt]

private theorem transition_two_pow_add (k start : Nat) (h : start + 1 < 2 ^ k) :
    transition (2 ^ k + start) = transition start := by
  rw [transition, transition]
  rw [thueMorse_two_pow_add k start (by omega)]
  rw [show 2 ^ k + start + 1 = 2 ^ k + (start + 1) by omega]
  rw [thueMorse_two_pow_add k (start + 1) h]
  cases thueMorse start <;> cases thueMorse (start + 1) <;> decide

private theorem alternations_two_pow_add (k edgeCount start : Nat)
    (h : start + edgeCount < 2 ^ k) :
    alternations edgeCount (2 ^ k + start) = alternations edgeCount start := by
  induction edgeCount generalizing start with
  | zero => simp [alternations]
  | succ edgeCount ih =>
      simp only [alternations]
      rw [transition_two_pow_add k start (by omega)]
      rw [show 2 ^ k + start + 1 = 2 ^ k + (start + 1) by omega]
      rw [ih (start + 1) (by omega)]

private def runs (length start : Nat) : Nat :=
  if length = 0 then 0 else alternations (length - 1) start + 1

private theorem runs_le (length start : Nat) : runs length start <= length := by
  cases length with
  | zero => simp [runs]
  | succ length =>
      simp only [runs, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact Nat.succ_le_succ (alternations_le length start)

private theorem runs_odd_even (n q : Nat) :
    runs (2 * n + 1) (2 * q) = 2 * n + 2 - runs (n + 1) q := by
  simp only [runs, show 2 * n + 1 ≠ 0 by omega, ↓reduceIte,
    show 2 * n + 1 - 1 = 2 * n by omega, alternations_double_even,
    Nat.add_one_ne_zero, show n + 1 - 1 = n by omega]
  have ha := alternations_le n q
  omega

private theorem runs_odd_odd (n q : Nat) :
    runs (2 * n + 1) (2 * q + 1) = 2 * n + 2 - runs (n + 1) q := by
  simp only [runs, show 2 * n + 1 ≠ 0 by omega, ↓reduceIte,
    show 2 * n + 1 - 1 = 2 * n by omega, alternations_double_odd,
    Nat.add_one_ne_zero, show n + 1 - 1 = n by omega]
  have ha := alternations_le n q
  omega

private theorem odd_reflect_runs (n q : Nat) :
    Odd (2 * n + 2 - runs (n + 1) q) <-> Odd (runs (n + 1) q) := by
  have hr := runs_le (n + 1) q
  have hle : runs (n + 1) q <= 2 * n + 2 := by omega
  simpa [show 2 * n + 2 = 2 * (n + 1) by omega] using Nat.odd_sub' hle

private theorem runs_two_pow_add (k length start : Nat)
    (h : start + length < 2 ^ k) :
    runs length (2 ^ k + start) = runs length start := by
  cases length with
  | zero => simp [runs]
  | succ length =>
      simp only [runs, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact congrArg (· + 1) (alternations_two_pow_add k length start (by omega))

private theorem exists_complement_factor (length start : Nat) :
    ∃ start', runs length start' = runs length start ∧
      thueMorse start' = !thueMorse start := by
  let k := start + length + 1
  have hsl : start + length < 2 ^ k :=
    (Nat.lt_succ_self (start + length)).trans Nat.lt_two_pow_self
  refine ⟨2 ^ k + start, runs_two_pow_add k length start hsl, ?_⟩
  exact thueMorse_two_pow_add k start (lt_of_le_of_lt (Nat.le_add_right start length) hsl)

private def reducedParikhOf (runCount : Nat) (initial : Bool) : Nat × Nat :=
  if initial then (runCount / 2, runCount - runCount / 2)
  else (runCount - runCount / 2, runCount / 2)

/-- The Parikh vector after run-reducing the indicated Thue-Morse factor. -/
def reducedParikh (length start : Nat) : Nat × Nat :=
  reducedParikhOf (runs length start) (thueMorse start)

private def listRuns : List Bool -> Nat
  | [] => 0
  | [_] => 1
  | a :: b :: word => (if a = b then 0 else 1) + listRuns (b :: word)

private theorem parikh_runCompress_cons (a : Bool) (word : List Bool) :
    parikh (runCompress (a :: word)) = reducedParikhOf (listRuns (a :: word)) a := by
  induction word generalizing a with
  | nil => cases a <;> simp [runCompress, parikh, listRuns, reducedParikhOf]
  | cons b word ih =>
      by_cases h : a = b
      · subst a
        simpa [runCompress, List.destutter_cons_cons, ← List.destutter_cons', listRuns]
          using ih b
      · have hc : runCompress (a :: b :: word) = a :: runCompress (b :: word) := by
          exact List.destutter'_cons_pos word h
        rw [hc]
        simp only [listRuns, h, ↓reduceIte]
        have ha : a = !b := by cases a <;> cases b <;> simp_all
        subst a
        have hi := ih b
        simp only [parikh] at hi ⊢
        rw [List.count_cons, List.count_cons]
        rw [Prod.mk.injEq] at hi
        rw [hi.1, hi.2]
        cases b <;> simp [reducedParikhOf] <;> constructor <;> omega

private theorem factor_succ (length start : Nat) :
    factor (length + 1) start = thueMorse start :: factor length (start + 1) := by
  simp only [factor, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.add_comm, Nat.add_left_comm]

private theorem listRuns_factor_succ (length start : Nat) :
    listRuns (factor (length + 1) start) = alternations length start + 1 := by
  induction length generalizing start with
  | zero => simp [factor, listRuns, alternations]
  | succ length ih =>
      rw [factor_succ, factor_succ, listRuns, ← factor_succ, ih]
      simp [alternations, transition, Nat.add_assoc]

/-- The arithmetic vector is the literal Parikh vector of the run-compressed factor. -/
theorem reducedParikh_eq_parikh_runCompress (length start : Nat) :
    reducedParikh length start = parikh (runCompress (factor length start)) := by
  cases length with
  | zero => cases thueMorse start <;>
      simp [reducedParikh, reducedParikhOf, runs, factor, runCompress, parikh]
  | succ length =>
      rw [factor_succ, parikh_runCompress_cons, ← factor_succ, listRuns_factor_succ]
      simp [reducedParikh, runs]

/-- Equality of reduced Parikh vectors for two equal-length factors. -/
def ReducedAbelianEquivalent (length start1 start2 : Nat) : Prop :=
  reducedParikh length start1 = reducedParikh length start2

/-- The run count together with the initial letter exactly when that count is odd. -/
def reducedAbelianCode (length start : Nat) : Nat × Bool :=
  let runCount := runs length start
  (runCount, if Odd runCount then thueMorse start else false)

private def codeOf (runCount : Nat) (initial : Bool) : Nat × Bool :=
  (runCount, if Odd runCount then initial else false)

private theorem reducedParikhOf_sum (runCount : Nat) (initial : Bool) :
    (reducedParikhOf runCount initial).1 + (reducedParikhOf runCount initial).2 =
      runCount := by
  have hd : runCount / 2 <= runCount := Nat.div_le_self runCount 2
  cases initial <;> simp [reducedParikhOf] <;> omega

private theorem reducedParikhOf_same_runs_iff (runCount : Nat)
    (initial1 initial2 : Bool) :
    reducedParikhOf runCount initial1 = reducedParikhOf runCount initial2 <->
      codeOf runCount initial1 = codeOf runCount initial2 := by
  cases initial1 <;> cases initial2
  · simp
  · by_cases hr : Odd runCount
    · obtain ⟨k, rfl⟩ := hr.exists_bit1
      simp [reducedParikhOf, codeOf]
      omega
    · rw [Nat.not_odd_iff_even] at hr
      obtain ⟨k, rfl⟩ := hr
      simp [reducedParikhOf, codeOf]
      omega
  · by_cases hr : Odd runCount
    · obtain ⟨k, rfl⟩ := hr.exists_bit1
      simp [reducedParikhOf, codeOf]
      omega
    · rw [Nat.not_odd_iff_even] at hr
      obtain ⟨k, rfl⟩ := hr
      simp [reducedParikhOf, codeOf]
      omega
  · simp

private theorem reducedParikhOf_eq_iff_codeOf_eq (r1 r2 : Nat)
    (initial1 initial2 : Bool) :
    reducedParikhOf r1 initial1 = reducedParikhOf r2 initial2 <->
      codeOf r1 initial1 = codeOf r2 initial2 := by
  constructor
  · intro h
    have hr : r1 = r2 := by
      have hs := congrArg (fun p : Nat × Nat => p.1 + p.2) h
      simpa only [reducedParikhOf_sum] using hs
    subst r2
    exact (reducedParikhOf_same_runs_iff r1 initial1 initial2).mp h
  · intro h
    have hr : r1 = r2 := by
      have hs := congrArg Prod.fst h
      simpa [codeOf] using hs
    subst r2
    exact (reducedParikhOf_same_runs_iff r1 initial1 initial2).mpr h

/-- Reduced Parikh equality is exactly equality of the canonical class codes. -/
theorem reducedAbelianEquivalent_iff_code_eq (length start1 start2 : Nat) :
    ReducedAbelianEquivalent length start1 start2 <->
      reducedAbelianCode length start1 = reducedAbelianCode length start2 := by
  simpa only [ReducedAbelianEquivalent, reducedParikh, reducedAbelianCode, codeOf] using
    reducedParikhOf_eq_iff_codeOf_eq (runs length start1) (runs length start2)
      (thueMorse start1) (thueMorse start2)

private def reflectCode (n : Nat) (code : Nat × Bool) : Nat × Bool :=
  (2 * n + 2 - code.1, code.2)

private theorem reducedAbelianCode_odd_even (n q : Nat) :
    reducedAbelianCode (2 * n + 1) (2 * q) =
      reflectCode n (reducedAbelianCode (n + 1) q) := by
  simp only [reducedAbelianCode, reflectCode, runs_odd_even, odd_reflect_runs,
    thueMorse_two_mul]

private theorem reducedAbelianCode_odd_odd (n q : Nat) :
    reducedAbelianCode (2 * n + 1) (2 * q + 1) =
      reflectCode n
        (runs (n + 1) q, if Odd (runs (n + 1) q) then !thueMorse q else false) := by
  simp only [reducedAbelianCode, reflectCode, runs_odd_odd, odd_reflect_runs,
    thueMorse_two_mul_add_one]

private noncomputable def reducedAbelianCodes (length : Nat) : Finset (Nat × Bool) := by
  classical
  exact ((Finset.range (length + 1)).product Finset.univ).filter fun code =>
    ∃ start, reducedAbelianCode length start = code

private theorem mem_reducedAbelianCodes_iff {length : Nat} (_hlength : 0 < length)
    (code : Nat × Bool) :
    code ∈ reducedAbelianCodes length <->
      ∃ start, reducedAbelianCode length start = code := by
  classical
  simp only [reducedAbelianCodes, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨start, rfl⟩ := h
    simpa [reducedAbelianCode] using Nat.lt_succ_of_le (runs_le length start)

private theorem fst_le_of_mem_reducedAbelianCodes {length : Nat}
    (hlength : 0 < length) {code : Nat × Bool}
    (hcode : code ∈ reducedAbelianCodes length) : code.1 <= length := by
  obtain ⟨start, hstart⟩ :=
    (mem_reducedAbelianCodes_iff hlength code).mp hcode
  rw [← hstart]
  simpa [reducedAbelianCode] using runs_le length start

private theorem reducedAbelianCodes_card_odd (n : Nat) :
    (reducedAbelianCodes (n + 1)).card =
      (reducedAbelianCodes (2 * n + 1)).card := by
  classical
  apply Finset.card_bij (fun code _ => reflectCode n code)
  · intro code hcode
    obtain ⟨q, hq⟩ :=
      (mem_reducedAbelianCodes_iff (by omega : 0 < n + 1) code).mp hcode
    apply (mem_reducedAbelianCodes_iff (by omega : 0 < 2 * n + 1) _).mpr
    refine ⟨2 * q, ?_⟩
    rw [reducedAbelianCode_odd_even, hq]
  · intro code1 hcode1 code2 hcode2 heq
    apply Prod.ext
    · have h1 := fst_le_of_mem_reducedAbelianCodes (by omega : 0 < n + 1) hcode1
      have h2 := fst_le_of_mem_reducedAbelianCodes (by omega : 0 < n + 1) hcode2
      have hfst := congrArg Prod.fst heq
      simp only [reflectCode] at hfst
      omega
    · have hsnd := congrArg Prod.snd heq
      simpa [reflectCode] using hsnd
  · intro code hcode
    obtain ⟨start, hstart⟩ :=
      (mem_reducedAbelianCodes_iff (by omega : 0 < 2 * n + 1) code).mp hcode
    obtain ⟨q, hq | hq⟩ := start.even_or_odd'
    · subst start
      let shortCode := reducedAbelianCode (n + 1) q
      have hshort : shortCode ∈ reducedAbelianCodes (n + 1) :=
        (mem_reducedAbelianCodes_iff (by omega : 0 < n + 1) _).mpr ⟨q, rfl⟩
      refine ⟨shortCode, hshort, ?_⟩
      rw [← reducedAbelianCode_odd_even]
      exact hstart
    · subst start
      obtain ⟨q', hruns, hletter⟩ := exists_complement_factor (n + 1) q
      let shortCode := reducedAbelianCode (n + 1) q'
      have hshort : shortCode ∈ reducedAbelianCodes (n + 1) :=
        (mem_reducedAbelianCodes_iff (by omega : 0 < n + 1) _).mpr ⟨q', rfl⟩
      refine ⟨shortCode, hshort, ?_⟩
      have hcomplement : shortCode =
          (runs (n + 1) q,
            if Odd (runs (n + 1) q) then !thueMorse q else false) := by
        simp only [shortCode, reducedAbelianCode, hruns, hletter]
      rw [hcomplement, ← reducedAbelianCode_odd_odd]
      exact hstart

/-- Reduced Parikh vectors of all length-`length` factors over every natural start. -/
noncomputable def reducedAbelianClasses (length : Nat) : Finset (Nat × Nat) := by
  classical
  exact ((Finset.range (length + 1)).product (Finset.range (length + 1))).filter
    fun parikh => ∃ start, reducedParikh length start = parikh

private theorem mem_reducedAbelianClasses_iff {length : Nat} (_hlength : 0 < length)
    (parikh : Nat × Nat) :
    parikh ∈ reducedAbelianClasses length <->
      ∃ start, reducedParikh length start = parikh := by
  classical
  simp only [reducedAbelianClasses, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨start, rfl⟩ := h
    have hr := runs_le length start
    have hd := Nat.div_le_self (runs length start) 2
    have hs : runs length start - runs length start / 2 <= runs length start :=
      Nat.sub_le _ _
    cases hletter : thueMorse start
    · simp only [reducedParikh, reducedParikhOf, hletter, Bool.false_eq_true,
        ↓reduceIte]
      exact Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
        (Finset.mem_range.mpr (by omega))
    · simp only [reducedParikh, reducedParikhOf, hletter, ↓reduceIte]
      exact Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
        (Finset.mem_range.mpr (by omega))

private def codeParikh (code : Nat × Bool) : Nat × Nat :=
  reducedParikhOf code.1 code.2

private theorem codeParikh_reducedAbelianCode (length start : Nat) :
    codeParikh (reducedAbelianCode length start) = reducedParikh length start := by
  apply (reducedParikhOf_same_runs_iff (runs length start)
    (if Odd (runs length start) then thueMorse start else false)
    (thueMorse start)).mpr
  simp [codeOf]

private theorem reducedAbelianCodes_card_eq_classes (length : Nat) (hlength : 0 < length) :
    (reducedAbelianCodes length).card = (reducedAbelianClasses length).card := by
  classical
  apply Finset.card_bij (fun code _ => codeParikh code)
  · intro code hcode
    obtain ⟨start, hstart⟩ := (mem_reducedAbelianCodes_iff hlength code).mp hcode
    apply (mem_reducedAbelianClasses_iff hlength _).mpr
    refine ⟨start, ?_⟩
    rw [← codeParikh_reducedAbelianCode, hstart]
  · intro code1 hcode1 code2 hcode2 heq
    obtain ⟨start1, hstart1⟩ := (mem_reducedAbelianCodes_iff hlength code1).mp hcode1
    obtain ⟨start2, hstart2⟩ := (mem_reducedAbelianCodes_iff hlength code2).mp hcode2
    have hparikh : reducedParikh length start1 = reducedParikh length start2 := by
      calc
        reducedParikh length start1 = codeParikh (reducedAbelianCode length start1) :=
          (codeParikh_reducedAbelianCode length start1).symm
        _ = codeParikh code1 := congrArg codeParikh hstart1
        _ = codeParikh code2 := heq
        _ = codeParikh (reducedAbelianCode length start2) :=
          congrArg codeParikh hstart2.symm
        _ = reducedParikh length start2 := codeParikh_reducedAbelianCode length start2
    have hcodes := (reducedAbelianEquivalent_iff_code_eq length start1 start2).mp hparikh
    exact hstart1.symm.trans (hcodes.trans hstart2)
  · intro parikh hparikh
    obtain ⟨start, hstart⟩ :=
      (mem_reducedAbelianClasses_iff hlength parikh).mp hparikh
    let code := reducedAbelianCode length start
    have hcode : code ∈ reducedAbelianCodes length :=
      (mem_reducedAbelianCodes_iff hlength code).mpr ⟨start, rfl⟩
    refine ⟨code, hcode, ?_⟩
    change codeParikh (reducedAbelianCode length start) = parikh
    rw [codeParikh_reducedAbelianCode, hstart]

/-- Reduced abelian complexity of the Thue-Morse word, over all natural starts. -/
noncomputable def R (length : Nat) : Nat :=
  (reducedAbelianClasses length).card

/-- The all-start odd-index recurrence conjectured by Campbell-Currie-Rampersad. -/
theorem reducedAbelianComplexity_odd (n : Nat) :
    R (2 * n + 1) = R (n + 1) := by
  unfold R
  calc
    (reducedAbelianClasses (2 * n + 1)).card =
        (reducedAbelianCodes (2 * n + 1)).card :=
      (reducedAbelianCodes_card_eq_classes (2 * n + 1) (by omega)).symm
    _ = (reducedAbelianCodes (n + 1)).card := (reducedAbelianCodes_card_odd n).symm
    _ = (reducedAbelianClasses (n + 1)).card :=
      reducedAbelianCodes_card_eq_classes (n + 1) (by omega)

private theorem reducedAbelianClasses_two :
    reducedAbelianClasses 2 = {(1, 0), (0, 1), (1, 1)} := by
  classical
  ext parikh
  rw [mem_reducedAbelianClasses_iff (by omega : 0 < 2)]
  constructor
  · rintro ⟨start, rfl⟩
    cases h0 : thueMorse start <;> cases h1 : thueMorse (start + 1) <;>
      simp [reducedParikh, reducedParikhOf, runs, alternations, transition, h0, h1]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · refine ⟨5, ?_⟩
      decide
    · refine ⟨1, ?_⟩
      decide
    · refine ⟨0, ?_⟩
      decide

theorem reducedAbelianComplexity_two : R 2 = 3 := by
  rw [R, reducedAbelianClasses_two]
  decide

/-- At every power of two plus one, reduced abelian complexity is three. -/
theorem reducedAbelianComplexity_two_pow_add_one (k : Nat) :
    R (2 ^ k + 1) = 3 := by
  induction k with
  | zero => simpa using reducedAbelianComplexity_two
  | succ k ih =>
      rw [Nat.pow_succ]
      rw [show 2 ^ k * 2 + 1 = 2 * 2 ^ k + 1 by omega]
      exact (reducedAbelianComplexity_odd (2 ^ k)).trans ih

#print axioms reducedAbelianEquivalent_iff_code_eq
#print axioms reducedParikh_eq_parikh_runCompress
#print axioms reducedAbelianComplexity_odd
#print axioms reducedAbelianComplexity_two_pow_add_one

end D5.S1.Words.Complexity
