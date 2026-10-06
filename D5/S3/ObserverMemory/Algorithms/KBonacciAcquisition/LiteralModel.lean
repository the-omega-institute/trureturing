/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Original KBonacci weights, literal bit execution, and joint actual-history realization. -/

import D5.S0.Tower.DBonacci.Substitution

import D5.S0.Tower.DBonacciGeneral.UniformBaseGap

import Mathlib.Data.Nat.Periodic

import D5.S1.Words.ClosedRunStarts

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

import Mathlib.Data.ZMod.Basic

import Mathlib.Data.List.OfFn

import Mathlib.Data.Nat.ModEq

import Mathlib.Tactic


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators

/- This model uses the original KBonacci recurrence, its fixed mod-two scalar,
legal-run language and endpoint alphabet. Its all-order results do not provide
a theorem for an arbitrary recurrence, scalar readout or controlled machine. -/

/-- Bit transitions use the whole ambient phase group. Endpoint phase restrictions
are imposed on sources, never on the intermediate bit states. -/
structure LiveRecord (k : ℕ) where
  value : ZMod 2
  phase : ZMod (k + 1)
  tail : ℕ
  deriving DecidableEq

/-- The original matched scalar coefficient cycle. -/
def coefficient (k : ℕ) (phase : ZMod (k + 1)) : ZMod 2 :=
  if phase = 0 ∨ phase = -1 then 1 else 0

/-- The original integer weights, reduced in the actual scalar readout. -/
def originalWeight (k n : ℕ) : ZMod 2 := dbonacci k (n + 2)

/-- The original-weight scalar, rather than the inverse-Perron word value. -/
def originalWordValue (k : ℕ) {n : ℕ} (word : Fin n → Bool) : ZMod 2 :=
  ∑ i : Fin n, if word i then originalWeight k i.val else 0

/-- `none` is absorbing rejection; a zero clears the current tail. -/
def bitUpdate (k : ℕ) (bit : Bool) : Option (LiveRecord k) → Option (LiveRecord k)
  | none => none
  | some q =>
      if bit then
        if q.tail + 1 < k then
          some ⟨q.value + coefficient k q.phase, q.phase + 1, q.tail + 1⟩
        else none
      else some ⟨q.value, q.phase + 1, 0⟩

/-- Execute all bits chronologically using the native controlled-word executor. -/
def runBits (k : ℕ) {n : ℕ} (word : Fin n → Bool)
    (q : Option (LiveRecord k)) : Option (LiveRecord k) :=
  runWord (bitUpdate k) (List.ofFn word) q

/-- The single reading offered after a complete block. -/
def endpointReading {k : ℕ} : Option (LiveRecord k) → Option (ZMod 2)
  | none => none
  | some q => some q.value

/-- Literal scalar increment, without any intermediate observation. -/
def wordIncrement (k : ℕ) {n : ℕ} (phase : ZMod (k + 1))
    (word : Fin n → Bool) : ZMod 2 :=
  ∑ i : Fin n, if word i then coefficient k (phase + (i.val : ℕ)) else 0

/-- The tail obtained by chronological updates, used only on surviving runs. -/
def tailAfter : {n : ℕ} → ℕ → (Fin n → Bool) → ℕ
  | 0, s, _ => s
  | _n + 1, s, word => tailAfter (if word 0 then s + 1 else 0) (Fin.tail word)

/-- Complete-block execution agrees with the native old-tail scanner and with the
literal scalar, phase and tail updates. Rejection is independent of the scalar. -/
theorem literal_block_execution (k : ℕ) (hk : 2 ≤ k) (n : ℕ)
    (word : Fin n → Bool) (v : ZMod 2) (phase : ZMod (k + 1))
    (s : ℕ) (hs : s < k) :
    runBits k word (some ⟨v, phase, s⟩) =
      (if runAdmissible (k - 1) (k - 1 - s) n word then
        some ⟨v + wordIncrement k phase word, phase + (n : ℕ), tailAfter s word⟩
      else none) ∧
    (runAdmissible (k - 1) (k - 1 - s) n word = true → tailAfter s word < k) := by
  have rejected : ∀ (bits : List Bool), runWord (bitUpdate k) bits none = none := by
    intro bits
    induction bits with
    | nil => rfl
    | cons bit bits ih => simpa [runWord, bitUpdate] using ih
  induction n generalizing v phase s with
  | zero => simp [runBits, runWord, wordIncrement, tailAfter, runAdmissible, hs]
  | succ n ih =>
      have increment : wordIncrement k phase word =
          (if word 0 then coefficient k phase else 0) +
            wordIncrement k (phase + 1) (Fin.tail word) := by
        unfold wordIncrement
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.tail, Fin.val_succ,
          Nat.cast_add, Nat.cast_one]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [add_assoc, add_comm (1 : ZMod (k + 1)) (i.val : ℕ), ← add_assoc]
        rfl
      have phaseShift : phase + 1 + (n : ℕ) = phase + ((n + 1 : ℕ) : ZMod (k + 1)) := by
        push_cast
        abel
      cases head : word 0 with
      | false =>
          have scanner : runAdmissible (k - 1) (k - 1 - s) (n + 1) word =
              runAdmissible (k - 1) (k - 1) n (Fin.tail word) := by
            cases hf : k - 1 - s <;> simp [runAdmissible, head]
          have h := ih (Fin.tail word) v (phase + 1) 0 (by omega)
          simpa +unfoldPartialApp [runBits, List.ofFn_succ, runWord, bitUpdate, head, scanner,
            increment, tailAfter, phaseShift, Fin.tail] using h
      | true =>
          by_cases safe : s + 1 < k
          · have fuel : k - 1 - s = (k - 1 - (s + 1)) + 1 := by omega
            have scanner : runAdmissible (k - 1) (k - 1 - s) (n + 1) word =
                runAdmissible (k - 1) (k - 1 - (s + 1)) n (Fin.tail word) := by
              rw [fuel]
              simp [runAdmissible, head]
            have h := ih (Fin.tail word) (v + coefficient k phase) (phase + 1)
              (s + 1) safe
            simpa +unfoldPartialApp [runBits, List.ofFn_succ, runWord, bitUpdate, head, safe,
              scanner, increment, tailAfter, phaseShift, add_assoc, Fin.tail] using h
          · have fuel : k - 1 - s = 0 := by omega
            simp [runBits, List.ofFn_succ, runWord, bitUpdate, head, safe,
              fuel, runAdmissible, rejected]

#print axioms literal_block_execution

/-- Every live endpoint record is realized jointly by one original-weight legal
history of complete blocks. Each constituent block is locally legal as well. -/
theorem joint_history_realization (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (hphase : Nat.gcd m (k + 1) ∣ phase.val) :
    ∃ (N : ℕ) (word : Fin N → Bool),
      m ∣ N ∧ DBonacciAdmissible k N word ∧
      runBits k word (some ⟨0, 0, 0⟩) = some ⟨v, phase, s⟩ ∧
      originalWordValue k word = v ∧ tailAfter 0 word = s ∧
      ∀ (j : ℕ) (hj : (j + 1) * m ≤ N),
        DBonacciAdmissible k m (fun i : Fin m =>
          word ⟨j * m + i.val, by nlinarith [i.isLt]⟩) := by
  classical
  have compatible : Nat.ModEq (Nat.gcd m (k + 1)) 0 phase.val :=
    (Nat.modEq_zero_iff_dvd.mpr hphase).symm
  let crt := Nat.chineseRemainder' (n := m) (m := k + 1) compatible
  let N := crt.val + (s + 2) * (m * (k + 1))
  have long : s + 2 ≤ N := by
    have hproduct : 1 ≤ m * (k + 1) := by nlinarith
    dsimp [N]
    nlinarith
  have divisible : m ∣ N := by
    apply dvd_add (Nat.modEq_zero_iff_dvd.mp crt.property.1)
    exact dvd_mul_of_dvd_right (dvd_mul_right m (k + 1)) (s + 2)
  have phaseN : (N : ZMod (k + 1)) = phase := by
    have modular : Nat.ModEq (k + 1) N phase.val := by
      dsimp [N]
      rw [← Nat.mul_assoc]
      exact (Nat.add_mul_modulus_modEq_iff).mpr crt.property.2
    have h := (ZMod.natCast_eq_natCast_iff N phase.val (k + 1)).mpr modular
    simpa using h
  let z := N - s - 1
  have positive : 0 < z := by dsimp [z]; omega
  let d := wordIncrement k ((N - s : ℕ) : ZMod (k + 1)) (fun _ : Fin s => true)
  let x := v + d
  let bit := decide (x ≠ 0)
  let bits := [bit] ++ List.replicate z false ++ List.replicate s true
  have length : bits.length = N := by simp [bits, z]; omega
  have appendRun : ∀ (left right : List Bool) (q : Option (LiveRecord k)),
      runWord (bitUpdate k) (left ++ right) q =
        runWord (bitUpdate k) right (runWord (bitUpdate k) left q) := by
    intro left
    induction left with
    | nil => intro right q; rfl
    | cons bit left ih => intro right q; simpa [runWord] using ih right (bitUpdate k bit q)
  have zeros : ∀ (r : ℕ) (value : ZMod 2) (phi : ZMod (k + 1)) (tail : ℕ),
      runWord (bitUpdate k) (List.replicate r false) (some ⟨value, phi, tail⟩) =
        some ⟨value, phi + (r : ℕ), if r = 0 then tail else 0⟩ := by
    intro r
    induction r with
    | zero => intro value phi tail; simp [runWord]
    | succ r ih =>
        intro value phi tail
        rw [List.replicate_succ, runWord]
        simp only [bitUpdate, Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        simp [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
  have onesTail : ∀ (r tail : ℕ), tailAfter tail (fun _ : Fin r => true) = tail + r := by
    intro r
    induction r with
    | zero => intro tail; simp [tailAfter]
    | succ r ih =>
        intro tail
        simp only [tailAfter, ↓reduceIte]
        change tailAfter (tail + 1) (fun _ : Fin r => true) = tail + (r + 1)
        rw [ih]
        omega
  have ones : ∀ (r : ℕ) (value : ZMod 2) (phi : ZMod (k + 1)) (tail : ℕ),
      tail + r < k →
      runWord (bitUpdate k) (List.replicate r true) (some ⟨value, phi, tail⟩) =
        some ⟨value + wordIncrement k phi (fun _ : Fin r => true), phi + (r : ℕ), tail + r⟩ := by
    intro r value phi tail htr
    have h := (literal_block_execution k hk r (fun _ => true) value phi tail (by omega)).1
    have scanner := runAdmissible_eq_true_of_length_le (k - 1) (k - 1 - tail)
      r (fun _ => true) (by omega) (by omega)
    simpa [runBits, List.ofFn_const, scanner, onesTail] using h
  have bitScalar : (if bit then (1 : ZMod 2) else 0) = x := by
    have represent : ∀ a : ZMod 2, (if decide (a ≠ 0) then (1 : ZMod 2) else 0) = a := by
      intro a
      have alternatives : a = 0 ∨ a = 1 := by
        have bound := ZMod.val_lt a
        have hval : a.val = 0 ∨ a.val = 1 := by omega
        rcases hval with hval | hval
        · left
          apply ZMod.val_injective 2
          simpa [ZMod.val_zero] using hval
        · right
          apply ZMod.val_injective 2
          simpa [show (1 : ZMod 2).val = 1 from rfl] using hval
      rcases alternatives with rfl | rfl <;> simp
    exact represent x
  have headRun : runWord (bitUpdate k) [bit] (some ⟨0, 0, 0⟩) =
      some ⟨x, 1, if bit then 1 else 0⟩ := by
    cases hbit : bit <;>
      simp [runWord, bitUpdate, coefficient, hbit, show 1 < k by omega] at bitScalar ⊢
    all_goals rw [← bitScalar]
  have headZeros : runWord (bitUpdate k) ([bit] ++ List.replicate z false)
      (some ⟨0, 0, 0⟩) = some ⟨x, ((N - s : ℕ) : ZMod (k + 1)), 0⟩ := by
    rw [appendRun, headRun, zeros]
    have hz : 1 + z = N - s := by dsimp [z]; omega
    simp only [show z ≠ 0 by omega, ↓reduceIte]
    have hzPhase : (1 : ZMod (k + 1)) + (z : ℕ) = ((N - s : ℕ) : ZMod (k + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun a : ℕ => (a : ZMod (k + 1))) hz
    rw [hzPhase]
  have actual : runWord (bitUpdate k) bits (some ⟨0, 0, 0⟩) = some ⟨v, phase, s⟩ := by
    dsimp only [bits]
    rw [appendRun, headZeros, ones s x ((N - s : ℕ) : ZMod (k + 1)) 0 (by omega)]
    have value : x + d = v := by
      have two : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      dsimp [x]
      calc
        _ = v + (2 : ZMod 2) * d := by ring
        _ = v := by rw [two]; simp
    have hend : N - s + s = N := by omega
    simpa only [zero_add, d, value, ← Nat.cast_add, hend, phaseN]
  let word : Fin bits.length → Bool := bits.get
  have run : runBits k word (some ⟨0, 0, 0⟩) = some ⟨v, phase, s⟩ := by
    change runWord (bitUpdate k) (List.ofFn bits.get) (some ⟨0, 0, 0⟩) = _
    rw [List.ofFn_get]
    exact actual
  have model := literal_block_execution k hk bits.length word 0 0 0 (by omega)
  have scanner : runAdmissible (k - 1) (k - 1) bits.length word = true := by
    cases h : runAdmissible (k - 1) (k - 1) bits.length word with
    | true => rfl
    | false =>
        have bad := model.1
        simp only [Nat.sub_zero, h, Bool.false_eq_true, ↓reduceIte] at bad
        rw [run] at bad
        contradiction
  have legal : DBonacciAdmissible k bits.length word := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa [ha, DBonacciAdmissible] using scanner
  have record : (⟨wordIncrement k 0 word, (bits.length : ℕ), tailAfter 0 word⟩ : LiveRecord k) =
      ⟨v, phase, s⟩ := by
    have equal := model.1
    simp only [Nat.sub_zero, scanner, ↓reduceIte, zero_add] at equal
    exact Option.some.inj (equal.symm.trans run)
  have scalar : originalWordValue k word = v := by
    let G := originalWeight k
    have two : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    have initial : ∀ i, i < k → G i = if i = 0 then 1 else 0 := by
      intro i hi
      rw [show G i = (dbonacci k (i + 2) : ZMod 2) from rfl,
        dbonacci_add_two_of_lt k i hi]
      cases i with
      | zero => simp
      | succ i => simp [Nat.cast_pow, pow_succ, two]
    have recurrence : ∀ q, k ≤ q → G q = ∑ i ∈ Finset.range k, G (q - k + i) := by
      intro q hq
      have h := congrArg (fun a : ℕ => (a : ZMod 2)) (dbonacci_add_two_of_le k q hq)
      have hcast : G q = ∑ i : Fin k, G (q - k + i.val) := by
        simpa [G, originalWeight, Nat.cast_sum] using h
      rw [Finset.sum_fin_eq_sum_range] at hcast
      calc
        G q = _ := hcast
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.mem_range.mp hi]
    have firstLast : G k = 1 := by
      rw [show G k = (dbonacci k (k + 2) : ZMod 2) from rfl,
        D5.S0.Tower.DBonacciGeneral.UniformBaseGap.dbonacci_diagonal_cardinality]
      rw [Nat.cast_sub (one_le_pow_of_one_le' (by norm_num : 1 ≤ (2 : ℕ)) k)]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, two,
        zero_pow (by omega : k ≠ 0)]
      exact ZMod.neg_eq_self_mod_two 1
    have period : Function.Periodic G (k + 1) := by
      intro q
      have left := recurrence (q + k) (by omega)
      have right := recurrence (q + k + 1) (by omega)
      have eqLeft : q + k - k = q := by omega
      have eqRight : q + k + 1 - k = q + 1 := by omega
      rw [eqLeft] at left
      rw [eqRight] at right
      have slide :
          (∑ i ∈ Finset.range k, G (q + 1 + i)) + G q =
            (∑ i ∈ Finset.range k, G (q + i)) + G (q + k) := by
        calc
          _ = ∑ i ∈ Finset.range (k + 1), G (q + i) := by
            rw [Finset.sum_range_succ']
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            omega
          _ = _ := Finset.sum_range_succ _ _
      rw [← left, ← right] at slide
      have twice : G (q + k) + G (q + k) = 0 := by
        calc
          _ = (2 : ZMod 2) * G (q + k) := by ring
          _ = 0 := by rw [two, zero_mul]
      rw [twice] at slide
      have hneg : G (q + k + 1) = -G q := eq_neg_of_add_eq_zero_left slide
      have selfneg := ZMod.neg_eq_self_mod_two (G q)
      simpa [Nat.add_assoc] using hneg.trans selfneg
    have identical : originalWordValue k word = wordIncrement k 0 word := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases bit : word i
      · simp only [bit, ↓reduceIte, zero_add]
        change G i.val = coefficient k (i.val : ZMod (k + 1))
        rw [← period.map_mod_nat i.val]
        let r := i.val % (k + 1)
        have hr : r < k + 1 := Nat.mod_lt _ (by omega)
        have base : G r = if r = 0 ∨ r = k then 1 else 0 := by
          by_cases h : r = k
          · simp [h, firstLast]
          · rw [initial r (by omega)]
            simp [h]
        have zero : (i.val : ZMod (k + 1)) = 0 ↔ r = 0 := by
          rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff']
          simp [r]
        have last : (i.val : ZMod (k + 1)) = -1 ↔ r = k := by
          constructor
          · intro h
            have hv := congrArg ZMod.val h
            simpa [ZMod.val_natCast, ZMod.val_neg_one, r] using hv
          · intro h
            apply (ZMod.val_injective (k + 1))
            simpa [ZMod.val_natCast, ZMod.val_neg_one, r] using h
        rw [base]
        simp only [coefficient, zero, last]
      · simp [bit]
    exact identical.trans (congrArg LiveRecord.value record)
  refine ⟨bits.length, word, length ▸ divisible, legal, run, scalar,
    congrArg LiveRecord.tail record, ?_⟩
  intro j hj
  let block : Fin m → Bool := fun i => word ⟨j * m + i.val, by nlinarith [i.isLt]⟩
  by_cases short : m < k
  · obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [ha]
    exact runAdmissible_eq_true_of_length_le a a m block (by omega) le_rfl
  · open D5.S1.Words.ClosedRunStarts in
    apply (closed_word_run_start_equivalence m k (by omega) (by omega) block).1.mpr
    intro start hblock
    have avoid := (closed_word_run_start_equivalence bits.length k (by omega)
      (by nlinarith) word).1.mp legal
    apply avoid (j * m + start)
    refine ⟨by nlinarith [hblock.1], ?_⟩
    intro i hlo hhi
    have hlength : start + k ≤ m := hblock.1
    have lower : j * m ≤ i.val := by omega
    have upper : i.val < j * m + m := by omega
    let r : Fin m := ⟨i.val - j * m, by omega⟩
    have index : (⟨j * m + r.val, by nlinarith [r.isLt]⟩ : Fin bits.length) = i := by
      apply Fin.ext
      dsimp [r]
      omega
    have hb := hblock.2 r (by dsimp [r]; omega) (by dsimp [r]; omega)
    simpa only [block, index] using hb

#print axioms joint_history_realization


end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
