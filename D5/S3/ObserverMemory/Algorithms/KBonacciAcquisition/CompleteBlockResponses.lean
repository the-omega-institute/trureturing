/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CompleteBlockResponses
   mirror-E: none(waiver:symbolic-response-classification)
   anchors: []
   utility: none
   digest: Exact finite-horizon legality responses of the original k-bonacci scanner. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card

set_option autoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CompleteBlockResponses

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost
open scoped BigOperators

variable (k : ℕ) (hk : 0 < k)

/-- Totalization of the original partial scanner, with absorbing rejection. -/
def run (s : Option (Fin k)) (w : List Bool) : Option (Fin k) :=
  s.bind (fun t => (scanner k hk).evalFrom t w)

/-- Only successful versus rejected execution is observed. -/
def response (s : Option (Fin k)) (w : List Bool) : Bool := (run k hk s w).isSome

/-- Equality of all legality responses within the bit budget. -/
def BitEquivalent (h : ℕ) (s t : Option (Fin k)) : Prop :=
  ∀ w : List Bool, w.length ≤ h → response k hk s w = response k hk t w

/-- The complete literal alphabet, executed as an actual ordered list of blocks. -/
def blockWord {m : ℕ} (blocks : List (Fin m → Bool)) : List Bool :=
  (blocks.map List.ofFn).flatten

/-- Equality of all endpoint legality responses after at most H complete blocks. -/
def BlockEquivalent (m H : ℕ) (s t : Option (Fin k)) : Prop :=
  ∀ blocks : List (Fin m → Bool), blocks.length ≤ H →
    response k hk s (blockWord blocks) = response k hk t (blockWord blocks)

private theorem response_nil (s : Option (Fin k)) :
    response k hk s [] = s.isSome := by
  cases s <;> rfl

private theorem run_append (s : Option (Fin k)) (u v : List Bool) :
    run k hk s (u ++ v) = run k hk (run k hk s u) v := by
  cases s with
  | none => rfl
  | some s => simpa [run] using (scanner k hk).evalFrom_append s u v

private theorem accepts_short (s : Fin k) (w : List Bool)
    (hw : s.val + w.length < k) : response k hk (some s) w = true := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
      cases b with
      | false =>
          change response k hk (some ⟨0, hk⟩) w = true
          apply ih
          simp only [List.length_cons] at hw
          simp only [Fin.val_mk]
          omega
      | true =>
          have hs : s.val + 1 < k := by simp only [List.length_cons] at hw; omega
          change (runTransition (scanner k hk).step s (true :: w)).isSome = true
          simp only [runTransition, scanner, ↓reduceIte, hs]
          apply ih ⟨s.val + 1, hs⟩
          simp only [List.length_cons] at hw
          simp only [Fin.val_mk]
          omega

private theorem response_ones (s : Fin k) (n : ℕ) :
    response k hk (some s) (List.replicate n true) = decide (s.val + n < k) := by
  induction n generalizing s with
  | zero => simpa [response, run, PartialDFA.evalFrom, runTransition] using s.isLt
  | succ n ih =>
      change (runTransition (scanner k hk).step s (List.replicate (n + 1) true)).isSome = _
      simp only [List.replicate_succ, runTransition, scanner, ↓reduceIte]
      split_ifs with hs
      · change response k hk (some ⟨s.val + 1, hs⟩) (List.replicate n true) = _
        rw [ih]
        simp only [Fin.val_mk, Nat.add_assoc, Nat.add_comm 1 n]
      · have hnot : ¬s.val + (n + 1) < k := by omega
        simp [hnot]

private theorem response_zeros (s : Option (Fin k)) (n : ℕ) :
    response k hk s (List.replicate n false) = s.isSome := by
  cases s with
  | none => rfl
  | some s =>
      induction n generalizing s with
      | zero => rfl
      | succ n ih =>
          change response k hk (some ⟨0, hk⟩) (List.replicate n false) = true
          exact ih ⟨0, hk⟩

private theorem response_pad (s : Option (Fin k)) (w : List Bool) (n : ℕ) :
    response k hk s (w ++ List.replicate n false) = response k hk s w := by
  unfold response
  rw [run_append]
  exact response_zeros k hk (run k hk s w) n

/-- The finite-horizon live class coordinate counts distinguishable remaining ones. -/
def coordinate (h : ℕ) (s : Fin k) : ℕ := min (k - 1 - s.val) h

/-- The bounded responses identify two live tails precisely when their truncated
remaining-one coordinates agree. Rejection is separate already at the empty word. -/
theorem live_response_classes (h : ℕ) (s t : Fin k) :
    BitEquivalent k hk h (some s) (some t) ↔ coordinate k h s = coordinate k h t := by
  constructor
  · intro heq
    by_contra hne
    have hs := s.isLt
    have ht := t.isLt
    have split : s.val < t.val ∨ t.val < s.val := by
      dsimp [coordinate] at hne
      omega
    rcases split with hst | hts
    · have hlen : k - t.val ≤ h := by dsimp [coordinate] at hne; omega
      have hr := heq (List.replicate (k - t.val) true) (by simpa using hlen)
      rw [response_ones, response_ones] at hr
      have hleft : s.val + (k - t.val) < k := by omega
      have hright : ¬t.val + (k - t.val) < k := by omega
      simp [hleft, hright] at hr
    · have hlen : k - s.val ≤ h := by dsimp [coordinate] at hne; omega
      have hr := heq (List.replicate (k - s.val) true) (by simpa using hlen)
      rw [response_ones, response_ones] at hr
      have hleft : ¬s.val + (k - s.val) < k := by omega
      have hright : t.val + (k - s.val) < k := by omega
      simp [hleft, hright] at hr
  · intro heq w hw
    by_cases hst : s = t
    · simp [hst]
    · have hs := s.isLt
      have ht := t.isLt
      have hvals : s.val ≠ t.val := fun e => hst (Fin.ext e)
      have hsafe : s.val + h < k ∧ t.val + h < k := by
        dsimp [coordinate] at heq
        omega
      rw [accepts_short k hk s w (by omega), accepts_short k hk t w (by omega)]

private theorem length_blockWord {m : ℕ} (blocks : List (Fin m → Bool)) :
    (blockWord blocks).length = blocks.length * m := by
  induction blocks with
  | nil => simp [blockWord]
  | cons b blocks ih =>
      simp only [blockWord, List.map_cons, List.flatten_cons, List.length_append,
        List.length_ofFn, List.length_cons] at *
      simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem complete_partition (m H : ℕ) (w : List Bool) (hw : w.length = H * m) :
    ∃ blocks : List (Fin m → Bool), blocks.length = H ∧ blockWord blocks = w := by
  let f : Fin (H * m) → Bool := fun i => w.get ⟨i.val, by omega⟩
  let blocks : List (Fin m → Bool) := List.ofFn (fun i : Fin H =>
    fun j : Fin m => f ⟨i.val * m + j.val, by
      have hi := i.isLt
      have hj := j.isLt
      nlinarith⟩)
  refine ⟨blocks, by simp [blocks], ?_⟩
  have hf : List.ofFn f = w := by
    apply List.ext_getElem
    · simp [hw]
    · intro i hi hi'
      simp [f]
  rw [← hf, List.ofFn_mul]
  simp only [blockWord, blocks, List.map_ofFn]
  rfl

/-- Arbitrary bounded bit tests and the original complete block tests give
exactly the same state relation, including the absorbing rejection state. -/
theorem complete_block_budget (m H : ℕ) (s t : Option (Fin k)) :
    BlockEquivalent k hk m H s t ↔ BitEquivalent k hk (H * m) s t := by
  constructor
  · intro heq w hw
    let padded := w ++ List.replicate (H * m - w.length) false
    have hp : padded.length = H * m := by simp [padded]; omega
    obtain ⟨blocks, hlen, hword⟩ := complete_partition m H padded hp
    have hr := heq blocks (by omega)
    rw [hword] at hr
    simpa only [padded, response_pad] using hr
  · intro heq blocks hlen
    apply heq
    rw [length_blockWord]
    exact Nat.mul_le_mul_right m hlen

/-- One representative of each live response class. -/
def representative (h : ℕ) (i : Fin (min k (h + 1))) : Fin k :=
  ⟨k - 1 - i.val, by have hi := i.isLt; omega⟩

private theorem coordinate_representative (h : ℕ) (i : Fin (min k (h + 1))) :
    coordinate k h (representative k hk h i) = i.val := by
  have hi := i.isLt
  simp only [coordinate, representative, Fin.val_mk]
  omega

/-- Bounded bit tests as a finite dependent family of literal words. -/
abbrev BitTest (h : ℕ) := Σ n : Fin (h + 1), Fin n.val → Bool

/-- The complete Boolean row, retaining every bounded word. -/
def row (h : ℕ) (s : Option (Fin k)) : BitTest h → Bool :=
  fun w => response k hk s (List.ofFn w.2)

private theorem row_eq_iff (h : ℕ) (s t : Option (Fin k)) :
    row k hk h s = row k hk h t ↔ BitEquivalent k hk h s t := by
  constructor
  · intro heq w hw
    have ht := congrFun heq ⟨⟨w.length, by omega⟩, w.get⟩
    simpa only [row, List.ofFn_get] using ht
  · intro heq
    funext w
    apply heq
    simp only [List.length_ofFn]
    exact Nat.le_of_lt_succ w.1.isLt

private theorem representative_rows_injective (h : ℕ) :
    Function.Injective (fun i : Fin (min k (h + 1)) =>
      row k hk h (some (representative k hk h i))) := by
  intro i j heq
  have hc := (live_response_classes k hk h _ _).mp ((row_eq_iff k hk h _ _).mp heq)
  rw [coordinate_representative, coordinate_representative] at hc
  exact Fin.ext hc

private theorem row_representative (h : ℕ) (s : Fin k) :
    row k hk h (some s) = row k hk h (some (representative k hk h
      ⟨coordinate k h s, by have hs := s.isLt; dsimp [coordinate]; omega⟩)) := by
  apply (row_eq_iff k hk h _ _).mpr
  apply (live_response_classes k hk h _ _).mpr
  rw [coordinate_representative]

/-- The number of distinct live Boolean response rows is exact. -/
theorem live_class_count (h : ℕ) :
    (Set.range (fun s : Fin k => row k hk h (some s))).ncard = min k (h + 1) := by
  have hr : Set.range (fun s : Fin k => row k hk h (some s)) =
      Set.range (fun i : Fin (min k (h + 1)) => row k hk h (some (representative k hk h i))) := by
    ext r
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨coordinate k h s, by have hs := s.isLt; dsimp [coordinate]; omega⟩,
        (row_representative k hk h s).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨representative k hk h i, rfl⟩
  rw [hr, Set.ncard_range_of_injective (representative_rows_injective k hk h)]
  simp

private theorem reject_ne_live_row (h : ℕ) (s : Fin k) :
    row k hk h none ≠ row k hk h (some s) := by
  intro heq
  have hnil := (row_eq_iff k hk h _ _).mp heq [] (by simp)
  simp only [response_nil, Option.isSome_none, Option.isSome_some] at hnil
  exact Bool.false_ne_true hnil

/-- Rejection contributes exactly one further Boolean response class. -/
theorem total_class_count (h : ℕ) :
    (Set.range (row k hk h)).ncard = min k (h + 1) + 1 := by
  have hr : Set.range (row k hk h) =
      insert (row k hk h none) (Set.range (fun s : Fin k => row k hk h (some s))) := by
    ext r
    simp only [Set.mem_range, Set.mem_insert_iff]
    constructor
    · rintro ⟨s, rfl⟩
      cases s with
      | none => exact Or.inl rfl
      | some s => exact Or.inr ⟨s, rfl⟩
    · rintro (rfl | ⟨s, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some s, rfl⟩
  rw [hr, Set.ncard_insert_of_notMem]
  · rw [live_class_count]
  · rintro ⟨s, hs⟩
    exact reject_ne_live_row k hk h s hs.symm

/-- Interpret the same legality response entries in an arbitrary field. -/
def responseMatrix (K : Type*) [Field K] (h : ℕ) :
    Matrix (Option (Fin k)) (BitTest h) K :=
  fun s w => if row k hk h s w then 1 else 0

private theorem response_minor (K : Type*) [Field K] (h : ℕ)
    (i j : Fin (min k (h + 1))) :
    responseMatrix k hk K h (some (representative k hk h i))
      ⟨⟨j.val, by have hj := j.isLt; omega⟩, fun _ => true⟩ =
      if j ≤ i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have harith : k - 1 - i.val + j.val < k ↔ j ≤ i := by
    simp only [Fin.le_iff_val_le_val]
    omega
  simp only [responseMatrix, row, List.ofFn_const, response_ones,
    representative, Fin.val_mk, harith, Bool.decide_iff]

/-- The linear response rank equals the number of live classes over every field. -/
theorem bit_response_rank (K : Type*) [Field K] (h : ℕ) :
    (responseMatrix k hk K h).rank = min k (h + 1) := by
  classical
  let b := min k (h + 1)
  let M := responseMatrix k hk K h
  let rows : Fin b → Option (Fin k) := fun i => some (representative k hk h i)
  let cols : Fin b → BitTest h := fun j =>
    ⟨⟨j.val, by have hj := j.isLt; dsimp [b] at hj; omega⟩, fun _ => true⟩
  let minor : Matrix (Fin b) (Fin b) K := M.submatrix rows cols
  have hminor : ∀ i j, minor i j = if j ≤ i then 1 else 0 := by
    intro i j
    exact response_minor k hk K h i j
  have htri : minor.IsLowerTriangular := by
    intro i j hij
    rw [hminor]
    exact if_neg (not_le.mpr hij)
  have hdet : minor.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular minor htri]
    simp [Matrix.diag, hminor]
  have hlower : b ≤ M.rank := by
    have hrank := Matrix.rank_of_det_ne_zero (by rw [hdet]; exact one_ne_zero)
    have hle := Matrix.rank_submatrix_le M rows cols
    simpa only [minor, hrank, Fintype.card_fin] using hle
  let C : Matrix (Option (Fin k)) (Fin b) K := fun s i =>
    match s with
    | none => 0
    | some s => if coordinate k h s = i.val then 1 else 0
  let R : Matrix (Fin b) (BitTest h) K := fun i w => M (rows i) w
  have hfactor : M = C * R := by
    ext s w
    cases s with
    | none =>
        change (0 : K) = ∑ j, (0 : K) * R j w
        simp
    | some s =>
        let i : Fin b := ⟨coordinate k h s, by
          have hs := s.isLt
          dsimp [b, coordinate]
          omega⟩
        have hrow := congrFun (row_representative k hk h s) w
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simpa [C, R, M, responseMatrix, rows, i] using congrArg (fun v : Bool =>
            if v then (1 : K) else 0) hrow
        · intro j _ hji
          have hne : coordinate k h s ≠ j.val := by
            intro heq
            apply hji
            exact Fin.ext heq.symm
          simp [C, hne]
        · simp
  apply Nat.le_antisymm
  · change M.rank ≤ b
    rw [hfactor]
    exact (Matrix.rank_mul_le_right C R).trans (by simpa [b] using Matrix.rank_le_card_height R)
  · exact hlower

#print axioms live_response_classes
#print axioms complete_block_budget
#print axioms live_class_count
#print axioms total_class_count
#print axioms bit_response_rank

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CompleteBlockResponses
