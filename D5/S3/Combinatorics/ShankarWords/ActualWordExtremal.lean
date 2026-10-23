/- GID: D5/S3/Combinatorics/ShankarWords/ActualWordExtremal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ShankarWords/ActualWordExtremal
   mirror-E: none(waiver:open-structural-word-classification)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Actual even lattice-word construction and the open extremal fiber law. -/

import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

/-- The prefix inequalities include the empty and whole prefixes. -/
def IsLattice (w : List ℕ) : Prop :=
  ∀ i : Fin (w.length + 1),
    (w.take i.val).count 2 ≤ (w.take i.val).count 1 ∧
    (w.take i.val).count 3 ≤ (w.take i.val).count 2

/-- Avoidance is of a subsequence, with three strictly increasing positions. -/
def Avoids321 (w : List ℕ) : Prop :=
  ∀ i j l : Fin w.length, i < j → j < l →
    ¬ (w.get i = 3 ∧ w.get j = 2 ∧ w.get l = 1)

/-- Shankar's original word conditions, with the literal letters 1, 2 and 3. -/
def IsAdmissible (k : ℕ) (w : List ℕ) : Prop :=
  w.length = 3 * k ∧
    (∀ a ∈ w, 1 ≤ a ∧ a ≤ 3) ∧
    w.count 1 = k ∧ w.count 2 = k ∧ w.count 3 = k ∧
    IsLattice w ∧ Avoids321 w

/-- Enumerate every length-3k word over 1,2,3 via the order-preserving Fin 3 encoding. -/
def rawWords (k : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (fun f : Fin (3 * k) → Fin 3 =>
    List.ofFn (fun i => (f i).val + 1))

/-- This carrier uses the actual word predicates, without a refined-count identity. -/
def actualWords (k : ℕ) : Finset (List ℕ) := by
  letI : DecidablePred (IsAdmissible k) := fun w => by
    unfold IsAdmissible IsLattice Avoids321
    infer_instance
  exact
  (rawWords k).filter (IsAdmissible k)

/-- Strict adjacent descents; neither inversions nor subsequence descents are counted. -/
def descents (w : List ℕ) : ℕ :=
  ((w.zip w.tail).filter (fun p => p.2 < p.1)).length

/-- The proposed extremal value, using natural-number division and subtraction. -/
def extremalValue (k : ℕ) : ℕ := 3 * k / 2 - 1

/-- The actual-word fiber over the proposed extremal value. -/
def topFiber (k : ℕ) : Finset (List ℕ) :=
  (actualWords k).filter (fun w => descents w = extremalValue k)

/-- The exact unproved structural obligation; no hypothesis assumes a counting formula. -/
def extremalLaw : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (∀ w ∈ actualWords k, descents w ≤ extremalValue k) ∧
      (topFiber k).card = if k % 2 = 0 then 1 else 2 * k

/-- Repeated two-letter blocks, with no shared or duplicated boundary letter. -/
def pairBlocks (a b n : ℕ) : List ℕ := (List.replicate n [a, b]).flatten

/-- Even construction for k=2t. Global maximality and uniqueness remain open. -/
def evenWord (t : ℕ) : List ℕ :=
  pairBlocks 1 2 t ++ pairBlocks 1 3 t ++ pairBlocks 2 3 t

/-- Descending-pair base for the odd words with an extra unpaired 1. -/
def oddOneBase (t : ℕ) : List ℕ :=
  pairBlocks 2 1 t ++ pairBlocks 3 1 (t - 1) ++ pairBlocks 3 2 (t + 1)

/-- Insert the unpaired 1 at a boundary among the first 2t descending pairs. -/
def oddOneWord (t : ℕ) (q : Fin (2 * t)) : List ℕ :=
  [1] ++ (oddOneBase t).take (2 * q.val) ++ [1] ++
    (oddOneBase t).drop (2 * q.val) ++ [3]

/-- Reverse and complement the literal alphabet; this is a word operation, not an assumed law. -/
def reverseComplement (w : List ℕ) : List ℕ := w.reverse.map (fun a => 4 - a)

/-- The two proposed odd words with an extra unpaired 2. -/
def oddTwoWord (t : ℕ) (late : Bool) : List ℕ :=
  [1] ++ pairBlocks 2 1 t ++
    (if late then pairBlocks 3 1 t ++ [2] else [2] ++ pairBlocks 3 1 t) ++
    pairBlocks 3 2 t ++ [3]

/-- Two families of size 2t and two singleton candidates. -/
abbrev OddIndex (t : ℕ) := (Fin (2 * t) ⊕ Fin (2 * t)) ⊕ Bool

/-- Explicit proposed classifier; its actual-word bijection is the missing proof obligation. -/
def oddWord (t : ℕ) : OddIndex t → List ℕ
  | .inl (.inl q) => oddOneWord t q
  | .inl (.inr q) => reverseComplement (oddOneWord t q)
  | .inr late => oddTwoWord t late

/-- Candidate words are kept separate from the actual carrier. -/
def oddCandidates (t : ℕ) : Finset (List ℕ) := Finset.univ.image (oddWord t)


/-- The explicit even family consists of actual lattice words at the proposed descent level. -/
theorem even_word_construction (t : ℕ) (ht : 1 ≤ t) :
    evenWord t ∈ actualWords (2 * t) ∧
      descents (evenWord t) = extremalValue (2 * t) := by
  classical
  have pair_zero (a b : ℕ) : pairBlocks a b 0 = [] := by
    simp [pairBlocks]
  have pair_succ (a b n : ℕ) :
      pairBlocks a b (n + 1) = a :: b :: pairBlocks a b n := by
    simp [pairBlocks, List.replicate_succ]
  have pair_len (a b n : ℕ) : (pairBlocks a b n).length = 2 * n := by
    simp [pairBlocks, Nat.mul_comm]
  have pair_mem (a b n c : ℕ) (hc : c ∈ pairBlocks a b n) : c = a ∨ c = b := by
    exact (by simpa [pairBlocks] using hc : n ≠ 0 ∧ (c = a ∨ c = b)).2
  have pair_count (a b c n : ℕ) :
      (pairBlocks a b n).count c = n * (([a, b] : List ℕ).count c) := by
    simp [pairBlocks, List.count_flatten]
  have pair_prefix (a b n m : ℕ) (hab : a ≠ b) :
      ((pairBlocks a b n).take m).count a = min n ((m + 1) / 2) ∧
      ((pairBlocks a b n).take m).count b = min n (m / 2) := by
    induction n generalizing m with
    | zero => simp [pair_zero]
    | succ n ih =>
      cases m with
      | zero => simp
      | succ m =>
        cases m with
        | zero => simp [pair_succ, hab]
        | succ m =>
          obtain ⟨ha, hb⟩ := ih m
          simp only [pair_succ, List.take_succ_cons, List.count_cons_self,
            List.count_cons_of_ne hab, List.count_cons_of_ne (Ne.symm hab)]
          constructor <;> omega
  have prefix_absent (a b c n m : ℕ) (hca : c ≠ a) (hcb : c ≠ b) :
      ((pairBlocks a b n).take m).count c = 0 := by
    apply List.count_eq_zero.mpr
    intro hc
    have hm := List.mem_of_mem_take hc
    rcases pair_mem a b n c hm with h | h <;> contradiction
  have hlen : (evenWord t).length = 3 * (2 * t) := by
    simp [evenWord, pair_len]; omega
  have halphabet : ∀ a ∈ evenWord t, 1 ≤ a ∧ a ≤ 3 := by
    intro a ha
    simp only [evenWord, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · rcases pair_mem 1 2 t a ha with rfl | rfl <;> omega
    · rcases pair_mem 1 3 t a ha with rfl | rfl <;> omega
    · rcases pair_mem 2 3 t a ha with rfl | rfl <;> omega
  have hcounts : (evenWord t).count 1 = 2 * t ∧
      (evenWord t).count 2 = 2 * t ∧ (evenWord t).count 3 = 2 * t := by
    simp [evenWord, pair_count]
    omega
  have hlattice : IsLattice (evenWord t) := by
    intro i
    obtain ⟨h12a, h12b⟩ := pair_prefix 1 2 t i.val (by decide)
    obtain ⟨h13a, h13b⟩ := pair_prefix 1 3 t (i.val - 2 * t) (by decide)
    obtain ⟨h23a, h23b⟩ := pair_prefix 2 3 t (i.val - 4 * t) (by decide)
    have hz12 := prefix_absent 1 2 3 t i.val (by decide) (by decide)
    have hz13 := prefix_absent 1 3 2 t (i.val - 2 * t) (by decide) (by decide)
    have hz23 := prefix_absent 2 3 1 t (i.val - 4 * t) (by decide) (by decide)
    simp only [evenWord, List.take_append, List.length_append, pair_len,
      List.count_append] at *
    simp only [show 2 * t + 2 * t = 4 * t by omega,
      h12a, h12b, h13a, h13b, h23a, h23b, hz12, hz13, hz23]
    constructor <;> omega
  have havoid : Avoids321 (evenWord t) := by
    intro i j k hij hjk hbad
    obtain ⟨hi, hj, hk⟩ := hbad
    change (evenWord t)[i.val] = 3 at hi
    change (evenWord t)[j.val] = 2 at hj
    change (evenWord t)[k.val] = 1 at hk
    have hi0 : 2 * t ≤ i.val := by
      by_contra h
      have hil : i.val < (pairBlocks 1 2 t).length := by rw [pair_len]; omega
      have he : (evenWord t)[i.val] = (pairBlocks 1 2 t)[i.val] := by
        simp only [evenWord, List.append_assoc]
        rw [List.getElem_append_left hil]
      have hm := pair_mem 1 2 t 3 (List.mem_of_getElem (he.symm.trans hi))
      omega
    have hj0 : 4 * t ≤ j.val := by
      by_contra h
      have hj1 : 2 * t ≤ j.val := by change i.val < j.val at hij; omega
      have hjl : j.val - 2 * t < (pairBlocks 1 3 t).length := by rw [pair_len]; omega
      have he : (evenWord t)[j.val] = (pairBlocks 1 3 t)[j.val - 2 * t] := by
        simp only [evenWord, List.append_assoc]
        rw [List.getElem_append_right (by rw [pair_len]; omega)]
        simp only [pair_len]
        rw [List.getElem_append_left hjl]
      have hm := pair_mem 1 3 t 2 (List.mem_of_getElem (he.symm.trans hj))
      omega
    have hkl : k.val - 4 * t < (pairBlocks 2 3 t).length := by
      have hh := k.isLt
      rw [pair_len]; omega
    have he : (evenWord t)[k.val] = (pairBlocks 2 3 t)[k.val - 4 * t] := by
      simp only [evenWord]
      rw [List.getElem_append_right (by simp [pair_len]; change j.val < k.val at hjk; omega)]
      simp only [List.length_append, pair_len]
      congr 1; omega
    have hm := pair_mem 2 3 t 1 (List.mem_of_getElem (he.symm.trans hk))
    omega
  have hraw : evenWord t ∈ rawWords (2 * t) := by
    let f : Fin (3 * (2 * t)) → Fin 3 := fun i =>
      ⟨(evenWord t)[i.val]'(by rw [hlen]; exact i.isLt) - 1, by
        have h := halphabet _ (List.getElem_mem (by rw [hlen]; exact i.isLt))
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    rw [← List.ofFn_get (evenWord t)]
    rw [List.ofFn_congr hlen]
    apply congrArg List.ofFn
    funext i
    dsimp [f]
    have h := halphabet _ (List.getElem_mem (by rw [hlen]; exact i.isLt))
    omega
  have hdesc_cons (a b : ℕ) (v : List ℕ) :
      descents (a :: b :: v) = (if b < a then 1 else 0) + descents (b :: v) := by
    simp [descents, List.zip_cons_cons, List.filter_cons]
    split <;> simp_all <;> omega
  have hdesc_pair (a b n : ℕ) (hab : a < b) :
      descents (pairBlocks a b (n + 1)) = n := by
    induction n with
    | zero => simp [pair_succ, pair_zero, descents, Nat.not_lt.mpr (Nat.le_of_lt hab)]
    | succ n ih =>
      rw [pair_succ, hdesc_cons, pair_succ, hdesc_cons]
      simp only [if_neg (by omega : ¬ b < a), if_pos hab, zero_add]
      rw [← pair_succ, ih]
      omega
  have hdesc_prefix (a b c n : ℕ) (v : List ℕ) (hab : a < b) :
      descents (pairBlocks a b (n + 1) ++ c :: v) =
        n + (if c < b then 1 else 0) + descents (c :: v) := by
    induction n with
    | zero => simp [pair_succ, pair_zero, hdesc_cons, Nat.not_lt.mpr (Nat.le_of_lt hab)]
    | succ n ih =>
      rw [pair_succ]
      simp only [List.cons_append]
      rw [hdesc_cons, pair_succ]
      simp only [List.cons_append]
      rw [hdesc_cons]
      simp only [if_neg (by omega : ¬ b < a), if_pos hab, zero_add]
      rw [← List.cons_append, ← List.cons_append, ← pair_succ, ih]
      omega
  have hd : descents (evenWord t) = 3 * t - 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    simp only [evenWord, List.append_assoc]
    rw [pair_succ 1 3, pair_succ 2 3]
    simp only [List.cons_append]
    rw [hdesc_prefix 1 2 1 n _ (by decide)]
    rw [← List.cons_append, ← List.cons_append, ← pair_succ]
    rw [hdesc_prefix 1 3 2 n _ (by decide)]
    rw [← pair_succ, hdesc_pair 2 3 n (by decide)]
    simp only [if_pos (by decide : (1 : ℕ) < 2), if_pos (by decide : (2 : ℕ) < 3)]
    omega
  constructor
  · simpa only [actualWords, Finset.mem_filter] using
      (show evenWord t ∈ rawWords (2 * t) ∧ IsAdmissible (2 * t) (evenWord t) from
        ⟨hraw, hlen, halphabet, hcounts.1, hcounts.2.1, hcounts.2.2, hlattice, havoid⟩)
  · unfold extremalValue
    omega

#print axioms even_word_construction

end D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
