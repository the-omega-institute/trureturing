/- GID: D5/S1/Digit/EqualBinaryRunBridge
   generality: I
   mirror-B: D5/B/S1/Digit/EqualBinaryRunBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal maximal binary run pairs and their positive block encoding. -/

import D5.S1.Words.DoubleTailShuffleSupport
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.SplitBy
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The source is OEIS A386705, with the literal integer set used for its sum.
Binary words here are most significant digit first. No recurrence defines a.
The theorem full_claim proves the three initial values and the integer recurrence.
-/

set_option autoImplicit false

namespace D5.S1.Digit.EqualBinaryRunBridge

/-- Canonical binary representation, most significant digit first. -/
def bits (m : ℕ) : List ℕ := (Nat.digits 2 m).reverse

/-- Maximal one runs and zero runs alternate, in equally long pairs.
Nonemptiness of each run is supplied by splitBy in the literal predicate. -/
def Matched : List (List ℕ) → Prop
  | [] => True
  | o :: z :: rest => (∀ d ∈ o, d = 1) ∧ (∀ d ∈ z, d = 0) ∧
      o.length = z.length ∧ Matched rest
  | [_] => False

/-- Literal membership in the positive even integers in source row n. -/
def Literal (n m : ℕ) : Prop :=
  0 < m ∧ Even m ∧ (bits m).length = 2 * n ∧
    Matched ((bits m).splitBy (· == ·))

noncomputable instance (n m : ℕ) : Decidable (Literal n m) := Classical.propDecidable _

/-- A finite set of integers, so each integer is included only once. -/
noncomputable def row (n : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (2 * n))).filter (Literal n)

/-- The source sum is evaluated in the integers. -/
noncomputable def a (n : ℕ) : ℤ := ∑ m ∈ row n, (m : ℤ)

/-- The complete source endpoint for the literal distinct-integer sum. -/
def FullClaim : Prop :=
  a 1 = 2 ∧ a 2 = 22 ∧ a 3 = 192 ∧
    ∀ n : ℕ, 4 ≤ n → a n = 12 * a (n - 1) - 36 * a (n - 2) + 32 * a (n - 3)

/-- The ordered run list associated with proposed positive part lengths. -/
def blockRuns : List ℕ → List (List ℕ)
  | [] => []
  | k :: ks => List.replicate k 1 :: List.replicate k 0 :: blockRuns ks

/-- Concatenate the actual one-zero blocks; this is a word, not a recurrence. -/
def word (ks : List ℕ) : List ℕ := (blockRuns ks).flatten

private theorem blockRuns_head (ks : List ℕ) :
    ∀ r ∈ (blockRuns ks).head?, ∀ d ∈ r, d = 1 := by
  cases ks with
  | nil => simp [blockRuns]
  | cons k ks => simp [blockRuns]

/-- The proposed blocks are precisely the maximal runs, without merging. -/
private theorem splitBy_word (ks : List ℕ) (h : ∀ k ∈ ks, 0 < k) :
    (word ks).splitBy (· == ·) = blockRuns ks := by
  unfold word
  apply List.splitBy_flatten
  · induction ks with
    | nil => simp [blockRuns]
    | cons k ks ih =>
        have hk := h k (by simp)
        have ht : ∀ j ∈ ks, 0 < j := fun j hj => h j (by simp [hj])
        simp [blockRuns, hk.ne', ih ht]
  · intro r hr
    have hc : ∀ js : List ℕ, ∀ r ∈ blockRuns js, ∃ k d, r = List.replicate k d := by
      intro js
      induction js with
      | nil => simp [blockRuns]
      | cons k ks ih =>
          intro r hr
          simp only [blockRuns, List.mem_cons] at hr
          rcases hr with rfl | rfl | hr
          · exact ⟨k, 1, rfl⟩
          · exact ⟨k, 0, rfl⟩
          · exact ih r hr
    obtain ⟨k, d, rfl⟩ := hc ks r hr
    exact List.isChain_replicate_of_rel k (by simp)
  · induction ks with
    | nil => simp [blockRuns]
    | cons k ks ih =>
        have hk := h k (by simp)
        have ht : ∀ j ∈ ks, 0 < j := fun j hj => h j (by simp [hj])
        rw [blockRuns, List.isChain_cons_cons]
        refine ⟨?_, ?_⟩
        · exact ⟨by simpa using hk.ne', by simpa using hk.ne', by simp⟩
        · rw [List.isChain_cons]
          refine ⟨?_, ih ht⟩
          intro r hr
          have hrn : r ≠ [] := by
            cases ks with
            | nil => simp [blockRuns] at hr
            | cons j js =>
                have hj := ht j (by simp)
                have he : List.replicate j 1 = r := by simpa [blockRuns] using hr
                rw [← he]
                simpa using hj.ne'
          refine ⟨by simpa using hk.ne', hrn, ?_⟩
          have hd := blockRuns_head ks r hr (r.head hrn) (List.head_mem hrn)
          simp [hd]

private theorem matched_iff (rs : List (List ℕ)) (hne : [] ∉ rs) :
    Matched rs ↔ ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ rs = blockRuns ks := by
  induction rs using List.twoStepInduction with
  | nil =>
      simp only [Matched, true_iff]
      exact ⟨[], by simp, rfl⟩
  | singleton r =>
      simp only [Matched, false_iff, not_exists, not_and]
      intro ks hk he
      cases ks <;> simp [blockRuns] at he
  | cons_cons o z rs ih =>
      have ho : o ≠ [] := fun he => hne (by simp [he])
      have hz : z ≠ [] := fun he => hne (by simp [he])
      have ht : [] ∉ rs := fun he => hne (by simp [he])
      constructor
      · rintro ⟨hone, hzero, hlen, hm⟩
        obtain ⟨ks, hk, he⟩ := (ih ht).mp hm
        refine ⟨o.length :: ks, ?_, ?_⟩
        · simpa using And.intro (List.length_pos_iff.mpr ho) hk
        · have heo : o = List.replicate o.length 1 := List.eq_replicate_of_mem hone
          have hez : z = List.replicate o.length 0 := by
            rw [hlen]; exact List.eq_replicate_of_mem hzero
          rw [blockRuns]
          exact congrArg₂ List.cons heo (congrArg₂ List.cons hez he)
      · rintro ⟨ks, hk, he⟩
        cases ks with
        | nil => simp [blockRuns] at he
        | cons k ks =>
            simp only [blockRuns, List.cons.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            refine ⟨by simp, by simp, by simp, ?_⟩
            exact (ih ht).mpr ⟨ks, fun j hj => hk j (by simp [hj]), rfl⟩

private theorem length_word (ks : List ℕ) : (word ks).length = 2 * ks.sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      change (List.replicate k 1 ++ (List.replicate k 0 ++ word ks)).length =
        2 * (k + ks.sum)
      simp only [List.length_append, List.length_replicate, ih]
      omega

/-- Every literal row member has, and is characterized by, a positive-part word.
The positivity and evenness clauses remain explicit on both sides. -/
private theorem literal_iff (n m : ℕ) : Literal n m ↔
    0 < m ∧ Even m ∧ ∃ ks : List ℕ,
      (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ bits m = word ks := by
  constructor
  · rintro ⟨hp, he, hl, hm⟩
    obtain ⟨ks, hk, hr⟩ := (matched_iff _ (List.nil_notMem_splitBy _ _)).mp hm
    have hw : bits m = word ks := by
      rw [word, ← hr, List.flatten_splitBy]
    refine ⟨hp, he, ks, hk, ?_, hw⟩
    rw [hw, length_word] at hl
    omega
  · rintro ⟨hp, he, ks, hk, hs, hw⟩
    refine ⟨hp, he, ?_, ?_⟩
    · rw [hw, length_word, hs]
    · rw [hw, splitBy_word ks hk]
      exact (matched_iff _ (by
        rw [← splitBy_word ks hk]; exact List.nil_notMem_splitBy _ _)).mpr ⟨ks, hk, rfl⟩

private theorem blockRuns_injective : Function.Injective blockRuns := by
  intro ks ls
  induction ks generalizing ls with
  | nil => cases ls <;> simp [blockRuns]
  | cons k ks ih =>
      cases ls with
      | nil => simp [blockRuns]
      | cons j js =>
          intro he
          simp only [blockRuns, List.cons.injEq] at he
          have hk := congrArg List.length he.1
          simp only [List.length_replicate] at hk
          subst j
          exact congrArg (List.cons k) (ih he.2.2)

private theorem word_injective (ks ls : List ℕ)
    (hk : ∀ k ∈ ks, 0 < k) (hl : ∀ k ∈ ls, 0 < k)
    (he : word ks = word ls) : ks = ls := by
  apply blockRuns_injective
  rw [← splitBy_word ks hk, he, splitBy_word ls hl]

/-- Literal distinct-integer membership has a unique positive-part encoding.
No composition count or sum over encodings is assumed in this statement. -/
theorem mem_row_iff (n m : ℕ) : m ∈ row n ↔
    0 < m ∧ Even m ∧ ∃! ks : List ℕ,
      (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ bits m = word ks := by
  classical
  have hrow : m ∈ row n ↔ Literal n m := by
    simp only [row, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hm
      refine ⟨?_, hm⟩
      have hb := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2)
        (fun d hd => Nat.digits_lt_base (by decide : 1 < 2) hd :
          ∀ d ∈ Nat.digits 2 m, d < 2)
      rw [Nat.ofDigits_digits] at hb
      have hl : (Nat.digits 2 m).length = 2 * n := by
        simpa [bits] using hm.2.2.1
      rwa [hl] at hb
  rw [hrow, literal_iff]
  constructor
  · rintro ⟨hp, he, ks, hk, hs, hw⟩
    refine ⟨hp, he, ks, ⟨hk, hs, hw⟩, ?_⟩
    intro ls hl
    exact word_injective ls ks hl.1 hk (hl.2.2.symm.trans hw)
  · rintro ⟨hp, he, ks, hk, _⟩
    exact ⟨hp, he, ks, hk⟩

/-- Decode the concatenated blocks as a binary integer. -/
private def decode (ks : List ℕ) : ℕ := Nat.ofDigits 2 (word ks).reverse

private theorem word_cons (k : ℕ) (ks : List ℕ) :
    word (k :: ks) = List.replicate k 1 ++ List.replicate k 0 ++ word ks := by
  simp [word, blockRuns, List.append_assoc]

private theorem word_digits (ks : List ℕ) : ∀ d ∈ word ks, d < 2 := by
  induction ks with
  | nil => simp [word, blockRuns]
  | cons k ks ih =>
      intro d hd
      simp only [word_cons, List.mem_append] at hd
      rcases hd with (hd | hd) | hd
      · simp only [List.mem_replicate] at hd; omega
      · simp only [List.mem_replicate] at hd; omega
      · exact ih d hd

private theorem word_starts (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k) (hne : ks ≠ []) :
    ∃ ws, word ks = 1 :: ws := by
  cases ks with
  | nil => contradiction
  | cons k ks =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hk k (by simp)).ne'
      simp [word_cons, List.replicate_succ]

private theorem word_ends (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k) (hne : ks ≠ []) :
    ∃ ws, word ks = ws ++ [0] := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
      by_cases he : ks = []
      · subst ks
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hk k (by simp)).ne'
        exact ⟨List.replicate (j+1) 1 ++ List.replicate j 0, by
          simp [word, blockRuns, List.replicate_succ', List.append_assoc]⟩
      · obtain ⟨ws, hw⟩ := ih (fun j hj => hk j (by simp [hj])) he
        exact ⟨List.replicate k 1 ++ List.replicate k 0 ++ ws, by
          simp [word_cons, hw, List.append_assoc]⟩

private theorem bits_decode (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k) :
    bits (decode ks) = word ks := by
  by_cases he : ks = []
  · subst ks; simp [decode, bits, word, blockRuns]
  obtain ⟨ws, hw⟩ := word_starts ks hk he
  unfold bits decode
  rw [Nat.digits_ofDigits 2 (by decide)]
  · simp
  · intro d hd
    exact word_digits ks d (List.mem_reverse.mp hd)
  · intro hn
    simp [hw]

private theorem decode_pos_even (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k) (hne : ks ≠ []) :
    0 < decode ks ∧ Even (decode ks) := by
  constructor
  · have hw := bits_decode ks hk
    obtain ⟨ws, hs⟩ := word_starts ks hk hne
    by_contra hn
    have hz : decode ks = 0 := by omega
    rw [hz, hs] at hw
    simp [bits] at hw
  · obtain ⟨ws, hw⟩ := word_ends ks hk hne
    unfold decode
    rw [hw, List.reverse_append]
    exact ⟨Nat.ofDigits 2 ws.reverse, by simp [Nat.ofDigits_cons]; omega⟩

private noncomputable def parts (n : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (Composition.blocks : Composition n → List ℕ)

private theorem mem_parts (n : ℕ) (ks : List ℕ) : ks ∈ parts n ↔
    (∀ k ∈ ks, 0 < k) ∧ ks.sum = n := by
  classical
  simp only [parts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun k hk => c.blocks_pos hk, c.blocks_sum⟩
  · rintro ⟨hk, hs⟩
    exact ⟨⟨ks, fun {k} h => hk k h, hs⟩, rfl⟩

private theorem parts_nonempty_list (n : ℕ) (hn : 0 < n) (ks : List ℕ)
    (hk : ks ∈ parts n) : ks ≠ [] := by
  have hs := (mem_parts n ks).mp hk
  rintro rfl
  simp at hs
  omega

private theorem row_eq_image (n : ℕ) (hn : 0 < n) : row n = (parts n).image decode := by
  classical
  ext m
  rw [mem_row_iff, Finset.mem_image]
  constructor
  · rintro ⟨_, _, ks, ⟨hk, hs, hb⟩, _⟩
    refine ⟨ks, (mem_parts n ks).mpr ⟨hk, hs⟩, ?_⟩
    unfold decode
    rw [← hb]
    simp [bits, Nat.ofDigits_digits]
  · rintro ⟨ks, hk, rfl⟩
    obtain ⟨hp, he⟩ := decode_pos_even ks ((mem_parts n ks).mp hk).1
      (parts_nonempty_list n hn ks hk)
    refine ⟨hp, he, ks, ⟨((mem_parts n ks).mp hk).1,
      ((mem_parts n ks).mp hk).2, bits_decode ks ((mem_parts n ks).mp hk).1⟩, ?_⟩
    intro ls hl
    exact word_injective ls ks hl.1 ((mem_parts n ks).mp hk).1
      (hl.2.2.symm.trans (bits_decode ks ((mem_parts n ks).mp hk).1))

private theorem sum_transport (n : ℕ) (hn : 0 < n) :
    a n = ∑ ks ∈ parts n, (decode ks : ℤ) := by
  classical
  rw [a, row_eq_image n hn, Finset.sum_image]
  intro ks hk ls hl he
  apply word_injective ks ls ((mem_parts n ks).mp hk).1 ((mem_parts n ls).mp hl).1
  rw [← bits_decode ks ((mem_parts n ks).mp hk).1,
    ← bits_decode ls ((mem_parts n ls).mp hl).1, he]

/-- Increment the first part, keeping all remaining parts. -/
private def grow : List ℕ → List ℕ
  | [] => []
  | k :: ks => (k+1) :: ks

private theorem grow_injective : Function.Injective grow := by
  intro ks ls he
  cases ks <;> cases ls <;> simp_all [grow]

private theorem parts_succ (n : ℕ) (hn : 0 < n) :
    parts (n+1) = (parts n).image (List.cons 1) ∪ (parts n).image grow := by
  classical
  ext ks
  simp only [Finset.mem_union, Finset.mem_image, mem_parts]
  constructor
  · rintro ⟨hk, hs⟩
    cases ks with
    | nil => simp at hs
    | cons k ks =>
        have hkp := hk k (by simp)
        have hks : ∀ j ∈ ks, 0 < j := fun j hj => hk j (by simp [hj])
        by_cases he : k = 1
        · subst k
          exact Or.inl ⟨ks, ⟨hks, by simp only [List.sum_cons] at hs; omega⟩, rfl⟩
        · right
          refine ⟨(k-1)::ks, ⟨?_, ?_⟩, ?_⟩
          · simp only [List.mem_cons, forall_eq_or_imp]
            exact ⟨by omega, hks⟩
          · simp only [List.sum_cons] at hs ⊢
            omega
          · simp only [grow, List.cons.injEq]
            exact ⟨by omega, trivial⟩
  · rintro (⟨ls, ⟨hl, hs⟩, rfl⟩ | ⟨ls, ⟨hl, hs⟩, rfl⟩)
    · exact ⟨by simpa using And.intro (by decide : 0 < 1) hl, by simp [hs, Nat.add_comm]⟩
    · cases ls with
      | nil => simp only [List.sum_nil] at hs; omega
      | cons k ls =>
          constructor
          · simp only [grow, List.mem_cons, forall_eq_or_imp]
            exact ⟨by omega, fun j hj => hl j (by simp [hj])⟩
          · simp only [grow, List.sum_cons] at hs ⊢
            omega

private theorem parts_images_disjoint (n : ℕ) (hn : 0 < n) :
    Disjoint ((parts n).image (List.cons 1)) ((parts n).image grow) := by
  classical
  apply Finset.disjoint_left.mpr
  intro ks hk hl
  obtain ⟨xs, hx, he⟩ := Finset.mem_image.mp hk
  obtain ⟨ys, hy, hf⟩ := Finset.mem_image.mp hl
  have hne := parts_nonempty_list n hn ys hy
  cases ys with
  | nil => contradiction
  | cons k ys =>
      have hp := ((mem_parts n (k::ys)).mp hy).1 k (by simp)
      have hh := he.trans hf.symm
      simp only [grow, List.cons.injEq] at hh
      omega

private theorem sum_parts_succ (n : ℕ) (hn : 0 < n) (f : List ℕ → ℤ) :
    ∑ ks ∈ parts (n+1), f ks =
      (∑ ks ∈ parts n, f (1::ks)) + ∑ ks ∈ parts n, f (grow ks) := by
  classical
  rw [parts_succ n hn, Finset.sum_union (parts_images_disjoint n hn),
    Finset.sum_image, Finset.sum_image]
  · intro a ha b hb he
    exact grow_injective he
  · intro a ha b hb he
    exact List.cons.inj he |>.2

private theorem parts_card (n : ℕ) : (parts n).card = 2 ^ (n-1) := by
  classical
  rw [parts, Finset.card_image_of_injective, Finset.card_univ, composition_card]
  intro c d h
  exact Composition.ext h

private def value (ks : List ℕ) : ℤ := (decode ks : ℤ)

private def tailValue (ks : List ℕ) : ℤ := value ks.tail

private def edge (ks : List ℕ) : ℤ := 2 ^ ks.headD 0 * 4 ^ ks.tail.sum

private noncomputable def total (n : ℕ) : ℤ := ∑ ks ∈ parts n, value ks

private noncomputable def tailTotal (n : ℕ) : ℤ := ∑ ks ∈ parts n, tailValue ks

private noncomputable def edgeTotal (n : ℕ) : ℤ := ∑ ks ∈ parts n, edge ks

private def capacity (n : ℕ) : ℤ := 4 ^ n * 2 ^ (n-1)

private theorem value_cons (k : ℕ) (ks : List ℕ) :
    value (k::ks) = (4 ^ k - 2 ^ k) * 4 ^ ks.sum + value ks := by
  have hon := congrArg (fun m : ℕ => (m : ℤ))
    (D5.S1.Words.DoubleTailShuffleSupport.ones_value k)
  push_cast at hon
  have hones : Nat.ofDigits (2 : ℤ) (List.replicate k 1) = 2 ^ k - 1 := by
    linarith
  unfold value decode
  simp only [word_cons, List.reverse_append, List.reverse_replicate]
  rw [Nat.ofDigits_append, Nat.ofDigits_append]
  simp only [List.length_reverse, List.length_replicate, length_word,
    Nat.ofDigits_replicate_zero, zero_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.coe_ofDigits, hones]
  have hp (r : ℕ) : (2 : ℤ) ^ (2*r) = 4 ^ r := by
    rw [pow_mul]; norm_num
  rw [hp]
  have hq : (2 : ℤ) ^ k * 2 ^ k = 4 ^ k := by
    rw [← pow_add, ← two_mul, hp]
  rw [mul_sub, hq, mul_one]
  ring

private theorem capacity_succ (n : ℕ) (hn : 0 < n) :
    capacity (n+1) = 8 * capacity n := by
  have he : n+1-1 = (n-1)+1 := by omega
  simp only [capacity, he, pow_succ]
  ring

private theorem value_grow (ks : List ℕ) (hne : ks ≠ []) :
    value (grow ks) = 4 * value ks + 2 * edge ks - 3 * tailValue ks := by
  cases ks with
  | nil => contradiction
  | cons k ks =>
      simp only [grow, value_cons, edge, tailValue, List.headD_cons, List.tail_cons, pow_succ]
      ring

private theorem tailValue_grow (ks : List ℕ) : tailValue (grow ks) = tailValue ks := by
  cases ks <;> rfl

private theorem edge_grow (ks : List ℕ) (hne : ks ≠ []) : edge (grow ks) = 2 * edge ks := by
  cases ks with
  | nil => contradiction
  | cons k ks => simp [edge, grow, pow_succ]; ring

private theorem sum_constant (n : ℕ) (c : ℤ) :
    (∑ _ks ∈ parts n, c) = 2 ^ (n-1) * c := by
  classical
  simp [parts_card]

private theorem total_succ (n : ℕ) (hn : 0 < n) :
    total (n+1) = 5 * total n + 2 * capacity n + 2 * edgeTotal n - 3 * tailTotal n := by
  classical
  have hpre : (∑ ks ∈ parts n, value (1::ks)) = 2 * capacity n + total n := by
    calc
      _ = ∑ ks ∈ parts n, (2 * 4^n + value ks) := by
        apply Finset.sum_congr rfl
        intro ks hk
        rw [value_cons, ((mem_parts n ks).mp hk).2]
        norm_num
      _ = _ := by rw [Finset.sum_add_distrib, sum_constant]; dsimp [capacity, total]; ring
  have hgrow : (∑ ks ∈ parts n, value (grow ks)) =
      4 * total n + 2 * edgeTotal n - 3 * tailTotal n := by
    calc
      _ = ∑ ks ∈ parts n, (4 * value ks + 2 * edge ks - 3 * tailValue ks) := by
        apply Finset.sum_congr rfl
        intro ks hk
        exact value_grow ks (parts_nonempty_list n hn ks hk)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          total, edgeTotal, tailTotal]
  rw [total, sum_parts_succ n hn, hpre, hgrow]
  ring

private theorem tailTotal_succ (n : ℕ) (hn : 0 < n) :
    tailTotal (n+1) = total n + tailTotal n := by
  classical
  rw [tailTotal, sum_parts_succ n hn]
  simp only [tailValue_grow]
  rfl

private theorem edgeTotal_succ (n : ℕ) (hn : 0 < n) :
    edgeTotal (n+1) = 2 * capacity n + 2 * edgeTotal n := by
  classical
  have hpre : (∑ ks ∈ parts n, edge (1::ks)) = 2 * capacity n := by
    calc
      _ = ∑ _ks ∈ parts n, ((2 : ℤ) * 4^n) := by
        apply Finset.sum_congr rfl
        intro ks hk
        simp [edge, ((mem_parts n ks).mp hk).2]
      _ = _ := by rw [sum_constant]; dsimp [capacity]; ring
  have hgrow : (∑ ks ∈ parts n, edge (grow ks)) = 2 * edgeTotal n := by
    calc
      _ = ∑ ks ∈ parts n, 2 * edge ks := by
        apply Finset.sum_congr rfl
        intro ks hk
        exact edge_grow ks (parts_nonempty_list n hn ks hk)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  rw [edgeTotal, sum_parts_succ n hn, hpre, hgrow]

private theorem parts_one : parts 1 = {[1]} := by
  classical
  obtain ⟨ks, hks⟩ := Finset.card_eq_one.mp (show (parts 1).card = 1 by
    simpa using parts_card 1)
  have hm : [1] ∈ parts 1 := (mem_parts 1 [1]).mpr ⟨by simp, by simp⟩
  rw [hks, Finset.mem_singleton] at hm
  simpa [← hm] using hks

private theorem totals_one : total 1 = 2 ∧ tailTotal 1 = 0 ∧ edgeTotal 1 = 2 := by
  classical
  norm_num [total, tailTotal, edgeTotal, parts_one, tailValue, edge, value,
    decode, word, blockRuns, Nat.ofDigits]

private theorem weighted_balance (n : ℕ) (hn : 0 < n) :
    total n - tailTotal n + edgeTotal n = capacity n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : n = 0
      · subst n
        norm_num [totals_one.1, totals_one.2.1, totals_one.2.2, capacity]
      · have hp : 0 < n := by omega
        have hi := ih hp
        rw [total_succ n hp, tailTotal_succ n hp, edgeTotal_succ n hp,
          capacity_succ n hp]
        linarith

private theorem total_step (n : ℕ) (hn : 0 < n) :
    total (n+1) = 2 * total n - edgeTotal n + 5 * capacity n := by
  have hw := weighted_balance n hn
  rw [total_succ n hn]
  linarith

private theorem total_recurrence (n : ℕ) (hn : 0 < n) :
    total (n+3) = 12 * total (n+2) - 36 * total (n+1) + 32 * total n := by
  have hn1 : 0 < n+1 := by omega
  have hn2 : 0 < n+2 := by omega
  have h0 := total_step n hn
  have h1 := total_step (n+1) hn1
  have h2 := total_step (n+2) hn2
  have e0 := edgeTotal_succ n hn
  have e1 := edgeTotal_succ (n+1) hn1
  have c0 := capacity_succ n hn
  have c1 := capacity_succ (n+1) hn1
  convert h2 using 1 <;> try omega
  linarith

/-- The complete literal distinct-integer sum recurrence of OEIS A386705. -/
theorem full_claim : FullClaim := by
  have ha (n : ℕ) (hn : 0 < n) : a n = total n := sum_transport n hn
  have h2 : total 2 = 22 := by
    have ht := total_step 1 (by decide)
    norm_num [totals_one.1, totals_one.2.2, capacity] at ht
    exact ht
  have h3 : total 3 = 192 := by
    have ht := total_step 2 (by decide)
    have he := edgeTotal_succ 1 (by decide)
    norm_num [totals_one.2.2, capacity] at he
    norm_num [h2, he, capacity] at ht
    exact ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha 1 (by decide)]; exact totals_one.1
  · rw [ha 2 (by decide)]; exact h2
  · rw [ha 3 (by decide)]; exact h3
  · intro n hn
    have h0 : 0 < n := by omega
    have h1 : 0 < n-1 := by omega
    have h2 : 0 < n-2 := by omega
    have h3 : 0 < n-3 := by omega
    rw [ha n h0, ha (n-1) h1, ha (n-2) h2, ha (n-3) h3]
    have hr := total_recurrence (n-3) h3
    have he0 : n-3+3 = n := by omega
    have he1 : n-3+2 = n-1 := by omega
    have he2 : n-3+1 = n-2 := by omega
    simpa only [he0, he1, he2] using hr

end D5.S1.Digit.EqualBinaryRunBridge
