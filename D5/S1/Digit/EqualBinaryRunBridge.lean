/- GID: D5/S1/Digit/EqualBinaryRunBridge
   generality: G
   mirror-B: D5/B/S1/Digit/EqualBinaryRunBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal maximal binary run pairs and their positive block encoding. -/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.SplitBy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The source is OEIS A386705, with the literal integer set used for its sum.
Binary words here are most significant digit first. No recurrence defines a.
The recurrence claim is a target proposition, not an established theorem.
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

/-- The complete source endpoint. This definition asserts no proof. -/
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

end D5.S1.Digit.EqualBinaryRunBridge
