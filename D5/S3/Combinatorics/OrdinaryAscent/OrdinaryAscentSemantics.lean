/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics
   mirror-E: none(waiver:literal-ascent-sequence-structure)
   anchors: [mathlib/module/Mathlib.Data.Set.Finite.List]
   utility: none
   digest: Literal vincular avoidance, ordinary ascent sequences and their one-letter extensions. -/

import D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation
import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

/-! The ordinary strict-ascent and literal adjacent-pair conventions are those of
Haobo Ma and Wenlin Zhang, *Ten Wilf classes, two pair equivalences and a Catalan
bijection for ascent sequences*, revision 3, supplied under CC BY 4.0. The questions
are credited there to Toufik Mansour. No transfer from weak or modified ascent
sequences is used. `asc` is the existing strict adjacent-ascent count. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentSemantics

open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)
open D5.S3.Combinatorics.InversionSeq.InversionSeqDefs (IsInversionSeq)

/-- All reduced length-three patterns with the first two positions adjacent. -/
inductive Pattern where
  | p000 | p001 | p010 | p011 | p012 | p021 | p100
  | p101 | p102 | p110 | p120 | p201 | p210
  deriving DecidableEq

/-- The equalities and strict inequalities in the literal pattern. -/
def Fits : Pattern → ℕ → ℕ → ℕ → Prop
  | .p000, x, y, z => x = y ∧ y = z
  | .p001, x, y, z => x = y ∧ y < z
  | .p010, x, y, z => x = z ∧ x < y
  | .p011, x, y, z => x < y ∧ y = z
  | .p012, x, y, z => x < y ∧ y < z
  | .p021, x, y, z => x < z ∧ z < y
  | .p100, x, y, z => y = z ∧ y < x
  | .p101, x, y, z => x = z ∧ y < x
  | .p102, x, y, z => y < x ∧ x < z
  | .p110, x, y, z => x = y ∧ z < x
  | .p120, x, y, z => z < x ∧ x < y
  | .p201, x, y, z => y < z ∧ z < x
  | .p210, x, y, z => z < y ∧ y < x

instance (p : Pattern) (x y z : ℕ) : Decidable (Fits p x y z) := by
  cases p <;> unfold Fits <;> infer_instance

/-- A literal occurrence at positions `i,i+1,k`, with `i+1<k`. -/
def Contains (p : Pattern) (w : List ℕ) : Prop :=
  ∃ i k, i + 1 < k ∧ k < w.length ∧
    Fits p (w.getD i 0) (w.getD (i + 1) 0) (w.getD k 0)

/-- Ordinary nonnegative ascent sequences, including the empty word. -/
def IsAscent (w : List ℕ) : Prop :=
  ∀ i < w.length, w.getD i 0 ≤ if i = 0 then 0 else 1 + asc (w.take i)

/-- The actual length-`n` ordinary ascent sequences avoiding every pattern in `B`. -/
def avoiders (n : ℕ) (B : Finset Pattern) : Set (List ℕ) :=
  {w | w.length = n ∧ IsAscent w ∧ ∀ p ∈ B, ¬ Contains p w}

/-- Primitive means unequal adjacent letters, without a distinctness-of-values condition. -/
def Primitive (w : List ℕ) : Prop := w.IsChain (· ≠ ·)

theorem contains_append_iff (p : Pattern) (w : List ℕ) (x : ℕ) :
    Contains p (w ++ [x]) ↔ Contains p w ∨
      ∃ i, i + 1 < w.length ∧ Fits p (w.getD i 0) (w.getD (i + 1) 0) x := by
  constructor
  · rintro ⟨i, k, hik, hk, hfit⟩
    have hi : i < w.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    have hi1 : i + 1 < w.length := by
      simp only [List.length_append, List.length_singleton] at hk
      omega
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi1] at hfit
    by_cases hkw : k < w.length
    · left
      rw [List.getD_append _ _ _ _ hkw] at hfit
      exact ⟨i, k, hik, hkw, hfit⟩
    · right
      have heq : k = w.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst k
      simpa using (show ∃ i, i + 1 < w.length ∧
        Fits p (w.getD i 0) (w.getD (i + 1) 0) ((w ++ [x]).getD w.length 0)
        from ⟨i, hi1, hfit⟩)
  · rintro (⟨i, k, hik, hk, hfit⟩ | ⟨i, hi, hfit⟩)
    · refine ⟨i, k, hik, by simp; omega, ?_⟩
      simpa only [List.getD_append _ _ _ _ (show i < w.length by omega),
        List.getD_append _ _ _ _ (show i + 1 < w.length by omega),
        List.getD_append _ _ _ _ hk] using hfit
    · refine ⟨i, w.length, hi, by simp, ?_⟩
      rw [List.getD_append _ _ _ _ (show i < w.length by omega),
        List.getD_append _ _ _ _ hi]
      simpa using hfit

theorem ascent_take (w : List ℕ) (h : IsAscent w) (n : ℕ) :
    IsAscent (w.take n) := by
  intro i hi
  have hil : i < w.length := by simp only [List.length_take] at hi; omega
  have hin : i < n := by simp only [List.length_take] at hi; omega
  have hb := h i hil
  rw [List.getD_eq_getElem _ _ hil] at hb
  rw [List.getD_eq_getElem _ _ hi, List.getElem_take]
  simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hin)] using hb

theorem ascent_append_iff (w : List ℕ) (x : ℕ) :
    IsAscent (w ++ [x]) ↔ IsAscent w ∧
      x ≤ if w = [] then 0 else 1 + asc w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have ht := ascent_take (w ++ [x]) h w.length
      simpa using ht
    · have hx := h w.length (by simp)
      simpa [List.length_eq_zero_iff] using hx
  · rintro ⟨hw, hx⟩ i hi
    by_cases hil : i < w.length
    · rw [List.getD_append _ _ _ _ hil, List.take_append_of_le_length (Nat.le_of_lt hil)]
      exact hw i hil
    · have heq : i = w.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simpa [List.length_eq_zero_iff] using hx

theorem asc_le (w : List ℕ) : asc w ≤ w.length - 1 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

/-- Appending a letter changes the existing strict-ascent count only at the new boundary. -/
theorem asc_append (w : List ℕ) (x : ℕ) :
    asc (w ++ [x]) = asc w +
      if w = [] then 0 else if w.getD (w.length - 1) 0 < x then 1 else 0 := by
  by_cases he : w = []
  · subst w
    simp [asc]
  · have hp : 0 < w.length := List.length_pos_iff.mpr he
    have hs : w.length - 1 + 1 = w.length := by omega
    have hf :
        ((Finset.range (w.length - 1)).filter (fun i =>
          (w ++ [x]).getD i 0 < (w ++ [x]).getD (i + 1) 0)) =
        ((Finset.range (w.length - 1)).filter (fun i =>
          w.getD i 0 < w.getD (i + 1) 0)) := by
      apply Finset.filter_congr
      intro i hi
      have hir := Finset.mem_range.mp hi
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    have hb : (w ++ [x]).getD (w.length - 1) 0 <
        (w ++ [x]).getD (w.length - 1 + 1) 0 ↔ w.getD (w.length - 1) 0 < x := by
      rw [List.getD_append _ _ _ _ (by omega), hs]
      simp
    unfold asc
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    have hr : Finset.range w.length =
        insert (w.length - 1) (Finset.range (w.length - 1)) := by
      simpa only [hs] using (Finset.range_add_one (n := w.length - 1))
    rw [hr, Finset.filter_insert, hf]
    simp only [hb, if_neg he]
    have hn : w.length - 1 ∉ ((Finset.range (w.length - 1)).filter
        (fun i => w.getD i 0 < w.getD (i + 1) 0)) := by simp
    split_ifs <;> simp only [Finset.card_insert_of_notMem hn, Nat.add_zero]

/-- Every letter is bounded by the total number of strict ascents, not merely by length. -/
theorem entry_le_asc (w : List ℕ) (ha : IsAscent w) :
    ∀ i < w.length, w.getD i 0 ≤ asc w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    obtain ⟨hw, hx⟩ := (ascent_append_iff w x).mp ha
    have hcount := asc_append w x
    intro i hi
    by_cases hil : i < w.length
    · rw [List.getD_append _ _ _ _ hil]
      have hb := ih hw i hil
      split_ifs at hcount <;> omega
    · have heq : i = w.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
        List.getD_cons_zero]
      by_cases he : w = []
      · subst w
        simpa [asc] using hx
      · have hp : 0 < w.length := List.length_pos_iff.mpr he
        have hl := ih hw (w.length - 1) (by omega)
        simp only [if_neg he] at hx hcount
        split_ifs at hcount with hlt
        · omega
        · omega

theorem ascent_isInversionSeq (w : List ℕ) (h : IsAscent w) : IsInversionSeq w := by
  intro i hi
  have hb := h i hi
  have hc := asc_le (w.take i)
  have hlen : (w.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  rw [hlen] at hc
  split_ifs at hb with hz
  · omega
  · omega

theorem avoiders_finite (n : ℕ) (B : Finset Pattern) : (avoiders n B).Finite := by
  classical
  let decode : (Fin n → Fin (n + 1)) → List ℕ := fun f => List.ofFn (fun i => (f i).val)
  apply (Set.finite_range decode).subset
  intro w hw
  obtain ⟨hlen, ha, _⟩ := hw
  have hb := ascent_isInversionSeq w ha
  let encode : Fin n → Fin (n + 1) := fun i =>
    ⟨w.getD i.val 0, by have hi := hb i.val (by omega); omega⟩
  refine ⟨encode, ?_⟩
  apply List.ext_getElem
  · simp [decode, hlen]
  · intro i hi hj
    simp only [decode, List.getElem_ofFn]
    exact List.getD_eq_getElem w 0 hj

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentSemantics
