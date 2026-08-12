/- GID: D5/S1/Words/Palindromes/PalindromicFactors
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:kernel-decide-readout-is-contained-in-this-formal-module)
   anchors: []
   digest: A finite word has at most its length plus one distinct palindromic factors. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Palindrome
import Mathlib.Tactic

namespace D5.S1.Words

/-- The finite set of distinct palindromic contiguous factors of a word. -/
def palindromicFactors {alpha : Type*} [DecidableEq alpha] (w : List alpha) :
    Finset (List alpha) :=
  ((w.tails.flatMap List.inits).filter fun u => decide (List.Palindrome u)).toFinset

private example : (palindromicFactors [true, false, true]).card = 4 := by decide

/-- Membership in `palindromicFactors` is exactly palindromic infix occurrence. -/
theorem mem_palindromicFactors {alpha : Type*} [DecidableEq alpha]
    {w u : List alpha} :
    u ∈ palindromicFactors w ↔ u <:+: w ∧ List.Palindrome u := by
  simp only [palindromicFactors, List.mem_toFinset, List.mem_filter,
    List.mem_flatMap, List.mem_tails, List.mem_inits, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v, hv, hu⟩, hpal⟩
    rcases hv with ⟨l, rfl⟩
    rcases hu with ⟨r, rfl⟩
    exact ⟨⟨l, r, by simp [List.append_assoc]⟩, hpal⟩
  · rintro ⟨⟨l, r, rfl⟩, hpal⟩
    refine ⟨⟨u ++ r, ?_, ?_⟩, hpal⟩
    · exact ⟨l, by simp [List.append_assoc]⟩
    · exact ⟨r, rfl⟩

private theorem palindromicFactors_mono_of_infix {alpha : Type*} [DecidableEq alpha]
    {u v : List alpha} (h : u <:+: v) : palindromicFactors u ⊆ palindromicFactors v := by
  intro p hp
  rw [mem_palindromicFactors] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

private theorem infix_of_append_singleton_eq_append_append_cons {alpha : Type*}
    {w u l r : List alpha} {a b : alpha}
    (h : l ++ u ++ b :: r = w ++ [a]) : u <:+: w := by
  have hpref : l ++ u <+: w ++ [a] := by
    refine ⟨b :: r, ?_⟩
    simpa [List.append_assoc] using h
  have hlength := congrArg List.length h
  have hle : (l ++ u).length ≤ w.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
    omega
  have hpref' : l ++ u <+: w :=
    (List.isPrefix_append_of_length hle).mp hpref
  rcases hpref' with ⟨s, hs⟩
  exact ⟨l, s, by simpa [List.append_assoc] using hs⟩

private theorem infix_append_singleton_old_or_suffix {alpha : Type*}
    {w u : List alpha} {a : alpha} (h : u <:+: w ++ [a]) :
    u <:+: w ∨ u <:+ w ++ [a] := by
  rcases h with ⟨l, r, h⟩
  cases r with
  | nil =>
      right
      exact ⟨l, by simpa using h⟩
  | cons b r =>
      left
      exact infix_of_append_singleton_eq_append_append_cons h

private theorem suffix_of_suffix_of_length_le {alpha : Type*}
    {p q z : List alpha} (hp : p <:+ z) (hq : q <:+ z)
    (hlength : p.length ≤ q.length) : p <:+ q := by
  have hple := hp.length_le
  have hqle := hq.length_le
  apply List.suffix_iff_eq_drop.mpr
  calc
    p = z.drop (z.length - p.length) := List.suffix_iff_eq_drop.mp hp
    _ = z.drop ((z.length - q.length) + (q.length - p.length)) := by
      congr 1
      omega
    _ = (z.drop (z.length - q.length)).drop (q.length - p.length) := by
      rw [List.drop_drop]
    _ = q.drop (q.length - p.length) := by
      rw [← List.suffix_iff_eq_drop.mp hq]

private theorem prefix_of_palindromic_suffix {alpha : Type*}
    {p q : List alpha} (hp : List.Palindrome p) (hq : List.Palindrome q)
    (h : p <:+ q) : p <+: q := by
  have hreverse := h.reverse
  rw [hp.reverse_eq, hq.reverse_eq] at hreverse
  exact hreverse

private theorem palindromicFactors_append_sdiff_card_le_one {alpha : Type*}
    [DecidableEq alpha] (w : List alpha) (a : alpha) :
    ((palindromicFactors (w ++ [a])) \ palindromicFactors w).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  rw [Finset.mem_sdiff] at hp hq
  have hpnew := mem_palindromicFactors.mp hp.1
  have hqnew := mem_palindromicFactors.mp hq.1
  have hpsuffix : p <:+ w ++ [a] := by
    rcases infix_append_singleton_old_or_suffix hpnew.1 with hold | hsuffix
    · exact (hp.2 (mem_palindromicFactors.mpr ⟨hold, hpnew.2⟩)).elim
    · exact hsuffix
  have hqsuffix : q <:+ w ++ [a] := by
    rcases infix_append_singleton_old_or_suffix hqnew.1 with hold | hsuffix
    · exact (hq.2 (mem_palindromicFactors.mpr ⟨hold, hqnew.2⟩)).elim
    · exact hsuffix
  rcases le_total p.length q.length with hpq | hqp
  · have hprefix : p <+: q :=
      prefix_of_palindromic_suffix hpnew.2 hqnew.2
        (suffix_of_suffix_of_length_le hpsuffix hqsuffix hpq)
    by_cases hlength : p.length = q.length
    · exact hprefix.eq_of_length hlength
    · rcases hprefix with ⟨t, ht⟩
      have htne : t ≠ [] := by
        intro htzero
        subst t
        apply hlength
        simpa using congrArg List.length ht
      rcases t with _ | ⟨b, r⟩
      · exact (htne rfl).elim
      · apply (hp.2 (mem_palindromicFactors.mpr ⟨?_, hpnew.2⟩)).elim
        rcases hqsuffix with ⟨l, hl⟩
        apply infix_of_append_singleton_eq_append_append_cons
        calc
          l ++ p ++ b :: r = l ++ q := by
            simpa [List.append_assoc] using congrArg (fun x => l ++ x) ht
          _ = w ++ [a] := hl
  · symm
    have hprefix : q <+: p :=
      prefix_of_palindromic_suffix hqnew.2 hpnew.2
        (suffix_of_suffix_of_length_le hqsuffix hpsuffix hqp)
    by_cases hlength : q.length = p.length
    · exact hprefix.eq_of_length hlength
    · rcases hprefix with ⟨t, ht⟩
      have htne : t ≠ [] := by
        intro htzero
        subst t
        apply hlength
        simpa using congrArg List.length ht
      rcases t with _ | ⟨b, r⟩
      · exact (htne rfl).elim
      · apply (hq.2 (mem_palindromicFactors.mpr ⟨?_, hqnew.2⟩)).elim
        rcases hpsuffix with ⟨l, hl⟩
        apply infix_of_append_singleton_eq_append_append_cons
        calc
          l ++ q ++ b :: r = l ++ p := by
            simpa [List.append_assoc] using congrArg (fun x => l ++ x) ht
          _ = w ++ [a] := hl

/-- A finite word has at most `length + 1` distinct palindromic factors. -/
theorem palindromicFactors_card_le_length_add_one {alpha : Type*}
    [DecidableEq alpha] (w : List alpha) :
    (palindromicFactors w).card ≤ w.length + 1 := by
  induction w using List.reverseRec with
  | nil =>
      have hempty : palindromicFactors ([] : List alpha) = {[]} := by
        ext u
        rw [Finset.mem_singleton, mem_palindromicFactors]
        constructor
        · rintro ⟨hinfix, _⟩
          simpa using hinfix.length_le
        · intro hu
          subst u
          exact ⟨⟨[], [], rfl⟩, List.Palindrome.nil⟩
      rw [hempty]
      simp
  | append_singleton w a ih =>
      have hsubset : palindromicFactors w ⊆ palindromicFactors (w ++ [a]) :=
        palindromicFactors_mono_of_infix (List.IsPrefix.isInfix (List.prefix_append w [a]))
      have hcard := Finset.card_sdiff_add_card_eq_card hsubset
      have hnew := palindromicFactors_append_sdiff_card_le_one w a
      simp only [List.length_append, List.length_singleton]
      omega

#print axioms mem_palindromicFactors
#print axioms palindromicFactors_card_le_length_add_one

end D5.S1.Words
