/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PalindromicLength
   mirror-E: none(waiver:general-palindromic-factorization-argument)
   anchors: []
   utility: none
   digest: Every nonempty word has an optimal final palindromic suffix cut. -/

/-
proof_shape: content (optimal_suffix_cut, suffix_cut_lower_bound)
escape_witness: Extracting an optimal last factor; well-founded propagation along all suffix cuts.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.PalindromicLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

open D5.S1.Words.FridPrefix (PL PalFactors)

/-- Some final palindromic suffix realizes the exact minimum cut recurrence. -/
theorem optimal_suffix_cut {α : Type*} (w : List α) (hw : w ≠ []) :
    ∃ j : ℕ, j < w.length ∧ List.Palindrome (w.drop j) ∧
      PL w = PL (w.take j) + 1 := by
  classical
  have minimal (v : List α) : PalFactors v (PL v) := by
    unfold PL
    exact Nat.find_spec _
  have bound {v : List α} {k : ℕ} (h : PalFactors v k) : PL v ≤ k :=
    Nat.find_le h
  obtain ⟨ps, hps, hlen, hp⟩ := minimal w
  cases ps using List.reverseRecOn with
  | nil => simp only [List.flatten_nil] at hps; exact (hw hps.symm).elim
  | append_singleton qs p _ =>
    have hpal := hp p (by simp)
    have hwconcat : w = qs.flatten ++ p := by
      simpa using hps.symm
    have hpre : PalFactors qs.flatten qs.length :=
      ⟨qs, rfl, rfl, fun q hq => hp q (by simp [hq])⟩
    have hlenp : 0 < p.length := List.length_pos_iff.mpr hpal.1
    refine ⟨qs.flatten.length, ?_, ?_, ?_⟩
    · rw [hwconcat, List.length_append]
      omega

    · simpa [hwconcat] using hpal.2
    · have htake : w.take qs.flatten.length = qs.flatten := by
        simp [hwconcat]
      rw [htake]
      have hlower := bound hpre
      have hcount : PL w = qs.length + 1 := by simpa using hlen.symm
      obtain ⟨rs, hrs, hrlen, hrpal⟩ := minimal qs.flatten
      have hupper : PL w ≤ PL qs.flatten + 1 := by
        apply bound
        refine ⟨rs ++ [p], ?_, ?_, ?_⟩
        · simpa [hrs] using hwconcat.symm
        · simp [hrlen]
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hrpal q hq
          · simpa using List.mem_singleton.mp hq ▸ hpal
      omega

/-- A lower potential valid on every palindromic suffix cut bounds the true optimum. -/
theorem suffix_cut_lower_bound {α : Type*} (w : List α) (B : ℕ → ℕ)
    (hzero : B 0 = 0)
    (hstep : ∀ n : ℕ, n ≤ w.length → ∀ j : ℕ, j < n →
      List.Palindrome ((w.take n).drop j) → B n ≤ B j + 1) :
    ∀ n : ℕ, n ≤ w.length → B n ≤ PL (w.take n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h : n = 0
    · subst n
      rw [hzero]
      exact Nat.zero_le _
    · have hlen : (w.take n).length = n := List.length_take_of_le hn
      have hne : w.take n ≠ [] := by
        intro he
        have he' := congrArg List.length he
        rw [hlen, List.length_nil] at he'
        exact h he'
      obtain ⟨j, hj, hpal, heq⟩ := optimal_suffix_cut (w.take n) hne
      rw [hlen] at hj
      have hlow := ih j hj (by omega)
      have hcost := hstep n hn j hj hpal
      have htake : (w.take n).take j = w.take j := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      rw [htake] at heq
      omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.optimal_suffix_cut
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.suffix_cut_lower_bound
