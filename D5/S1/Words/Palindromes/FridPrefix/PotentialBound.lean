/- GID: D5/S1/Words/Palindromes/FridPrefix/PotentialBound
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/PotentialBound
   mirror-E: none(waiver:palindrome-path-induction)
   anchors: []
   utility: none
   digest: Every unit-gain potential bounds the literal palindromic length of golden prefixes. -/

/-
proof_shape: content (potential_pl_bound).
escape_witness: induction over the actual nonempty palindrome factors and their numeric cuts.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S1/Words/GoldenFactorComplexity; module statement_id sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
    D5/S1/Words/GoldenFactorComplexity.goldenFactor: sha256:45653c076830e3d013ea9e728d954ed6444072d1161a1656d45e0c92ab921ed8
  D5/S1/Words/GoldenWord; module statement_id sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
    D5/S1/Words/GoldenWord.goldenWord: sha256:8f1246e0f7522a641bfb80a0177aa34160f096f22a06c1e4b8b73d07921da29b
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.PalindromicLength
import D5.S1.Words.GoldenFactorComplexity

namespace D5.S1.Words.FridPrefix

/-- A potential whose gain on each actual palindrome is at most one bounds PL. -/
theorem potential_pl_bound (S : ℕ → ℤ) (hz : S 0 = 0) (n : ℕ)
    (he : ∀ i j : ℕ, i < j → j ≤ n → List.Palindrome (goldenFactor (j-i) i) →
      S j ≤ S i + 1) : S n ≤ (PL (goldenFactor n 0) : ℤ) := by
  classical
  have take_segment (i j t : ℕ) (ht : i+t ≤ j) :
      (goldenFactor (j-i) i).take t = goldenFactor t i := by
    apply List.ext_getElem
    · simp [goldenFactor]; omega
    · intro r hr hr'
      simp [goldenFactor]
  have drop_segment (i j t : ℕ) :
      (goldenFactor (j-i) i).drop t = goldenFactor (j-(i+t)) (i+t) := by
    apply List.ext_getElem
    · simp [goldenFactor]; omega
    · intro r hr hr'
      simp [goldenFactor, Nat.add_assoc, Nat.add_left_comm]
  have factors_bound (ps : List (List Bool)) (i j : ℕ) (hij : i ≤ j)
      (hjn : j ≤ n) (hword : ps.flatten = goldenFactor (j-i) i)
      (hpal : ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p) :
      S j ≤ S i + (ps.length : ℤ) := by
    induction ps generalizing i with
    | nil =>
      have hl := congrArg List.length hword
      simp only [List.flatten_nil, List.length_nil, goldenFactor, List.length_ofFn] at hl
      have hj : j = i := by omega
      simp [hj]
    | cons p ps ih =>
      simp only [List.flatten_cons] at hword
      have hp := hpal p (by simp)
      have hpos : 0 < p.length := List.length_pos_iff.mpr hp.1
      have hl := congrArg List.length hword
      simp only [List.length_append, goldenFactor, List.length_ofFn] at hl
      have hnext : i+p.length ≤ j := by omega
      have hfirst : goldenFactor p.length i = p := by
        have ht := congrArg (List.take p.length) hword
        rw [List.take_left, take_segment i j p.length hnext] at ht
        exact ht.symm
      have hrest : ps.flatten = goldenFactor (j-(i+p.length)) (i+p.length) := by
        have ht := congrArg (List.drop p.length) hword
        simpa only [List.drop_left, drop_segment] using ht
      have hed := he i (i+p.length) (by omega) (by omega)
        (by rw [show i+p.length-i=p.length by omega, hfirst]; exact hp.2)
      have htail := ih (i+p.length) hnext hrest (fun q hq => hpal q (by simp [hq]))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega
  obtain ⟨ps, hword, hlen, hpal⟩ : PalFactors (goldenFactor n 0)
      (PL (goldenFactor n 0)) := by
    unfold PL
    exact Nat.find_spec _
  have hb := factors_bound ps 0 n (by omega) (le_refl _) (by simpa using hword) hpal
  simpa only [hz, zero_add, hlen] using hb

end D5.S1.Words.FridPrefix
