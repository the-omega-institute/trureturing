/- GID: D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome
   mirror-E: none(waiver:parity-obstruction-to-even-palindromes)
   anchors: []
   utility: none
   digest: Period doubling has no even palindromic factor of length at least four. -/

/-
proof_shape: content (even_palindrome_length)
escape_witness: Reflection forces zero at a position whose valuation parity is one.
admission_basis: escape-witness
Direct frozen dependencies: none; Word is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.Word

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- An even palindrome in the source word has length zero or two. -/
theorem even_palindrome_length (s k : ℕ)
    (hpal : List.Palindrome (List.ofFn (fun i : Fin (2 * k) => u_pd (s + i)))) :
    k ≤ 1 := by
  have word_val (n : ℕ) :
      u_pd n = decide (padicValNat 2 (n + 1) % 2 = 1) := by
    have hlt : n < 2 ^ (n + 1) := by
      have hn := Nat.lt_two_pow_self (n := n + 1)
      omega
    have h := (block_valuation (n + 1)).2 n hlt
    simp [u_pd, h]
  have zero_letter (n : ℕ) (hn : n % 2 = 0) : u_pd n = false := by
    rw [word_val, padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ n + 1)]
    rfl
  have one_letter (n : ℕ) (hn : n % 4 = 1) : u_pd n = true := by
    have he : n + 1 = 2 * ((n + 1) / 2) := by omega
    have ho : ¬2 ∣ (n + 1) / 2 := by omega
    have hval : padicValNat 2 (n + 1) = 1 := by
      rw [he, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega),
        padicValNat_self, padicValNat.eq_zero_of_not_dvd ho]
    simp [word_val, hval]
  by_contra hk
  have hlen : 4 ≤ 2 * k := by omega
  have reflect (i : ℕ) (hi : i < 2 * k) :
      u_pd (s + i) = u_pd (s + (2 * k - 1 - i)) := by
    let w := List.ofFn (fun t : Fin (2 * k) => u_pd (s + t))
    have he : w.reverse = w := hpal.reverse_eq
    have hw : i < w.length := by simpa [w] using hi
    have hwr : i < w.reverse.length := by simpa using hw
    have hv : w.reverse[i] = w[i] := by simp only [he]
    rw [List.getElem_reverse] at hv
    simpa [w] using hv.symm
  have choose : ∃ i : ℕ, i < 4 ∧ (s + i) % 4 = 1 := by
    refine ⟨(5 - s % 4) % 4, ?_, ?_⟩
    · omega
    · have hs := Nat.mod_lt s (by decide : (0 : ℕ) < 4)
      omega
  obtain ⟨i, hi, hmod⟩ := choose
  have hleft : u_pd (s + i) = true := one_letter _ hmod
  have hright : u_pd (s + (2 * k - 1 - i)) = false :=
    zero_letter _ (by omega)
  have he := reflect i (by omega)
  rw [hleft, hright] at he
  cases he

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.even_palindrome_length
