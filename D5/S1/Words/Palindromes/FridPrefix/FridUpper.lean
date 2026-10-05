/- GID: D5/S1/Words/Palindromes/FridPrefix/FridUpper
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/FridUpper
   mirror-E: none(waiver:explicit-palindromic-factorisation)
   anchors: []
   utility: none
   digest: Symmetric central-word trims factor every Frid prefix into at most 2k+1 palindromes. -/

/-
proof_shape: content (frid_upper).
escape_witness: increasing symmetric cuts and induction on their palindrome factorisations.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S0/Tower/GoldenGapWord.fibWord
    statement_id: sha256:cdb325ce53ff53959ea3b3de305df2d88f1d96e3874184a481eab5e31ab99105
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Words/GoldenFactorComplexity.goldenFactor
    statement_id: sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
  D5/S1/Words/GoldenWord.fibWord_length
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_length
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_palindrome
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Powers/WordPower.length_wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower_succ
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.PalindromicLength
import D5.S1.Words.Palindromes.FridPrefix.FridNumerals
import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.Palindromes.GoldenPalindromicPrefix

namespace D5.S1.Words.FridPrefix

open D5.S0.Tower.GoldenGapWord D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Words.Powers

/-- Two initial letters and consecutive symmetric trims give Frid's upper bound. -/
theorem frid_upper (k : ℕ) (hk : 1 ≤ k) : PL (goldenFactor (N k) 0) ≤ 2*k+1 := by
  classical
  have append_le (u v : List Bool) : PL (u ++ v) ≤ PL u + PL v := by
    classical
    obtain ⟨ps, hps, hlenps, hp⟩ : PalFactors u (PL u) := by
      unfold PL
      exact Nat.find_spec _
    obtain ⟨qs, hqs, hlenqs, hq⟩ : PalFactors v (PL v) := by
      unfold PL
      exact Nat.find_spec _
    apply Nat.find_le (show PalFactors (u ++ v) (PL u + PL v) from ?_)
    refine ⟨ps ++ qs, by simp [hps, hqs], by simp [hlenps, hlenqs], ?_⟩
    intro p h
    rcases List.mem_append.mp h with h | h
    · exact hp p h
    · exact hq p h
  let z (m : ℕ) := (fibPair (wordPower m [1,0,0] ++ [1,0,1])).1
  let correction (m : ℕ) := if Even m then 2 else 0
  let cut (m : ℕ) := z m - correction m
  have z_zero : z 0 = 4 := by norm_num [z, wordPower, fibPair, Nat.fib]
  have z_succ (m : ℕ) : z (m+1) = Nat.fib (3*m+7) + z m := by
    dsimp [z]
    rw [wordPower_succ]
    simp only [List.cons_append, List.nil_append, fibPair,
      List.length_cons, List.length_append, length_wordPower]
    norm_num
    congr 1
    omega
  have z_lower (m : ℕ) : 4 ≤ z m := by
    induction m with
    | zero => omega
    | succ m ih => rw [z_succ]; omega
  have z_pair (m : ℕ) : z m + z (m+1) = Nat.fib (3*m+8) := by
    have ht := frid_numeral_twice m
    have hs := z_succ m
    have hf := Nat.fib_add_two (n := 3*m+6)
    norm_num only [Nat.add_assoc] at hf
    change 2*z m = _ at ht
    omega
  have correction_le (m : ℕ) : correction m ≤ 2 := by dsimp [correction]; split <;> omega
  have correction_pair (m : ℕ) : correction m + correction (m+1) = 2 := by
    by_cases h : Even m <;> simp [correction, Nat.even_add_one, h]
  have cut_pair (m : ℕ) : cut m + cut (m+1) = Nat.fib (3*m+8)-2 := by
    have hz0 := z_lower m
    have hz1 := z_lower (m+1)
    have hc0 := correction_le m
    have hc1 := correction_le (m+1)
    have hcp := correction_pair m
    have hzp := z_pair m
    dsimp [cut]
    omega
  have cut_lt (m : ℕ) : cut m < cut (m+1) := by
    have hzl := z_lower m
    have hzs := z_succ m
    have hc0 := correction_le m
    have hc1 := correction_le (m+1)
    have hf : 13 ≤ Nat.fib (3*m+7) := by
      have hm := Nat.fib_mono (show 7 ≤ 3*m+7 by omega)
      norm_num [Nat.fib] at hm
      exact hm
    dsimp [cut]
    omega
  have prefix_take (n m : ℕ) (hn : n ≤ m) :
      (goldenFactor m 0).take n = goldenFactor n 0 := by
    apply List.ext_getElem
    · simp [goldenFactor, hn]
    · intro i hi hj
      simp [goldenFactor]
  have core_prefix (Q : ℕ) (hQ : 1 ≤ Q) :
      fibPalCore Q = goldenFactor (Nat.fib (Q+2)-2) 0 := by
    apply List.ext_getElem
    · simp [fibPalCore_length Q hQ, goldenFactor]
    · intro i hi hj
      have hiword : i < (fibWord Q).length := by
        rw [fibWord_length]
        rw [fibPalCore_length Q hQ] at hi
        omega
      simp only [fibPalCore, List.getElem_take, goldenFactor, List.getElem_ofFn,
        Nat.zero_add]
      exact (goldenWord_eq_fibWord_get Q i hiword).symm
  have palindrome_trim {w : List Bool} (hp : List.Palindrome w) (a : ℕ)
      (ha : 2*a ≤ w.length) : List.Palindrome ((w.drop a).take (w.length-2*a)) := by
    apply List.Palindrome.of_reverse_eq
    rw [List.reverse_take, List.length_drop, List.reverse_drop, hp.reverse_eq]
    have hn : w.length-a-(w.length-2*a)=a := by omega
    rw [hn, List.drop_take]
    congr 1
    omega
  have factor_pal (m : ℕ) :
      List.Palindrome ((goldenFactor (cut (m+1)) 0).drop (cut m)) := by
    let Q := 3*m+6
    let a := cut m
    let b := cut (m+1)
    have hlen : (fibPalCore Q).length = a+b := by
      rw [fibPalCore_length Q (by dsimp [Q]; omega)]
      exact (cut_pair m).symm
    have hab : a ≤ b := (cut_lt m).le
    have hsize : Nat.fib (Q+2)-2 = a+b := by
      rw [← hlen, fibPalCore_length Q (by dsimp [Q]; omega)]
    have hpref : goldenFactor b 0 = (fibPalCore Q).take b := by
      rw [core_prefix Q (by dsimp [Q]; omega)]
      exact (prefix_take b _ (by omega)).symm
    have hpal := palindrome_trim (fibPalCore_palindrome Q (by dsimp [Q]; omega)) a
      (by omega)
    rw [hlen, show a+b-2*a=b-a by omega] at hpal
    change List.Palindrome ((goldenFactor b 0).drop a)
    rw [hpref, List.drop_take]
    exact hpal
  have pal_le {w : List Bool} (hw : List.Palindrome w) : PL w ≤ 1 := by
    by_cases he : w = []
    · subst w
      have h0 : PL ([] : List Bool) ≤ 0 :=
        Nat.find_le (show PalFactors ([] : List Bool) 0 from ⟨[], rfl, rfl, by simp⟩)
      omega
    · exact Nat.find_le (show PalFactors w 1 from
        ⟨[w], by simp, rfl, by simpa using And.intro he hw⟩)
  have cut_upper (m : ℕ) : PL (goldenFactor (cut m) 0) ≤ m+2 := by
    induction m with
    | zero =>
      have hc : cut 0 = 2 := by simp [cut, correction, z_zero]
      rw [hc]
      have hw : goldenFactor 2 0 = [true] ++ [false] := by decide
      rw [hw]
      have ha := append_le [true] [false]
      have h0 := pal_le (List.Palindrome.singleton true)
      have h1 := pal_le (List.Palindrome.singleton false)
      omega
    | succ m ih =>
      have hstep : goldenFactor (cut (m+1)) 0 = goldenFactor (cut m) 0 ++
          (goldenFactor (cut (m+1)) 0).drop (cut m) := by
        rw [← prefix_take (cut m) (cut (m+1)) (cut_lt m).le, List.take_append_drop]
      rw [hstep]
      have hf := pal_le (factor_pal m)
      have ha := append_le (goldenFactor (cut m) 0)
        ((goldenFactor (cut (m+1)) 0).drop (cut m))
      omega
  have ho : Odd (2*k-1) := ⟨k-1, by omega⟩
  have hc : cut (2*k-1) = N k := by
    simp [cut, correction, Nat.not_even_iff_odd.mpr ho, N, z]
  have hu := cut_upper (2*k-1)
  rw [hc] at hu
  omega

end D5.S1.Words.FridPrefix
