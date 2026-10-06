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
  D5/S0/Tower/GoldenGapWord; module statement_id sha256:cdb325ce53ff53959ea3b3de305df2d88f1d96e3874184a481eab5e31ab99105
    D5/S0/Tower/GoldenGapWord.fibWord: sha256:c8520ae54a0eace400fd18644db28aa25debda739a3315d6cdc8d4de6eebee63
  D5/S1/Digit/GoldenBase4IntervalMachine; module statement_id sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
    D5/S1/Digit/GoldenBase4IntervalMachine.fibPair: sha256:cbaa673b2d8bdcd2f56ac60fbd4b8496a29d1b3a9a6aa673af463265b40f3053
  D5/S1/Words/GoldenFactorComplexity; module statement_id sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
    D5/S1/Words/GoldenFactorComplexity.goldenFactor: sha256:45653c076830e3d013ea9e728d954ed6444072d1161a1656d45e0c92ab921ed8
  D5/S1/Words/GoldenWord; module statement_id sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
    D5/S1/Words/GoldenWord.fibWord_length: sha256:5a1d44cf15492ea9a6ff43c74e45238ca5f5a566d96b8b42041061ea6c98c408
    D5/S1/Words/GoldenWord.goldenWord: sha256:8f1246e0f7522a641bfb80a0177aa34160f096f22a06c1e4b8b73d07921da29b
    D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get: sha256:7be520e3583f7e49ff9381fd7da2849dbe777596ec9bdad180cebc4f2824798a
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix; module statement_id sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
    D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore: sha256:3f40284cf61afcce4df82d31142b4bd49f1b8469186a92731b352f63e5655305
    D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_length: sha256:0c959afe34a61a1028bf84864cbda37db398aa6eae5a4107da514b8754c2d4a4
    D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_palindrome: sha256:968775ab16ecaf47afae1af915a6ffceddc28088285630e7ddd658e3d5152734
  D5/S1/Words/Powers/WordPower; module statement_id sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
    D5/S1/Words/Powers/WordPower.length_wordPower: sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf
    D5/S1/Words/Powers/WordPower.wordPower: sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416
    D5/S1/Words/Powers/WordPower.wordPower_succ: sha256:2555a0f5d0c0ce76d62ea9dc70d6f8b1554ec0d5a37821080b16cbaabc5c2b5d
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
