/- GID: D5/S1/Words/Palindromes/GoldenPalindromicFactorComplexity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:kernel-decide-small-cases-are-contained-in-this-formal-module)
   anchors: []
   digest: Golden palindromic factor complexity alternates exactly between one and two. -/

import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.Palindromes.GoldenPalindromicPrefix
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

/-- The finite set of palindromic length-`n` factors of the infinite golden word. -/
noncomputable def goldenPalindromicFactorSet (n : Nat) : Finset (List Bool) :=
  (goldenFactorSet n).filter fun w => List.Palindrome w

/-- A word belongs to the palindromic factor set exactly when it occurs and is a palindrome. -/
theorem mem_goldenPalindromicFactorSet {n : Nat} {w : List Bool} :
    w ∈ goldenPalindromicFactorSet n ↔
      ∃ i, w = goldenFactor n i ∧ List.Palindrome w := by
  classical
  rw [goldenPalindromicFactorSet, Finset.mem_filter, mem_goldenFactorSet]
  aesop

private def boundedGoldenPalindromicFactorSet (n starts : Nat) : Finset (List Bool) :=
  ((Finset.range starts).image (goldenFactor n)).filter fun w => List.Palindrome w

private example : (boundedGoldenPalindromicFactorSet 0 34).card = 1 := by decide
private example : (boundedGoldenPalindromicFactorSet 1 34).card = 2 := by decide
private example : (boundedGoldenPalindromicFactorSet 2 34).card = 1 := by decide
private example : (boundedGoldenPalindromicFactorSet 3 34).card = 2 := by decide
private example : (boundedGoldenPalindromicFactorSet 4 34).card = 1 := by decide
private example : (boundedGoldenPalindromicFactorSet 5 34).card = 2 := by decide
private example : (boundedGoldenPalindromicFactorSet 6 34).card = 1 := by decide

private theorem fib_even_add_three_iff (k : Nat) :
    Even (Nat.fib (k + 3)) ↔ Even (Nat.fib k) := by
  rw [show k + 3 = (k + 1) + 2 by omega, Nat.fib_add_two,
    show k + 1 + 1 = k + 2 by omega, Nat.fib_add_two]
  simp only [Nat.even_add]
  tauto

private theorem fib_even_three_mul (k : Nat) : Even (Nat.fib (3 * k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, fib_even_add_three_iff]
      exact ih

private theorem fib_not_even_three_mul_add_one (k : Nat) :
    ¬Even (Nat.fib (3 * k + 1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.mul_succ, show 3 * k + 3 + 1 = (3 * k + 1) + 3 by omega,
        fib_even_add_three_iff]
      exact ih

private theorem exists_long_fibPalCore_same_parity (n : Nat) :
    ∃ Q, 1 ≤ Q ∧ n ≤ (fibPalCore Q).length ∧
      Even ((fibPalCore Q).length - n) := by
  by_cases hn : Even n
  · let Q := 3 * (n + 1) + 1
    have hQ : 1 ≤ Q := by simp [Q]
    have hdiag := index_lt_diagonal_level Q
    rw [fibWord_length] at hdiag
    have hlength : n ≤ (fibPalCore Q).length := by
      rw [fibPalCore_length Q hQ]
      have hnQ : n + 2 ≤ Q := by dsimp [Q]; omega
      have := hnQ.trans hdiag.le
      omega
    have hfib : Even (Nat.fib (Q + 2)) := by
      have := fib_even_three_mul (n + 2)
      rw [show Q + 2 = 3 * (n + 2) by dsimp [Q]; omega]
      exact this
    have hcore : Even (fibPalCore Q).length := by
      rw [fibPalCore_length Q hQ, Nat.even_sub (by omega)]
      simpa using hfib
    refine ⟨Q, hQ, hlength, ?_⟩
    rw [Nat.even_sub hlength]
    exact iff_of_true hcore hn
  · let Q := 3 * (n + 1) + 2
    have hQ : 1 ≤ Q := by simp [Q]
    have hdiag := index_lt_diagonal_level Q
    rw [fibWord_length] at hdiag
    have hlength : n ≤ (fibPalCore Q).length := by
      rw [fibPalCore_length Q hQ]
      have hnQ : n + 2 ≤ Q := by dsimp [Q]; omega
      have := hnQ.trans hdiag.le
      omega
    have hfib : ¬Even (Nat.fib (Q + 2)) := by
      have := fib_not_even_three_mul_add_one (n + 2)
      rw [show Q + 2 = 3 * (n + 2) + 1 by dsimp [Q]; omega]
      exact this
    have hcore : ¬Even (fibPalCore Q).length := by
      rw [fibPalCore_length Q hQ, Nat.even_sub (by omega)]
      simpa using hfib
    refine ⟨Q, hQ, hlength, ?_⟩
    rw [Nat.even_sub hlength]
    exact iff_of_false hcore hn

private theorem palindrome_has_infix_of_length {alpha : Type*} {w : List alpha}
    (hpal : List.Palindrome w) (n : Nat) (hn : n ≤ w.length)
    (hparity : Even (w.length - n)) :
    ∃ u, u <:+: w ∧ u.length = n ∧ List.Palindrome u := by
  induction hpal with
  | nil =>
      have hnzero : n = 0 := by simp at hn; exact hn
      subst n
      exact ⟨[], List.infix_rfl, rfl, List.Palindrome.nil⟩
  | singleton x =>
      have hnle : n ≤ 1 := by simpa using hn
      have hnzero : n ≠ 0 := by
        intro hnzero
        subst n
        norm_num at hparity
      have : n = 1 := by omega
      subst n
      exact ⟨[x], List.infix_rfl, rfl, List.Palindrome.singleton x⟩
  | @cons_concat x inner hinner ih =>
      by_cases hfull : n = (x :: (inner ++ [x])).length
      · subst n
        exact ⟨x :: (inner ++ [x]), List.infix_rfl, rfl,
          List.Palindrome.cons_concat x hinner⟩
      · have hninner : n ≤ inner.length := by
          obtain ⟨k, hk⟩ := hparity
          simp only [List.length_cons, List.length_append, List.length_nil] at hn hk hfull
          omega
        have hinnerParity : Even (inner.length - n) := by
          rw [Nat.even_sub hninner]
          have houterParity : Even (inner.length + 2) ↔ Even n := by
            have := (Nat.even_sub hn).mp hparity
            simpa using this
          constructor
          · exact fun h => houterParity.mp (h.add even_two)
          · intro h
            obtain ⟨k, hk⟩ := houterParity.mpr h
            refine ⟨k - 1, ?_⟩
            omega
        obtain ⟨u, hu, hulength, hupal⟩ := ih hninner hinnerParity
        refine ⟨u, hu.trans ?_, hulength, hupal⟩
        exact ⟨[x], [x], by simp⟩

private theorem goldenFactor_eq_take_drop (Q n i : Nat)
    (h : i + n ≤ (fibWord Q).length) :
    goldenFactor n i = ((fibWord Q).drop i).take n := by
  apply List.ext_get
  · simp [goldenFactor]
    omega
  · intro k hkleft hkright
    have hk : k < n := by simpa [goldenFactor] using hkleft
    have hindex : i + k < (fibWord Q).length := by omega
    simpa [goldenFactor] using goldenWord_eq_fibWord_get Q (i + k) hindex

private theorem palindromic_golden_factor_exists (n : Nat) :
    (goldenPalindromicFactorSet n).Nonempty := by
  obtain ⟨Q, hQ, hncore, hparity⟩ := exists_long_fibPalCore_same_parity n
  obtain ⟨u, hu, hulength, hupal⟩ :=
    palindrome_has_infix_of_length (fibPalCore_palindrome Q hQ) n hncore hparity
  have hcorePrefix : fibPalCore Q <+: fibWord Q := by
    rw [fibWord_eq_fibPalCore_append_fibTail Q hQ]
    exact List.prefix_append _ _
  have huword : u <:+: fibWord Q := hu.trans hcorePrefix.isInfix
  rcases huword with ⟨left, right, hword⟩
  let i := left.length
  have hibound : i + n ≤ (fibWord Q).length := by
    have hlength := congrArg List.length hword
    simp only [List.length_append] at hlength
    dsimp [i]
    omega
  have hfactor : u = goldenFactor n i := by
    calc
      u = ((fibWord Q).drop i).take n := by
        dsimp only [i]
        rw [← hword]
        simp [hulength]
      _ = goldenFactor n i := (goldenFactor_eq_take_drop Q n i hibound).symm
  refine ⟨u, mem_goldenPalindromicFactorSet.mpr ⟨i, hfactor, hupal⟩⟩

private def palindromeTrim {alpha : Type*} (w : List alpha) : List alpha :=
  w.tail.dropLast

private theorem palindromeTrim_palindrome {alpha : Type*} {w : List alpha}
    (hpal : List.Palindrome w) : List.Palindrome (palindromeTrim w) := by
  cases hpal with
  | nil => exact List.Palindrome.nil
  | singleton x => exact List.Palindrome.nil
  | cons_concat x hinner => simpa [palindromeTrim] using hinner

private theorem palindrome_eq_cons_trim_append {alpha : Type*} {w : List alpha}
    (hpal : List.Palindrome w) (hlarge : 2 ≤ w.length) :
    ∃ a, w = a :: palindromeTrim w ++ [a] := by
  cases hpal with
  | nil => simp at hlarge
  | singleton x => simp at hlarge
  | cons_concat x hinner => exact ⟨x, by simp [palindromeTrim]⟩

private theorem goldenFactor_succ (n i : Nat) :
    goldenFactor (n + 1) i = goldenFactor n i ++ [goldenWord (i + n)] := by
  unfold goldenFactor
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

private theorem goldenFactor_succ_left (n i : Nat) :
    goldenFactor (n + 1) i = goldenWord i :: goldenFactor n (i + 1) := by
  apply List.ext_get
  · simp [goldenFactor]
  · intro k hkleft hkright
    simp only [List.get_eq_getElem]
    cases k with
    | zero => simp [goldenFactor]
    | succ k =>
        simp [goldenFactor]
        congr 1
        omega

private theorem palindromeTrim_goldenFactor (n i : Nat) :
    palindromeTrim (goldenFactor (n + 2) i) = goldenFactor n (i + 1) := by
  rw [show n + 2 = (n + 1) + 1 by omega, goldenFactor_succ_left,
    palindromeTrim, List.tail_cons, goldenFactor_succ]
  simp

private noncomputable def trimPalFactor (n : Nat) :
    ↥(goldenPalindromicFactorSet (n + 2)) → ↥(goldenPalindromicFactorSet n) :=
  fun w => ⟨palindromeTrim w.1, by
    obtain ⟨i, hi, hpal⟩ := mem_goldenPalindromicFactorSet.mp w.2
    refine mem_goldenPalindromicFactorSet.mpr ⟨i + 1, ?_, palindromeTrim_palindrome hpal⟩
    rw [hi, palindromeTrim_goldenFactor]⟩

private theorem goldenWindowTrueCount_succ (i n : Nat) :
    goldenWindowTrueCount i (n + 1) = goldenWindowTrueCount i n +
      if goldenWord (i + n) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + n) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]

private theorem goldenFactor_count_true (n i : Nat) :
    (goldenFactor n i).count true = goldenWindowTrueCount i n := by
  induction n with
  | zero => simp [goldenFactor, goldenWindowTrueCount]
  | succ n ih =>
      rw [goldenFactor_succ, List.count_append, goldenWindowTrueCount_succ, ih]
      by_cases h : goldenWord (i + n) = true <;> simp [h]

private theorem count_true_cons_append (a : Bool) (w : List Bool) :
    (a :: w ++ [a]).count true = w.count true + if a = true then 2 else 0 := by
  cases a <;> simp [List.count_append]

private theorem trimPalFactor_injective (n : Nat) :
    Function.Injective (trimPalFactor n) := by
  intro u v huv
  have htrim : palindromeTrim u.1 = palindromeTrim v.1 := by
    simpa [trimPalFactor] using congrArg Subtype.val huv
  obtain ⟨i, hi, huPal⟩ := mem_goldenPalindromicFactorSet.mp u.2
  obtain ⟨j, hj, hvPal⟩ := mem_goldenPalindromicFactorSet.mp v.2
  have huLength : u.1.length = n + 2 := by
    exact length_eq_of_mem_goldenFactorSet
      (Finset.mem_filter.mp u.2 |>.1)
  have hvLength : v.1.length = n + 2 := by
    exact length_eq_of_mem_goldenFactorSet
      (Finset.mem_filter.mp v.2 |>.1)
  obtain ⟨a, hua⟩ := palindrome_eq_cons_trim_append huPal (by omega)
  obtain ⟨b, hvb⟩ := palindrome_eq_cons_trim_append hvPal (by omega)
  have hab : a = b := by
    by_contra hab
    have hbalance := goldenWord_balanced_one i j (n + 2)
    rw [← goldenFactor_count_true (n + 2) i,
      ← goldenFactor_count_true (n + 2) j, ← hi, ← hj, hua, hvb,
      count_true_cons_append, count_true_cons_append, htrim] at hbalance
    cases a <;> cases b
    · exact (hab rfl).elim
    · norm_num at hbalance
    · norm_num at hbalance
    · exact (hab rfl).elim
  apply Subtype.ext
  rw [hua, hvb, hab, htrim]

private theorem palindromic_factor_card_add_two_le (n : Nat) :
    (goldenPalindromicFactorSet (n + 2)).card ≤
      (goldenPalindromicFactorSet n).card := by
  simpa using Finset.card_le_card_of_injective (trimPalFactor_injective n)

private theorem palindromic_factor_even_upper (k : Nat) :
    (goldenPalindromicFactorSet (2 * k)).card ≤ 1 := by
  induction k with
  | zero =>
      have hfilter := Finset.card_filter_le (goldenFactorSet 0) List.Palindrome
      rw [golden_factor_complexity] at hfilter
      simpa [goldenPalindromicFactorSet] using hfilter
  | succ k ih =>
      have hstep := palindromic_factor_card_add_two_le (2 * k)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      exact hstep.trans ih

private theorem palindromic_factor_odd_upper (k : Nat) :
    (goldenPalindromicFactorSet (2 * k + 1)).card ≤ 2 := by
  induction k with
  | zero =>
      have hfilter := Finset.card_filter_le (goldenFactorSet 1) List.Palindrome
      rw [golden_factor_complexity] at hfilter
      simpa [goldenPalindromicFactorSet] using hfilter
  | succ k ih =>
      have hstep := palindromic_factor_card_add_two_le (2 * k + 1)
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
      exact hstep.trans ih

private theorem palindrome_getElem?_mirror {alpha : Type*} {w : List alpha}
    (hpal : List.Palindrome w) {i j : Nat} (hij : i + j + 1 = w.length) :
    w[i]? = w[j]? := by
  have h := congrArg (fun u : List alpha => u[i]?) hpal.reverse_eq
  rw [List.getElem?_reverse' hij] at h
  exact h.symm

private theorem golden_factor_reverse_occurs (m i : Nat) :
    ∃ j, (goldenFactor m i).reverse = goldenFactor m j := by
  let Q := i + m + 2
  let N := Nat.fib (Q + 2) - 2
  have hlevel := index_lt_diagonal_level Q
  rw [fibWord_length] at hlevel
  have hbound : i + m ≤ N := by
    have hlevel' : i + m + 2 < Nat.fib (i + m + 2 + 2) := by
      simpa [Q] using hlevel
    dsimp [Q, N]
    omega
  have hpal : List.Palindrome
      (List.ofFn fun i : Fin N => goldenWord i) := by
    exact goldenWord_palindromic_prefix Q (by dsimp [Q]; omega)
  let j := N - (i + m)
  refine ⟨j, ?_⟩
  apply List.ext_get
  · simp [goldenFactor]
  · intro k hkleft hkright
    have hk : k < m := by simpa [goldenFactor] using hkright
    have hindex : i + (m - 1 - k) + (j + k) + 1 = N := by
      dsimp [j]
      omega
    have hiindex : i + (m - 1 - k) < N := by omega
    have hjindex : j + k < N := by omega
    have hmirror := palindrome_getElem?_mirror hpal (by
      simpa using hindex)
    rw [List.getElem?_eq_getElem (by simpa using hiindex),
      List.getElem?_eq_getElem (by simpa using hjindex)] at hmirror
    simp only [List.getElem_ofFn, Option.some.injEq] at hmirror
    simp only [List.get_eq_getElem]
    rw [List.getElem_reverse]
    simp only [goldenFactor, List.length_ofFn, List.getElem_ofFn]
    exact hmirror

private noncomputable def goldenFactorReverse (n : Nat) :
    Function.End ↥(goldenFactorSet n) :=
  fun w => ⟨w.1.reverse, by
    obtain ⟨i, hi⟩ := mem_goldenFactorSet.mp w.2
    obtain ⟨j, hj⟩ := golden_factor_reverse_occurs n i
    exact mem_goldenFactorSet.mpr ⟨j, by rw [hi]; exact hj⟩⟩

private theorem goldenFactorReverse_sq (n : Nat) :
    goldenFactorReverse n ^ 2 = 1 := by
  rw [pow_two, Function.End.mul_def, Function.End.one_def]
  funext w
  apply Subtype.ext
  change w.1.reverse.reverse = w.1
  exact List.reverse_reverse w.1

private noncomputable def reverseFixedPointsEquiv (n : Nat) :
    Function.fixedPoints (goldenFactorReverse n) ≃
      ↥(goldenPalindromicFactorSet n) where
  toFun w := ⟨w.1.1, Finset.mem_filter.mpr ⟨w.1.2, by
    apply List.Palindrome.of_reverse_eq
    exact congrArg Subtype.val w.2⟩⟩
  invFun w := ⟨⟨w.1, Finset.mem_filter.mp w.2 |>.1⟩, by
    apply Subtype.ext
    simpa [goldenFactorReverse] using
      (Finset.mem_filter.mp w.2 |>.2).reverse_eq⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

private theorem palindromic_factor_card_mod_two (n : Nat) :
    (goldenPalindromicFactorSet n).card ≡ (goldenFactorSet n).card [MOD 2] := by
  have hpow : goldenFactorReverse n ^ 2 ^ 1 = 1 := by
    simpa using goldenFactorReverse_sq n
  have hmod := Equiv.Perm.card_fixedPoints_modEq
    (p := 2) (n := 1) (f := goldenFactorReverse n) hpow
  simp only [Fintype.card_eq_nat_card] at hmod
  have hfixed :
      Nat.card (Function.fixedPoints (goldenFactorReverse n)) =
        (goldenPalindromicFactorSet n).card := by
    calc
      Nat.card (Function.fixedPoints (goldenFactorReverse n)) =
          Nat.card ↥(goldenPalindromicFactorSet n) :=
        Nat.card_congr (reverseFixedPointsEquiv n)
      _ = Fintype.card ↥(goldenPalindromicFactorSet n) :=
        Nat.card_eq_fintype_card
      _ = (goldenPalindromicFactorSet n).card := Fintype.card_coe _
  rw [hfixed] at hmod
  simpa using hmod.symm

/-- The golden word has one palindromic factor in every even length and two in every odd length. -/
theorem golden_palindromic_factor_complexity (n : Nat) :
    (goldenPalindromicFactorSet n).card = if Even n then 1 else 2 := by
  by_cases hn : Even n
  · rw [if_pos hn]
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hn
    have hupper : (goldenPalindromicFactorSet n).card ≤ 1 := by
      rw [hk]
      exact palindromic_factor_even_upper k
    have hlower : 0 < (goldenPalindromicFactorSet n).card :=
      Finset.card_pos.mpr (palindromic_golden_factor_exists n)
    omega
  · rw [if_neg hn]
    have hodd : Odd n := Nat.not_even_iff_odd.mp hn
    obtain ⟨k, hk⟩ := hodd.exists_bit1
    have hupper : (goldenPalindromicFactorSet n).card ≤ 2 := by
      rw [hk]
      exact palindromic_factor_odd_upper k
    have hlower : 0 < (goldenPalindromicFactorSet n).card :=
      Finset.card_pos.mpr (palindromic_golden_factor_exists n)
    have hmod := palindromic_factor_card_mod_two n
    rw [golden_factor_complexity] at hmod
    have htotalEven : Even (n + 1) := hodd.add_one
    have hcardEven : Even (goldenPalindromicFactorSet n).card := by
      apply even_iff_two_dvd.mpr
      exact Nat.modEq_zero_iff_dvd.mp (hmod.trans htotalEven.two_dvd.modEq_zero_nat)
    obtain ⟨r, hr⟩ := hcardEven
    omega

#print axioms mem_goldenPalindromicFactorSet
#print axioms golden_palindromic_factor_complexity

end D5.S1.Words
