/- GID: D5/S1/Words/Palindromes/GoldenPalindromicPrefixComplete
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:kernel-decide-small-cases-are-contained-in-this-formal-module)
   anchors: []
   digest: Palindromic golden-word prefixes are exactly the Fibonacci cores, with a unique index. -/

import D5.S1.Words.Palindromes.GoldenPalindromicPrefix
import Mathlib.Data.List.Infix

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

private def goldenPrefix (n : Nat) : List Bool :=
  List.ofFn fun i : Fin n => goldenWord i

private def smallExpected (n : Nat) : Bool :=
  (List.range 8).any fun Q => decide (1 <= Q /\ n = Nat.fib (Q + 2) - 2)

example : List.Palindrome (goldenPrefix 0) <-> smallExpected 0 = true := by decide
example : List.Palindrome (goldenPrefix 1) <-> smallExpected 1 = true := by decide
example : List.Palindrome (goldenPrefix 2) <-> smallExpected 2 = true := by decide
example : List.Palindrome (goldenPrefix 3) <-> smallExpected 3 = true := by decide
example : List.Palindrome (goldenPrefix 4) <-> smallExpected 4 = true := by decide
example : List.Palindrome (goldenPrefix 5) <-> smallExpected 5 = true := by decide
example : List.Palindrome (goldenPrefix 6) <-> smallExpected 6 = true := by decide
example : List.Palindrome (goldenPrefix 7) <-> smallExpected 7 = true := by decide
example : List.Palindrome (goldenPrefix 8) <-> smallExpected 8 = true := by decide
example : List.Palindrome (goldenPrefix 9) <-> smallExpected 9 = true := by decide
example : List.Palindrome (goldenPrefix 10) <-> smallExpected 10 = true := by decide
example : List.Palindrome (goldenPrefix 11) <-> smallExpected 11 = true := by decide
example : List.Palindrome (goldenPrefix 12) <-> smallExpected 12 = true := by decide
example : List.Palindrome (goldenPrefix 13) <-> smallExpected 13 = true := by decide

private def palLift (w : List Bool) : List Bool :=
  w.flatMap subst ++ [true]

private def substDecoder : List Bool -> List Bool
  | true :: false :: rest => true :: substDecoder rest
  | _ :: rest => false :: substDecoder rest
  | [] => []

private theorem substDecoder_flatMap (w : List Bool) :
    substDecoder (w.flatMap subst) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · cases w with
        | nil => rfl
        | cons c w =>
            cases c <;>
              simpa [subst, substDecoder] using congrArg (fun x => false :: x) ih
      · simp [subst, substDecoder, ih]

private theorem flatMap_subst_injective :
    Function.Injective (fun w : List Bool => w.flatMap subst) :=
  Function.LeftInverse.injective substDecoder_flatMap

private theorem palLift_injective : Function.Injective palLift := by
  intro u v huv
  apply flatMap_subst_injective
  exact List.append_cancel_right huv

private theorem reverse_palLift (w : List Bool) :
    (palLift w).reverse = palLift w.reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · simpa [palLift, subst, List.flatMap_append, List.reverse_append,
          List.append_assoc] using congrArg (fun x => x ++ [true]) ih
      · simpa [palLift, subst, List.flatMap_append, List.reverse_append,
          List.append_assoc] using congrArg (fun x => x ++ [false, true]) ih

private theorem palLift_palindrome_iff (w : List Bool) :
    List.Palindrome (palLift w) <-> List.Palindrome w := by
  constructor
  · intro hpal
    apply List.Palindrome.of_reverse_eq
    apply palLift_injective
    exact (reverse_palLift w).symm.trans hpal.reverse_eq
  · intro hpal
    apply List.Palindrome.of_reverse_eq
    rw [reverse_palLift, hpal.reverse_eq]

private theorem fibTail_flatMap_subst (Q : Nat) :
    (fibTail Q).flatMap subst = [true] ++ fibTail (Q + 1) := by
  by_cases hQ : Even Q <;> simp [fibTail, subst, Nat.even_add_one, hQ]

private theorem fibPalCore_succ_eq_palLift (Q : Nat) (hQ : 1 <= Q) :
    fibPalCore (Q + 1) = palLift (fibPalCore Q) := by
  have hword : fibWord (Q + 1) = palLift (fibPalCore Q) ++ fibTail (Q + 1) := by
    calc
      fibWord (Q + 1) = (fibWord Q).flatMap subst := by rfl
      _ = (fibPalCore Q ++ fibTail Q).flatMap subst := by
        rw [fibWord_eq_fibPalCore_append_fibTail Q hQ]
      _ = (fibPalCore Q).flatMap subst ++ (fibTail Q).flatMap subst :=
        List.flatMap_append
      _ = (fibPalCore Q).flatMap subst ++ ([true] ++ fibTail (Q + 1)) := by
        rw [fibTail_flatMap_subst]
      _ = palLift (fibPalCore Q) ++ fibTail (Q + 1) := by
        simp [palLift, List.append_assoc]
  have hdecomp := fibWord_eq_fibPalCore_append_fibTail (Q + 1) (by omega)
  exact List.append_cancel_right (hdecomp.symm.trans hword)

-- A prefix ending at a block boundary can be uniquely desubstituted by peeling the first block.
private theorem prefix_flatMap_subst_parser (source pre : List Bool)
    (hpre : pre <+: source.flatMap subst) (hne : Not (pre = []))
    (hlast : pre.getLast? = some true) :
    exists v, v <+: source /\ pre = palLift v := by
  induction source generalizing pre with
  | nil =>
      have : pre = [] := by simpa using hpre
      exact (hne this).elim
  | cons b source ih =>
      cases pre with
      | nil => exact (hne rfl).elim
      | cons p pre =>
          cases b with
          | false =>
              change p :: pre <+: true :: source.flatMap subst at hpre
              rcases List.cons_prefix_cons.mp hpre with ⟨hp, hpreTail⟩
              cases hp
              cases pre with
              | nil => exact ⟨[], List.nil_prefix, rfl⟩
              | cons q rest =>
                  have hlast' : (q :: rest).getLast? = some true := by
                    simpa using hlast
                  obtain ⟨v, hv, hpv⟩ := ih (q :: rest) hpreTail (by simp) hlast'
                  refine ⟨false :: v, List.cons_prefix_cons.mpr ⟨rfl, hv⟩, ?_⟩
                  simp [palLift, subst, hpv]
          | true =>
              change p :: pre <+: true :: false :: source.flatMap subst at hpre
              rcases List.cons_prefix_cons.mp hpre with ⟨hp, hpreTail⟩
              cases hp
              cases pre with
              | nil => exact ⟨[], List.nil_prefix, rfl⟩
              | cons q rest =>
                  rcases List.cons_prefix_cons.mp hpreTail with ⟨hq, hrest⟩
                  cases hq
                  cases rest with
                  | nil => simp at hlast
                  | cons r rest =>
                      have hlast' : (r :: rest).getLast? = some true := by
                        simpa using hlast
                      obtain ⟨v, hv, hpv⟩ := ih (r :: rest) hrest (by simp) hlast'
                      refine ⟨true :: v, List.cons_prefix_cons.mpr ⟨rfl, hv⟩, ?_⟩
                      simp [palLift, subst, hpv]

private theorem length_le_flatMap_subst (w : List Bool) :
    w.length <= (w.flatMap subst).length := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      cases b <;> simp only [subst, List.length_cons, List.length_nil] <;> omega

private theorem goldenPrefix_prefix_fibWord (n : Nat) :
    goldenPrefix n <+: fibWord (n + 1) := by
  have hlength : n <= (fibWord (n + 1)).length := by
    have h := index_lt_diagonal_level (n + 1)
    omega
  rw [List.prefix_iff_eq_take]
  apply List.ext_get
  · simp [goldenPrefix, hlength]
  · intro i hi _
    have hiword : i < (fibWord (n + 1)).length := by
      simp [goldenPrefix] at hi
      omega
    simpa [goldenPrefix] using goldenWord_eq_fibWord_get (n + 1) i hiword

private theorem prefix_eq_goldenPrefix {Q : Nat} {v : List Bool}
    (hv : v <+: fibWord Q) : v = goldenPrefix v.length := by
  apply List.ext_get
  · simp [goldenPrefix]
  · intro i hi _
    have hiword : i < (fibWord Q).length := lt_of_lt_of_le hi hv.length_le
    simpa [goldenPrefix] using
      (hv.getElem hi).trans (goldenWord_eq_fibWord_get Q i hiword).symm

private theorem palindromic_goldenPrefix_eq_fibPalCore :
    forall n, List.Palindrome (goldenPrefix n) ->
      exists Q, 1 <= Q /\ goldenPrefix n = fibPalCore Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hpal
      by_cases hn : n = 0
      · subst n
        exact ⟨1, by omega, by decide⟩
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hpref := goldenPrefix_prefix_fibWord n
        change goldenPrefix n <+: (fibWord n).flatMap subst at hpref
        have hne : Not (goldenPrefix n = []) := by simp [goldenPrefix, hn]
        have hhead : (goldenPrefix n).head? = some true := by
          have hzero : goldenWord 0 = true := by decide
          rw [List.head?_eq_getElem?]
          simp [goldenPrefix, hnpos, hzero]
        have hlast : (goldenPrefix n).getLast? = some true := by
          calc
            (goldenPrefix n).getLast? = (goldenPrefix n).reverse.head? :=
              List.getLast?_eq_head?_reverse
            _ = (goldenPrefix n).head? := by rw [hpal.reverse_eq]
            _ = some true := hhead
        obtain ⟨v, hv, hpv⟩ := prefix_flatMap_subst_parser _ _ hpref hne hlast
        have hvgolden : v = goldenPrefix v.length := prefix_eq_goldenPrefix hv
        have hvlen : v.length < n := by
          have hlength := congrArg List.length hpv
          have hsub := length_le_flatMap_subst v
          simp only [goldenPrefix, List.length_ofFn, palLift, List.length_append,
            List.length_singleton] at hlength
          omega
        have hvpal : List.Palindrome (goldenPrefix v.length) := by
          have hliftpal : List.Palindrome (palLift v) := by rwa [← hpv]
          have : List.Palindrome v := (palLift_palindrome_iff v).mp hliftpal
          rwa [← hvgolden]
        obtain ⟨Q, hQ, hcore⟩ := ih v.length hvlen hvpal
        refine ⟨Q + 1, by omega, ?_⟩
        calc
          goldenPrefix n = palLift v := hpv
          _ = palLift (goldenPrefix v.length) := congrArg palLift hvgolden
          _ = palLift (fibPalCore Q) := congrArg palLift hcore
          _ = fibPalCore (Q + 1) := (fibPalCore_succ_eq_palLift Q hQ).symm

/-- A finite golden-word prefix is palindromic exactly at a Fibonacci-core length. -/
theorem goldenWord_palindromic_prefix_iff (n : Nat) :
    List.Palindrome (List.ofFn (fun i : Fin n => goldenWord i)) <->
      (exists Q, 1 <= Q /\ n = Nat.fib (Q + 2) - 2) := by
  change List.Palindrome (goldenPrefix n) <-> _
  constructor
  · intro hpal
    obtain ⟨Q, hQ, hcore⟩ := palindromic_goldenPrefix_eq_fibPalCore n hpal
    refine ⟨Q, hQ, ?_⟩
    have hlength := congrArg List.length hcore
    simpa [goldenPrefix, fibPalCore_length Q hQ] using hlength
  · rintro ⟨Q, hQ, rfl⟩
    exact goldenWord_palindromic_prefix Q hQ

/-- The Fibonacci-core index representing a palindromic-prefix length is unique. -/
theorem goldenWord_palindromic_prefix_index_unique (n Q R : Nat)
    (hQ : 1 <= Q) (hnQ : n = Nat.fib (Q + 2) - 2)
    (hR : 1 <= R) (hnR : n = Nat.fib (R + 2) - 2) : Q = R := by
  apply Nat.fib_add_two_strictMono.injective
  change Nat.fib (Q + 2) = Nat.fib (R + 2)
  have hQtwo : 2 <= Nat.fib (Q + 2) := by
    have hmono := Nat.fib_add_two_strictMono.monotone hQ
    norm_num [Nat.fib] at hmono ⊢
    exact hmono
  have hRtwo : 2 <= Nat.fib (R + 2) := by
    have hmono := Nat.fib_add_two_strictMono.monotone hR
    norm_num [Nat.fib] at hmono ⊢
    exact hmono
  have hsub : Nat.fib (Q + 2) - 2 = Nat.fib (R + 2) - 2 := hnQ.symm.trans hnR
  omega

#print axioms goldenWord_palindromic_prefix_iff
#print axioms goldenWord_palindromic_prefix_index_unique

end D5.S1.Words
