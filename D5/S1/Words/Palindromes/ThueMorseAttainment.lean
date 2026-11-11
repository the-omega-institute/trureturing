/- GID: D5/S1/Words/Palindromes/ThueMorseAttainment
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ThueMorseAttainment
   mirror-E: none(waiver:literal-thue-morse-attainment)
   anchors: []
   utility: none
   digest: An unbounded family attains equal ordinary and mixed palindromic costs. -/

import D5.S1.Words.Palindromes.ThueMorseSignedCut
import D5.S1.Words.Palindromes.PeriodDoubling.NonadjacentSignedDigits

/-! An attaining family for the literal mixed-cost prefix bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.ThueMorse
open D5.S1.Words.Complexity
open D5.S1.Words.Palindromes.PeriodDoubling

/-- Index zero is the first member of the positive family. -/
def attainingLength : ℕ → ℕ
  | 0 => 1
  | m + 1 => 4 * attainingLength m - 1

private def digits : ℕ → List ℤ
  | 0 => [1]
  | m + 1 => -1 :: 0 :: digits m

private theorem family_positive (m : ℕ) : 0 < attainingLength m := by
  induction m with
  | zero => decide
  | succ m ih => simp only [attainingLength]; omega

private theorem family_weight (m : ℕ) : signedWeight (attainingLength m : ℤ) = m + 1 := by
  have hd : ∀ m, (∀ z ∈ digits m, z = -1 ∨ z = 0 ∨ z = 1) ∧
      (digits m).IsChain (fun a b => a = 0 ∨ b = 0) ∧
      (digits m).foldr (fun z acc => z + 2 * acc) 0 = (attainingLength m : ℤ) ∧
      ((digits m).filter (fun z => z != 0)).length = m + 1 := by
    intro m
    induction m with
    | zero => simp [digits, attainingLength]
    | succ m ih =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [digits] using ih.1
      · rw [digits, List.isChain_cons_cons]
        refine ⟨Or.inr rfl, ?_⟩
        exact ih.2.1.cons (by intro y hy; exact Or.inl rfl)
      · have hp := family_positive m
        simp only [digits, List.foldr_cons, ih.2.2.1, attainingLength]
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      · simpa [digits] using congrArg (fun n : ℕ => n + 1) ih.2.2.2
  have h := signed_weight_nonadjacent (digits m) (hd m).1 (hd m).2.1
  simpa only [(hd m).2.2.1, (hd m).2.2.2] using h

def tau (w : List Bool) : List Bool :=
  w.flatMap (fun b => [b, !b, !b, b])

private theorem tau_append (u v : List Bool) : tau (u ++ v) = tau u ++ tau v := by
  simp only [tau, List.flatMap_append]

private theorem tau_palindrome {w : List Bool} (h : List.Palindrome w) :
    List.Palindrome (tau w) := by
  have rev (v : List Bool) : (tau v).reverse = tau v.reverse := by
    induction v with
    | nil => rfl
    | cons b v ih =>
      rw [show tau (b :: v) = [b, !b, !b, b] ++ tau v from rfl,
        List.reverse_append, ih]
      rw [show (b :: v).reverse = v.reverse ++ [b] by simp only [List.reverse_cons],
        tau_append]
      simp [tau]
  apply List.Palindrome.of_reverse_eq
  rw [rev, h.reverse_eq]

theorem tau_pl (w : List Bool) : FridPrefix.PL (tau w) ≤ FridPrefix.PL w := by
  classical
  obtain ⟨ps, hps, hlen, hp⟩ : FridPrefix.PalFactors w (FridPrefix.PL w) := by
    unfold FridPrefix.PL
    exact Nat.find_spec _
  apply Nat.find_le (show FridPrefix.PalFactors (tau w) (FridPrefix.PL w) from ?_)
  refine ⟨ps.map tau, ?_, by simpa using hlen, ?_⟩
  · have flatten_tau (qs : List (List Bool)) : (qs.map tau).flatten = tau qs.flatten := by
      induction qs with
      | nil => rfl
      | cons p ps ih => simpa [tau, List.flatMap_append] using congrArg (List.append (tau p)) ih
    rw [flatten_tau, hps]
  · intro q hq
    obtain ⟨p, hpmem, rfl⟩ := List.mem_map.mp hq
    refine ⟨?_, tau_palindrome (hp p hpmem).2⟩
    cases p with
    | nil => exact ((hp [] hpmem).1 rfl).elim
    | cons b p => simp [tau]

theorem factor_concat (n start : ℕ) :
    factor (n + 1) start = factor n start ++ [thueMorse (start + n)] := by
  simp [factor, List.range_succ, List.map_append]

theorem tau_prefix (n : ℕ) : tau (factor n 0) = factor (4 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [factor_concat]
    simp only [tau, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change tau (factor n 0) ++ _ = _
    rw [ih]
    rw [show 4 * (n + 1) = ((4 * n + 1) + 1) + 1 + 1 by omega]
    simp only [factor_concat, Nat.zero_add]
    have h0 : thueMorse (4 * n) = thueMorse n := by
      rw [show 4 * n = 2 * (2 * n) by omega, thueMorse_two_mul, thueMorse_two_mul]
    have h1 : thueMorse (4 * n + 1) = !thueMorse n := by
      rw [show 4 * n + 1 = 2 * (2 * n) + 1 by omega,
        thueMorse_two_mul_add_one, thueMorse_two_mul]
    have h2 : thueMorse (4 * n + 1 + 1) = !thueMorse n := by
      rw [show 4 * n + 1 + 1 = 2 * (2 * n + 1) by omega,
        thueMorse_two_mul, thueMorse_two_mul_add_one]
    have h3 : thueMorse (4 * n + 1 + 1 + 1) = thueMorse n := by
      rw [show 4 * n + 1 + 1 + 1 = 2 * (2 * n + 1) + 1 by omega,
        thueMorse_two_mul_add_one, thueMorse_two_mul_add_one, Bool.not_not]
    simp only [h0, h1, h2, h3, List.append_assoc, List.cons_append, List.nil_append]

theorem prefix_four_sub_one (n : ℕ) (hn : 0 < n) :
    FridPrefix.PL (factor (4 * n - 1) 0) ≤ FridPrefix.PL (factor n 0) + 1 := by
  have ht := tau_pl (factor n 0)
  rw [tau_prefix] at ht
  have hd := FridPrefix.pl_one_letter_lipschitz
    (factor (4 * n - 1) 0) (thueMorse (4 * n - 1))
  have hc := factor_concat (4 * n - 1) 0
  simp only [Nat.zero_add] at hc
  rw [← hc] at hd
  rw [show 4 * n - 1 + 1 = 4 * n by omega] at hd
  rw [abs_le] at hd
  omega

private theorem family_upper (m : ℕ) :
    FridPrefix.PL (factor (attainingLength m) 0) ≤ m + 1 := by
  classical
  induction m with
  | zero =>
    apply Nat.find_le (show FridPrefix.PalFactors (factor (attainingLength 0) 0) 1 from ?_)
    exact ⟨[[false]], rfl, rfl, by simp [List.Palindrome.singleton]⟩
  | succ m ih =>
    have h := prefix_four_sub_one (attainingLength m) (family_positive m)
    simp only [attainingLength]
    omega

/-- Both actual minimum factorization costs equal the unbounded family index. -/
theorem family_attains (m : ℕ) :
    signedWeight (attainingLength m : ℤ) = m + 1 ∧
    combinedLength (factor (attainingLength m) 0) = m + 1 ∧
    FridPrefix.PL (factor (attainingLength m) 0) = m + 1 := by
  have hl := combined_prefix_signed_lower (attainingLength m)
  have hw := family_weight m
  have hu := family_upper m
  exact ⟨hw, by omega, by omega⟩

/-- The exact Section 6 whole assertion for literal prefixes and nonempty factors. -/
theorem unbounded_equal_cost (K : ℕ) (_hK : 1 ≤ K) :
    ∃ n : ℕ, 1 ≤ n ∧
      combinedLength (factor n 0) = FridPrefix.PL (factor n 0) ∧
      K ≤ FridPrefix.PL (factor n 0) := by
  refine ⟨attainingLength K, family_positive K, ?_, ?_⟩
  · rw [(family_attains K).2.1, (family_attains K).2.2]
  · rw [(family_attains K).2.2]; omega

end D5.S1.Words.Palindromes.ThueMorse

#print axioms D5.S1.Words.Palindromes.ThueMorse.family_attains
#print axioms D5.S1.Words.Palindromes.ThueMorse.unbounded_equal_cost
