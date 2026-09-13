/- GID: D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: Infinitely many decimal palindromes have nonpalindromic squares whose reversals are squares. -/
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Palindromes whose reversed square is a square

`Nat.digits` is little-endian. Thus reversing that list and applying
`Nat.ofDigits` gives the natural number obtained by reversing the usual
decimal representation. This is distinct from
`D5.S3.Arith.SumInConcatenation.D`, which returns only a digit list.
-/

namespace D5.S1.Digit.Admissibility.PalindromeSquareReversalInfinitude

/-- Reverse the ordinary base-ten digits of a natural number. -/
def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A natural number is a decimal palindrome. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  rev10 n = n

/-- Membership in OEIS A133901, expressed through the definition of A128921. -/
def IsMember (p : ℕ) : Prop :=
  IsPalindrome10 p ∧ ¬ IsPalindrome10 (p ^ 2) ∧ ∃ q, rev10 (p ^ 2) = q ^ 2

/-- Decimal digits of little-endian base-`10^j` blocks, with only the top block unpadded. -/
private def blockDigits (j : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => Nat.digits 10 a
  | a :: b :: rest => Nat.digitsAppend 10 j a ++ blockDigits j (b :: rest)

private theorem digits_of_pow_blocks (j : ℕ) (blocks : List ℕ)
    (hpos : ∀ a ∈ blocks, 0 < a)
    (hlt : ∀ a ∈ blocks, a < 10 ^ j) :
    Nat.digits 10 (Nat.ofDigits (10 ^ j) blocks) = blockDigits j blocks := by
  induction blocks with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => simp [blockDigits, Nat.ofDigits]
      | cons b rest =>
          have hm : 0 < Nat.ofDigits (10 ^ j) (b :: rest) := by
            rw [Nat.ofDigits_cons]
            have hb := hpos b (by simp)
            omega
          have hlen : (Nat.digits 10 a).length ≤ j :=
            (Nat.digits_length_le_iff (by norm_num) a).2 (hlt a (by simp))
          have hadd := Nat.digits_append_zeroes_append_digits
            (b := 10) (k := j - (Nat.digits 10 a).length)
            (m := Nat.ofDigits (10 ^ j) (b :: rest)) (n := a) (by norm_num) hm
          rw [Nat.add_sub_of_le hlen] at hadd
          rw [Nat.ofDigits_cons, ← hadd]
          rw [ih (fun x hx => hpos x (by simp [hx]))
            (fun x hx => hlt x (by simp [hx]))]
          simp only [blockDigits, Nat.digitsAppend, List.append_assoc]

/-- The Brockhaus-Seidov conjecture for OEIS A133901: its members are unbounded. -/
theorem brockhaus_seidov_a133901 : ∀ B : ℕ, ∃ p, B < p ∧ IsMember p := by
  intro B
  let j := B + 5
  let t := 10 ^ j
  let p := 100 * t ^ 4 + 110 * t ^ 3 + 90 * t ^ 2 + 11 * t + 1
  let q := p - 99 * t ^ 2
  let pBlocks : List ℕ := [1, 11, 90, 110, 100]
  let pSqBlocks : List ℕ :=
    [1, 22, 301, 2200, 10720, 22000, 30100, 22000, 10000]
  let qSqBlocks : List ℕ :=
    [1, 22, 103, 22, 2701, 220, 10300, 22000, 10000]

  have ht : 10 ^ 5 ≤ t := by
    dsimp [t, j]
    exact pow_le_pow_right' (a := 10) (n := 5) (m := B + 5)
      (by norm_num) (by omega)
  have htpos : 0 < t := by positivity
  have htOne : 1 ≤ t := htpos
  have hBlt : B < t := by
    calc
      B < 2 ^ B := B.lt_two_pow_self
      _ ≤ 10 ^ B := Nat.pow_le_pow_left (by norm_num) B
      _ ≤ 10 ^ (B + 5) := pow_le_pow_right' (by norm_num) (by omega)
      _ = t := by rfl

  have hpRepr : Nat.ofDigits t pBlocks = p := by
    dsimp [pBlocks, p]
    norm_num [Nat.ofDigits]
    ring
  have hpDigits : Nat.digits 10 p = blockDigits j pBlocks := by
    rw [← hpRepr]
    apply digits_of_pow_blocks
    · intro a ha
      simp [pBlocks] at ha
      omega
    · intro a ha
      simp [pBlocks] at ha
      omega
  have hpBlockPalindrome : (blockDigits j pBlocks).reverse = blockDigits j pBlocks := by
    dsimp [j, pBlocks]
    let z := List.replicate (B + 4) 0
    have hform :
        blockDigits (B + 5) [1, 11, 90, 110, 100] =
          [1] ++ z ++ [1, 1] ++ z ++ [9] ++ z ++ [1, 1] ++ z ++ [1] := by
      simp [blockDigits, Nat.digitsAppend, z, List.replicate_add, List.append_assoc]
    rw [hform]
    simp [z, List.reverse_append, List.reverse_replicate, List.append_assoc]
  have hpPalindrome : IsPalindrome10 p := by
    simp only [IsPalindrome10, rev10]
    rw [hpDigits, hpBlockPalindrome, ← hpDigits, Nat.ofDigits_digits]

  have hpSqRepr : Nat.ofDigits t pSqBlocks = p ^ 2 := by
    dsimp [pSqBlocks, p]
    norm_num [Nat.ofDigits]
    ring
  have hpSqDigits : Nat.digits 10 (p ^ 2) = blockDigits j pSqBlocks := by
    rw [← hpSqRepr]
    apply digits_of_pow_blocks
    · intro a ha
      simp [pSqBlocks] at ha
      omega
    · intro a ha
      simp [pSqBlocks] at ha
      omega

  have htPowers : t ^ 2 ≤ t ^ 4 := pow_le_pow_right' htOne (by norm_num)
  have htFourPos : 0 < t ^ 4 := by positivity
  have hdeltaCore : 99 * t ^ 2 < 100 * t ^ 4 := by nlinarith
  have hdelta : 99 * t ^ 2 < p := by
    dsimp [p]
    omega
  have hqpos : 0 < q := by
    change 0 < p - 99 * t ^ 2
    exact Nat.sub_pos_of_lt hdelta
  have hqLt : q < p := by
    change p - 99 * t ^ 2 < p
    exact Nat.sub_lt (by omega) (by positivity)
  have hqCast : (q : ℤ) = (p : ℤ) - 99 * (t : ℤ) ^ 2 := by
    dsimp [q]
    rw [Nat.cast_sub hdelta.le]
    push_cast
    rfl
  have hqSqRepr : Nat.ofDigits t qSqBlocks = q ^ 2 := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hqCast]
    dsimp [qSqBlocks, p]
    norm_num [Nat.ofDigits]
    ring
  have hqSqDigits : Nat.digits 10 (q ^ 2) = blockDigits j qSqBlocks := by
    rw [← hqSqRepr]
    apply digits_of_pow_blocks
    · intro a ha
      simp [qSqBlocks] at ha
      omega
    · intro a ha
      simp [qSqBlocks] at ha
      omega

  have hSqBlockReverse : (blockDigits j pSqBlocks).reverse = blockDigits j qSqBlocks := by
    dsimp [j, pSqBlocks, qSqBlocks]
    let z := List.replicate B 0
    have hpad (n : ℕ) (hn : n < 10 ^ 5) :
        Nat.digitsAppend 10 (B + 5) n = Nat.digitsAppend 10 5 n ++ z := by
      have hlen : (Nat.digits 10 n).length ≤ 5 :=
        (Nat.digits_length_le_iff (by norm_num) n).2 hn
      simp only [Nat.digitsAppend, z]
      rw [show B + 5 - (Nat.digits 10 n).length =
        (5 - (Nat.digits 10 n).length) + B by omega]
      rw [List.replicate_add, List.append_assoc]
    simp only [blockDigits]
    rw [hpad 1 (by norm_num), hpad 22 (by norm_num), hpad 301 (by norm_num),
      hpad 2200 (by norm_num), hpad 10720 (by norm_num), hpad 22000 (by norm_num),
      hpad 30100 (by norm_num), hpad 103 (by norm_num), hpad 2701 (by norm_num),
      hpad 220 (by norm_num), hpad 10300 (by norm_num)]
    simp [Nat.digitsAppend, z, List.reverse_append, List.reverse_replicate,
      List.append_assoc]
  have hreverseSquare : rev10 (p ^ 2) = q ^ 2 := by
    simp only [rev10]
    rw [hpSqDigits, hSqBlockReverse, ← hqSqDigits, Nat.ofDigits_digits]
  have hpSquareNotPalindrome : ¬IsPalindrome10 (p ^ 2) := by
    intro hpal
    have hpq : p ^ 2 = q ^ 2 := by
      rw [← hreverseSquare]
      exact hpal.symm
    have hlt : q ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hqLt (by norm_num)
    omega

  refine ⟨p, ?_, hpPalindrome, hpSquareNotPalindrome, q, hreverseSquare⟩
  have htLeFourth : t ≤ t ^ 4 := Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) t
  dsimp [p]
  omega

#print axioms brockhaus_seidov_a133901

end D5.S1.Digit.Admissibility.PalindromeSquareReversalInfinitude
