/- GID: D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/CarrylessMultiplierEquivalence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Data.Nat.EvenOddRec]
   utility: kind=checker; basis=terminal=gid:D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result; instance=D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.related; result=D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result
   digest: Equivalence of two ordinary versus binary carryless multiplier equations. -/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Ordinary and binary carryless multiplier equations -/

namespace D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

/-- Binary polynomial multiplication: adjoining a low zero shifts the product,
and adjoining a low one also adds the other factor by exclusive OR. -/
def binaryProduct (u k : ℕ) : ℕ :=
  k.evenOddRec 0 (fun _ r => 2 * r) (fun _ r => (2 * r) ^^^ u)

private theorem binaryProduct_zero (u : ℕ) : binaryProduct u 0 = 0 := rfl

private theorem binaryProduct_even (u n : ℕ) : binaryProduct u (2*n) = 2*binaryProduct u n := by
  unfold binaryProduct
  rw [Nat.evenOddRec_even (H := by rfl)]

private theorem binaryProduct_odd (u n : ℕ) :
    binaryProduct u (2*n+1) = (2*binaryProduct u n) ^^^ u := by
  unfold binaryProduct
  rw [Nat.evenOddRec_odd (H := by rfl)]

/-- The coefficient of the binary convolution, expressed as a parity. -/
private def convolutionDigit (u k t : ℕ) : ℕ :=
  (∑ i ∈ Finset.range (t+1), (u.testBit i).toNat * (k.testBit (t-i)).toNat) % 2

private theorem bit_low (n : ℕ) (b : Bool) :
    (2*n+b.toNat).testBit 0 = b := by
  cases b <;> simp [Nat.testBit_zero]

private theorem bit_high (n t : ℕ) (b : Bool) :
    (2*n+b.toNat).testBit (t+1) = n.testBit t := by
  simpa only [Nat.bit_val, Nat.succ_eq_add_one] using Nat.testBit_bit_succ t b n

private theorem convolution_low (u n : ℕ) (b : Bool) :
    convolutionDigit u (2*n+b.toNat) 0 =
      ((u.testBit 0).toNat*b.toNat)%2 := by
  simp only [convolutionDigit, Nat.zero_add, Finset.sum_range_one, Nat.sub_self, bit_low]

private theorem convolution_high (u n t : ℕ) (b : Bool) :
    convolutionDigit u (2*n+b.toNat) (t+1) =
      (convolutionDigit u n t + (u.testBit (t+1)).toNat*b.toNat)%2 := by
  unfold convolutionDigit
  rw [Finset.sum_range_succ]
  have hh : (∑ i ∈ Finset.range (t+1),
      (u.testBit i).toNat * ((2*n+b.toNat).testBit (t+1-i)).toNat) =
      ∑ i ∈ Finset.range (t+1), (u.testBit i).toNat * (n.testBit (t-i)).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show t+1-i = (t-i)+1 by omega, bit_high]
  rw [hh]
  rw [Nat.sub_self, bit_low]
  omega

private theorem xor_digit (a b : Bool) :
    (bne a b).toNat = (a.toNat+b.toNat)%2 := by
  cases a <;> cases b <;> rfl

private theorem binaryProduct_spec (u k t : ℕ) :
    ((binaryProduct u k).testBit t).toNat = convolutionDigit u k t := by
  induction k using Nat.evenOddRec generalizing t with
  | h0 => simp [binaryProduct_zero, convolutionDigit]
  | h_even n ih =>
    rw [binaryProduct_even]
    cases t with
    | zero => simpa using (convolution_low u n false).symm
    | succ t =>
      rw [show (2*binaryProduct u n).testBit (t+1) =
        (binaryProduct u n).testBit t by simpa using bit_high (binaryProduct u n) t false]
      have hc := convolution_high u n t false
      simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at hc
      rw [hc, ih]
      simp [convolutionDigit]
  | h_odd n ih =>
    rw [binaryProduct_odd, Nat.testBit_xor, xor_digit]
    cases t with
    | zero =>
      have hzero : (2*binaryProduct u n).testBit 0 = false := by
        simpa using bit_low (binaryProduct u n) false
      have hc := convolution_low u n true
      simp only [Bool.toNat_true, Nat.mul_one] at hc
      rw [hc, hzero]
      cases u.testBit 0 <;> rfl
    | succ t =>
      have hh : (2*binaryProduct u n).testBit (t+1) =
        (binaryProduct u n).testBit t := by
        simpa using bit_high (binaryProduct u n) t false
      rw [hh, ih]
      simpa only [Bool.toNat_true, Nat.mul_one] using (convolution_high u n t true).symm

/-- The natural number encoding the convolution of binary coefficients over GF(2).
The summation includes every pair of nonnegative indices with total degree t. -/
noncomputable def carryless (u k : ℕ) : ℕ :=
  Classical.choose (show ∃ z : ℕ, ∀ t, (z.testBit t).toNat = convolutionDigit u k t from
    ⟨binaryProduct u k, binaryProduct_spec u k⟩)

theorem carryless_eq (u k : ℕ) : carryless u k = binaryProduct u k := by
  apply Nat.eq_of_testBit_eq
  intro t
  have h : ((carryless u k).testBit t).toNat = convolutionDigit u k t :=
    Classical.choose_spec (show ∃ z : ℕ, ∀ t, (z.testBit t).toNat = convolutionDigit u k t from
      ⟨binaryProduct u k, binaryProduct_spec u k⟩) t
  have hh := binaryProduct_spec u k t
  cases ha : (carryless u k).testBit t <;> cases hb : (binaryProduct u k).testBit t <;>
    simp_all <;> omega

abbrev State := Option (ℕ × ℕ)

def holds (u m : ℕ) (s : State) (k : ℕ) : Prop :=
  match s with
  | none => False
  | some (c,d) => m*k+c = binaryProduct u k ^^^ d

instance (u m : ℕ) (s : State) (k : ℕ) : Decidable (holds u m s k) := by
  cases s with
  | none => exact isFalse id
  | some p => exact inferInstanceAs (Decidable (m*k+p.1 = binaryProduct u k ^^^ p.2))

def step (u m : ℕ) (s : State) (b : Bool) : State :=
  match s with
  | none => none
  | some (c,d) =>
    let e := (if b then u else 0) ^^^ d
    let v := m*b.toNat+c
    if v%2 = e%2 then some (v/2,e/2) else none

private theorem split_eq (x y c e : ℕ) :
    2*y+c = (2*x) ^^^ e ↔
      c%2=e%2 ∧ y+c/2 = x ^^^ (e/2) := by
  have hd : ((2*x) ^^^ e)/2 = x ^^^ (e/2) := by
    simp [Nat.xor_div_two]
  have hm : ((2*x) ^^^ e)%2 = e%2 := by
    rw [Nat.xor_mod_two_eq]
    omega
  omega

theorem holds_step (u m : ℕ) (s : State) (b : Bool) (n : ℕ) :
    holds u m s (2*n+b.toNat) ↔ holds u m (step u m s b) n := by
  cases s with
  | none => simp [holds, step]
  | some s =>
    rcases s with ⟨c,d⟩
    have hbit : binaryProduct u (2*n+b.toNat) =
        (2*binaryProduct u n) ^^^ (if b then u else 0) := by
      cases b <;> simp [binaryProduct_even, binaryProduct_odd]
    simp only [holds, hbit, Nat.xor_assoc]
    have hr : m*(2*n+b.toNat)+c = 2*(m*n)+(m*b.toNat+c) := by ring
    rw [hr, split_eq]
    simp only [step]
    split_ifs <;> simp_all [holds]

private def related : Finset (State × State) := {
  (some (0, 0), some (0, 0)),
  (some (4, 12), some (7, 9)),
  (some (2, 6), some (3, 4)),
  (some (6, 10), some (11, 13)),
  (some (1, 3), none),
  (some (5, 15), none),
  (some (3, 5), some (5, 6)),
  (some (7, 9), some (13, 15)),
  (some (0, 1), none),
  (some (5, 13), none),
  (some (2, 7), none),
  (some (7, 11), none),
  (some (1, 2), none),
  (some (6, 14), none),
  (some (3, 4), some (6, 7)),
  (some (8, 8), some (14, 14)),
  (none, none),
  (some (2, 6), none),
  (some (7, 10), none),
  (some (3, 5), none),
  (some (8, 9), none),
  (some (3, 7), none),
  (some (4, 4), some (7, 7)),
  (some (6, 15), none),
  (some (2, 2), some (3, 3)),
  (some (6, 14), some (11, 10)),
  (some (1, 1), some (1, 1)),
  (some (5, 13), some (9, 8)),
  (some (5, 12), some (8, 9))
}

private theorem related_final : ∀ p ∈ related,
    holds 25 9 p.1 0 ↔ holds 19 15 p.2 0 := by
  decide

private theorem related_step : ∀ p ∈ related, ∀ b : Bool,
    (step 25 9 p.1 b, step 19 15 p.2 b) ∈ related := by
  decide

private theorem related_equiv (k : ℕ) : ∀ p ∈ related,
    holds 25 9 p.1 k ↔ holds 19 15 p.2 k := by
  induction k using Nat.evenOddRec with
  | h0 => exact related_final
  | h_even n ih =>
    intro p hp
    simpa using (holds_step 25 9 p.1 false n).trans
      ((ih _ (related_step p hp false)).trans (holds_step 19 15 p.2 false n).symm)
  | h_odd n ih =>
    intro p hp
    simpa using (holds_step 25 9 p.1 true n).trans
      ((ih _ (related_step p hp true)).trans (holds_step 19 15 p.2 true n).symm)

/-- For every natural number, including zero, the two multiplier equations agree. -/
theorem result (k : ℕ) :
    9*k = carryless 25 k ↔ 15*k = carryless 19 k := by
  simp only [carryless_eq]
  have h := related_equiv k (some (0,0), some (0,0)) (by decide)
  simpa [holds] using h

#print axioms result

end D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence
