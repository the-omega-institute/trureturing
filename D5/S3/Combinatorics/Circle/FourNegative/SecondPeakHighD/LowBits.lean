/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: LowBits and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Algebra
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open private multiple_predecessor_bits
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding

def Submask (m M : ℕ) : Prop := ∀ e : ℕ, m.testBit e=true → M.testBit e=true

theorem bit_below (m k e : ℕ) (hm : m<2^k) (he : m.testBit e=true) : e<k := by
  by_contra hn
  have hp : 2^k≤(2:ℕ)^e := Nat.pow_le_pow_right (by decide) (by omega)
  have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm hp)
  rw [hf] at he
  contradiction

theorem submask_le (m M : ℕ) (hs : Submask m M) : m≤M := by
  have sub : m.bitIndices.toFinset⊆M.bitIndices.toFinset := by
    intro e he
    simp only [List.mem_toFinset,Nat.mem_bitIndices] at he ⊢
    exact hs e he
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg sub
    (fun e _ _ => Nat.zero_le ((2:ℕ)^e))
  simpa only [Finset.sum_toFinset_bitIndices_two_pow] using hsum

theorem submask_of_land (m M : ℕ) (h : m &&& M=m) : Submask m M := by
  intro e he
  have hh := congrArg (fun n : ℕ => n.testBit e) h
  simp only [Nat.testBit_and,he,Bool.true_and] at hh
  exact hh

theorem submask_high_block (k n c m : ℕ) (hc : c<2^k)
    (hm : m<2^k) (hs : Submask m c) : Submask m (2^k*n+c) := by
  intro e he
  have hek := bit_below m k e hm he
  have hmod : (2^k*n+c)%2^k=c := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hc]
  have ht := congrArg (fun z : ℕ => z.testBit e) hmod
  simp only [Nat.testBit_mod_two_pow,hek,decide_true,Bool.true_and] at ht
  rw [ht]
  exact hs e he

theorem submask_predecessor (k n m : ℕ) (hn : 1≤n) (hm : m<2^k) :
    Submask m (2^k*n-1) := by
  intro e he
  exact multiple_predecessor_bits k n hn e (bit_below m k e hm he)


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
