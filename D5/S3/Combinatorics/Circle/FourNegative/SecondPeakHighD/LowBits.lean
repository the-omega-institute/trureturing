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

theorem submask_of_land (m M : ℕ) (h : m &&& M=m) : Submask m M := by
  intro e he
  have hh := congrArg (fun n : ℕ => n.testBit e) h
  simp only [Nat.testBit_and,he,Bool.true_and] at hh
  exact hh

theorem submask_predecessor (k n m : ℕ) (hn : 1≤n) (hm : m<2^k) :
    Submask m (2^k*n-1) := by
  intro e he
  exact multiple_predecessor_bits k n hn e (bit_below m k e hm he)


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
