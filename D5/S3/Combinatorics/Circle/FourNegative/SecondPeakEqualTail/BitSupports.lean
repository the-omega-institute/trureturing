/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/BitSupports
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Actual sparse high bits and even low stocks for all selector branches. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation

/-! Native bit containment, including the sparse small-parameter stocks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open private Submask full_submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private scaled_bits from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks

private theorem submask_iff (j m : ℕ) :
    Submask j m ↔ ∀ i, j.testBit i=true → m.testBit i=true := by
  simp only [Submask,Finset.subset_iff,List.mem_toFinset,Nat.mem_bitIndices]

private theorem zero_submask (m : ℕ) : Submask 0 m := by
  rw [submask_iff]
  simp

private theorem shift_submask (r j m : ℕ) (hj : Submask j m) :
    Submask (2^r*j) (2^r*m) := by
  dsimp [Submask] at *
  rw [scaled_bits,scaled_bits]
  exact Finset.image_mono (r+·) hj

private theorem submask_add_high (k j m : ℕ)
    (hj : j<2^k) (hm : m<2^k) (hsub : Submask j m) :
    Submask (2^k+j) (2^k+m) := by
  rw [submask_iff] at hsub ⊢
  intro i hi
  have htj := Nat.testBit_two_pow_mul_add 1 hj i
  have htm := Nat.testBit_two_pow_mul_add 1 hm i
  simp only [Nat.mul_one] at htj htm
  rw [htj] at hi
  rw [htm]
  by_cases hik : i<k
  · simp only [hik,ite_true] at hi ⊢
    exact hsub i hi
  · simpa only [hik,ite_false] using hi

private theorem even_low_bit (r e : ℕ) (he : e<r) :
    Submask (2^(e+1)) (2*(2^r-1)) := by
  have hs : Submask (2^e) (2^r-1) :=
    full_submask r (2^e) (Nat.pow_lt_pow_right (by decide : 1<2) he)
  have hh := shift_submask 1 _ _ hs
  simpa only [pow_one,pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_comm] using hh

private theorem small_less_submask (r ellExp : ℕ) (hr : 1≤r) (he : ellExp<r) :
    Submask (2^(r+ellExp+1)+2^(ellExp+1))
      (2^(r+ellExp+1)+2*(2^r-1)) := by
  have hm : 2*(2^r-1)<2^(r+ellExp+1) := by
    have hp := Nat.two_pow_pos r
    have hh : r+1≤r+ellExp+1 := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) hh
    rw [pow_succ] at hpow
    omega
  have hj : 2^(ellExp+1)<2^(r+ellExp+1) :=
    Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  exact submask_add_high _ _ _ hj hm (even_low_bit r ellExp he)

private theorem small_ge_submask (r ellExp : ℕ) (hr : 1≤r) (he : r≤ellExp) :
    Submask (2^(r+ellExp+1)+2^(ellExp+1))
      (2^(r+ellExp+1)+(2^(ellExp+1)+2*(2^r-1))) := by
  have hlo : 2*(2^r-1)<2^(ellExp+1) := by
    have hp := Nat.two_pow_pos r
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) he
    rw [pow_succ]
    omega
  have hinner : Submask (2^(ellExp+1)) (2^(ellExp+1)+2*(2^r-1)) := by
    simpa only [Nat.add_zero] using
      submask_add_high (ellExp+1) 0 (2*(2^r-1)) (Nat.two_pow_pos _) hlo (zero_submask _)
  have hp : 2^(ellExp+1)<2^(r+ellExp+1) :=
    Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  have hm : 2^(ellExp+1)+2*(2^r-1)<2^(r+ellExp+1) := by
    have hpow := Nat.pow_le_pow_right (by decide : 0<2)
      (show ellExp+2≤r+ellExp+1 by omega)
    rw [show ellExp+2=(ellExp+1)+1 by omega,pow_succ] at hpow
    omega
  exact submask_add_high _ _ _ hp hm hinner

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
