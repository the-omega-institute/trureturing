/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryConstruction
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-physical-boundary-constructions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical dyadic masks and packet certificates on the upper-gap boundary. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryMargins

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private standard_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets
open private rising_margins swapped_margins tied_margins all_equal_margins
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryMargins

private theorem one_mask_capacity (n : ℕ) (hn : 2≤n) : 1<2^n := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) hn
  norm_num at h
  omega

private theorem interval_capacity (n k : ℕ) (hk : k≤n) : 2^k-1<2^n := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) hk
  have hp := Nat.two_pow_pos k
  omega

private theorem singleton_capacity (n k : ℕ) (hk : k<n) : 2^k<2^n :=
  Nat.pow_lt_pow_right (by decide) hk

private theorem rising_certificate (a b c : ℕ) (ha : 2≤a) (hab : a<b) (hbc : b<c) :
    Nonempty (Certificate a b c (c+1)) := by
  apply standard_certificate a b c (c+1) 1 0 (2^(c-b)-1) 0 (2^(b-a-1))
    ha (by omega) (by omega) (by omega)
  · exact one_mask_capacity c (by omega)
  · positivity
  · exact interval_capacity (c-1) (c-b) (by omega)
  · positivity
  · exact singleton_capacity (b-1) (b-a-1) (by omega)
  · intro e _ he; simp at he
  · intro e _ he; simp at he
  · exact rising_margins a b c ha hab hbc

private theorem swapped_certificate (a b c : ℕ) (hb : 2≤b) (hba : b<a) (hac : a<c) :
    Nonempty (Certificate a b c (c+1)) := by
  apply standard_certificate a b c (c+1) 1 1 (2^(c-b-1)-1) (2^(c-a-1)) 0
    (by omega) hb (by omega) (by omega)
  · exact one_mask_capacity c (by omega)
  · exact one_mask_capacity c (by omega)
  · exact interval_capacity (c-1) (c-b-1) (by omega)
  · exact singleton_capacity (c-1) (c-a-1) (by omega)
  · positivity
  · intro e _ he; exact he
  · intro e _ he
    have heq : e=c-a-1 := by
      have ht : c-a-1=e := of_decide_eq_true (by simpa only [Nat.testBit_two_pow] using he)
      exact ht.symm
    subst e
    simp [Nat.testBit_two_pow_sub_one,show c-a-1<c-b-1 by omega]
  · exact swapped_margins a b c hb hba hac

private theorem tied_certificate (a b : ℕ) (hb : 2≤b) (hba : b<a) :
    Nonempty (Certificate a b a (a+1)) := by
  apply standard_certificate a b a (a+1) 1 1 (2^(a-b-1)-1) 0 0
    (by omega) hb (by omega) (by omega)
  · exact one_mask_capacity a (by omega)
  · exact one_mask_capacity a (by omega)
  · exact interval_capacity (a-1) (a-b-1) (by omega)
  · positivity
  · positivity
  · intro e _ he; exact he
  · intro e _ he; simp at he
  · exact tied_margins a b hb hba

private theorem all_equal_certificate (a : ℕ) (ha : 2≤a) :
    Nonempty (Certificate a a a (a+1)) := by
  apply standard_certificate a a a (a+1) 0 0 0 0 0 ha ha ha (by omega)
  · positivity
  · positivity
  · positivity
  · positivity
  · positivity
  · intro e _ he; simp at he
  · intro e _ he; simp at he
  · exact all_equal_margins a ha

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
