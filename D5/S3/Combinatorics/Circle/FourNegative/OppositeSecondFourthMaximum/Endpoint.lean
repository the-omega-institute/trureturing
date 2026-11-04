/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeSecondFourthMaximum/Endpoint
   generality: I
   mirror-B: none(waiver:source-family-registration)
   mirror-E: none(waiver:source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original opposite second/fourth strict maximum face, literal ear, both zero totals and all repetitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Endpoint

/-! Joint prefix bounds in the original physical coordinates and both strict sectors. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private selection from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum.Arithmetic
open private physical_joint from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum.Physical
open private repeated_prefixes from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Endpoint
open private strip_of_prefix from D5.S3.Combinatorics.Circle.PeriodicShortening

theorem actualSource_opposite_second_fourth_maximum_joint_lift
    (a b c d : Nat) (ha : 2 <= a) (hc : 2 <= c) (hbd : b = d)
    (hab : a < b) (hcb : c < b) (hne : a ≠ c) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : Nat, j <= a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : Nat,
        ((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : Nat,
        ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : Nat,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum = 0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum = 0) := by
  subst d
  obtain ⟨m,n,hm,hn,hw⟩ := selection a b c ha hc hab hcb hne
  obtain ⟨sigma,j,hj,ho,he⟩ := physical_joint a b c m n (decide (c<a))
    ha (by omega) hc hm hn hw
  have oldstrip : InStrip (actualSource (a+b+c+b)
      (1+2^a+2^(a+b)+2^(a+b+c))) (modulus (a+b+c+b)/2) 0 sigma := by
    apply strip_of_prefix
    intro r
    simpa only [zero_add,Set.mem_Icc] using ho.2.2 r
  have newstrip : InStrip (actualSource (a+b+c+b+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+c)))) (modulus (a+b+c+b+1)/2) 0
      (earWord (a+b+c+b) sigma j) := by
    apply strip_of_prefix
    intro r
    simpa only [zero_add,Set.mem_Icc] using he.2.2 r
  have hhalf : modulus (a+b+c+b+1)/2=modulus (a+b+c+b) := by
    have hp : (2:ℤ)^(a+b+c+b+1)=2*(2:ℤ)^(a+b+c+b) := by rw [pow_succ];ring
    dsimp [modulus]
    rw [hp]
    omega
  obtain ⟨oldAll,oldZero⟩ := repeated_prefixes _ _ _ oldstrip ho.2.1
  obtain ⟨newAll,newZero⟩ := repeated_prefixes _ _ _ newstrip he.2.1
  refine ⟨sigma,j,hj,ho,he,?_,?_,?_⟩
  · intro h r
    simpa only [Set.mem_Icc] using oldAll h r
  · intro h r
    simpa only [hhalf,Set.mem_Icc] using newAll h r
  · intro h
    exact ⟨oldZero h,newZero h⟩

end D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum
