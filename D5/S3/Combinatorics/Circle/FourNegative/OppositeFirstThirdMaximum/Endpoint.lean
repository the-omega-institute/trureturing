/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Endpoint
   generality: I
   mirror-B: none(waiver:source-bound-dependent-family-registration)
   mirror-E: none(waiver:source-bound-dependent-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full original opposite first/third maximum joint lift, literal ear, all natural repeated prefixes and both zero totals. -/
import D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private choose_mask from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Arithmetic
open private physical_joint from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Physical
open private repeated_prefixes from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Endpoint
open private strip_of_prefix from D5.S3.Combinatorics.Circle.PeriodicShortening

/-- The original four-parameter family; c is retained in the telescope and seed.
The fresh physical label k is inserted into the same old permutation. -/
theorem actualSource_opposite_first_third_maximum_joint_lift
    (a b c d : Nat) (hb : 2≤b) (hd : 2≤d) (hca : c=a)
    (hba : b<a) (hda : d<a) (hreg : b<d ∨ d+2≤b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : Nat, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : Nat,
        (((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : Nat,
        (((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : Nat,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  subst c
  obtain ⟨mask,hmask,hmargins⟩ := choose_mask a b d hb hd hba hda hreg
  obtain ⟨sigma,j,hj,ho,hn⟩ := physical_joint a b d mask (decide (b<d))
    hb hd hba hda hmask hmargins
  have oldstrip : InStrip (actualSource (a+b+a+d)
      (1+2^a+2^(a+b)+2^(a+b+a))) (modulus (a+b+a+d)/2) 0 sigma := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using ho.2.2 n
  have hhalf : modulus (a+b+a+d+1)/2=modulus (a+b+a+d) := by
    have hp : (2:ℤ)^(a+b+a+d+1)=2*(2:ℤ)^(a+b+a+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  have newstrip : InStrip (actualSource (a+b+a+d+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+a)))) (modulus (a+b+a+d+1)/2) 0
      (earWord (a+b+a+d) sigma j) := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using hn.2.2 n
  obtain ⟨oldAll,oldZero⟩ := repeated_prefixes _ _ _ oldstrip ho.2.1
  obtain ⟨newAll,newZero⟩ := repeated_prefixes _ _ _ newstrip hn.2.1
  refine ⟨sigma,j,hj,ho,hn,?_,?_,?_⟩
  · intro m n
    simpa only [Set.mem_Icc] using oldAll m n
  · intro m n
    simpa only [hhalf,Set.mem_Icc] using newAll m n
  · intro m
    exact ⟨oldZero m,newZero m⟩

end D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
