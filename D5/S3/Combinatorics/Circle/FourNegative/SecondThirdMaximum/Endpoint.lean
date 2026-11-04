/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Endpoint
   generality: I
   mirror-B: none(waiver:source-bound-dependent-family-registration)
   mirror-E: none(waiver:source-bound-dependent-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original four-parameter equal second-third maximum source, literal ear, all repeats and both zero totals. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! The unrestricted Circle J/C3.1 four-negative objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private physical_joint
  from D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum.Physical
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- One original physical permutation, one literal fresh insertion, the two
complete OriginalOrder predicates, every natural repeat/flatten/take window,
and separately zero totals for every finite old and enlarged repetition.
The independent parameters and the equality hypothesis are kept in the source
telescope; there is no selector-feasibility or finite-range premise. -/
theorem actualSource_second_third_maximum_joint_lift (a b c d : Nat)
    (ha : 2 <= a) (had : a < d) (hdb : d < b) (hbc : b = c) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : Nat, j <= a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : Nat, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : Nat, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : Nat,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  subst c
  obtain ⟨sigma,j,hj,ho,hn⟩ := physical_joint a b d ha had hdb
  have oldPeriods (m : Nat) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have newPeriods (m : Nat) := zero_period_transport _ _ (earWord (a+b+b+d) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+b+d+1)/2=modulus (a+b+b+d) := by
    have hp : (2:ℤ)^(a+b+b+d+1)=2*(2:ℤ)^(a+b+b+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (oldPeriods m).2,
    fun m n => by simpa only [half] using (newPeriods m).2 n,
    fun m => ⟨(oldPeriods m).1,(newPeriods m).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum
