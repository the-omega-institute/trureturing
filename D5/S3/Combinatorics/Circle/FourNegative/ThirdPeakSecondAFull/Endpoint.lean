/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Endpoint
   generality: I
   mirror-B: none(waiver:physical-dependent-source-registration-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete original full-domain third-peak second-a cone endpoint. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.SourceCertificate
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size sourceMod from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private freshCut from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private physical_order from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.SourceCertificate

open private zero_period_transport from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- One exact original full-domain source endpoint.  The telescope has exactly
nine outer binders: four naturals followed by the five original inequalities. -/
theorem actualSource_third_peak_second_a_full_joint_lift
    (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,
      j=freshCut a b c d ∧ j<a+b+c+d ∧
      OriginalOrder (a+b+c+d)
        (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1)
        (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d)
          (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m
          (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1)
          (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d)
            (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1)
            (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hjcut,hj,ho,hn⟩ :=
    physical_order a b c d hb hba hac hd hda
  have eo := zero_period_transport
    (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))
    (modulus (a+b+c+d)/2) sigma ho.2.1 ho.2.2
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    dsimp [modulus]
    rw [pow_succ]
    omega
  have en := zero_period_transport
    (actualSource (a+b+c+d+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+c))))
    (modulus (a+b+c+d))
    (earWord (a+b+c+d) sigma j) hn.2.1 (by simpa only [half] using hn.2.2)
  refine ⟨sigma,j,hjcut,hj,ho,hn,fun m n => ?_,fun m n => ?_,fun m => ?_⟩
  · exact (eo m).2 n
  · exact (en m).2 n
  · exact ⟨(eo m).1,(en m).1⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
