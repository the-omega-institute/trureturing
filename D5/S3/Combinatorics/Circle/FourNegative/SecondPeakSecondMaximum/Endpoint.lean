/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full physical joint lift for independent 2<=c,d<a<=b. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BoundaryCertificates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! The unrestricted Circle J and C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private broad_certificate_exists
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.Broad
open private adjacent_certificate_exists diagonal_certificate_exists
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BoundaryCertificates
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- One old physical permutation, one literal fresh insertion, both complete orders,
all natural repeated prefixes and zero totals for every finite repetition. -/
theorem actualSource_second_peak_second_maximum_joint_lift (a b c d : ℕ)
    (hc : 2≤c) (hd : 2≤d) (hca : c<a) (hda : d<a) (hab : a≤b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  by_cases hdc : d<c
  · exact SecondPeakMiddleGap.actualSource_second_peak_middle_gap_joint_lift a b c d hd hdc hca hab
  have cert : Nonempty (PacketNormalForm.Certificate a b c d) := by
    by_cases heq : c=d
    · subst c
      exact diagonal_certificate_exists a b d hd hda hab
    · by_cases hadj : d=c+1
      · exact adjacent_certificate_exists a b c d hc hadj hda hab
      · exact broad_certificate_exists a b c d hc (by omega) hda hab
  obtain ⟨sigma,j,hj,ho,hn⟩ :=
    (PacketNormalForm.actual_four_packet_iff a b c d (by omega) (by omega) (by omega) hd).mpr
      cert
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    have hp : (2:ℤ)^(a+b+c+d+1)=2*(2:ℤ)^(a+b+c+d) := by rw [pow_succ];ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_second_peak_second_maximum_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
