/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete original-label physical joint lift for every independent 2<=a<=b=d<c. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Allocation
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! The unrestricted Circle J and C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open SourceWidth PeriodicShortening RunFirstEarTransport
open private strict_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Allocation
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- One old physical permutation, one literal fresh insertion, both complete orders,
all natural repeated prefixes and zero totals for every finite repetition. -/
theorem actualSource_third_peak_equal_second_joint_lift (a b c : ℕ)
    (ha : 2≤a) (hab : a≤b) (hbc : b<c) :
    ∃ sigma : List (Fin (a+b+c+b)), ∃ j : ℕ, j≤a+b+c+b ∧
      OriginalOrder (a+b+c+b) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+b+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+b) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+b) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+b)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+b) sigma j)).flatten).take n).map
        (actualSource (a+b+c+b+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+b))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+b) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+b) sigma j)).flatten).map
          (actualSource (a+b+c+b+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  have hjoint : ∃ sigma : List (Fin (a+b+c+b)), ∃ j : ℕ, j≤a+b+c+b ∧
      OriginalOrder (a+b+c+b) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+b+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+b) sigma j) := by
    by_cases he : a=b
    · subst b
      have hh:=EqualFirstTwoLast.actualSource_equal_first_two_last_joint_lift a c ha (by omega)
      rw [show 3*a+c=a+a+c+a by omega] at hh
      exact hh
    · exact (PacketNormalForm.actual_four_packet_iff a b c b ha (by omega) (by omega) (by omega)).mpr
        (strict_certificate a b c ha (by omega) hbc)
  obtain ⟨sigma,j,hj,ho,hn⟩:=hjoint
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+c+b) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+b+1)/2=modulus (a+b+c+b) := by
    have hp : (2:ℤ)^(a+b+c+b+1)=2*(2:ℤ)^(a+b+c+b) := by rw [pow_succ];ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_third_peak_equal_second_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
