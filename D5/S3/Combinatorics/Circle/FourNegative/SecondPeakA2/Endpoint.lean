/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Endpoint and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Physical

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open SourceWidth PeriodicShortening RunFirstEarTransport
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- Complete original a=2 near-b physical endpoint, including literal fresh ear,
both OriginalOrder structures, all natural repetitions and all natural takes. -/
theorem actualSource_second_peak_a2_joint_lift (b c d : ℕ)
    (hc : 3≤c) (hd : c+2≤d) (hb : b=d+1 ∨ b=d+2) :
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) ∧
      (∀ r n : ℕ, ((((List.replicate r sigma).flatten).take n).map
        (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d)/2)) ∧
      (∀ r n : ℕ, ((((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).take n).map
        (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d))) ∧
      (∀ r : ℕ,
        (((List.replicate r sigma).flatten).map
          (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum=0 ∧
        (((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).map
          (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hj,ho,hn⟩ := complete_original_orders b c d hc hd hb
  have eo (r : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 r
  have en (r : ℕ) := zero_period_transport _ _ (earWord (2+b+c+d) sigma j) hn.2.1 hn.2.2 r
  have half : modulus (2+b+c+d+1)/2=modulus (2+b+c+d) := by
    have hp : (2:ℤ)^(2+b+c+d+1)=2*(2:ℤ)^(2+b+c+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun r => (eo r).2,
    fun r n => by simpa only [half] using (en r).2 n,
    fun r => ⟨(eo r).1,(en r).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
