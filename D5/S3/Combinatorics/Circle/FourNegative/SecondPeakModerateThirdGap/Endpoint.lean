/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Endpoint
   digest: complete source-only moderate-c endpoint with one physical permutation and one ear cut. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open private joint_construction
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Schedule
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/--
The full natural moderate-c sector
`2 ≤ a < d < c < b` and `c ≤ a+d`.  The same physical `sigma` is used
in both rows; the fresh label is inserted at the selector's literal cut.
-/
theorem actualSource_second_peak_moderate_third_gap_joint_lift (a b c d : ℕ)
    (ha : 2 ≤ a) (had : a < d) (hdc : d < c) (hcb : c < b)
    (hmoder : c ≤ a+d) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j ≤ a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ,
        (((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ,
        (((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
          (actualSource (a+b+c+d+1)
            (2*(1+2^a+2^(a+b)+2^(a+b+c)))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1)
            (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  obtain ⟨l,hl,hold,j,hj,hnew⟩ :=
    joint_construction a b c d ha had hdc hcb hmoder
  obtain ⟨sigma,j,hj,ho,hn⟩ :=
    (actual_nat_joint_iff a b c d ha (by omega) (by omega) (by omega)).mpr
      ⟨l,hl,hold,j,hj,hnew⟩
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _
    (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    have hp : (2:ℤ)^(a+b+c+d+1)=2*(2:ℤ)^(a+b+c+d) := by
      rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_second_peak_moderate_third_gap_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
