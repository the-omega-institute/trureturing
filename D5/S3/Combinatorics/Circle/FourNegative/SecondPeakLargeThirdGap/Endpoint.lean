/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A native ceiling joint lift in four independent unbounded gap parameters. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Schedule

/-! A physical joint lift on the separated gap cone. The unrestricted problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open private joint_construction
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Schedule

/-- A single permutation and a single literal cut for both full physical source rows. -/
theorem actualSource_second_peak_large_third_gap_joint_lift (a b c d : ℕ)
    (ha : 2 ≤ a) (had : a+1 ≤ d) (hdc : a+d+1 ≤ c) (hcb : c+1 ≤ b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j ≤ a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  obtain ⟨sigma,hold,hnew⟩ := joint_construction a b c d ha had hdc hcb
  exact ⟨sigma,0,by omega,hold,hnew⟩

#print axioms actualSource_second_peak_large_third_gap_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
