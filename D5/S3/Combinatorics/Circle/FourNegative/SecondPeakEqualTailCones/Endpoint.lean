/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Endpoint
   generality: I
   mirror-B: none(waiver:substantive-native-cone-theorem)
   mirror-E: Reg/D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Endpoint
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Three equal-tail cones with adaptive old masks and a new native ceiling. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerSchedule
/-! One three-clause theorem. Unrestricted four-gap J/C3.1 remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Endpoint
open PeriodicShortening RunFirstEarTransport
open private rank amplitude
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private physical_finish
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Schedule
open private lower_physical_finish
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerSchedule

/-- One physical permutation and one late fresh insertion on the full union of cones. -/
theorem actualSource_second_peak_equal_tail_cones_joint_lift
    (a b s : ℕ) (hs : 2≤s)
    (hcone : ((2*s+2≤a ∧ a+1≤b) ∨ (s+1≤a ∧ max (a+1) (3*s+1)≤b)) ∨
      (2≤a ∧ a+1≤s ∧ 2*s+1≤b)) :
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) := by
  rcases hcone with hold|hlower
  · exact physical_finish a b s hs hold
  · exact lower_physical_finish a b s hs hlower.1 hlower.2.1 hlower.2.2

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Endpoint
