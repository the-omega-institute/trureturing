/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Endpoint
   mirror-E: none(waiver:source-equivalence-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical order and a literal numeric ear throughout the complete independent equal-first-three family. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Hard
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Large

/-! All independent s,d >= 2 are covered; the unrestricted four-gap problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private natural_slices from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Natural
open private lower from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Lower
open private hard from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Hard
open private large from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Large

theorem actualSource_equal_first_three_joint_lift (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d) :
    ∃ sigma : List (Fin (3*s+d)), ∃ cut : ℕ, cut ≤ 3*s+d ∧
      OriginalOrder (3*s+d) (1+2^s+2^(2*s)+2^(3*s)) sigma ∧
      OriginalOrder (3*s+d+1) (2*(1+2^s+2^(2*s)+2^(3*s)))
        (earWord (3*s+d) sigma cut) := by
  change ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut ≤ rank s d ∧
    OriginalOrder (rank s d) (amplitude s) sigma ∧
    OriginalOrder (rank s d+1) (2*amplitude s) (earWord (rank s d) sigma cut)
  by_cases hds : d<s
  · by_cases hwindow : s≤2*d-1
    · exact lower s d hd hds hwindow
    · exact hard s d hd (by omega)
  · by_cases heq : d=s
    · exact natural_slices s d hs hd (Or.inl heq)
    · by_cases hcritical : d=s+1
      · exact natural_slices s d hs hd (Or.inr hcritical)
      · exact large s d hs (by omega)

#print axioms actualSource_equal_first_three_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
