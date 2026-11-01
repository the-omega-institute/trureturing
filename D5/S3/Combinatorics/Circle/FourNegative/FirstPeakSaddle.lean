/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle
   generality: I
   mirror-B: none(waiver:strict-saddle-source-ear-existence)
   mirror-E: none(waiver:joint-source-ear-existence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: One literal ear jointly lifts both actual complete source orders for every strict saddle. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Native
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Physical

/-! Complete theorem for all a>b>d>c>=2.
The six exhaustive native arithmetic branches are consumed by the complete
physical constructor. No arithmetic choice or gate is a public hypothesis.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open private native_choice_exists from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Native
open private actualSource_of_nativeChoice from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Physical

/-- All strict saddles: one original physical permutation and one literal cut
give both complete actual orders, retaining every prefix and both zero totals. -/
theorem actualSource_first_peak_saddle_joint_lift
    (a b c d : ℕ) (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut) := by
  obtain ⟨ch⟩ := native_choice_exists a b c d hc hcd hdb hba
  exact actualSource_of_nativeChoice a b c d hc hcd hdb hba ch

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
