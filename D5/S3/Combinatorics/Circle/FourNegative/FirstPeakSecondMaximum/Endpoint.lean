/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical joint lift for all a>d>=max(b,c) with b,c at least two. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.AscendingSchedule
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingSchedule
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Endpoint

/-! Physical complementary masks and signed grid allocations control both source rows.
The unrestricted four-gap joint lift and Circle C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private ascending_joint_construction
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.AscendingSchedule
open private descending_joint_construction
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingSchedule

/-- A common physical order and a literal ear cut throughout the first-peak chamber. -/
theorem actualSource_first_peak_second_maximum_joint_lift (a b c d : ℕ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hbd : b ≤ d) (hcd : c ≤ d) (hda : d<a) :
    ∃ sigma : List (Fin (a + b + c + d)), ∃ j : ℕ, j ≤ a + b + c + d ∧ 
      OriginalOrder (a + b + c + d) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧ 
      OriginalOrder (a + b + c + d + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + d) sigma j) := by
  by_cases hbc : b ≤ c
  · have hh : ∃ sigma : List (Fin (a + b + c + d)), ∃ j : ℕ,
        j=(if b=c ∧ c=d then 3 * b else 0) ∧ j ≤ a + b + c + d ∧ 
        OriginalOrder (a + b + c + d) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧ 
        OriginalOrder (a + b + c + d + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
          (earWord (a + b + c + d) sigma j) := by
      by_cases he : b=c ∧ c=d
      · obtain ⟨hbc',hcd'⟩ := he
        subst c
        subst d
        obtain ⟨sigma,_,hj,hold,hnew⟩ :=
          EqualLastThreeUpper.actualSource_equal_last_three_upper_joint_lift a b hb (by omega)
        have hab : a ≠ b := by omega
        simp only [if_neg hab] at hj hnew
        have hk : a + b + b + b=a + 3 * b := by omega
        have hs : a + b + b=a + 2 * b := by omega
        have hres : ∃ sigma : List (Fin (a + 3 * b)), ∃ j : ℕ,
            j=3 * b ∧ j ≤ a + 3 * b ∧ 
            OriginalOrder (a + 3 * b) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + 2 * b)) sigma ∧ 
            OriginalOrder (a + 3 * b + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + 2 * b)))
              (earWord (a + 3 * b) sigma j) := ⟨sigma,3 * b,rfl,hj,hold,hnew⟩
        rw [hk,hs]
        simpa only [eq_self, and_self, ite_true] using hres
      · obtain ⟨sigma,hold,hnew⟩ := ascending_joint_construction a b c d hb hbc hcd hda he
        exact ⟨sigma,0,by simp only [if_neg he],by omega,hold,hnew⟩
    obtain ⟨sigma,j,_,hj,hold,hnew⟩ := hh
    exact ⟨sigma,j,hj,hold,hnew⟩
  · obtain ⟨sigma,hold,hnew⟩ := descending_joint_construction a b c d hc (by omega) hbd hda
    exact ⟨sigma,0,by omega,hold,hnew⟩

#print axioms actualSource_first_peak_second_maximum_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum
