/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Endpoint
   mirror-E: none(waiver:physical-two-parameter-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A literal joint-prefix family for every s at least two and a at least s. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Strict
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Equal

/-! The high-X construction for a>=2s is due to Pro task
b882f14d-1d25-4689-b46f-9960312490d7. The extension to every a > s
and the separate equality construction are due to the caller.
Unrestricted physical four - gap J and Circle C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source
open private strict from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Strict
open private equal from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Equal

theorem actualSource_equal_last_three_upper_joint_lift (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a) :
    ∃ sigma : List (Fin (a + 3 * s)), 
      sigma.map Fin.val =
        (if a = s then List.range (a + 3 * s) else
          List.range' (a + 2 * s - 1) (s + 1) ++ List.range (3 * s - 1) ++
            List.range' (3 * s) (a - s - 1) ++ [3 * s - 1]) ∧
      (if a = s then s - 1 else 3 * s) ≤ a + 3 * s ∧
      OriginalOrder (a + 3 * s) (1 + 2 ^ a + 2 ^ (a + s) + 2 ^ (a + 2 * s)) sigma ∧
      OriginalOrder (a + 3 * s + 1) (2 * (1 + 2 ^ a + 2 ^ (a + s) + 2 ^ (a + 2 * s)))
        (earWord (a + 3 * s) sigma (if a = s then s - 1 else 3 * s)) := by
  by_cases heq : a = s
  · subst a
    simpa [rank, amplitude] using equal s hs
  · simpa only [ite_eq_right heq, rank, amplitude] using strict a s hs (by omega)

#check actualSource_equal_last_three_upper_joint_lift
#print axioms actualSource_equal_last_three_upper_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
