/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Finite and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Small
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QFourStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QEightStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QSixteenStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QThirtyTwoStructural

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private q_two_boundary_good
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

/-- The parameter split consumes scale-unbounded selectors for every q branch. -/
theorem finite_exists (p q h : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)
    (hq : q=2 ∨ q=4 ∨ q=8 ∨ q=16 ∨ q=32) (hh : h=1 ∨ h=2) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before := by
  rcases hp with rfl|rfl|rfl|rfl <;>
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> rcases hh with rfl|rfl
  · exact ⟨5,5,7,false,by simpa using q_two_boundary_good 0⟩
  · exact ⟨5,10,15,false,by simpa using q_two_boundary_good 1⟩
  · simpa using q_four_dyadic_good 2 0 (by omega)
  · simpa using q_four_dyadic_good 2 1 (by omega)
  · simpa using q_eight_dyadic_good 2 0 (by omega)
  · simpa using q_eight_dyadic_good 2 1 (by omega)
  · simpa using q_sixteen_dyadic_good 2 0 (by omega)
  · simpa using q_sixteen_dyadic_good 2 1 (by omega)
  · simpa using q_thirtytwo_dyadic_good 2 0 (by omega)
  · simpa using q_thirtytwo_dyadic_good 2 1 (by omega)
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 3 0 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 3 1 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · simpa using q_four_dyadic_good 3 0 (by omega)
  · simpa using q_four_dyadic_good 3 1 (by omega)
  · simpa using q_eight_dyadic_good 3 0 (by omega)
  · simpa using q_eight_dyadic_good 3 1 (by omega)
  · simpa using q_sixteen_dyadic_good 3 0 (by omega)
  · simpa using q_sixteen_dyadic_good 3 1 (by omega)
  · simpa using q_thirtytwo_dyadic_good 3 0 (by omega)
  · simpa using q_thirtytwo_dyadic_good 3 1 (by omega)
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 4 0 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 4 1 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · simpa using q_four_dyadic_good 4 0 (by omega)
  · simpa using q_four_dyadic_good 4 1 (by omega)
  · simpa using q_eight_dyadic_good 4 0 (by omega)
  · simpa using q_eight_dyadic_good 4 1 (by omega)
  · simpa using q_sixteen_dyadic_good 4 0 (by omega)
  · simpa using q_sixteen_dyadic_good 4 1 (by omega)
  · simpa using q_thirtytwo_dyadic_good 4 0 (by omega)
  · simpa using q_thirtytwo_dyadic_good 4 1 (by omega)
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 5 0 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 5 1 (by omega)
    exact ⟨v,m,M,true,hg⟩
  · simpa using q_four_dyadic_good 5 0 (by omega)
  · simpa using q_four_dyadic_good 5 1 (by omega)
  · simpa using q_eight_dyadic_good 5 0 (by omega)
  · simpa using q_eight_dyadic_good 5 1 (by omega)
  · simpa using q_sixteen_dyadic_good 5 0 (by omega)
  · simpa using q_sixteen_dyadic_good 5 1 (by omega)
  · simpa using q_thirtytwo_dyadic_good 5 0 (by omega)
  · simpa using q_thirtytwo_dyadic_good 5 1 (by omega)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
