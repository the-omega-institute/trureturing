/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/UpperGap/Endpoint
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical joint ear orders for all four gaps with the fourth strictly largest. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPeak
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryEqualFirst
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private peak_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPeak
open private first_less_certificate first_right_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryRounded
open private rising_certificate swapped_certificate tied_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction
open private equal_first_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryEqualFirst

private theorem boundary_certificate (a b c : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    Nonempty (Certificate a b c (max (max a b) c+1)) := by
  by_cases hp : a≤b ∧ c≤b
  · rw [max_eq_right hp.1,max_eq_left hp.2]
    exact peak_certificate a b c ha hc hp.1 hp.2
  · by_cases hf : b<a ∧ c<a
    · rw [max_eq_left hf.1.le,max_eq_left hf.2.le]
      by_cases hbc : b<c
      · exact first_less_certificate a b c hb hbc hf.2
      · exact first_right_certificate a b c hc (by omega) hf.1
    · by_cases he : a=c
      · have hba : b<a := by omega
        rw [max_eq_left hba.le,←he,max_self]
        subst c
        exact tied_certificate a b hb hba
      · have hac : a<c := by omega
        have hbc : b<c := by omega
        rw [max_eq_right (max_le hac.le hbc.le)]
        by_cases hab : a=b
        · subst b
          exact equal_first_certificate a c ha hac
        · by_cases hlt : a<b
          · exact rising_certificate a b c ha hlt hbc
          · exact swapped_certificate a b c hb (by omega) hac

/-- One old physical permutation and one literal ear cut work for every upper gap. -/
theorem actualSource_upper_gap_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : max (max a b) c<d) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  by_cases he : d=max (max a b) c+1
  · subst d
    exact (actual_four_packet_iff a b c (max (max a b) c+1)
      ha hb hc (by omega)).mpr (boundary_certificate a b c ha hb hc)
  · obtain ⟨sigma,hold,hnew⟩ :=
      D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Endpoint.actualSource_max_plus_two_first_ear
        a b c d ha hb hc (by omega)
    exact ⟨sigma,0,by omega,hold,hnew⟩

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
