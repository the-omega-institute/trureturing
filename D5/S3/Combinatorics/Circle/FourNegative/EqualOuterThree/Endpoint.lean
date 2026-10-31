/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint
   mirror-E: none(waiver:complete-equal-outer-three-physical-joint-lift)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: All independent equal-outer-three gaps with a common physical order and literal cut. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Upper
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Lower
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Endpoint

/-! Upper, lower and balanced constructions exhaust every independent pair of gaps. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed upper_actual_s_ge_three upper_actual_s_two_four upper_actual_s_two_large
  from D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Upper
open private actual_lower
  from D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Lower

/-- A common actual physical permutation and a literal ear cut for every s,b ≥ 2. -/
theorem actualSource_equal_outer_three_joint_lift (s b : ℕ) (hs : 2≤s) (hb : 2≤b) :
    ∃ sigma : List (Fin (3*s+b)), ∃ cut : ℕ, cut≤3*s+b ∧
      OriginalOrder (3*s+b) (1+2^s+2^(s+b)+2^(2*s+b)) sigma ∧
      OriginalOrder (3*s+b+1) (2*(1+2^s+2^(s+b)+2^(2*s+b)))
        (earWord (3*s+b) sigma cut) := by
  by_cases hu : s+2≤b
  · rw [← show s+b+s+s=3*s+b by omega]
    change ∃ sigma : List (Fin (size s b)), ∃ cut : ℕ, cut≤size s b ∧
      OriginalOrder (size s b) (seed s b) sigma ∧
      OriginalOrder (size s b+1) (2*seed s b) (earWord (size s b) sigma cut)
    have hupper : ∃ sigma : List (Fin (size s b)),
        OriginalOrder (size s b) (seed s b) sigma ∧
        ∃ cut : ℕ, cut≤size s b ∧
          OriginalOrder (size s b+1) (2*seed s b) (earWord (size s b) sigma cut) := by
      by_cases hs3 : 3≤s
      · exact upper_actual_s_ge_three s b hs3 hu
      · have hs2 : s=2 := by omega
        subst s
        by_cases hb4 : b=4
        · subst b; exact upper_actual_s_two_four
        · exact upper_actual_s_two_large b (by omega)
    obtain ⟨sigma,hold,cut,hcut,hnew⟩ := hupper
    exact ⟨sigma,cut,hcut,hold,hnew⟩
  · by_cases hl : b+2≤s
    · rw [← show s+s+b+s=3*s+b by omega]
      obtain ⟨sigma,hold,hnew⟩ := actual_lower s b hb hl
      exact ⟨sigma,0,by omega,hold,hnew⟩
    · have hbal : max (max s b) (max s s) ≤ min (min s b) (min s s)+1 := by omega
      rw [← show s+b+s+s=3*s+b by omega, ← show s+b+s=2*s+b by omega]
      exact BalancedGaps.actualSource_balanced_gaps_joint_lift s b s s hs hb hs hs hbal

#print axioms actualSource_equal_outer_three_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
