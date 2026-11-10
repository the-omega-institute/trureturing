/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint
   mirror-E: none(waiver:complete-physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete second-peak equal-outer physical face with all finite repetitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Lower
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Strict
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Palindromic

/-! Complete second-peak equal-outer physical face with all finite repetitions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private lower_lift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Lower
open private strict_lift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Strict
open private palindromic_lift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Palindromic
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- Every original occurrence, one literal fresh label, both actual source orders,
all natural finite-copy prefixes, and exact zero scalar totals for every copy count. -/
theorem actualSource_second_peak_equal_outer_joint_lift (a b c : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hb : max a c≤b) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j≤a+b+c+a ∧
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+a)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+a) sigma j)).flatten).take n).map
        (actualSource (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+a))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+a) sigma j)).flatten).map
          (actualSource (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  have hab : a≤b := le_trans (le_max_left a c) hb
  have hcb : c≤b := le_trans (le_max_right a c) hb
  have joint :
      ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j≤a+b+c+a ∧
        OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
        OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
          (earWord (a+b+c+a) sigma j) := by
    by_cases hba : b=a
    · subst b
      have h:=EqualFirstTwoLast.actualSource_equal_first_two_last_joint_lift a c ha hc
      rw [show 3*a+c=a+a+c+a by omega] at h
      exact h
    · by_cases hca : c=a
      · subst c
        have h:=EqualOuterThree.actualSource_equal_outer_three_joint_lift a b ha (by omega)
        rw [show 3*a+b=a+b+a+a by omega] at h
        rw [show 2*a+b=a+b+a by omega] at h
        exact h
      · by_cases hlt : c<a
        · exact lower_lift a b c hc hlt (by omega)
        · have hac : a<c := by omega
          by_cases hbc : c=b
          · subst c
            by_cases hbal : b≤a+1
            · have balance : max (max a b) (max b a)≤min (min a b) (min b a)+1 := by omega
              exact BalancedGaps.actualSource_balanced_gaps_joint_lift a b b a ha
                (by omega) (by omega) ha balance
            · exact palindromic_lift a b ha (by omega)
          · exact strict_lift a b c ha hac (by omega)
  obtain ⟨sigma,j,hj,ho,hn⟩:=joint
  have eo (m : ℕ):=zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ):=zero_period_transport _ _ (earWord (a+b+c+a) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+a+1)/2=modulus (a+b+c+a) := by
    have hp : (2:ℤ)^(a+b+c+a+1)=2*(2:ℤ)^(a+b+c+a) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_second_peak_equal_outer_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
