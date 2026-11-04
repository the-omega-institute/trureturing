/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Endpoint
   generality: I
   mirror-B: none(waiver:complete-tied-maximum-physical-source)
   mirror-E: none(waiver:complete-tied-maximum-physical-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Entire tied-last-two maximum face with a common physical order, literal ear and all repeated prefixes. -/
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.SourceCertificate
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentPairsJointLift
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private singleton_actual_source borrow_actual_source
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.SourceCertificate
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- The original gaps, exact seed, one common physical order, one literal ear,
every natural finite repetition/take, and separate repeated old/new zero totals. -/
def Conclusion (a b s : ℕ) : Prop :=
  ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
    OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
    OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
      (earWord (a+b+s+s) sigma j) ∧
    (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
      (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum ∈
      Set.Icc (0 : ℤ) (modulus (a+b+s+s)/2)) ∧
    (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).take n).map
      (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum ∈
      Set.Icc (0 : ℤ) (modulus (a+b+s+s))) ∧
    (∀ m : ℕ,
      (((List.replicate m sigma).flatten).map
        (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum=0 ∧
      (((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).map
        (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum=0)

private theorem full_conclusion_of_orders (a b s : ℕ)
    (hjoint : ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j)) : Conclusion a b s := by
  obtain ⟨sigma,j,hj,ho,hn⟩ := hjoint
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+s+s) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+s+s+1)/2=modulus (a+b+s+s) := by
    have hp : (2 : ℤ)^(a+b+s+s+1)=2*(2 : ℤ)^(a+b+s+s) := by rw [pow_succ];ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

private theorem singleton_full_conclusion (a b s : ℕ) (ha : 2≤a) (hab : a<b)
    (hbs : b≤s) (hnotbalanced : ¬ (b=s ∧ s=a+1)) : Conclusion a b s :=
  full_conclusion_of_orders a b s
    (singleton_actual_source a b s ha hab hbs hnotbalanced)

/-- Original gaps (a,b,s,s), their original seed, every occurrence and one
literal fresh insertion; no bound is imposed on repetitions or take lengths. -/
theorem actualSource_last_two_maximum_joint_lift (a b s : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hs : max a b≤s) :
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum ∈
        Set.Icc (0 : ℤ) (modulus (a+b+s+s)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).take n).map
        (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum ∈
        Set.Icc (0 : ℤ) (modulus (a+b+s+s))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+s+s) sigma j)).flatten).map
          (actualSource (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s))))).sum=0) := by
  change Conclusion a b s
  have has : a≤s := le_trans (le_max_left a b) hs
  have hbs : b≤s := le_trans (le_max_right a b) hs
  by_cases hae : a=s
  · subst a
    apply full_conclusion_of_orders s b s
    have hk : s+b+s+s=3*s+b := by omega
    have he : s+b+s=2*s+b := by omega
    rw [hk,he]
    exact
      EqualOuterThree.actualSource_equal_outer_three_joint_lift s b ha hb
  · by_cases he : a=b
    · subst b
      apply full_conclusion_of_orders a a s
      have hk : a+a+s+s=2*a+2*s := by omega
      have he : a+a=2*a := by omega
      rw [hk,he]
      exact
        Adjacent.FourNegativeAdjacentPairsJointLift.actualSource_four_negative_adjacent_pairs_joint_lift
          a s ha (by omega)
    · by_cases hba : b<a
      · exact full_conclusion_of_orders a b s
          (borrow_actual_source a b s hb hba (by omega))
      · have hab : a<b := by omega
        by_cases hbalanced : b=s ∧ s=a+1
        · apply full_conclusion_of_orders a b s
          exact BalancedGaps.actualSource_balanced_gaps_joint_lift a b s s ha hb
            (by omega) (by omega) (by omega)
        · exact singleton_full_conclusion a b s ha hab hbs hbalanced

#print axioms actualSource_last_two_maximum_joint_lift

end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
