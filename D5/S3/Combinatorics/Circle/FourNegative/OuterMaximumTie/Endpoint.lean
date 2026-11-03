/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Endpoint
   mirror-E: none(waiver:complete-face-no-independent-encoding)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exhaustive original outer-maximum-tie face, including every finite repeated take. -/
import D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Certificate
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! The original seed, physical labels and both complete
OriginalOrder predicates are retained. Library boundary cuts are existential;
the new interior constructions use the literal front insertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
open SourceWidth PeriodicShortening RunFirstEarTransport
open private ascending_allocate descending_allocate
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Allocation
open private critical_allocate
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Critical
open private physical_joint_construction
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Certificate
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

private theorem joint (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (hba : b≤a) (hca : c≤a) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ cut : ℕ, cut≤a+b+c+a ∧
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma cut) := by
  by_cases hce : c=a
  · subst c
    simpa only [show a+b+a+a=3*a+b by omega,show a+b+a=2*a+b by omega] using
      EqualOuterThree.actualSource_equal_outer_three_joint_lift a b ha hb
  by_cases hbe : b=a
  · subst b
    simpa only [show a+a+c+a=3*a+c by omega] using
      EqualFirstTwoLast.actualSource_equal_first_two_last_joint_lift a c ha hc
  by_cases hbal : a≤b+1 ∧ a≤c+1
  · exact BalancedGaps.actualSource_balanced_gaps_joint_lift a b c a ha hb hc ha (by omega)
  by_cases hbc : b≤c
  · obtain ⟨v,w,hs,hg⟩ := ascending_allocate a b c hb hbc (by omega) (by omega)
    obtain ⟨sigma,hold,hnew⟩ := physical_joint_construction true a b c ha hb hc v w hs hg
    exact ⟨sigma,0,by omega,hold,hnew⟩
  · by_cases hwide : b+2≤a
    · obtain ⟨v,w,hs,hg⟩ := descending_allocate a b c hc (by omega) hwide
      obtain ⟨sigma,hold,hnew⟩ := physical_joint_construction false a b c ha hb hc v w hs hg
      exact ⟨sigma,0,by omega,hold,hnew⟩
    · have hcritical : b+1=a := by omega
      obtain ⟨v,w,hs,hg⟩ := critical_allocate a b c hc hcritical (by omega)
      obtain ⟨sigma,hold,hnew⟩ := physical_joint_construction false a b c ha hb hc v w hs hg
      exact ⟨sigma,0,by omega,hold,hnew⟩

/-- The ENTIRE original d=a, b,c≤a face. Each row separately has zero
total for every natural finite repetition, and every natural take is bounded. -/
theorem actualSource_outer_maximum_tie_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hda : d=a) (hba : b≤a) (hca : c≤a) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut) ∧
      (∀ r : ℕ, (((List.replicate r sigma).flatten).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0) ∧
      (∀ r : ℕ, (((List.replicate r (earWord (a+b+c+d) sigma cut)).flatten).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) ∧
      (∀ r h : ℕ, ((((List.replicate r sigma).flatten).take h).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum∈
          Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ r h : ℕ, ((((List.replicate r (earWord (a+b+c+d) sigma cut)).flatten).take h).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum∈
          Set.Icc (0:ℤ) (modulus (a+b+c+d+1)/2)) := by
  subst d
  obtain ⟨sigma,cut,hcut,hold,hnew⟩ := joint a b c ha hb hc hba hca
  have old (r : ℕ) := zero_period_transport
    (actualSource (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)))
    (modulus (a+b+c+a)/2) sigma hold.2.1 hold.2.2 r
  have new (r : ℕ) := zero_period_transport
    (actualSource (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))
    (modulus (a+b+c+a+1)/2) (earWord (a+b+c+a) sigma cut) hnew.2.1 hnew.2.2 r
  exact ⟨sigma,cut,hcut,hold,hnew,fun r => (old r).1,fun r => (new r).1,fun r => (old r).2,fun r => (new r).2⟩

end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
