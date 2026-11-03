import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Small
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateNear
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! UNELABORATED candidate source for exactly b<a=d<c. No kernel or official
acceptance is asserted. The unrestricted Circle and third-peak cone remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private large_third_joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.LargeThird
open private small_A small_B small_C
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Small
open private moderate_high_joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateHigh
open private moderate_near_joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateNear
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

private theorem moderate_joint (a b c : ℕ) (hb : 2 ≤ b) (hba : b < a)
    (hac : a < c) (hmod : c ≤ a+b-2) : Joint a b c := by
  by_cases hn : a=b+1
  · exact moderate_near_joint a b c hb hn hac hmod
  · exact moderate_high_joint a b c hb (by omega) hac hmod

private theorem original_joint (a b c : ℕ) (hb : 2 ≤ b) (hba : b < a)
    (hac : a < c) : Joint a b c := by
  by_cases hl : a+3 ≤ c
  · exact large_third_joint a b c hb hba hl
  · have hc : c=a+1 ∨ c=a+2 := by omega
    by_cases h2 : b=2
    · subst b
      rcases hc with rfl|rfl
      · exact small_A a (by omega)
      · exact small_B a (by omega)
    · by_cases h3 : b=3
      · subst b
        rcases hc with rfl|rfl
        · exact moderate_joint a 3 (a+1) (by omega) hba (by omega) (by omega)
        · exact small_C a (by omega)
      · exact moderate_joint a b c hb hba hac (by omega)

/-- Every original gaps(a,b,c,a), 2≤b<a<c: one physical permutation, one literal
fresh label k, both unchanged actual orders, all natural repeated/overlong takes,
and two independently zero repeated totals. SOURCE ONLY; UNELABORATED. -/
theorem actualSource_third_peak_equal_outer_joint_lift (a b c : ℕ)
    (hb : 2 ≤ b) (hba : b < a) (hac : a < c) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j ≤ a+b+c+a ∧
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
  obtain ⟨sigma,j,hj,ho,hn⟩ := original_joint a b c hb hba hac
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+c+a) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+a+1)/2=modulus (a+b+c+a) := by
    have hp : (2:ℤ)^(a+b+c+a+1)=2*(2:ℤ)^(a+b+c+a) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
