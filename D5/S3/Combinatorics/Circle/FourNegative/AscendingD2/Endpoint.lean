/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Endpoint
   mirror-E: none(waiver:source-equivalence-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical permutation and a fresh first ear for every independent two-at-most-a-less-b-less-c gap tuple. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Realize

/-! The strict ascending three-coordinate d=2 chamber; unrestricted four-gap J remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open SourceWidth PeriodicShortening RunFirstEarTransport
open private realize from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Realize
open private large_choice small_choice tail_choice from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Choices

private theorem finite_order (k t : ℕ) (word : List (Fin k))
    (hp : word.Perm (List.finRange k)) (hz : (word.map (actualSource k t)).sum=0)
    (hs : ∀ n : Fin (k+1), ((word.take n.val).map (actualSource k t)).sum ∈
      Set.Icc (0 : ℤ) (modulus k/2)) : OriginalOrder k t word := by
  refine ⟨hp,hz,?_⟩
  intro n
  have hl : word.length=k := by have := hp.length_eq; simpa using this
  by_cases hn : n≤k
  · exact hs ⟨n,by omega⟩
  · rw [List.take_of_length_le (by omega),hz]
    have h := hs ⟨0,by omega⟩
    simpa using h

private theorem finite_four : ∃ sigma : List (Fin 11),
    OriginalOrder 11 549 sigma ∧ OriginalOrder 12 1098 (earWord 11 sigma 0) := by
  refine ⟨[9,2,8,7,10,4,6,5,0,3,1],?_,?_⟩
  all_goals apply finite_order <;> decide

private theorem finite_five : ∃ sigma : List (Fin 12),
    OriginalOrder 12 1061 sigma ∧ OriginalOrder 13 2122 (earWord 12 sigma 0) := by
  refine ⟨[8,2,9,10,3,11,5,7,6,0,4,1],?_,?_⟩
  all_goals apply finite_order <;> decide

private theorem finite_six : ∃ sigma : List (Fin 13),
    OriginalOrder 13 2085 sigma ∧ OriginalOrder 14 4170 (earWord 13 sigma 0) := by
  refine ⟨[9,3,10,11,4,12,6,8,7,0,5,2,1],?_,?_⟩
  all_goals apply finite_order <;> decide

/-- Every independent 2≤a<b<c has a complete literal physical first-ear joint order.
Both complete integer totals vanish and both orders include every natural take-prefix. -/
theorem actualSource_strict_ascending_d2_joint_lift (a b c : ℕ)
    (ha : 2≤a) (hab : a<b) (hbc : b<c) :
    ∃ sigma : List (Fin (a+b+c+2)),
      OriginalOrder (a+b+c+2) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+2+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+2) sigma 0) := by
  by_cases ha4 : 4≤a
  · exact realize a b c ha (by omega) (by omega) (large_choice a b c ha4 hab hbc)
  by_cases hb4 : 4≤b
  · exact realize a b c ha (by omega) (by omega)
      (small_choice a b c (by omega) hb4 hbc)
  have ha2 : a=2 := by omega
  have hb3 : b=3 := by omega
  subst a b
  by_cases hc7 : 7≤c
  · exact realize 2 3 c (by decide) (by decide) (by omega) (tail_choice c hc7)
  have hc : c=4 ∨ c=5 ∨ c=6 := by omega
  rcases hc with rfl|rfl|rfl
  · exact finite_four
  · exact finite_five
  · exact finite_six

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
