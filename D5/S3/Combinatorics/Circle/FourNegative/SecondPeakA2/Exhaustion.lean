/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Exhaustion and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Finite

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2

/-- Every pair of independent dyadic p>=4,q>=2 and both near-b ratios. -/
theorem dyadic_exists (u s h : ℕ) (hu : 2≤u) (hs : 1≤s) (hh : h=1 ∨ h=2) :
    ∃ v m M : ℕ, ∃ before : Bool, Good (2^u) (2^s) h v m M before := by
  have hp : 4≤2^u := le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) hu)
  have hq : 2≤2^s := le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) hs)
  rcases dyadic_p_partition u hp with hp4|hp8|hp16|hp32|hp64
  · by_cases hq64 : 64≤2^s
    · exact small_exists (2^u) s h (Or.inl hp4) hq64 hh
    · exact finite_exists (2^u) (2^s) h (Or.inl hp4)
        (dyadic_small_partition s hq (by omega)) hh
  · by_cases hq64 : 64≤2^s
    · exact small_exists (2^u) s h (Or.inr (Or.inl hp8)) hq64 hh
    · exact finite_exists (2^u) (2^s) h (Or.inr (Or.inl hp8))
        (dyadic_small_partition s hq (by omega)) hh
  · by_cases hq64 : 64≤2^s
    · exact small_exists (2^u) s h (Or.inr (Or.inr (Or.inl hp16))) hq64 hh
    · exact finite_exists (2^u) (2^s) h (Or.inr (Or.inr (Or.inl hp16)))
        (dyadic_small_partition s hq (by omega)) hh
  · by_cases hq64 : 64≤2^s
    · exact small_exists (2^u) s h (Or.inr (Or.inr (Or.inr hp32))) hq64 hh
    · exact finite_exists (2^u) (2^s) h (Or.inr (Or.inr (Or.inr hp32)))
        (dyadic_small_partition s hq (by omega)) hh
  · exact large_exists (2^u) (2^s) h hp64 hq (dyadic_large_partition s hq) hh

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
