/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllSelection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllSelection
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded a2 second peak AllSelection construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Exhaustion
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.LargeP

/-! All-H selection using the small selector and the consumed
large_p_allh_good construction from LargeP. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH

open private good_of_row_bounds large_p_allh_good
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.LargeP

/-- Exhaustive independent dyadic selection, with no cutoff on any exponent.
The near-b selector supplies k=0,1; all other k use the small/large-p closure. -/
private theorem dyadic_allh_good (u s k : ℕ) (hu : 2≤u) (hs : 1≤s) :
    ∃ v m M : ℕ, ∃ before : Bool,
      SecondPeakA2.Good (2^u) (2^s) (2^k) v m M before := by
  by_cases hk : k≤1
  · apply SecondPeakA2.dyadic_exists u s (2^k) hu hs
    have he : k=0 ∨ k=1 := by omega
    rcases he with rfl|rfl <;> norm_num
  have hk2 : 2≤k := by omega
  have hp : 4≤(2^u:ℕ) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) hu)
  have hq : 2≤(2^s:ℕ) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) hs)
  have small (hps : (2^u:ℕ)=4 ∨ (2^u:ℕ)=8 ∨ (2^u:ℕ)=16 ∨ (2^u:ℕ)=32) :
      ∃ v m M : ℕ, ∃ before : Bool,
        SecondPeakA2.Good (2^u) (2^s) (2^k) v m M before := by
    obtain ⟨v,m,M,before,hsub,hmM,hbounds⟩ :=
      small_p_allh_selection (2^u) s k hps hs hk2
    refine ⟨v,m,M,before,
      good_of_row_bounds (2^u) (2^s) (2^k) v m M before hsub hmM ?_⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbounds
  rcases SecondPeakA2.dyadic_p_partition u hp with h4|h8|h16|h32|h64
  · exact small (Or.inl h4)
  · exact small (Or.inr (Or.inl h8))
  · exact small (Or.inr (Or.inr (Or.inl h16)))
  · exact small (Or.inr (Or.inr (Or.inr h32)))
  · exact large_p_allh_good (2^u) (2^s) k h64 hq hk2
      (SecondPeakA2.dyadic_large_partition s hq)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
