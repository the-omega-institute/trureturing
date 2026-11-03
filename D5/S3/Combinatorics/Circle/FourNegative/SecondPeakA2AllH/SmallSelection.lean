import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallTables
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallLargeQ

/-! Source draft: consumed small-p component of the unchanged original all-h lift.
This selector does not assert the downstream physical permutation/ear endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakHighD

/-- Exhaustion only of the genuinely finite q<64 sector; Q itself is unrestricted. -/
theorem small_q_partition (Q : ℕ) (hQ : 1≤Q) :
    (2^Q:ℕ)=2 ∨ (2^Q:ℕ)=4 ∨ (2^Q:ℕ)=8 ∨
    (2^Q:ℕ)=16 ∨ (2^Q:ℕ)=32 ∨ 64≤(2^Q:ℕ) := by
  by_cases hbig : 6≤Q
  · right; right; right; right; right
    have hp := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hbig
    norm_num at hp
    exact hp
  · have hsmall : Q=1 ∨ Q=2 ∨ Q=3 ∨ Q=4 ∨ Q=5 := by omega
    rcases hsmall with rfl|rfl|rfl|rfl|rfl <;> norm_num

/-- The missing small-p component, with all physical slacks and a PROPER submask.
Q and H have no upper bound. The large-p and h=1,2 components remain separate
inputs to the complete original endpoint, not alternative completion targets. -/
theorem small_p_allh_selection (p Q H : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hQ : 1≤Q) (hH : 2≤H) :
    ∃ v m M : ℕ, ∃ before : Bool,
      Submask m M ∧ m<M ∧ rowBounds 4 p (2^Q) (2^H) v m M before := by
  have hp4 : 4≤p := by rcases hp with rfl|rfl|rfl|rfl <;> norm_num
  have hp32 : p≤32 := by rcases hp with rfl|rfl|rfl|rfl <;> norm_num
  have hfour : 4∣p := by rcases hp with rfl|rfl|rfl|rfl <;> norm_num
  by_cases hqbig : 64≤(2^Q:ℕ)
  · obtain ⟨v,m,M,before,_,_,_,_,hs,hm,hb⟩ :=
      small_large_q_selection p (2^Q) H hp4 hp32 hfour hqbig hH
    refine ⟨v,m,M,before,hs,hm,?_⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb
  have hqsmall : (2^Q:ℕ)=2 ∨ (2^Q:ℕ)=4 ∨ (2^Q:ℕ)=8 ∨
      (2^Q:ℕ)=16 ∨ (2^Q:ℕ)=32 := by
    rcases small_q_partition Q hQ with h|h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · contradiction
  obtain ⟨i,hpi,hqi⟩ := small_row_pairs p (2^Q) hp hqsmall
  by_cases hH3 : 3≤H
  · obtain ⟨v,m,M,before,hs,hm,hb⟩ := affine_small_selection i H hH3
    refine ⟨v,m,M,before,hs,hm,?_⟩
    simpa only [hpi,hqi,Nat.cast_pow,Nat.cast_ofNat] using hb
  · have he : H=2 := by omega
    subst H
    let w := h4SmallRows i
    have bits := h4_small_bits i
    have bounds := h4_small_bounds i
    have pair := h4_pairs i
    have hwp : w.p=p := pair.1.trans hpi
    have hwq : w.q=(2^Q:ℕ) := pair.2.trans hqi
    refine ⟨w.v,w.m,w.M,w.before,bits.1,bits.2,?_⟩
    simpa only [hwp,hwq,Nat.cast_pow,Nat.cast_ofNat,show (2:ℤ)^2=4 by norm_num]
      using bounds

/-- Value-level interface for callers already holding the original exponent dictionary. -/
theorem small_p_dyadic_selection (p q h : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)
    (hq : ∃ Q : ℕ, 1≤Q ∧ q=2^Q) (hh : ∃ H : ℕ, 2≤H ∧ h=2^H) :
    ∃ v m M : ℕ, ∃ before : Bool,
      Submask m M ∧ m<M ∧ rowBounds 4 p q h v m M before := by
  obtain ⟨Q,hQ,rfl⟩ := hq
  obtain ⟨H,hH,rfl⟩ := hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using small_p_allh_selection p Q H hp hQ hH

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
