/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: All unbounded dyadic h and q for the four small p. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QFourStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QEightStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QSixteenStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QThirtyTwoStructural
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallLargeQ

/-! All unbounded dyadic h and q for the four small p. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakHighD
open private q_two_boundary_good from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

private theorem good_row_bounds (p q h v m M : ℕ) (before : Bool)
    (hg : SecondPeakA2.Good p q h v m M before) :
    Submask m M ∧ m<M ∧ rowBounds 4 p q h v m M before := by
  rcases hg with ⟨hv,hvT,hm,hM,hs,hw⟩
  have hv' : (1:ℤ)≤v := by exact_mod_cast hv
  have hvT' : 2*(v:ℤ)≤4*(p:ℤ)*q := by exact_mod_cast hvT
  have hM' : 2*(M:ℤ)<8*(h:ℤ)*p*q := by exact_mod_cast hM
  have he : (8:ℤ)*h*p*q=2*(4*(h:ℤ)*p*q) := by ring
  rw [he] at hM'
  refine ⟨hs,hm,?_,hv',hvT',by positivity,?_⟩
  · intro r
    exact ⟨(hw r.castSucc).1.1,(hw r.castSucc).1.2,
      (hw r.castSucc).2.1,(hw r.castSucc).2.2⟩
  · have hy : Y 4 (p:ℤ) q h=2*(4*(h:ℤ)*p*q) := by dsimp [Y,T]; ring
    rw [hy]
    omega

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
  obtain ⟨P,hP,hpP⟩ : ∃ P : ℕ, 2≤P ∧ p=2^P := by
    rcases hp with rfl|rfl|rfl|rfl
    · exact ⟨2,by decide,by decide⟩
    · exact ⟨3,by decide,by decide⟩
    · exact ⟨4,by decide,by decide⟩
    · exact ⟨5,by decide,by decide⟩
  have hgood : ∃ v m M : ℕ, ∃ before : Bool,
      SecondPeakA2.Good p (2^Q) (2^H) v m M before := by
    rcases hqsmall with hq|hq|hq|hq|hq
    · rw [hq]
      by_cases hp4 : p=4
      · rw [hp4]
        exact ⟨5,5*2^H,8*2^H-1,false,q_two_boundary_good H⟩
      · have hP3 : 3≤P := by
          by_contra hn
          have : P=2 := by omega
          subst P
          norm_num at hpP
          exact hp4 hpP
        obtain ⟨v,m,M,hg⟩ := SecondPeakA2.q_two_dyadic_good P H hP3
        exact ⟨v,m,M,true,by simpa only [hpP] using hg⟩
    · rw [hq,hpP]
      exact SecondPeakA2.q_four_dyadic_good P H hP
    · rw [hq,hpP]
      exact SecondPeakA2.q_eight_dyadic_good P H hP
    · rw [hq,hpP]
      exact SecondPeakA2.q_sixteen_dyadic_good P H hP
    · rw [hq,hpP]
      exact SecondPeakA2.q_thirtytwo_dyadic_good P H hP
  obtain ⟨v,m,M,before,hg⟩ := hgood
  exact ⟨v,m,M,before,good_row_bounds p (2^Q) (2^H) v m M before hg⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
