/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Exhaustion
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded dyadic partition of both complete approved high-d domains. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Selection

/-! Exact HighD construction on unrestricted natural exponents. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open private Tail pow_mono_int generic_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
open private residue_selection dilation_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Selection

private theorem dyadic_selection (a P Q H : ℕ)
    (ha : 3≤a) (hP : 2≤P) (hQ : 1≤Q) :
    ∃ v m M : ℕ, ∃ before : Bool, Submask m M ∧
      rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
  have generic (hr : 4*(2:ℤ)^P≤2^a ∨ (a≤P+1 ∧ Tail (2^a) (2^P) (2^Q))) :
      ∃ v m M : ℕ, ∃ before : Bool, Submask m M ∧
        rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
    obtain ⟨v,m,M,hs,hb⟩:=generic_selection a P Q H ha hP hQ hr
    exact ⟨v,m,M,true,hs,hb⟩
  by_cases hsmall : P+2≤a
  · apply generic
    left
    have hp:=pow_mono_int (P+2) a hsmall
    have he : (2:ℤ)^(P+2)=4*2^P := by rw [pow_add]; ring
    rw [he] at hp
    exact hp
  have hexp : a≤P+1 := by omega
  by_cases hlarge : 5≤a
  · apply generic
    right
    refine ⟨hexp,Or.inl ⟨?_,?_⟩⟩
    · have hx:=pow_mono_int 5 a hlarge
      norm_num at hx
      exact hx
    · have hx:=pow_mono_int a (P+1) hexp
      simpa [pow_succ,mul_comm] using hx
  have haSmall : a=3 ∨ a=4 := by omega
  by_cases hboundary : (a=3 ∧ P=2 ∧ Q=1) ∨ (a=3 ∧ P=2 ∧ Q=2) ∨
      (a=3 ∧ P=3 ∧ Q=1) ∨ (a=3 ∧ P=3 ∧ Q=2) ∨ (a=3 ∧ P=4 ∧ Q=1) ∨
      (a=4 ∧ P=3 ∧ Q=1) ∨ (a=4 ∧ P=3 ∧ Q=2) ∨ (a=4 ∧ P=4 ∧ Q=1)
  · apply dilation_selection (2^a) (2^P) (2^Q) H
    rcases hboundary with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
      ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> norm_num
  by_cases hH : 2≤H
  · obtain ⟨v,m,M,before,_,hs,hb⟩ := SmallAAllH.small_a_selection a P Q H haSmall hP hQ hH
    exact ⟨v,m,M,before,hs,hb⟩
  have hnear : (2^H:ℕ)=1 ∨ (2^H:ℕ)=2 := by
    have he : H=0 ∨ H=1 := by omega
    rcases he with rfl|rfl <;> norm_num
  rcases haSmall with rfl|rfl
  · by_cases hP5 : 5≤P
    · apply generic
      right
      refine ⟨hexp,Or.inr (Or.inl ⟨by norm_num,?_⟩)⟩
      have hp:=pow_mono_int 5 P hP5
      norm_num at hp ⊢
      exact hp
    by_cases hQ3 : 3≤Q
    · have hres : ∃ s : ℕ, 2^Q=8*2^s := by
        refine ⟨Q-3,?_⟩
        calc
          2^Q=2^((Q-3)+3) := by congr 1; omega
          _=8*2^(Q-3) := by rw [pow_add]; ring
      have hpCases : P=2 ∨ P=3 ∨ P=4 := by omega
      rcases hpCases with rfl|rfl|rfl
      · simpa using residue_selection 4 (2^H) (2^Q) (by simp) hnear hres
      · simpa using residue_selection 8 (2^H) (2^Q) (by simp) hnear hres
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inl ⟨by norm_num,by norm_num,?_⟩))⟩
        have hq:=pow_mono_int 2 Q (by omega)
        norm_num at hq
        exact hq
    · have hpCases : P=2 ∨ P=3 ∨ P=4 := by omega
      have hqCases : Q=1 ∨ Q=2 := by omega
      rcases hpCases with rfl|rfl|rfl <;> rcases hqCases with rfl|rfl
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · apply generic
        right
        exact ⟨by omega,by norm_num [Tail]⟩
  · by_cases hP5 : 5≤P
    · apply generic
      right
      refine ⟨hexp,Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num,?_⟩)))⟩
      have hp:=pow_mono_int 5 P hP5
      norm_num at hp ⊢
      exact hp
    have hpCases : P=3 ∨ P=4 := by omega
    by_cases hQ3 : 3≤Q
    · have hq8 : (8:ℤ)≤2^Q := by
        have hh:=pow_mono_int 3 Q hQ3; norm_num at hh; exact hh
      rcases hpCases with rfl|rfl
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
        exact ⟨by norm_num,by norm_num,hq8⟩
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
        exact ⟨by norm_num,by norm_num,by omega⟩
    · have hqCases : Q=1 ∨ Q=2 := by omega
      rcases hpCases with rfl|rfl <;> rcases hqCases with rfl|rfl
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · exact (hboundary (by norm_num)).elim
      · apply generic
        right
        exact ⟨by omega,by norm_num [Tail]⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
