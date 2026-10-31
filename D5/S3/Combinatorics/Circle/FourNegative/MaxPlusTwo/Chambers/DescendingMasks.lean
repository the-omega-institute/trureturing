/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/DescendingMasks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/DescendingMasks
   mirror-E: none(waiver:internal-mask-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Actual descending dyadic mask values, physical capacities and exact reserves. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Descending

/-! The descending OR masks identify coincident bits without duplicating a physical label. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private descending_polynomials descending_mask_values
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Descending

set_option maxHeartbeats 1400000 in
-- Exact dyadic ratios convert the polynomial charts to the literal constructor masks.
private theorem descending_masks (a b c : ℕ) (hc : 2≤c) (hcb : c≤b) (hba : b≤a)
    (hedge : ¬((2:ℕ)^c=4 ∧ (2:ℕ)^a=2*2^b)) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let u1:=(2*R/Z) ||| (2*R/T) ||| 2
    let u2:=(2*R/T) ||| 2
    let A:=seedZ a b c
    let e1:=2*(R:ℤ)*((R:ℤ)*T+R+1)
    let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z; let e3:=2*(R:ℤ)*T*Z
    u1<2^(a+1) ∧ u2<2^(a+1) ∧ 2<2^(a+1) ∧
    (∀ e, u2.testBit e=true → u1.testBit e=true) ∧
    (∀ e, (2:ℕ).testBit e=true → u2.testBit e=true) ∧
    e1≤A*u1 ∧ A*u1≤2*e1-A+1 ∧
    e2≤A*u2 ∧ A*u2≤2*e2-A+Z+1 ∧
    e3≤2*A ∧ 2*A≤2*e3-A+(T*Z+T+1) := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let p:=a-b
  let l:=b-c
  let P : ℕ:=2^p
  let L : ℕ:=2^l
  let u1:=(2*R/Z) ||| (2*R/T) ||| 2
  let u2:=(2*R/T) ||| 2
  let A:=seedZ a b c
  let e1:=2*(R:ℤ)*((R:ℤ)*T+R+1)
  let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z
  let e3:=2*(R:ℤ)*T*Z
  have hR : R=T*P := by dsimp [R,T,P,p]; rw [←pow_add]; congr 1; omega
  have hT : T=Z*L := by dsimp [T,Z,L,l]; rw [←pow_add]; congr 1; omega
  have h1 : 2*R/Z=2*P*L := by
    have he : 2*R=Z*(2*P*L) := by rw [hR,hT]; ring
    rw [he,Nat.mul_div_right (2*P*L) (Nat.two_pow_pos _)]
  have h2 : 2*R/T=2*P := by
    have he : 2*R=T*(2*P) := by rw [hR]; ring
    rw [he,Nat.mul_div_right (2*P) (Nat.two_pow_pos _)]
  have hpone : ((P:ℤ)=1) ↔ p=0 := by
    constructor
    · intro he
      by_contra hh
      have hp2 : 2≤P:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤p by omega)
      have : (2:ℤ)≤P := by exact_mod_cast hp2
      omega
    · intro he; simp only [P,he,pow_zero,Nat.cast_one]
  have hlone : ((L:ℤ)=1) ↔ l=0 := by
    constructor
    · intro he
      by_contra hh
      have hl2 : 2≤L:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤l by omega)
      have : (2:ℤ)≤L := by exact_mod_cast hl2
      omega
    · intro he; simp only [L,he,pow_zero,Nat.cast_one]
  have hpCases : (P:ℤ)=1 ∨ 2≤(P:ℤ) := by
    by_cases he : p=0
    · exact Or.inl (hpone.mpr he)
    · right; exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤p by omega))
  have hlCases : (L:ℤ)=1 ∨ 2≤(L:ℤ) := by
    by_cases he : l=0
    · exact Or.inl (hlone.mpr he)
    · right; exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤l by omega))
  have heCases : (P:ℤ)=1 ∨ 8≤(Z:ℤ) ∨ 4≤(P:ℤ) := by
    by_cases hp0 : p=0
    · exact Or.inl (hpone.mpr hp0)
    · right
      by_cases hc3 : 3≤c
      · left; exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two hc3)
      · right
        have hc2 : c=2 := by omega
        have hp2 : 2≤p := by
          by_contra hh
          have hpe : p=1 := by omega
          have hae : a=b+1 := by dsimp [p] at hpe; omega
          apply hedge
          constructor
          · rw [hc2]; norm_num
          · rw [hae,pow_succ]; ring
        exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two hp2)
  have hm:=descending_mask_values p l
  change ((2*P ||| 2)=if p=0 then 2 else 2*P+2) ∧
    ((2*P*L ||| 2*P ||| 2)=if p=0 then (if l=0 then 2 else 2*L+2)
      else if l=0 then 2*P+2 else 2*P*L+2*P+2) at hm
  have hu1i : (u1:ℤ)=if (P:ℤ)=1 then (if (L:ℤ)=1 then (2:ℤ) else 2*(L:ℤ)+2)
      else if (L:ℤ)=1 then 2*(P:ℤ)+2 else 2*(P:ℤ)*(L:ℤ)+2*(P:ℤ)+2 := by
    dsimp only [u1]
    rw [h1,h2,hm.2]
    by_cases hp0 : p=0 <;> by_cases hl0 : l=0 <;>
      simp only [hpone,hlone,hp0,hl0,if_true,if_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hu2i : (u2:ℤ)=if (P:ℤ)=1 then (2:ℤ) else 2*(P:ℤ)+2 := by
    dsimp only [u2]
    rw [h2,hm.1]
    by_cases hp0 : p=0 <;>
      simp only [hpone,hp0,if_true,if_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hH1 : 2*P*L=2^(p+l+1) := by dsimp [P,L]; rw [pow_succ,pow_add]; ring
  have hH2 : 2*P=2^(p+1) := by dsimp [P]; rw [pow_succ]; ring
  have hcap1 : 2*P*L<2^(a+1) := by
    rw [hH1]
    exact Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show p+l+1<a+1 by dsimp [p,l]; omega)
  have hcap2 : 2*P<2^(a+1) := by
    rw [hH2]
    exact Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show p+1<a+1 by dsimp [p]; omega)
  have hcap3 : 2<2^(a+1) :=
    Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show 1<a+1 by omega)
  have hucap1 : u1<2^(a+1) := by
    dsimp only [u1]; rw [h1,h2]
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow hcap1 hcap2) hcap3
  have hucap2 : u2<2^(a+1) := by
    dsimp only [u2]; rw [h2]
    exact Nat.or_lt_two_pow hcap2 hcap3
  have h12 : ∀ e, u2.testBit e=true → u1.testBit e=true := by
    intro e he
    dsimp only [u1,u2] at he ⊢
    simp only [Nat.testBit_or,Bool.or_eq_true] at he ⊢
    rcases he with h|h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h23 : ∀ e, (2:ℕ).testBit e=true → u2.testBit e=true := by
    intro e he
    dsimp only [u2]
    simp only [Nat.testBit_or,he,Bool.or_true]
  have hRi : (R:ℤ)=(T:ℤ)*P := by exact_mod_cast hR
  have hTi : (T:ℤ)=(Z:ℤ)*L := by exact_mod_cast hT
  have hA : A=(R:ℤ)*T*Z+((R:ℤ)*T+R+1) := by dsimp [A,seedZ,R,T,Z]; push_cast; ring
  have hp:=descending_polynomials (Z:ℤ) (L:ℤ) (P:ℤ)
    (by exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two hc)) hlCases hpCases heCases
  dsimp only at hp
  rw [←hTi,←hRi,←hA,←hu1i,←hu2i] at hp
  exact ⟨hucap1,hucap2,hcap3,h12,h23,hp⟩

private theorem descending_word (a b c : ℕ) (hcb : c≤b) (hba : b≤a)
    (hedge : ¬((2:ℕ)^c=4 ∧ (2:ℕ)^a=2*2^b)) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    baseWord a b c=chamberMaskedWord a b c (a+2)
      ((2*R/Z) ||| (2*R/T) ||| 2) ((2*R/T) ||| 2) 2 0 0 0 0 := by
  have hmin : min a c=c := min_eq_right (by omega)
  have hmax : max a c=a := max_eq_left (by omega)
  have hmono : min a c≤b ∧ b≤max a c := by rw [hmin,hmax]; exact ⟨hcb,hba⟩
  have hd : max (max a b) c+2=a+2 := by rw [max_eq_left hba,max_eq_left (by omega)]
  dsimp only [baseWord,baseBlocks]
  rw [if_pos hmono]
  simp only [monotoneBlocks,if_pos (And.intro hcb hba),if_neg hedge,hd]
  rfl

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
