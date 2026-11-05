/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Descending
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Descending
   mirror-E: none(waiver:consumed-chamber-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact-charge descending reserve margins in dyadic polynomial coordinates. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise

/-! The ordinary descending masks retain the exact remaining charge at every seam. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers

set_option maxHeartbeats 1800000 in
-- Six polynomial charts keep all coincident dyadic bits and the smallest nonexceptional edge.
private theorem descending_polynomials (Z L P : ℤ)
    (hZ : 4≤Z) (hL : L=1 ∨ 2≤L) (hP : P=1 ∨ 2≤P)
    (hedge : P=1 ∨ 8≤Z ∨ 4≤P) :
    let T:=Z*L; let R:=T*P; let C:=R*T+R+1
    let A:=R*T*Z+C
    let e1:=2*R*C; let e2:=2*R*(R+1)*Z; let e3:=2*R*T*Z
    let Cprime:=T*Z+T+1
    let l1:=if P=1 then (if L=1 then 2 else 2*L+2)
      else if L=1 then 2*P+2 else 2*P*L+2*P+2
    let l2:=if P=1 then 2 else 2*P+2
    e1≤A*l1 ∧ A*l1≤2*e1-A+1 ∧
    e2≤A*l2 ∧ A*l2≤2*e2-A+Z+1 ∧
    e3≤2*A ∧ 2*A≤2*e3-A+Cprime := by
  rcases hP with hp|hp
  · subst P
    rcases hL with hl|hl
    · subst L
      dsimp only
      simp only [if_true,if_false,if_pos rfl]
      have hz : 0≤Z-4 := by omega
      generalize hz0 : Z-4=z at hz
      have heZ : Z=z+4 := by omega
      rw [heZ]
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      all_goals apply sub_nonneg.mp; ring_nf; positivity
    · dsimp only
      simp only [if_true,if_false,if_pos rfl,if_neg (show ¬L=1 by omega)]
      have hz : 0≤Z-4 := by omega
      have hl' : 0≤L-2 := by omega
      generalize hz0 : Z-4=z at hz
      generalize hl0 : L-2=l at hl'
      have heZ : Z=z+4 := by omega
      have heL : L=l+2 := by omega
      rw [heZ,heL]
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      all_goals apply sub_nonneg.mp; ring_nf; positivity
  · have hnot : ¬P=1 := by omega
    rcases hedge with hh|hz8|hp4
    · omega
    · rcases hL with hl|hl
      · subst L
        dsimp only
        simp only [if_true,if_false,if_neg hnot,if_pos rfl]
        have hz : 0≤Z-8 := by omega
        have hp' : 0≤P-2 := by omega
        generalize hz0 : Z-8=z at hz
        generalize hp0 : P-2=p at hp'
        have heZ : Z=z+8 := by omega
        have heP : P=p+2 := by omega
        rw [heZ,heP]
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        all_goals apply sub_nonneg.mp; ring_nf; positivity
      · dsimp only
        simp only [if_true,if_false,if_neg hnot,if_neg (show ¬L=1 by omega)]
        have hz : 0≤Z-8 := by omega
        have hl' : 0≤L-2 := by omega
        have hp' : 0≤P-2 := by omega
        generalize hz0 : Z-8=z at hz
        generalize hl0 : L-2=l at hl'
        generalize hp0 : P-2=p at hp'
        have heZ : Z=z+8 := by omega
        have heL : L=l+2 := by omega
        have heP : P=p+2 := by omega
        rw [heZ,heL,heP]
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        all_goals apply sub_nonneg.mp; ring_nf; positivity
    · rcases hL with hl|hl
      · subst L
        dsimp only
        simp only [if_true,if_false,if_neg hnot,if_pos rfl]
        have hz : 0≤Z-4 := by omega
        have hp' : 0≤P-4 := by omega
        generalize hz0 : Z-4=z at hz
        generalize hp0 : P-4=p at hp'
        have heZ : Z=z+4 := by omega
        have heP : P=p+4 := by omega
        rw [heZ,heP]
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        all_goals apply sub_nonneg.mp; ring_nf; positivity
      · dsimp only
        simp only [if_true,if_false,if_neg hnot,if_neg (show ¬L=1 by omega)]
        have hz : 0≤Z-4 := by omega
        have hl' : 0≤L-2 := by omega
        have hp' : 0≤P-4 := by omega
        generalize hz0 : Z-4=z at hz
        generalize hl0 : L-2=l at hl'
        generalize hp0 : P-4=p at hp'
        have heZ : Z=z+4 := by omega
        have heL : L=l+2 := by omega
        have heP : P=p+4 := by omega
        rw [heZ,heL,heP]
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        all_goals apply sub_nonneg.mp; ring_nf; positivity


set_option maxHeartbeats 1000000 in
-- Advancing the lowest X-positive changes both the last reserve and its remaining charge.
private theorem descending_edge_polynomials (T : ℤ) (hT : T=4 ∨ 8≤T) :
    let A:=10*T^2+2*T+1
    let e1:=8*T^3+8*T^2+4*T
    let e2:=32*T^2+16*T; let e3:=16*T^2
    let Cprime:=5*T+1
    let l1:=if T=4 then 5 else T+5
    e1≤A*l1 ∧ A*l1≤2*e1-A+1 ∧
    e2≤5*A ∧ 5*A≤2*e2-A+5 ∧
    e3≤5*A-2*e3 ∧ 5*A-2*e3≤2*e3-A+2*Cprime := by
  rcases hT with rfl|hT
  · norm_num
  · dsimp only
    rw [if_neg (show ¬T=4 by omega)]
    have ht : 0≤T-8 := by omega
    generalize ht0 : T-8=t at ht
    have heT : T=t+8 := by omega
    rw [heT]
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    all_goals apply sub_nonneg.mp; ring_nf; positivity


private theorem descending_mask_values (p l : ℕ) :
    let P:ℕ:=2^p; let L:ℕ:=2^l
    ((2*P ||| 2)=if p=0 then 2 else 2*P+2) ∧
    ((2*P*L ||| 2*P ||| 2)=
      if p=0 then (if l=0 then 2 else 2*L+2)
      else if l=0 then 2*P+2 else 2*P*L+2*P+2) := by
  let P:ℕ:=2^p
  let L:ℕ:=2^l
  have hP : 1≤P:=Nat.one_le_two_pow
  have hL : 1≤L:=Nat.one_le_two_pow
  have hH2 : 2*P=2^(p+1) := by dsimp [P]; rw [pow_succ]; ring
  have hH1 : 2*P*L=2^(p+l+1) := by dsimp [P,L]; rw [pow_succ,pow_add]; ring
  have hlow : (2*P ||| 2)=if p=0 then 2 else 2*P+2 := by
    by_cases hp : p=0
    · simp only [if_true,if_false,hp,P,pow_zero,mul_one,Nat.or_self,if_pos rfl]
    · have hlt : 2<(2:ℕ)^(p+1) :=
        Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show 1<p+1 by omega)
      rw [if_neg hp,Nat.or_comm,hH2,Nat.or_two_pow_eq_add_of_lt hlt]
      omega
  refine ⟨hlow,?_⟩
  change (2*P*L ||| 2*P ||| 2)=_
  rw [Nat.or_assoc,hlow]
  by_cases hp : p=0
  · simp only [if_true,if_false,if_pos hp]
    have hPe : P=1 := by dsimp [P]; rw [hp,pow_zero]
    rw [hPe]
    simp only [if_true,if_false,mul_one]
    by_cases hl : l=0
    · simp only [if_true,if_false,hl,L,pow_zero,mul_one,Nat.or_self,if_pos rfl]
    · rw [if_neg hl,Nat.or_comm]
      have hZ : 2*L=2^(l+1) := by dsimp [L]; rw [pow_succ]; ring
      have hlt : 2<(2:ℕ)^(l+1) :=
        Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show 1<l+1 by omega)
      rw [hZ,Nat.or_two_pow_eq_add_of_lt hlt]
      omega
  · simp only [if_true,if_false,if_neg hp]
    have hP2 : 2≤P:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤p by omega)
    by_cases hl : l=0
    · have hLe : L=1 := by dsimp [L]; rw [hl,pow_zero]
      rw [if_pos hl,hLe,mul_one]
      have hlow' : (2*P ||| 2)=2*P+2 := by simpa only [if_neg hp] using hlow
      rw [←hlow',←Nat.or_assoc,Nat.or_self]
    · rw [if_neg hl]
      have hL2 : 2≤L:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤l by omega)
      have hlt : 2*P+2<2*P*L := by nlinarith
      rw [Nat.or_comm,hH1,Nat.or_two_pow_eq_add_of_lt (by simpa only [←hH1] using hlt)]
      rw [←hH1]
      omega

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
