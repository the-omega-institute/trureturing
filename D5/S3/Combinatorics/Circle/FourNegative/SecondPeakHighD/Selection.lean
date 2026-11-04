/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Selection
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Convert the ceiling/remainder construction into genuine bounded natural submasks. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.TableCertificates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

/-! Unbounded dyadic dilation and literal h=1,2 residue selectors. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open private submask_shift
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

private theorem residue_selection (p h q : ℕ)
    (hp : p=4 ∨ p=8) (hh : h=1 ∨ h=2)
    (hq : ∃ s : ℕ, q=8*2^s) :
    ∃ v m M : ℕ, ∃ before : Bool, Submask m M ∧ rowBounds 8 p q h v m M before := by
  obtain ⟨s,rfl⟩:=hq
  obtain ⟨R,r,hr,hrr⟩:=SmallAAllH.residue_decomposition s
  have pick : ∃ i : Fin 24,
      (residueRows i).p=p ∧ (residueRows i).h=h ∧ (residueRows i).r=r := by
    rcases hp with rfl|rfl <;> rcases hh with rfl|rfl <;>
      rcases hrr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨0,by norm_num [residueRows]⟩
    · exact ⟨1,by norm_num [residueRows]⟩
    · exact ⟨2,by norm_num [residueRows]⟩
    · exact ⟨3,by norm_num [residueRows]⟩
    · exact ⟨4,by norm_num [residueRows]⟩
    · exact ⟨5,by norm_num [residueRows]⟩
    · exact ⟨6,by norm_num [residueRows]⟩
    · exact ⟨7,by norm_num [residueRows]⟩
    · exact ⟨8,by norm_num [residueRows]⟩
    · exact ⟨9,by norm_num [residueRows]⟩
    · exact ⟨10,by norm_num [residueRows]⟩
    · exact ⟨11,by norm_num [residueRows]⟩
    · exact ⟨12,by norm_num [residueRows]⟩
    · exact ⟨13,by norm_num [residueRows]⟩
    · exact ⟨14,by norm_num [residueRows]⟩
    · exact ⟨15,by norm_num [residueRows]⟩
    · exact ⟨16,by norm_num [residueRows]⟩
    · exact ⟨17,by norm_num [residueRows]⟩
    · exact ⟨18,by norm_num [residueRows]⟩
    · exact ⟨19,by norm_num [residueRows]⟩
    · exact ⟨20,by norm_num [residueRows]⟩
    · exact ⟨21,by norm_num [residueRows]⟩
    · exact ⟨22,by norm_num [residueRows]⟩
    · exact ⟨23,by norm_num [residueRows]⟩
  obtain ⟨i,hp',hh',hr'⟩:=pick
  let row:=residueRows i
  let v:=row.p*(72*R+row.r)-row.offset
  let M:=row.block*R+row.constant
  have hb:=residue_bounds i R
  have ho : row.offset≤row.p*(72*R+row.r) := by
    have hz : (row.offset:ℤ)≤(row.p:ℤ)*(72*(R:ℤ)+row.r) := by
      have hv:=hb.2.1
      change 1≤(row.p:ℤ)*(72*(R:ℤ)+row.r)-row.offset at hv
      omega
    exact_mod_cast hz
  have hvcast : (v:ℤ)=(row.p:ℤ)*(72*(R:ℤ)+row.r)-row.offset := by
    dsimp [v]
    rw [Nat.cast_sub ho]
    push_cast
    ring
  have hMcast : (M:ℤ)=(row.block:ℤ)*(R:ℤ)+row.constant := by dsimp [M]
  let before : Bool:=if p=4 ∧ h=1 ∧ r=56 then false else true
  have timing : row.before=before := by
    have ht:=residue_fresh_exact i
    change row.before=false ↔ row.p=4 ∧ row.h=1 ∧ row.r=56 at ht
    rw [hp',hh',hr'] at ht
    by_cases he : p=4 ∧ h=1 ∧ r=56
    · simpa [before,he] using ht.mpr he
    · have hn : row.before≠false := fun hf => he (ht.mp hf)
      cases hrow : row.before
      · exact (hn hrow).elim
      · simp only [hrow,before,if_neg he]
  refine ⟨v,row.m,M,before,residue_submask i R,?_⟩
  rw [←timing]
  rw [show (8*2^s:ℕ)=72*R+r from hr]
  rw [←hp',←hh',←hr']
  simpa only [hvcast,hMcast,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hb

/-- The eight boundary sectors dilate at every dyadic scale. -/
private theorem dilation_selection (x p q H : ℕ)
    (ht : (x=8 ∧ p=4 ∧ q=2) ∨ (x=8 ∧ p=4 ∧ q=4) ∨
      (x=8 ∧ p=8 ∧ q=2) ∨ (x=8 ∧ p=8 ∧ q=4) ∨ (x=8 ∧ p=16 ∧ q=2) ∨
      (x=16 ∧ p=8 ∧ q=2) ∨ (x=16 ∧ p=8 ∧ q=4) ∨ (x=16 ∧ p=16 ∧ q=2)) :
    ∃ v m M : ℕ, ∃ before : Bool,
      Submask m M ∧ rowBounds x p q (2^H) v m M before := by
  have hh : (1:ℤ)≤2^H := by exact_mod_cast (Nat.one_le_two_pow (n:=H))
  rcases ht with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · refine ⟨3,2^H*9,2^H*9,true,submask_shift 9 9 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨6,2^H*18,2^H*22,true,submask_shift 18 22 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨9,2^H*12,2^H*15,true,submask_shift 12 15 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨5,2^H*48,2^H*49,true,submask_shift 48 49 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨15,2^H*29,2^H*31,true,submask_shift 29 31 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨7,2^H*17,2^H*19,true,submask_shift 17 19 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨6,2^H*49,2^H*51,true,submask_shift 49 51 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega
  · refine ⟨10,2^H*41,2^H*43,true,submask_shift 41 43 H (submask_of_land _ _ (by decide)),?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r
      fin_cases r <;>
        norm_num [oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T] <;> omega
    all_goals norm_num [Y,T] <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
