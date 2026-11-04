/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QEightStructural
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QEightStructural
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Unbounded modulus-33 q-8 selector with exact physical windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private submask_shift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

private theorem q_eight_first (p h : ℤ) (hp : 8 ≤ p) (hh : 1 ≤ h) :
    let j := (26*p+12)%33
    let v := (256*p+9-20*j)/33
    First p 8 h v (h*j) true := by
  let j := (26*p+12)%33
  let v := (256*p+9-20*j)/33
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj32 : j ≤ 32 := by
    have := Int.emod_lt_of_pos (26*p+12) (by norm_num : (0:ℤ)<33)
    dsimp [j]; omega
  have heq : 33*v+20*j=256*p+9 := by dsimp [v,j]; omega
  have hv0 : 1 ≤ v := by omega
  have hv4 : v ≤ 8*p := by omega
  have hA : A p 8 h=5+8448*h*p := by
    dsimp [A,SecondPeakHighD.A,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]; ring
  have hR : R p 8 h v (h*j)=5*v-1+h*(192*p+33*j) := by
    dsimp [R,A,L,K,SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,
      SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
    linear_combination 256*h*p*heq
  have hN : 4*R p 8 h v (h*j)+2*((y p 8 h-h*j)*Q 8+1)=
      20*v-2+h*(4992*p+66*j) := by rw [hR]; dsimp [y,Q]; ring
  have hc0 : 0 ≤ 192*p+33*j := by omega
  have hc1 : 0 ≤ 8064*p-66*j := by omega
  have hc2 : 0 ≤ 4992*p+66*j := by omega
  have hc3 : 0 ≤ 3456*p-66*j := by omega
  have hprod0 := mul_nonneg (show 0≤h by omega) hc0
  have hprod1 := mul_nonneg (show 0≤h-1 by omega) hc1
  have hprod2 := mul_nonneg (show 0≤h by omega) hc2
  have hprod3 := mul_nonneg (show 0≤h-1 by omega) hc3
  change First p 8 h v (h*j) true
  dsimp only [First]
  simp only [ite_true]
  rw [hN,hR,hA]
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [hp,hj0,hj32,hv0,hv4,hprod0,hprod1,hprod2,hprod3]

private theorem q_eight_windows (p h : ℤ) (hp : 8 ≤ p) (hh : 1 ≤ h) :
    let j := (26*p+12)%33
    let v := (256*p+9-20*j)/33
    Windows p 8 h v (h*j) (h*(12*p-1)) true := by
  let j := (26*p+12)%33
  let v := (256*p+9-20*j)/33
  have hf := q_eight_first p h hp hh
  change First p 8 h v (h*j) true at hf
  change Windows p 8 h v (h*j) (h*(12*p-1)) true
  intro r
  fin_cases r
  · have he : SecondPeakHighD.oldEnds 4 p 8 h v (h*j) (h*(12*p-1)) 0=
        2*R p 8 h v (h*j) := by dsimp [SecondPeakHighD.oldEnds,R]; ring
    have hn : SecondPeakHighD.newEnds 4 p 8 h v (h*j) (h*(12*p-1)) true 0=
        4*R p 8 h v (h*j)+2*((y p 8 h-h*j)*Q 8+1) := by
      dsimp [SecondPeakHighD.newEnds,R,A,L,K,y,Q,SecondPeakHighD.A,
        SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SV,
        SecondPeakHighD.SW,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
      ring
    change (0≤SecondPeakHighD.oldEnds 4 p 8 h v (h*j) (h*(12*p-1)) 0 ∧
      SecondPeakHighD.oldEnds 4 p 8 h v (h*j) (h*(12*p-1)) 0≤A p 8 h-1) ∧
      (0≤SecondPeakHighD.newEnds 4 p 8 h v (h*j) (h*(12*p-1)) true 0 ∧
      SecondPeakHighD.newEnds 4 p 8 h v (h*j) (h*(12*p-1)) true 0≤A p 8 h-1)
    rw [he,hn]
    exact ⟨⟨hf.1,hf.2.1⟩,by simpa only [ite_true,sub_zero] using hf.2.2⟩
  all_goals constructor <;> constructor
  all_goals
    apply le_of_sub_nonneg
    obtain ⟨a,ha,hpa⟩ : ∃ a : ℤ, 0≤a ∧ p=a+8 := ⟨p-8,by omega,by ring⟩
    obtain ⟨b,hb,hhb⟩ : ∃ b : ℤ, 0≤b ∧ h=b+1 := ⟨h-1,by omega,by ring⟩
    rw [hpa,hhb]
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> positivity

private theorem q_eight_large_good (P H : ℕ) (hP : 3 ≤ P) :
    ∃ v m M : ℕ, Good (2^P) 8 (2^H) v m M true := by
  let p : ℕ := 2^P
  let h : ℕ := 2^H
  have hp : 8 ≤ p := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hP
  have hh : 1 ≤ h := Nat.one_le_two_pow
  let j : ℤ := (26*(p:ℤ)+12)%33
  let v : ℤ := (256*(p:ℤ)+9-20*j)/33
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj32 : j ≤ 32 := by
    have := Int.emod_lt_of_pos (26*(p:ℤ)+12) (by norm_num : (0:ℤ)<33)
    dsimp [j]; omega
  have hpz : (8:ℤ) ≤ p := by exact_mod_cast hp
  have heq : 33*v+20*j=256*(p:ℤ)+9 := by dsimp [v,j]; omega
  have hv0 : 0 ≤ v := by omega
  have hjlt : j.toNat < 2^(P+2) := by
    have hpow : (2:ℕ)^(P+2)=4*p := by dsimp [p]; rw [pow_add]; norm_num; omega
    rw [hpow]
    by_cases he : p=8
    · have hp8 : (p:ℤ)=8 := by exact_mod_cast he
      have hj22 : j=22 := by dsimp [j]; rw [hp8]; norm_num
      omega
    · have := Int.toNat_of_nonneg hj0; omega
  have hs := SecondPeakHighD.submask_predecessor (P+2) 3 j.toNat (by omega) hjlt
  have hmask : 2^(P+2)*3-1=12*p-1 := by dsimp [p]; rw [pow_add]; norm_num; omega
  rw [hmask] at hs
  have hvcast : (v.toNat:ℤ)=v := Int.toNat_of_nonneg hv0
  have hjcast : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
  have hMcast : ((12*p-1:ℕ):ℤ)=12*(p:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤12*p)]; push_cast; rfl
  refine ⟨v.toNat,h*j.toNat,h*(12*p-1),?_,?_,?_,?_,?_,?_⟩
  · have : 1≤v := by omega
    rw [←hvcast] at this; exact_mod_cast this
  · have : 2*v≤16*(p:ℤ) := by omega
    rw [←hvcast] at this
    have hn : 2*v.toNat≤16*p := by exact_mod_cast this
    change 2*v.toNat≤4*p*8; omega
  · have : j.toNat<12*p-1 := by omega
    exact Nat.mul_lt_mul_of_pos_left this (by omega)
  · change 2*(h*(12*p-1))<8*h*p*8
    nlinarith [Nat.sub_le (12*p) 1]
  · exact submask_shift _ _ H hs
  · have hw := q_eight_windows p h hpz (by exact_mod_cast hh)
    simpa only [Nat.cast_ofNat,Nat.cast_mul,hvcast,hjcast,hMcast] using hw

private theorem q_eight_boundary_windows (h : ℤ) (hh : 1≤h) :
    Windows 4 8 h 5 (44*h) (46*h) false := by
  all_goals intro r; fin_cases r
  all_goals constructor <;> constructor
  all_goals
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> omega

/-- The complete scale-unbounded q-8 selector on the original physical windows. -/
theorem q_eight_dyadic_good (P H : ℕ) (hP : 2≤P) :
    ∃ v m M : ℕ, ∃ before : Bool, Good (2^P) 8 (2^H) v m M before := by
  have hh : 1≤(2:ℕ)^H := Nat.one_le_two_pow
  have hw := q_eight_boundary_windows ((2^H:ℕ):ℤ) (by exact_mod_cast hh)
  by_cases h2 : P=2
  · subst P
    have hs : SecondPeakHighD.Submask 44 46 :=
      SecondPeakHighD.submask_of_land 44 46 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨5,44*2^H,46*2^H,false,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^2=4 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw
  obtain ⟨v,m,M,hg⟩ := q_eight_large_good P H (by omega)
  exact ⟨v,m,M,true,hg⟩
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
