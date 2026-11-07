/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QSixteenStructural
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QSixteenStructural
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Unbounded modulus-sixty-five q-sixteen selector with exact physical windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private submask_shift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

private theorem q_sixteen_first (p h c j v : ℤ) (hp : 32≤p) (hh : 1≤h)
    (hc : 17≤c ∧ c≤21) (hj : 0≤j ∧ j≤12) (hv : 1≤v ∧ v≤16*p)
    (heq : 65*v+40*j=1024*p+c) : First p 16 h v (h*j) true := by
  have hA : A p 16 h=5+33280*h*p := by
    dsimp [A,SecondPeakHighD.A,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]; ring
  have hR : R p 16 h v (h*j)=5*v-1+h*(128*(4*c-65)*p+65*j) := by
    dsimp [R,A,L,K,SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,
      SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
    linear_combination 512*h*p*heq
  have hN : 4*R p 16 h v (h*j)+2*((y p 16 h-h*j)*Q 16+1)=
      20*v-2+h*(512*(4*c-65)*p+16640*p+130*j) := by
    rw [hR]; dsimp [y,Q]; ring
  have hcp0 := mul_nonneg (show 0≤c-17 by omega) (show 0≤p by omega)
  have hcp1 := mul_nonneg (show 0≤21-c by omega) (show 0≤p by omega)
  have hc0 : 0≤128*(4*c-65)*p+65*j := by nlinarith only [hcp0,hp,hj.1]
  have hc1 : 0≤33280*p-2*(128*(4*c-65)*p+65*j) := by
    nlinarith only [hcp1,hp,hj.2]
  have hc2 : 0≤512*(4*c-65)*p+16640*p+130*j := by
    nlinarith only [hcp0,hp,hj.1]
  have hc3 : 0≤33280*p-(512*(4*c-65)*p+16640*p+130*j) := by
    nlinarith only [hcp1,hp,hj.2]
  have hprod0 := mul_nonneg (show 0≤h by omega) hc0
  have hprod1 := mul_nonneg (show 0≤h-1 by omega) hc1
  have hprod2 := mul_nonneg (show 0≤h by omega) hc2
  have hprod3 := mul_nonneg (show 0≤h-1 by omega) hc3
  dsimp only [First]
  simp only [ite_true]
  rw [hN,hR,hA]
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [hp,hj.1,hj.2,hv.1,hv.2,hcp0,hcp1,hprod0,hprod1,hprod2,hprod3]

private theorem q_sixteen_windows (p h k c j v : ℤ) (hp : 32≤p) (hh : 1≤h)
    (hk : 2*k=p) (hc : 17≤c ∧ c≤21) (hj : 0≤j ∧ j≤12)
    (hv : 1≤v ∧ v≤16*p) (heq : 65*v+40*j=1024*p+c) :
    Windows p 16 h v (h*j) (h*(49*k-1)) true := by
  have hf := q_sixteen_first p h c j v hp hh hc hj hv heq
  intro r
  fin_cases r
  · have he : SecondPeakHighD.oldEnds 4 p 16 h v (h*j) (h*(49*k-1)) 0=
        2*R p 16 h v (h*j) := by dsimp [SecondPeakHighD.oldEnds,R]; ring
    have hn : SecondPeakHighD.newEnds 4 p 16 h v (h*j) (h*(49*k-1)) true 0=
        4*R p 16 h v (h*j)+2*((y p 16 h-h*j)*Q 16+1) := by
      dsimp [SecondPeakHighD.newEnds,R,A,L,K,y,Q,SecondPeakHighD.A,
        SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SV,
        SecondPeakHighD.SW,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
      ring
    change (0≤SecondPeakHighD.oldEnds 4 p 16 h v (h*j) (h*(49*k-1)) 0 ∧
      SecondPeakHighD.oldEnds 4 p 16 h v (h*j) (h*(49*k-1)) 0≤A p 16 h-1) ∧
      (0≤SecondPeakHighD.newEnds 4 p 16 h v (h*j) (h*(49*k-1)) true 0 ∧
      SecondPeakHighD.newEnds 4 p 16 h v (h*j) (h*(49*k-1)) true 0≤A p 16 h-1)
    rw [he,hn]
    exact ⟨⟨hf.1,hf.2.1⟩,by simpa only [ite_true,sub_zero] using hf.2.2⟩
  all_goals constructor <;> constructor
  all_goals
    apply le_of_sub_nonneg
    have hpk : p=2*k := by omega
    rw [hpk]
    obtain ⟨a,ha,hka⟩ : ∃ a : ℤ, 0≤a ∧ k=a+16 := ⟨k-16,by omega,by ring⟩
    obtain ⟨b,hb,hhb⟩ : ∃ b : ℤ, 0≤b ∧ h=b+1 := ⟨h-1,by omega,by ring⟩
    rw [hka,hhb]
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> positivity

private theorem q_sixteen_large_good (P H : ℕ) (hP : 5≤P) :
    ∃ v m M : ℕ, Good (2^P) 16 (2^H) v m M true := by
  let p : ℕ := 2^P
  let h : ℕ := 2^H
  let k : ℕ := 2^(P-1)
  have hp : 32≤p := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hP
  have hk : 16≤k := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 4≤P-1 by omega)
  have hpk : 2*k=p := by
    have he : P-1+1=P := by omega
    have heq := pow_succ (2:ℕ) (P-1)
    rw [he] at heq
    change 2*2^(P-1)=2^P
    omega
  have hh : 1≤h := Nat.one_le_two_pow
  have hpz : (32:ℤ)≤p := by exact_mod_cast hp
  let c : ℤ := 17+((p:ℤ)+3)%5
  let S : ℤ := (1024*(p:ℤ)+c)/5
  let j : ℤ := (5*S)%13
  let v : ℤ := (S-8*j)/13
  have hc : 17≤c ∧ c≤21 := by
    have := Int.emod_nonneg ((p:ℤ)+3) (by norm_num : (5:ℤ)≠0)
    have := Int.emod_lt_of_pos ((p:ℤ)+3) (by norm_num : (0:ℤ)<5)
    dsimp [c]; omega
  have hS : 5*S=1024*(p:ℤ)+c := by dsimp [S,c]; omega
  have hj0 : 0≤j := Int.emod_nonneg _ (by norm_num)
  have hj12 : j≤12 := by
    have := Int.emod_lt_of_pos (5*S) (by norm_num : (0:ℤ)<13)
    dsimp [j]; omega
  have heq13 : 13*v+8*j=S := by dsimp [v,j]; omega
  have heq : 65*v+40*j=1024*(p:ℤ)+c := by omega
  have hv : 1≤v ∧ v≤16*(p:ℤ) := by constructor <;> omega
  have hvcast : (v.toNat:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have hjcast : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
  have hjlt : j.toNat<2^(P-1) := by
    change j.toNat<k
    omega
  have hs := SecondPeakHighD.submask_predecessor (P-1) 49 j.toNat (by omega) hjlt
  have hmask : 2^(P-1)*49-1=49*k-1 := by dsimp [k]; omega
  rw [hmask] at hs
  have hMcast : ((49*k-1:ℕ):ℤ)=49*(k:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤49*k)]; push_cast; rfl
  refine ⟨v.toNat,h*j.toNat,h*(49*k-1),?_,?_,?_,?_,?_,?_⟩
  · rw [←hvcast] at hv; exact_mod_cast hv.1
  · have hz : 2*v≤64*(p:ℤ) := by omega
    rw [←hvcast] at hz
    have hn : 2*v.toNat≤64*p := by exact_mod_cast hz
    change 2*v.toNat≤4*p*16; omega
  · have : j.toNat<49*k-1 := by omega
    exact Nat.mul_lt_mul_of_pos_left this (by omega)
  · change 2*(h*(49*k-1))<8*h*p*16
    rw [←hpk]
    nlinarith [Nat.sub_le (49*k) 1]
  · exact submask_shift _ _ H hs
  · have hpkz : 2*(k:ℤ)=(p:ℤ) := by exact_mod_cast hpk
    have hw := q_sixteen_windows p h k c j v hpz (by exact_mod_cast hh)
      hpkz hc ⟨hj0,hj12⟩ hv heq
    simpa only [Nat.cast_ofNat,Nat.cast_mul,hvcast,hjcast,hMcast] using hw

private theorem q_sixteen_boundary_windows (h : ℤ) (hh : 1≤h) :
    Windows 4 16 h 43 (33*h) (97*h) true ∧
    Windows 8 16 h 87 (64*h) (195*h) true ∧
    Windows 16 16 h 173 (129*h) (391*h) true := by
  refine ⟨?_,?_,?_⟩
  all_goals intro r; fin_cases r
  all_goals constructor <;> constructor
  all_goals
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> omega

/-- A scale-unbounded q-sixteen selector including every small-p branch. -/
theorem q_sixteen_dyadic_good (P H : ℕ) (hP : 2≤P) :
    ∃ v m M : ℕ, ∃ before : Bool, Good (2^P) 16 (2^H) v m M before := by
  have hh : 1≤(2:ℕ)^H := Nat.one_le_two_pow
  have hw := q_sixteen_boundary_windows ((2^H:ℕ):ℤ) (by exact_mod_cast hh)
  by_cases h2 : P=2
  · subst P
    have hs : SecondPeakHighD.Submask 33 97 :=
      SecondPeakHighD.submask_of_land 33 97 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨43,33*2^H,97*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^2=4 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.1
  by_cases h3 : P=3
  · subst P
    have hs : SecondPeakHighD.Submask 64 195 :=
      SecondPeakHighD.submask_of_land 64 195 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨87,64*2^H,195*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^3=8 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.1
  by_cases h4 : P=4
  · subst P
    have hs : SecondPeakHighD.Submask 129 391 :=
      SecondPeakHighD.submask_of_land 129 391 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨173,129*2^H,391*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^4=16 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.2
  obtain ⟨v,m,M,hg⟩ := q_sixteen_large_good P H (by omega)
  exact ⟨v,m,M,true,hg⟩
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
