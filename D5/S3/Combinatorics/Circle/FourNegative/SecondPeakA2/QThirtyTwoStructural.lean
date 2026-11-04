/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QThirtyTwoStructural
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QThirtyTwoStructural
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Unbounded modulus-129 q-32 selector with exact physical windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private submask_shift from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

private theorem q_thirtytwo_first (p h : ℤ) (hp : 128 ≤ p) (hh : 1 ≤ h) :
    let j := (50*(4096*p+33))%129
    let v := (4096*p+33-80*j)/129
    First p 32 h v (h*j) true := by
  let j := (50*(4096*p+33))%129
  let v := (4096*p+33-80*j)/129
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj128 : j ≤ 128 := by
    have := Int.emod_lt_of_pos (50*(4096*p+33)) (by norm_num : (0:ℤ)<129)
    dsimp [j]; omega
  have heq : 129*v+80*j=4096*p+33 := by dsimp [v,j]; omega
  have hv0 : 1 ≤ v := by omega
  have hv4 : v ≤ 32*p := by omega
  have hA : A p 32 h=5+132096*h*p := by
    dsimp [A,SecondPeakHighD.A,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]; ring
  have hR : R p 32 h v (h*j)=5*v-1+h*(768*p+129*j) := by
    dsimp [R,A,L,K,SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,
      SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
    linear_combination 1024*h*p*heq
  have hN : 4*R p 32 h v (h*j)+2*((y p 32 h-h*j)*Q 32+1)=
      20*v-2+h*(69120*p+258*j) := by rw [hR]; dsimp [y,Q]; ring
  have hc0 : 0 ≤ 768*p+129*j := by omega
  have hc1 : 0 ≤ 130560*p-258*j := by omega
  have hc2 : 0 ≤ 69120*p+258*j := by omega
  have hc3 : 0 ≤ 62976*p-258*j := by omega
  have hprod0 := mul_nonneg (show 0≤h by omega) hc0
  have hprod1 := mul_nonneg (show 0≤h-1 by omega) hc1
  have hprod2 := mul_nonneg (show 0≤h by omega) hc2
  have hprod3 := mul_nonneg (show 0≤h-1 by omega) hc3
  change First p 32 h v (h*j) true
  dsimp only [First]
  simp only [ite_true]
  rw [hN,hR,hA]
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [hp,hj0,hj128,hv0,hv4,hprod0,hprod1,hprod2,hprod3]

private theorem q_thirtytwo_windows (p h : ℤ) (hp : 128 ≤ p) (hh : 1 ≤ h) :
    let j := (50*(4096*p+33))%129
    let v := (4096*p+33-80*j)/129
    Windows p 32 h v (h*j) (h*(50*p-1)) true := by
  let j := (50*(4096*p+33))%129
  let v := (4096*p+33-80*j)/129
  have hf := q_thirtytwo_first p h hp hh
  change First p 32 h v (h*j) true at hf
  change Windows p 32 h v (h*j) (h*(50*p-1)) true
  intro r
  fin_cases r
  · have he : SecondPeakHighD.oldEnds 4 p 32 h v (h*j) (h*(50*p-1)) 0=
        2*R p 32 h v (h*j) := by dsimp [SecondPeakHighD.oldEnds,R]; ring
    have hn : SecondPeakHighD.newEnds 4 p 32 h v (h*j) (h*(50*p-1)) true 0=
        4*R p 32 h v (h*j)+2*((y p 32 h-h*j)*Q 32+1) := by
      dsimp [SecondPeakHighD.newEnds,R,A,L,K,y,Q,SecondPeakHighD.A,
        SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SV,
        SecondPeakHighD.SW,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
      ring
    change (0≤SecondPeakHighD.oldEnds 4 p 32 h v (h*j) (h*(50*p-1)) 0 ∧
      SecondPeakHighD.oldEnds 4 p 32 h v (h*j) (h*(50*p-1)) 0≤A p 32 h-1) ∧
      (0≤SecondPeakHighD.newEnds 4 p 32 h v (h*j) (h*(50*p-1)) true 0 ∧
      SecondPeakHighD.newEnds 4 p 32 h v (h*j) (h*(50*p-1)) true 0≤A p 32 h-1)
    rw [he,hn]
    exact ⟨⟨hf.1,hf.2.1⟩,by simpa only [ite_true,sub_zero] using hf.2.2⟩
  all_goals constructor <;> constructor
  all_goals
    apply le_of_sub_nonneg
    obtain ⟨a,ha,hpa⟩ : ∃ a : ℤ, 0≤a ∧ p=a+128 := ⟨p-128,by omega,by ring⟩
    obtain ⟨b,hb,hhb⟩ : ∃ b : ℤ, 0≤b ∧ h=b+1 := ⟨h-1,by omega,by ring⟩
    rw [hpa,hhb]
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> positivity

private theorem q_thirtytwo_large_good (P H : ℕ) (hP : 7 ≤ P) :
    ∃ v m M : ℕ, Good (2^P) 32 (2^H) v m M true := by
  let p : ℕ := 2^P
  let h : ℕ := 2^H
  have hp : 128 ≤ p := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hP
  have hh : 1 ≤ h := Nat.one_le_two_pow
  let j : ℤ := (50*(4096*(p:ℤ)+33))%129
  let v : ℤ := (4096*(p:ℤ)+33-80*j)/129
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj128 : j ≤ 128 := by
    have := Int.emod_lt_of_pos (50*(4096*(p:ℤ)+33)) (by norm_num : (0:ℤ)<129)
    dsimp [j]; omega
  have hpz : (128:ℤ) ≤ p := by exact_mod_cast hp
  have heq : 129*v+80*j=4096*(p:ℤ)+33 := by dsimp [v,j]; omega
  have hv0 : 0 ≤ v := by omega
  have hjlt : j.toNat < 2^(P+1) := by
    rw [pow_succ]
    change j.toNat < p*2
    have := Int.toNat_of_nonneg hj0; omega
  have hs := SecondPeakHighD.submask_predecessor (P+1) 25 j.toNat (by omega) hjlt
  have hmask : 2^(P+1)*25-1=50*p-1 := by dsimp [p]; rw [pow_succ]; omega
  rw [hmask] at hs
  have hvcast : (v.toNat:ℤ)=v := Int.toNat_of_nonneg hv0
  have hjcast : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
  have hMcast : ((50*p-1:ℕ):ℤ)=50*(p:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤50*p)]; push_cast; rfl
  refine ⟨v.toNat,h*j.toNat,h*(50*p-1),?_,?_,?_,?_,?_,?_⟩
  · have : 1≤v := by omega
    rw [←hvcast] at this; exact_mod_cast this
  · have : 2*v≤64*(p:ℤ) := by omega
    rw [←hvcast] at this
    have hn : 2*v.toNat≤64*p := by exact_mod_cast this
    change 2*v.toNat≤4*p*32; omega
  · have : j.toNat<50*p-1 := by omega
    exact Nat.mul_lt_mul_of_pos_left this (by omega)
  · change 2*(h*(50*p-1))<8*h*p*32
    nlinarith [Nat.sub_le (50*p) 1]
  · exact submask_shift _ _ H hs
  · have hw := q_thirtytwo_windows p h hpz (by exact_mod_cast hh)
    simpa only [Nat.cast_ofNat,Nat.cast_mul,hvcast,hjcast,hMcast] using hw

private theorem q_thirtytwo_boundary_windows (h : ℤ) (hh : 1≤h) :
    Windows 4 32 h 123 (7*h) (199*h) true ∧
    Windows 8 32 h 245 (15*h) (399*h) true ∧
    Windows 16 32 h 499 (15*h) (799*h) true ∧
    Windows 32 32 h 994 (36*h) (1599*h) true ∧
    Windows 64 32 h 2002 (49*h) (3199*h) true := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals intro r; fin_cases r
  all_goals constructor <;> constructor
  all_goals
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> omega

/-- The complete scale-unbounded q-32 selector on the original physical windows. -/
theorem q_thirtytwo_dyadic_good (P H : ℕ) (hP : 2≤P) :
    ∃ v m M : ℕ, ∃ before : Bool, Good (2^P) 32 (2^H) v m M before := by
  have hh : 1≤(2:ℕ)^H := Nat.one_le_two_pow
  have hw := q_thirtytwo_boundary_windows ((2^H:ℕ):ℤ) (by exact_mod_cast hh)
  by_cases h2 : P=2
  · subst P
    have hs : SecondPeakHighD.Submask 7 199 :=
      SecondPeakHighD.submask_of_land 7 199 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨123,7*2^H,199*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^2=4 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.1
  by_cases h3 : P=3
  · subst P
    have hs : SecondPeakHighD.Submask 15 399 :=
      SecondPeakHighD.submask_of_land 15 399 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨245,15*2^H,399*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^3=8 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.1
  by_cases h4 : P=4
  · subst P
    have hs : SecondPeakHighD.Submask 15 799 :=
      SecondPeakHighD.submask_of_land 15 799 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨499,15*2^H,799*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^4=16 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.2.1
  by_cases h5 : P=5
  · subst P
    have hs : SecondPeakHighD.Submask 36 1599 :=
      SecondPeakHighD.submask_of_land 36 1599 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨994,36*2^H,1599*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^5=32 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.2.2.1
  by_cases h6 : P=6
  · subst P
    have hs : SecondPeakHighD.Submask 49 3199 :=
      SecondPeakHighD.submask_of_land 49 3199 (by decide)
    have ht := submask_shift _ _ H hs
    refine ⟨2002,49*2^H,3199*2^H,true,by norm_num,by norm_num,by omega,by omega,?_,?_⟩
    · simpa only [Nat.mul_comm] using ht
    · simpa only [show (2:ℕ)^6=64 by decide,Nat.cast_ofNat,Nat.cast_mul] using hw.2.2.2.2
  obtain ⟨v,m,M,hg⟩ := q_thirtytwo_large_good P H (by omega)
  exact ⟨v,m,M,true,hg⟩
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
