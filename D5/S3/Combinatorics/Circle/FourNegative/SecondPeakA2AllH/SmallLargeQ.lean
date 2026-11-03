/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallLargeQ
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: An unbounded large-q small-p selector. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallWindows

/-! An unbounded large-q small-p selector. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakHighD
open private ceilDiv
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Selection
open private signed_ceiling_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.IntegerSelector

def smallCeiling (p q h : ℤ) : ℤ :=
  ceilDiv (Y 4 p q h-8*h*p+4*h+5) (5*h)

/-- The prescribed M=h*ceil((y-8hp+4h+5)/(5h))-1, with its whole low bit block. -/
theorem small_ceiling_interval (p q h : ℤ)
    (hp : 4≤p) (hq : 64≤q) (hh : 4≤h) :
    2≤smallCeiling p q h ∧
    4*h≤smallDelta p q h (h*smallCeiling p q h-1) ∧
    smallDelta p q h (h*smallCeiling p q h-1)<9*h := by
  have hh0 : 0<h := by omega
  have hc := signed_ceiling_bounds (Y 4 p q h-8*h*p+4*h+5) (5*h) (by positivity)
  change Y 4 p q h-8*h*p+4*h+5≤5*h*smallCeiling p q h ∧
    5*h*smallCeiling p q h<Y 4 p q h-8*h*p+4*h+5+5*h at hc
  have hprod : 1≤p*(q-1) := by
    calc
      1≤4*63 := by norm_num
      _≤p*(q-1) := mul_le_mul hp (by omega) (by norm_num) (by omega)
  have hmul := mul_nonneg hh0.le (show 0≤p*(q-1)-1 by omega)
  have hyid : Y (4:ℤ) p q h-8*h*p=8*h*(p*(q-1)) := by dsimp [Y,T]; ring
  have hc2 : 2≤smallCeiling p q h := by
    by_contra hn
    have hn1 : smallCeiling p q h≤1 := by omega
    have hcap := mul_le_mul_of_nonneg_left hn1 (show 0≤5*h by positivity)
    rw [hyid] at hc
    nlinarith only [hc.1,hcap,hmul,hh]
  refine ⟨hc2,?_,?_⟩ <;> dsimp [smallDelta] <;> nlinarith only [hc.1,hc.2]

/-- The residue construction is proved with integer halves and quarters,
so no field division or truncated natural division enters 16R. -/
theorem small_large_q_bounds (p q h a b M : ℤ)
    (hp : 4≤p) (hp32 : p≤32) (hq : 64≤q) (hh : 4≤h)
    (ha : 4*a=p) (hb : 2*b=h)
    (hd0 : 4*h≤smallDelta p q h M) (hd1 : smallDelta p q h M≤4*h*p) :
    rowBounds 4 p q h (p*q-a) b M true := by
  have hp0 : 0<p := by omega
  have hh0 : 0<h := by omega
  have hq0 : 0<q := by omega
  have ha0 : 0≤a := by omega
  have hb0 : 0≤b := by omega
  let z := Z (4:ℤ) q
  let t := T (4:ℤ) p q
  let Q := z+1
  let AA := A (4:ℤ) p q h
  let D := 5*AA-8*h*L 4 p q
  let E := 8*h*p^2*z-5*p*(z-1)-1
  let R := (p*q-a)*AA+b*L 4 p q-K 4 p q h
  have hz : 256≤z := by dsimp [z,Z]; omega
  have hz0 : 0<z := by omega
  have hQ : 0<Q := by dsimp [Q]; omega
  have ht : t=p*z := by dsimp [t,z,T,Z]; ring
  have hT0 : 0<t := by rw [ht]; positivity
  have hA : 5≤AA := by
    have he : AA=5+8*h*t*Q := by dsimp [AA,t,Q,z,A,Y,Z,T]; ring
    rw [he]
    have hn : 0≤8*h*t*Q := by positivity
    omega
  have hDform : D=25+8*h*(5*t-Q) := by
    dsimp [D,AA,t,Q,z,A,L,Y,Z,T]; ring
  have htp : 4*z≤t := by
    rw [ht]
    have := mul_nonneg (show 0≤p-4 by omega) hz0.le
    nlinarith only [this]
  have hD : 0<D := by
    rw [hDform]
    have hdiff : 0≤5*t-Q := by dsimp [Q]; omega
    positivity
  have hhp : 16≤h*p := by
    calc
      16=4*4 := by norm_num
      _≤h*p := mul_le_mul hh hp (by norm_num) (by omega)
  have hEform : E=p*z*(8*h*p-5)+5*p-1 := by dsimp [E]; ring
  have hE : 0<E := by
    rw [hEform]
    have hdiff : 0≤8*h*p-5 := by nlinarith only [hhp]
    have hn : 0≤p*z*(8*h*p-5) := by positivity
    omega
  have hquarter : 4*(p*q*AA-K 4 p q h)=(p-1)*AA-E := by
    dsimp [AA,E,z,A,K,Y,Z,T]; ring
  have hrotation : 8*h*L 4 p q=5*AA-D := by dsimp [D]; ring
  have hR : 16*R=AA-D-4*E := by
    dsimp [R]
    linear_combination 4*hquarter+8*L (4:ℤ) p q*hb-4*AA*ha+hrotation
  have hRform : AA-D-4*E=
      8*h*p*z*(z-4-4*p)+20*p*(z-1)+8*h*Q-16 := by
    dsimp [AA,D,E,Q,z,A,L,Y,Z,T]; ring
  have hgap : 0≤z-4-4*p := by omega
  have hz1 : 0≤z-1 := by omega
  have hpos0 : 0≤8*h*p*z*(z-4-4*p) := by positivity
  have hpos1 : 0≤20*p*(z-1) := by positivity
  have hpos2 : 0<8*h*Q-16 := by
    have hmul := mul_le_mul_of_nonneg_right (show 1≤h by omega) hQ.le
    have hQ3 : 3≤Q := by dsimp [Q]; omega
    nlinarith only [hmul,hQ3]
  have hR0 : 0<R := by rw [hRform] at hR; nlinarith only [hR,hpos0,hpos1,hpos2]
  have hRcap : 16*R<AA := by nlinarith only [hR,hD,hE]
  have hS : oldEnds 4 p q h (p*q-a) b M 0=2*R := by
    dsimp [oldEnds,R,AA]; ring
  have hT : 2*newEnds 4 p q h (p*q-a) b M true 0=
      8*R+(AA-1)-2*h*Q := by
    dsimp [newEnds,R,AA,Q,z,SU,SV,SW,A,K,L,Y,Z,T]
    linear_combination -2*(4*q+1)*hb
  have hconstant : AA-1-2*h*Q=4+2*h*Q*(4*t-1) := by
    dsimp [AA,Q,t,z,A,Y,Z,T]; ring
  have hconstant0 : 0<AA-1-2*h*Q := by
    rw [hconstant]
    have ht1 : 0≤4*t-1 := by omega
    positivity
  have hcharge : 0≤h*Q := by positivity
  have hpq := mul_nonneg hp0.le (show 0≤q-1 by omega)
  have hv0 : 1≤p*q-a := by nlinarith only [hpq,ha,hp]
  have hv : 2*(p*q-a)≤T 4 p q := by
    have hpq0 : 0≤p*q := by positivity
    dsimp [T]
    nlinarith only [hpq0,ha0]
  apply finish_small_bounds p q h (p*q-a) b M true hp (by omega) hh hv0 hv hd0 hd1
  intro r
  fin_cases r
  · change 0≤oldEnds 4 p q h (p*q-a) b M 0
    rw [hS]; omega
  · change 0≤A 4 p q h-1-oldEnds 4 p q h (p*q-a) b M 0
    rw [hS]
    change 0≤AA-1-2*R
    nlinarith only [hRcap,hA]
  · change 0≤newEnds 4 p q h (p*q-a) b M true 0
    nlinarith only [hT,hconstant0,hR0]
  · change 0≤A 4 p q h-1-newEnds 4 p q h (p*q-a) b M true 0
    change 0≤AA-1-newEnds 4 p q h (p*q-a) b M true 0
    nlinarith only [hT,hRcap,hcharge,hA]

/-- Complete construction at every q>=64, for every dyadic h>=4.
The q assumption is stronger than needed for stocks and requires no dyadic cutoff. -/
theorem small_large_q_selection (p q H : ℕ)
    (hp : 4≤p) (hp32 : p≤32) (hfour : 4∣p) (hq : 64≤q) (hH : 2≤H) :
    ∃ v m M : ℕ, ∃ before : Bool, before=true ∧
      4*v+p=4*p*q ∧ 2*m=(2:ℕ)^H ∧
      (M:ℤ)=(2:ℤ)^H*smallCeiling p q (2^H)-1 ∧
      Submask m M ∧ m<M ∧ rowBounds 4 p q (2^H) v m M before := by
  obtain ⟨a,ha⟩ := hfour
  let h : ℤ := 2^H
  let b : ℕ := 2^(H-1)
  let c := smallCeiling p q h
  let v : ℤ := (p:ℤ)*q-a
  have hpZ : (4:ℤ)≤p := by exact_mod_cast hp
  have hp32Z : (p:ℤ)≤32 := by exact_mod_cast hp32
  have hqZ : (64:ℤ)≤q := by exact_mod_cast hq
  have hh : 4≤h := by
    have hh' := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hH
    norm_num at hh'
    exact hh'
  have hbNat : 2*b=(2:ℕ)^H := by
    calc
      2*b=(2:ℕ)^((H-1)+1) := by dsimp [b]; rw [pow_succ]; ring
      _=2^H := by congr 1; omega
  have hbZ : 2*(b:ℤ)=h := by
    dsimp only [h]
    exact_mod_cast hbNat
  have haZ : 4*(a:ℤ)=p := by exact_mod_cast ha.symm
  have hc := small_ceiling_interval p q h hpZ hqZ hh
  have hc2 : 2≤c := hc.1
  have hcZ : (c.toNat:ℤ)=c := Int.toNat_of_nonneg (by omega)
  have hcN : 2≤c.toNat := by omega
  have hdelta : smallDelta p q h (h*c-1)≤4*h*p := by
    have hn := mul_nonneg (show 0≤h by omega) (show 0≤4*(p:ℤ)-9 by omega)
    have hlt : smallDelta p q h (h*c-1)<9*h := hc.2.2
    nlinarith only [hn,hlt]
  have bounds := small_large_q_bounds p q h a b (h*c-1)
    hpZ hp32Z hqZ hh haZ hbZ hc.2.1 hdelta
  have hv0 : 1≤v := bounds.2.1
  have hvZ : (v.toNat:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have hb0 : 0<b := by dsimp [b]; positivity
  have hm : b<2^H := by omega
  have bits := small_proper_predecessor H c.toNat b hcN hm
  have hprod : 1≤(2:ℕ)^H*c.toNat :=
    mul_pos (Nat.two_pow_pos H) (by omega)
  have hMZ : (((2:ℕ)^H*c.toNat-1:ℕ):ℤ)=h*c-1 := by
    rw [Nat.cast_sub hprod]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hcZ,h]
  have hvEq : 4*v.toNat+p=4*p*q := by
    have he : 4*(v.toNat:ℤ)+(p:ℤ)=4*(p:ℤ)*q := by
      rw [hvZ]
      dsimp [v]
      linear_combination -haZ
    exact_mod_cast he
  refine ⟨v.toNat,b,2^H*c.toNat-1,true,rfl,hvEq,hbNat,hMZ,bits.1,bits.2,?_⟩
  simpa only [hvZ,hMZ] using bounds

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
