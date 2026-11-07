/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Selection
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded integer allocation of complementary U and V masks for the plus-two joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open private A B L K SU SV SW E H1 H2 J1 J2 D T window firstTwo windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Parameters
open private high_firstTwo high_aux boundary_windows boundary_stock small_firstTwo small_aux
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Arithmetic

-- Integer ceiling, proved from the remainder equation without real rounding.
private theorem rounding (b l : ℤ) (hb : 0<b) (hl : b<l) :
    let v := (l+b-1)/(2*b)
    1≤v ∧ 0≤(2*v+1)*b-l ∧ (2*v+1)*b-l<2*b := by
  dsimp only
  have hp : 0<2*b := by omega
  have hr0 := Int.emod_nonneg (l+b-1) (ne_of_gt hp)
  have hr1 := Int.emod_lt_of_pos (l+b-1) hp
  have he := Int.emod_add_mul_ediv (l+b-1) (2*b)
  have hlow : 0≤(2*((l+b-1)/(2*b))+1)*b-l := by nlinarith only [he,hr1]
  have hupp : (2*((l+b-1)/(2*b))+1)*b-l<2*b := by nlinarith only [he,hr0]
  refine ⟨?_,hlow,hupp⟩
  by_contra hn
  have hv : (l+b-1)/(2*b)≤0 := by omega
  have hmul := mul_nonpos_of_nonneg_of_nonpos hb.le hv
  nlinarith only [hmul,hlow,hl]

private theorem rounding_upper (b l m v : ℤ) (hb : 0<b)
    (hl : l<2*m*b) (hv : (2*v+1)*b-l<2*b) : v≤m := by
  by_contra hn
  have hh : m+1≤v := by omega
  have hm := mul_le_mul_of_nonneg_right hh hb.le
  nlinarith only [hm,hl,hv,hb]

private theorem high_selection (x t m : ℤ) (hx : 8≤x) (ht : 8*x≤t)
    (hm0 : 0≤m) (hm : 2*x*m=4*t) :
    ∃ u v : ℤ, 0≤u ∧ 2*u≤t-2 ∧ 0≤v ∧ 2*v≤4*t-2 ∧ windows x t u v := by
  obtain ⟨hEz,hAE,hstock,hLB,hAB⟩ := high_aux x t hx ht
  have hxpos : 0<x := by omega
  have htpos : 0<t := by omega
  have hb : 0<B x t := by dsimp [B]; positivity
  let v0 := (L x t+B x t-1)/(2*B x t)
  obtain ⟨hv0,hraw0,hraw1⟩ := rounding (B x t) (L x t) hb hLB
  change 1≤v0 at hv0
  have hd0 : 0≤D x t 0 v0 := by simpa [D] using hraw0
  have hd1 : D x t 0 v0<2*B x t := by simpa [D] using hraw1
  have hlm : L x t<2*m*B x t := by
    by_contra hh
    have he : x*(2*m*B x t)=4*t*B x t := by linear_combination B x t*hm
    have hmul := mul_le_mul_of_nonneg_left (show 2*m*B x t≤L x t by omega) hxpos.le
    linarith only [he,hmul,hstock]
  have hvm : v0≤m := rounding_upper (B x t) (L x t) m v0 hb hlm (by simpa [D] using hd1)
  have hmstock : 4*m≤t := by
    have hh := mul_le_mul_of_nonneg_right hx hm0
    nlinarith only [hh,hm]
  have ht64 : 64≤t := by omega
  have hvstock : v0+3≤t := by omega
  have hfirst := high_firstTwo x t hx ht
  by_cases hpass : T x t 0 v0≤A x t-1
  · refine ⟨0,v0,by omega,by omega,by omega,by omega,hfirst.1,⟨hd0,by omega⟩,?_,hpass⟩
    dsimp [T]
    omega
  · have hfailed : A x t≤T x t 0 v0 := by omega
    have hdshift : D x t 1 (v0+3)=D x t 0 v0+2*E x t-2*B x t := by
      dsimp [D,E]; ring
    have hEdef : A x t=4*B x t-E x t := by dsimp [E]; ring
    have hdpositive : 0≤D x t 1 (v0+3) := by
      dsimp [T] at hfailed
      nlinarith only [hfailed,hdshift,hEdef,hEz,hv0,htpos]
    have hdsmall : D x t 1 (v0+3)<2*E x t := by linarith only [hdshift,hd1]
    have hdold : D x t 1 (v0+3)≤A x t-1 := by omega
    have htnew : T x t 1 (v0+3)≤A x t-1 := by
      dsimp [T]
      linarith only [hdsmall,hAE,hv0]
    have htpos : 0≤T x t 1 (v0+3) := by dsimp [T]; omega
    exact ⟨1,v0+3,by omega,by omega,by omega,by omega,
      hfirst.2,⟨hdpositive,hdold⟩,⟨htpos,htnew⟩⟩

-- Only the selected index has a lower-bound proof. Later unused D_i may be negative.
private theorem small_selection (t m : ℤ) (ht : 128≤t) (hm : 2*m=t) :
    ∃ u v : ℤ, 0≤u ∧ 2*u≤t-2 ∧ 0≤v ∧ 2*v≤4*t-2 ∧ windows 4 t u v := by
  classical
  obtain ⟨hstock,hAB,hLB⟩ := small_aux t ht
  have htpos : 0<t := by omega
  have hb : 0<B 4 t := by dsimp [B]; positivity
  let v0 := (L 4 t+B 4 t-1)/(2*B 4 t)
  let d0 := (2*v0+1)*B 4 t-L 4 t
  obtain ⟨hv0,hd0,hd1⟩ := rounding (B 4 t) (L 4 t) hb hLB
  change 1≤v0 at hv0
  change 0≤d0 at hd0
  change d0<2*B 4 t at hd1
  have hvnonneg : 0≤v0 := by omega
  have hmb : 2*m*B 4 t=t*B 4 t := by rw [hm]
  have hlm : L 4 t<2*m*B 4 t := by nlinarith only [hstock,hmb]
  have hvm : v0≤m := rounding_upper (B 4 t) (L 4 t) m v0 hb hlm hd1
  let vi : ℕ→ℤ := fun i => v0+3*(i:ℤ)
  let di : ℕ→ℤ := fun i => d0-2*(i:ℤ)*(t+18)
  let ti : ℕ→ℤ := fun i => 2*di i+4*t-2*vi i
  have hdelta (i : ℕ) : D 4 t (i:ℤ) (vi i)=di i := by
    dsimp [D,vi,di,d0,A,B,L]; ring
  have hterminal : ti 6≤A 4 t-1 := by
    dsimp [ti,di,vi]
    norm_num only [Nat.cast_ofNat]
    dsimp [A,B] at hd1 ⊢
    nlinarith only [hd1,hv0]
  have hex : ∃ i : ℕ, i≤6 ∧ ti i≤A 4 t-1 := ⟨6,by omega,hterminal⟩
  let i := Nat.find hex
  have hispec : i≤6 ∧ ti i≤A 4 t-1 := Nat.find_spec hex
  have hi0 : 0≤(i:ℤ) := Int.natCast_nonneg i
  have hi6 : (i:ℤ)≤6 := by exact_mod_cast hispec.1
  have hvstock : vi i≤t := by dsimp [vi]; omega
  have hvpos : 0≤vi i := by dsimp [vi]; omega
  have hdpos : 0≤di i := by
    by_cases he : i=0
    · simpa [he,di] using hd0
    · have hip : i-1< i := by omega
      have hnot := Nat.find_min hex (show i-1<Nat.find hex from hip)
      have hprev : A 4 t≤ti (i-1) := by
        have hile : i-1≤6 := by omega
        omega
      have hcast : ((i-1:ℕ):ℤ)+1=(i:ℤ) := by exact_mod_cast (show i-1+1=i by omega)
      have hdnext : 2*di i=2*di (i-1)-4*(t+18) := by
        dsimp [di]
        linear_combination 4*(t+18)*hcast
      have hvprev : 0≤vi (i-1) := by dsimp [vi]; positivity
      dsimp [ti] at hprev
      dsimp [A] at hprev
      nlinarith only [hprev,hdnext,hvprev,ht]
  have hdsmall : di i<A 4 t := by
    have hp := mul_nonneg hi0 (show 0≤t+18 by omega)
    dsimp [di]
    nlinarith only [hp,hd1,hAB]
  have htpos : 0≤ti i := by dsimp [ti]; omega
  refine ⟨(i:ℤ),vi i,hi0,by omega,hvpos,by omega,?_,?_,?_⟩
  · exact small_firstTwo t (i:ℤ) ht hi0 hi6
  · rw [hdelta]
    exact ⟨hdpos,by omega⟩
  · change 0≤2*D 4 t (i:ℤ) (vi i)+4*t-2*vi i ∧
        2*D 4 t (i:ℤ) (vi i)+4*t-2*vi i≤A 4 t-1
    rw [hdelta]
    exact ⟨htpos,hispec.2⟩

private theorem half_power (d : ℕ) (hd : 1≤d) :
    (2:ℤ)^d=2*((2^(d-1):ℕ):ℤ) := by
  push_cast
  conv_lhs => rw [show d=(d-1)+1 by omega,pow_succ]
  ring

private theorem allocation (a d : ℕ) (ha : 2≤a) (had : a+2≤d)
    (hlarge : 3≤a ∨ 7≤d) :
    ∃ u v : ℕ, u<2^(d-1) ∧ v<2^(d+1) ∧
      windows ((2:ℤ)^a) ((2:ℤ)^d) u v := by
  let x : ℤ := 2^a
  let t : ℤ := 2^d
  have hhalf : t=2*((2^(d-1):ℕ):ℤ) := half_power d (by omega)
  have hvhalf : ((2^(d+1):ℕ):ℤ)=2*t := by push_cast; dsimp [t]; rw [pow_succ]; ring
  have hs : ∃ u v : ℤ, 0≤u ∧ 2*u≤t-2 ∧ 0≤v ∧ 2*v≤4*t-2 ∧ windows x t u v := by
    by_cases ha3 : 3≤a
    · have hx : 8≤x := by
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha3
        norm_num at hh
        exact hh
      by_cases he : d=a+2
      · have ht : t=4*x := by dsimp [t,x]; rw [he,pow_add]; norm_num; ring
        have hw := boundary_windows x hx
        have hst := boundary_stock x hx
        rw [ht]
        exact ⟨0,8,by omega,by omega,by omega,by omega,hw⟩
      · have ht : 8*x≤t := by
          have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show a+3≤d by omega)
          have hp : (2:ℤ)^(a+3)=8*x := by dsimp [x]; rw [pow_add]; norm_num; ring
          simpa only [hp] using hh
        let m : ℤ := 2^(d+1-a)
        have hm0 : 0≤m := by dsimp [m]; positivity
        have hm : 2*x*m=4*t := by
          dsimp [x,m,t]
          rw [mul_assoc,←pow_add,show a+(d+1-a)=d+1 by omega,pow_succ]
          ring
        exact high_selection x t m hx ht hm0 hm
    · have he : a=2 := by omega
      have hd7 : 7≤d := by omega
      have ht : 128≤t := by
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd7
        norm_num at hh
        exact hh
      have hx : x=4 := by dsimp [x]; rw [he]; norm_num
      rw [hx]
      exact small_selection t ((2^(d-1):ℕ):ℤ) ht hhalf.symm
  obtain ⟨u,v,hu0,hu,hv0,hv,hw⟩ := hs
  have cu : (u.toNat:ℤ)=u := Int.toNat_of_nonneg hu0
  have cv : (v.toNat:ℤ)=v := Int.toNat_of_nonneg hv0
  refine ⟨u.toNat,v.toNat,?_,?_,?_⟩
  · exact_mod_cast (show (u.toNat:ℤ)<((2^(d-1):ℕ):ℤ) by rw [cu]; omega)
  · exact_mod_cast (show (v.toNat:ℤ)<((2^(d+1):ℕ):ℤ) by rw [cv]; omega)
  · simpa only [cu,cv] using hw

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
