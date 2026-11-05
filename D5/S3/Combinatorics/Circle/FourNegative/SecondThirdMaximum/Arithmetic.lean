/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-by-physical-endpoint)
   mirror-E: none(waiver:private-consumed-by-physical-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Constructive paired available grids and exact equal-maximum seam inequalities. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

/-! Constructive integer selectors for the original-label construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum

private def A (x z : ℤ) : ℤ := 1+x+x*z+x*z^2
private def B (x t z : ℤ) : ℤ := 1+t+x*t+x*z*t
private def L (x t z : ℤ) : ℤ := 1+z+z*t+x*z*t
private def K (t z : ℤ) : ℤ := 1+z+z^2+z^2*t
private def SU (x t z : ℤ) : ℤ := 2*B x t z-1
private def SV (x t z : ℤ) : ℤ := 2*L x t z-1-z
private def SW (t z : ℤ) : ℤ := 2*K t z-1-z-z^2
private def old2 (x t z n h p : ℤ) : ℤ :=
  2*h*L x t z+2*p*B x t z+B x t z-n*K t z
private def new2 (x t z n h p : ℤ) : ℤ :=
  2*h*SV x t z+2*p*SU x t z+SU x t z-n*SW t z
private def middle (x t z n h p : ℤ) : Prop :=
  0≤old2 x t z n h p ∧ new2 x t z n h p≤A x z-1

/-- Integer ceiling, with a strict error bound, including v=0. -/
private theorem ceiling (m B v : ℤ) (hm : 1≤m) (hB : 0<B)
    (hv : 0≤v) (hcap : v≤(m-1)*B) :
    ∃ p : ℤ, 0≤p ∧ p≤m-1 ∧ v≤p*B ∧ p*B<v+B := by
  let p := (v+B-1)/B
  have hp : 0≤p := Int.ediv_nonneg (by omega) hB.le
  have hr0 := Int.emod_nonneg (v+B-1) (ne_of_gt hB)
  have hr1 := Int.emod_lt_of_pos (v+B-1) hB
  have he := Int.emod_add_mul_ediv (v+B-1) B
  change (v+B-1)%B+B*p=v+B-1 at he
  have helo : v≤p*B := by nlinarith only [he,hr1]
  have hehi : p*B<v+B := by nlinarith only [he,hr0]
  have hpcap : p≤m-1 := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_right (show m≤p by omega) hB.le
    nlinarith only [hm,hcap,hehi,hmul]
  exact ⟨p,hp,hpcap,helo,hehi⟩

/-- The three-case quotient/residue selector on actual paired grids.
No finite-minimum or density premise is left to a caller. -/
private theorem paired_grid (m B L J T : ℤ)
    (hm : 3≤m) (hJ : 1≤J) (hB : 0<B) (hBL : B<L)
    (hover : L≤(m-1)*B) (hgap : (m-1)*(L-B)<B)
    (hT : 0≤T) (hmax : T≤(m*(J-1)+1)*L+(m-1)*B) :
    ∃ H e p : ℤ, 0≤H ∧ H<J ∧ (e=0 ∨ e=1) ∧
      0≤p ∧ p≤m-1 ∧ T≤(m*H+e)*L+p*B ∧
      (m*H+e)*L+p*B<T+B := by
  let q := T/(m*L)
  let r := T%(m*L)
  have hL : 0<L := lt_trans hB hBL
  have hmL : 0<m*L := mul_pos (by omega) hL
  have hq : 0≤q := Int.ediv_nonneg hT hmL.le
  have hr0 : 0≤r := Int.emod_nonneg T (ne_of_gt hmL)
  have hr1 : r<m*L := Int.emod_lt_of_pos T hmL
  have he : r+m*L*q=T := Int.emod_add_mul_ediv T (m*L)
  have hqJ : q<J := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_right (show J≤q by omega) hmL.le
    have hid : m*J*L-((m*(J-1)+1)*L+(m-1)*B)=(m-1)*(L-B) := by ring
    have hpos : 0<(m-1)*(L-B) := mul_pos (by omega) (by omega)
    nlinarith only [hmax,he,hr0,hmul,hid,hpos]
  by_cases h0 : r≤(m-1)*B
  · obtain ⟨p,hp,hpc,hlo,hhi⟩ := ceiling m B r (by omega) hB hr0 h0
    refine ⟨q,0,p,hq,hqJ,Or.inl rfl,hp,hpc,?_,?_⟩ <;>
      nlinarith only [he,hlo,hhi]
  · by_cases h1 : r≤L+(m-1)*B
    · obtain ⟨p,hp,hpc,hlo,hhi⟩ :=
        ceiling m B (r-L) (by omega) hB (by omega) (by omega)
      refine ⟨q,1,p,hq,hqJ,Or.inr rfl,hp,hpc,?_,?_⟩ <;>
        nlinarith only [he,hlo,hhi]
    · have hnext : q+1<J := by
        by_contra hh
        have hlast : q=J-1 := by omega
        rw [hlast] at he
        nlinarith only [he,hmax,h1]
      refine ⟨q+1,0,0,by omega,hnext,Or.inl rfl,le_rfl,by omega,?_,?_⟩
      · nlinarith only [he,hr1]
      · nlinarith only [he,h1,hgap]

/-- Uniform first and paid-last seams. The shifts leave polynomials with
nonnegative coefficients; this includes x=4, t=2x, z=2t. -/
private theorem universal (x t z : ℤ) (hx : 4≤x) (ht : 2*x≤t) (hz : 2*t≤z) :
    0≤B x t z+K t z-2*A x z ∧
    B x t z+K t z-2*A x z≤K t z-1 ∧
    0≤SU x t z+SW t z-2*A x z ∧
    SU x t z+SW t z-2*A x z≤SW t z-1 ∧
    0≤2*(x*B x t z-(x-1)*L x t z) ∧
    2*(x*B x t z-(x-1)*L x t z)≤B x t z-1 ∧
    0≤2*(x*SU x t z-(x-1)*SV x t z) ∧
    2*(x*SU x t z-(x-1)*SV x t z)≤SU x t z-1 ∧
    0<B x t z ∧ B x t z<L x t z ∧
    (x-1)*(L x t z-B x t z)<B x t z ∧
    B x t z<x*t*z^2-1 ∧ A x z≤x*t*z^2-1 := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ x=4+u := ⟨x-4,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2*(4+u)+v := ⟨t-2*(4+u),by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ z=2*(2*(4+u)+v)+w :=
    ⟨z-2*(2*(4+u)+v),by omega,by omega⟩
  dsimp [A,B,L,K,SU,SV,SW]
  repeat' constructor
  all_goals first
    | (apply sub_nonneg.mp; ring_nf; positivity)
    | (apply sub_pos.mp; ring_nf; positivity)

private theorem discrepancy (x t z n H e p J : ℤ)
    (hx : 4≤x) (hz : 0≤z) (hn : 1≤n) (hH : H<J)
    (he : e=0 ∨ e=1) (hp : p<x) (hJ : 2*x*J=z) :
    0≤new2 x t z n (x*H+e) p-2*old2 x t z n (x*H+e) p := by
  have he' : e≤1 := by omega
  have hh : 2*(x*H+e)≤z-2*x+2 := by
    have := mul_le_mul_of_nonneg_left (show H≤J-1 by omega) (show 0≤x by omega)
    nlinarith only [this,hJ,he']
  have nn := mul_nonneg (show 0≤n-1 by omega) (show 0≤1+z+z^2 by positivity)
  have hs := mul_nonneg (show 0≤z+1 by omega) (show 0≤z-2*x+2-2*(x*H+e) by omega)
  have hbase := mul_nonneg (show 0≤x-1 by omega) hz
  dsimp [new2,old2,SU,SV,SW,A,B,L,K]
  nlinarith only [nn,hs,hbase,hp]

private theorem regular_boundary (x t n h p : ℤ)
    (hx : 4≤x) (ht : 2*x≤t) (hn : 1≤n) (hnx : 2*n≤x)
    (hh : x≤h) (hp : 0≤p) (hpx : p<x)
    (he : n*t=(x+1)*h+x*p) : middle x t (2*t) n h p := by
  have eid : old2 x t (2*t) n h p=
      (2*x-4*n)*t^2+(4*h+2*p*(x+1)-2*n+x+1)*t+2*h+2*p-n+1 := by
    dsimp [old2,B,L,K]
    linear_combination (-4*t^2)*he
  have nid : new2 x t (2*t) n h p-(A x (2*t)-1)=
      4*t*(p-x*h)+2*(1-n)*t+2*h+2*p+1-n-x := by
    dsimp [new2,SU,SV,SW,A,B,L,K]
    linear_combination (-8*t^2-4*t)*he
  have h0 := mul_nonneg (show 0≤2*x-4*n by omega) (sq_nonneg t)
  have h1 := mul_nonneg (show 0≤4*h+2*p*(x+1)-2*n+x+1 by
    have := mul_nonneg hp (show 0≤x+1 by omega); nlinarith) (show 0≤t by omega)
  have hph : p-x*h≤-h := by
    have := mul_nonneg (show 0≤x-2 by omega) (show 0≤h by omega)
    nlinarith
  have h2 := mul_nonneg (show 0≤t by omega) (show 0≤-h-(p-x*h) by omega)
  have h3 := mul_nonneg (show 0≤t-1 by omega) (show 0≤h by omega)
  have h4 := mul_nonneg (show 0≤n-1 by omega) (show 0≤t by omega)
  constructor
  · nlinarith only [eid,h0,h1,hh,hpx,hp,hnx,hx]
  · nlinarith only [nid,h2,h3,h4,hph,hpx,hh,hn,hx]

private theorem first_boundary (y : ℤ) (hy : 1≤y) :
    middle (4*y) (8*y) (16*y) (2*y+1) (4*y+1) 0 := by
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ y=v+1 := ⟨y-1,by omega,by omega⟩
  dsimp [middle,old2,new2,A,B,L,K,SU,SV,SW]
  constructor
  · ring_nf; positivity
  · apply sub_nonneg.mp; ring_nf; positivity

private theorem four_boundary (t h : ℤ) (ht : 16≤t) (he : 5*h=3*(t-1)) :
    middle 4 t (2*t) 3 h 1 := by
  have eid : 5*old2 4 t (2*t) 3 h 1=12*t^2+39*t-6 := by
    dsimp [old2,B,L,K]
    linear_combination (20*t^2+4*t+2)*he
  have nid : 5*(A 4 (2*t)-1-new2 4 t (2*t) 3 h 1)=
      2*(4*t^2-37*t+13) := by
    dsimp [new2,SU,SV,SW,A,B,L,K]
    linear_combination (-40*t^2-4*t-2)*he
  have hsq := mul_nonneg (show 0≤t by omega) (show 0≤4*t-37 by omega)
  constructor <;> nlinarith [sq_nonneg t]

private theorem moderate (x t z h p e : ℤ) (hx : 4≤x) (ht : 2*x≤t)
    (hz : 4*t≤z) (hzx : z≤x*t) (hh : 0≤h)
    (hp : 1≤p) (hpx : p<x) (he : e=0 ∨ e=1)
    (hrel : 2*(x+1)*h+2*x*p=z+2*e) : middle x t z 1 h p := by
  have he0 : 0≤e := by omega
  have he1 : e≤1 := by omega
  have eid : old2 x t z 1 h p=(x+2*e)*z*t+(2*p+1)*(x+1)*t-z^2+
      (2*h-1)*z+2*(h+p) := by
    dsimp [old2,B,L,K]
    linear_combination (z*t)*hrel
  have nid : new2 x t z 1 h p=2*(x+2*e)*z*t+2*(2*p+1)*(x+1)*t-z^2+
      (2*h-1)*z+2*(h+p) := by
    dsimp [new2,SU,SV,SW,B,L,K]
    linear_combination (2*z*t)*hrel
  have ht0 : 0≤t := by omega
  have hz0 : 0≤z := by omega
  have hzt0 : 0≤z*t := mul_nonneg hz0 ht0
  have h8x : 8*x≤z := by omega
  have h8h : 8*h≤z := by
    have := mul_nonneg (show 0≤x-3 by omega) hh
    have hxp := mul_le_mul_of_nonneg_left hp (show 0≤x by omega)
    nlinarith only [this,hxp,hrel,he1,hx]
  have h8p : 8*p≤z-8 := by omega
  have hsum : 2*(h+p)≤z := by omega
  have first := mul_nonneg hz0 (show 0≤x*t-z by omega)
  have eps := mul_nonneg he0 hzt0
  have ph := mul_nonneg (show 0≤p by omega) (show 0≤(x+1)*t by positivity)
  have hhead := mul_nonneg hh hz0
  have lower : 0≤old2 x t z 1 h p := by
    nlinarith only [eid,first,eps,ph,hhead,hzx,ht0,hp,hh]
  have hzt := mul_nonneg hz0 (show 0≤z-4*t by omega)
  have hzsq := mul_nonneg (show 0≤z-4*t by omega) (show 0≤z+4*t by omega)
  have htsq := mul_nonneg (show 0≤x*t by positivity) (show 0≤t-2*x by omega)
  have hxzs := mul_nonneg (show 0≤x by omega) (show 0≤z^2-16*t^2 by nlinarith only [hzsq])
  have hpcoef : (2*p+1)*(x+1)≤4*x^2 := by nlinarith [mul_nonneg (show 0≤x-p by omega) (show 0≤x+1 by omega)]
  have hpc := mul_le_mul_of_nonneg_right hpcoef ht0
  have hbnd : 8*(2*p+1)*(x+1)*t≤x*z^2 := by nlinarith only [hpc,htsq,hxzs]
  have hezt := mul_nonneg (show 0≤1-e by omega) hzt0
  have hscaled := mul_nonneg (show 0≤x+2 by omega) (show 0≤z^2-4*z*t by nlinarith only [hzt])
  have hhz := mul_nonneg hz0 (show 0≤z-8*h by omega)
  have nbnd : 4*new2 x t z 1 h p≤(3*x+1)*z^2 := by
    nlinarith only [nid,hbnd,hezt,hscaled,hhz,hsum]
  have hlast := mul_nonneg (show 0≤x-1 by omega) (sq_nonneg z)
  have hxz := mul_nonneg (show 0≤x by omega) hz0
  refine ⟨lower,?_⟩
  dsimp [A]
  nlinarith only [nbnd,hlast,hxz,hx]

private theorem high (x t z J : ℤ) (hx : 4≤x) (ht : 2*x≤t)
    (hz : 2*x*t≤z) (hJ : 1≤J) (hJz : 2*x*J=z)
    (hodd : (K t z-B x t z)%2=0) :
    ∃ H e p : ℤ, 0≤H ∧ H<J ∧ (e=0 ∨ e=1) ∧
      0≤p ∧ p<x ∧ middle x t z 1 (x*H+e) p := by
  have hzt : 2*t≤z := by nlinarith [mul_nonneg (show 0≤x-1 by omega) (show 0≤t by omega)]
  have uni := universal x t z hx ht hzt
  have hB := uni.2.2.2.2.2.2.2.2.1
  have hBL := uni.2.2.2.2.2.2.2.2.2.1
  have hgap := uni.2.2.2.2.2.2.2.2.2.2.1
  have hNB := uni.2.2.2.2.2.2.2.2.2.2.2.1
  have hD : 0≤L x t z-B x t z := by omega
  have hL2 : L x t z<2*B x t z := by
    have := mul_nonneg (show 0≤x-2 by omega) hD
    nlinarith only [hgap,this]
  have hover : L x t z≤(x-1)*B x t z := by
    have := mul_nonneg (show 0≤x-3 by omega) hB.le
    nlinarith only [this,hL2]
  let T := (K t z-B x t z)/2
  have hT2 : 2*T=K t z-B x t z := by
    have := Int.emod_add_mul_ediv (K t z-B x t z) 2
    dsimp [T]; omega
  have hKB : 0≤K t z-B x t z := by
    obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ x=4+u := ⟨x-4,by omega,by omega⟩
    obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2*(4+u)+v := ⟨t-2*(4+u),by omega,by omega⟩
    obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ z=2*(4+u)*(2*(4+u)+v)+w :=
      ⟨z-2*(4+u)*(2*(4+u)+v),by omega,by omega⟩
    dsimp [K,B]; ring_nf; positivity
  have hmax : T≤(x*(J-1)+1)*L x t z+(x-1)*B x t z := by
    have hid : 2*((x*(J-1)+1)*L x t z+(x-1)*B x t z)-
        (K t z-B x t z)=(x*t*z^2-1)-B x t z+
        2*(x*B x t z-(x-1)*L x t z) := by
      dsimp [L,B,K]
      linear_combination (1+z+z*t+x*z*t)*hJz
    nlinarith only [hid,hT2,hNB,uni.2.2.2.2.1]
  obtain ⟨H,e,p,hH0,hHJ,he,hp,hpx,hlo,hhi⟩ :=
    paired_grid x (B x t z) (L x t z) J T (by omega) hJ hB hBL hover hgap
      (by omega) hmax
  have hold : 0≤old2 x t z 1 (x*H+e) p ∧ old2 x t z 1 (x*H+e) p<2*B x t z := by
    dsimp [old2]; constructor <;> nlinarith only [hT2,hlo,hhi]
  have hh : 0≤x*H+e := by rcases he with rfl|rfl <;> positivity
  have hd : new2 x t z 1 (x*H+e) p-2*old2 x t z 1 (x*H+e) p≤z*(z+1) := by
    have hs:=mul_nonneg hh (show 0≤z+1 by omega)
    dsimp [new2,old2,SU,SV,SW,B,L,K]
    nlinarith only [hs,hp]
  have hBupper : B x t z≤x*z*t+z := by
    dsimp [B]
    have := mul_nonneg (show 0≤x-2 by omega) (show 0≤t by omega)
    nlinarith only [hz,this,hx,ht]
  have hprod := mul_nonneg (show 0≤z by omega) (show 0≤z-2*x*t by omega)
  have hb2 : 2*B x t z≤z^2+2*z := by nlinarith only [hBupper,hprod]
  have margin : 0<A x z-1-4*B x t z-z*(z+1) := by
    have hid : A x z-1-4*B x t z-z*(z+1)≥
        (x-4)*(z^2+z+1)+z^2-z+4 := by dsimp [A]; nlinarith only [hb2]
    have hz0 : 0≤z := by omega
    have h0:=mul_nonneg (show 0≤x-4 by omega) (show 0≤z^2+z+1 by positivity)
    have h1:=mul_nonneg (show 0≤z by omega) (show 0≤z-1 by omega)
    nlinarith only [hid,h0,h1]
  refine ⟨H,e,p,hH0,hHJ,he,hp,by omega,hold.1,?_⟩
  nlinarith only [hold.2,hd,margin]

private theorem pow_split (n j : ℕ) (h : j≤n) :
    (2:ℤ)^n=2^j*2^(n-j) := by rw [←pow_add,Nat.add_sub_of_le h]

private theorem pow_even (n : ℕ) (hn : 1≤n) : (2:ℤ)^n%2=0 := by
  rw [pow_split n 1 hn]
  norm_num [Int.mul_emod]

private theorem odd_not_dvd_pow (m : ℤ) (hm : 2≤m) (ho : m%2=1) (n : ℕ) :
    ¬m∣(2:ℤ)^n := by
  induction n with
  | zero =>
    rintro ⟨q,hq⟩
    norm_num only [pow_zero] at hq
    by_cases hq0 : q≤0
    · have := mul_nonpos_of_nonneg_of_nonpos (show 0≤m by omega) hq0
      nlinarith only [hq,this]
    · have := mul_le_mul_of_nonneg_left (show 1≤q by omega) (show 0≤m by omega)
      nlinarith only [hq,this,hm]
  | succ n ih =>
    intro hd
    obtain ⟨q,hq⟩ : m∣2*(2:ℤ)^n := by simpa only [pow_succ,mul_comm] using hd
    have he := Int.emod_add_mul_ediv m 2
    rw [ho] at he
    apply ih
    refine ⟨(m/2+1)*q-(2:ℤ)^n,?_⟩
    calc
      (2:ℤ)^n=(m/2+1)*(2*(2:ℤ)^n)-m*(2:ℤ)^n := by
        linear_combination -((2:ℤ)^n)*he
      _=m*((m/2+1)*q-(2:ℤ)^n) := by rw [hq]; ring

/-- All three exponent ranges, including all five boundary rows. The integer
selectors are later converted to physical masks by proved nonnegativity. -/
private theorem selector_data (a s d : ℕ) (ha : 2≤a) (had : a<d) (hds : d<s) :
    let x : ℤ:=2^a
    let t : ℤ:=2^d
    let z : ℤ:=2^s
    let J : ℤ:=2^(s-a-1)
    ∃ n H e p : ℤ, 1≤n ∧ n<x ∧ n%2=1 ∧ 0≤H ∧ H<J ∧
      (e=0 ∨ e=1) ∧ 0≤p ∧ p<x ∧ middle x t z n (x*H+e) p := by
  dsimp only
  let x : ℤ:=2^a
  let t : ℤ:=2^d
  let z : ℤ:=2^s
  let J : ℤ:=2^(s-a-1)
  change ∃ n H e p : ℤ, 1≤n ∧ n<x ∧ n%2=1 ∧ 0≤H ∧ H<J ∧
    (e=0 ∨ e=1) ∧ 0≤p ∧ p<x ∧ middle x t z n (x*H+e) p
  have hx : 4≤x := by dsimp [x]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha; norm_num at this; exact this
  have ht : 2*x≤t := by
    have he : 2*x=(2:ℤ)^(a+1) := by dsimp [x]; rw [pow_succ]; ring
    rw [he]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hz : 2*t≤z := by
    have he : 2*t=(2:ℤ)^(d+1) := by dsimp [t]; rw [pow_succ]; ring
    rw [he]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hJ : 1≤J := by dsimp [J]; exact one_le_pow₀ (by norm_num)
  have hJz : 2*x*J=z := by
    dsimp [x,J,z]
    calc
      2*(2:ℤ)^a*2^(s-a-1)=2^(a+(s-a-1)+1) := by rw [pow_succ,pow_add]; ring
      _=2^s := by congr 1; omega
  have xe : x%2=0 := pow_even a (by omega)
  have te : t%2=0 := pow_even d (by omega)
  have ze : z%2=0 := pow_even s (by omega)
  have hodd : (K t z-B x t z)%2=0 := by
    norm_num [K,B,pow_two,Int.add_emod,Int.sub_emod,Int.mul_emod,xe,te,ze]
  by_cases hboundary : s=d+1
  · have zt : z=2*t := by dsimp [z,t]; rw [hboundary,pow_succ]; ring
    let r : ℤ:=2^(d-a)
    have Jr : J=r := by dsimp [J,r]; congr 1; omega
    have hr : 2≤r := by
      dsimp [r]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤d-a by omega)
      norm_num at this; exact this
    have trx : t=x*r := by dsimp [t,x,r]; rw [←pow_add]; congr 1; omega
    by_cases hfirst : d=a+1
    · have rr : r=2 := by dsimp [r]; rw [hfirst,show a+1-a=1 by omega]; norm_num
      let y : ℤ:=2^(a-2)
      have hy : 1≤y := by dsimp [y]; exact one_le_pow₀ (by norm_num)
      have xy : x=4*y := by dsimp [x,y]; rw [pow_split a 2 ha]; norm_num
      have tt : t=8*y := by rw [trx,rr,xy]; ring
      have zz : z=16*y := by rw [zt,tt]; ring
      have cap : 1<J := by rw [Jr,rr]; norm_num
      refine ⟨2*y+1,1,1,0,by omega,by omega,by omega,by omega,cap,Or.inr rfl,le_rfl,by omega,?_⟩
      simpa only [xy,tt,zz,mul_one] using first_boundary y hy
    · have hr4 : 4≤r := by
        dsimp [r]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤d-a by omega)
        norm_num at this; exact this
      by_cases hsmall : d<2*a
      · let q : ℤ:=2^(2*a-d)
        have hq2 : 2≤q := by
          dsimp [q]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤2*a-d by omega)
          norm_num at this; exact this
        have qe : q%2=0 := pow_even (2*a-d) (by omega)
        have xrq : x=r*q := by dsimp [x,r,q]; rw [←pow_add]; congr 1; omega
        have hnx : 2*(q+1)≤x := by
          have := mul_nonneg (show 0≤r-4 by omega) (show 0≤q by omega)
          nlinarith only [xrq,hr4,hq2,this]
        have cap : 1<J := by rw [Jr]; omega
        have hpx : r-1<x := by
          have := mul_nonneg (show 0≤r by omega) (show 0≤q-1 by omega)
          nlinarith only [xrq,hq2,hr4,this]
        have rel : (q+1)*t=(x+1)*x+x*(r-1) := by rw [trx,xrq]; ring
        refine ⟨q+1,1,0,r-1,by omega,by omega,by omega,by omega,cap,Or.inl rfl,by omega,hpx,?_⟩
        simpa only [zt,mul_one,add_zero] using
          regular_boundary x t (q+1) x (r-1) hx ht (by omega) hnx le_rfl (by omega) hpx rel
      · let q := r/(x+1)
        let v := r%(x+1)
        have q0 : 0≤q := Int.ediv_nonneg (by omega) (by omega)
        have v0 : 0≤v := Int.emod_nonneg _ (by omega)
        have vx : v≤x := by have := Int.emod_lt_of_pos r (show 0<x+1 by omega); omega
        have rq : v+(x+1)*q=r := Int.emod_add_mul_ediv r (x+1)
        have rx : x≤r := by
          dsimp [x,r]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        by_cases hv : v<x
        · have q1 : 1≤q := by
            by_contra hq1
            have qz : q=0 := by omega
            rw [qz] at rq
            simp only [mul_zero,add_zero] at rq
            omega
          have hh : x≤x*q := by
            have := mul_nonneg (show 0≤x by omega) (show 0≤q-1 by omega)
            nlinarith only [this]
          have cap : q<J := by
            rw [Jr]
            have hmul:=mul_nonneg (show 0≤x-1 by omega) q0
            nlinarith only [rq,hx,hr,q0,hmul,v0]
          have rel : t=(x+1)*(x*q)+x*v := by rw [trx,←rq]; ring
          refine ⟨1,q,0,v,le_rfl,by omega,by norm_num,q0,cap,Or.inl rfl,v0,hv,?_⟩
          simpa only [zt,add_zero,one_mul] using
            regular_boundary x t 1 (x*q) v hx ht le_rfl (by omega) hh v0 hv (by simpa only [one_mul] using rel)
        · have vv : v=x := by omega
          let q3 := 3*r/(x+1)
          have q30 : 0≤q3 := Int.ediv_nonneg (by omega) (by omega)
          have rem3 : 3*r%(x+1)=x-2 := by
            have hm : 0≤x-2 ∧ x-2<x+1 := by omega
            have he : 3*r=(x+1)*(3*q+2)+(x-2) := by rw [←rq,vv]; ring
            rw [he]
            simp only [Int.add_emod,Int.mul_emod,Int.emod_self,zero_mul,
              Int.zero_emod,zero_add,Int.emod_emod]
            exact Int.emod_eq_of_lt hm.1 hm.2
          have rq3 : x-2+(x+1)*q3=3*r := by
            have := Int.emod_add_mul_ediv (3*r) (x+1); rw [rem3] at this; exact this
          have q31 : 1≤q3 := by
            by_contra hq31
            have qz : q3=0 := by omega
            rw [qz] at rq3
            simp only [mul_zero,add_zero] at rq3
            omega
          have qcap : q3<J := by
            rw [Jr]
            have hmul:=mul_nonneg (show 0≤x-3 by omega) q30
            nlinarith only [rq3,hx,rx,q30,hmul]
          by_cases hfour : a=2
          · have xx : x=4 := by dsimp [x]; rw [hfour]; norm_num
            have t16 : 16≤t := by
              rw [xx] at trx rx
              nlinarith only [trx,rx]
            have rel : 5*(x*q3+1)=3*(t-1) := by rw [xx] at rq3 trx ⊢; nlinarith only [rq3,trx]
            refine ⟨3,q3,1,1,by omega,by omega,by norm_num,q30,qcap,Or.inr rfl,by omega,by omega,?_⟩
            simpa only [xx,zt] using four_boundary t (x*q3+1) t16 rel
          · have x8 : 8≤x := by
              dsimp [x]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤a by omega)
              norm_num at this; exact this
            have rel : 3*t=(x+1)*(x*q3)+x*(x-2) := by rw [trx]; linear_combination -x*rq3
            have hh : x≤x*q3 := by
              have := mul_nonneg (show 0≤x by omega) (show 0≤q3-1 by omega)
              nlinarith only [this]
            refine ⟨3,q3,0,x-2,by omega,by omega,by norm_num,q30,qcap,Or.inl rfl,by omega,by omega,?_⟩
            simpa only [zt,add_zero] using regular_boundary x t 3 (x*q3) (x-2) hx ht
              (by omega) (by omega) hh (by omega) (by omega) rel
  · by_cases hmoderate : s≤a+d
    · have hz4 : 4*t≤z := by
        have he : 4*t=(2:ℤ)^(d+2) := by dsimp [t]; rw [pow_add]; norm_num; ring
        rw [he]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hzx : z≤x*t := by
        dsimp [z,x,t]; rw [←pow_add]; exact pow_le_pow_right₀ (by norm_num) hmoderate
      let H := J/(x+1)
      let v := J%(x+1)
      have hH : 0≤H := Int.ediv_nonneg (by omega) (by omega)
      have hv0 : 0≤v := Int.emod_nonneg _ (by omega)
      have hvx : v≤x := by have := Int.emod_lt_of_pos J (show 0<x+1 by omega); omega
      have rel : v+(x+1)*H=J := Int.emod_add_mul_ediv J (x+1)
      have hv : 1≤v := by
        have notdiv : ¬ x+1 ∣ J := by
          exact odd_not_dvd_pow (x+1) (by omega) (by omega) (s-a-1)
        by_contra hh
        have vz : v=0 := by omega
        exact notdiv (Int.dvd_of_emod_eq_zero vz)
      have cap : H<J := by
        have hmul:=mul_nonneg (show 0≤x by omega) hH
        nlinarith only [rel,hv,hmul]
      have relx:=congrArg (fun q : ℤ => 2*x*q) rel
      by_cases hve : v=x
      · rw [hve] at relx
        have hmid := moderate x t z (x*H+1) (x-1) 1 hx ht hz4 hzx
          (by positivity) (by omega) (by omega) (Or.inr rfl) (by
            nlinarith only [hJz,relx])
        exact ⟨1,H,1,x-1,le_rfl,by omega,by norm_num,hH,cap,Or.inr rfl,by omega,by omega,hmid⟩
      · have hmid := moderate x t z (x*H) v 0 hx ht hz4 hzx
          (by positivity) hv (by omega) (Or.inl rfl) (by nlinarith only [hJz,relx])
        exact ⟨1,H,0,v,le_rfl,by omega,by norm_num,hH,cap,Or.inl rfl,by omega,by omega,by simpa using hmid⟩
    · have hhigh : 2*x*t≤z := by
        have he : 2*x*t=(2:ℤ)^(a+d+1) := by dsimp [x,t]; rw [pow_succ,pow_add]; ring
        rw [he]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      obtain ⟨H,e,p,hH,cap,he,hp,hpx,hm⟩ := high x t z J hx ht hhigh hJ hJz hodd
      exact ⟨1,H,e,p,le_rfl,by omega,by norm_num,hH,cap,he,hp,hpx,hm⟩

private theorem selector_exists (a s d : ℕ) (ha : 2≤a) (had : a<d) (hds : d<s) :
    ∃ n H e p w : ℤ, 1≤n ∧ n<(2:ℤ)^a ∧
      0≤H ∧ H<(2:ℤ)^(s-a-1) ∧ (e=0 ∨ e=1) ∧
      0≤p ∧ p<(2:ℤ)^a ∧ 0≤w ∧ 2*w+n+1=(2:ℤ)^a ∧
      middle (2^a) (2^d) (2^s) n (2^a*H+e) p := by
  obtain ⟨n,H,e,p,hn,hnx,hodd,hH,hHJ,he,hp,hpx,hm⟩ := selector_data a s d ha had hds
  let w := ((2:ℤ)^a-n-1)/2
  have xe := pow_even a (by omega)
  have rem : ((2:ℤ)^a-n-1)%2=0 := by omega
  have hw : 0≤w := Int.ediv_nonneg (by omega) (by norm_num)
  have hr := Int.emod_add_mul_ediv ((2:ℤ)^a-n-1) 2
  refine ⟨n,H,e,p,w,hn,hnx,hH,hHJ,he,hp,hpx,hw,?_,hm⟩
  dsimp [w]; omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum
