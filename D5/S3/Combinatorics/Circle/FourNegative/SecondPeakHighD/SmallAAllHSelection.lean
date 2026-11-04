/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHSelection
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Closed a=3,4 selector, unbounded in P,Q,H, on exact old/new heads. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHCertificates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Rounding
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.IntegerCertificates
import Mathlib.Tactic.LinearCombination

/-! The selector combines the signed ceiling and parity remainder with polynomial
tail bounds and universal dyadic families. Its two charge identities come from
SmallAAllHData, and all branches use the same actual physical endpoint heads. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
open private ceilInt chooseM ceiling_M ceiling_M_bits parityJ parity_remainder
  parity_standard_cap parity_odd_cap first_remainder_identity
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Rounding
open private int_base_K_gt_B int_base_C_positive int_base_second_slack int_base_M_stock
  int_base_S3_lower int_base_S3_upper int_base_T3_lower int_base_T3_upper
  int_base_F2_positive int_first_large int_first_small_R_lower int_first_small_T1_upper
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.IntegerCertificates

open private int_tail_R32 int_tail_R8 int_tail_R8q4 int_tail_R16 int_tail_R16q4 int_tail_R16odd
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.IntegerCertificates

private theorem generic_M_second (x p q h D : ℤ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) (hD : 2*D=h*p) :
    let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
    0≤M ∧ 2*M≤Y x p q h-2 ∧
      ∀ v m : ℤ, ∀ before : Bool,
        0≤oldEnds x p q h v m M 1 ∧
        oldEnds x p q h v m M 1≤B x p q h-1 ∧
        0≤newEnds x p q h v m M before 1 ∧
        newEnds x p q h v m M before 1≤SU x p q h-1 := by
  let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
  have hL : 0<L x p q := by dsimp [L,Z,T]; positivity
  have hY : 0<Y x p q h := by dsimp [Y,T]; positivity
  have hQ : 0<Z x q+1 := by dsimp [Z]; positivity
  have hDp : 0<D := by have := mul_pos (by omega : 0<h) (by omega : 0<p); nlinarith
  have hDL : 2*D*L x p q=h*p*L x p q := by linear_combination L x p q*hD
  have hKB:=int_base_K_gt_B x p q h (by omega) hp hq hh
  have hb:=ceiling_M (K x p q h) (B x p q h) (L x p q) D hL hDp (by omega)
  have hlo : 0≤M := hb.1
  have hr0 : 0≤B x p q h-K x p q h+M*L x p q := hb.2.1
  have hr1 : B x p q h-K x p q h+M*L x p q<D*L x p q := hb.2.2.1
  have stock:=int_base_M_stock x p q h (by omega) hp hq hh
  have slack:=int_base_second_slack x p q h (by omega) hp hq hh
  have hMlt : 2*M<Y x p q h := by
    by_contra hn
    have ht:=mul_nonneg (show 0≤2*M-Y x p q h by omega) hL.le
    nlinarith only [stock,hr1,ht,hDL]
  have hMcap : 2*M≤Y x p q h-2 := by
    have heven : Y x p q h=2*(h*T x p q) := by dsimp [Y]; ring
    omega
  refine ⟨hlo,hMcap,?_⟩
  intro v m before
  change 0≤oldEnds x p q h v m M 1 ∧ oldEnds x p q h v m M 1≤B x p q h-1 ∧
    0≤newEnds x p q h v m M before 1 ∧ newEnds x p q h v m M before 1≤SU x p q h-1
  have hs0 : 0≤oldEnds x p q h v m M 1 := by dsimp [oldEnds]; nlinarith only [hr0]
  have hs1 : oldEnds x p q h v m M 1<2*D*L x p q := by dsimp [oldEnds]; nlinarith only [hr1]
  have hsB : oldEnds x p q h v m M 1<B x p q h := by
    have hYQ:=mul_pos hY hQ
    nlinarith only [hs1,slack,hDL,hYQ]
  have hYM : 0≤Y x p q h-M := by omega
  have hMq:=mul_nonneg hYM hQ.le
  have hT0 : 0≤newEnds x p q h v m M before 1 := by
    rw [second_charge]
    nlinarith only [hs0,hMq]
  have hprod:=mul_nonneg hlo hQ.le
  have hTlt : newEnds x p q h v m M before 1<2*B x p q h := by
    rw [second_charge]
    nlinarith only [hs1,slack,hDL,hprod]
  refine ⟨hs0,by omega,hT0,?_⟩
  have heven : newEnds x p q h v m M before 1=
      2*(SU x p q h-SW x p q h+M*SV x p q) := by
    change 2*SU x p q h-2*SW x p q h+2*M*SV x p q=
      2*(SU x p q h-SW x p q h+M*SV x p q)
    ring
  rw [heven] at hTlt ⊢
  dsimp only [SU] at hTlt ⊢
  omega

private theorem complete_row_bounds (x p q h v m M : ℤ) (before : Bool)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h)
    (hv0 : 1≤v) (hv : 2*v≤T x p q) (hM0 : 0≤M) (hM : 2*M≤Y x p q h-2)
    (hs : 0≤oldEnds x p q h v m M 0 ∧ oldEnds x p q h v m M 0≤A x p q h-1)
    (ht : 0≤newEnds x p q h v m M before 0 ∧ newEnds x p q h v m M before 0≤A x p q h-1)
    (hsecond : 0≤oldEnds x p q h v m M 1 ∧ oldEnds x p q h v m M 1≤B x p q h-1 ∧
      0≤newEnds x p q h v m M before 1 ∧ newEnds x p q h v m M before 1≤SU x p q h-1) :
    rowBounds x p q h v m M before := by
  refine ⟨?_,hv0,hv,hM0,hM⟩
  intro r
  fin_cases r
  · exact ⟨hs.1,hs.2,ht.1,ht.2⟩
  · exact hsecond
  · have h0:=int_base_S3_lower x p q h (by omega) hp hq hh
    have h1:=int_base_S3_upper x p q h (by omega) hp hq hh
    have h2:=int_base_T3_lower x p q h (by omega) hp hq hh
    have h3:=int_base_T3_upper x p q h (by omega) hp hq hh
    dsimp [oldEnds,newEnds,oldHeads,newHeads]
    exact ⟨by omega,by omega,by omega,by omega⟩

/-- Small p uses m=0; the ceiling M remains unchanged. -/
private theorem small_p_bounds (x p q h D : ℤ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h)
    (hsmall : 4*p≤x) (hD : 2*D=h*p) :
    let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
    rowBounds x p q h (p*q) 0 M true := by
  let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
  have hm:=generic_M_second x p q h D hx hp hq hh hD
  have hl:=int_first_small_R_lower x p q h hsmall hp hq hh
  have hu:=int_first_small_T1_upper x p q h hsmall hp hq hh
  have hQ : 0<Z x q+1 := by dsimp [Z]; positivity
  have hY : 0<Y x p q h := by dsimp [Y,T]; positivity
  have hS : 0≤oldEnds x p q h (p*q) 0 M 0 := by dsimp [oldEnds]; nlinarith only [hl]
  have hT:=first_charge x p q h (p*q) 0 M
  have hT0 : 0≤newEnds x p q h (p*q) 0 M true 0 := by
    rw [hT]
    have :=mul_nonneg hY.le hQ.le
    nlinarith only [hS,this]
  have hTcap : newEnds x p q h (p*q) 0 M true 0≤A x p q h-1 := by
    rw [hT]
    dsimp [oldEnds]
    nlinarith only [hu]
  have hScap : oldEnds x p q h (p*q) 0 M 0≤A x p q h-1 := by
    have :=mul_nonneg hY.le hQ.le
    rw [hT] at hTcap
    nlinarith only [hS,hTcap,this]
  have hv0 : 1≤p*q := by nlinarith
  have hv : 2*(p*q)≤T x p q := by
    have :=mul_nonneg (show 0≤x-2 by omega) (mul_nonneg (by omega : 0≤p) (by omega : 0≤q))
    dsimp [T]
    nlinarith only [this]
  exact complete_row_bounds x p q h (p*q) 0 M true hx hp hq hh hv0 hv hm.1 hm.2.1
    ⟨hS,hScap⟩ ⟨hT0,hTcap⟩ (hm.2.2 (p*q) 0 true)

/-- Both ordinary and odd-tail caps feed the same exact parity remainder. -/
private theorem remainder_bounds (x p q h D e : ℤ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h)
    (hD : 2*D=h*p) (he : x*e=2*p)
    (hcap : 2*parityJ (2*K x p q h-(2*p*q-e)*A x p q h) (C x p q h) e<p) :
    let j:=parityJ (2*K x p q h-(2*p*q-e)*A x p q h) (C x p q h) e
    let v:=p*q-(e+j)/2
    let m:=h*j
    let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
    0≤m ∧ m<D ∧ rowBounds x p q h v m M true := by
  let F:=2*K x p q h-(2*p*q-e)*A x p q h
  let j:=parityJ F (C x p q h) e
  let v:=p*q-(e+j)/2
  let m:=h*j
  let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
  have hC:=int_base_C_positive x p q h (by omega) hp hq hh
  have hFnum:=int_base_F2_positive x p q h (by omega) hp hq hh
  have hFeq : x*F=2*x*K x p q h-(2*p*q*x-2*p)*A x p q h := by
    dsimp [F]
    linear_combination A x p q h*he
  have hF : 0<F := by nlinarith only [hFnum,hFeq,hx]
  have hj:=parity_remainder F (C x p q h) e hF hC
  have hjp : 2*j<p := hcap
  have he0 : 0≤e := by nlinarith only [he,hx,hp]
  have hep : e≤p := by nlinarith only [he,hx,he0]
  have hhj:=mul_nonneg (show 0≤h by omega) (show 0≤j by exact hj.1.le)
  have hmc : m<D := by
    have :=mul_pos (show 0<h by omega) (show 0<p-2*j by omega)
    dsimp [m]
    nlinarith only [this,hD]
  have hv0 : 1≤v := by
    have hdiv : 2*((e+j)/2)=e+j := by have :=hj.2.2.2; omega
    have hpq:=mul_nonneg (show 0≤p by omega) (show 0≤q-2 by omega)
    dsimp [v]
    nlinarith only [hdiv,hep,hjp,hpq,hp]
  have hvpq : v≤p*q := by
    have hdiv : 0≤(e+j)/2 := by have :=hj.1; omega
    dsimp [v]; omega
  have hv : 2*v≤T x p q := by
    have hpq:=mul_nonneg (show 0≤p by omega) (show 0≤q by omega)
    have :=mul_nonneg (show 0≤x-2 by omega) hpq
    dsimp [T]
    nlinarith only [hvpq,this]
  have hm:=generic_M_second x p q h D hx hp hq hh hD
  have hR:=first_remainder_identity (A x p q h) (L x p q) (K x p q h) p q h e j hj.2.2.2
  have hSeq : oldEnds x p q h v m M 0=j*C x p q h-F := by
    calc
      oldEnds x p q h v m M 0=2*(v*A x p q h+m*L x p q-K x p q h) := by
        dsimp [oldEnds]; ring
      _=j*C x p q h-F := hR
  have hS0 : 0≤oldEnds x p q h v m M 0 := by
    rw [hSeq]
    exact hj.2.1
  have hSlt : oldEnds x p q h v m M 0<2*C x p q h := by
    rw [hSeq]
    exact hj.2.2.1
  have hY : 0<Y x p q h := by dsimp [Y,T]; positivity
  have hQ : 0<Z x q+1 := by dsimp [Z]; positivity
  have hDY : D<Y x p q h := by
    have hxx:=mul_pos (show 0<h*p by positivity) (show 0<4*x*q-1 by nlinarith)
    dsimp [Y,T]
    nlinarith only [hxx,hD]
  have hYm : 0<Y x p q h-m := by omega
  have hprod:=mul_nonneg hYm.le hQ.le
  have hfirst:=first_charge x p q h v m M
  have hlarge:=int_first_large x p q h hx hp hq hh
  have hT0 : 0≤newEnds x p q h v m M true 0 := by rw [hfirst]; nlinarith only [hS0,hprod]
  have hmQ:=mul_nonneg hhj hQ.le
  have hTcap : newEnds x p q h v m M true 0≤A x p q h-1 := by
    rw [hfirst]
    nlinarith only [hSlt,hlarge,hmQ]
  have hScap : oldEnds x p q h v m M 0≤A x p q h-1 := by
    rw [hfirst] at hTcap
    nlinarith only [hS0,hTcap,hprod]
  exact ⟨hhj,hmc,complete_row_bounds x p q h v m M true hx hp hq hh hv0 hv hm.1 hm.2.1
    ⟨hS0,hScap⟩ ⟨hT0,hTcap⟩ (hm.2.2 v m true)⟩

private def Tail (x p q : ℤ) : Prop :=
  (32≤x ∧ x≤2*p) ∨ (8≤x ∧ 4*x≤p) ∨
  (8≤x ∧ 2*x≤p ∧ 4≤q) ∨ (16≤x ∧ 2*x≤p) ∨
  (16≤x ∧ x≤p ∧ 4≤q) ∨ (16≤x ∧ x=2*p ∧ 8≤q)

private theorem pow_mono_int (m n : ℕ) (h : m≤n) : (2:ℤ)^m≤2^n :=
  pow_le_pow_right₀ (by norm_num) h

private theorem tail_cap (x p q h e : ℤ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h)
    (he : x*e=2*p) (hfour : 4∣p) (ht : Tail x p q) :
    2*parityJ (2*K x p q h-(2*p*q-e)*A x p q h) (C x p q h) e<p := by
  let F:=2*K x p q h-(2*p*q-e)*A x p q h
  have hC:=int_base_C_positive x p q h (by omega) hp hq hh
  have hN:=int_base_F2_positive x p q h (by omega) hp hq hh
  have hFeq : x*F=2*x*K x p q h-(2*p*q*x-2*p)*A x p q h := by
    dsimp [F]
    linear_combination A x p q h*he
  have hF : 0<F := by nlinarith only [hFeq,hN,hx]
  rcases ht with ht|ht|ht|ht|ht|ht
  all_goals try (
    apply parity_standard_cap F (C x p q h) e p hF hC
    have ht' : 0<x*(p-4)*C x p q h-
        2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
      first
        | exact int_tail_R32 x p q h ht.1 ht.2 hq hh
        | exact int_tail_R8 x p q h ht.1 ht.2 hq hh
        | exact int_tail_R8q4 x p q h ht.1 ht.2.1 ht.2.2 hh
        | exact int_tail_R16 x p q h ht.1 ht.2 hq hh
        | exact int_tail_R16q4 x p q h ht.1 ht.2.1 ht.2.2 hh
    nlinarith only [ht',hFeq,hx])
  have he1 : e=1 := by nlinarith only [he,ht.2.1,hx]
  change 2*parityJ F (C x p q h) e<p
  rw [he1]
  apply parity_odd_cap F (C x p q h) p hF hC hfour
  have ht':=int_tail_R16odd x p q h ht.1 ht.2.1.symm ht.2.2 hh
  obtain ⟨u,hu⟩:=hfour
  have hp2 : 2*(p/2)=p := by omega
  have heq : x*(p-2)*C x p q h-
      2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)=
      2*x*((p/2-1)*C x p q h-F) := by
    linear_combination 2*hFeq-x*(C x p q h)*hp2
  have hpos : 0<2*x*((p/2-1)*C x p q h-F) := by rw [←heq]; exact ht'
  exact lt_of_sub_pos ((mul_pos_iff_of_pos_left (by omega : (0:ℤ)<2*x)).mp hpos)

/-- The power exponents are unrestricted; the output is an actual native mask triple. -/
private theorem generic_selection (a P Q H : ℕ) (ha : 3≤a) (hP : 2≤P) (hQ : 1≤Q)
    (hroute : 4*(2:ℤ)^P≤2^a ∨ (a≤P+1 ∧ Tail (2^a) (2^P) (2^Q))) :
    ∃ v m M : ℕ, Submask m M ∧
      rowBounds (2^a) (2^P) (2^Q) (2^H) v m M true := by
  let x : ℤ:=2^a
  let p : ℤ:=2^P
  let q : ℤ:=2^Q
  let h : ℤ:=2^H
  let D : ℤ:=2^(H+P-1)
  let M:=chooseM (K x p q h) (B x p q h) (L x p q) D
  have hx : 8≤x := by have :=pow_mono_int 3 a ha; norm_num at this; exact this
  have hp : 4≤p := by have :=pow_mono_int 2 P hP; norm_num at this; exact this
  have hq : 2≤q := by have :=pow_mono_int 1 Q hQ; norm_num at this; exact this
  have hh : 1≤h := by dsimp [h]; exact_mod_cast (Nat.one_le_two_pow (n:=H))
  have hD : 2*D=h*p := by
    dsimp [D,h,p]
    calc
      2*(2:ℤ)^(H+P-1)=(2:ℤ)^((H+P-1)+1) := by rw [pow_succ]; ring
      _=(2:ℤ)^H*2^P := by rw [←pow_add]; congr 1; omega
  have hL : 0<L x p q := by dsimp [L,Z,T]; positivity
  have hKB:=int_base_K_gt_B x p q h (by omega) hp hq hh
  have hm:=generic_M_second x p q h D hx hp hq hh hD
  have hM0 : 0≤M := hm.1
  have hMN : (M.toNat:ℤ)=M := Int.toNat_of_nonneg hM0
  rcases hroute with hsmall|⟨hexp,htail⟩
  · have hb:=small_p_bounds x p q h D hx hp hq hh hsmall hD
    have hv0 : 0≤p*q := by positivity
    have hvN : ((p*q).toNat:ℤ)=p*q := Int.toNat_of_nonneg hv0
    have hz : (0:ℕ)<2^(H+P-1) := Nat.two_pow_pos _
    have hs:=ceiling_M_bits (K x p q h) (B x p q h) (L x p q) (H+P-1) hL (by omega) 0 hz
    refine ⟨(p*q).toNat,0,M.toNat,hs,?_⟩
    simpa only [hvN,hMN,Nat.cast_zero] using hb
  · let e : ℤ:=2^(P+1-a)
    have he : x*e=2*p := by
      dsimp [x,e,p]
      rw [←pow_add,show a+(P+1-a)=P+1 by omega,pow_succ]
      ring
    have hfour : 4∣p := by
      refine ⟨2^(P-2),?_⟩
      dsimp [p]
      calc
        (2:ℤ)^P=2^((P-2)+2) := by congr 1; omega
        _=4*2^(P-2) := by rw [pow_add]; ring
    have hcap:=tail_cap x p q h e hx hp hq hh he hfour htail
    let j:=parityJ (2*K x p q h-(2*p*q-e)*A x p q h) (C x p q h) e
    let v:=p*q-(e+j)/2
    let m:=h*j
    have hb:=remainder_bounds x p q h D e hx hp hq hh hD he hcap
    have hm0 : 0≤m := hb.1
    have hmD : m<D := hb.2.1
    have hb' : rowBounds x p q h v m M true := hb.2.2
    have hv0 : 0≤v := by have hv:=hb'.2.1; omega
    have hvN : (v.toNat:ℤ)=v := Int.toNat_of_nonneg hv0
    have hmN : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm0
    have hmDN : m.toNat<2^(H+P-1) := by exact_mod_cast (show (m.toNat:ℤ)<2^(H+P-1) by simpa only [hmN] using hmD)
    have hs:=ceiling_M_bits (K x p q h) (B x p q h) (L x p q) (H+P-1) hL (by omega) m.toNat hmDN
    refine ⟨v.toNat,m.toNat,M.toNat,hs,?_⟩
    simpa only [hvN,hmN,hMN] using hb'

/-- Exact power splitting; no upper bound on H enters any later argument. -/
private theorem h_split (H : ℕ) (hH : 2≤H) :
    (2:ℤ)^H=4*2^(H-2) := by
  calc
    (2:ℤ)^H = 2^((H-2)+2) := by congr 1; omega
    _ = 4*2^(H-2) := by rw [pow_add]; ring

private theorem scaled_residue_selection (p q k : ℕ)
    (hp : p=4 ∨ p=8) (hq : ∃ s : ℕ, q=8*2^s) :
    ∃ v m M : ℕ, Submask m M ∧ m<M ∧
      rowBounds 8 p q (4*(2:ℤ)^k) v m M true := by
  obtain ⟨s,rfl⟩:=hq
  obtain ⟨R,r,hr,hrr⟩:=residue_decomposition s
  have pick : ∃ i : Fin 12,
      (residueFamilies i).p=p ∧ (residueFamilies i).r=r := by
    rcases hp with rfl|rfl <;> rcases hrr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨0,by norm_num [residueFamilies]⟩
    · exact ⟨1,by norm_num [residueFamilies]⟩
    · exact ⟨2,by norm_num [residueFamilies]⟩
    · exact ⟨3,by norm_num [residueFamilies]⟩
    · exact ⟨4,by norm_num [residueFamilies]⟩
    · exact ⟨5,by norm_num [residueFamilies]⟩
    · exact ⟨6,by norm_num [residueFamilies]⟩
    · exact ⟨7,by norm_num [residueFamilies]⟩
    · exact ⟨8,by norm_num [residueFamilies]⟩
    · exact ⟨9,by norm_num [residueFamilies]⟩
    · exact ⟨10,by norm_num [residueFamilies]⟩
    · exact ⟨11,by norm_num [residueFamilies]⟩
  obtain ⟨i,hpi,hri⟩:=pick
  let f:=residueFamilies i
  have hfp : f.p=p := hpi
  have hfr : f.r=r := hri
  have hqeq : 8*2^s=72*R+f.r := by simpa only [hfr] using hr
  have hprod : 1≤f.p*(72*R+f.r) := by
    rw [hfp,←hqeq]
    rcases hp with rfl|rfl <;> have := Nat.two_pow_pos s <;> omega
  let u : ℕ:=2^k
  have hu : (1:ℤ)≤u := by dsimp [u]; exact_mod_cast (Nat.one_le_two_pow (n:=k))
  have hb:=residue_bounds i (R:ℤ) ((u:ℤ)-1) (by positivity) (by omega)
  change rowBounds 8 f.p (72*(R:ℤ)+f.r) (4*(1+((u:ℤ)-1)))
      ((f.p:ℤ)*(72*(R:ℤ)+f.r)-1) ((1+((u:ℤ)-1))*f.m0)
      ((1+((u:ℤ)-1))*(512*f.p*(R:ℤ)+f.C)) true ∧
      (1+((u:ℤ)-1))*f.m0 < (1+((u:ℤ)-1))*(512*f.p*(R:ℤ)+f.C) at hb
  rw [show 1+((u:ℤ)-1)=(u:ℤ) by ring] at hb
  have hv : ((f.p*(72*R+f.r)-1:ℕ):ℤ)=
      (f.p:ℤ)*(72*(R:ℤ)+f.r)-1 := by
    simp only [Nat.cast_sub hprod,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hbN : rowBounds 8 f.p (72*R+f.r:ℕ) (4*(2:ℤ)^k)
      (f.p*(72*R+f.r)-1:ℕ) (2^k*f.m0:ℕ)
      (2^k*(512*f.p*R+f.C):ℕ) true := by
    simpa only [hv,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,u] using hb.1
  have hproper : (2^k*f.m0:ℕ)<2^k*(512*f.p*R+f.C) := by
    have hh := hb.2
    dsimp [u] at hh
    exact_mod_cast hh
  refine ⟨f.p*(72*R+f.r)-1,2^k*f.m0,2^k*(512*f.p*R+f.C),
    residue_masks i R k,hproper,?_⟩
  simpa only [hfp,←hqeq] using hbN

private theorem scaled_fixed_selection (i : Fin 8) (k : ℕ) :
    let f:=fixedFamilies i
    ∃ v m M : ℕ, Submask m M ∧ m<M ∧
      rowBounds f.x f.p f.q (4*(2:ℤ)^k) v m M true := by
  let f:=fixedFamilies i
  let u : ℕ:=2^k
  have hu : (1:ℤ)≤u := by dsimp [u]; exact_mod_cast (Nat.one_le_two_pow (n:=k))
  have hb:=fixed_bounds i ((u:ℤ)-1) (by omega)
  change rowBounds f.x f.p f.q (4*(1+((u:ℤ)-1))) f.v
      ((1+((u:ℤ)-1))*f.m0) ((1+((u:ℤ)-1))*f.M0) true ∧
      (1+((u:ℤ)-1))*f.m0 < (1+((u:ℤ)-1))*f.M0 at hb
  rw [show 1+((u:ℤ)-1)=(u:ℤ) by ring] at hb
  refine ⟨f.v,2^k*f.m0,2^k*f.M0,fixed_masks i k,?_,?_⟩
  · have hh:=hb.2
    dsimp [u] at hh
    exact_mod_cast hh
  · simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,u] using hb.1

/-- Finite parameter selection uses only equalities with literal table entries. -/
private theorem fixed_dyadic_selection (a P Q H : ℕ) (i : Fin 8)
    (hH : 2≤H)
    (he : (fixedFamilies i).x=2^a ∧ (fixedFamilies i).p=2^P ∧
      (fixedFamilies i).q=2^Q) :
    ∃ v m M : ℕ, ∃ before : Bool, before=true ∧ Submask m M ∧
      rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
  obtain ⟨v,m,M,hs,_,hb⟩:=scaled_fixed_selection i (H-2)
  refine ⟨v,m,M,true,rfl,hs,?_⟩
  rw [he.1,he.2.1,he.2.2] at hb
  simpa only [Nat.cast_pow,Nat.cast_ofNat,←h_split H hH] using hb

/-- Closed selector on the genuine unbounded small-a region.
The proof's finite splits are only P=2,3,4 and Q=1,2; all larger exponents
use the original universal generic tails or the universal mod-72 families. -/
theorem small_a_selection (a P Q H : ℕ) (ha : a=3 ∨ a=4)
    (hP : 2≤P) (hQ : 1≤Q) (hH : 2≤H) :
    ∃ v m M : ℕ, ∃ before : Bool, before=true ∧ Submask m M ∧
      rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
  have ha3 : 3≤a := by omega
  have generic (hr : 4*(2:ℤ)^P≤2^a ∨
      (a≤P+1 ∧ Tail (2^a) (2^P) (2^Q))) :
      ∃ v m M : ℕ, ∃ before : Bool, before=true ∧ Submask m M ∧
        rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
    obtain ⟨v,m,M,hs,hb⟩:=generic_selection a P Q H ha3 hP hQ hr
    exact ⟨v,m,M,true,rfl,hs,hb⟩
  have residue (ha8 : a=3) (hp : (2^P:ℕ)=4 ∨ (2^P:ℕ)=8) (hq : 3≤Q) :
      ∃ v m M : ℕ, ∃ before : Bool, before=true ∧ Submask m M ∧
        rowBounds (2^a) (2^P) (2^Q) (2^H) v m M before := by
    have hqr : ∃ s : ℕ, 2^Q=8*2^s := by
      refine ⟨Q-3,?_⟩
      calc
        (2:ℕ)^Q=2^((Q-3)+3) := by congr 1; omega
        _=8*2^(Q-3) := by rw [pow_add]; ring
    obtain ⟨v,m,M,hs,_,hb⟩:=scaled_residue_selection (2^P) (2^Q) (H-2) hp hqr
    refine ⟨v,m,M,true,rfl,hs,?_⟩
    simpa only [ha8,h_split H hH,Nat.cast_pow,Nat.cast_ofNat,
      show (2:ℤ)^3=8 by norm_num] using hb
  have q4 (hq : 2≤Q) : (4:ℤ)≤2^Q := by
    have hh:=pow_mono_int 2 Q hq
    norm_num at hh
    exact hh
  have q8 (hq : 3≤Q) : (8:ℤ)≤2^Q := by
    have hh:=pow_mono_int 3 Q hq
    norm_num at hh
    exact hh
  rcases ha with rfl|rfl
  · by_cases hP5 : 5≤P
    · apply generic
      right
      refine ⟨by omega,Or.inr (Or.inl ⟨by norm_num,?_⟩)⟩
      have hp:=pow_mono_int 5 P hP5
      norm_num at hp ⊢
      exact hp
    have hpCases : P=2 ∨ P=3 ∨ P=4 := by omega
    rcases hpCases with rfl|rfl|rfl
    · by_cases hq3 : 3≤Q
      · exact residue rfl (by norm_num) hq3
      have hqc : Q=1 ∨ Q=2 := by omega
      rcases hqc with rfl|rfl
      · exact fixed_dyadic_selection 3 2 1 H 0 hH (by norm_num [fixedFamilies])
      · exact fixed_dyadic_selection 3 2 2 H 1 hH (by norm_num [fixedFamilies])
    · by_cases hq3 : 3≤Q
      · exact residue rfl (by norm_num) hq3
      have hqc : Q=1 ∨ Q=2 := by omega
      rcases hqc with rfl|rfl
      · exact fixed_dyadic_selection 3 3 1 H 2 hH (by norm_num [fixedFamilies])
      · exact fixed_dyadic_selection 3 3 2 H 3 hH (by norm_num [fixedFamilies])
    · by_cases hq2 : 2≤Q
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inl ?_))⟩
        exact ⟨by norm_num,by norm_num,q4 hq2⟩
      have hq1 : Q=1 := by omega
      subst Q
      exact fixed_dyadic_selection 3 4 1 H 4 hH (by norm_num [fixedFamilies])
  · by_cases hP2 : P=2
    · subst P
      apply generic
      left
      norm_num
    by_cases hP5 : 5≤P
    · apply generic
      right
      refine ⟨by omega,Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num,?_⟩)))⟩
      have hp:=pow_mono_int 5 P hP5
      norm_num at hp ⊢
      exact hp
    have hpCases : P=3 ∨ P=4 := by omega
    rcases hpCases with rfl|rfl
    · by_cases hq3 : 3≤Q
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
        exact ⟨by norm_num,by norm_num,q8 hq3⟩
      have hqc : Q=1 ∨ Q=2 := by omega
      rcases hqc with rfl|rfl
      · exact fixed_dyadic_selection 4 3 1 H 5 hH (by norm_num [fixedFamilies])
      · exact fixed_dyadic_selection 4 3 2 H 6 hH (by norm_num [fixedFamilies])
    · by_cases hq2 : 2≤Q
      · apply generic
        right
        refine ⟨by omega,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
        exact ⟨by norm_num,by norm_num,q4 hq2⟩
      have hq1 : Q=1 := by omega
      subst Q
      exact fixed_dyadic_selection 4 4 1 H 7 hH (by norm_num [fixedFamilies])

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
