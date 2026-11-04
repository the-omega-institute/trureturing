/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/BorrowArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-unbounded-windows)
   mirror-E: none(waiver:private-consumed-unbounded-windows)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded borrow selectors, literal bit containment and residual windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
namespace StrictDictionary

open private pA pB pD pL pK pH window adjacent_W_windows
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Arithmetic
open private x y z A B D L K H SU SV SW vNat wBit quotientT
  hybridOld hybridNew vEndpoint vNewEndpoint
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source

private theorem borrow_far_slacks (x y p : ℤ) (hy : 4 ≤ y)
    (hx : 2*y ≤ x) (hp : 2 ≤ p) :
    0 < 2*pL x (2*x*p)-4*(p+1)*pB x y (2*x*p)-(y-4)*pD x y (2*x*p) ∧
    0 < pK y (2*x*p)-pA x y (2*x*p)-p*pB x y (2*x*p) ∧
    0 < (2*p+1)*pA x y (2*x*p)-pK y (2*x*p) := by
  let alpha := x-2*y
  let beta := y-4
  let gamma := p-2
  have ha : 0 ≤ alpha := by dsimp [alpha];omega
  have hb : 0 ≤ beta := by dsimp [beta];omega
  have hc : 0 ≤ gamma := by dsimp [gamma];omega
  have hVId : 2*pL x (2*x*p)-4*(p+1)*pB x y (2*x*p)-(y-4)*pD x y (2*x*p) = 8*alpha^3*gamma^2 + 32*alpha^3*gamma + 32*alpha^3 + 40*alpha^2*beta*gamma^2 + 150*alpha^2*beta*gamma + 140*alpha^2*beta + 160*alpha^2*gamma^2 + 600*alpha^2*gamma + 560*alpha^2 + 64*alpha*beta^2*gamma^2 + 216*alpha*beta^2*gamma + 177*alpha*beta^2 + 512*alpha*beta*gamma^2 + 1726*alpha*beta*gamma + 1409*alpha*beta + 1016*alpha*gamma^2 + 3420*alpha*gamma + 2776*alpha + 32*beta^3*gamma^2 + 88*beta^3*gamma + 50*beta^3 + 384*beta^2*gamma^2 + 1052*beta^2*gamma + 586*beta^2 + 1520*beta*gamma^2 + 4136*beta*gamma + 2232*beta + 1984*gamma^2 + 5340*gamma + 2742 := by
    dsimp [pL,pB,pD,pA,pK,alpha,beta,gamma];ring
  have hV : 0 < 2*pL x (2*x*p)-4*(p+1)*pB x y (2*x*p)-(y-4)*pD x y (2*x*p) := by rw [hVId];positivity
  have hWId : pK y (2*x*p)-pA x y (2*x*p)-p*pB x y (2*x*p) = 2*alpha^2*beta*gamma^2 + 6*alpha^2*beta*gamma + 4*alpha^2*beta + 6*alpha^2*gamma^2 + 16*alpha^2*gamma + 8*alpha^2 + 8*alpha*beta^2*gamma^2 + 24*alpha*beta^2*gamma + 16*alpha*beta^2 + 56*alpha*beta*gamma^2 + 162*alpha*beta*gamma + 99*alpha*beta + 94*alpha*gamma^2 + 256*alpha*gamma + 131*alpha + 8*beta^3*gamma^2 + 24*beta^3*gamma + 16*beta^3 + 88*beta^2*gamma^2 + 260*beta^2*gamma + 166*beta^2 + 316*beta*gamma^2 + 912*beta*gamma + 543*beta + 368*gamma^2 + 1023*gamma + 538 := by
    dsimp [pL,pB,pD,pA,pK,alpha,beta,gamma];ring
  have hW : 0 < pK y (2*x*p)-pA x y (2*x*p)-p*pB x y (2*x*p) := by rw [hWId];positivity
  have hJId : (2*p+1)*pA x y (2*x*p)-pK y (2*x*p) = 2*alpha^2*beta*gamma + 4*alpha^2*beta + 8*alpha^2*gamma + 16*alpha^2 + 8*alpha*beta^2*gamma + 16*alpha*beta^2 + 64*alpha*beta*gamma + 129*alpha*beta + 130*alpha*gamma + 265*alpha + 8*beta^3*gamma + 16*beta^3 + 96*beta^2*gamma + 194*beta^2 + 388*beta*gamma + 793*beta + 530*gamma + 1096 := by
    dsimp [pL,pB,pD,pA,pK,alpha,beta,gamma];ring
  have hJ : 0 < (2*p+1)*pA x y (2*x*p)-pK y (2*x*p) := by rw [hJId];positivity
  exact ⟨hV,hW,hJ⟩

private theorem borrow_far_W_windows (x y p F chi : ℤ)
    (hy : 4 ≤ y) (hx : 2*y ≤ x) (hp : 2 ≤ p)
    (hFlo : p*pA x y (2*x*p) ≤ F) (hFhi : F ≤ p*pB x y (2*x*p))
    (hchi0 : 0 ≤ chi) (hchip : chi ≤ p) :
    let z := 2*x*p
    let G := pK y z-pA x y z-F
    let Gp := 2*G-pH y z+chi
    window G (pK y z) ∧ window (Gp+pA x y z) (2*pK y z-pH y z) ∧
    (0 ≤ Gp → window Gp (2*pK y z-pH y z)) := by
  dsimp only
  let z := 2*x*p
  let G := pK y z-pA x y z-F
  let Gp := 2*G-pH y z+chi
  change window G (pK y z) ∧ window (Gp+pA x y z) (2*pK y z-pH y z) ∧
    (0 ≤ Gp → window Gp (2*pK y z-pH y z))
  have hs := borrow_far_slacks x y p hy hx hp
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hz0 : 0 < z := by dsimp [z];positivity
  have hG : 0 < G := by dsimp [G,z];linarith [hs.2.1]
  have hJ : 0 < 2*F-(pK y z-pA x y z) := by
    dsimp [z]
    nlinarith only [hFlo,hs.2.2]
  have hA : 0 < pA x y z := by dsimp [pA];positivity
  have hGold : window G (pK y z) := by dsimp [window,G];constructor <;> omega
  have hAH : pH y z < pA x y z := by
    have hid : pA x y z-pH y z=(x-1)*pH y z+1 := by dsimp [pA,pH];ring
    have hH : 0 < pH y z := by dsimp [pH];positivity
    have hxm : 0 < x-1 := by omega
    have hm : 0 < (x-1)*pH y z := mul_pos hxm hH
    omega
  have hHchi : 2*chi ≤ pH y z-1 := by
    have hzId : y*z=2*p*(x*y) := by dsimp [z];ring
    have hxy : 1 ≤ x*y := by have hh : 0<x*y := mul_pos hx0 hy0;omega
    have hm := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 2*p by omega)
    dsimp [pH]
    nlinarith only [hzId,hm,hchip,hy]
  have hnewId : 2*pK y z-pH y z-1-2*(Gp+pA x y z)=
      2*(2*F-(pK y z-pA x y z))+pH y z-1-2*chi := by
    dsimp [Gp,G];ring
  have hnew : window (Gp+pA x y z) (2*pK y z-pH y z) := by
    dsimp [window]
    constructor
    · dsimp [Gp];omega
    · omega
  refine ⟨hGold,hnew,?_⟩
  intro hgp
  have hA : 0 < pA x y z := by dsimp [pA];positivity
  exact ⟨by omega,by have hh := hnew.2;omega⟩

private theorem borrowed_bit (q e : ℕ) (hq : 2*2^e ≤ q) :
    (if q.testBit e then q else q-2^e).testBit e = true := by
  by_cases he : q.testBit e = true
  · simp [he]
  · have he0 : q.testBit e = false := by cases h : q.testBit e <;> simp_all
    simp only [he0,Bool.false_eq_true,if_false]
    let p := 2^e
    let d := q/p
    let r := q%p
    have hp : 0 < p := by dsimp [p];positivity
    have hr : r < p := Nat.mod_lt _ hp
    have hqr : r+p*d=q := Nat.mod_add_div q p
    have hd : 1 ≤ d := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      dsimp [p]
      omega
    have hdmod : d%2=0 := by
      have hh := he0
      rw [Nat.testBit_eq_decide_div_mod_eq] at hh
      have hm := Nat.mod_lt d (by omega : 0<2)
      dsimp [d,p] at *
      simp only [decide_eq_false_iff_not] at hh
      omega
    have hmul : p*d=(d-1)*p+p := by
      calc
        p*d = d*p := Nat.mul_comm _ _
        _ = (d-1+1)*p := by rw [Nat.sub_add_cancel hd]
        _ = (d-1)*p+p := by rw [Nat.add_mul, Nat.one_mul]
    have hsub : q-p=r+(d-1)*p := by omega
    have hdiv : (q-p)/p=d-1 := by
      rw [hsub,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hr]
      omega
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change decide ((q-p)/p%2=1)=true
    rw [hdiv]
    simp only [decide_eq_true_eq]
    omega

private theorem singleton_bit_submask (q e : ℕ) (hq : 2*2^e ≤ q) :
    ∀ i : ℕ, (2^e).testBit i=true →
      (if q.testBit e then q else q-2^e).testBit i=true := by
  intro i hi
  by_cases he : e=i
  · subst i;exact borrowed_bit q e hq
  · simp [Nat.testBit_two_pow_of_ne he] at hi

private theorem borrow_basic (x y z : ℤ) (hy : 4 ≤ y) (hx : 2*y ≤ x) (hz : 2*x ≤ z) :
    0 < pA x y z ∧ 0 < pB x y z ∧ 1 ≤ pD x y z ∧
    z+1 < pA x y z ∧ z+1 ≤ pL x z-pA x y z ∧
    2*pA x y z ≤ 2*pL x z-z-2 ∧ pL x z < x*y*z^2-1 := by
  have hx0 : 0 < x := by omega
  have hy8 : 4 ≤ y := by omega
  have hz8 : 8 ≤ z := by omega
  have hy0 : 0 < y := by omega
  have hz0 : 0 < z := by omega
  have hD : pD x y z=(z-x)+x*(z-y) := by dsimp [pD,pA,pB];ring
  have hDn : 1 ≤ pD x y z := by
    rw [hD]
    have hp := mul_nonneg hx0.le (show 0 ≤ z-y by omega)
    omega
  have hA : 0 < pA x y z := by dsimp [pA];positivity
  have hB : 0 < pB x y z := by dsimp [pB];positivity
  have hxy := mul_le_mul_of_nonneg_left (show 4 ≤ y by omega) hx0.le
  have haId : pA x y z-(z+1)=x+x*y+(x*y-1)*z := by dsimp [pA];ring
  have hAz : z+1 < pA x y z := by
    have hc : 0 ≤ x*y-1 := by nlinarith only [hxy,hx0]
    have hp : 0 ≤ (x*y-1)*z := mul_nonneg hc hz0.le
    have hxy0 : 0 < x*y := mul_pos hx0 hy0
    nlinarith only [haId,hp,hxy0,hx0]
  have hgap : pL x z-pA x y z=(z+1)*pD x y z := by
    dsimp [pL,pA,pD,pB];ring
  have hLA : z+1 ≤ pL x z-pA x y z := by
    have hm := mul_le_mul_of_nonneg_left hDn (show 0 ≤ z+1 by omega)
    rw [hgap]
    simpa only [mul_one] using hm
  have hc : 0 ≤ x*y-x-3 := by nlinarith only [hxy,hx0]
  have hp : 0 ≤ (x*y-x-3)*z^2 := mul_nonneg hc (sq_nonneg z)
  have hnId : x*y*z^2-1-pL x z=(x*y-x-3)*z^2+2*z^2-z-2 := by
    dsimp [pL];ring
  have hN : pL x z < x*y*z^2-1 := by
    nlinarith only [hp,hnId,sq_nonneg (z-1),hz8]
  exact ⟨hA,hB,hDn,hAz,hLA,by omega,hN⟩

private theorem borrow_far_V_windows (x y p v t : ℤ)
    (hy : 4 ≤ y) (hx : 2*y ≤ x) (hp : 2 ≤ p) (hv : 4*v=y)
    (htlo : (pL x (2*x*p)-pA x y (2*x*p))/pB x y (2*x*p)-p ≤ t)
    (hthi : t ≤ (pL x (2*x*p)-pA x y (2*x*p))/pB x y (2*x*p)) :
    let z := 2*x*p
    let q := (pL x z-pA x y z)/pB x y z
    let n := t%v
    let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
    let Rp := 2*R-z-1+t-n
    2*p+1 ≤ q ∧ 0 ≤ t ∧ 2*t<z ∧ window R (pL x z) ∧
      window (if Rp<0 then Rp+pA x y z else Rp) (2*pL x z-z-1) := by
  dsimp only
  let z := 2*x*p
  let q := (pL x z-pA x y z)/pB x y z
  let n := t%v
  let r := (pL x z-pA x y z)%pB x y z
  let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
  let Rp := 2*R-z-1+t-n
  change 2*p+1 ≤ q ∧ 0 ≤ t ∧ 2*t<z ∧ window R (pL x z) ∧
    window (if Rp<0 then Rp+pA x y z else Rp) (2*pL x z-z-1)
  change q-p ≤ t at htlo
  change t ≤ q at hthi
  have hx0 : 0 < x := by omega
  have hz : 2*x ≤ z := by dsimp [z];nlinarith only [hp,hx0]
  have hb := borrow_basic x y z hy hx hz
  have hA : 0 < pA x y z := hb.1
  have hB : 0 < pB x y z := hb.2.1
  have hD : 1 ≤ pD x y z := hb.2.2.1
  have hAz : z+1 < pA x y z := hb.2.2.2.1
  have hAs : 2*pA x y z ≤ 2*pL x z-z-2 := hb.2.2.2.2.2.1
  have hN : pL x z < x*y*z^2-1 := hb.2.2.2.2.2.2
  have hAB : pA x y z < pB x y z := by dsimp [pD] at hD;omega
  have hs := (borrow_far_slacks x y p hy hx hp).1
  change 0 < 2*pL x z-4*(p+1)*pB x y z-(y-4)*pD x y z at hs
  have hdprod : 0 ≤ (y-4)*pD x y z := mul_nonneg (by omega) (by omega)
  have hqlo : 2*p+1 ≤ q := by
    apply (Int.le_ediv_iff_mul_le hB).mpr
    nlinarith only [hs,hdprod,hAB]
  have ht0 : 0 ≤ t := by omega
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hB)
  have hrB : r < pB x y z := Int.emod_lt_of_pos _ hB
  have hdiv : r+pB x y z*q=pL x z-pA x y z := Int.emod_add_mul_ediv _ _
  have hn0 : 0 ≤ n := Int.emod_nonneg _ (by omega)
  have hnv : n < v := Int.emod_lt_of_pos _ (by omega)
  have hnle : n ≤ t := by
    have he := Int.emod_add_mul_ediv t v
    have hm := mul_nonneg (show 0 ≤ v by omega) (Int.ediv_nonneg ht0 (show 0 ≤ v by omega))
    dsimp [n];omega
  have hrec : z*pB x y z=x*y*z^2-1+pL x z := by dsimp [pB,pL];ring
  have hqcap : 2*q < z := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_right (show z ≤ 2*q by omega) hB.le
    nlinarith only [hm,hdiv,hr0,hrec,hN,hA]
  have hR : R=r+(q-t)*pB x y z+n*pD x y z := by dsimp [R];nlinarith only [hdiv]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact add_nonneg (add_nonneg hr0 (mul_nonneg (by omega) hB.le))
      (mul_nonneg hn0 (by omega))
  have hRhi : R < (p+1)*pB x y z+(v-1)*pD x y z := by
    have hm := mul_le_mul_of_nonneg_right (show q-t ≤ p by omega) hB.le
    have hm' := mul_le_mul_of_nonneg_right (show n ≤ v-1 by omega) (show 0 ≤ pD x y z by omega)
    rw [hR]
    nlinarith only [hm,hm',hrB]
  have hRw : window R (pL x z) := by
    constructor
    · omega
    · have hvD := congrArg (fun r : ℤ => r*pD x y z) hv
      nlinarith only [hRhi,hs,hvD]
  have hnew : window (if Rp<0 then Rp+pA x y z else Rp) (2*pL x z-z-1) := by
    dsimp [window]
    by_cases he : Rp<0
    · rw [if_pos he]
      have hlo : -z-1 ≤ Rp := by dsimp [Rp];omega
      constructor <;> omega
    · rw [if_neg he]
      have hu := hRw.2
      constructor
      · omega
      · dsimp [Rp];omega
  exact ⟨hqlo,ht0,by omega,hRw,hnew⟩

private theorem borrow_adjacent_V_windows (x y v : ℤ)
    (hy : 4 ≤ y) (hx : 2*y ≤ x) (hv : 4*v=y)
    (hdyadic : x=2*y ∨ 4*y ≤ x) :
    let z := 2*x
    let q := (pL x z-pA x y z)/pB x y z
    let t := if x=2*y then 2 else q-1
    let n := t%v
    let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
    let Rp := 2*R-z-1+t-n
    1 ≤ q ∧ 0 ≤ t ∧ 2*t<z ∧ window R (pL x z) ∧ window Rp (2*pL x z-z-1) := by
  dsimp only
  let z := 2*x
  let q := (pL x z-pA x y z)/pB x y z
  let t := if x=2*y then 2 else q-1
  let n := t%v
  let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
  let Rp := 2*R-z-1+t-n
  change 1 ≤ q ∧ 0 ≤ t ∧ 2*t<z ∧ window R (pL x z) ∧
    window Rp (2*pL x z-z-1)
  have hb := borrow_basic x y z hy hx (by dsimp [z];omega)
  have hA : 0 < pA x y z := hb.1
  have hB : 0 < pB x y z := hb.2.1
  have hD : 1 ≤ pD x y z := hb.2.2.1
  have hN : pL x z < x*y*z^2-1 := hb.2.2.2.2.2.2
  have hAB : pA x y z < pB x y z := by dsimp [pD] at hD;omega
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hv0 : 0 < v := by omega
  have hfirstId : 2*(pB x y z-1)-y*pD x y z=
      ((x-1)*y+2*x+2)*z+x*y*(y+1) := by dsimp [pA,pB,pD];ring
  have hfirst : 2*v*pD x y z < pB x y z-1 := by
    have hidpos : 0 < 2*(pB x y z-1)-y*pD x y z := by
      rw [hfirstId]
      have hxm : 0 < x-1 := by omega
      have hz0 : 0 < z := by dsimp [z];omega
      positivity
    have hvD := congrArg (fun r : ℤ => r*pD x y z) hv
    nlinarith only [hidpos,hvD]
  let r := (pL x z-pA x y z)%pB x y z
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hB)
  have hrB : r < pB x y z := Int.emod_lt_of_pos _ hB
  have hdiv : r+pB x y z*q=pL x z-pA x y z := Int.emod_add_mul_ediv _ _
  have hrec : z*pB x y z=x*y*z^2-1+pL x z := by dsimp [pB,pL];ring
  have hqcap : 2*q < z := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_right (show z ≤ 2*q by omega) hB.le
    nlinarith only [hm,hdiv,hr0,hrec,hN,hA]
  have hdata : 1 ≤ q ∧ 0 ≤ t ∧ 2*t<z ∧ window R (pL x z) ∧ 0 ≤ Rp := by
    rcases hdyadic with hxy | hxy
    · have ht2 : t=2 := by simp [t,hxy]
      let beta := y-4
      have hbeta : 0 ≤ beta := by dsimp [beta];omega
      have hcoreId : pL x z-pA x y z-2*pB x y z = 8*beta^3 + 94*beta^2 + 362*beta + 454 := by
        dsimp [pL,pA,pB,z,beta];rw [hxy];ring
      have hcore : 0 < pL x z-pA x y z-2*pB x y z := by rw [hcoreId];positivity
      have hL3Id : pL x z-3*pB x y z = 8*beta^3 + 88*beta^2 + 312*beta + 350 := by
        dsimp [pL,pA,pB,z,beta];rw [hxy];ring
      have hL3 : 0 < pL x z-3*pB x y z := by rw [hL3Id];positivity
      have hnewlowId : 2*(pL x z-pA x y z-2*pB x y z)-z-1 = 16*beta^3 + 188*beta^2 + 720*beta + 891 := by
        dsimp [pL,pA,pB,z,beta];rw [hxy];ring
      have hnewlow : 0 < 2*(pL x z-pA x y z-2*pB x y z)-z-1 := by rw [hnewlowId];positivity
      have hsmall : pL x z-pA x y z < 3*pB x y z := by
        have hid : pL x z-pA x y z-3*pB x y z= -10*y^2-10*y-3 := by
          dsimp [pL,pA,pB,z];rw [hxy];ring
        nlinarith only [hid,sq_nonneg y,hy]
      have hq2 : q=2 := by
        apply (Int.ediv_eq_iff_of_pos hB).mpr
        constructor <;> omega
      have hn0 : 0 ≤ n := Int.emod_nonneg _ (by omega)
      have hnhi : n < v := Int.emod_lt_of_pos _ (by omega)
      have hnle : n ≤ t := by
        dsimp [n]
        rw [ht2]
        have hvlo : 1 ≤ v := by omega
        by_cases hv1 : v=1
        · simp [hv1]
        · have hmod := Int.emod_lt_of_pos 2 (show 0<v by omega)
          by_cases hv2 : v=2
          · simp [hv2]
          · rw [Int.emod_eq_of_lt (by omega) (by omega)]
      have hRlo : pL x z-pA x y z-2*pB x y z ≤ R := by
        have hm := mul_nonneg hn0 (show 0 ≤ pD x y z by omega)
        dsimp [R];rw [ht2];nlinarith only [hm]
      have hRhi : R < pB x y z+v*pD x y z := by
        have hm := mul_lt_mul_of_pos_right hnhi (show 0 < pD x y z by omega)
        dsimp [R];rw [ht2]
        nlinarith only [hm,hsmall]
      have hRw : window R (pL x z) := by
        constructor <;> nlinarith only [hRlo,hcore,hRhi,hfirst,hL3]
      have hRp : 0 ≤ Rp := by
        dsimp [Rp]
        nlinarith only [hRlo,hnewlow,hnle]
      exact ⟨by omega,by omega,by dsimp [z];omega,hRw,hRp⟩
    · have hneq : x ≠ 2*y := by omega
      have htt : t=q-1 := by simp [t,hneq]
      let alpha := x-4*y
      let beta := y-4
      have halpha : 0 ≤ alpha := by dsimp [alpha];omega
      have hbeta : 0 ≤ beta := by dsimp [beta];omega
      have hL5Id : pL x z-5*pB x y z = 4*alpha^3 + 38*alpha^2*beta + 146*alpha^2 + 112*alpha*beta^2 + 848*alpha*beta + 1592*alpha + 96*beta^3 + 1056*beta^2 + 3808*beta + 4476 := by
        dsimp [pL,pB,z,alpha,beta];ring
      have hL5 : 0 < pL x z-5*pB x y z := by rw [hL5Id];positivity
      have hq4 : 4 ≤ q := by
        apply (Int.le_ediv_iff_mul_le hB).mpr
        nlinarith only [hL5,hAB]
      have ht0 : 0 ≤ t := by omega
      have hn0 : 0 ≤ n := Int.emod_nonneg _ (by omega)
      have hnhi : n < v := Int.emod_lt_of_pos _ (by omega)
      have hnle : n ≤ t := by
        have he := Int.emod_add_mul_ediv t v
        have hm := mul_nonneg (show 0 ≤ v by omega) (Int.ediv_nonneg ht0 (show 0 ≤ v by omega))
        dsimp [n];omega
      have hRid : R=r+pB x y z+n*pD x y z := by dsimp [R];rw [htt];nlinarith only [hdiv]
      have hRlo : pB x y z ≤ R := by
        rw [hRid]
        have hm := mul_nonneg hn0 (show 0 ≤ pD x y z by omega)
        omega
      have hRhi : R < 2*pB x y z+v*pD x y z := by
        rw [hRid]
        have hm := mul_lt_mul_of_pos_right hnhi (show 0 < pD x y z by omega)
        nlinarith only [hrB,hm]
      have hRw : window R (pL x z) := by
        constructor <;> nlinarith only [hRlo,hB,hRhi,hfirst,hL5]
      have hBz : 0 < 2*pB x y z-z-1 := by
        have hid : 2*pB x y z-z-1=1+z+2*x*z+2*x*y*z := by dsimp [pB];ring
        rw [hid]
        have hz0 : 0 < z := by dsimp [z];omega
        positivity
      have hRp : 0 ≤ Rp := by dsimp [Rp];nlinarith only [hRlo,hBz,hnle]
      exact ⟨by omega,ht0,by omega,hRw,hRp⟩
  have hn0 : 0 ≤ n := Int.emod_nonneg _ (by omega)
  have hnew : window Rp (2*pL x z-z-1) := by
    refine ⟨by omega,?_⟩
    have hu := hdata.2.2.2.1.2
    dsimp [Rp]
    omega
  exact ⟨hdata.1,hdata.2.1,hdata.2.2.1,hdata.2.2.2.1,hnew⟩


open private borrowT borrowU borrowP wEndpoint wNewEndpoint
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source

private theorem residual_cast (a b s t : ℕ) :
    vEndpoint a b s t=pL (x a) (z s)-pA (x a) (y b) (z s)-
      ((t : ℤ)*pB (x a) (y b) (z s)-(t%vNat b : ℕ)*pD (x a) (y b) (z s)) ∧
    vNewEndpoint a b s t=2*vEndpoint a b s t-z s-1+(t : ℤ)-(t%vNat b : ℕ) := by
  constructor
  · rfl
  · dsimp [vNewEndpoint]
    rw [Nat.cast_sub (Nat.mod_le _ _)]
    push_cast
    ring

private theorem borrow_first_windows (x y z v : ℤ)
    (hy : 4≤y) (hx : 2*y≤x) (hz : 2*x≤z) (hv : 4*v=y) :
    window (v*pD x y z) (pB x y z) ∧
    window (v*(2*pD x y z-1)) (2*pB x y z-1) := by
  have hb := borrow_basic x y z hy hx hz
  have hv0 : 0<v := by omega
  have hx0 : 0<x := by omega
  have hy0 : 0<y := by omega
  have hz0 : 0<z := by omega
  have hid : 2*(pB x y z-1)-y*pD x y z=
      ((x-1)*y+2*x+2)*z+x*y*(y+1) := by dsimp [pB,pD,pA];ring
  have hc : 0<2*(pB x y z-1)-y*pD x y z := by
    rw [hid]
    have hx1 : 0<x-1 := by omega
    positivity
  have he : 0<v*pD x y z := mul_pos hv0 (by omega)
  have hep : 0<v*(2*pD x y z-1) := mul_pos hv0 (by omega)
  have hvD := congrArg (fun r : ℤ => r*pD x y z) hv
  dsimp [window]
  constructor <;> constructor <;> nlinarith only [hc,he,hep,hvD,hv0]

/- Natural selectors are connected to the integer quotient before any physical
   masks are split. In the far case the lower quotient bound is proved first;
   subtraction then supplies the actual bit, rather than a numeric submask. -/
private theorem borrow_selector_windows (a b s : ℕ) (hb : 2≤b)
    (hba : b<a) (has : a<s) :
    let t := borrowT a b s
    let u := borrowU a b s
    t<2^(s-1) ∧ u<2^(s-1) ∧
    (∀ e : ℕ, u.testBit e=true → t.testBit e=true) ∧
    window ((vNat b : ℤ)*D a b s) (B a b s) ∧
    window ((vNat b : ℤ)*(2*D a b s-1)) (SU a b s) ∧
    window (vEndpoint a b s t) (L a b s) ∧
    window (vNewEndpoint a b s t+
      (if s=a+1 then 0 else if vNewEndpoint a b s t<0 then A a b s else 0)) (SV a b s) ∧
    window (wEndpoint a b s u) (K a b s) ∧
    window (wNewEndpoint a b s u+
      (if s=a+1 then 0 else
        if vNewEndpoint a b s t<0 ∨ wNewEndpoint a b s u<0 then A a b s else 0)) (SW a b s) := by
  dsimp only
  have ha : 2≤a := by omega
  have hs2 : 2≤s := by omega
  have hy : 4≤y b := by
    simpa [y] using pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2) hb
  have hx : 2*y b≤x a := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2)
      (show b+1≤a by omega)
    simpa [x,y,pow_succ,mul_comm] using hh
  have hz : 2*x a≤z s := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2)
      (show a+1≤s by omega)
    simpa [x,z,pow_succ,mul_comm] using hh
  have hv : 4*(vNat b : ℤ)=y b := by
    dsimp [vNat,y]
    push_cast
    conv_rhs => rw [show b=(b-2)+2 by omega,pow_add]
    ring
  have basic := borrow_basic (x a) (y b) (z s) hy hx hz
  have hB : 0<B a b s := basic.2.1
  have hLA : 0≤L a b s-A a b s := by
    have zz : 0<z s := by dsimp [z];positivity
    change 0≤pL (x a) (z s)-pA (x a) (y b) (z s)
    linarith [basic.2.2.2.2.1]
  have hqcast : (quotientT a b s : ℤ)=
      (pL (x a) (z s)-pA (x a) (y b) (z s))/pB (x a) (y b) (z s) := by
    dsimp [quotientT]
    rw [Int.toNat_of_nonneg hLA,Int.toNat_of_nonneg hB.le]
    rfl
  have hcap : 2*((2^(s-1) : ℕ) : ℤ)=z s := by
    push_cast
    dsimp [z]
    conv_rhs => rw [show s=(s-1)+1 by omega,pow_succ]
    ring
  have hSV : SV a b s=2*pL (x a) (z s)-z s-1 := by
    dsimp [SV,L,pL];ring
  have first := borrow_first_windows (x a) (y b) (z s) (vNat b : ℤ) hy hx hz hv
  by_cases hadj : s=a+1
  · have hza : z s=2*x a := by simp [z,x,hadj,pow_succ,mul_comm]
    have hdyadic : x a=2*y b ∨ 4*y b≤x a := by
      by_cases hab : a=b+1
      · left;simp [x,y,hab,pow_succ,mul_comm]
      · right
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2)
          (show b+2≤a by omega)
        simpa [x,y,pow_add,mul_comm] using hh
    have hxeq : (x a=2*y b) ↔ a=b+1 := by
      constructor
      · intro he
        by_contra hne
        have hlarge : 4*y b≤x a := by
          have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2)
            (show b+2≤a by omega)
          simpa [x,y,pow_add,mul_comm] using hh
        omega
      · intro he;simp [x,y,he,pow_succ,mul_comm]
    have vd := borrow_adjacent_V_windows (x a) (y b) (vNat b : ℤ) hy hx hv hdyadic
    dsimp only at vd
    rw [←hza,←hqcast] at vd
    have hq1 : 1≤quotientT a b s := by exact_mod_cast vd.1
    have htcast : (borrowT a b s : ℤ)=
        if x a=2*y b then 2 else (quotientT a b s : ℤ)-1 := by
      by_cases he : a=b+1
      · rw [if_pos (hxeq.mpr he)]
        simp only [borrowT, if_pos hadj, if_pos he, Nat.cast_ofNat]
      · simp only [borrowT,if_pos hadj,if_neg he,if_neg (mt hxeq.mp he)]
        exact Nat.cast_sub hq1
    rw [←htcast,←Int.natCast_emod] at vd
    have ht : borrowT a b s<2^(s-1) := by
      have hh := vd.2.2.1
      rw [←hcap] at hh
      exact_mod_cast (show (borrowT a b s : ℤ)<(2^(s-1) : ℕ) by omega)
    have hu0 : borrowU a b s=0 := by simp [borrowU,hadj]
    have wr := adjacent_W_windows (x a) (y b) hy hx
    dsimp only at wr
    rw [←hza] at wr
    refine ⟨ht,by rw [hu0];positivity,by simp [hu0],first.1,first.2,?_,?_,?_,?_⟩
    · rw [(residual_cast a b s (borrowT a b s)).1]
      exact vd.2.2.2.1
    · simp only [if_pos hadj,add_zero]
      rw [hSV,(residual_cast a b s (borrowT a b s)).2,
        (residual_cast a b s (borrowT a b s)).1]
      exact vd.2.2.2.2
    · simpa only [hu0,wEndpoint,hybridOld,Nat.zero_mod,Nat.cast_zero,
        zero_mul,sub_zero,K,A,pK,pA] using wr.1
    · simpa only [if_pos hadj,hu0,wNewEndpoint,wEndpoint,hybridOld,
        Nat.zero_mod,Nat.sub_self,Nat.cast_zero,zero_mul,sub_zero,add_zero,
        K,A,H,SW,pK,pA,pH] using wr.2
  · let p := borrowP a s
    have hp : 2≤(p : ℤ) := by
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2)
        (show 1≤s-a-1 by omega)
      simpa [p,borrowP] using hh
    have hzp : z s=2*x a*(p : ℤ) := by
      dsimp [p,borrowP,x,z]
      push_cast
      conv_lhs => rw [show s=a+(s-a-1)+1 by omega,pow_add,pow_add]
      ring
    have pre := borrow_far_V_windows (x a) (y b) (p : ℤ) (vNat b : ℤ)
      (quotientT a b s : ℤ) hy hx hp hv
      (by rw [←hzp,←hqcast];omega) (by rw [←hzp,←hqcast])
    dsimp only at pre
    rw [←hzp,←hqcast] at pre
    have hqlo : 2*p+1≤quotientT a b s := by exact_mod_cast pre.1
    have hple : p≤quotientT a b s := by omega
    have htlo : (quotientT a b s : ℤ)-(p : ℤ)≤(borrowT a b s : ℤ) := by
      have hh : quotientT a b s-p≤borrowT a b s := by
        simp only [borrowT,if_neg hadj]
        change quotientT a b s-p≤
          if (quotientT a b s).testBit (s-a-1) then quotientT a b s
            else quotientT a b s-p
        split <;> omega
      have hh' : ((quotientT a b s-p : ℕ) : ℤ)≤(borrowT a b s : ℤ) := by
        exact_mod_cast hh
      rwa [Nat.cast_sub hple] at hh'
    have hthi : (borrowT a b s : ℤ)≤(quotientT a b s : ℤ) := by
      have hh : borrowT a b s≤quotientT a b s := by
        simp only [borrowT,if_neg hadj]
        change (if (quotientT a b s).testBit (s-a-1) then quotientT a b s
          else quotientT a b s-p)≤quotientT a b s
        split <;> omega
      exact_mod_cast hh
    have vd := borrow_far_V_windows (x a) (y b) (p : ℤ) (vNat b : ℤ)
      (borrowT a b s : ℤ) hy hx hp hv
      (by rwa [←hzp,←hqcast]) (by rwa [←hzp,←hqcast])
    dsimp only at vd
    rw [←hzp,←hqcast,←Int.natCast_emod] at vd
    have ht : borrowT a b s<2^(s-1) := by
      have hh := vd.2.2.1
      rw [←hcap] at hh
      exact_mod_cast (show (borrowT a b s : ℤ)<(2^(s-1) : ℕ) by omega)
    have hueq : borrowU a b s=p := by simp [borrowU,hadj,p]
    have hu : borrowU a b s<2^(s-1) := by
      rw [hueq]
      dsimp [p,borrowP]
      exact Nat.pow_lt_pow_right (by omega : 1<2) (by omega)
    have hsub : ∀ e : ℕ, (borrowU a b s).testBit e=true →
        (borrowT a b s).testBit e=true := by
      have hh := singleton_bit_submask (quotientT a b s) (s-a-1)
        (show 2*2^(s-a-1)≤quotientT a b s by change 2*p≤_;omega)
      simpa only [borrowT,borrowU,if_neg hadj,borrowP] using hh
    have hnle : borrowU a b s%vNat b≤borrowU a b s := Nat.mod_le _ _
    have hchi : ((borrowU a b s-borrowU a b s%vNat b : ℕ) : ℤ)=
        (p : ℤ)-(borrowU a b s%vNat b : ℕ) := by
      rw [Nat.cast_sub hnle,hueq]
    have hD : 0≤D a b s := by have hh := basic.2.2.1;change 1≤D a b s at hh;omega
    have hFlo : (p : ℤ)*pA (x a) (y b) (2*x a*(p : ℤ))≤
        hybridOld a b s (borrowU a b s) := by
      rw [←hzp]
      have hm := mul_nonneg (show 0≤(p : ℤ)-(borrowU a b s%vNat b : ℕ) by
        rw [←hchi];positivity) hD
      dsimp [hybridOld]
      rw [hueq]
      rw [hueq] at hm
      change 0≤((p : ℤ)-(p%vNat b : ℕ))*D a b s at hm
      dsimp [D] at hm
      change (p : ℤ)*A a b s≤(p : ℤ)*B a b s-(p%vNat b : ℕ)*D a b s
      dsimp [D]
      nlinarith only [hm]
    have hFhi : hybridOld a b s (borrowU a b s)≤
        (p : ℤ)*pB (x a) (y b) (2*x a*(p : ℤ)) := by
      rw [←hzp]
      have hm := mul_nonneg (show (0 : ℤ)≤(borrowU a b s%vNat b : ℕ) by positivity) hD
      dsimp [hybridOld]
      rw [hueq] at *
      change (p : ℤ)*B a b s-(p%vNat b : ℕ)*D a b s≤(p : ℤ)*B a b s
      omega
    have wd := borrow_far_W_windows (x a) (y b) (p : ℤ)
      (hybridOld a b s (borrowU a b s))
      ((borrowU a b s-borrowU a b s%vNat b : ℕ) : ℤ)
      hy hx hp hFlo hFhi (by positivity)
      (by
        rw [hchi]
        have hh : (0 : ℤ)≤(borrowU a b s%vNat b : ℕ) := by positivity
        omega)
    dsimp only at wd
    rw [←hzp] at wd
    change window (wEndpoint a b s (borrowU a b s)) (K a b s) ∧
      window (wNewEndpoint a b s (borrowU a b s)+A a b s) (SW a b s) ∧
      (0≤wNewEndpoint a b s (borrowU a b s) →
        window (wNewEndpoint a b s (borrowU a b s)) (SW a b s)) at wd
    refine ⟨ht,hu,hsub,first.1,first.2,?_,?_,wd.1,?_⟩
    · rw [(residual_cast a b s (borrowT a b s)).1]
      exact vd.2.2.2.1
    · simp only [if_neg hadj]
      have hh : window (if vNewEndpoint a b s (borrowT a b s)<0 then
          vNewEndpoint a b s (borrowT a b s)+A a b s else
          vNewEndpoint a b s (borrowT a b s)) (SV a b s) := by
        rw [hSV,(residual_cast a b s (borrowT a b s)).2,
          (residual_cast a b s (borrowT a b s)).1]
        exact vd.2.2.2.2
      by_cases he : vNewEndpoint a b s (borrowT a b s)<0
      · simpa only [if_pos he] using hh
      · simpa only [if_neg he,add_zero] using hh
    · simp only [if_neg hadj]
      split
      · exact wd.2.1
      · rename_i he
        simp only [not_or,not_lt] at he
        simpa only [add_zero] using wd.2.2 he.2

end StrictDictionary
end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
