/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-unbounded-windows)
   mirror-E: none(waiver:private-consumed-unbounded-windows)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded singleton windows and shared polynomial window definitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source
import Mathlib.Data.Int.DivMod

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
namespace StrictDictionary

private def pA (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def pB (x y z : ℤ) : ℤ := 1+z+x*z+x*y*z
private def pD (x y z : ℤ) : ℤ := pB x y z-pA x y z
private def pL (x z : ℤ) : ℤ := 1+z+z^2+x*z^2
private def pK (y z : ℤ) : ℤ := 1+y+y*z+y*z^2
private def pH (y z : ℤ) : ℤ := 1+y+y*z
private def pG (x y z w : ℤ) : ℤ := pK y z-pA x y z-w*pL x z
private def pGp (x y z w : ℤ) : ℤ := 2*pG x y z w-pH y z+w*(z+1)
private def window (e T : ℤ) : Prop := 0 ≤ 2*e ∧ 2*e ≤ T-1

private theorem singleton_W_windows (x y z w : ℤ)
    (hx : 4 ≤ x) (hy : 2*x ≤ y) (hz : 4*x ≤ z)
    (hw : 2*x*w=y) :
    window (pG x y z w) (pK y z) ∧
    window (pGp x y z w) (2*pK y z-pH y z) ∧
    window (pGp x y z w+pA x y z) (2*pK y z-pH y z) := by
  let alpha := x-4
  let beta := y-2*x
  let gamma := z-4*x
  have ha : 0 ≤ alpha := by dsimp [alpha];omega
  have hb : 0 ≤ beta := by dsimp [beta];omega
  have hc : 0 ≤ gamma := by dsimp [gamma];omega
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hz0 : 0 < z := by omega
  have hA : 0 < pA x y z := by dsimp [pA];positivity
  have holdId : 2*x*pG x y z w = 16*alpha^4 + 8*alpha^3*beta + 12*alpha^3*gamma + 236*alpha^3 + 6*alpha^2*beta*gamma + 86*alpha^2*beta + 2*alpha^2*gamma^2 + 132*alpha^2*gamma + 1290*alpha^2 + alpha*beta*gamma^2 + 42*alpha*beta*gamma + 302*alpha*beta + 14*alpha*gamma^2 + 478*alpha*gamma + 3086*alpha + 3*beta*gamma^2 + 71*beta*gamma + 343*beta + 24*gamma^2 + 568*gamma + 2712 := by
    dsimp [pG,pGp,pA,pL,pK,pH,alpha,beta,gamma]
    linear_combination (-(1+z+z^2+x*z^2))*hw
  have holdPos : 0 < 2*x*pG x y z w := by
    rw [holdId]
    positivity
  have hnewId : 2*x*pGp x y z w = 32*alpha^4 + 16*alpha^3*beta + 24*alpha^3*gamma + 456*alpha^3 + 12*alpha^2*beta*gamma + 164*alpha^2*beta + 4*alpha^2*gamma^2 + 260*alpha^2*gamma + 2392*alpha^2 + 2*alpha*beta*gamma^2 + 82*alpha*beta*gamma + 542*alpha*beta + 28*alpha*gamma^2 + 926*alpha*gamma + 5436*alpha + 6*beta*gamma^2 + 135*beta*gamma + 567*beta + 48*gamma^2 + 1080*gamma + 4464 := by
    dsimp [pG,pGp,pA,pL,pK,pH,alpha,beta,gamma]
    linear_combination (z+1-2*(1+z+z^2+x*z^2))*hw
  have hnewPos : 0 < 2*x*pGp x y z w := by
    rw [hnewId]
    positivity
  have hG : 0 < pG x y z w :=
    (mul_pos_iff_of_pos_left (show 0<2*x by omega)).mp holdPos
  have hGp : 0 < pGp x y z w :=
    (mul_pos_iff_of_pos_left (show 0<2*x by omega)).mp hnewPos
  have hupper : x*(pK y z-1-2*pG x y z w)=
      x*(2*x-1)*y*z+x*(2*x-1)*y+2*x^2+y*z^2+y*z+y := by
    dsimp [pG,pK,pA,pL]
    linear_combination (1+z+z^2+x*z^2)*hw
  have hupper' : x*(2*pK y z-pH y z-1-2*(pGp x y z w+pA x y z))=
      x*(2*x-1)*y*z+x*(2*x-1)*y+2*x^2+2*y*z^2+y*z+y := by
    dsimp [pGp,pG,pK,pH,pA,pL]
    linear_combination (1+z+2*z^2+2*x*z^2)*hw
  have hp : 0 < x*(pK y z-1-2*pG x y z w) := by
    rw [hupper]
    have ht : 0 < 2*x-1 := by omega
    positivity
  have hp' : 0 < x*(2*pK y z-pH y z-1-2*(pGp x y z w+pA x y z)) := by
    rw [hupper']
    have ht : 0 < 2*x-1 := by omega
    positivity
  have hu : 2*pG x y z w ≤ pK y z-1 := by
    have hh := (mul_pos_iff_of_pos_left hx0).mp hp
    omega
  have hu' : 2*(pGp x y z w+pA x y z) ≤ 2*pK y z-pH y z-1 := by
    have hh := (mul_pos_iff_of_pos_left hx0).mp hp'
    omega
  exact ⟨⟨by omega,hu⟩,⟨by omega,by omega⟩,⟨by omega,hu'⟩⟩

/- These are the corrected constants. The older values K-1-2G=2x-y-2
   and Gp=4x^2y+y-2x+1 are not used. -/
private theorem adjacent_W_windows (x y : ℤ) (hy : 4 ≤ y) (hx : 2*y ≤ x) :
    let z := 2*x
    let G := pK y z-pA x y z
    let Gp := 2*G-pH y z
    window G (pK y z) ∧ window Gp (2*pK y z-pH y z) := by
  dsimp only
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hH : 0 < pH y (2*x)-2 := by
    dsimp [pH]
    have hh : 0 ≤ y*(2*x) := by positivity
    omega
  have hG : pK y (2*x)-pA x y (2*x)=x*(pH y (2*x)-2)+y := by
    dsimp [pK,pA,pH];ring
  have hslack : pK y (2*x)-1-2*(pK y (2*x)-pA x y (2*x))=2*x-y := by
    dsimp [pK,pA];ring
  have hGp : 2*(pK y (2*x)-pA x y (2*x))-pH y (2*x)=
      4*x^2*y+y-2*x-1 := by dsimp [pK,pA,pH];ring
  have hG0 : 0 < pK y (2*x)-pA x y (2*x) := by rw [hG];positivity
  have hGp0 : 0 < 2*(pK y (2*x)-pA x y (2*x))-pH y (2*x) := by
    rw [hGp]
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ y by omega) (sq_nonneg x)
    nlinarith only [hm,sq_nonneg (x-1),hx0,hy]
  constructor
  · constructor <;> omega
  · constructor
    · omega
    · have hH0 : 0 < pH y (2*x) := by dsimp [pH];positivity
      omega


private theorem singleton_basic (x y z : ℤ) (hx : 4 ≤ x) (hy : 2*x ≤ y) (hz : y ≤ z) :
    0 < pA x y z ∧ 0 < pB x y z ∧ 1 ≤ pD x y z ∧
    z+1 < pA x y z ∧ z+1 ≤ pL x z-pA x y z ∧
    2*pA x y z ≤ 2*pL x z-z-2 ∧ pL x z < x*y*z^2-1 := by
  have hx0 : 0 < x := by omega
  have hy8 : 8 ≤ y := by omega
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
    have hc : 0 ≤ x*y-1 := by nlinarith only [hxy,hx]
    have hp : 0 ≤ (x*y-1)*z := mul_nonneg hc hz0.le
    have hxy0 : 0 < x*y := mul_pos hx0 hy0
    nlinarith only [haId,hp,hxy0,hx0]
  have hgap : pL x z-pA x y z=(z+1)*pD x y z := by
    dsimp [pL,pA,pD,pB];ring
  have hLA : z+1 ≤ pL x z-pA x y z := by
    have hm := mul_le_mul_of_nonneg_left hDn (show 0 ≤ z+1 by omega)
    rw [hgap]
    simpa only [mul_one] using hm
  have hc : 0 ≤ x*y-x-3 := by nlinarith only [hxy,hx]
  have hp : 0 ≤ (x*y-x-3)*z^2 := mul_nonneg hc (sq_nonneg z)
  have hnId : x*y*z^2-1-pL x z=(x*y-x-3)*z^2+2*z^2-z-2 := by
    dsimp [pL];ring
  have hN : pL x z < x*y*z^2-1 := by
    nlinarith only [hp,hnId,sq_nonneg (z-1),hz8]
  exact ⟨hA,hB,hDn,hAz,hLA,by omega,hN⟩

private theorem singleton_first_windows (x y z v : ℤ)
    (hx : 4 ≤ x) (hy : 2*x ≤ y) (hz : y ≤ z) (hv : 4*v=y) :
    window (v*pD x y z) (pB x y z) ∧
    window (v*(2*pD x y z-1)) (2*pB x y z-1) := by
  have hb := singleton_basic x y z hx hy hz
  have hv0 : 0 < v := by omega
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hz0 : 0 < z := by omega
  have hcId : 2*(pB x y z-1)-y*pD x y z=
      ((x-1)*y+2*x+2)*z+x*y*(y+1) := by dsimp [pA,pB,pD];ring
  have hc : 0 < 2*(pB x y z-1)-y*pD x y z := by
    rw [hcId]
    have hxm : 0 < x-1 := by omega
    positivity
  have he : 0 < v*pD x y z := mul_pos hv0 (by omega)
  have hep : 0 < v*(2*pD x y z-1) := mul_pos hv0 (by omega)
  have hvD := congrArg (fun r : ℤ => r*pD x y z) hv
  dsimp [window]
  constructor <;> constructor <;> nlinarith only [hvD,hc,he,hep,hv0]

private theorem singleton_V_windows (x y z v : ℤ)
    (hx : 4 ≤ x) (hy : 2*x ≤ y) (hz : y ≤ z) (hv : 4*v=y)
    (hdyadic : z=y ∨ z=2*y ∨ 4*y ≤ z) :
    let t := (pL x z-pA x y z)/pB x y z
    let n := t%v
    let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
    let Rp := 2*R-z-1+t-n
    0 ≤ t ∧ 2*t < z ∧ window R (pL x z) ∧
      window (if Rp<0 then Rp+pA x y z else Rp) (2*pL x z-z-1) := by
  dsimp only
  let t := (pL x z-pA x y z)/pB x y z
  let n := t%v
  let R := pL x z-pA x y z-(t*pB x y z-n*pD x y z)
  let Rp := 2*R-z-1+t-n
  have hb := singleton_basic x y z hx hy hz
  have hA : 0 < pA x y z := hb.1
  have hB : 0 < pB x y z := hb.2.1
  have hD : 1 ≤ pD x y z := hb.2.2.1
  have hAz : z+1 < pA x y z := hb.2.2.2.1
  have hLA : z+1 ≤ pL x z-pA x y z := hb.2.2.2.2.1
  have hAs : 2*pA x y z ≤ 2*pL x z-z-2 := hb.2.2.2.2.2.1
  have hN : pL x z < x*y*z^2-1 := hb.2.2.2.2.2.2
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hz0 : 0 < z := by omega
  have hv2 : 2 ≤ v := by omega
  have ht : 0 ≤ t := Int.ediv_nonneg (by omega) hB.le
  let r := (pL x z-pA x y z)%pB x y z
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hB)
  have hrB : r < pB x y z := Int.emod_lt_of_pos _ hB
  have hdiv : r+pB x y z*t=pL x z-pA x y z := by
    exact Int.emod_add_mul_ediv _ _
  have hn0 : 0 ≤ n := Int.emod_nonneg _ (by omega)
  have hnv : n < v := Int.emod_lt_of_pos _ (by omega)
  have hnle : n ≤ t := by
    have he := Int.emod_add_mul_ediv t v
    have hp := mul_nonneg (show 0 ≤ v by omega) (Int.ediv_nonneg ht (show 0 ≤ v by omega))
    dsimp [n]
    omega
  have hR : R=r+n*pD x y z := by dsimp [R];nlinarith only [hdiv]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact add_nonneg hr0 (mul_nonneg hn0 (by omega))
  have hRhi : R < pB x y z+(v-1)*pD x y z := by
    have hm := mul_le_mul_of_nonneg_right (show n ≤ v-1 by omega) (show 0 ≤ pD x y z by omega)
    rw [hR]
    omega
  have hrec : z*pB x y z=x*y*z^2-1+pL x z := by dsimp [pB,pL];ring
  have htcap : 2*t < z := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_right (show z ≤ 2*t by omega) hB.le
    nlinarith only [hm,hdiv,hr0,hrec,hN,hA]
  have hRwindow : window R (pL x z) := by
    refine ⟨by omega,?_⟩
    rcases hdyadic with hzy | hzy | hzy
    · have hsmall : pL x z-pA x y z < pB x y z := by
        have hid : pB x y y-(pL x y-pA x y y)=1+x+2*x*y+(x-1)*y^2 := by
          dsimp [pA,pB,pL];ring
        have hpos : 0 < pB x y y-(pL x y-pA x y y) := by
          rw [hid]
          have hxm : 0 < x-1 := by omega
          positivity
        rw [hzy]
        omega
      have ht0 : t=0 := Int.ediv_eq_zero_of_lt (by omega) hsmall
      have hnzero : n=0 := by simp [n,ht0]
      have hRval : R=pL x z-pA x y z := by simp [R,ht0,hnzero]
      have hid : pL x y-1-2*(pL x y-pA x y y)=
          (x-1)*y^2+(2*x-1)*y+2*x := by dsimp [pL,pA];ring
      have hp : 0 < pL x y-1-2*(pL x y-pA x y y) := by
        rw [hid]
        have hxm : 0 < x-1 := by omega
        have hxm' : 0 < 2*x-1 := by omega
        positivity
      rw [hRval,hzy]
      omega
    · have hlow : pB x y z ≤ pL x z-pA x y z := by
        have hid : pL x (2*y)-pA x y (2*y)-pB x y (2*y)=
            (4*y-3*x)*y-x-1 := by dsimp [pL,pA,pB];ring
        have hm := mul_le_mul_of_nonneg_right (show x ≤ 4*y-3*x by omega) hy0.le
        have hxy := mul_le_mul_of_nonneg_left (show 2 ≤ y by omega) hx0.le
        rw [hzy]
        nlinarith only [hid,hm,hxy,hx]
      have hhigh : pL x z-pA x y z < 2*pB x y z := by
        have hid : 2*pB x y (2*y)-pL x (2*y)+pA x y (2*y)=
            2*(x-2)*y^2+5*x*y+x+2*y+2 := by dsimp [pL,pA,pB];ring
        have hp : 0 < 2*pB x y (2*y)-pL x (2*y)+pA x y (2*y) := by
          rw [hid]
          have hxm : 0 < x-2 := by omega
          positivity
        rw [hzy]
        omega
      have ht1 : t=1 := by
        apply (Int.ediv_eq_iff_of_pos hB).mpr
        constructor <;> omega
      have hn1 : n=1 := by dsimp [n];rw [ht1];exact Int.emod_eq_of_lt (by omega) (by omega)
      have hRval : R=pL x z-2*pA x y z := by
        dsimp [R,pD]
        rw [ht1,hn1]
        ring
      have hid : pL x (2*y)-1-2*(pL x (2*y)-2*pA x y (2*y))=
          2*((2*x-2)*y^2+(2*x-1)*y+2*x+1) := by dsimp [pL,pA];ring
      have hp : 0 < pL x (2*y)-1-2*(pL x (2*y)-2*pA x y (2*y)) := by
        rw [hid]
        have hxm : 0 < 2*x-2 := by omega
        have hxm' : 0 < 2*x-1 := by omega
        positivity
      rw [hRval,hzy]
      omega
    · let alpha := x-4
      let beta := y-2*x
      let gamma := z-4*y
      have ha : 0 ≤ alpha := by dsimp [alpha];omega
      have hb' : 0 ≤ beta := by dsimp [beta];omega
      have hc : 0 ≤ gamma := by dsimp [gamma];omega
      have hid : 2*pL x z-4*pB x y z-(y-4)*pD x y z = 52*alpha^3 + 52*alpha^2*beta + 22*alpha^2*gamma + 730*alpha^2 + 13*alpha*beta^2 + 11*alpha*beta*gamma + 525*alpha*beta + 2*alpha*gamma^2 + 206*alpha*gamma + 3356*alpha + 80*beta^2 + 59*beta*gamma + 1276*beta + 10*gamma^2 + 474*gamma + 5070 := by
        dsimp [pL,pB,pD,pA,alpha,beta,gamma];ring
      have hp : 0 < 2*pL x z-4*pB x y z-(y-4)*pD x y z := by
        rw [hid]
        positivity
      have hvD := congrArg (fun r : ℤ => r*pD x y z) hv
      nlinarith only [hRhi,hp,hvD]
  have hnew : window (if Rp<0 then Rp+pA x y z else Rp) (2*pL x z-z-1) := by
    dsimp [window]
    by_cases hneg : Rp<0
    · rw [if_pos hneg]
      have hRplow : -z-1 ≤ Rp := by dsimp [Rp];omega
      constructor <;> omega
    · rw [if_neg hneg]
      constructor
      · omega
      · dsimp [Rp]
        have hRw := hRwindow.2
        omega
  exact ⟨ht,htcap,hRwindow,hnew⟩

open private x y z A B D L K H SU SV SW vNat wBit quotientT
  hybridOld hybridNew vEndpoint vNewEndpoint
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source

private theorem singleton_scalar_windows (a b s : ℕ) (ha : 2 ≤ a)
    (hab : a < b) (hbs : b ≤ s) (hnotbalanced : ¬ (b=s ∧ s=a+1)) :
    let t := quotientT a b s
    let w := wBit a b
    t < 2^(s-1) ∧ w < 2^(b-1) ∧
    window ((vNat b : ℕ)*D a b s) (B a b s) ∧
    window ((vNat b : ℕ)*(2*D a b s-1)) (SU a b s) ∧
    window (vEndpoint a b s t) (L a b s) ∧
    window (if vNewEndpoint a b s t<0 then
      vNewEndpoint a b s t+A a b s else vNewEndpoint a b s t) (SV a b s) ∧
    window (K a b s-A a b s-(w : ℤ)*L a b s) (K a b s) ∧
    window (2*(K a b s-A a b s-(w : ℤ)*L a b s)-H b s+(w : ℤ)*(z s+1))
      (SW a b s) ∧
    window (2*(K a b s-A a b s-(w : ℤ)*L a b s)-H b s+(w : ℤ)*(z s+1)+A a b s)
      (SW a b s) := by
  dsimp only
  have hs2 : 2 ≤ s := by omega
  have hsa : a+2 ≤ s := by omega
  have hx : 4 ≤ x a := by
    simpa [x] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  have hy : 2*x a ≤ y b := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a+1 ≤ b by omega)
    simpa [x,y,pow_succ,mul_comm] using hp
  have hz : y b ≤ z s := by
    simpa [y,z] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hbs
  have hz4 : 4*x a ≤ z s := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hsa
    simpa [x,z,pow_add,mul_comm] using hp
  have hv : 4*(vNat b : ℤ)=y b := by
    dsimp [vNat,y]
    push_cast
    conv_rhs => rw [show b=(b-2)+2 by omega,pow_add]
    ring
  have hw : 2*x a*(wBit a b : ℤ)=y b := by
    dsimp [x,wBit,y]
    push_cast
    conv_rhs => rw [show b=a+(b-a-1)+1 by omega,pow_add,pow_add]
    ring
  have hdyadic : z s=y b ∨ z s=2*y b ∨ 4*y b ≤ z s := by
    by_cases he : s=b
    · left; simp [z,y,he]
    · by_cases he' : s=b+1
      · right;left;simp [z,y,he',pow_succ,mul_comm]
      · right;right
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show b+2 ≤ s by omega)
        simpa [z,y,pow_add,mul_comm] using hp
  have hb := singleton_basic (x a) (y b) (z s) hx hy hz
  have hnonneg : 0 ≤ L a b s-A a b s := by
    change 0 ≤ pL (x a) (z s)-pA (x a) (y b) (z s)
    have hp : 0 < z s := by dsimp [z];positivity
    linarith [hb.2.2.2.2.1]
  have hB : 0 < B a b s := hb.2.1
  have htcast : (quotientT a b s : ℤ)=
      (pL (x a) (z s)-pA (x a) (y b) (z s))/pB (x a) (y b) (z s) := by
    dsimp [quotientT]
    rw [Int.toNat_of_nonneg hnonneg,Int.toNat_of_nonneg hB.le]
    rfl
  have vdata := singleton_V_windows (x a) (y b) (z s) (vNat b : ℤ) hx hy hz hv hdyadic
  dsimp only at vdata
  rw [←htcast,←Int.natCast_emod] at vdata
  have wdata := singleton_W_windows (x a) (y b) (z s) (wBit a b : ℤ) hx hy hz4 hw
  have first := singleton_first_windows (x a) (y b) (z s) (vNat b : ℤ) hx hy hz hv
  have hcapacity : 2*((2^(s-1) : ℕ) : ℤ)=z s := by
    push_cast
    dsimp [z]
    conv_rhs => rw [show s=(s-1)+1 by omega,pow_succ]
    ring
  have ht : quotientT a b s < 2^(s-1) := by
    have hh := vdata.2.1
    rw [←hcapacity] at hh
    exact_mod_cast (show (quotientT a b s : ℤ)<(2^(s-1) : ℕ) by omega)
  have hwcap : wBit a b < 2^(b-1) := by
    dsimp [wBit]
    exact Nat.pow_lt_pow_right (by omega : 1<2) (by omega)
  have hchi : ((quotientT a b s-quotientT a b s%vNat b : ℕ) : ℤ)=
      (quotientT a b s : ℤ)-(quotientT a b s%vNat b : ℕ) := by
    exact Nat.cast_sub (Nat.mod_le _ _)
  have hR : vEndpoint a b s (quotientT a b s)=
      pL (x a) (z s)-pA (x a) (y b) (z s)-
        ((quotientT a b s : ℤ)*pB (x a) (y b) (z s)-
          (quotientT a b s%vNat b : ℕ)*pD (x a) (y b) (z s)) := rfl
  have hRp : vNewEndpoint a b s (quotientT a b s)=
      2*vEndpoint a b s (quotientT a b s)-z s-1+
        (quotientT a b s : ℤ)-(quotientT a b s%vNat b : ℕ) := by
    dsimp [vNewEndpoint]
    rw [hchi]
    push_cast
    ring
  refine ⟨ht,hwcap,first.1,first.2,?_,?_,wdata.1,wdata.2.1,wdata.2.2⟩
  · simpa only [hR,L,pL] using vdata.2.2.1
  · have hsv : SV a b s=2*pL (x a) (z s)-z s-1 := by
      dsimp [SV,L,pL];ring
    rw [hsv,hRp,hR]
    exact vdata.2.2.2

end StrictDictionary
end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
