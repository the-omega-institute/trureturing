/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.concentrated_scalar; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n23_low_strict,D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n24_low_strict,D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict
   digest: Strict outer scalar intervals with the retained low-r mass. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowScalarData
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterPolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterScalar
noncomputable section

open SixRowMiddlePolynomial (W slack cn den T138)
open SixRowScalarData SixRowOuterPolynomial
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar (quadratic_lower)

/-- The two cleared head-cap eliminations, on the entire low/cap range.
    The second estimate retains the actual tail Cauchy variable d. -/
theorem head_cap_elimination (r H D a q d : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hr : r ≤ 1/5) (hDd : D ≤ d) :
    Den r*W r H D a q ≤ Den r*(q+r*(6-15*r))+cn r*V r q ∧
    Den r*W r H D a q ≤ Den r*(q+r*d)+An r*V r q := by
  have hr2 : r^2 ≤ 1/25 := by nlinarith only [h.r_nonneg,hr]
  have hd : 0 < den r := by dsimp only [den]; linarith only [hr]
  have hc : 0 ≤ cn r := by dsimp only [cn]; nlinarith only [hr,hr2]
  have hA : 0 ≤ An r := by dsimp only [An]; nlinarith only [hr,hr2]
  have hDen : 0 < Den r := by dsimp only [Den]; nlinarith only [hr,hr2]
  have hcap := mul_le_mul_of_nonneg_left h.head_cap hd.le
  have hid : den r*((cn r/den r)*H) = cn r*H := by
    field_simp [ne_of_gt hd]
  rw [hid] at hcap
  have hp := mul_nonneg h.r_nonneg (sub_nonneg.mpr hcap)
  have hv : a+2*r*H ≤ V r q := by dsimp only [V]; linarith only [h.coupled]
  have hvC := mul_le_mul_of_nonneg_left hv hc
  have hvA := mul_le_mul_of_nonneg_left hv hA
  have hm := h.mass
  dsimp only [slack] at hm
  have hb := mul_nonneg h.r_nonneg (show 0 ≤ 6-15*r-H-D by linarith only [hm])
  have hbd := mul_nonneg hDen.le hb
  have hdd := mul_nonneg (mul_nonneg hDen.le h.r_nonneg) (sub_nonneg.mpr hDd)
  dsimp only [W,Den,An,cn,den] at *
  constructor <;> nlinarith only [hp,hvC,hvA,hbd,hdd]

/-- Exact tensor tables and cap elimination give the entire [1/12,1/5]
    interval; no lower-Cauchy or variance conclusion is assumed. -/
theorem cap_interval_strict (r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hrl : 1/12 ≤ r) (hru : r ≤ 1/5) :
    W r H D a q < T138 r := by
  let d := Real.sqrt (20*q)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2=20*q := Real.sq_sqrt (mul_nonneg (by norm_num) h.q_nonneg)
  have hDd : D ≤ d := by nlinarith only [hd,hd2,h.tail_cauchy,h.D_nonneg]
  have hDen : 0 < Den r := by dsimp only [Den]; nlinarith only [hrl,hru]
  have hc : 0 ≤ cn r := by dsimp only [cn]; nlinarith only [hrl,hru]
  obtain ⟨hb1,hb2⟩ := head_cap_elimination r H D a q d h hru hDd
  let x := (60/7)*(r-1/12)
  have hx : 0 ≤ x := by dsimp [x]; linarith only [hrl]
  have hX : x ≤ 1 := by dsimp [x]; linarith only [hru]
  have hxid : (1/12:ℝ)+(7/60)*x=r := by dsimp [x]; ring
  by_cases hq : q ≤ 3/32
  · have hdu : d ≤ 137/100 := by nlinarith only [hd,hd2,hq]
    have hh := p2_mid x ((100/137)*d) hx hX (by positivity) (by nlinarith only [hdu])
    have hyid : (137/100:ℝ)*((100/137)*d)=d := by ring
    rw [hxid,hyid] at hh
    have hqeq : q=d^2/20 := by linarith only [hd2]
    conv at hb2 => rhs; rw [hqeq]
    apply (mul_lt_mul_iff_right₀ hDen).mp
    dsimp only [P2,V] at hh hb2
    nlinarith only [hh,hb2]
  · have hqc : 3/32 ≤ q := le_of_lt (lt_of_not_ge hq)
    have hm := h.mass
    dsimp only [slack] at hm
    have hqu : q ≤ 4-10*r := h.tail_cap.trans
      (max_le (by linarith only [hru]) (by linarith only [hm,h.H_nonneg]))
    have hl := p1_mid_cut x hx hX
    have hu := p1_mid_tail x hx hX
    rw [hxid] at hl hu
    have hl0 : 0 < P1 r (3/32) (T138 r) := by linarith only [hl]
    have hu0 : 0 < P1 r (4-10*r) (T138 r) := by linarith only [hu]
    have hmin : 0 < min (P1 r (3/32) (T138 r)) (P1 r (4-10*r) (T138 r)) :=
      lt_min hl0 hu0
    have hP (Q : ℝ) : P1 r Q (T138 r) =
        -(cn r)/4*Q^2+(2*cn r-Den r)*Q+
        (T138 r*Den r-4*cn r+15*cn r*r^2-Den r*r*(6-15*r)) := by
      unfold P1 V
      ring
    have hh := quadratic_lower (-(cn r)/4) (2*cn r-Den r)
      (T138 r*Den r-4*cn r+15*cn r*r^2-Den r*r*(6-15*r))
      (3/32) (4-10*r) q
      (min (P1 r (3/32) (T138 r)) (P1 r (4-10*r) (T138 r)))
      (by linarith only [hc]) hqc hqu
      (by rw [← hP]; exact min_le_left _ _)
      (by rw [← hP]; exact min_le_right _ _)
    have hp : 0 < P1 r q (T138 r) := hmin.trans_le (by rw [hP q]; exact hh)
    apply (mul_lt_mul_iff_right₀ hDen).mp
    unfold P1 at hp
    linarith only [hp,hb1]

/-- For [0,1/12] the n24 threshold is a weak W bound; its only possible
    equality corner is r=q=0. This does NOT assert W<T138 globally. -/
theorem low_W_le (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q)
    (hr : r ≤ 1/12) :
    W r H D a q ≤ T144 r ∧ (W r H D a q=T144 r → r=0 ∧ q=0) := by
  let d := Real.sqrt (20*q)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2=20*q := Real.sq_sqrt (mul_nonneg (by norm_num) h.q_nonneg)
  have hDd : D ≤ d := by nlinarith only [hd,hd2,h.tail_cauchy,h.D_nonneg]
  have hDen : 0 < Den r := by dsimp only [Den]; nlinarith only [h.r_nonneg,hr]
  have hc : 0 ≤ cn r := by dsimp only [cn]; nlinarith only [h.r_nonneg,hr]
  obtain ⟨hb1,hb2⟩ := head_cap_elimination r H D a q d h (by linarith only [hr]) hDd
  by_cases hq : q ≤ 3/32
  · have hdu : d ≤ 137/100 := by nlinarith only [hd,hd2,hq]
    have hp := p2_low_separation (12*r) ((100/137)*d)
      (mul_nonneg (by norm_num) h.r_nonneg) (by linarith only [hr])
      (by positivity) (by nlinarith only [hdu])
    have hxid : (12*r)/12=r := by ring
    have hyid : (137/100:ℝ)*((100/137)*d)=d := by ring
    rw [hxid,hyid] at hp
    have hqeq : q=d^2/20 := by linarith only [hd2]
    conv at hb2 => rhs; rw [hqeq]
    have hp0 : 0 ≤ P2 r d (T144 r) := by
      nlinarith only [hp,sq_nonneg ((12*r)^2),sq_nonneg (((100/137)*d)^2)]
    have hW : W r H D a q ≤ T144 r := by
      apply (mul_le_mul_iff_right₀ hDen).mp
      dsimp only [P2,V] at hp0 hb2
      nlinarith only [hp0,hb2]
    refine ⟨hW,?_⟩
    intro heq
    have hzero : P2 r d (T144 r) ≤ 0 := by
      rw [heq] at hb2
      dsimp only [P2,V] at hb2 ⊢
      nlinarith only [hb2]
    have hr4 : ((12*r)^2)^2=0 := by
      nlinarith only [hp,hzero,sq_nonneg (((100/137)*d)^2),sq_nonneg ((12*r)^2)]
    have hd4 : ((((100/137)*d)^2)^2)=0 := by
      nlinarith only [hp,hzero,sq_nonneg ((12*r)^2),sq_nonneg (((100/137)*d)^2)]
    have hr0 : r=0 := by
      have hh := sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hr4)
      linarith only [hh]
    have hd0 : d=0 := by
      have hh := sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hd4)
      linarith only [hh]
    exact ⟨hr0,by nlinarith only [hd0,hd2]⟩
  · have hqc : 3/32 ≤ q := le_of_lt (lt_of_not_ge hq)
    have hqu := q_le_29_8 r H D a q h
    have hx := mul_nonneg (show (0:ℝ) ≤ 12 by norm_num) h.r_nonneg
    have hl := p1_low_cut (12*r) hx (by linarith only [hr])
    have hu := p1_low_tail (12*r) hx (by linarith only [hr])
    have hxid : (1/12:ℝ)*(12*r)=r := by ring
    rw [zero_add,hxid] at hl hu
    have hl0 : 0 < P1 r (3/32) (T144 r) := by linarith only [hl]
    have hu0 : 0 < P1 r (29/8) (T144 r) := by linarith only [hu]
    have hmin : 0 < min (P1 r (3/32) (T144 r)) (P1 r (29/8) (T144 r)) := lt_min hl0 hu0
    have hP (Q : ℝ) : P1 r Q (T144 r) =
        -(cn r)/4*Q^2+(2*cn r-Den r)*Q+
        (T144 r*Den r-4*cn r+15*cn r*r^2-Den r*r*(6-15*r)) := by
      unfold P1 V
      ring
    have hh := quadratic_lower (-(cn r)/4) (2*cn r-Den r)
      (T144 r*Den r-4*cn r+15*cn r*r^2-Den r*r*(6-15*r))
      (3/32) (29/8) q
      (min (P1 r (3/32) (T144 r)) (P1 r (29/8) (T144 r)))
      (by linarith only [hc]) hqc hqu
      (by rw [← hP]; exact min_le_left _ _)
      (by rw [← hP]; exact min_le_right _ _)
    have hW : W r H D a q < T144 r := by
      have hp : 0 < P1 r q (T144 r) := hmin.trans_le (by rw [hP q]; exact hh)
      apply (mul_lt_mul_iff_right₀ hDen).mp
      unfold P1 at hp
      linarith only [hp,hb1]
    exact ⟨hW.le,fun heq => False.elim (ne_of_lt hW heq)⟩

/-- The retained square closes the r=q=0, W=4 corner at n24.
    M=144+H there, so it is strictly above the center 140. -/
theorem n24_low_strict (j r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) :
    0 < gap 144 j (1/140) r H D a q := by
  obtain ⟨hW,heq⟩ := low_W_le r H D a q h hr
  have hs := square_completion 144 j (1/140) r H D a q (by norm_num)
  have hT : T 144 (1/140) r = T144 r := by unfold T T144; norm_num; ring
  rw [hT] at hs
  by_cases hlt : W r H D a q < T144 r
  · nlinarith only [hs,hlt,sq_nonneg (mass 144 j r H D-(2+r)/(2*(1/140:ℝ)))]
  · have he : W r H D a q=T144 r := le_antisymm hW (le_of_not_gt hlt)
    obtain ⟨hr0,hq0⟩ := heq he
    have hD : D=0 := by nlinarith only [h.tail_cauchy,hq0,h.D_nonneg]
    have hM : 144 ≤ mass 144 j r H D := by
      dsimp only [mass]; rw [hr0,hD]; linarith only [h.H_nonneg]
    have hcenter : (2+r)/(2*(1/140:ℝ))=140 := by rw [hr0]; norm_num
    rw [hcenter] at hs
    have hp : 0 < (mass 144 j r H D-140)^2 := sq_pos_of_pos (by linarith only [hM])
    nlinarith only [hs,he,hp]

/-- Continuous [1/3,79/200] region. -/
theorem continuous_strict (r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hrl : 1/3 ≤ r) (hru : r ≤ 79/200) :
    W r H D a q < T138 r := by
  have hb := mass_energy_envelope r H D a q h
  have hh := quadratic_lower (-1179229/4842) (861068/4842) (-155752/4842)
    (1/3) (79/200) r (1/100) (by norm_num) hrl hru (by norm_num) (by norm_num)
  have hid : T138 r-(6-15*r)*(6-14*r) =
      (-1179229/4842)*r^2+(861068/4842)*r+(-155752/4842) := by
    unfold T138
    ring
  linarith only [hh,hb,hid]

/-- Variance region [3/10,1/3]; positive root is constructed, not assumed. -/
theorem variance_strict (r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hrl : 3/10 ≤ r) (hru : r ≤ 1/3) :
    W r H D a q < T138 r := by
  let L := H+D
  let B := 6-15*r
  let ell := (7-15*r)/2
  have hL : 0 ≤ L := add_nonneg h.H_nonneg h.D_nonneg
  have hB : B ≤ 3/2 := by dsimp [B]; linarith only [hrl]
  have hell : 0 < ell := by dsimp [ell]; linarith only [hru]
  have hp := quadratic_lower (-796913/9684) (511636/9684) (-81509/9684)
    (3/10) (1/3) r (1/100) (by norm_num) hrl hru (by norm_num) (by norm_num)
  have hP : 0 < T138 r-ell^2-r*ell := by
    have hid : T138 r-ell^2-r*ell =
        (-796913/9684)*r^2+(511636/9684)*r+(-81509/9684) := by
      unfold T138 ell
      ring
    linarith only [hp,hid]
  have hT : 0 < T138 r := by nlinarith only [hP,hell,hrl]
  let t := (Real.sqrt (r^2+4*T138 r)-r)/2
  have hrads := Real.sq_sqrt (show 0 ≤ r^2+4*T138 r by positivity)
  have hrad0 := Real.sqrt_nonneg (r^2+4*T138 r)
  have ht : 0 < t := by dsimp [t]; nlinarith only [hrads,hrad0,hT,hrl]
  have ht2 : t^2+r*t=T138 r := by dsimp [t]; nlinarith only [hrads]
  have htell : ell < t := by
    nlinarith only [ht2,hP,hell,ht,hrl]
  have hA : a+q ≤ L^2 := by
    dsimp [L]; nlinarith only [h.head_sq,h.q_mass,mul_nonneg h.H_nonneg h.D_nonneg]
  have hW1 : W r H D a q ≤ L^2+r*L := by dsimp [W,L] at *; linarith only [hA]
  have hW2 : W r H D a q ≤ (7/5)*(4*(B-L)-(B-L)^2/3)+L^2/15+r*L := by
    have hv := h.variance
    dsimp only [W,L,B,slack] at *
    nlinarith only [hv,h.q_nonneg,mul_nonneg h.H_nonneg h.D_nonneg]
  by_cases hLt : L < t
  · have hp := mul_pos (sub_pos.mpr hLt) (show 0 < t+L+r by linarith only [ht,hL,hrl])
    nlinarith only [hW1,ht2,hp]
  · have htL : t ≤ L := le_of_not_gt hLt
    have hm := mul_nonneg (sub_nonneg.mpr htL)
      (show 0 ≤ (2/5)*(L+t)-(14/15)*B+28/5-r by linarith only [hL,ht,hB,hru])
    have hV : (7/5)*(4*(B-L)-(B-L)^2/3)+L^2/15+r*L ≤
        (7/5)*(4*(B-t)-(B-t)^2/3)+t^2/15+r*t := by nlinarith only [hm]
    have hQ0 := quadratic_lower (-126094/1614) (171083/1614) (-39544/1614)
      (3/10) (1/3) r (1/10) (by norm_num) hrl hru (by norm_num) (by norm_num)
    have hQ1 : 0 < 3*T138 r+27*r*ell+225*r^2-36 := by
      have hid : 3*T138 r+27*r*ell+225*r^2-36 =
          (-126094/1614)*r^2+(171083/1614)*r+(-39544/1614) := by
        unfold T138 ell
        ring
      linarith only [hQ0,hid]
    have hrt := mul_pos (show 0 < r by linarith only [hrl]) (sub_pos.mpr htell)
    dsimp only [B] at *
    nlinarith only [hW2,hV,ht2,hQ1,hrt]

/-- Combined base W bound; imports the peer's middle theorem unchanged. -/
theorem base_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q)
    (hrl : 1/12 ≤ r) (hru : r ≤ 79/200) : W r H D a q < T138 r := by
  by_cases h1 : r ≤ 1/5
  · exact cap_interval_strict r H D a q h hrl h1
  by_cases h2 : r ≤ 3/10
  · exact SixRowMiddleScalar.middle_strict r H D a q h.toHyp6 (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : r ≤ 1/3
  · exact variance_strict r H D a q h (le_of_lt (lt_of_not_ge h2)) h3
  · exact continuous_strict r H D a q h (le_of_lt (lt_of_not_ge h3)) hru

/-- The exceptional n23 low interval uses actual mass and plateau index,
    with the quartic and all three q/r splits retained. -/
theorem n23_low_strict (j r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) :
    0 < gap 138 j th23 r H D a q := by
  let z := H+r-D
  let T0 := a+2*r*H+r^2+q
  let x := (j-1)*r
  have hx : 0 ≤ x := mul_nonneg (by linarith only [hj]) h.r_nonneg
  have hid : gap 138 j th23 r H D a q =
      C z-T0+th23*x^2+x*(2*th23*(z+K)-r) := by
    dsimp [gap,energy,mass,W,C,K,th23,z,T0,x]
    ring
  have hm := h.mass
  dsimp only [slack] at hm
  have hqmax := q_le_29_8 r H D a q h
  by_cases hq : q ≤ 9/20
  · let d := Real.sqrt (20*q)
    let t := Real.sqrt (a+2*r*H+r^2)
    let u := 2-q/2
    have hd : 0 ≤ d := Real.sqrt_nonneg _
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have hd2 : d^2=20*q := Real.sq_sqrt (mul_nonneg (by norm_num) h.q_nonneg)
    have ht2 : t^2=a+2*r*H+r^2 := Real.sq_sqrt
      (add_nonneg (add_nonneg h.a_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) h.r_nonneg) h.H_nonneg)) (sq_nonneg r))
    have hd3 : d ≤ 3 := by nlinarith only [hd,hd2,hq]
    have hDd : D ≤ d := by nlinarith only [h.tail_cauchy,hd2,hd,h.D_nonneg]
    have hu : 71/40 ≤ u := by dsimp [u]; linarith only [hq]
    have hcouple : 14*r^2 ≤ u^2-t^2 := by dsimp only [u]; nlinarith only [h.coupled,ht2]
    have htu : t ≤ u := by nlinarith only [ht,hu,hcouple,sq_nonneg r]
    have htH : t ≤ H+r := by
      nlinarith only [ht,ht2,h.head_sq,h.H_nonneg,h.r_nonneg]
    have hz : t-d ≤ z := by dsimp [z]; linarith only [htH,hDd]
    have hz3 : -3 ≤ z := by linarith only [hz,ht,hd3]
    have hzC : C (t-d) ≤ C z := by
      have hp := mul_nonneg (show 0 ≤ z-(t-d) by linarith only [hz])
        (show 0 ≤ z+(t-d)+2*K by dsimp [K]; linarith only [hz3,ht,hd3])
      dsimp [C,th23] at *
      nlinarith only [hp]
    have hqeq : q=d^2/20 := by linarith only [hd2]
    have hFid : F d=C (u-d)-u^2-q := by
      dsimp only [u,C,K,th23,F]
      rw [hqeq]
      ring
    have hcoeff : 0 ≤ (1-th23-13/14)*(u+t)-2*th23*(K-d) := by
      norm_num only [th23,K]
      linarith only [hu,ht,hd]
    have hprod := mul_nonneg (sub_nonneg.mpr htu) hcoeff
    have hF := quartic_lower d hd hd3
    have hstrong : 1/25+13*r^2 ≤ C z-T0 := by
      dsimp only [C,th23] at hFid hzC hprod ⊢
      dsimp only [T0] at *
      nlinarith only [hFid,hzC,hprod,hcouple,ht2,hF]
    by_cases ht1 : 1 ≤ t
    · have hz2 : -2 ≤ z := by linarith only [hz,ht1,hd3]
      have hlin : 4438/162409-r ≤ 2*th23*(z+K)-r := by
        norm_num only [th23,K]
        linarith only [hz2]
      have hp := mul_nonneg hx (sub_nonneg.mpr hlin)
      have hs := sq_nonneg (x-(r-4438/162409)/(2*th23))
      have hg := quadratic_lower (13-1/(4*th23))
        ((4438/162409)/(2*th23)) (1/25-(4438/162409)^2/(4*th23))
        0 (1/12) r (1/100) (by norm_num [th23]) h.r_nonneg hr
        (by norm_num [th23]) (by norm_num [th23])
      norm_num only [th23] at *
      nlinarith only [hid,hstrong,hp,hs,hg]
    · have ht1 : t ≤ 1 := le_of_lt (lt_of_not_ge ht1)
      have hC : K ≤ C z := by dsimp [C,th23]; nlinarith only [sq_nonneg (z+K)]
      have hbase : 2 ≤ C z-T0 := by
        dsimp only [T0] at *
        norm_num only [K] at *
        nlinarith only [hC,ht1,ht2,hq,ht]
      have hlin : -(1/12) ≤ 2*th23*(z+K)-r := by
        norm_num only [th23,K]
        linarith only [hz3,hr]
      have hp := mul_nonneg hx (sub_nonneg.mpr hlin)
      have hs := sq_nonneg (x-1/(24*th23))
      norm_num only [th23] at *
      nlinarith only [hid,hbase,hp,hs]
  · have hqc : 9/20 ≤ q := le_of_lt (lt_of_not_ge hq)
    let phi := q-q^2/4
    have hT0 : T0 ≤ 4-phi-14*r^2 := by dsimp [T0,phi]; nlinarith only [h.coupled]
    have hz : 16*r-6 ≤ z := by dsimp [z]; linarith only [hm,h.H_nonneg]
    have hp := mul_nonneg h.r_nonneg (show 0 ≤ z-(16*r-6) by linarith only [hz])
    have hs := sq_nonneg (x+z+K-r/(2*th23))
    have hgap : K-4+phi+r*(K-6)+(30-1/(4*th23))*r^2 ≤
        gap 138 j th23 r H D a q := by
      dsimp only [C] at hid
      norm_num only [th23] at *
      nlinarith only [hid,hT0,hp,hs]
    by_cases hr1 : r ≤ 1/20
    · have hphi := quadratic_lower (-1/4) 1 0 (9/20) (29/8) q (87/256)
        (by norm_num) hqc hqmax (by norm_num) (by norm_num)
      have hg := quadratic_lower (30-1/(4*th23)) (K-6) (K-4+87/256)
        0 (1/20) r (1/100) (by norm_num [th23]) h.r_nonneg hr1
        (by norm_num [K,th23]) (by norm_num [K,th23])
      dsimp [phi] at *
      linarith only [hgap,hphi,hg]
    · have hr1 : 1/20 ≤ r := le_of_lt (lt_of_not_ge hr1)
      have hqu : q ≤ 4-10*r := h.tail_cap.trans
        (max_le (by linarith only [hr]) (by linarith only [hm,h.H_nonneg]))
      have hphiend := quadratic_lower (-25) 10 0 (1/20) (1/12) r (639/1600)
        (by norm_num) hr1 hr (by norm_num) (by norm_num)
      have hphi := quadratic_lower (-1/4) 1 0 (9/20) (4-10*r) q (639/1600)
        (by norm_num) hqc hqu (by norm_num) (by nlinarith only [hphiend])
      have hg := quadratic_lower (30-1/(4*th23)) (K-6) (K-4+639/1600)
        (1/20) (1/12) r (1/100) (by norm_num [th23]) hr1 hr
        (by norm_num [K,th23]) (by norm_num [K,th23])
      dsimp [phi] at *
      linarith only [hgap,hphi,hg]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterScalar
