/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementScaleEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementScaleEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual square-displacement fourth-order errors decay algebraically and exponentially in q. -/

/- The finite FourthEnvelope logarithmic data are shared below.
The shared proof uses FourthCoefficient.quartic_tail,
Envelope.coefficient_bounds, ThresholdBracket.state_data, and the existing
Reg UpperEnvelope.choose_grow_diagonal supplier. New/shared helper audit binding
and the full source binding remain unfinished under issue 25856.
The only new finite-log estimate is the shrinking positive pointwise constant;
the finite products, moments and global negative cubic are shared suppliers. -/
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
open BajnokBeattySquareDisplacementSingleCrossing
open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapGaussianSecondOrder

private def C (v : ℝ) : ℝ := 2*(v+1)/(3*(v-1)^2)
private def E (v : ℝ) : ℝ := 4/(3*(v-1)^2)
private def B (v : ℝ) : ℝ := 16*(v^2+v+1)/(15*(v-1)^4)
private def U (v : ℝ) : ℝ := 16*(v+1)/(3*(v-1)^4)
private def V (v : ℝ) : ℝ := 112/(15*(v-1)^4)

/-- Rational estimates retain the powers of nu-1 rather than taking a uniform
maximum at nu=9. Every coefficient here is explicit. -/
private theorem scaled_coefficients {v s : ℝ} (hv : 9 ≤ v)
    (hs : 0 ≤ s) (hs7 : s ≤ 5/7) :
    let N := v-1
    let C := 2*(v+1)/(3*N^2)
    let E := 4/(3*N^2)
    let B := 16*(v^2+v+1)/(15*N^4)
    let U := 16*(v+1)/(3*N^4)
    let V := 112/(15*N^4)
    0 ≤ C*s^3 ∧ C*s^3 ≤ 625/(2058*N) ∧ C*s^3 ≤ 1/(3*N) ∧
      |B*s^5-E*s^3| ≤ 1/(2*N^2) ∧
      0 ≤ U ∧ U ≤ 20/(3*N^3) ∧ 0 ≤ V ∧ V ≤ 14/(15*N^3) := by
  dsimp only
  let N := v-1
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hv]
  have hN : 0 < N := by linarith only [hN8]
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hz : 0 ≤ v-9 := sub_nonneg.mpr hv
  have hC : 2*(v+1)/(3*N^2) ≤ 5/(6*N) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3*N^2) (by positivity : 0 < 6*N)).2
    have hh := mul_nonneg hN.le (sub_nonneg.mpr hv)
    dsimp [N] at hh ⊢
    nlinarith only [hh]
  have hB : 16*(v^2+v+1)/(15*N^4) ≤ 91/(60*N^2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 15*N^4) (by positivity : 0 < 60*N^2)).2
    have hh : 0 ≤ N^2*((v-9)*(9*v-1)) := by
      have : 0 ≤ 9*v-1 := by linarith only [hv]
      positivity
    dsimp [N] at hh ⊢
    nlinarith only [hh]
  have hU : 16*(v+1)/(3*N^4) ≤ 20/(3*N^3) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3*N^4) (by positivity : 0 < 3*N^3)).2
    have hh := mul_nonneg (pow_nonneg hN.le 3) (sub_nonneg.mpr hv)
    dsimp [N] at hh ⊢
    nlinarith only [hh]
  have hV : 112/(15*N^4) ≤ 14/(15*N^3) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 15*N^4) (by positivity : 0 < 15*N^3)).2
    have hh := mul_nonneg (pow_nonneg hN.le 3) (sub_nonneg.mpr hv)
    dsimp [N] at hh ⊢
    nlinarith only [hh]
  have hs3 := pow_le_pow_left₀ hs hs7 3
  have hs5 := pow_le_pow_left₀ hs hs7 5
  have ha : (2*(v+1)/(3*N^2))*s^3 ≤ 625/(2058*N) := by
    have hh := mul_le_mul hC hs3 (pow_nonneg hs 3) (by positivity : 0 ≤ 5/(6*N))
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have ha' : 625/(2058*N) ≤ 1/(3*N) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2058*N) (by positivity : 0 < 3*N)).2
    nlinarith only [hN.le]
  have hb : (16*(v^2+v+1)/(15*N^4))*s^5 ≤ 1/(2*N^2) := by
    have hh := mul_le_mul hB hs5 (pow_nonneg hs 5) (by positivity : 0 ≤ 91/(60*N^2))
    have hn : (91/(60*N^2))*(5/7)^5 ≤ 1/(2*N^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*N^2)).2
      field_simp [hN.ne']
      norm_num
    exact hh.trans hn
  have he : (4/(3*N^2))*s^3 ≤ 1/(2*N^2) := by
    have hh := mul_le_mul_of_nonneg_left hs3 (show 0 ≤ 4/(3*N^2) by positivity)
    have hn : (4/(3*N^2))*(5/7)^3 ≤ 1/(2*N^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*N^2)).2
      field_simp [hN.ne']
      norm_num
    exact hh.trans hn
  refine ⟨by positivity,ha,ha.trans ha',?_,by positivity,hU,by positivity,hV⟩
  have hp : 0 ≤ (16*(v^2+v+1)/(15*N^4))*s^5 := by positivity
  have hn : 0 ≤ (4/(3*N^2))*s^3 := by positivity
  exact abs_le.mpr ⟨by linarith only [he,hp],by linarith only [hb,hn]⟩

/-- The positive tail coefficient shrinks quadratically in N before the cubic
moment contributes its further inverse power of N. -/
private theorem positive_tail_coefficient {Q a : ℝ} (hQ3 : 3 ≤ Q)
    (ha0 : 0 ≤ a) (ha : a ≤ 625/(2058*(Q^2-1))) :
    let N := Q^2-1
    let k := 10*Q/(7*N)
    3*k^4/(1-k^2/25)*a ≤
      (3*(225/98:ℝ)^2*(784/775)*(625/2058))/N^3 := by
  dsimp only
  let N := Q^2-1
  let k := 10*Q/(7*N)
  change a ≤ 625/(2058*N) at ha
  change 3*k^4/(1-k^2/25)*a ≤
    (3*(225/98:ℝ)^2*(784/775)*(625/2058))/N^3
  have hQ : 0 ≤ Q := by linarith only [hQ3]
  have hQsq : 9 ≤ Q^2 := by nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hQsq]
  have hN : 0 < N := by linarith only [hN8]
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk2 : k^2 ≤ 225/(98*N) := by
    dsimp only [k]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : 0 < (7*N)^2) (by positivity : 0 < 98*N)).2
    have hh := mul_nonneg hN.le (show 0 ≤ Q^2-9 by linarith only [hQsq])
    dsimp [N] at hh ⊢
    nlinarith only [hh]
  have hkcap : k^2 ≤ 225/784 := by
    have hh : 225/(98*N) ≤ 225/784 := by
      apply (div_le_iff₀ (by positivity : 0 < 98*N)).2
      linarith only [hN8]
    exact hk2.trans hh
  have hd : 0 < 1-k^2/25 := by linarith only [hkcap]
  have hinv : 1/(1-k^2/25) ≤ 784/775 := by
    apply (div_le_iff₀ hd).2
    linarith only [hkcap]
  have hk4 : k^4 ≤ (225/98:ℝ)^2/N^2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg k) hk2 2
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hprod := mul_le_mul hk4 hinv (by positivity : 0 ≤ 1/(1-k^2/25))
    (by positivity : 0 ≤ (225/98:ℝ)^2/N^2)
  have hcoef : 3*k^4/(1-k^2/25) ≤ (3*(225/98:ℝ)^2*(784/775))/N^2 := by
    have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 3)
    convert hh using 1 <;> ring
  have hh := mul_le_mul hcoef ha ha0 (by positivity :
    0 ≤ (3*(225/98:ℝ)^2*(784/775))/N^2)
  convert hh using 1 <;> field_simp [hN.ne'] <;> ring

/-- This is arithmetic on the single shared finite-log residual, with no second
finite product or AP implementation. -/
private theorem positive_residual {e Q s U V rx Tx : ℝ}
    (he : 0 ≤ e) (he25 : e ≤ 1/25) (hQ3 : 3 ≤ Q)
    (hs : 0 ≤ s) (hs7 : s ≤ 5/7)
    (hU0 : 0 ≤ U) (hU : U ≤ 20/(3*(Q^2-1)^3))
    (hV0 : 0 ≤ V) (hV : V ≤ 14/(15*(Q^2-1)^3))
    (hTx0 : 0 ≤ Tx)
    (hTx : Tx ≤ (3*(225/98:ℝ)^2*(784/775)*(625/2058))*e^3/(Q^2-1)^3)
    (hrx : rx = -U*s^5*e^3+V*s^5*e^4+Tx) :
    |rx| ≤ 7*e^3/(Q^2-1)^3 := by
  let N := Q^2-1
  change U ≤ 20/(3*N^3) at hU
  change V ≤ 14/(15*N^3) at hV
  change Tx ≤ (3*(225/98:ℝ)^2*(784/775)*(625/2058))*e^3/N^3 at hTx
  have hQsq : 9 ≤ Q^2 := by nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hN : 0 < N := by dsimp [N]; linarith only [hQsq]
  have hs5 := pow_le_pow_left₀ hs hs7 5
  have he4 : e^4 ≤ e^3/25 := by
    have hh := mul_le_mul_of_nonneg_right he25 (pow_nonneg he 3)
    nlinarith only [hh]
  have h₁ := mul_le_mul hU hs5 (pow_nonneg hs 5) (by positivity : 0 ≤ 20/(3*N^3))
  have h₂ := mul_le_mul hV hs5 (pow_nonneg hs 5) (by positivity : 0 ≤ 14/(15*N^3))
  have hUp : U*s^5*e^3 ≤ ((20/3:ℝ)*(5/7)^5)*e^3/N^3 := by
    have hh := mul_le_mul_of_nonneg_right h₁ (pow_nonneg he 3)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hVp : V*s^5*e^4 ≤ ((14/15:ℝ)*(5/7)^5/25)*e^3/N^3 := by
    have hh := mul_le_mul h₂ he4 (pow_nonneg he 4)
      (by positivity : 0 ≤ (14/(15*N^3))*(5/7)^5)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hnum : (20/3:ℝ)*(5/7)^5+(14/15)*(5/7)^5/25+
      3*(225/98)^2*(784/775)*(625/2058) = 3180700/521017 := by norm_num
  have htotal : U*s^5*e^3+V*s^5*e^4+Tx ≤ 7*e^3/N^3 := by
    have hh := add_le_add (add_le_add hUp hVp) hTx
    have ht : 0 ≤ e^3/N^3 := by positivity
    calc
      _ ≤ _ := hh
      _ = (3180700/521017)*(e^3/N^3) := by ring
      _ ≤ 7*(e^3/N^3) := mul_le_mul_of_nonneg_right (by norm_num) ht
      _ = 7*e^3/N^3 := by ring
  have hUp0 : 0 ≤ U*s^5*e^3 := by positivity
  have hVp0 : 0 ≤ V*s^5*e^4 := by positivity
  rw [hrx]
  apply abs_le.mpr
  constructor <;> linarith only [htotal,hUp0,hVp0,hTx0]

/-- Normalize by e/N. The negative block is not part of this bounded positive
Taylor argument; it is supplied by the existing global nonlinear theorem. -/
private theorem positive_nonlinear {w a b rx dx : ℝ}
    (hw : 0 ≤ w) (hw200 : w ≤ 1/200)
    (ha0 : 0 ≤ a) (ha : a ≤ 1/3) (hb : |b| ≤ 1/2)
    (hrx : |rx| ≤ 7*w^3) (hdx0 : 0 ≤ dx)
    (hdx : dx = a*w+b*w^2+rx) :
    |Real.exp dx-1-a*w-(b+a^2/2)*w^2| ≤
      (7+21/100+343/8000)*w^3 := by
  have hw2 : w^2 ≤ w/200 := by
    have hh := mul_le_mul_of_nonneg_right hw200 hw
    nlinarith only [hh]
  have hw3 : w^3 ≤ w^2/200 := by
    have hh := mul_le_mul_of_nonneg_right hw200 (sq_nonneg w)
    nlinarith only [hh]
  have herr : |dx-a*w| ≤ (3/5)*w^2 := by
    have hh : |dx-a*w| ≤ |b| * w^2+|rx| := by
      rw [hdx,show a*w+b*w^2+rx-a*w = b*w^2+rx by ring]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_of_nonneg (sq_nonneg w)])
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg w)
    nlinarith only [hh,hm,hrx,hw3,sq_nonneg w]
  have haw : a*w ≤ w/3 := by
    have hh := mul_le_mul_of_nonneg_right ha hw
    linarith only [hh]
  have hdxhi : dx ≤ (7/20)*w := by
    have hh := (abs_le.mp herr).2
    nlinarith only [hh,haw,hw2,hw]
  have hsum : dx+a*w ≤ (7/10)*w := by linarith only [hdxhi,haw,hw]
  have hsq : |dx^2-(a*w)^2| ≤ (21/50)*w^3 := by
    rw [show dx^2-(a*w)^2 = (dx-a*w)*(dx+a*w) by ring,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ dx+a*w)]
    have hh := mul_le_mul herr hsum (by positivity : 0 ≤ dx+a*w)
      (by positivity : 0 ≤ (3/5)*w^2)
    convert hh using 1 <;> ring
  have hcub : dx^3 ≤ (343/8000)*w^3 := by
    have hh := pow_le_pow_left₀ hdx0 hdxhi 3
    convert hh using 1 <;> ring
  have hTaylor := BajnokBeattySquareDisplacementFourthEnvelope.positive_cubic hdx0
    (show dx ≤ 1 by linarith only [hdxhi,hw200])
  have hid : Real.exp dx-1-a*w-(b+a^2/2)*w^2 =
      (Real.exp dx-1-dx-dx^2/2)+rx+(dx^2-(a*w)^2)/2 := by rw [hdx]; ring
  have hh := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hTaylor hrx))
    (show |(dx^2-(a*w)^2)/2| ≤ ((21/50)*w^3)/2 by
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact div_le_div_of_nonneg_right hsq (by norm_num)))
  rw [← hid] at hh
  nlinarith only [hh,hcub]

private theorem damped_blocks {P v s L M rx ry : ℝ}
    (hP5 : 5 ≤ P) (hv : 9 ≤ v) (hslo : 2/3 ≤ s) (hshi : s ≤ 5/7)
    (hL0 : 0 ≤ L-s) (hM0 : 0 ≤ M-v*s)
    (hL : L-s = C v*s^3/P^2+(B v*s^5-E v*s^3)/P^4+rx)
    (hM : M-v*s = v^2*C v*s^3/P^2+
      (v^3*B v*s^5-v*E v*s^3)/P^4+ry)
    (hrxold : |rx| ≤ 1/(50*P^6)) (hry : |ry| ≤ 8*v/P^6)
    (hrx : |rx| ≤ 7/(P^6*(v-1)^3)) :
    |Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+
        B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/P^4| ≤
      (17/(v-1)^3+(8*v+27*v^2/100+4*v^3/375)*
        Real.exp (-2*v/3))/P^6 := by
  let N := v-1
  let e := 1/P^2
  let a := C v*s^3
  let b := B v*s^5-E v*s^3
  let A := v^2*C v*s^3
  let BB := v^3*B v*s^5-v*E v*s^3
  have hP : 0 < P := by linarith only [hP5]
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hv]
  have hN : 0 < N := by linarith only [hN8]
  have he : 0 < e := by dsimp [e]; positivity
  have he25 : e ≤ 1/25 := by
    apply (div_le_div_iff₀ (by positivity : 0 < P^2) (by norm_num : (0:ℝ)<25)).2
    nlinarith only [hP5,sq_nonneg (P-5)]
  have he2 : e^2 = 1/P^4 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have he3 : e^3 = 1/P^6 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have hs0 : 0 ≤ s := by linarith only [hslo]
  obtain ⟨ha0,ha,hb,hA0,hA,hB⟩ :=
    BajnokBeattySquareDisplacementFourthEnvelope.coefficient_sizes hv hs0 hshi
  change 0 ≤ a at ha0
  change a ≤ 1/20 at ha
  change |b| ≤ 1/50 at hb
  change 0 ≤ A at hA0
  change A ≤ (7/20)*v at hA
  change |BB| ≤ (2/5)*v at hB
  obtain ⟨_,_,hascaled,hbscaled,_,_,_,_⟩ := scaled_coefficients hv hs0 hshi
  change a ≤ 1/(3*N) at hascaled
  change |b| ≤ 1/(2*N^2) at hbscaled
  have hrxold' : |rx| ≤ e^3/50 := by rw [he3]; convert hrxold using 1 <;> ring
  have hry' : |ry| ≤ 8*v*e^3 := by rw [he3]; convert hry using 1 <;> ring
  have hL' : L-s = a*e+b*e^2+rx := by
    rw [he2]; convert hL using 1 <;> dsimp [a,b,e] <;> ring
  have hM' : M-v*s = A*e+BB*e^2+ry := by
    rw [he2]; convert hM using 1 <;> dsimp [A,BB,e] <;> ring
  have hy := (BajnokBeattySquareDisplacementFourthEnvelope.nonlinear_blocks
    he he25 hv ha0 ha hb hrxold' hA0 hA hB hry' hL0 hM0 hL' hM').2
  let w := e/N
  let aa := a*N
  let bb := b*N^2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw200 : w ≤ 1/200 := by
    apply (div_le_iff₀ hN).2
    nlinarith only [he25,hN8]
  have haa0 : 0 ≤ aa := by dsimp [aa]; positivity
  have haa : aa ≤ 1/3 := by
    have hh := mul_le_mul_of_nonneg_right hascaled hN.le
    dsimp only [aa]
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hbb : |bb| ≤ 1/2 := by
    dsimp only [bb]
    rw [abs_mul,abs_of_nonneg (sq_nonneg N)]
    have hh := mul_le_mul_of_nonneg_right hbscaled (sq_nonneg N)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hrxscaled : |rx| ≤ 7*w^3 := by
    convert hrx using 1 <;> dsimp [w,e,N] <;> field_simp [hP.ne',hN.ne'] <;> ring
  have hLscaled : L-s = aa*w+bb*w^2+rx := by
    rw [hL']
    dsimp [aa,bb,w]
    field_simp [hN.ne'] <;> ring
  have hx := positive_nonlinear hw hw200 haa0 haa hbb hrxscaled hL0 hLscaled
  have hfactorX : Real.exp L = Real.exp s*Real.exp (L-s) := by
    rw [← Real.exp_add]; congr 1; ring
  have hfactorY : Real.exp (-M) = Real.exp (-v*s)*Real.exp (-(M-v*s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX : |Real.exp L-Real.exp s*(1+a*e+(b+a^2/2)*e^2)| ≤ 17*e^3/N^3 := by
    have hx' : |Real.exp (L-s)-1-a*e-(b+a^2/2)*e^2| ≤
        (7+21/100+343/8000)*e^3/N^3 := by
      have hlin : aa*w = a*e := by
        dsimp [aa,w]; field_simp [hN.ne'] <;> ring
      have hquad : (bb+aa^2/2)*w^2 = (b+a^2/2)*e^2 := by
        dsimp [aa,bb,w]; field_simp [hN.ne'] <;> ring
      rw [hlin,hquad] at hx
      simpa only [w,div_pow,mul_div_assoc] using hx
    have hh := mul_le_mul_of_nonneg_left hx' (Real.exp_pos s).le
    have hexp : Real.exp s ≤ 9/4 :=
      (Real.exp_le_exp.mpr (by linarith only [hshi] : s ≤ 3/4)).trans exp_three_quarters_lt.le
    have hm := mul_le_mul_of_nonneg_right hexp
      (show 0 ≤ (7+21/100+343/8000)*e^3/N^3 by positivity)
    rw [hfactorX,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos s)]
    have hid : Real.exp (L-s)-(1+a*e+(b+a^2/2)*e^2) =
        Real.exp (L-s)-1-a*e-(b+a^2/2)*e^2 := by ring
    rw [hid]
    have hnum : (9/4:ℝ)*(7+21/100+343/8000) = 522207/32000 := by norm_num
    have ht : 0 ≤ e^3/N^3 := by positivity
    calc
      _ ≤ (9/4)*((7+21/100+343/8000)*e^3/N^3) := hh.trans hm
      _ = (522207/32000)*(e^3/N^3) := by ring
      _ ≤ 17*(e^3/N^3) := mul_le_mul_of_nonneg_right (by norm_num) ht
      _ = 17*e^3/N^3 := by ring
  have hY : |Real.exp (-M)-Real.exp (-v*s)*(1-A*e+(-BB+A^2/2)*e^2)| ≤
      (8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3)*e^3 := by
    have hh := mul_le_mul_of_nonneg_left hy (Real.exp_pos (-v*s)).le
    have hexp : Real.exp (-v*s) ≤ Real.exp (-2*v/3) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hv0 (sub_nonneg.mpr hslo)]
    have hm := mul_le_mul_of_nonneg_right hexp
      (show 0 ≤ (8*v+(27/100)*v^2+(4/375)*v^3)*e^3 by positivity)
    rw [hfactorY,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos (-v*s))]
    have hid : Real.exp (-(M-v*s))-(1-A*e+(-BB+A^2/2)*e^2) =
        Real.exp (-(M-v*s))-1+A*e-(-BB+A^2/2)*e^2 := by ring
    rw [hid]
    nlinarith only [hh,hm]
  have hid : Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+
        B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/P^4 =
      (Real.exp L-Real.exp s*(1+a*e+(b+a^2/2)*e^2))+
      (Real.exp (-M)-Real.exp (-v*s)*(1-A*e+(-BB+A^2/2)*e^2)) := by
    dsimp [a,b,A,BB,e]; ring
  rw [hid]
  have hh := (abs_add_le _ _).trans (add_le_add hX hY)
  rw [he3] at hh
  convert hh using 1 <;> dsimp [N] <;> ring

/-- The exact shared finite log data supplies both the old residual needed by the
negative nonlinear inference and the shrinking positive residual. -/
private theorem finite_binomial (p q n a r : ℕ) (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (hr : 2*r = (q-1)*p) (hna : n+p = 2*a) (hfit : a+(q+1)*r ≤ n) :
    let P : ℝ := p
    let Q : ℝ := q
    let s : ℝ := (Q^2-1)*P^2/(2*((n : ℝ)+1))
    let v : ℝ := Q^2
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
    |((Nat.choose n a : ℝ)+Nat.choose n (a+(q+1)*r))/(Nat.choose n (a+r) : ℝ)-
      (Real.exp s+Real.exp (-v*s))-C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/P^4| ≤
      (17/(v-1)^3+(8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3))/P^6 := by
  dsimp only
  intro hslo hshi
  let P : ℝ := p
  let Q : ℝ := q
  let v := Q^2
  let N := v-1
  let s := N*P^2/(2*((n : ℝ)+1))
  let e := 1/P^2
  change (2/3:ℝ) ≤ s at hslo
  change s ≤ 5/7 at hshi
  have hP5 : 5 ≤ P := by change (5:ℝ) ≤ (p:ℝ); exact_mod_cast hp5
  have hQ3 : 3 ≤ Q := by change (3:ℝ) ≤ (q:ℝ); exact_mod_cast hq3
  have hP : 0 < P := by linarith only [hP5]
  have hv : 9 ≤ v := by dsimp [v]; nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hN : 0 < N := by dsimp [N]; linarith only [hv]
  have hs0 : 0 ≤ s := by linarith only [hslo]
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he25 : e ≤ 1/25 := by
    apply (div_le_div_iff₀ (by positivity : 0 < P^2) (by norm_num : (0:ℝ)<25)).2
    nlinarith only [hP5,sq_nonneg (P-5)]
  have he3 : e^3 = 1/P^6 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  obtain ⟨L,M,rx,ry,Tx,hexpL,hexpM,hL0,hM0,hL,hM,hrxold,hry,hrxeq,hTx0,hTx⟩ :=
    BajnokBeattySquareDisplacementFourthEnvelope.finite_log_data p q n a r hp5 hq3 hr hna hfit hslo hshi
  obtain ⟨ha0,ha,_,_,hU0,hU,hV0,hV⟩ := scaled_coefficients hv hs0 hshi
  change 0 ≤ C v*s^3 at ha0
  change C v*s^3 ≤ 625/(2058*N) at ha
  change 0 ≤ U v at hU0
  change U v ≤ 20/(3*N^3) at hU
  change 0 ≤ V v at hV0
  change V v ≤ 14/(15*N^3) at hV
  have htail := positive_tail_coefficient hQ3 ha0 ha
  have hTxfine : Tx ≤ (3*(225/98:ℝ)^2*(784/775)*(625/2058))*e^3/N^3 := by
    change Tx ≤ 3*(10*Q/(7*N))^4/(1-(10*Q/(7*N))^2/25)*(C v*s^3)*e^3 at hTx
    change 3*(10*Q/(7*N))^4/(1-(10*Q/(7*N))^2/25)*(C v*s^3) ≤
      (3*(225/98:ℝ)^2*(784/775)*(625/2058))/N^3 at htail
    have hh := mul_le_mul_of_nonneg_right htail (pow_nonneg he 3)
    exact hTx.trans (hh.trans_eq (by ring))
  have hrxfine := positive_residual he he25 hQ3 hs0 hshi hU0 hU hV0 hV hTx0 hTxfine hrxeq
  have hrxfine' : |rx| ≤ 7/(P^6*(v-1)^3) := by
    rw [he3] at hrxfine
    convert hrxfine using 1 <;> dsimp [N,v] <;> field_simp [hP.ne',hN.ne'] <;> ring
  have hh := damped_blocks hP5 hv hslo hshi hL0 hM0 hL hM hrxold hry hrxfine'
  rw [hexpL,hexpM,← add_div] at hh
  exact hh

/-- A scale-sensitive fourth-order envelope for the complete quotient return
counts over the full signed odd domain, including all odd composites. -/
theorem actual_square_displacement_scale_envelope (p q : ℤ) (t : ℕ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : ((q+1)/2).toNat ≤ t) :
    let nReal : ℝ := (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1)
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*(nReal+1))
    let nu : ℝ := (q : ℝ)^2
    let C : ℝ := 2*(nu+1)/(3*(nu-1)^2)
    let E : ℝ := 4/(3*(nu-1)^2)
    let Bcoef : ℝ := 16*(nu^2+nu+1)/(15*(nu-1)^4)
    let G : ℝ := Real.exp s+Real.exp (-nu*s)
    let H : ℝ := C*s^3*(Real.exp s-nu^2*Real.exp (-nu*s))
    let K : ℝ := -E*s^3*(Real.exp s-nu*Real.exp (-nu*s))+
      Bcoef*s^5*(Real.exp s-nu^3*Real.exp (-nu*s))+
      (C^2/2)*s^6*(Real.exp s+nu^4*Real.exp (-nu*s))
    let N : ℝ := nu-1
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-
        G-H/(p : ℝ)^2-K/(p : ℝ)^4| ≤
        (17/N^3+(8*nu+27*nu^2/100+4*nu^3/375)*Real.exp (-2*nu/3))/(p : ℝ)^6 := by
  obtain ⟨n,a,r,hN,hna,hr,hfit,hWa,hWq⟩ :=
    BajnokBeattySquareDisplacementThresholdBracket.state_data p q t hp5 hpo hq3 hqo ht
  have hPn : (p.toNat : ℝ) = (p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ p by omega)
  have hQn : (q.toNat : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  have hNR : (n : ℝ) = (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1) := by exact_mod_cast hN
  have hBr : a+r ≤ n := by
    have h : r ≤ (q.toNat+1)*r := by rw [add_mul,one_mul]; omega
    omega
  have hBpos : (0:ℝ) < (Nat.choose n (a+r) : ℝ) := by exact_mod_cast Nat.choose_pos hBr
  have hratio : 2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ) =
      ((Nat.choose n a : ℝ)+Nat.choose n (a+(q.toNat+1)*r))/(Nat.choose n (a+r) : ℝ) := by
    rw [hWa,hWq]; push_cast; field_simp [hBpos.ne'] <;> ring
  have hh := finite_binomial p.toNat q.toNat n a r (by omega) (by omega) hr hna hfit
  dsimp only at hh ⊢
  rw [hPn,hQn,hNR] at hh
  rw [hratio]
  simpa only [C,E,B] using hh

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
