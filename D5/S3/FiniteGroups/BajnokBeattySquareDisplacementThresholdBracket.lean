/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform finite square-displacement counts locate the full unique threshold at the corrected center. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
open Set Finset
open D5.S0.Tower.DBonacci.PerronRoot
open BajnokBeattySquareDisplacementSingleCrossing BajnokBeattySquareDisplacementEnvelope
open BajnokBeattySquareDisplacementCorrection BajnokBeattySquareDisplacementProfile
open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapGaussianSecondOrder

private def G (v s : ℝ) : ℝ := Real.exp s+Real.exp (-v*s)
private def H (v s : ℝ) : ℝ :=
  (2*(v+1)/(3*(v-1)^2))*s^3*(Real.exp s-v^2*Real.exp (-v*s))

-- All fields below are supplied from the original Perron/coefficient theorems.
-- No field is a count, sign, threshold or desired rounding assumption.
private structure Model where
  q : ℝ
  sigma : ℝ
  d : ℝ
  q3 : 3 ≤ q
  sigmaLo : 200/291 < sigma
  sigmaHi : sigma < 7/10
  d0 : 0 < d
  dHi : d < 7/(48*q)
  root : G (q^2) sigma = 2
  slope : ∀ a b : ℝ, 2/3 ≤ a → a ≤ b →
    (161/90)*(b-a) ≤ G (q^2) b-G (q^2) a
  cancellation : (Real.exp sigma-q^2*Real.exp (-q^2*sigma))*
    (sigma*d/(((q^2-1)/(4*q))/sigma)) = H (q^2) sigma

private def kap (M : Model) : ℝ := (M.q^2-1)/(4*M.q)
private def alpha (M : Model) : ℝ := kap M/M.sigma
private def k (M : Model) : ℝ := M.sigma*M.d/alpha M
private def g (M : Model) : ℝ := Real.exp M.sigma-M.q^2*Real.exp (-M.q^2*M.sigma)
private def F (M : Model) (P s : ℝ) : ℝ := G (M.q^2) s+H (M.q^2) s/P^2
private def parameter (M : Model) (P v : ℝ) : ℝ := kap M*P/v
private def vc (M : Model) (P : ℝ) : ℝ := alpha M*P+M.d/P
private def eps (M : Model) (P : ℝ) : ℝ := M.q/(10*P^3)
private def center (M : Model) (P : ℝ) : ℝ :=
  alpha M*P+1/(2*M.q)+(M.d-1/(2*M.q))/P
private def centered (q P t : ℝ) : ℝ := t-1/(2*q)+1/(2*q*P)

theorem H_secant {v a b : ℝ} (hv : 9 ≤ v)
    (ha : a ∈ Icc (2/3 : ℝ) (5/7)) (hb : b ∈ Icc (2/3 : ℝ) (5/7))
    (hab : a ≤ b) : 0 ≤ H v b-H v a ∧ H v b-H v a ≤ b-a := by
  let C : ℝ := 2*(v+1)/(3*(v-1)^2)
  have hv0 : 0 < v := by linarith
  have hvm : 0 < v-1 := by linarith
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 5/48 := by
    apply (div_le_iff₀ (show 0 < 3*(v-1)^2 by positivity)).2
    nlinarith [mul_nonneg (show 0 ≤ v-9 by linarith) (show 0 ≤ 5*v+3 by linarith)]
  have hd (s : ℝ) : HasDerivAt (H v)
      (C*s^2*((s+3)*Real.exp s+v^2*(v*s-3)*Real.exp (-v*s))) s := by
    have hl := (hasDerivAt_const_mul (x := s) (-v)).exp
    convert ((((hasDerivAt_id s).pow 3).const_mul C).mul
      ((Real.hasDerivAt_exp s).sub (hl.const_mul (v^2)))) using 1 <;>
      (try funext x) <;> (try simp [H,C,Pi.mul_apply,Pi.sub_apply]) <;> ring
  have hbound (s : ℝ) (hs : s ∈ Icc (2/3 : ℝ) (5/7)) :
      0 ≤ deriv (H v) s ∧ deriv (H v) s ≤ 1 := by
    rw [(hd s).deriv]
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have ht := real_rational_tail_on_ray hv hs.1
    have htail3 : v^3*Real.exp (-v*s) ≤ 81/10 := by
      have ht' := mul_lt_mul_of_pos_left ht.2.1 hv0
      have hid : v*(243/(2*v*(v+6))) = 243/(2*(v+6)) := by
        field_simp [hv0.ne',show v+6 ≠ 0 by linarith] <;> ring
      rw [hid] at ht'
      have hr : 243/(2*(v+6)) ≤ (81/10 : ℝ) :=
        (div_le_iff₀ (by positivity)).2 (by linarith)
      nlinarith only [ht',hr]
    have he : Real.exp s ≤ 9/4 :=
      (Real.exp_le_exp.mpr (show s ≤ 3/4 by linarith [hs.2])).trans exp_three_quarters_lt.le
    have hs2 := pow_le_pow_left₀ hs0 hs.2 2
    have hs3 := pow_le_pow_left₀ hs0 hs.2 3
    norm_num at hs2 hs3
    have hvs0 := mul_le_mul hv hs.1 (by norm_num : (0:ℝ)≤2/3) hv0.le
    have hvs : 0 ≤ v*s-3 := by nlinarith only [hvs0]
    have hfirst : s^2*(s+3)*Real.exp s ≤ (25/49 : ℝ)*(26/7)*(9/4) := by
      exact mul_le_mul (mul_le_mul hs2 (by linarith [hs.2]) (by linarith) (by norm_num))
        he (Real.exp_pos s).le (by norm_num)
    have hsecond : s^2*(v^2*(v*s-3)*Real.exp (-v*s)) ≤ (125/343 : ℝ)*(81/10) := by
      have hdrop : s^2*(v^2*(v*s-3)*Real.exp (-v*s)) ≤ s^3*(v^3*Real.exp (-v*s)) := by
        nlinarith [mul_nonneg (sq_nonneg s) (mul_nonneg (sq_nonneg v) (Real.exp_pos (-v*s)).le)]
      exact hdrop.trans (mul_le_mul hs3 htail3 (by positivity) (by norm_num))
    have hsum : s^2*((s+3)*Real.exp s+v^2*(v*s-3)*Real.exp (-v*s)) ≤
        (25/49 : ℝ)*(26/7)*(9/4)+(125/343)*(81/10) := by
      nlinarith only [hfirst,hsecond]
    have hscaled := mul_le_mul hC hsum (by positivity) (by norm_num)
    exact ⟨by positivity, by nlinarith only [hscaled]⟩
  have hdiff : Differentiable ℝ (H v) := fun s => (hd s).differentiableAt
  have hl := (convex_Icc (2/3 : ℝ) (5/7)).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun s hs => (hbound s (interior_subset hs)).1) a ha b hb hab
  have hu := (convex_Icc (2/3 : ℝ) (5/7)).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun s hs => (hbound s (interior_subset hs)).2) a ha b hb hab
  constructor <;> linarith only [hl,hu]

private theorem coeff (M : Model) :
    0 < kap M ∧ 0 < alpha M ∧ alpha M*M.sigma = kap M ∧
    (2/9)*M.q ≤ kap M ∧ (10/7)*kap M < alpha M ∧
    alpha M < (291/200)*kap M ∧ M.d ≤ M.q/8 ∧
    0 < k M ∧ k M ≤ 1/25 ∧ M.q^2*k M ≤ 1/3 ∧
    M.d/alpha M ≤ 1/16 ∧ 0 < g M ∧ g M ≤ 2 := by
  have hq : 0 < M.q := by linarith [M.q3]
  have hn : 9 ≤ M.q^2 := by nlinarith [M.q3,sq_nonneg (M.q-3)]
  have hnm : 0 < M.q^2-1 := by linarith
  have hs : 0 < M.sigma := by linarith [M.sigmaLo]
  have hkap : 0 < kap M := div_pos (by linarith) (by positivity)
  have ha : 0 < alpha M := div_pos hkap hs
  have hid : alpha M*M.sigma = kap M := by dsimp [alpha]; field_simp
  have hkapq : (2/9)*M.q ≤ kap M := by
    apply (le_div_iff₀ (show 0 < 4*M.q by positivity)).2; nlinarith only [hn]
  have haLo : (10/7)*kap M < alpha M := by
    apply (lt_div_iff₀ hs).2
    nlinarith [mul_pos hkap (sub_pos.mpr M.sigmaHi)]
  have haHi : alpha M < (291/200)*kap M := by
    apply (div_lt_iff₀ hs).2
    nlinarith [mul_pos hkap (sub_pos.mpr M.sigmaLo)]
  have hdr : M.d/alpha M < 49/(120*(M.q^2-1)) := by
    have hr := div_lt_div_of_pos_right M.dHi ha
    have he : (7/(48*M.q))/alpha M = 7*M.sigma/(12*(M.q^2-1)) := by
      dsimp [alpha,kap]; field_simp [hq.ne',hs.ne',show M.q^2-1 ≠ 0 by linarith] <;> ring
    rw [he] at hr
    have hh : 7*M.sigma/(12*(M.q^2-1)) < 49/(120*(M.q^2-1)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_pos (show 0 < M.q^2-1 by linarith) (sub_pos.mpr M.sigmaHi)]
    exact hr.trans hh
  have hdr0 : 0 < M.d/alpha M := div_pos M.d0 ha
  have hk0 : 0 < k M := div_pos (mul_pos hs M.d0) ha
  have hkr : k M = M.sigma*(M.d/alpha M) := by dsimp [k]; ring
  have hksharp : k M < 343/(1200*(M.q^2-1)) := by
    rw [hkr]
    have hh := mul_lt_mul M.sigmaHi hdr.le hdr0 (by norm_num : (0:ℝ)≤7/10)
    have hrat : (7/10 : ℝ)*(49/(120*(M.q^2-1))) = 343/(1200*(M.q^2-1)) := by
      field_simp [hnm.ne'] <;> ring
    exact hh.trans_eq hrat
  have hk : k M ≤ 1/25 := by
    have hh := (lt_div_iff₀ (show 0 < 1200*(M.q^2-1) by positivity)).mp hksharp
    nlinarith [mul_nonneg hk0.le (show 0 ≤ M.q^2-9 by linarith)]
  have hnk : M.q^2*k M ≤ 1/3 := by
    have hh := (lt_div_iff₀ (show 0 < 1200*(M.q^2-1) by positivity)).mp hksharp
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ M.q^2-9 by linarith)]
  have hdr16 : M.d/alpha M ≤ 1/16 := by
    have hh := (lt_div_iff₀ (show 0 < 120*(M.q^2-1) by positivity)).mp hdr
    nlinarith [mul_nonneg hdr0.le (show 0 ≤ M.q^2-9 by linarith)]
  have ht := real_rational_tail_on_ray hn (show 2/3 ≤ M.sigma by linarith [M.sigmaLo])
  have hg0 : 0 < g M := by
    have he := Real.add_one_le_exp M.sigma
    have ht1 : M.q^2*Real.exp (-M.q^2*M.sigma) < 9/10 := by
      have hh := mul_nonneg (mul_nonneg (sq_nonneg M.q) (show 0 ≤ M.q^2-1 by linarith))
        (Real.exp_pos (-M.q^2*M.sigma)).le
      nlinarith only [ht.2.2,hh]
    dsimp [g]; linarith [ht1]
  have hg : g M ≤ 2 := by
    have hr := M.root; dsimp [G] at hr
    dsimp [g]; nlinarith [Real.exp_pos (-M.q^2*M.sigma)]
  refine ⟨hkap,ha,hid,hkapq,haLo,haHi,?_,hk0,hk,hnk,hdr16,hg0,hg⟩
  exact M.dHi.le.trans ((div_le_iff₀ (show 0 < 48*M.q by positivity)).2 (by nlinarith only [hn]))

private theorem band (M : Model) {P : ℝ} (hP : 5 ≤ P) :
    (7/5)*kap M*P < vc M P-eps M P ∧
    vc M P+eps M P ≤ (3/2)*kap M*P := by
  obtain ⟨hκ,hα,hid,hκq,hαlo,hαhi,hdq,rest⟩ := coeff M
  have hp : 0 < P := by linarith
  have hq : 0 < M.q := by linarith [M.q3]
  have hp2 : 25 ≤ P^2 := by nlinarith [sq_nonneg (P-5)]
  have hp4 : 625 ≤ P^4 := by nlinarith [sq_nonneg (P^2-25)]
  have hε : 0 < eps M P := by dsimp [eps]; positivity
  have heps : eps M P < kap M*P/35 := by
    apply (div_lt_iff₀ (show 0 < 10*P^3 by positivity)).2
    have hh := mul_le_mul_of_nonneg_right hκq (show 0 ≤ P^4 by positivity)
    have hj := mul_le_mul_of_nonneg_left hp4 hq.le
    nlinarith only [hh,hj,hq]
  have hd : M.d/P ≤ M.q/(8*P) := by
    convert div_le_div_of_nonneg_right hdq hp.le using 1 <;> ring
  have he : eps M P ≤ M.q/(10*P) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hh := mul_nonneg hq.le (mul_nonneg hp.le (show 0 ≤ P^2-1 by linarith))
    nlinarith only [hh]
  have hsmall : M.q/(8*P)+M.q/(10*P) < M.q*P/100 := by
    have hh := mul_pos hq (show 0 < P^2-45/2 by linarith)
    rw [show M.q/(8*P)+M.q/(10*P) = 9*M.q/(40*P) by ring]
    apply (div_lt_iff₀ (show 0 < 40*P by positivity)).2
    nlinarith only [hh]
  have hlo := mul_lt_mul_of_pos_right hαlo hp
  have hhi := mul_lt_mul_of_pos_right hαhi hp
  have hκp := mul_le_mul_of_nonneg_right hκq hp.le
  dsimp [vc]
  constructor
  · linarith [div_pos M.d0 hp]
  · nlinarith only [hhi,hd,he,hsmall,hκp]

private theorem parameter_mem (M : Model) {P v : ℝ} (hp : 0 < P)
    (hl : (7/5)*kap M*P ≤ v) (hu : v ≤ (3/2)*kap M*P) :
    parameter M P v ∈ Icc (2/3 : ℝ) (5/7) := by
  have hκ := (coeff M).1
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hl
  constructor
  · exact (le_div_iff₀ hv).2 (by linarith only [hu])
  · exact (div_le_iff₀ hv).2 (by linarith only [hl])

private theorem antitone_parameter (M : Model) {P a b : ℝ}
    (hp : 0 < P) (ha : 0 < a) (hab : a ≤ b) :
    parameter M P b ≤ parameter M P a :=
  div_le_div_of_nonneg_left (mul_pos (coeff M).1 hp).le ha hab

private theorem F_secant (M : Model) {P a b : ℝ} (ha : a ∈ Icc (2/3 : ℝ) (5/7))
    (hb : b ∈ Icc (2/3 : ℝ) (5/7)) (hab : a ≤ b) :
    F M P a+(161/90)*(b-a) ≤ F M P b := by
  have hn : 9 ≤ M.q^2 := by nlinarith [M.q3,sq_nonneg (M.q-3)]
  have hg := M.slope a b ha.1 hab
  have hh := div_le_div_of_nonneg_right (H_secant hn ha hb hab).1 (sq_nonneg P)
  dsimp [F]; rw [zero_div,sub_div] at hh; linarith only [hg,hh]

private theorem center_error (M : Model) {P : ℝ} (hP : 5 ≤ P) :
    |F M P (parameter M P (vc M P))-2| ≤ 1/(20*P^4) := by
  obtain ⟨hκ,hα,hid,hκq,hαlo,hαhi,hdq,hk0,hk,hnk,hda,hg0,hg⟩ := coeff M
  have hp : 0 < P := by linarith
  have hs : 0 < M.sigma := by linarith [M.sigmaLo]
  have hd0 : 0 < M.d := M.d0
  have hD : 0 < alpha M*P^2+M.d := by positivity
  have hvc : 0 < vc M P := by dsimp [vc]; positivity
  let sc := parameter M P (vc M P)
  let δ := M.sigma-sc
  let r := k M/P^2-δ
  let E := G (M.q^2) sc-2+g M*δ
  have hvc_repr : vc M P = (alpha M*P^2+M.d)/P := by
    dsimp [vc]; field_simp [hp.ne'] <;> ring
  have hsc_repr : sc = kap M*P^2/(alpha M*P^2+M.d) := by
    dsimp [sc,parameter]; rw [hvc_repr]; field_simp [hp.ne',hD.ne'] <;> ring
  have hδ : δ = k M*alpha M/(alpha M*P^2+M.d) := by
    dsimp only [δ]; rw [hsc_repr,← hid]; dsimp [k]
    field_simp [hα.ne',hD.ne'] <;> ring
  have hr : r = k M*M.d/(P^2*(alpha M*P^2+M.d)) := by
    dsimp [r]; rw [hδ]; field_simp [hp.ne',hD.ne'] <;> ring
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hδk : δ ≤ k M/P^2 := by dsimp [r] at hr0; linarith only [hr0]
  have hδsmall : δ ≤ (1/25)/P^2 :=
    hδk.trans (div_le_div_of_nonneg_right hk (sq_nonneg P))
  have hδsq : δ^2 ≤ (1/625)/P^4 := by
    have hh := pow_le_pow_left₀ hδ0 hδsmall 2
    convert hh using 1 <;> ring
  have hrsmall : r ≤ 1/(400*P^4) := by
    rw [hr]
    calc
      _ ≤ k M*M.d/(P^2*(alpha M*P^2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith [M.d0]) (sq_nonneg P))
      _ = (k M*(M.d/alpha M))/P^4 := by field_simp [hp.ne',hα.ne'] <;> ring
      _ ≤ ((1/25)*(1/16))/P^4 :=
        div_le_div_of_nonneg_right (mul_le_mul hk hda (by positivity) (by norm_num)) (by positivity)
      _ = _ := by ring
  have hn : 9 ≤ M.q^2 := by nlinarith [M.q3,sq_nonneg (M.q-3)]
  have hp2 : 25 ≤ P^2 := by nlinarith [sq_nonneg (P-5)]
  have hνδ : M.q^2*δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hδk (sq_nonneg M.q)
    have hj := div_le_div_of_nonneg_right hnk (sq_nonneg P)
    rw [← mul_div_assoc] at hh
    have hi : (1/3)/P^2 ≤ (1 : ℝ) := (div_le_iff₀ (by positivity)).2 (by linarith)
    exact hh.trans (hj.trans hi)
  have hm := abs_le.mp (exp_negative_quadratic_remainder hδ0)
  have hp' := abs_le.mp (exp_positive_quadratic_remainder
    (show 0 ≤ M.q^2*δ by positivity) hνδ)
  have hm0 : 0 ≤ Real.exp (-δ)-1+δ := by linarith [Real.add_one_le_exp (-δ)]
  have hp0 : 0 ≤ Real.exp (M.q^2*δ)-1-M.q^2*δ := by
    linarith [Real.add_one_le_exp (M.q^2*δ)]
  have hrepr : E = Real.exp M.sigma*(Real.exp (-δ)-1+δ)+
      Real.exp (-M.q^2*M.sigma)*(Real.exp (M.q^2*δ)-1-M.q^2*δ) := by
    have he : sc = M.sigma-δ := by dsimp [δ]; ring
    have hroot := M.root
    dsimp [E,G,g] at *
    rw [he,show M.sigma-δ = M.sigma+(-δ) by ring,Real.exp_add,
      show -M.q^2*(M.sigma+-δ) = -M.q^2*M.sigma+M.q^2*δ by ring,Real.exp_add]
    nlinarith only [hroot]
  have ht := (real_rational_tail_on_ray hn (show 2/3 ≤ M.sigma by linarith [M.sigmaLo])).2.2.le
  have hes : Real.exp M.sigma ≤ 2 := by
    have hh := M.root; dsimp [G] at hh; linarith [Real.exp_pos (-M.q^2*M.sigma)]
  have hE0 : 0 ≤ E := by rw [hrepr]; positivity
  have hE : E ≤ 2*δ^2 := by
    rw [hrepr]
    have hm' := mul_le_mul hes hm.2 hm0 (by norm_num : (0:ℝ)≤2)
    have hp'' := mul_le_mul_of_nonneg_left hp'.2 (Real.exp_pos (-M.q^2*M.sigma)).le
    have ht' := mul_le_mul_of_nonneg_right ht (show 0 ≤ (3/4)*δ^2 by positivity)
    nlinarith only [hm',hp'',ht',sq_nonneg δ]
  have hq : 0 < M.q := by linarith [M.q3]
  have hε : 0 < eps M P := by dsimp [eps]; positivity
  have hb := band M hP
  have hsc : sc ∈ Icc (2/3 : ℝ) (5/7) :=
    parameter_mem M hp (by linarith [hb.1]) (by linarith [hb.2])
  have hσ : M.sigma ∈ Icc (2/3 : ℝ) (5/7) :=
    ⟨by linarith [M.sigmaLo],by linarith [M.sigmaHi]⟩
  have hH := H_secant hn hsc hσ (show sc ≤ M.sigma by dsimp [δ] at hδ0; linarith)
  have hHsmall : (H (M.q^2) M.sigma-H (M.q^2) sc)/P^2 ≤ (1/25)/P^4 := by
    have hh := div_le_div_of_nonneg_right (hH.2.trans hδsmall) (sq_nonneg P)
    convert hh using 1 <;> ring
  have hc : g M*k M = H (M.q^2) M.sigma := M.cancellation
  have heq : F M P sc-2 = g M*r+E-(H (M.q^2) M.sigma-H (M.q^2) sc)/P^2 := by
    dsimp [F,r,E]; rw [sub_div,← hc]; ring
  have hgr := mul_le_mul hg hrsmall hr0 (by norm_num : (0:ℝ)≤2)
  have hEs := hE.trans (mul_le_mul_of_nonneg_left hδsq (by norm_num : (0:ℝ)≤2))
  have htotal : 2*(1/(400*P^4))+2*((1/625)/P^4)+(1/25)/P^4 < 1/(20*P^4) := by
    have hpos : 0 < (9/5000 : ℝ)/P^4 := by positivity
    have hid : 1/(20*P^4)-(2*(1/(400*P^4))+2*((1/625)/P^4)+(1/25)/P^4) =
        (9/5000 : ℝ)/P^4 := by ring
    linarith only [hid,hpos]
  have hhr0 : 0 ≤ (H (M.q^2) M.sigma-H (M.q^2) sc)/P^2 := div_nonneg hH.1 (sq_nonneg P)
  have hgr0 : 0 ≤ g M*r := mul_nonneg hg0.le hr0
  apply abs_le.mpr; rw [heq]
  constructor <;> nlinarith only [hgr,hEs,hHsmall,htotal,hhr0,hgr0,hE0,
    show 0 ≤ 2*(1/(400*P^4)) by positivity,show 0 ≤ 2*((1/625)/P^4) by positivity]

private theorem parameter_gap (M : Model) {P a b : ℝ} (hp : 0 < P)
    (ha : 0 < a) (hb : 0 < b) (haU : a ≤ 3*M.q*P/8) (hbU : b ≤ 3*M.q*P/8)
    (hgap : eps M P ≤ b-a) :
    64/(405*P^4) ≤ parameter M P a-parameter M P b := by
  have hq : 0 < M.q := by linarith [M.q3]
  have hκ := (coeff M).1
  have hκq := (coeff M).2.2.2.1
  have hid : parameter M P a-parameter M P b = kap M*P*(b-a)/(a*b) := by
    dsimp [parameter]; field_simp [ha.ne',hb.ne'] <;> ring
  rw [hid]; apply (le_div_iff₀ (mul_pos ha hb)).2
  have hab : a*b ≤ (3*M.q*P/8)^2 := by
    simpa only [pow_two] using mul_le_mul haU hbU hb.le (by positivity)
  calc
    _ ≤ (64/(405*P^4))*(3*M.q*P/8)^2 :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ = ((2/9)*M.q)*P*eps M P := by dsimp [eps]; field_simp [hp.ne'] <;> ring
    _ ≤ kap M*P*eps M P := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hκq hp.le) (by dsimp [eps]; positivity)
    _ ≤ kap M*P*(b-a) := mul_le_mul_of_nonneg_left hgap (by positivity)

private theorem test_values (M : Model) {P : ℝ} (hP : 5 ≤ P) :
    2+1/(5*P^4) < F M P (parameter M P (vc M P-eps M P)) ∧
    F M P (parameter M P (vc M P+eps M P)) < 2-1/(5*P^4) := by
  have hp : 0 < P := by linarith
  have hκ := (coeff M).1
  have hq : 0 < M.q := by linarith [M.q3]
  have hε : 0 < eps M P := by dsimp [eps]; positivity
  have hv := band M hP
  have hm0 : 0 < vc M P-eps M P := lt_of_lt_of_le (by positivity) hv.1.le
  have hc0 : 0 < vc M P := by linarith
  have hp0 : 0 < vc M P+eps M P := by linarith
  have hκU : (3/2)*kap M*P ≤ 3*M.q*P/8 := by
    rw [show (3/2)*kap M*P = 3*(M.q^2-1)*P/(8*M.q) by dsimp [kap]; ring]
    apply (div_le_iff₀ (show 0 < 8*M.q by positivity)).2
    nlinarith [hp.le]
  have hmU : vc M P-eps M P ≤ 3*M.q*P/8 := by linarith [hv.2]
  have hcU : vc M P ≤ 3*M.q*P/8 := by linarith [hv.2]
  have hpU : vc M P+eps M P ≤ 3*M.q*P/8 := hv.2.trans hκU
  have hmI := parameter_mem M hp hv.1.le (by linarith [hv.2])
  have hcI := parameter_mem M (P := P) (v := vc M P) hp (by linarith [hv.1]) (by linarith [hv.2])
  have hpI := parameter_mem M (P := P) (v := vc M P+eps M P) hp (by linarith [hv.1]) hv.2
  have hmc := antitone_parameter M hp hm0 (show vc M P-eps M P ≤ vc M P by linarith)
  have hpc := antitone_parameter M hp hc0 (show vc M P ≤ vc M P+eps M P by linarith)
  have hmg := parameter_gap M hp hm0 hc0 hmU hcU (by linarith : eps M P ≤ vc M P-(vc M P-eps M P))
  have hpg := parameter_gap M hp hc0 hp0 hcU hpU (by linarith : eps M P ≤ vc M P+eps M P-vc M P)
  have hms := F_secant M (P := P) hcI hmI hmc
  have hps := F_secant M (P := P) hpI hcI hpc
  have he := abs_le.mp (center_error M hP)
  have hmargin : 1/(20*P^4)+1/(5*P^4) < (161/90)*(64/(405*P^4)) := by
    have hid : (161/90)*(64/(405*P^4))-1/(20*P^4)-1/(5*P^4) =
        (2383/72900 : ℝ)/P^4 := by ring
    have hh : 0 < (2383/72900 : ℝ)/P^4 := by positivity
    linarith only [hid,hh]
  have hm := mul_le_mul_of_nonneg_left hmg (by norm_num : (0:ℝ)≤161/90)
  have hp' := mul_le_mul_of_nonneg_left hpg (by norm_num : (0:ℝ)≤161/90)
  constructor <;> linarith only [hms,hps,he.1,he.2,hm,hp',hmargin]

-- Only the small sharp inference is new here; the q=3 architecture is not imported.
private theorem sigma_nine_sharp : (200/291 : ℝ) < Real.log (dbonacciPerronRoot 9) := by
  have he := Real.exp_bound' (x := (200/291 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [sum_range_succ,Nat.factorial] at he
  have h6 := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 9
  norm_num [sum_range_succ,Nat.factorial] at h6
  have hmono := Real.exp_le_exp.mpr (by norm_num : (6:ℝ) ≤ 9*(200/291))
  have hn : Real.exp (-9*(200/291 : ℝ)) < 1/300 := by
    rw [show -9*(200/291 : ℝ) = -(9*(200/291)) by ring,Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).2
    linarith only [h6,hmono]
  by_contra h
  have hs := BajnokBeattyOddWrapGaussianRoot.gaussian_secant
    BajnokBeattyOddWrapGaussianRoot.two_thirds_lt_s_star.le (le_of_not_gt h)
  rw [BajnokBeattyOddWrapGaussianRoot.gaussian_s_star] at hs
  dsimp [BajnokBeattyOddWrapGaussianRoot.gaussian,
    BajnokBeattyOddWrapGaussianRoot.s_star] at hs
  linarith only [he,hn,hs,le_of_not_gt h]

private def model (q : ℕ) (hq : 3 ≤ q) : Model := by
  let Q : ℝ := q
  let β := dbonacciPerronRoot (q^2)
  let σ := Real.log β
  let d := ((Q^2+1)*σ/(6*Q*(Q^2-1)))*
    (((Q^4+1)*β-2*Q^4)/((Q^2+1)*β-2*Q^2))
  have hqR : 3 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hq0 : 0 < Q := by linarith
  have hn : 9 ≤ q^2 := by simpa only [pow_two] using Nat.mul_le_mul hq hq
  have hb : 0 < β := lt_trans zero_lt_one (one_lt_dbonacciPerronRoot _ (by omega))
  have hβ : β < 2 := dbonacciPerronRoot_lt_two _ (by omega)
  have hσ : 200/291 < σ := sigma_nine_sharp.trans_le
    (Real.strictMonoOn_log.monotoneOn
      (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num))) hb
      (dbonacciPerronRoot_strictMonoOn.monotoneOn (by norm_num)
        (by change 2 ≤ q^2; omega) hn))
  have hl2 : Real.log (2 : ℝ) < 7/10 := by
    have he := Real.sum_le_exp_of_nonneg (x := (7/10 : ℝ)) (by norm_num) 5
    norm_num [sum_range_succ,Nat.factorial] at he
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<2)).2
    linarith only [he]
  have hσhi : σ < 7/10 := (Real.strictMonoOn_log hb (by norm_num) hβ).trans hl2
  have hc := square_displacement_correction q hq
  change 0 < _ ∧ 0 < d ∧ d < 5*Real.log 2/(24*Q) ∧ _ at hc
  refine ⟨Q,σ,d,hqR,hσ,hσhi,hc.2.1,?_,?_,?_,?_⟩
  · exact hc.2.2.1.trans ((div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hl2 (by norm_num)) (by positivity : 0 < 24*Q)).trans_eq (by ring))
  · have hm : Real.exp (Q^2*σ) = β^(q^2) := by
      have hh := Real.exp_nat_mul σ (q^2)
      have hcast : ((q^2 : ℕ) : ℝ) = Q^2 := by dsimp [Q]; norm_cast
      rw [hcast] at hh
      simpa only [σ,Real.exp_log hb] using hh
    have ht : Real.exp (-Q^2*σ) = 2-β := by
      rw [neg_mul,Real.exp_neg,hm,← inv_pow]
      exact (two_sub_dbonacciPerronRoot_eq_inv_pow _ (by omega)).symm
    dsimp [G]; rw [show Real.exp σ = β from Real.exp_log hb,ht]; ring
  · intro a b ha hab
    exact (square_displacement_profile.2.1 q hq a b ha hab).1
  · simpa only [H,show (Q^2)^2 = Q^4 by ring] using hc.2.2.2.2.2

-- A new finite positive-cone estimate. The correct x-block bound is 1/(2p),
-- not the candidate's 1/(3p). The slightly larger tail still closes strictly.
set_option maxHeartbeats 800000 in
theorem binomial_signs (p q n a r : ℕ) (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (hr : 2*r = (q-1)*p) (hna : n+p = 2*a) (hfit : a+(q+1)*r ≤ n) :
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1))
    let A : ℝ := Nat.choose n a
    let B : ℝ := Nat.choose n (a+r)
    let D : ℝ := Nat.choose n (a+(q+1)*r)
    0 < B ∧ (5/7 < s → 2*B < A+D) ∧
      (2/5 ≤ s → s ≤ 2/3 → A+D < 2*B) := by
  dsimp only
  let P : ℝ := p
  let Q : ℝ := q
  let R : ℝ := (n : ℝ)+1
  let s := (Q^2-1)*P^2/(2*R)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+r)
  let D : ℝ := Nat.choose n (a+(q+1)*r)
  have hP : 5 ≤ P := by dsimp [P]; exact_mod_cast hp5
  have hQ : 3 ≤ Q := by dsimp [Q]; exact_mod_cast hq3
  have hp : 0 < P := by linarith
  have hq : 0 < Q := by linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hn : (n : ℝ)+P = 2*(a : ℝ) := by dsimp [P]; exact_mod_cast hna
  have hrR : (r : ℝ) = (Q-1)*P/2 := by
    have hh := congrArg (fun z : ℕ => (z : ℝ)) hr
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hh
    dsimp [P,Q]; linarith only [hh]
  have hqr : ((q*r : ℕ) : ℝ) = Q*(r : ℝ) := by push_cast; rfl
  have hrl : r ≤ (q+1)*r := by
    simpa only [one_mul] using Nat.mul_le_mul_right r (show 1 ≤ q+1 by omega)
  have hBr : a+r ≤ n := by omega
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (show a ≤ n by omega)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos hBr
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos hfit
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  let y (i : ℕ) : ℝ := (Q*P+2*(i : ℝ)+1)/R
  have hx (i : ℕ) (hi : i ∈ range r) : 0 ≤ x i ∧ x i < 1 := by
    have hi' := mem_range.mp hi
    have hiR : (a : ℝ)+(i : ℝ) < n := by exact_mod_cast (show a+i < n by omega)
    exact ⟨by dsimp [x]; positivity,(div_lt_iff₀ hR).2 (by dsimp [R]; linarith only [hn,hiR])⟩
  have hy (i : ℕ) (hi : i ∈ range (q*r)) : 0 ≤ y i ∧ y i < 1 := by
    have hi' := mem_range.mp hi
    have hfar : a+r+q*r ≤ n := by nlinarith only [hfit]
    have hiR : ((a+r : ℕ) : ℝ)+(i : ℝ) < n := by
      exact_mod_cast (show a+r+i < n by omega)
    have hnB : 2*((a+r : ℕ) : ℝ)-(n : ℝ) = Q*P := by push_cast; nlinarith only [hrR,hn]
    exact ⟨by dsimp [y]; positivity,(div_lt_iff₀ hR).2 (by dsimp [R]; linarith only [hnB,hiR])⟩
  have hAB : A/B = ∏ i ∈ range r, (1+x i)/(1-x i) :=
    choose_ratio_centered_prod n a r P R hBr rfl (by linarith only [hn])
  have hBD : B/D = ∏ i ∈ range (q*r), (1+y i)/(1-y i) := by
    have hh := choose_ratio_centered_prod n (a+r) (q*r) (Q*P) R
      (by convert hfit using 1 <;> ring) rfl (by push_cast; nlinarith only [hrR,hn])
    simpa only [show a+r+q*r = a+(q+1)*r by ring] using hh
  have hxsum : 2*(∑ i ∈ range r, x i) = s := by
    dsimp [x]; rw [← sum_div,sum_linear,hrR]; dsimp [s]; field_simp [hR.ne'] <;> ring
  have hysum : 2*(∑ i ∈ range (q*r), y i) = Q^2*s := by
    dsimp [y]; rw [← sum_div,sum_linear,hqr,hrR]; dsimp [s]; field_simp [hR.ne'] <;> ring
  have hlogA : Real.log (A/B) = ∑ i ∈ range r, Real.log ((1+x i)/(1-x i)) := by
    rw [hAB,Real.log_prod (fun i hi => (div_pos (by linarith [(hx i hi).1])
      (by linarith [(hx i hi).2])).ne')]
  have hlogD : Real.log (B/D) = ∑ i ∈ range (q*r), Real.log ((1+y i)/(1-y i)) := by
    rw [hBD,Real.log_prod (fun i hi => (div_pos (by linarith [(hy i hi).1])
      (by linarith [(hy i hi).2])).ne')]
  have hL : s ≤ Real.log (A/B) := by
    have hh := sum_le_sum (fun i hi => Real.sum_range_le_log_div (hx i hi).1 (hx i hi).2 1)
    norm_num [sum_range_succ] at hh
    rw [← mul_sum,← hlogA] at hh; linarith only [hh,hxsum]
  have hJ : Q^2*s ≤ Real.log (B/D) := by
    have hh := sum_le_sum (fun i hi => Real.sum_range_le_log_div (hy i hi).1 (hy i hi).2 1)
    norm_num [sum_range_succ] at hh
    rw [← mul_sum,← hlogD] at hh; linarith only [hh,hysum]
  refine ⟨hB,?_,?_⟩
  · intro hs
    have hlog2 : Real.log (2 : ℝ) < 7/10 := by
      have he := Real.sum_le_exp_of_nonneg (x := (7/10:ℝ)) (by norm_num) 5
      norm_num [sum_range_succ,Nat.factorial] at he
      exact (Real.log_lt_iff_lt_exp (by norm_num)).2 (by linarith only [he])
    have hratio : 2 < A/B := (Real.log_lt_log_iff (by norm_num) (div_pos hA hB)).mp
      (show Real.log 2 < Real.log (A/B) by linarith only [hL,hs,hlog2])
    have hh := (lt_div_iff₀ hB).mp hratio; linarith only [hh,hD]
  · intro hslo hshi
    have hnine : 9 ≤ Q^2 := by nlinarith [sq_nonneg (Q-3)]
    have hnm : 0 < Q^2-1 := by linarith
    have hs0 : 0 ≤ s := by linarith
    have hC : 2*(Q^2+1)/(3*(Q^2-1)^2) ≤ (5/48 : ℝ) := by
      apply (div_le_iff₀ (show 0 < 3*(Q^2-1)^2 by positivity)).2
      nlinarith [mul_nonneg (show 0 ≤ Q^2-9 by linarith) (show 0 ≤ 5*Q^2+3 by positivity)]
    have hxsmall (i : ℕ) (hi : i ∈ range r) : x i ≤ 1/10 := by
      have hiR : (i : ℝ)+1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
      have hnum : P+2*(i : ℝ)+1 ≤ Q*P := by nlinarith only [hiR,hrR]
      have hrel : 2*s*R = (Q^2-1)*P^2 := by dsimp [s]; field_simp [hR.ne'] <;> ring
      have hqrel : 4*Q ≤ 3*(Q^2-1)/2 := by nlinarith [sq_nonneg (Q-3)]
      have hband := mul_le_mul_of_nonneg_right hshi hR.le
      have hmul := mul_le_mul_of_nonneg_right hqrel (sq_nonneg P)
      have hlast : x i ≤ 1/(2*P) := by
        have hnumP := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 2*P by positivity)
        apply (div_le_div_iff₀ hR (by positivity)).2
        nlinarith only [hnumP,hrel,hband,hmul]
      exact hlast.trans ((div_le_iff₀ (by positivity)).2 (by linarith only [hP]))
    let U : ℝ := (2/3)*(∑ i ∈ range r, (x i)^3)
    have hU : U ≤ 1/810 := by
      have heq : U = (2*(Q^2+1)/(3*(Q^2-1)^2))*s^3/P^2-
          (4/(3*(Q^2-1)^2))*s^3/P^4 := by
        dsimp [U,x]; simp_rw [div_pow]; rw [← sum_div,sum_cubic,hrR]
        dsimp [s]; field_simp [hR.ne',hp.ne',show Q^2-1 ≠ 0 by linarith] <;> ring
      have hs3 := pow_le_pow_left₀ hs0 hshi 3
      norm_num at hs3
      have hp2 : 25 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-5)]
      have hprod := mul_le_mul hC hs3 (by positivity) (by norm_num : (0:ℝ)≤5/48)
      have hmain : (2*(Q^2+1)/(3*(Q^2-1)^2))*s^3/P^2 ≤ 1/810 :=
        (div_le_iff₀ (by positivity)).2 (by nlinarith only [hprod,hp2])
      rw [heq]; exact (sub_le_self _ (by positivity)).trans hmain
    have hlog : Real.log (A/B) ≤ 2/3+(34/33)/810 := by
      have hpoint (i : ℕ) (hi : i ∈ range r) :
          Real.log ((1+x i)/(1-x i)) ≤ 2*x i+(34/33)*((2/3)*(x i)^3) := by
        have hz := hx i hi
        have hz2 : (x i)^2 ≤ 1/100 := by
          have hh := pow_le_pow_left₀ hz.1 (hxsmall i hi) 2
          norm_num at hh; exact hh
        have hd : 0 < 1-(x i)^2 := by linarith
        have htail : 2*(x i)^5/(1-(x i)^2) ≤ (1/33)*((2/3)*(x i)^3) := by
          apply (div_le_iff₀ hd).2
          nlinarith only [mul_nonneg (pow_nonneg hz.1 3)
            (show 0 ≤ 1/100-(x i)^2 by linarith only [hz2])]
        have hh := Real.log_div_le_sum_range_add hz.1 hz.2 2
        norm_num [sum_range_succ] at hh
        rw [mul_div_assoc] at htail
        linarith only [hh,htail]
      have hh := sum_le_sum hpoint
      rw [← hlogA,sum_add_distrib,← mul_sum,← mul_sum,← mul_sum,hxsum] at hh
      change Real.log (A/B) ≤ s+(34/33)*U at hh
      linarith only [hh,hU,hshi]
    have hABsmall : A/B < 49/25 := by
      have he := Real.exp_bound' (x := (67/100:ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
      norm_num [sum_range_succ,Nat.factorial] at he
      have hh := Real.exp_lt_exp.mpr (show Real.log (A/B) < 67/100 by linarith only [hlog])
      rw [Real.exp_log (div_pos hA hB)] at hh; linarith only [hh,he]
    have hDBsmall : D/B < 1/30 := by
      have he := Real.sum_le_exp_of_nonneg (x := (18/5:ℝ)) (by norm_num) 6
      norm_num [sum_range_succ,Nat.factorial] at he
      have hvs := mul_le_mul hnine hslo (by norm_num : (0:ℝ)≤2/5) (sq_nonneg Q)
      have hh := Real.exp_le_exp.mpr (show (18/5:ℝ) ≤ Real.log (B/D) by nlinarith only [hJ,hvs])
      rw [Real.exp_log (div_pos hB hD)] at hh
      have hratio : 30 < B/D := by linarith only [he,hh]
      have hmul := (lt_div_iff₀ hD).mp hratio
      exact (div_lt_iff₀ hB).2 (by linarith only [hmul])
    have hsum : (A+D)/B < 2 := by rw [add_div]; linarith only [hABsmall,hDBsmall]
    exact (div_lt_iff₀ hB).mp hsum

-- SC's private natural-coordinate definitions are unfolded by `change`;
-- only its completed actual_counts theorem needs visibility, not those defs.
theorem state_data (p q : ℤ) (t : ℕ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (ht : ((q+1)/2).toNat ≤ t) :
    ∃ n a r : ℕ, (n : ℤ) = p*(2*q*t-1) ∧ n+p.toNat = 2*a ∧
      2*r = (q.toNat-1)*p.toNat ∧ a+(q.toNat+1)*r ≤ n ∧
      (square_return_pair p q t).1 = 2*(Nat.choose n a+Nat.choose n (a+(q.toNat+1)*r)) ∧
      (square_return_pair p q t).2 = 4*Nat.choose n (a+r) := by
  obtain ⟨j,hj⟩ := hpo
  obtain ⟨e,he⟩ := hqo
  let u := j.toNat
  let v := e.toNat
  have huZ : (u : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hvZ : (v : ℤ) = e := Int.toNat_of_nonneg (by omega)
  have hu : 1 ≤ u := by omega
  have hv : 1 ≤ v := by omega
  let P : ℕ := 2*u+1
  let Q : ℕ := 2*v+1
  have hP : (P : ℤ) = p := by dsimp [P]; push_cast; omega
  have hQ : (Q : ℤ) = q := by dsimp [Q]; push_cast; omega
  have hpn : p.toNat = P := by rw [← hP,Int.toNat_natCast]
  have hqn : q.toNat = Q := by rw [← hQ,Int.toNat_natCast]
  have ht' : v+1 ≤ t := by
    have hh : (q+1)/2 = ((v+1 : ℕ) : ℤ) := by push_cast; omega
    simpa only [hh,Int.toNat_natCast] using ht
  let n := P*(2*(Q*t)-1)
  let a := P*(Q*t)
  let r := v*P
  have hqt : 1 ≤ 2*(Q*t) := by dsimp [Q]; nlinarith
  have hN : (n : ℤ) = p*(2*q*t-1) := by
    simp only [n,Nat.cast_mul,Nat.cast_sub hqt,Nat.cast_ofNat,Nat.cast_one,hP,hQ]; ring
  have hn : n+P = 2*a := by
    have hh : 2*(Q*t)-1+1 = 2*(Q*t) := by omega
    dsimp [n,a]; nlinarith only [congrArg (fun z : ℕ => P*z) hh]
  have hr : 2*r = (Q-1)*P := by dsimp [r,Q]; ring
  have hfit : a+(Q+1)*r ≤ n := by
    have htime := Nat.mul_le_mul_left Q ht'
    have hrr : (Q+1)*r = 2*v*(v+1)*P := by dsimp [Q,r]; ring
    have hrows : Q*t ≥ 2*v*(v+1)+1 := by
      dsimp [Q] at htime ⊢; nlinarith only [htime,Nat.zero_le v]
    have hbound : (Q+1)*r+P ≤ a := by
      rw [hrr]; dsimp [a]; nlinarith only [Nat.mul_le_mul_left P hrows]
    omega
  have hc := actual_counts u v t hu hv ht'
  change (square_return_pair (P : ℤ) (Q : ℤ) t).1 =
      2*(Nat.choose n a+Nat.choose n (a+(Q+1)*r)) ∧
    (square_return_pair (P : ℤ) (Q : ℤ) t).2 = 4*Nat.choose n (a+r) at hc
  rw [hP,hQ] at hc
  exact ⟨n,a,r,hN,by simpa [hpn] using hn,by simpa [hpn,hqn] using hr,
    by simpa [hqn] using hfit,by simpa [hqn] using hc.1,by simpa [hqn] using hc.2⟩

private theorem actual_estimates (M : Model) (p q : ℤ) (t : ℕ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (hMq : M.q = (q : ℝ)) (ht : ((q+1)/2).toNat ≤ t) :
    let P : ℝ := p
    let v := centered M.q P t
    let s := parameter M P v
    0 < v ∧ 0 < ((square_return_pair p q t).2 : ℝ) ∧
    (5/7 < s → (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
    (2/5 ≤ s → s ≤ 2/3 → (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
    (2/3 ≤ s → s ≤ 5/7 →
      |2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-F M P s| ≤ 1/(5*P^4)) ∧
    (t ≤ ((q*p+1)/2).toNat → 2/5 < s) := by
  dsimp only
  obtain ⟨n,a,r,hN,hna,hr,hfit,hWa,hWq⟩ := state_data p q t hp5 hpo hq3 hqo ht
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpN : 5 ≤ p.toNat := by omega
  have hqN : 3 ≤ q.toNat := by omega
  have hPn : (p.toNat : ℝ) = (p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ p by omega)
  have hQn : (q.toNat : ℝ) = (q : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  have hNR : (n : ℝ) = (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1) := by exact_mod_cast hN
  have hR : (n : ℝ)+1 = 2*(q : ℝ)*(p : ℝ)*centered M.q p t := by
    rw [hNR]; dsimp [centered]; rw [hMq]; field_simp [hp.ne',hq.ne'] <;> ring
  have hv : 0 < centered M.q p t := by
    have hh : 0 < 2*(q : ℝ)*(p : ℝ)*centered M.q p t := by rw [← hR]; positivity
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*(q : ℝ)*(p : ℝ) by positivity) (le_of_not_gt hn)
    linarith only [hh,hm]
  have hs : parameter M p (centered M.q p t) =
      (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1)) := by
    rw [hR]; dsimp [parameter,kap]; rw [hMq]; field_simp [hp.ne',hq.ne',hv.ne'] <;> ring
  obtain ⟨hB,hhi,hlo⟩ := binomial_signs p.toNat q.toNat n a r hpN hqN hr hna hfit
  rw [hPn,hQn,← hs] at hhi hlo
  have hWpos : 0 < ((square_return_pair p q t).2 : ℝ) := by rw [hWq]; push_cast; positivity
  refine ⟨hv,hWpos,?_,?_,?_,?_⟩
  · intro h
    have hh := hhi h
    have hhN : 2*Nat.choose n (a+r) < Nat.choose n a+Nat.choose n (a+(q.toNat+1)*r) := by exact_mod_cast hh
    rw [hWa,hWq]; omega
  · intro hl hu
    have hh := hlo hl hu
    have hhN : Nat.choose n a+Nat.choose n (a+(q.toNat+1)*r) < 2*Nat.choose n (a+r) := by exact_mod_cast hh
    rw [hWa,hWq]; omega
  · intro hl hu
    have htZ : q+1 ≤ 2*(t : ℤ) := by
      have htcast : (((q+1)/2).toNat : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
      have hh : (q+1)/2 ≤ (t : ℤ) := by
        have h : (0 : ℤ) ≤ (q+1)/2 := Int.ediv_nonneg (by omega) (by norm_num)
        simpa only [Int.toNat_of_nonneg h] using htcast
      obtain ⟨e,he⟩ := hqo; omega
    have he := actual_square_displacement_envelope p q (t : ℤ) hp5 hpo hq3 hqo htZ
    have hnN : (p*(2*q*(t : ℤ)-1)).toNat = n := by rw [← hN,Int.toNat_natCast]
    change 2/3 ≤ (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((((p*(2*q*(t : ℤ)-1)).toNat : ℕ) : ℝ)+1)) → _ at he
    simp only [hnN] at he
    have hh := he (by rwa [← hs]) (by rwa [← hs])
    rw [← hnN] at hh
    change |2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-
      G ((q : ℝ)^2) _-H ((q : ℝ)^2) _/(p : ℝ)^2| ≤ _ at hh
    simp only [hnN] at hh
    rw [← hs,← hMq] at hh
    simpa only [F,sub_add_eq_sub_sub] using hh
  · intro hlate
    have htime : 2*(t : ℤ) ≤ q*p+1 := by
      have hpos : 0 ≤ (q*p+1)/2 := Int.ediv_nonneg (by positivity) (by norm_num)
      have hhcast : (t : ℤ) ≤ (((q*p+1)/2).toNat : ℤ) := by exact_mod_cast hlate
      have hh : (t : ℤ) ≤ (q*p+1)/2 := by simpa only [Int.toNat_of_nonneg hpos] using hhcast
      omega
    have htimeR : 2*(t : ℝ) ≤ (q : ℝ)*(p : ℝ)+1 := by exact_mod_cast htime
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have hbound : (n : ℝ) ≤ (q : ℝ)^2*(p : ℝ)^2+((q : ℝ)-1)*(p : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left htimeR (mul_pos hq hp).le
      nlinarith only [hh,hNR]
    have hcert : 0 < ((q : ℝ)^2-5)*(p : ℝ)^2-4*((q : ℝ)-1)*(p : ℝ)-4 := by
      have hqcert : 2*((q : ℝ)-1) ≤ (q : ℝ)^2-5 := by
        nlinarith [mul_nonneg (show 0 ≤ (q : ℝ)-3 by linarith) (show 0 ≤ (q : ℝ)+1 by positivity)]
      have hh := mul_le_mul_of_nonneg_right hqcert (sq_nonneg (p : ℝ))
      have hp2 : 15 ≤ (p : ℝ)*((p : ℝ)-2) := by nlinarith [sq_nonneg ((p : ℝ)-5)]
      have hj := mul_le_mul (show 2 ≤ (q : ℝ)-1 by linarith) hp2 (by norm_num) (by linarith)
      nlinarith only [hh,hj]
    rw [hs]; apply (lt_div_iff₀ (show 0 < 2*((n : ℝ)+1) by positivity)).2
    nlinarith only [hbound,hcert]

private theorem threshold_bounds (M : Model) (p q : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (hMq : M.q = (q : ℝ)) (T : ℕ)
    (hT : ((q+1)/2).toNat < T)
    (hbefore : ∀ t : ℕ, ((q+1)/2).toNat ≤ t → t < T →
      (square_return_pair p q t).2 < (square_return_pair p q t).1)
    (hat : (square_return_pair p q T).1 ≤ (square_return_pair p q T).2)
    (hlate : T ≤ ((q*p+1)/2).toNat) :
    center M p-eps M p < (T : ℝ) ∧ (T : ℤ) ≤ Int.ceil (center M p+eps M p) := by
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hp : (0 : ℝ) < p := by linarith
  have hq : 0 < M.q := by linarith [M.q3]
  have hκ := (coeff M).1
  have hκq := (coeff M).2.2.2.1
  have hε : 0 < eps M p := by dsimp [eps]; positivity
  have hb := band M hpR
  have hm0 : 0 < vc M p-eps M p := lt_of_lt_of_le (by positivity) hb.1.le
  have hp0 : 0 < vc M p+eps M p := by linarith
  have hmI := parameter_mem M hp hb.1.le (by linarith [hb.2])
  have hpI := parameter_mem M (P := (p : ℝ)) (v := vc M p+eps M p) hp (by linarith [hb.1]) hb.2
  have htest := test_values M hpR
  have hcenter (t : ℝ) : centered M.q p t = vc M p+(t-center M p) := by
    dsimp [centered,vc,center]; field_simp [hp.ne',hq.ne'] <;> ring
  constructor
  · by_contra hn
    have htR : (T : ℝ) ≤ center M p-eps M p := le_of_not_gt hn
    obtain ⟨hv,hW,hhigh,_,henv,_⟩ := actual_estimates M p q T hp5 hpo hq3 hqo hMq hT.le
    have hvle : centered M.q p T ≤ vc M p-eps M p := by rw [hcenter]; linarith only [htR]
    have hsge := antitone_parameter M hp hv hvle
    by_cases hs : parameter M p (centered M.q p T) ≤ 5/7
    · have hslo : 2/3 ≤ parameter M p (centered M.q p T) := hmI.1.trans hsge
      have hsec := F_secant M (P := (p : ℝ)) hmI ⟨hslo,hs⟩ hsge
      have hdiff : 0 ≤ (161/90)*(parameter M p (centered M.q p T)-parameter M p (vc M p-eps M p)) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr hsge)
      have he := (abs_le.mp (henv hslo hs)).1
      have hratio : 2 < 2*((square_return_pair p q T).1 : ℝ)/((square_return_pair p q T).2 : ℝ) := by
        linarith only [htest.1,hsec,hdiff,he]
      have hh := (lt_div_iff₀ hW).mp hratio
      have hatR : ((square_return_pair p q T).1 : ℝ) ≤ (square_return_pair p q T).2 := by exact_mod_cast hat
      linarith only [hh,hatR]
    · have hh := hhigh (lt_of_not_ge hs); omega
  · let U : ℤ := Int.ceil (center M p+eps M p)
    have hminpos : 0 ≤ (q+1)/2 := Int.ediv_nonneg (by omega) (by norm_num)
    have hminZ : (((q+1)/2).toNat : ℤ) = (q+1)/2 := Int.toNat_of_nonneg hminpos
    have hmin2 : 2*((((q+1)/2).toNat : ℕ) : ℝ) = M.q+1 := by
      have hh : 2*((((q+1)/2).toNat : ℕ) : ℤ) = q+1 := by
        rw [hminZ]; obtain ⟨e,he⟩ := hqo; omega
      rw [hMq]; exact_mod_cast hh
    have hoffset : 0 ≤ 1/(2*M.q)-1/(2*M.q*(p : ℝ)) := by
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have hcbase : ((((q+1)/2).toNat : ℕ) : ℝ) < center M p+eps M p := by
      have hqP := mul_le_mul_of_nonneg_left hpR hq.le
      have hκP := mul_le_mul_of_nonneg_right hκq (show 0 ≤ (7/5)*(p : ℝ) by positivity)
      have hc : center M p = vc M p+(1/(2*M.q)-1/(2*M.q*(p : ℝ))) := by
        dsimp [center,vc]; field_simp [hp.ne',hq.ne'] <;> ring
      rw [hc]; nlinarith only [hb.1,hε,hqP,hκP,hmin2,M.q3,hoffset]
    have hceil : center M p+eps M p ≤ (U : ℝ) := Int.le_ceil _
    have hU0 : 0 ≤ U := by
      have hh : (0 : ℝ) ≤ (U : ℝ) :=
        (Nat.cast_nonneg (((q+1)/2).toNat)).trans (hcbase.le.trans hceil)
      exact_mod_cast hh
    let u := U.toNat
    have huZ : (u : ℤ) = U := Int.toNat_of_nonneg hU0
    have huR : (u : ℝ) = (U : ℝ) := by exact_mod_cast huZ
    have hubase : ((q+1)/2).toNat ≤ u := by exact_mod_cast (show ((((q+1)/2).toNat : ℕ) : ℝ) ≤ u by rw [huR]; linarith only [hcbase,hceil])
    suffices T ≤ u by exact_mod_cast (show (T : ℤ) ≤ U by rw [← huZ]; exact_mod_cast this)
    by_cases hul : ((q*p+1)/2).toNat ≤ u
    · exact hlate.trans hul
    have hult : u < ((q*p+1)/2).toNat := lt_of_not_ge hul
    obtain ⟨hv,hW,_,hcone,henv,hslow⟩ := actual_estimates M p q u hp5 hpo hq3 hqo hMq hubase
    have hvge : vc M p+eps M p ≤ centered M.q p u := by
      rw [hcenter,huR]; linarith only [hceil]
    have hsle := antitone_parameter M hp hp0 hvge
    have hsU : parameter M p (centered M.q p u) ≤ 5/7 := hsle.trans hpI.2
    have hsign : (square_return_pair p q u).1 < (square_return_pair p q u).2 := by
      by_cases hs : 2/3 ≤ parameter M p (centered M.q p u)
      · have hsec := F_secant M (P := (p : ℝ)) ⟨hs,hsU⟩ hpI hsle
        have hdiff : 0 ≤ (161/90)*(parameter M p (vc M p+eps M p)-parameter M p (centered M.q p u)) :=
          mul_nonneg (by norm_num) (sub_nonneg.mpr hsle)
        have he := (abs_le.mp (henv hs hsU)).2
        have hratio : 2*((square_return_pair p q u).1 : ℝ)/((square_return_pair p q u).2 : ℝ) < 2 := by
          linarith only [htest.2,hsec,hdiff,he]
        have hh := (div_lt_iff₀ hW).mp hratio
        have hhR : ((square_return_pair p q u).1 : ℝ) < (square_return_pair p q u).2 := by linarith only [hh]
        exact_mod_cast hhR
      · exact hcone (hslow hult.le).le (le_of_not_ge hs)
    by_contra hn
    have hh := hbefore u hubase (lt_of_not_ge hn); omega

/-- The full original actual-count single crossing, with a uniform corrected
rounding bracket, for all signed odd p>=5 and q>=3, including composites.
No equality at T or continuous-binomial extension is asserted. -/
theorem actual_square_displacement_threshold_bracket (p q : ℤ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q) :
    let nu : ℝ := (q : ℝ)^2
    let beta : ℝ := dbonacciPerronRoot (q.toNat^2)
    let sigma : ℝ := Real.log beta
    let alpha : ℝ := (nu-1)/(4*(q : ℝ)*sigma)
    let d : ℝ := ((nu+1)*sigma/(6*(q : ℝ)*(nu-1)))*
      (((nu^2+1)*beta-2*nu^2)/((nu+1)*beta-2*nu))
    let b : ℝ := d-1/(2*(q : ℝ))
    let c : ℝ := alpha*(p : ℝ)+1/(2*(q : ℝ))+b/(p : ℝ)
    let epsilon : ℝ := (q : ℝ)/(10*(p : ℝ)^3)
    let tmin : ℕ := ((q+1)/2).toNat
    let tlate : ℕ := ((q*p+1)/2).toNat
    ∃! T : ℕ, tmin < T ∧
      (∀ t : ℕ, tmin ≤ t → t < T → (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
      (square_return_pair p q T).1 ≤ (square_return_pair p q T).2 ∧
      (∀ t : ℕ, T < t → (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
      T ≤ tlate ∧ c-epsilon < (T : ℝ) ∧ (T : ℤ) ≤ Int.ceil (c+epsilon) := by
  let Q := q.toNat
  have hQ : 3 ≤ Q := by omega
  have hQR : (Q : ℝ) = (q : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  let M := model Q hQ
  have hMq : M.q = (q : ℝ) := hQR
  obtain ⟨T,hT,huniq⟩ := actual_square_displacement_single_crossing p q (by omega) hpo hq3 hqo
  obtain ⟨hmin,hbefore,hat,hafter,hlate⟩ := hT
  have hb := threshold_bounds M p q hp5 hpo hq3 hqo hMq T hmin hbefore hat hlate
  have hbound : center M p-eps M p < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil (center M p+eps M p) := hb
  dsimp only
  have hc : center M p =
      (((q : ℝ)^2-1)/(4*(q : ℝ)*Real.log (dbonacciPerronRoot (q.toNat^2))))*(p : ℝ)+1/(2*(q : ℝ))+
      ((((q : ℝ)^2+1)*Real.log (dbonacciPerronRoot (q.toNat^2))/(6*(q : ℝ)*((q : ℝ)^2-1)))*
        (((((q : ℝ)^2)^2+1)*dbonacciPerronRoot (q.toNat^2)-2*((q : ℝ)^2)^2)/
          (((q : ℝ)^2+1)*dbonacciPerronRoot (q.toNat^2)-2*(q : ℝ)^2))-1/(2*(q : ℝ)))/(p : ℝ) := by
    dsimp [center,M,model,alpha,kap,Q]; rw [hQR]; ring
  have heps : eps M p = (q : ℝ)/(10*(p : ℝ)^3) := by dsimp [eps]; rw [hMq]
  rw [hc,heps] at hbound
  change _ ∧ (T : ℤ) ≤ Int.ceil (_+(q : ℝ)/(10*(p : ℝ)^3)) at hbound
  refine ⟨T,⟨hmin,hbefore,hat,hafter,hlate,hbound.1,hbound.2⟩,?_⟩
  intro U hU
  exact huniq U ⟨hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,hU.2.2.2.2.1⟩

theorem scalar_coefficients (q : ℕ) (hq : 3 ≤ q) :
    let Q : ℝ := q
    let sigma := Real.log (dbonacciPerronRoot (q^2))
    let kap := (Q^2-1)/(4*Q)
    let alpha := kap/sigma
    let d := ((Q^2+1)*sigma/(6*Q*(Q^2-1)))*
      (((Q^4+1)*dbonacciPerronRoot (q^2)-2*Q^4)/
        ((Q^2+1)*dbonacciPerronRoot (q^2)-2*Q^2))
    let k := sigma*d/alpha
    let g := Real.exp sigma-Q^2*Real.exp (-Q^2*sigma)
    200/291 < sigma ∧ sigma < 7/10 ∧ 0 < d ∧ d < 7/(48*Q) ∧
    0 < kap ∧ 0 < alpha ∧ alpha*sigma = kap ∧
    (2/9)*Q ≤ kap ∧ (10/7)*kap < alpha ∧ alpha < (291/200)*kap ∧
    d ≤ Q/8 ∧ 0 < k ∧ k ≤ 1/25 ∧ Q^2*k ≤ 1/3 ∧
    d/alpha ≤ 1/16 ∧ 0 < g ∧ g ≤ 2 ∧
    Real.exp sigma+Real.exp (-Q^2*sigma) = 2 ∧
    g*k = (2*(Q^2+1)/(3*(Q^2-1)^2))*sigma^3*
      (Real.exp sigma-Q^4*Real.exp (-Q^2*sigma)) := by
  let M := model q hq
  obtain ⟨hκ,hα,hid,hκq,hαlo,hαhi,hdq,hk0,hk,hnk,hda,hg0,hg⟩ := coeff M
  refine ⟨M.sigmaLo,M.sigmaHi,M.d0,M.dHi,hκ,hα,hid,hκq,hαlo,hαhi,
    hdq,hk0,hk,hnk,hda,hg0,hg,M.root,?_⟩
  exact (square_displacement_correction q hq).2.2.2.2.2

theorem scalar_band (q : ℕ) (hq : 3 ≤ q) (P : ℝ) (hP : 5 ≤ P) :
    let Q : ℝ := q
    let sigma := Real.log (dbonacciPerronRoot (q^2))
    let alpha := ((Q^2-1)/(4*Q))/sigma
    let d := ((Q^2+1)*sigma/(6*Q*(Q^2-1)))*
      (((Q^4+1)*dbonacciPerronRoot (q^2)-2*Q^4)/
        ((Q^2+1)*dbonacciPerronRoot (q^2)-2*Q^2))
    (7/5)*((Q^2-1)/(4*Q))*P < alpha*P+d/P-Q/(10*P^3) ∧
    alpha*P+d/P+Q/(10*P^3) ≤ (3/2)*((Q^2-1)/(4*Q))*P := by
  exact band (model q hq) hP

theorem scalar_coordinates (p q : ℤ) (t : ℕ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (ht : ((q+1)/2).toNat ≤ t) :
    let Q : ℝ := q
    let P : ℝ := p
    let v := (t : ℝ)-1/(2*Q)+1/(2*Q*P)
    let s := ((Q^2-1)/(4*Q))*P/v
    0 < v ∧ (t ≤ ((q*p+1)/2).toNat → 2/5 < s) := by
  have hqn : 3 ≤ q.toNat := by omega
  have hqr : (q.toNat : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  obtain ⟨hv,_,_,_,_,hlate⟩ :=
    actual_estimates (model q.toNat hqn) p q t hp5 hpo hq3 hqo hqr ht
  simpa only [parameter,kap,centered,show (model q.toNat hqn).q = (q:ℝ) from hqr]
    using And.intro hv hlate

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
