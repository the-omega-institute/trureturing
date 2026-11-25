/- GID: D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/FinitePairGaussianLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pair fourth moments certify the central Gaussian score profile and its envelope. -/

import D5.S3.Fourier.Concentration.FejerCollisionVariance
import D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Finset Filter
open scoped Topology
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open D5.S3.Weil.DirichletPolynomialMeanSquare

noncomputable section

namespace D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit

private theorem cos_global_quartic (x : ℝ) :
    0 ≤ Real.cos x - (1-x^2/2) ∧ Real.cos x - (1-x^2/2) ≤ x^4/24 := by
  constructor
  · exact sub_nonneg.mpr Real.one_sub_sq_div_two_le_cos
  · have h := scaled_sin_sq_error (x/2) 1 one_ne_zero
    simp only [mul_one, one_pow, div_one] at h
    have hcos := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at hcos
    have hleft := (abs_le.mp h).1
    rw [hcos]
    linarith only [hleft]

private theorem score_square_cosine {J : Type*} [Fintype J]
    (g w : J → ℝ) (t : ℝ) :
    ‖complexScore g w t‖^2 = ∑ i, ∑ j, w i*w j*Real.cos ((g i-g j)*t) := by
  have hr := congrArg Complex.re (Complex.mul_conj' (complexScore g w t))
  rw [← Complex.ofReal_pow,Complex.ofReal_re] at hr
  rw [← hr]
  unfold complexScore
  rw [map_sum, sum_mul]
  simp_rw [mul_sum, Complex.re_sum, map_mul, Complex.conj_ofReal]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have he : starRingEnd ℂ (phase (g j) t) = phase (-g j) t := by
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [he, show ((w i:ℂ)*phase (g i) t)*((w j:ℂ)*phase (-g j) t) =
    ((w i:ℂ)*(w j:ℂ))*(phase (g i) t*phase (-g j) t) by ring,
    ← character_add]
  rw [show g i + -g j = g i-g j by ring]
  simp [phase, Complex.mul_re, Complex.exp_re, Complex.mul_im]

/-- The moment of the ordered pair-frequency differences. -/
def pairMoment {J : Type*} [Fintype J] (g w : J → ℝ) (p : ℕ) : ℝ :=
  ∑ i, ∑ j, w i*w j*(g i-g j)^p

/-- Global quadratic approximation to the squared score with controlled quartic remainder. -/
theorem score_quartic {J : Type*} [Fintype J] (g w : J → ℝ) (hw : ∀ i j, 0≤w i*w j) (t : ℝ) :
    let square := fun z : ℂ => ‖z‖^2
    0 ≤ square (complexScore g w t)-((∑ i, w i)^2-pairMoment g w 2*t^2/2) ∧
    square (complexScore g w t)-((∑ i, w i)^2-pairMoment g w 2*t^2/2) ≤ pairMoment g w 4*t^4/24 := by
  dsimp
  rw [score_square_cosine]
  have hsum : ∑ i, ∑ j, w i*w j = (∑ i, w i)^2 := by
    rw [pow_two,sum_mul]
    simp_rw [mul_sum]
  have hquad : ∑ i, ∑ j, w i*w j*(1-((g i-g j)*t)^2/2) = (∑ i, w i)^2-pairMoment g w 2*t^2/2 := by
    unfold pairMoment
    simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [hsum]
    congr 1
    simp_rw [div_eq_mul_inv,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hquart : ∑ i, ∑ j, w i*w j*(((g i-g j)*t)^4/24) = pairMoment g w 4*t^4/24 := by
    unfold pairMoment
    simp_rw [div_eq_mul_inv,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [← hquad,← hquart]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw i j) (cos_global_quartic _).1
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (cos_global_quartic _).2 (hw i j)


private theorem scaled_quartic {J : Type*} [Fintype J] (g w : J → ℝ)
    (hw : ∀ i j, 0≤w i*w j) (hW : ∑ i, w i=1) (n : ℕ) (hn : 0<n)
    (hm : 0<pairMoment g w 2) (u : ℝ) :
    let M := pairMoment g w 2
    let R := pairMoment g w 4 / ((n:ℝ)*M^2)
    let s := Real.sqrt ((n:ℝ)*M/2)
    let Q := ‖complexScore g w (u/s)‖^2
    0 ≤ (n:ℝ)*(Q-1)+u^2 ∧ (n:ℝ)*(Q-1)+u^2 ≤ (u^4/6)*R := by
  intro M R s Q
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hms : 0<M := hm
  have hs2 : s^2 = (n:ℝ)*M/2 := Real.sq_sqrt (div_nonneg (mul_nonneg hn'.le hms.le) (by norm_num))
  have hq := score_quartic g w hw (u/s)
  rw [hW,one_pow] at hq
  change 0≤Q-(1-M*(u/s)^2/2) ∧
    Q-(1-M*(u/s)^2/2) ≤ pairMoment g w 4 * (u/s)^4/24 at hq
  have he : (n:ℝ)*(M*(u/s)^2/2) = u^2 := by
    rw [div_pow,hs2]
    field_simp [hn'.ne',hms.ne']
  have he4 : (n:ℝ)*(pairMoment g w 4*(u/s)^4/24) = (u^4/6)*R := by
    rw [div_pow,show s^4 = (s^2)^2 by ring,hs2]
    dsimp [R]
    field_simp [hn'.ne',hms.ne']
    ring
  constructor
  · have hh := mul_nonneg hn'.le hq.1
    linarith only [hh,he]
  · have hh := mul_le_mul_of_nonneg_left hq.2 hn'.le
    rw [he4] at hh
    linarith only [hh,he]

/-- A vanishing normalized pair fourth moment implies the central Gaussian power limit. -/
theorem score_gaussian_limit {J : ℕ → Type*} [∀ n, Fintype (J n)] (g w : ∀ n, J n → ℝ)
    (hw : ∀ᶠ n in atTop, ∀ i j, 0≤w n i*w n j) (hW : ∀ᶠ n in atTop, ∑ j, w n j = 1)
    (hM : ∀ᶠ n in atTop, 0 < pairMoment (g n) (w n) 2)
    (hR : Tendsto (fun n => pairMoment (g n) (w n) 4 /
      ((n:ℝ)*pairMoment (g n) (w n) 2^2)) atTop (𝓝 0)) (u : ℝ) :
    let gaussian := fun t : ℝ => Real.exp t
    Tendsto (fun n => ‖complexScore (g n) (w n)
      (u/Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2))‖^(2*n)) atTop (𝓝 (gaussian (-u^2))) := by
  intro gaussian
  let M := fun n => pairMoment (g n) (w n) 2
  let R := fun n : ℕ => pairMoment (g n) (w n) 4 / ((n:ℝ)*M n^2)
  let s := fun n : ℕ => Real.sqrt ((n:ℝ)*M n/2)
  let Q := fun n => ‖complexScore (g n) (w n) (u/s n)‖^2
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ (n:ℝ)*(Q n-1)+u^2 ∧ (n:ℝ)*(Q n-1)+u^2 ≤ (u^4/6)*R n := by
    filter_upwards [hM,eventually_gt_atTop (0:ℕ),hw,hW] with n hm hn hwn hmass
    exact scaled_quartic (g n) (w n) hwn hmass n hn hm u
  have hupper : Tendsto (fun n => (u^4/6)*R n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hR.const_mul (u^4/6))
  have herr : Tendsto (fun n : ℕ => (n:ℝ)*(Q n-1)+u^2) atTop (𝓝 0) :=
    squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hupper
  have harg : Tendsto (fun n : ℕ => (n:ℝ)*(Q n-1)) atTop (𝓝 (-u^2)) := by
    have h := herr.sub_const (u^2)
    have he : (fun n : ℕ => (n:ℝ)*(Q n-1)+u^2-u^2) = (fun n : ℕ => (n:ℝ)*(Q n-1)) := by
      funext n
      ring
    rw [he,zero_sub] at h
    exact h
  have hp := Real.tendsto_one_add_pow_exp_of_tendsto harg
  apply hp.congr'
  filter_upwards [] with n
  simp [Q,s,M,pow_mul]


/-- The fourth-moment condition gives an integrable Gaussian envelope on the central window. -/
theorem score_gaussian_envelope {J : Type*} [Fintype J] (g w : J → ℝ)
    (hw : ∀ i j, 0≤w i*w j) (hW : ∑ i, w i=1) (n : ℕ) (hn : 0<n)
    (hm : 0<pairMoment g w 2) (u : ℝ)
    (hwin : u^2*pairMoment g w 4 ≤ 3*(n:ℝ)*pairMoment g w 2^2) :
    let gaussian := fun t : ℝ => Real.exp t
    ‖complexScore g w (u/Real.sqrt ((n:ℝ)*pairMoment g w 2/2))‖^(2*n) ≤
      gaussian (-u^2/2) := by
  intro gaussian
  let M := pairMoment g w 2
  let R := pairMoment g w 4 / ((n:ℝ)*M^2)
  let s := Real.sqrt ((n:ℝ)*M/2)
  let Q := ‖complexScore g w (u/s)‖^2
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hM : 0<M := hm
  have hden : 0<(n:ℝ)*M^2 := mul_pos hn' (sq_pos_of_pos hM)
  have hbound := (scaled_quartic g w hw hW n hn hm u).2
  change (n:ℝ)*(Q-1)+u^2 ≤ (u^4/6)*R at hbound
  have hR : u^2*R ≤ 3 := by
    dsimp [R]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by convert hwin using 1; ring)
  have hquart : (u^4/6)*R ≤ u^2/2 := by
    have h := mul_le_mul_of_nonneg_left hR (by positivity : 0≤u^2/6)
    convert h using 1 <;> ring
  have hQ : Q ≤ 1 + (-u^2/2)/(n:ℝ) := by
    have h := hbound.trans hquart
    have ht : (n:ℝ)*Q ≤ (n:ℝ) + (-u^2/2) := by linarith only [h]
    have he : (n:ℝ)*(1+(-u^2/2)/(n:ℝ)) = (n:ℝ)+(-u^2/2) := by field_simp
    apply (mul_le_mul_iff_of_pos_left hn').mp
    rw [he]; exact ht
  have hE := hQ.trans (by simpa only [add_comm] using Real.add_one_le_exp ((-u^2/2)/(n:ℝ)))
  have hp := pow_le_pow_left₀ (by dsimp [Q]; positivity) hE n
  change Q^n ≤ _ at hp
  rw [← Real.exp_nat_mul] at hp
  have he : (n:ℝ)*((-u^2/2)/(n:ℝ)) = -u^2/2 := by field_simp
  rw [he] at hp
  simpa [Q,s,M,pow_mul] using hp

#print axioms score_quartic
#print axioms score_gaussian_limit
#print axioms score_gaussian_envelope

end D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
