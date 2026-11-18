/- GID: D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation.claim; result=D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation.result; claim=D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation.claim
   digest: Every strict fractional power violates the spectral Ando-Hiai implication near zero. -/

import D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
import D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/- admission_basis: open-problem-resolution (preregistration #31242).
   The private family has one fixed positive definite pair for each power,
   and that pair violates the implication on an entire interval at zero. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace D5.S3.Quantum.Matrix.SeoWadaYamazakiAndoHiaiRefutation
open Filter Topology
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation (wgm specMean cfc_diag)
open _root_.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic (symmetricTwo symmetricTwo_selfAdjoint)

/-- The universal implication asked in Problem 3.11. -/
def claim : Prop := ∀ (t q : ℝ), 0 < t → t < 1 → t ≠ 1/2 → 0 < q → q ≤ 1 →
  ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ), A.PosDef → B.PosDef →
    specMean A B t ≤ 1 → specMean (mpow A q) (mpow B q) t ≤ 1

private def p (x : ℝ) := x^3-x^5
private def r (x : ℝ) := 1-x^8
private def w (x : ℝ) := Real.sqrt (p x ^ 2+r x ^ 2-p x*r x)
private def z (x : ℝ) := Real.sqrt (3+x^2+8*x^5+x^8+3*x^10)
private def alpha (x : ℝ) := (r x/2-p x)/w x
private def correction (x : ℝ) := 3*(1-x^2)*(p x-r x)/(2*w x*(r x-2*p x+w x))
private def logarithm (x : ℝ) := Real.log ((1+x^3+x^5+x^8+w x)/z x)
private def H (u : ℝ) := alpha (Real.exp (-u/4))*(3*u/8+logarithm (Real.exp (-u/4)))

private lemma alpha_rationalization (x : ℝ) (hw : w x ≠ 0)
    (hd : r x-2*p x+w x ≠ 0) :
    alpha x-1/2 = x^3*correction x := by
  have hs : w x ^ 2 = p x ^ 2+r x ^ 2-p x*r x := by
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (p x-r x), sq_nonneg (p x), sq_nonneg (r x)]
  have hp : x^3*(1-x^2) = p x := by dsimp [p]; ring
  dsimp only [alpha, correction]
  rw [show x^3*(3*(1-x^2)*(p x-r x)/(2*w x*(r x-2*p x+w x))) =
      3*(x^3*(1-x^2))*(p x-r x)/(2*w x*(r x-2*p x+w x)) by ring]
  rw [hp]
  field_simp
  nlinarith [hs]

private lemma scalar_limit :
    Tendsto (fun u => H u-3*u/16) atTop
      (𝓝 (Real.log (2/Real.sqrt 3)/2)) := by
  let x : ℝ → ℝ := fun u => Real.exp (-u/4)
  have hx : Tendsto x atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert (tendsto_const_mul_atBot_of_neg (by norm_num : -(1/4 : ℝ) < 0)).mpr
      (tendsto_id : Tendsto (fun u : ℝ => u) atTop atTop) using 1
    ext u
    simp only [id_eq]
    ring
  have hw : ContinuousAt w 0 := by unfold w p r; fun_prop
  have hz : ContinuousAt z 0 := by unfold z; fun_prop
  have ha : ContinuousAt alpha 0 := by
    unfold alpha
    apply ContinuousAt.div
    · unfold p r; fun_prop
    · exact hw
    · norm_num [w, p, r]
  have hc : ContinuousAt correction 0 := by
    unfold correction
    apply ContinuousAt.div
    · unfold p r; fun_prop
    · exact (continuousAt_const.mul hw).mul
        ((by unfold r p; fun_prop : ContinuousAt (fun x : ℝ => r x-2*p x) 0).add hw)
    · norm_num [w, p, r]
  have hl : ContinuousAt logarithm 0 := by
    unfold logarithm
    apply ContinuousAt.log
    · apply ContinuousAt.div
      · exact (by fun_prop : ContinuousAt (fun x : ℝ => 1+x^3+x^5+x^8) 0).add hw
      · exact hz
      · norm_num [z]
    · norm_num [w, z, p, r]
  have hal : Tendsto (fun u => alpha (x u)) atTop (𝓝 (1/2)) := by
    simpa only [Function.comp_def, show alpha 0 = 1/2 by norm_num [alpha,w,p,r]] using ha.tendsto.comp hx
  have hcl : Tendsto (fun u => correction (x u)) atTop (𝓝 (-(3/4))) := by
    simpa only [Function.comp_def, show correction 0 = -(3/4) by norm_num [correction,w,p,r]] using hc.tendsto.comp hx
  have hll : Tendsto (fun u => logarithm (x u)) atTop (𝓝 (Real.log (2/Real.sqrt 3))) := by
    simpa only [Function.comp_def, show logarithm 0 = Real.log (2/Real.sqrt 3) by norm_num [logarithm,w,z,p,r]] using hl.tendsto.comp hx
  have hux : Tendsto (fun u : ℝ => u*(x u)^3) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3/4) (by norm_num) using 1
    · ext u
      simp only [Real.rpow_one, x, ← Real.exp_nat_mul]
      congr 2
      ring
  have hev : ∀ᶠ u in atTop, alpha (x u)-1/2 = (x u)^3*correction (x u) := by
    have hwv := (hw.tendsto.comp hx).eventually_ne (by norm_num [w,p,r] : w 0 ≠ 0)
    have hdv := (((by unfold r p; fun_prop : ContinuousAt (fun x : ℝ => r x-2*p x) 0).add hw).tendsto.comp hx).eventually_ne
      (by norm_num [w,p,r] : r 0-2*p 0+w 0 ≠ 0)
    filter_upwards [hwv, hdv] with u hu hv
    exact alpha_rationalization (x u) hu hv
  have hdiff : Tendsto (fun u : ℝ => u*(alpha (x u)-1/2)) atTop (𝓝 0) := by
    convert (hux.mul hcl).congr' ?_ using 1
    · norm_num
    filter_upwards [hev] with u hu
    rw [hu]
    ring
  convert ((hdiff.mul_const (3/8)).add (hal.mul hll)).congr' ?_ using 1
  · ring_nf
  filter_upwards with u
  dsimp [H, x]
  ring

private lemma separation {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ u : ℝ, 0 < u ∧ 0 < H (q*u)-q*H u := by
  have hqu : Tendsto (fun u : ℝ => q*u) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hq).mpr tendsto_id
  have hl := (scalar_limit.comp hqu).sub (scalar_limit.const_mul q)
  have hd : Tendsto (fun u : ℝ => H (q*u)-q*H u) atTop
      (𝓝 ((1-q)*Real.log (2/Real.sqrt 3)/2)) := by
    convert hl using 1
    · ext u; dsimp only [Function.comp_def]; ring
    · congr 1; ring
  have hs3 : Real.sqrt 3 < 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]
  have hpos : 0 < (1-q)*Real.log (2/Real.sqrt 3)/2 := by
    have hh : 0 < Real.log (2/Real.sqrt 3) := Real.log_pos
      ((lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr (by simpa using hs3))
    positivity
  obtain ⟨u, hu, hv⟩ := ((eventually_gt_atTop (0 : ℝ)).and (hd.eventually (eventually_gt_nhds hpos))).exists
  exact ⟨u, hu, hv⟩


private def T (h : ℝ) := 1+h^3+h^5+h^8

private lemma normalized_logs {h t v s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hv : 0 < v) (hvt : v < t) (hdet : t^2-v^2 = h^3*s^2) (b : ℝ) :
    let lp := Real.exp (b/2)*(t+v)/(h^2*s)
    let lm := Real.exp (b/2)*(t-v)/(h^2*s)
    0 < lp ∧ 0 < lm ∧
      Real.log lp = b/2-2*Real.log h+Real.log ((t+v)/s) ∧
      Real.log lp+Real.log lm = b-Real.log h := by
  dsimp only
  let lp := Real.exp (b/2)*(t+v)/(h^2*s)
  let lm := Real.exp (b/2)*(t-v)/(h^2*s)
  have hplus : 0 < t+v := by linarith
  have hminus : 0 < t-v := sub_pos.mpr hvt
  have hratio : 0 < (t+v)/s := div_pos hplus hs
  have hp : 0 < lp := by dsimp [lp]; positivity
  have hm : 0 < lm := by dsimp [lm]; positivity
  have he : (Real.exp (b/2))^2 = Real.exp b := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hprod : lp*lm = Real.exp b/h := by
    calc
      lp*lm = (Real.exp (b/2))^2*(t^2-v^2)/(h^4*s^2) := by
        dsimp [lp,lm]
        field_simp [hh.ne',hs.ne']
        <;> ring
      _ = Real.exp b/h := by
        rw [he,hdet]
        field_simp [hh.ne',hs.ne']
        <;> ring
  have hlp : Real.log lp = b/2-2*Real.log h+Real.log ((t+v)/s) := by
    have hpform : lp = (Real.exp (b/2)*((t+v)/s))/(h^2) := by
      dsimp [lp]; ring
    rw [hpform, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hratio.ne', Real.log_exp, Real.log_pow]
    ring
  refine ⟨hp,hm,hlp,?_⟩
  rw [← Real.log_mul hp.ne' hm.ne',hprod,Real.log_div (Real.exp_ne_zero _) hh.ne',
    Real.log_exp]

private lemma normalized_log_slope {h t v s a : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hv : 0 < v) (hvt : v < t) (hdet : t^2-v^2 = h^3*s^2) (b : ℝ) :
    let lp := Real.exp (b/2)*(t+v)/(h^2*s)
    let lm := Real.exp (b/2)*(t-v)/(h^2*s)
    (Real.log lp+Real.log lm)/2+(Real.log lp-Real.log lm)/2*a =
      b/2-Real.log h/2+a*(Real.log ((t+v)/s)-3*Real.log h/2) := by
  rcases normalized_logs hh hs hv hvt hdet b with ⟨_,_,hp,hsum⟩
  dsimp only at hp hsum ⊢
  linear_combination (1/2-a/2)*hsum+a*hp

private lemma logarithmic_slope (u b : ℝ)
    (hw : 0 < w (Real.exp (-u/4))) (hz : 0 < z (Real.exp (-u/4)))
    (hwt : w (Real.exp (-u/4)) < T (Real.exp (-u/4)))
    (hdet : (T (Real.exp (-u/4)))^2-(w (Real.exp (-u/4)))^2 =
      (Real.exp (-u/4))^3*(z (Real.exp (-u/4)))^2) :
    let h := Real.exp (-u/4)
    let lp := Real.exp (b/2)*(T h+w h)/(h^2*z h)
    let lm := Real.exp (b/2)*(T h-w h)/(h^2*z h)
    (Real.log lp+Real.log lm)/2+
      (Real.log lp-Real.log lm)/2*alpha h = b/2+u/8+H u := by
  have hh := normalized_log_slope (a := alpha (Real.exp (-u/4)))
    (Real.exp_pos _) hz hw hwt hdet b
  dsimp only at hh ⊢
  rw [hh,Real.log_exp]
  dsimp [H,logarithm,T]
  ring


private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private def A (u : ℝ) : Mat := diagonal ![(1 : ℂ), (Real.exp (-u/2) : ℂ)]
private def B (u b : ℝ) : Mat :=
  symmetricTwo (Real.exp b*(3*Real.exp u+Real.exp (-u))/4)
    (Real.exp b*Real.sqrt 3*(Real.exp u-Real.exp (-u))/4)
    (Real.exp b*(Real.exp u+3*Real.exp (-u))/4)
private def J : Mat := symmetricTwo (1/2) (Real.sqrt 3/2) (-1/2)

private lemma A_pos (u : ℝ) : (A u).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · norm_num [Complex.lt_def]
  · change (0 : ℂ) < (Real.exp (-u/2) : ℂ)
    exact_mod_cast Real.exp_pos (-u/2)

private lemma A_power (u q : ℝ) : mpow (A u) q = A (q*u) := by
  have he : A u = diagonal (fun i : Fin 2 => (((![1, Real.exp (-u/2)] : Fin 2 → ℝ) i) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A]
  have hp : (Real.exp (-u/2))^q = Real.exp (-(q*u)/2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [mpow, he, SpectralGeometricLogEuclideanRefutation.cfc_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, hp]

private lemma J_data : IsSelfAdjoint J ∧ J*J = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have he : (2 : ℝ)^2 = ((1/2 : ℝ)-(-1/2))^2+4*(Real.sqrt 3/2)^2 := by
    nlinarith
  have hi := HiaiHarmonicArithmetic.symmetricTwo_involution (by norm_num : (2 : ℝ) ≠ 0) he
  norm_num [J] at hi ⊢
  exact hi

private lemma B_affine (u b : ℝ) :
    B u b = ((Real.exp (b+u)+Real.exp (b-u))/2) • (1 : Mat) +
      ((Real.exp (b+u)-Real.exp (b-u))/2) • J := by
  rw [show b-u=b+(-u) by ring, Real.exp_add, Real.exp_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, J, symmetricTwo, Matrix.smul_apply, Complex.real_smul]
  all_goals push_cast
  all_goals ring

private lemma B_pos (u b : ℝ) : (B u b).PosDef := by
  have he : B u b = cfc (fun z : ℝ => Real.exp (b+u*z)) J := by
    rw [B_affine]
    have hh := QuantumTwoPointFunctionalCalculus.two_point_cfc
      (fun z : ℝ => Real.exp (b+u*z)) 0 1 J J_data.1 J_data.2
    simpa [sub_eq_add_neg] using hh.symm
  rw [he]
  exact ((cfc_isStrictlyPositive_iff _ _ (by fun_prop) J_data.1).mpr
    (fun _ _ => Real.exp_pos _)).posDef

private lemma B_power (u b q : ℝ) : mpow (B u b) q = B (q*u) (q*b) := by
  rw [mpow, B_affine, QuantumTwoPointFunctionalCalculus.two_point_cfc
    _ _ _ _ J_data.1 J_data.2]
  rw [show (Real.exp (b+u)+Real.exp (b-u))/2 +
      (Real.exp (b+u)-Real.exp (b-u))/2 = Real.exp (b+u) by ring,
    show (Real.exp (b+u)+Real.exp (b-u))/2 -
      (Real.exp (b+u)-Real.exp (b-u))/2 = Real.exp (b-u) by ring]
  rw [← Real.exp_mul, ← Real.exp_mul, B_affine,
    show (b+u)*q=q*b+q*u by ring, show (b-u)*q=q*b-q*u by ring]


private lemma input_coordinates (u b : ℝ) :
    let h := Real.exp (-u/4)
    A u = symmetricTwo 1 0 (h^2) ∧
    B u b = symmetricTwo (Real.exp b*(3+h^8)/(4*h^4))
      (Real.exp b*Real.sqrt 3*(1-h^8)/(4*h^4))
      (Real.exp b*(1+3*h^8)/(4*h^4)) := by
  let h := Real.exp (-u/4)
  change A u = symmetricTwo 1 0 (h^2) ∧
    B u b = symmetricTwo (Real.exp b*(3+h^8)/(4*h^4))
      (Real.exp b*Real.sqrt 3*(1-h^8)/(4*h^4))
      (Real.exp b*(1+3*h^8)/(4*h^4))
  have h0 : h ≠ 0 := (Real.exp_pos _).ne'
  have h2 : h^2 = Real.exp (-u/2) := by
    dsimp [h]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : h^4 = Real.exp (-u) := by
    dsimp [h]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hc : h^4 * Real.exp u = 1 := by
    rw [h4, ← Real.exp_add]
    simp
  have hp : Real.exp u = 1/h^4 := by
    apply (eq_div_iff (pow_ne_zero 4 h0)).mpr
    simpa only [mul_comm] using hc
  refine ⟨?_, ?_⟩
  · rw [h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, symmetricTwo]
  · unfold B
    rw [hp, ← h4]
    congr 1 <;> field_simp [h0] <;> ring


private lemma first_entry_slope_negative {a b c : ℝ → ℝ} {d da db dc : ℝ}
    (ha : HasDerivAt a da 0) (hb : HasDerivAt b db 0) (hc : HasDerivAt c dc 0)
    (ha0 : a 0 = 1) (hb0 : b 0 = 0) (hc0 : c 0 = d)
    (hd : d < 1) (hda : da < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (symmetricTwo (a t) (b t) (c t) : Matrix (Fin 2) (Fin 2) ℂ) ≤ 1 := by
  have hfirst : HasDerivAt (fun t => 1-a t) (-da) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ha using 1 <;> simp
  have hdet : HasDerivAt (fun t => (1-a t)*(1-c t)-(b t)^2)
      (-da*(1-d)) 0 := by
    convert (hfirst.mul ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hc)).sub
      (hb.pow 2) using 1
    simp [ha0, hb0, hc0]
  have hevFirst := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := fun t => 1-a t) (by rw [hfirst.deriv]; linarith) (by simp [ha0])
  have hevDet := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := fun t => (1-a t)*(1-c t)-(b t)^2)
    (by rw [hdet.deriv]; exact mul_pos (neg_pos.mpr hda) (sub_pos.mpr hd))
    (by simp [ha0, hb0])
  filter_upwards [hevFirst.filter_mono nhdsWithin_le_nhds,
    hevDet.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t htFirst htDet (ht : 0 < t)
  have htFirst : 0 < 1-a t := sign_eq_one_iff.mp (by simpa [ht] using htFirst)
  have htDet : 0 < (1-a t)*(1-c t)-(b t)^2 :=
    sign_eq_one_iff.mp (by simpa [ht] using htDet)
  have hpos := SpectralPower.posDef_two (1-a t) (-b t) (1-c t) htFirst
    (by simpa only [neg_sq] using htDet)
  rw [Matrix.le_iff]
  convert hpos.posSemidef using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricTwo]

private lemma first_entry_slope_positive {a b c : ℝ → ℝ} {da : ℝ}
    (ha : HasDerivAt a da 0) (ha0 : a 0 = 1) (hda : 0 < da) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ¬ (symmetricTwo (a t) (b t) (c t) : Matrix (Fin 2) (Fin 2) ℂ) ≤ 1 := by
  have hfirst : HasDerivAt (fun t => a t-1) da 0 := by
    simpa using ha.sub_const 1
  have hevFirst := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := fun t => a t-1) (by rw [hfirst.deriv]; exact hda) (by simp [ha0])
  filter_upwards [hevFirst.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t ht (htpos : 0 < t)
  have ht : 0 < a t-1 := sign_eq_one_iff.mp (by simpa [htpos] using ht)
  intro hle
  have hdiag := (Matrix.le_iff.mp hle).diag_nonneg (i := (0 : Fin 2))
  have hreal : 0 ≤ 1-a t := by
    simpa [symmetricTwo] using (Complex.nonneg_iff.mp hdiag).1
  linarith

private lemma first_entry_slope_split {a b c aq bq cq : ℝ → ℝ}
    {d da db dc dqa : ℝ}
    (ha : HasDerivAt a da 0) (hb : HasDerivAt b db 0) (hc : HasDerivAt c dc 0)
    (ha0 : a 0 = 1) (hb0 : b 0 = 0) (hc0 : c 0 = d)
    (hd : d < 1) (hda : da < 0)
    (haq : HasDerivAt aq dqa 0) (haq0 : aq 0 = 1) (hdqa : 0 < dqa) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (symmetricTwo (a t) (b t) (c t) : Matrix (Fin 2) (Fin 2) ℂ) ≤ 1 ∧
      ¬ (symmetricTwo (aq t) (bq t) (cq t) : Matrix (Fin 2) (Fin 2) ℂ) ≤ 1 := by
  have hev := (first_entry_slope_negative ha hb hc ha0 hb0 hc0 hd hda).and
    (first_entry_slope_positive (b := bq) (c := cq) haq haq0 hdqa)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro t ht htε
  apply hball
  refine ⟨?_, ht⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htε

private lemma two_point_exponent_coordinates (a b c e : ℝ)
    (he : e ≠ 0) (he2 : e^2 = (a-c)^2+4*b^2)
    (hp : 0 < (a+c+e)/2) (hm : 0 < (a+c-e)/2) :
    ∃ f g h : ℝ → ℝ,
      (∀ t, SpectralPower.mpow (symmetricTwo a b c) t = symmetricTwo (f t) (g t) (h t)) ∧
      f 0 = 1 ∧ g 0 = 0 ∧ h 0 = 1 ∧
      HasDerivAt f
        ((Real.log ((a+c+e)/2)+Real.log ((a+c-e)/2))/2 +
          (Real.log ((a+c+e)/2)-Real.log ((a+c-e)/2))/2*((a-c)/e)) 0 ∧
      HasDerivAt g
        ((Real.log ((a+c+e)/2)-Real.log ((a+c-e)/2))/2*(2*b/e)) 0 ∧
      HasDerivAt h
        ((Real.log ((a+c+e)/2)+Real.log ((a+c-e)/2))/2 +
          (Real.log ((a+c+e)/2)-Real.log ((a+c-e)/2))/2*((c-a)/e)) 0 := by
  let p := (a+c+e)/2
  let m := (a+c-e)/2
  let U : ℝ → ℝ := fun t => (p^t+m^t)/2
  let V : ℝ → ℝ := fun t => (p^t-m^t)/2
  let f : ℝ → ℝ := fun t => U t+V t*((a-c)/e)
  let g : ℝ → ℝ := fun t => V t*(2*b/e)
  let h : ℝ → ℝ := fun t => U t+V t*((c-a)/e)
  have hpd : HasDerivAt (fun t : ℝ => p^t) (Real.log p) 0 := by
    simpa using (Real.hasStrictDerivAt_const_rpow hp (0 : ℝ)).hasDerivAt
  have hmd : HasDerivAt (fun t : ℝ => m^t) (Real.log m) 0 := by
    simpa using (Real.hasStrictDerivAt_const_rpow hm (0 : ℝ)).hasDerivAt
  have hU : HasDerivAt U ((Real.log p+Real.log m)/2) 0 :=
    (hpd.add hmd).div_const 2
  have hV : HasDerivAt V ((Real.log p-Real.log m)/2) 0 :=
    (hpd.sub hmd).div_const 2
  refine ⟨f, g, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [SpectralPower.mpow, HiaiHarmonicArithmetic.symmetricTwo_cfc (fun z : ℝ => z^t) he he2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricTwo, f, g, h, U, V, p, m, Matrix.smul_apply, Complex.real_smul,
        ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
        ← Complex.ofReal_div]
  · simp [f, U, V]
  · simp [g, V]
  · simp [h, U, V]
  · exact hU.add (hV.mul_const ((a-c)/e))
  · exact hV.mul_const (2*b/e)
  · exact hU.add (hV.mul_const ((c-a)/e))

private lemma sandwich_endpoint_coordinates {f g h : ℝ → ℝ} {df dg dh : ℝ}
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0) (hh : HasDerivAt h dh 0)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) (hh0 : h 0 = 1) (d : ℝ) :
    ∃ a b c : ℝ → ℝ,
      (∀ t, symmetricTwo (f t) (g t) (h t) * symmetricTwo 1 0 d *
        symmetricTwo (f t) (g t) (h t) = symmetricTwo (a t) (b t) (c t)) ∧
      a 0 = 1 ∧ b 0 = 0 ∧ c 0 = d ∧
      HasDerivAt a (2*df) 0 ∧ HasDerivAt b (dg*(1+d)) 0 ∧
      HasDerivAt c (2*d*dh) 0 := by
  let a : ℝ → ℝ := fun t => (f t)^2+d*(g t)^2
  let b : ℝ → ℝ := fun t => g t*(f t+d*h t)
  let c : ℝ → ℝ := fun t => (g t)^2+d*(h t)^2
  refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricTwo, a, b, c, Matrix.mul_apply, Fin.sum_univ_two,
        ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_pow]
    all_goals push_cast
    all_goals ring
  · simp [a, hf0, hg0]
  · simp [b, hg0]
  · simp [c, hg0, hh0]
  · convert (hf.pow 2).add ((hg.pow 2).const_mul d) using 1 <;>
      first | rfl | simp [hf0, hg0]
  · convert hg.mul (hf.add (hh.const_mul d)) using 1 <;>
      first | rfl | simp [hf0, hg0, hh0]
  · convert (hg.pow 2).add ((hh.pow 2).const_mul d) using 1 <;>
      first | rfl | simp [hg0, hh0]; ring


private lemma geometric_bridge {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) :
    wgm A⁻¹ B (1/2) = AlternativeMeanLinearization.gmInv A B := by
  have hpow (t : ℝ) : mpow A⁻¹ t = mpow A (-t) := by
    rw [mpow, mpow, ← CFC.rpow_eq_cfc_real hA.inv.posSemidef.nonneg,
      HiaiHarmonicArithmetic.rpow_inv hA,
      CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  rw [wgm, hpow, hpow]
  norm_num
  rfl


private def X (h : ℝ) := T h+r h/2-p h
private def Y (h : ℝ) := Real.sqrt 3*r h/2
private def Z (h : ℝ) := T h-r h/2+p h
private def transport (h b : ℝ) :=
  symmetricTwo (Real.exp (b/2)*X h/(h^2*z h))
    (Real.exp (b/2)*Y h/(h^2*z h)) (Real.exp (b/2)*Z h/(h^2*z h))

private lemma radical_data {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    0 < w h ∧ 0 < z h ∧ (w h)^2 = (p h)^2+(r h)^2-p h*r h ∧
    (z h)^2 = 3+h^2+8*h^5+h^8+3*h^10 ∧ w h < T h := by
  have hr : 0 < r h := by
    dsimp [r]
    exact sub_pos.mpr (pow_lt_one₀ hh.le hh1 (by decide : (8 : ℕ) ≠ 0))
  have hw : 0 < (p h)^2+(r h)^2-p h*r h := by
    nlinarith [sq_nonneg (p h-r h/2), sq_pos_of_pos hr]
  have hz : 0 < 3+h^2+8*h^5+h^8+3*h^10 := by positivity
  have hws := Real.sq_sqrt hw.le
  have hzs := Real.sq_sqrt hz.le
  have hT : 0 < T h := by dsimp [T]; positivity
  have hid : (T h)^2-((p h)^2+(r h)^2-p h*r h) =
      h^3*(3+h^2+8*h^5+h^8+3*h^10) := by dsimp [T,p,r]; ring
  refine ⟨Real.sqrt_pos.mpr hw, Real.sqrt_pos.mpr hz, hws, hzs, ?_⟩
  dsimp [w] at *
  nlinarith [mul_pos (pow_pos hh 3) hz, Real.sqrt_nonneg ((p h)^2+(r h)^2-p h*r h)]

private lemma transport_pos {h : ℝ} (hh : 0 < h) (b : ℝ) :
    (transport h b).PosDef := by
  have hz : 0 < z h := Real.sqrt_pos.mpr (by positivity)
  have hzs : (z h)^2 = 3+h^2+8*h^5+h^8+3*h^10 := Real.sq_sqrt (by positivity)
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hX : 0 < X h := by
    have hx : X h = 3/2+2*h^5+h^8/2 := by dsimp [X,T,r,p]; ring
    rw [hx]; positivity
  apply SpectralPower.posDef_two
  · exact div_pos (mul_pos (Real.exp_pos _) hX) (by positivity)
  · have hy : (Y h)^2 = 3*(r h)^2/4 := by
      dsimp [Y]
      calc
        _ = (Real.sqrt 3)^2*(r h)^2/4 := by ring
        _ = _ := by rw [hs]
    have hid : X h*Z h-(Y h)^2 = h^3*(z h)^2 := by
      rw [hy,hzs]
      dsimp [X,Z,T,p,r]
      ring
    change 0 < (Real.exp (b/2)*X h/(h^2*z h))*
      (Real.exp (b/2)*Z h/(h^2*z h))-(Real.exp (b/2)*Y h/(h^2*z h))^2
    have he : (Real.exp (b/2)*X h/(h^2*z h))*
        (Real.exp (b/2)*Z h/(h^2*z h))-(Real.exp (b/2)*Y h/(h^2*z h))^2 =
        (Real.exp (b/2))^2/h := by
      field_simp
      nlinarith [hid]
    rw [he]; positivity

private lemma transport_riccati {h : ℝ} (hh : 0 < h) (b : ℝ) :
    transport h b * symmetricTwo 1 0 (h^2) * transport h b =
      symmetricTwo (Real.exp b*(3+h^8)/(4*h^4))
        (Real.exp b*Real.sqrt 3*(1-h^8)/(4*h^4))
        (Real.exp b*(1+3*h^8)/(4*h^4)) := by
  have hz : z h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hzs : (z h)^2 = 3+h^2+8*h^5+h^8+3*h^10 := Real.sq_sqrt (by positivity)
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have he : Real.exp (b/2)*Real.exp (b/2) = Real.exp b := by
    rw [← Real.exp_add]; congr 1; ring
  have hy : (Y h)^2 = 3*(r h)^2/4 := by
    dsimp [Y]
    calc
      _ = (Real.sqrt 3)^2*(r h)^2/4 := by ring
      _ = _ := by rw [hs]
  have h1 : (X h)^2+h^2*(Y h)^2 = (z h)^2*(3+h^8)/4 := by
    rw [hy,hzs]
    dsimp [X,T,p,r]
    ring
  have h2 : Y h*(X h+h^2*Z h) = (z h)^2*Real.sqrt 3*(1-h^8)/4 := by
    rw [hzs]
    dsimp [Y,X,Z,T,p,r]
    ring
  have h3 : (Y h)^2+h^2*(Z h)^2 = (z h)^2*(1+3*h^8)/4 := by
    rw [hy,hzs]
    dsimp [Z,T,p,r]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, symmetricTwo, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_div,
      ← Complex.ofReal_pow, ← Complex.ofReal_sub]
  all_goals norm_cast
  all_goals field_simp
  · linear_combination 4*Real.exp b*h1 +
      (4*(X h)^2+4*h^2*(Y h)^2)*he
  · linear_combination 4*Real.exp b*h2 +
      (4*Y h*(X h+h^2*Z h))*he
  · linear_combination 4*Real.exp b*h2 +
      (4*Y h*(X h+h^2*Z h))*he
  · linear_combination 4*Real.exp b*h3 +
      (4*(Y h)^2+4*h^2*(Z h)^2)*he

private lemma transport_spectrum {h : ℝ} (hh : 0 < h) (hh1 : h < 1) (b : ℝ) :
    let a := Real.exp (b/2)*X h/(h^2*z h)
    let c := Real.exp (b/2)*Z h/(h^2*z h)
    let d := Real.exp (b/2)*Y h/(h^2*z h)
    let e := 2*Real.exp (b/2)*w h/(h^2*z h)
    e ≠ 0 ∧ e^2 = (a-c)^2+4*d^2 ∧
      (a+c+e)/2 = Real.exp (b/2)*(T h+w h)/(h^2*z h) ∧
      (a+c-e)/2 = Real.exp (b/2)*(T h-w h)/(h^2*z h) ∧
      0 < (a+c+e)/2 ∧ 0 < (a+c-e)/2 ∧ (a-c)/e = alpha h ∧
      (T h)^2-(w h)^2 = h^3*(z h)^2 := by
  rcases radical_data hh hh1 with ⟨hw,hz,hws,hzs,hwt⟩
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hplus : 0 < T h+w h := by linarith
  have hminus : 0 < T h-w h := sub_pos.mpr hwt
  dsimp only
  have he : 2*Real.exp (b/2)*w h/(h^2*z h) ≠ 0 := by positivity
  refine ⟨he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    dsimp [X,Z,Y,T,p,r] at *
    nlinarith [hws,hs]
  · dsimp [X,Z]; ring
  · dsimp [X,Z]; ring
  · have hid : (Real.exp (b/2)*X h/(h^2*z h)+Real.exp (b/2)*Z h/(h^2*z h)+
        2*Real.exp (b/2)*w h/(h^2*z h))/2 =
        Real.exp (b/2)*(T h+w h)/(h^2*z h) := by dsimp [X,Z]; ring
    rw [hid]; positivity
  · have hid : (Real.exp (b/2)*X h/(h^2*z h)+Real.exp (b/2)*Z h/(h^2*z h)-
        2*Real.exp (b/2)*w h/(h^2*z h))/2 =
        Real.exp (b/2)*(T h-w h)/(h^2*z h) := by dsimp [X,Z]; ring
    rw [hid]; positivity
  · dsimp [X,Z,alpha]
    field_simp
    ring
  · rw [hws,hzs]
    dsimp [T,p,r]
    ring


private lemma mean_coordinates {u : ℝ} (hu : 0 < u) (b : ℝ) :
    ∃ a c d : ℝ → ℝ, ∃ dc dd : ℝ,
      (∀ t, specMean (A u) (B u b) t = symmetricTwo (a t) (c t) (d t)) ∧
      a 0 = 1 ∧ c 0 = 0 ∧ d 0 = Real.exp (-u/2) ∧
      HasDerivAt a (b+u/4+2*H u) 0 ∧ HasDerivAt c dc 0 ∧ HasDerivAt d dd 0 := by
  let h := Real.exp (-u/4)
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hin := input_coordinates u b
  have htr : wgm (A u)⁻¹ (B u b) (1/2) = transport h b := by
    rw [geometric_bridge (A_pos u)]
    apply AlternativeMeanLinearization.riccati_unique (A_pos u) (transport_pos hh b)
    rw [hin.1,hin.2]
    exact transport_riccati hh b
  let a := Real.exp (b/2)*X h/(h^2*z h)
  let c := Real.exp (b/2)*Y h/(h^2*z h)
  let d := Real.exp (b/2)*Z h/(h^2*z h)
  let e := 2*Real.exp (b/2)*w h/(h^2*z h)
  rcases transport_spectrum hh hh1 b with ⟨he,he2,hp,hm,hp0,hm0,hratio,hdet⟩
  obtain ⟨f,g,j,hpow,hf0,hg0,hj0,hf,hg,hj⟩ :=
    two_point_exponent_coordinates a c d e he he2 hp0 hm0
  have hfl : HasDerivAt f (b/2+u/8+H u) 0 := by
    convert hf using 1
    dsimp [a,d,c,e]
    rw [hp,hm,hratio]
    exact (logarithmic_slope u b (radical_data hh hh1).1
      (radical_data hh hh1).2.1 (radical_data hh hh1).2.2.2.2 hdet).symm
  obtain ⟨aa,bb,cc,hsand,ha0,hb0,hc0,ha,hb,hc⟩ :=
    sandwich_endpoint_coordinates hfl hg hj hf0 hg0 hj0 (Real.exp (-u/2))
  refine ⟨aa,bb,cc,_,_,?_,ha0,hb0,hc0,?_,hb,hc⟩
  · intro t
    rw [specMean,htr]
    change mpow (symmetricTwo a c d) t * A u * mpow (symmetricTwo a c d) t = _
    rw [hpow t]
    have heA : A u = symmetricTwo 1 0 (Real.exp (-u/2)) := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [A,symmetricTwo]
    rw [heA]
    exact hsand t
  · convert ha using 1 <;> ring

private theorem counterexample (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosDef ∧ B.PosDef ∧
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
        specMean A B t ≤ 1 ∧ ¬ specMean (mpow A q) (mpow B q) t ≤ 1 := by
  obtain ⟨u,hu,hsep⟩ := separation hq hq1
  let D := H (q*u)-q*H u
  have hD : 0 < D := hsep
  let b := -u/4-2*H u-D/q
  obtain ⟨a,c,d,dc,dd,he,ha0,hc0,hd0,ha,hc,hd⟩ := mean_coordinates hu b
  obtain ⟨aq,cq,dq,dcq,ddq,heq,haq0,hcq0,hdq0,haq,hcq,hdq⟩ :=
    mean_coordinates (mul_pos hq hu) (q*b)
  have hneg : b+u/4+2*H u < 0 := by
    dsimp [b]
    have hh := div_pos hD hq
    linarith
  have hpos : 0 < q*b+(q*u)/4+2*H (q*u) := by
    have heq : q*b+(q*u)/4+2*H (q*u) = D := by
      dsimp [b,D]
      field_simp
      ring
    rw [heq]
    exact hD
  obtain ⟨t₀,ht₀,ht⟩ := first_entry_slope_split ha hc hd ha0 hc0 hd0
    (Real.exp_lt_one_iff.mpr (by linarith)) hneg haq haq0 hpos
  refine ⟨A u,B u b,A_pos u,B_pos u b,t₀,ht₀,?_⟩
  intro t ht0 htt
  rcases ht t ht0 htt with ⟨hleft,hright⟩
  constructor
  · rw [he t]; exact hleft
  · rw [A_power,B_power,heq t]; exact hright

/-- Problem 3.11's universal Ando--Hiai implication is false. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨A,B,hA,hB,t₀,ht₀,hfail⟩ := counterexample (1/2) (by norm_num) (by norm_num)
  let t : ℝ := min (t₀/2) (1/4)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htt : t < t₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htquarter : t ≤ 1/4 := min_le_right _ _
  have hf := hfail t ht htt
  exact hf.2 (hclaim t (1/2) ht (by linarith) (by linarith) (by norm_num)
    (by norm_num) 2 A B hA hB hf.1)

#print axioms result

end D5.S3.Quantum.Matrix.SeoWadaYamazakiAndoHiaiRefutation
