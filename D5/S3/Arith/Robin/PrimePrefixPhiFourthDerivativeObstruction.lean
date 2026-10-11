/- GID: D5/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixPhiFourthDerivativeObstruction
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact zero values and one actual positive decreasing strictly concave curvature interval supply the exact three-point positive Laplace approximation error for every positive scalar and any two interval endpoints; every positive measure satisfies the sharp lower bound and an explicit positive Dirac atom attains it. -/

import D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-!
The literal Phi, actual rate, first derivative and zero value are consumed from
PrimorialGlobalLaplaceEnvelope. The private all-real moment differentiation
supplier generalizes the dominated rate derivative body from
PrimePrefixPhiCurvature, originally supplied by
PrimorialFirstOrderConcentrationCounterexample. It is consumed by the genuine
fourth derivative, not exported as a standalone classical supplier.
The original-object negative fourth derivative realizes the positive-axis
curvature obstruction of actual-prefix theory section 450.4. It is consumed by
one common positive, decreasing and strictly concave interval of the actual
second derivative. Every pair of endpoints in this interval and every positive
scalar has a sharp three-point positive-Laplace error; the lower bound uses only
three integrable kernels and an explicit positive Dirac atom attains it.
No analyticity, positive representation or RH estimate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
namespace D5.S3.Arith.Robin.PrimePrefixPhiFourthDerivativeObstruction
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

private def rateMoment (j : ℕ) (v : ℝ) : ℝ :=
  ∫ b in (0 : ℝ)..1, b^j*Real.exp (-v*b)

private theorem continuous_moment (j : ℕ) : Continuous (rateMoment j) := by
  unfold rateMoment
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem moment_zero (j : ℕ) : rateMoment j 0 = 1/((j : ℝ)+1) := by
  simp [rateMoment, integral_pow]

private theorem moment_zero_eq_rate : rateMoment 0 = rate := by
  funext v
  simp [rateMoment, rate]

/-- Full real parameter differentiation, including zero, with a genuine compact-input bound. -/
private theorem hasDerivAt_moment (j : ℕ) (v : ℝ) :
    HasDerivAt (rateMoment j) (-rateMoment (j+1) v) v := by
  let F : ℝ → ℝ → ℝ := fun w b => b^j*Real.exp (-w*b)
  let F' : ℝ → ℝ → ℝ := fun w b => -(b^(j+1))*Real.exp (-w*b)
  have hdiff (w b : ℝ) : HasDerivAt (fun x : ℝ => F x b) (F' w b) w := by
    have h := ((((hasDerivAt_id w).neg).mul_const b).exp).const_mul (b^j)
    apply h.congr_deriv
    dsimp [F']
    rw [pow_succ]
    ring
  have hmeas : ∀ᶠ w in 𝓝 v,
      AEStronglyMeasurable (F w) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun w =>
      (show Continuous (F w) by dsimp [F]; fun_prop).aestronglyMeasurable)
  have hint : IntervalIntegrable (F v) volume 0 1 :=
    (show Continuous (F v) by dsimp [F]; fun_prop).intervalIntegrable 0 1
  have hmeas' : AEStronglyMeasurable (F' v)
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    (show Continuous (F' v) by dsimp [F']; fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ b : ℝ ∂volume,
      b ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball v 1,
        ‖F' w b‖ ≤ Real.exp (|v|+1) := by
    apply Filter.Eventually.of_forall
    intro b hb w hw
    have hb' : b ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le zero_le_one] using hb
    have hb0 : 0 ≤ b := hb'.1.le
    have hw' : |w-v| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hw
    have hwabs : |w| ≤ |v|+1 := by
      have htri := abs_add_le (w-v) v
      have heq : w-v+v = w := by ring
      rw [heq] at htri
      linarith
    have hexp : -w*b ≤ |v|+1 := by
      calc
        -w*b ≤ |w| * b := mul_le_mul_of_nonneg_right (neg_le_abs w) hb0
        _ ≤ |w| := by nlinarith [abs_nonneg w, hb'.2]
        _ ≤ |v|+1 := hwabs
    change |-(b^(j+1)) * Real.exp (-w*b)| ≤ Real.exp (|v|+1)
    rw [abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hb0 _),
      abs_of_pos (Real.exp_pos _)]
    calc
      b^(j+1)*Real.exp (-w*b) ≤ 1*Real.exp (-w*b) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hb0 hb'.2) (Real.exp_pos _).le
      _ ≤ Real.exp (|v|+1) := by
        simpa only [one_mul] using Real.exp_le_exp.mpr hexp
  have hboundInt : IntervalIntegrable (fun _ : ℝ => Real.exp (|v|+1)) volume 0 1 :=
    intervalIntegrable_const
  have hdiffAE : ∀ᵐ b : ℝ ∂volume,
      b ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball v 1,
        HasDerivAt (fun x : ℝ => F x b) (F' w b) w :=
    Filter.Eventually.of_forall (fun b _ w _ => hdiff w b)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := v) (s := Metric.ball v 1)
    (bound := fun _ : ℝ => Real.exp (|v|+1))
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1))
    hmeas hint hmeas' hbound hboundInt hdiffAE
  change HasDerivAt
    (fun w : ℝ => ∫ b in (0 : ℝ)..1, b^j*Real.exp (-w*b))
    (-∫ b in (0 : ℝ)..1, b^(j+1)*Real.exp (-v*b)) v
  simpa only [F, F', neg_mul, intervalIntegral.integral_neg] using h.2

private def phiSecond (v : ℝ) : ℝ :=
  actualPhi v*(rateMoment 0 v^2-rateMoment 1 v)

private def phiThird (v : ℝ) : ℝ :=
  actualPhi v*(rateMoment 0 v^3-3*(rateMoment 0 v*rateMoment 1 v)+rateMoment 2 v)

private def phiFourth (v : ℝ) : ℝ :=
  actualPhi v*(rateMoment 0 v^4-6*(rateMoment 0 v^2*rateMoment 1 v)+
    3*rateMoment 1 v^2+4*(rateMoment 0 v*rateMoment 2 v)-rateMoment 3 v)

private theorem hasDerivAt_phi (v : ℝ) :
    HasDerivAt actualPhi (actualPhi v*rateMoment 0 v) v := by
  simpa only [moment_zero_eq_rate] using hasDerivAt_actualPhi v

private theorem hasDerivAt_first (v : ℝ) :
    HasDerivAt (fun w : ℝ => actualPhi w*rateMoment 0 w) (phiSecond v) v := by
  have h := (hasDerivAt_phi v).mul (hasDerivAt_moment 0 v)
  apply h.congr_deriv
  unfold phiSecond
  norm_num only [Nat.reduceAdd]
  ring

private theorem hasDerivAt_second (v : ℝ) : HasDerivAt phiSecond (phiThird v) v := by
  have hp := ((hasDerivAt_moment 0 v).pow 2).sub (hasDerivAt_moment 1 v)
  have h := (hasDerivAt_phi v).mul hp
  apply h.congr_deriv
  unfold phiThird
  simp only [Pi.sub_apply, Pi.pow_apply]
  norm_num only [Nat.reduceAdd]
  ring

private theorem hasDerivAt_third (v : ℝ) : HasDerivAt phiThird (phiFourth v) v := by
  have hp := (((hasDerivAt_moment 0 v).pow 3).sub
    (((hasDerivAt_moment 0 v).mul (hasDerivAt_moment 1 v)).const_mul 3)).add
      (hasDerivAt_moment 2 v)
  have h := (hasDerivAt_phi v).mul hp
  apply h.congr_deriv
  unfold phiFourth
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
  norm_num only [Nat.reduceAdd]
  ring

private theorem first_binding : deriv actualPhi = fun v : ℝ => actualPhi v*rateMoment 0 v := by
  funext v
  exact (hasDerivAt_phi v).deriv

private theorem second_binding : deriv (deriv actualPhi) = phiSecond := by
  rw [first_binding]
  funext v
  exact (hasDerivAt_first v).deriv

private theorem third_binding : deriv (deriv (deriv actualPhi)) = phiThird := by
  rw [second_binding]
  funext v
  exact (hasDerivAt_second v).deriv

private theorem fourth_binding : deriv (deriv (deriv (deriv actualPhi))) = phiFourth := by
  rw [third_binding]
  funext v
  exact (hasDerivAt_third v).deriv

private theorem fourth_zero : deriv (deriv (deriv (deriv actualPhi))) 0 = -(1/6 : ℝ) := by
  rw [fourth_binding]
  norm_num [phiFourth, actualPhi_zero, moment_zero]

private theorem continuous_fourth : Continuous (deriv (deriv (deriv (deriv actualPhi)))) := by
  rw [fourth_binding]
  have hp : Continuous actualPhi := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)
  have h0 := continuous_moment 0
  have h1 := continuous_moment 1
  have h2 := continuous_moment 2
  have h3 := continuous_moment 3
  unfold phiFourth
  fun_prop

private theorem continuous_second : Continuous (deriv (deriv actualPhi)) := by
  rw [second_binding]
  exact continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_second v).continuousAt)

/-- The literal fourth derivative is the second derivative of the literal curvature. -/
private theorem curvature_strict_concavity {η : ℝ}
    (hneg : ∀ v : ℝ, 0 < v → v < η →
      deriv (deriv (deriv (deriv actualPhi))) v < 0) :
    StrictConcaveOn ℝ (Ioo 0 η) (deriv (deriv actualPhi)) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo (0 : ℝ) η)
    continuous_second.continuousOn
  intro v hv
  change deriv (deriv (deriv (deriv actualPhi))) v < 0
  exact hneg v hv.1 hv.2


private theorem second_zero : deriv (deriv actualPhi) 0 = (1/2 : ℝ) := by
  rw [second_binding]
  norm_num [phiSecond, actualPhi_zero, moment_zero]

private theorem third_zero : deriv (deriv (deriv actualPhi)) 0 = -(1/6 : ℝ) := by
  rw [third_binding]
  norm_num [phiThird, actualPhi_zero, moment_zero]

private theorem continuous_third : Continuous (deriv (deriv (deriv actualPhi))) := by
  rw [third_binding]
  exact continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_third v).continuousAt)

private theorem joint_interval : ∃ η : ℝ, 0 < η ∧
    ∀ v : ℝ, 0 < v → v < η →
      0 < deriv (deriv actualPhi) v ∧
      deriv (deriv (deriv actualPhi)) v < 0 ∧
      deriv (deriv (deriv (deriv actualPhi))) v < 0 := by
  have h20 : 0 < deriv (deriv actualPhi) 0 := by rw [second_zero]; norm_num
  have h30 : deriv (deriv (deriv actualPhi)) 0 < 0 := by rw [third_zero]; norm_num
  have h40 : deriv (deriv (deriv (deriv actualPhi))) 0 < 0 := by rw [fourth_zero]; norm_num
  have h2 : ∀ᶠ v in 𝓝 (0 : ℝ), 0 < deriv (deriv actualPhi) v :=
    continuous_const.continuousAt.eventually_lt continuous_second.continuousAt h20
  have h3 : ∀ᶠ v in 𝓝 (0 : ℝ), deriv (deriv (deriv actualPhi)) v < 0 :=
    continuous_third.continuousAt.eventually_lt continuous_const.continuousAt h30
  have h4 : ∀ᶠ v in 𝓝 (0 : ℝ), deriv (deriv (deriv (deriv actualPhi))) v < 0 :=
    continuous_fourth.continuousAt.eventually_lt continuous_const.continuousAt h40
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (h2.and (h3.and h4))
  refine ⟨η, hη, fun v hv hvη => hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hv] using hvη

/-- Three genuinely integrable exponential kernels satisfy midpoint log-convexity.
This is Cauchy-Schwarz from the integrated nonnegative square. No mass or support
hypothesis is imposed on the positive measure. -/
private theorem positive_laplace_logconvex (μ : Measure ℝ) (a b : ℝ)
    (ha : Integrable (fun t : ℝ => Real.exp (-a*t)) μ)
    (hb : Integrable (fun t : ℝ => Real.exp (-b*t)) μ)
    (hm : Integrable (fun t : ℝ => Real.exp (-((a+b)/2)*t)) μ) :
    (∫ t : ℝ, Real.exp (-((a+b)/2)*t) ∂μ)^2 ≤
      (∫ t : ℝ, Real.exp (-a*t) ∂μ)*(∫ t : ℝ, Real.exp (-b*t) ∂μ) := by
  let A : ℝ := ∫ t : ℝ, Real.exp (-a*t) ∂μ
  let B : ℝ := ∫ t : ℝ, Real.exp (-b*t) ∂μ
  let M : ℝ := ∫ t : ℝ, Real.exp (-((a+b)/2)*t) ∂μ
  have hsqa (t : ℝ) : Real.exp (-a*t/2)^2 = Real.exp (-a*t) := by
    rw [pow_two, ←Real.exp_add]
    congr 1
    ring
  have hsqb (t : ℝ) : Real.exp (-b*t/2)^2 = Real.exp (-b*t) := by
    rw [pow_two, ←Real.exp_add]
    congr 1
    ring
  have hcross (t : ℝ) : Real.exp (-a*t/2)*Real.exp (-b*t/2) =
      Real.exp (-((a+b)/2)*t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hexpand (s t : ℝ) :
      (s*Real.exp (-b*t/2)-Real.exp (-a*t/2))^2 =
        s^2*Real.exp (-b*t)+(-2*s)*Real.exp (-((a+b)/2)*t)+Real.exp (-a*t) := by
    calc
      (s*Real.exp (-b*t/2)-Real.exp (-a*t/2))^2 =
          s^2*Real.exp (-b*t/2)^2+
          (-2*s)*(Real.exp (-a*t/2)*Real.exp (-b*t/2))+
          Real.exp (-a*t/2)^2 := by ring
      _ = _ := by rw [hsqa, hsqb, hcross]
  have hid (s : ℝ) :
      (∫ t : ℝ, (s*Real.exp (-b*t/2)-Real.exp (-a*t/2))^2 ∂μ) =
        B*(s*s)+(-2*M)*s+A := by
    calc
      (∫ t : ℝ, (s*Real.exp (-b*t/2)-Real.exp (-a*t/2))^2 ∂μ) =
          ∫ t : ℝ, (s^2*Real.exp (-b*t)+
            (-2*s)*Real.exp (-((a+b)/2)*t)+Real.exp (-a*t)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (hexpand s))
      _ = B*(s*s)+(-2*M)*s+A := by
        have hsum : Integrable (fun t : ℝ =>
            s^2*Real.exp (-b*t)+(-2*s)*Real.exp (-((a+b)/2)*t)) μ :=
          (hb.const_mul (s^2)).add (hm.const_mul (-2*s))
        rw [integral_add hsum ha,
          integral_add (hb.const_mul (s^2)) (hm.const_mul (-2*s)),
          integral_const_mul, integral_const_mul]
        dsimp [A, B, M]
        ring
  have hpoly (s : ℝ) : 0 ≤ B*(s*s)+(-2*M)*s+A := by
    rw [←hid s]
    exact integral_nonneg (fun t => sq_nonneg _)
  have hdis := discrim_le_zero hpoly
  dsimp [discrim] at hdis
  change M^2 ≤ A*B
  nlinarith

/-- A log-convex triple cannot lie closer than the sharp K at all three points.
The strict positivity of the shifted midpoint and its exact square identity are
precisely the algebraic conditions paid by the sharp formula in the main plan. -/
private theorem sharp_error_lower {x y z X Y Z K : ℝ}
    (hxp : 0 < x+K) (hym : 0 < y-K)
    (hZ : 0 ≤ Z)
    (hidentity : (y-K)^2 = (x+K)*(z+K)) (hCS : Y^2 ≤ X*Z) :
    K ≤ |x-X| ∨ K ≤ |y-Y| ∨ K ≤ |z-Z| := by
  by_contra h
  push_neg at h
  rcases h with ⟨hx, hy, hz⟩
  have hXupper : X < x+K := by linarith [neg_le_abs (x-X)]
  have hZupper : Z < z+K := by linarith [neg_le_abs (z-Z)]
  have hYlower : y-K < Y := by linarith [le_abs_self (y-Y)]
  have hprod : X*Z ≤ (x+K)*(z+K) :=
    mul_le_mul hXupper.le hZupper.le hZ hxp.le
  have hYsquare : 0 < (Y-(y-K))*(Y+(y-K)) :=
    mul_pos (sub_pos.mpr hYlower) (by linarith)
  nlinarith


/-- The sharp formula pays all shifted positivity and the exact exponential boundary identity. -/
private theorem sharp_data {x y z : ℝ} (hx : 0 < x) (hz : 0 < z)
    (hconc : (x+z)/2 < y) :
    let K : ℝ := (y^2-x*z)/(2*y+x+z)
    0 < K ∧ 0 < y-K ∧ (y-K)^2 = (x+K)*(z+K) := by
  let K : ℝ := (y^2-x*z)/(2*y+x+z)
  change 0 < K ∧ 0 < y-K ∧ (y-K)^2 = (x+K)*(z+K)
  have hy : 0 < y := by linarith
  have hden : 0 < 2*y+x+z := by linarith
  have hproduct : 0 < (2*y-(x+z))*(2*y+(x+z)) :=
    mul_pos (by linarith) (by linarith)
  have hnum : 0 < y^2-x*z := by nlinarith [sq_nonneg (x-z)]
  have hK : 0 < K := div_pos hnum hden
  have hmul : K*(2*y+x+z) = y^2-x*z := by
    dsimp [K]
    exact div_mul_cancel₀ _ hden.ne'
  have hminus : (y-K)*(2*y+x+z) = (x+y)*(y+z) := by nlinarith
  have hpositive : 0 < (y-K)*(2*y+x+z) := by
    rw [hminus]
    exact mul_pos (add_pos hx hy) (add_pos hy hz)
  have hyK : 0 < y-K := pos_of_mul_pos_left hpositive hden.le
  refine ⟨hK, hyK, ?_⟩
  nlinarith

/-- A positive atom, with positive location, attains the sharp three-point data. -/
private theorem positive_atom_attains {a b x y z K : ℝ} (hab : a < b)
    (hxz : z < x) (hxK : 0 < x+K) (hzK : 0 < z+K) (hyK : 0 < y-K)
    (hidentity : (y-K)^2 = (x+K)*(z+K)) :
    ∃ τ w : ℝ, 0 < τ ∧ 0 < w ∧
      w*Real.exp (-a*τ) = x+K ∧ w*Real.exp (-b*τ) = z+K ∧
      w*Real.exp (-((a+b)/2)*τ) = y-K := by
  let τ : ℝ := Real.log ((x+K)/(z+K))/(b-a)
  let w : ℝ := (x+K)*Real.exp (a*τ)
  have hratio : 1 < (x+K)/(z+K) := (lt_div_iff₀ hzK).mpr (by linarith)
  have hτ : 0 < τ := div_pos (Real.log_pos hratio) (sub_pos.mpr hab)
  have hw : 0 < w := mul_pos hxK (Real.exp_pos _)
  have ht : τ*(b-a) = Real.log ((x+K)/(z+K)) := by
    dsimp [τ]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hA : w*Real.exp (-a*τ) = x+K := by
    dsimp [w]
    rw [mul_assoc, ←Real.exp_add]
    rw [show a*τ+(-a*τ) = 0 by ring, Real.exp_zero, mul_one]
  have hB : w*Real.exp (-b*τ) = z+K := by
    have he : a*τ+(-b*τ) = -Real.log ((x+K)/(z+K)) := by nlinarith
    dsimp [w]
    rw [mul_assoc, ←Real.exp_add, he, Real.exp_neg,
      Real.exp_log (div_pos hxK hzK)]
    field_simp [hxK.ne', hzK.ne']
  let q : ℝ := w*Real.exp (-((a+b)/2)*τ)
  have hq : 0 < q := mul_pos hw (Real.exp_pos _)
  have hexp : Real.exp (-((a+b)/2)*τ)^2 =
      Real.exp (-a*τ)*Real.exp (-b*τ) := by
    rw [pow_two, ←Real.exp_add, ←Real.exp_add]
    congr 1
    ring
  have hqsq : q^2 = (x+K)*(z+K) := by
    calc
      q^2 = w^2*Real.exp (-((a+b)/2)*τ)^2 := by dsimp [q]; ring
      _ = w^2*(Real.exp (-a*τ)*Real.exp (-b*τ)) := by rw [hexp]
      _ = (w*Real.exp (-a*τ))*(w*Real.exp (-b*τ)) := by ring
      _ = (x+K)*(z+K) := by rw [hA, hB]
  have hM : q = y-K := (sq_eq_sq₀ hq.le hyK.le).mp (hqsq.trans hidentity.symm)
  exact ⟨τ, w, hτ, hw, hA, hB, hM⟩

private theorem atom_kernel_integrable (τ w v : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-v*t))
      (ENNReal.ofReal w • Measure.dirac τ) := by
  have h : Integrable (fun t : ℝ => Real.exp (-v*t)) (Measure.dirac τ) :=
    integrable_dirac (by finiteness)
  exact h.smul_measure ENNReal.ofReal_ne_top

private theorem atom_kernel_integral {τ w : ℝ} (hw : 0 < w) (v : ℝ) :
    (∫ t : ℝ, Real.exp (-v*t) ∂(ENNReal.ofReal w • Measure.dirac τ)) =
      w*Real.exp (-v*τ) := by
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hw.le, smul_eq_mul]

/-- The literal curvature supplies the exact optimum, including a genuine positive atomic measure.
One joint positive interval is fixed before arbitrary endpoints and positive scalar.
All three comparison kernels are explicitly integrable; the attaining atom has
positive mass, positive location, and genuinely integrable kernels at every real parameter. -/
theorem result :
    deriv (deriv actualPhi) 0 = (1/2 : ℝ) ∧
    deriv (deriv (deriv actualPhi)) 0 = -(1/6 : ℝ) ∧
    deriv (deriv (deriv (deriv actualPhi))) 0 = -(1/6 : ℝ) ∧
    ∃ η : ℝ, 0 < η ∧
      (∀ v : ℝ, 0 < v → v < η →
        0 < deriv (deriv actualPhi) v ∧
        deriv (deriv (deriv actualPhi)) v < 0 ∧
        deriv (deriv (deriv (deriv actualPhi))) v < 0) ∧
      ∀ a b c : ℝ, 0 < a → a < b → b < η → 0 < c →
        let m : ℝ := (a+b)/2
        let x : ℝ := c*deriv (deriv actualPhi) a
        let y : ℝ := c*deriv (deriv actualPhi) m
        let z : ℝ := c*deriv (deriv actualPhi) b
        let K : ℝ := (y^2-x*z)/(2*y+x+z)
        0 < K ∧
        (∀ μ : Measure ℝ,
          Integrable (fun t : ℝ => Real.exp (-a*t)) μ →
          Integrable (fun t : ℝ => Real.exp (-b*t)) μ →
          Integrable (fun t : ℝ => Real.exp (-m*t)) μ →
          K ≤ |x-(∫ t : ℝ, Real.exp (-a*t) ∂μ)| ∨
          K ≤ |y-(∫ t : ℝ, Real.exp (-m*t) ∂μ)| ∨
          K ≤ |z-(∫ t : ℝ, Real.exp (-b*t) ∂μ)|) ∧
        ∃ τ w : ℝ, 0 < τ ∧ 0 < w ∧
          (∀ v : ℝ, Integrable (fun t : ℝ => Real.exp (-v*t))
            (ENNReal.ofReal w • Measure.dirac τ)) ∧
          (∀ v : ℝ, (∫ t : ℝ, Real.exp (-v*t)
            ∂(ENNReal.ofReal w • Measure.dirac τ)) = w*Real.exp (-v*τ)) ∧
          |x-w*Real.exp (-a*τ)| = K ∧
          |y-w*Real.exp (-m*τ)| = K ∧
          |z-w*Real.exp (-b*τ)| = K := by
  obtain ⟨η, hη, hsign⟩ := joint_interval
  have hconc := curvature_strict_concavity
    (fun v hv hvη => (hsign v hv hvη).2.2)
  have hanti : StrictAntiOn (deriv (deriv actualPhi)) (Ioo 0 η) :=
    strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) η) continuous_second.continuousOn
      (fun v hv => (hsign v (interior_subset hv).1 (interior_subset hv).2).2.1)
  refine ⟨second_zero, third_zero, fourth_zero, η, hη, hsign, ?_⟩
  intro a b c ha hab hb hc
  let m : ℝ := (a+b)/2
  let x : ℝ := c*deriv (deriv actualPhi) a
  let y : ℝ := c*deriv (deriv actualPhi) m
  let z : ℝ := c*deriv (deriv actualPhi) b
  let K : ℝ := (y^2-x*z)/(2*y+x+z)
  have hsa : a ∈ Ioo (0 : ℝ) η := ⟨ha, hab.trans hb⟩
  have hsb : b ∈ Ioo (0 : ℝ) η := ⟨ha.trans hab, hb⟩
  have hx : 0 < x := mul_pos hc (hsign a hsa.1 hsa.2).1
  have hz : 0 < z := mul_pos hc (hsign b hsb.1 hsb.2).1
  have hxz : z < x := mul_lt_mul_of_pos_left (hanti hsa hsb hab) hc
  have hmraw := hconc.2 hsa hsb hab.ne (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at hmraw
  have hmarg : (1/2 : ℝ)*a+(1/2 : ℝ)*b = m := by dsimp [m]; ring
  rw [hmarg] at hmraw
  have hmaverage : (deriv (deriv actualPhi) a+deriv (deriv actualPhi) b)/2 <
      deriv (deriv actualPhi) m := by linarith
  have hxyz : (x+z)/2 < y := by
    have h := mul_lt_mul_of_pos_left hmaverage hc
    dsimp [x, y, z]
    nlinarith
  obtain ⟨hK, hyK, hidentity⟩ := sharp_data hx hz hxyz
  refine ⟨hK, ?_, ?_⟩
  · intro μ hia hib him
    have hCS := positive_laplace_logconvex μ a b hia hib him
    have hZ : 0 ≤ ∫ t : ℝ, Real.exp (-b*t) ∂μ :=
      integral_nonneg (fun t => (Real.exp_pos _).le)
    exact sharp_error_lower (x := x) (y := y) (z := z) (K := K)
      (add_pos hx hK) hyK hZ hidentity hCS
  · obtain ⟨τ, w, hτ, hw, hA, hB, hM⟩ := positive_atom_attains hab hxz
      (add_pos hx hK) (add_pos hz hK) hyK hidentity
    refine ⟨τ, w, hτ, hw, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun v => atom_kernel_integrable τ w v
    · exact fun v => atom_kernel_integral hw v
    · rw [hA, show x-(x+K) = -K by ring, abs_neg, abs_of_pos hK]
    · rw [hM, show y-(y-K) = K by ring, abs_of_pos hK]
    · rw [hB, show z-(z+K) = -K by ring, abs_neg, abs_of_pos hK]

end D5.S3.Arith.Robin.PrimePrefixPhiFourthDerivativeObstruction
