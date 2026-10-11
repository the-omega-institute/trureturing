/- GID: D5/S3/Arith/Robin/PrimePrefixPhiMandatoryUnitThreshold
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixPhiMandatoryUnitThreshold
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A fixed genuine unit atom strictly increases the exact three-point positive Laplace error of the literal Phi curvature; a genuine two-atom positive measure with precisely that unit mass attains the new bound on one common compact-unit window. -/

import D5.S3.Arith.Robin.PrimePrefixPhiFourthDerivativeObstruction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-!
The literal actualPhi and its first derivative remain the original
PrimorialGlobalLaplaceEnvelope supplier. The common negative-fourth-derivative
interval is consumed from PrimePrefixPhiFourthDerivativeObstruction.result.
Private moment/derivative and integrated-square/atomic helper bodies reuse that
staged supplier, with its PrimePrefixPhiCurvature and original
PrimorialFirstOrderConcentrationCounterexample attribution preserved.
The new restriction-to-the-complement-of-zero bridge retains the actual fixed
unit mass. Its stronger sharp threshold and genuine attaining measure realize
the zero-negative-Jordan-mass branch of actual-prefix theory section 461.
The complete signed optimum and actual arithmetic node supplier remain open.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
namespace D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
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

private theorem first_binding : deriv actualPhi = fun v : ℝ => actualPhi v*rateMoment 0 v := by
  funext v
  exact (hasDerivAt_phi v).deriv

private theorem second_binding : deriv (deriv actualPhi) = phiSecond := by
  rw [first_binding]
  funext v
  exact (hasDerivAt_first v).deriv

private theorem continuous_curvature : Continuous (deriv (deriv actualPhi)) := by
  rw [second_binding]
  have hp : Continuous actualPhi := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)
  have h0 := continuous_moment 0
  have h1 := continuous_moment 1
  unfold phiSecond
  fun_prop

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

private theorem atom_kernel_integral {τ w : ℝ} (hw : 0 ≤ w) (v : ℝ) :
    (∫ t : ℝ, Real.exp (-v*t) ∂(ENNReal.ofReal w • Measure.dirac τ)) =
      w*Real.exp (-v*τ) := by
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hw, smul_eq_mul]

private theorem restricted_laplace_integral {μ : Measure ℝ} {unit : ℝ}
    (hu : 0 ≤ unit) (hunit : μ {(0 : ℝ)} = ENNReal.ofReal unit) (v : ℝ)
    (hi : Integrable (fun t : ℝ => Real.exp (-v*t)) μ) :
    (∫ t : ℝ, Real.exp (-v*t) ∂(μ.restrict {(0 : ℝ)}ᶜ)) =
      (∫ t : ℝ, Real.exp (-v*t) ∂μ) - unit := by
  have hi0 : Integrable (fun t : ℝ => Real.exp (-v*t)) (μ.restrict {(0 : ℝ)}) :=
    hi.restrict
  have hic : Integrable (fun t : ℝ => Real.exp (-v*t))
      (μ.restrict {(0 : ℝ)}ᶜ) := hi.restrict
  have hsplit : μ.restrict {(0 : ℝ)} + μ.restrict {(0 : ℝ)}ᶜ = μ :=
    Measure.restrict_add_restrict_compl (measurableSet_singleton (0 : ℝ))
  have hzero : (∫ t : ℝ, Real.exp (-v*t) ∂(μ.restrict {(0 : ℝ)})) = unit := by
    rw [Measure.restrict_singleton, hunit]
    simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hu,
      mul_zero, Real.exp_zero, smul_eq_mul, mul_one]
  have htotal : (∫ t : ℝ, Real.exp (-v*t) ∂μ) =
      unit + (∫ t : ℝ, Real.exp (-v*t) ∂(μ.restrict {(0 : ℝ)}ᶜ)) := by
    calc
      _ = ∫ t : ℝ, Real.exp (-v*t)
            ∂(μ.restrict {(0 : ℝ)} + μ.restrict {(0 : ℝ)}ᶜ) := by rw [hsplit]
      _ = _ := by rw [integral_add_measure hi0 hic, hzero]
  linarith

private theorem threshold_shift {x y z unit : ℝ}
    (hs : 0 < 2*y+x+z) (hsa : 0 < 2*y+x+z-4*unit) :
    ((y-unit)^2-(x-unit)*(z-unit))/(2*y+x+z-4*unit) -
        (y^2-x*z)/(2*y+x+z) =
      unit*(x-z)^2/((2*y+x+z)*(2*y+x+z-4*unit)) := by
  rw [div_sub_div _ _ hsa.ne' hs.ne', mul_comm (2*y+x+z-4*unit) (2*y+x+z)]
  congr 1
  ring

private theorem unit_atom_integrable (unit τ w v : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-v*t))
      (ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
        ENNReal.ofReal w • Measure.dirac τ) := by
  exact (atom_kernel_integrable 0 unit v).add_measure (atom_kernel_integrable τ w v)

private theorem unit_atom_integral {unit τ w : ℝ} (hu : 0 ≤ unit) (hw : 0 ≤ w)
    (v : ℝ) :
    (∫ t : ℝ, Real.exp (-v*t) ∂(ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
      ENNReal.ofReal w • Measure.dirac τ)) = unit+w*Real.exp (-v*τ) := by
  rw [integral_add_measure (atom_kernel_integrable 0 unit v)
    (atom_kernel_integrable τ w v), atom_kernel_integral hu, atom_kernel_integral hw]
  simp only [mul_zero, Real.exp_zero, mul_one]

private theorem unit_atom_mass (unit w : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
      ENNReal.ofReal w • Measure.dirac τ) {(0 : ℝ)} = ENNReal.ofReal unit := by
  simp [Measure.add_apply, Measure.smul_apply, hτ.ne']

/-- On one common compact-unit window of the literal curvature, the true fixed
unit mass gives a strictly stronger exact three-point error, and a genuine positive
two-atom measure with precisely that unit mass attains it. -/
theorem result :
    ∀ c aMax : ℝ, 0 < c → 0 ≤ aMax → aMax < c/2 →
      ∃ η : ℝ, 0 < η ∧
        ∀ p q unit : ℝ, 0 < p → p < q → q < η → 0 ≤ unit → unit ≤ aMax →
          let m : ℝ := (p+q)/2
          let x : ℝ := c*deriv (deriv actualPhi) p
          let y : ℝ := c*deriv (deriv actualPhi) m
          let z : ℝ := c*deriv (deriv actualPhi) q
          let S : ℝ := 2*y+x+z
          let K : ℝ := (y^2-x*z)/S
          let Ka : ℝ := ((y-unit)^2-(x-unit)*(z-unit))/(S-4*unit)
          0 < K ∧ 0 < Ka ∧
          Ka-K = unit*(x-z)^2/(S*(S-4*unit)) ∧
          (0 < unit → K < Ka) ∧
          (∀ μ : Measure ℝ, μ {(0 : ℝ)} = ENNReal.ofReal unit →
            Integrable (fun t : ℝ => Real.exp (-p*t)) μ →
            Integrable (fun t : ℝ => Real.exp (-q*t)) μ →
            Integrable (fun t : ℝ => Real.exp (-m*t)) μ →
            Ka ≤ |x-(∫ t : ℝ, Real.exp (-p*t) ∂μ)| ∨
            Ka ≤ |y-(∫ t : ℝ, Real.exp (-m*t) ∂μ)| ∨
            Ka ≤ |z-(∫ t : ℝ, Real.exp (-q*t) ∂μ)|) ∧
          ∃ τ w : ℝ, 0 < τ ∧ 0 < w ∧
            (ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
              ENNReal.ofReal w • Measure.dirac τ) {(0 : ℝ)} = ENNReal.ofReal unit ∧
            (∀ v : ℝ, Integrable (fun t : ℝ => Real.exp (-v*t))
              (ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
                ENNReal.ofReal w • Measure.dirac τ)) ∧
            (∀ v : ℝ, (∫ t : ℝ, Real.exp (-v*t)
              ∂(ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
                ENNReal.ofReal w • Measure.dirac τ)) = unit+w*Real.exp (-v*τ)) ∧
            |x-(∫ t : ℝ, Real.exp (-p*t)
              ∂(ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
                ENNReal.ofReal w • Measure.dirac τ))| = Ka ∧
            |y-(∫ t : ℝ, Real.exp (-m*t)
              ∂(ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
                ENNReal.ofReal w • Measure.dirac τ))| = Ka ∧
            |z-(∫ t : ℝ, Real.exp (-q*t)
              ∂(ENNReal.ofReal unit • Measure.dirac (0 : ℝ) +
                ENNReal.ofReal w • Measure.dirac τ))| = Ka := by
  intro c aMax hc hMax0 hMax
  obtain ⟨hB0, _, _, η0, hη0, hsign, _⟩ :=
    D5.S3.Arith.Robin.PrimePrefixPhiFourthDerivativeObstruction.result
  have hbudget0 : aMax < c*deriv (deriv actualPhi) 0 := by
    rw [hB0]
    nlinarith
  have hbudget : ∀ᶠ v in 𝓝 (0 : ℝ), aMax < c*deriv (deriv actualPhi) v :=
    continuous_const.continuousAt.eventually_lt
      (continuous_const.mul continuous_curvature).continuousAt hbudget0
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hbudget
  let η : ℝ := min η0 δ
  have hη : 0 < η := lt_min hη0 hδ
  have hsignη (v : ℝ) (hv : 0 < v) (hvη : v < η) :=
    hsign v hv (hvη.trans_le (min_le_left η0 δ))
  have hconc : StrictConcaveOn ℝ (Ioo 0 η) (deriv (deriv actualPhi)) := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Ioo (0 : ℝ) η)
      continuous_curvature.continuousOn
    intro v hv
    exact (hsignη v hv.1 hv.2).2.2
  have hanti : StrictAntiOn (deriv (deriv actualPhi)) (Ioo 0 η) :=
    strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) η)
      continuous_curvature.continuousOn
      (fun v hv => (hsignη v (interior_subset hv).1 (interior_subset hv).2).2.1)
  refine ⟨η, hη, ?_⟩
  intro p q unit hp hpq hqη hu hunitMax
  let m : ℝ := (p+q)/2
  let x : ℝ := c*deriv (deriv actualPhi) p
  let y : ℝ := c*deriv (deriv actualPhi) m
  let z : ℝ := c*deriv (deriv actualPhi) q
  let S : ℝ := 2*y+x+z
  let K : ℝ := (y^2-x*z)/S
  let Ka : ℝ := ((y-unit)^2-(x-unit)*(z-unit))/(S-4*unit)
  have hpη : p < η := hpq.trans hqη
  have hbp : aMax < x := by
    apply hball
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hp] using
      hpη.trans_le (min_le_right η0 δ)
  have hbq : aMax < z := by
    apply hball
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (hp.trans hpq)] using
      hqη.trans_le (min_le_right η0 δ)
  have hxunit : 0 < x-unit := by linarith
  have hzunit : 0 < z-unit := by linarith
  have hx : 0 < x := by linarith
  have hz : 0 < z := by linarith
  have hsp : p ∈ Ioo (0 : ℝ) η := ⟨hp, hpη⟩
  have hsq : q ∈ Ioo (0 : ℝ) η := ⟨hp.trans hpq, hqη⟩
  have hxz : z < x := mul_lt_mul_of_pos_left (hanti hsp hsq hpq) hc
  have hmraw := hconc.2 hsp hsq hpq.ne (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at hmraw
  have hmarg : (1/2 : ℝ)*p+(1/2 : ℝ)*q = m := by dsimp [m]; ring
  rw [hmarg] at hmraw
  have hmaverage : (deriv (deriv actualPhi) p+deriv (deriv actualPhi) q)/2 <
      deriv (deriv actualPhi) m := by linarith
  have hxyz : (x+z)/2 < y := by
    have h := mul_lt_mul_of_pos_left hmaverage hc
    dsimp [x, y, z]
    nlinarith
  have hxyzunit : ((x-unit)+(z-unit))/2 < y-unit := by linarith
  have hK : 0 < K := (sharp_data hx hz hxyz).1
  have hdenEq : 2*(y-unit)+(x-unit)+(z-unit) = S-4*unit := by dsimp [S]; ring
  have hdata : 0 < Ka ∧ 0 < y-unit-Ka ∧
      (y-unit-Ka)^2 = ((x-unit)+Ka)*((z-unit)+Ka) := by
    dsimp only [Ka]
    rw [←hdenEq]
    exact sharp_data hxunit hzunit hxyzunit
  obtain ⟨hKa, hyKa, hidentity⟩ := hdata
  have hS : 0 < S := by dsimp [S]; linarith
  have hSa : 0 < S-4*unit := by dsimp [S]; linarith
  have hshift : Ka-K = unit*(x-z)^2/(S*(S-4*unit)) :=
    threshold_shift hS hSa
  refine ⟨hK, hKa, hshift, ?_, ?_, ?_⟩
  · intro hunit
    have hsqpos : 0 < (x-z)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxz.ne')
    have hgap : 0 < unit*(x-z)^2/(S*(S-4*unit)) :=
      div_pos (mul_pos hunit hsqpos) (mul_pos hS hSa)
    rw [←hshift] at hgap
    exact sub_pos.mp hgap
  · intro μ hmass hip hiq him
    let ν : Measure ℝ := μ.restrict {(0 : ℝ)}ᶜ
    have hCS := positive_laplace_logconvex ν p q hip.restrict hiq.restrict him.restrict
    have hZ : 0 ≤ ∫ t : ℝ, Real.exp (-q*t) ∂ν :=
      integral_nonneg (fun t => (Real.exp_pos _).le)
    have hlower := sharp_error_lower (x := x-unit) (y := y-unit) (z := z-unit)
      (K := Ka) (add_pos hxunit hKa) hyKa hZ hidentity hCS
    have hrp := restricted_laplace_integral hu hmass p hip
    have hrq := restricted_laplace_integral hu hmass q hiq
    have hrm := restricted_laplace_integral hu hmass m him
    change Ka ≤ |(x-unit)-(∫ t : ℝ, Real.exp (-p*t)
        ∂(μ.restrict {(0 : ℝ)}ᶜ))| ∨
      Ka ≤ |(y-unit)-(∫ t : ℝ, Real.exp (-m*t)
        ∂(μ.restrict {(0 : ℝ)}ᶜ))| ∨
      Ka ≤ |(z-unit)-(∫ t : ℝ, Real.exp (-q*t)
        ∂(μ.restrict {(0 : ℝ)}ᶜ))| at hlower
    rw [hrp, hrm, hrq] at hlower
    simpa only [sub_sub_sub_cancel_right] using hlower
  · obtain ⟨τ, w, hτ, hw, hA, hB, hM⟩ := positive_atom_attains hpq
      (by linarith : z-unit < x-unit) (add_pos hxunit hKa) (add_pos hzunit hKa)
      hyKa hidentity
    refine ⟨τ, w, hτ, hw, unit_atom_mass unit w hτ,
      fun v => unit_atom_integrable unit τ w v,
      fun v => unit_atom_integral hu hw.le v, ?_, ?_, ?_⟩
    · rw [unit_atom_integral hu hw.le p, hA,
        show x-(unit+(x-unit+Ka)) = -Ka by ring, abs_neg, abs_of_pos hKa]
    · rw [unit_atom_integral hu hw.le m, hM,
        show y-(unit+(y-unit-Ka)) = Ka by ring, abs_of_pos hKa]
    · rw [unit_atom_integral hu hw.le q, hB,
        show z-(unit+(z-unit+Ka)) = -Ka by ring, abs_neg, abs_of_pos hKa]

end D5.S3.Arith.Robin.PrimePrefixPhiMandatoryUnitThreshold
