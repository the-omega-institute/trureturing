/- GID: D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Parameter, Green, source and reflection identities for the original tail derivative vector. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorResiduals

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open OriginalPrimalTailProjection OriginalPrimalTailResponse
open NormalizedJensenDegreeLowering SourceJensenIntegralExtension
open private primalJet_zero primalJet_deriv shiftedBudget shifted_summable scale_summable
  flux_summable tailJet_summable_ray tailJet_deriv tailJet_continuous tailJet_eq_iterated
  adjoint_formula adjoint_deriv adjoint_second_deriv adjoint_square flux_eq from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private mode_residual_integral residual_series later_mode_sum scale_gap full_flux_lower
  originalCoefficient originalPolynomial original_coefficient_recurrence
  original_polynomial_eval original_polynomial_origin original_polynomial_ode
  original_polynomial_energy polynomial_jet polynomial_adjoint
  polynomial_adjoint_deriv_limit polynomial_adjoint_square_integrable original_green
  original_moment_bridge original_source_split original_full_source exp_increment jet_one jet_two from
  D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

open private adjoint_linear from
  D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorResiduals

private def parameterPolynomial (n:ℕ) (t:ℝ) : ℝ[X] :=
  ∑ j∈Finset.range (n+1),C (originalCoefficient n 1 j*(j:ℝ)*t^(j-1))*X^(2*j)

/-- The coefficientwise fixed-degree parameter derivative, including the top coefficient. -/
def originalb (n:ℕ) (t x:ℝ) : ℝ := (parameterPolynomial n t).eval x

private theorem coefficient_factor (n j:ℕ) (t:ℝ) :
    originalCoefficient n t j=originalCoefficient n 1 j*t^j := by
  dsimp [originalCoefficient]
  simp only [one_pow,mul_one]
  ring

private theorem parameter_derivative (n:ℕ) (t x:ℝ) :
    HasDerivAt (fun u:ℝ => originalB n u x) (originalb n t x) t := by
  have hd (j:ℕ) : HasDerivAt
      (fun u:ℝ => originalCoefficient n 1 j*x^(2*j)*u^j)
      (originalCoefficient n 1 j*x^(2*j)*((j:ℝ)*t^(j-1))) t :=
    by simpa only [id_eq,Pi.pow_apply,mul_one] using
      ((hasDerivAt_id t).pow j).const_mul (originalCoefficient n 1 j*x^(2*j))
  convert! HasDerivAt.fun_sum (u:=Finset.range (n+1)) (fun j _ => hd j) using 1
  · ext u
    simp only [originalB]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [originalCoefficient]
    simp only [one_pow,mul_one]
    ring
  · simp only [originalb,parameterPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem parameter_spatial_identity (n:ℕ) (t:ℝ) :
    C (2*t)*parameterPolynomial n t=X*(originalPolynomial n t).derivative := by
  simp only [parameterPolynomial,originalPolynomial,derivative_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficient_factor n j t]
  cases j with
  | zero => simp
  | succ j =>
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,derivative_pow,derivative_X,mul_one]
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,
      show 2*(j+1)=2*j+2 by omega,show 2*j+2-1=2*j+1 by omega,
      Nat.cast_add,Nat.cast_mul,Nat.cast_one,pow_succ,C_mul,C_add]
    norm_num
    ring

private theorem parameter_origin (n:ℕ) (t:ℝ) :
    (parameterPolynomial n t).eval 0=0 ∧ (parameterPolynomial n t).derivative.eval 0=0 := by
  constructor
  · simp only [parameterPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply Finset.sum_eq_zero
    intro j _
    cases j <;> simp
  · simp only [parameterPolynomial,derivative_sum,derivative_mul,derivative_C,
      zero_mul,zero_add,derivative_pow,derivative_X,mul_one,
      eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply Finset.sum_eq_zero
    intro j _
    cases j with
    | zero => simp
    | succ j =>
      have h:2*(j+1)-1≠0 := by omega
      simp [h]

private theorem tester_equations {n:ℕ} (hn:1≤n) {t:ℝ} (ht:0<t) :
    let p:=originalPolynomial n t
    let b:=parameterPolynomial n t
    let α:=t/(2*(n:ℝ))
    b.derivative.derivative-C α*(X*b.derivative)+C (t-2*α)*b= -p ∧
    (X^2*p).derivative.derivative-C α*(X*(X^2*p).derivative)+C (t+2*α)*(X^2*p)=
      C 2*p+C (8*t)*b := by
  let p:=originalPolynomial n t
  let b:=parameterPolynomial n t
  let α:=t/(2*(n:ℝ))
  have hode:=original_polynomial_ode hn t
  change p.derivative.derivative-C α*(X*p.derivative)+C t*p=0 at hode
  have hdiff:=congrArg Polynomial.derivative hode
  simp only [derivative_sub,derivative_add,derivative_mul,derivative_C,derivative_X,
    zero_mul,mul_zero,zero_add,add_zero,derivative_zero] at hdiff
  have hbp:=parameter_spatial_identity n t
  change C (2*t)*b=X*p.derivative at hbp
  have hb1:=congrArg Polynomial.derivative hbp
  have hb2:=congrArg (fun q:ℝ[X] => q.derivative.derivative) hbp
  simp only [derivative_mul,derivative_C,derivative_X,zero_mul,zero_add,mul_zero,
    add_zero,one_mul,derivative_add] at hb1 hb2
  change _ ∧ _
  constructor
  · have hpoly : C (2*t)*(b.derivative.derivative-C α*(X*b.derivative)+C (t-2*α)*b+p)=0 := by
      simp only [C_sub,C_mul,C_ofNat] at hode hdiff hbp hb1 hb2 ⊢
      linear_combination hb2-C α*X*hb1+(C t-2*C α)*hbp+2*hode+X*hdiff
    have hc:C (2*t)≠(0:ℝ[X]) := by simp; positivity
    have h:= (mul_eq_zero.mp hpoly).resolve_left hc
    linear_combination h
  · simp only [derivative_mul,derivative_pow,derivative_X,derivative_add,derivative_C,
      zero_mul,mul_zero,zero_add,add_zero,one_mul,mul_one,pow_zero,pow_one]
    simp only [C_add,C_mul,C_ofNat] at hode hbp ⊢
    norm_num
    simp only [C_ofNat]
    linear_combination X^2*hode-4*hbp

private theorem spatial_derivative_bound {n:ℕ} (hn:1≤n) {t x:ℝ}
    (ht:0<t) (hx:0≤x) :
    |(originalPolynomial n t).derivative.eval x|≤t*x*exp ((t/(2*(n:ℝ)))*x^2/2) := by
  let p:=originalPolynomial n t
  let α:=t/(2*(n:ℝ))
  let f:=fun y:ℝ => exp (-α*y^2/2)*p.derivative.eval y
  let g:=fun y:ℝ => -t*exp (-α*y^2/2)*p.eval y
  have hd (y:ℝ):HasDerivAt f (g y) y := by
    have he:HasDerivAt (fun z:ℝ => exp (-α*z^2/2))
        ((-α*y)*exp (-α*y^2/2)) y := by
      convert! ((((hasDerivAt_id y).pow 2).const_mul (-α)).div_const 2).exp using 1 <;> simp only [id_eq,Pi.pow_apply] <;> ring
    have ho:=congrArg (fun q:ℝ[X] => q.eval y) (original_polynomial_ode hn t)
    simp only [eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_zero] at ho
    convert! he.mul (p.derivative.hasDerivAt y) using 1
    dsimp [f,g,p,α] at *
    linear_combination -exp (-(t/(2*(n:ℝ)))*y^2/2)*ho
  have hg:Continuous g := by dsimp [g]; fun_prop
  have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=x)
    (fun y _ => hd y) (hg.intervalIntegrable 0 x)
  have hf0:f 0=0 := by dsimp [f,p]; rw [(original_polynomial_origin n t).2]; simp
  rw [hf0,sub_zero] at he
  have hb (y:ℝ) (hy:y∈Set.uIoc (0:ℝ) x) : ‖g y‖≤t := by
    have hy0:0≤y := by rw [uIoc_of_le hx] at hy; exact hy.1.le
    have h:=mul_le_mul_of_nonneg_left (original_polynomial_energy hn ht hy0)
      (exp_pos (-α*y^2/2)).le
    have hex:exp (-α*y^2/2)*exp (α*y^2/2)=1 := by rw [←exp_add]; ring_nf; simp
    have h':exp (-α*y^2/2)*|p.eval y|≤1 := by simpa only [p,α,hex] using h
    dsimp [g]
    simp only [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos ht,abs_of_pos (exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left h' ht.le]
  have hnorm:=intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [he] at hnorm
  have hf:|f x|≤t*x := by simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hx] using hnorm
  have h:=mul_le_mul_of_nonneg_left hf (exp_pos (α*x^2/2)).le
  have hid:exp (α*x^2/2)*|f x|=|p.derivative.eval x| := by
    dsimp [f]
    rw [abs_mul,abs_of_pos (exp_pos _),←mul_assoc,←exp_add]
    ring_nf
    simp
  rw [hid] at h
  convert! h using 1 <;> ring

private theorem parameter_bound {n:ℕ} (hn:1≤n) {t x:ℝ} (ht:0<t) (hx:0≤x) :
    |originalb n t x|≤x^2*exp ((t/(2*(n:ℝ)))*x^2/2)/2 := by
  have he:=congrArg (fun q:ℝ[X] => q.eval x) (parameter_spatial_identity n t)
  simp only [eval_mul,eval_C,eval_X] at he
  change 2*t*originalb n t x=x*(originalPolynomial n t).derivative.eval x at he
  have h:=mul_le_mul_of_nonneg_left (spatial_derivative_bound hn ht hx) hx
  have ha:=congrArg abs he
  simp only [abs_mul,abs_of_pos ht,abs_of_nonneg hx] at ha
  norm_num at ha
  nlinarith


/-- The raw half-line parameter derivative. -/
def rawD (n:ℕ) (t:ℝ) (h:ℝ→ℝ) : ℝ := ∫ x in Ioi (0:ℝ),originalb n t x*h x

/-- The raw half-line second spatial moment. -/
def rawM2 (n:ℕ) (t:ℝ) (h:ℝ→ℝ) : ℝ := ∫ x in Ioi (0:ℝ),x^2*originalB n t x*h x

/-- The complete finite coefficient extraction. -/
def rawG (n:ℕ) (t:ℝ) (h:ℝ→ℝ) : ℝ :=
  (2*(n:ℝ)*rawD n t h-rawM2 n t h/2)/(2*(n:ℝ)+1)

/-- Parameter response against the original normalized full density. -/
def fullD (n:ℕ) (t:ℝ) : ℝ := ∫ x:ℝ,originalb n t x*sourceThetaDensity x

/-- Second spatial moment against the original normalized full density. -/
def fullM2 (n:ℕ) (t:ℝ) : ℝ := ∫ x:ℝ,x^2*originalB n t x*sourceThetaDensity x

/-- The actual adjacent-degree derivative extraction. -/
def fullG (n:ℕ) (t:ℝ) : ℝ := (2*(n:ℝ)*fullD n t-fullM2 n t/2)/(2*(n:ℝ)+1)

private theorem finite_moments (n:ℕ) (t:ℝ) (h:ℝ→ℝ) (μ:Measure ℝ)
    (hm:∀ k:ℕ,Integrable (fun x:ℝ =>x^(2*k)*h x) μ) :
    Integrable (fun x:ℝ =>originalB n t x*h x) μ ∧
    Integrable (fun x:ℝ =>originalb n t x*h x) μ ∧
    Integrable (fun x:ℝ =>x^2*originalB n t x*h x) μ ∧
    (∫ x,originalB n t x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*t^j*(∫ x,x^(2*j)*h x ∂μ) ∧
    (∫ x,originalb n t x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*(j:ℝ)*t^(j-1)*(∫ x,x^(2*j)*h x ∂μ) ∧
    (∫ x,x^2*originalB n t x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*t^j*(∫ x,x^(2*(j+1))*h x ∂μ) ∧
    HasDerivAt (fun u:ℝ =>∫ x,originalB n u x*h x ∂μ)
      (∫ x,originalb n t x*h x ∂μ) t := by
  have heB (u x:ℝ):originalB n u x*h x=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*u^j*(x^(2*j)*h x) := by
    rw [←original_polynomial_eval]
    simp only [originalPolynomial,eval_finsetSum,eval_mul,eval_C,eval_X,eval_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficient_factor]
    ring
  have heb (x:ℝ):originalb n t x*h x=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*(j:ℝ)*t^(j-1)*(x^(2*j)*h x) := by
    simp only [originalb,parameterPolynomial,eval_finsetSum,eval_mul,eval_C,
      eval_X,eval_pow,Finset.sum_mul,mul_assoc]
  have heM (x:ℝ):x^2*originalB n t x*h x=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*t^j*(x^(2*(j+1))*h x) := by
    rw [show x^2*originalB n t x*h x = x^2*(originalB n t x*h x) by ring,heB,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show 2*(j+1)=2+2*j by omega,pow_add]
    ring
  have hiB (u:ℝ):Integrable (fun x =>originalB n u x*h x) μ := by
    simp_rw [heB]
    exact integrable_finsetSum _ (fun j _ => (hm j).const_mul _)
  have hib:Integrable (fun x =>originalb n t x*h x) μ := by
    simp_rw [heb]
    exact integrable_finsetSum _ (fun j _ => (hm j).const_mul _)
  have hiM:Integrable (fun x =>x^2*originalB n t x*h x) μ := by
    simp_rw [heM]
    exact integrable_finsetSum _ (fun j _ => (hm (j+1)).const_mul _)
  have hB (u:ℝ):(∫ x,originalB n u x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*u^j*(∫ x,x^(2*j)*h x ∂μ) := by
    simp_rw [heB]
    rw [integral_finsetSum _ (fun j _ => (hm j).const_mul _)]
    simp only [integral_const_mul]
  have hb:(∫ x,originalb n t x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*(j:ℝ)*t^(j-1)*(∫ x,x^(2*j)*h x ∂μ) := by
    simp_rw [heb]
    rw [integral_finsetSum _ (fun j _ => (hm j).const_mul _)]
    simp only [integral_const_mul]
  have hM:(∫ x,x^2*originalB n t x*h x ∂μ)=
      ∑ j∈Finset.range (n+1),originalCoefficient n 1 j*t^j*(∫ x,x^(2*(j+1))*h x ∂μ) := by
    simp_rw [heM]
    rw [integral_finsetSum _ (fun j _ => (hm (j+1)).const_mul _)]
    simp only [integral_const_mul]
  refine ⟨hiB t,hib,hiM,hB t,hb,hM,?_⟩
  have he:(fun u:ℝ =>∫ x,originalB n u x*h x ∂μ)=
      fun u =>∑ j∈Finset.range (n+1),originalCoefficient n 1 j*u^j*(∫ x,x^(2*j)*h x ∂μ) :=
    funext hB
  rw [he,hb]
  convert! HasDerivAt.fun_sum (u:=Finset.range (n+1))
    (fun j _ => ((hasDerivAt_id t).pow j).const_mul
      (originalCoefficient n 1 j*(∫ x,x^(2*j)*h x ∂μ))) using 1
  · ext u; apply Finset.sum_congr rfl; intro j _; simp only [id_eq,Pi.pow_apply,mul_one]; ring
  · apply Finset.sum_congr rfl; intro j _; simp only [id_eq,Pi.pow_apply,mul_one]; ring

private theorem coefficient_G {n:ℕ} (hn:1≤n) (k:ℕ) :
    2*(n:ℝ)*(k+1)*originalCoefficient n 1 (k+1)-originalCoefficient n 1 k/2=
      -(2*(n:ℝ)+1)*originalCoefficient n 1 k/(2*(2*(k:ℝ)+1)) := by
  have h:=(original_coefficient_recurrence hn 1 k).2
  have hn0:(n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  push_cast at h
  have hk0:2*(2*(k:ℝ)+1)≠0 := by positivity
  field_simp [hn0] at h
  apply (eq_div_iff hk0).mpr
  nlinarith

private theorem finite_G {n:ℕ} (hn:1≤n) (t:ℝ) (h:ℝ→ℝ) (μ:Measure ℝ)
    (hm:∀ k:ℕ,Integrable (fun x:ℝ =>x^(2*k)*h x) μ) :
    (2*(n:ℝ)*(∫ x,originalb n t x*h x ∂μ)-
      (∫ x,x^2*originalB n t x*h x ∂μ)/2)/(2*(n:ℝ)+1)=
      -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
        (∫ x,x^(2*(k+1))*h x ∂μ)/(2*(2*(k:ℝ)+1)) := by
  have hf:=finite_moments n t h μ hm
  have hb:=hf.2.2.2.2.1
  have hM:=hf.2.2.2.2.2.1
  let μk:=fun k:ℕ =>∫ x,x^(2*k)*h x ∂μ
  have hnxt:originalCoefficient n 1 (n+1)=0 := by
    simp [originalCoefficient,Nat.descFactorial_of_lt (show n<n+1 by omega)]
  have hshift:(∫ x,originalb n t x*h x ∂μ)=
      ∑ k∈Finset.range (n+1),originalCoefficient n 1 (k+1)*((k+1:ℕ):ℝ)*t^k*μk (k+1) := by
    rw [hb,Finset.sum_range_succ']
    simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero]
    rw [Finset.sum_range_succ]
    simp only [hnxt,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.add_sub_cancel]
    rfl
  rw [hshift,hM,Finset.mul_sum,Finset.sum_div,←Finset.sum_sub_distrib,Finset.sum_div]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hc:=coefficient_G hn k
  have hd:(2*(n:ℝ)+1)≠0 := by positivity
  have hk:2*(2*(k:ℝ)+1)≠0 := by positivity
  dsimp [μk]
  push_cast
  field_simp [hd,hk] at hc ⊢
  linear_combination (t^k*(∫ x,x^(2*(k+1))*h x ∂μ))*hc

private def spatialOperator (α:ℝ) (p:ℝ[X]) : ℝ[X] :=
  p.derivative.derivative-C α*(X*p.derivative)

private theorem polynomial_green (α c:ℝ) (p h:ℝ[X]) (F:ℝ→ℝ)
    (hdF:Differentiable ℝ F) (hddF:Differentiable ℝ (deriv F))
    (hode:spatialOperator α p+C c*p=h)
    (hiF:IntegrableOn (fun x => p.eval x*F x) (Ioi 0))
    (hiA:IntegrableOn (fun x => p.eval x*densityAdjoint α F x) (Ioi 0))
    (hih:IntegrableOn (fun x => h.eval x*F x) (Ioi 0))
    (hl0:Tendsto (fun x => p.eval x*deriv F x) atTop (𝓝 0))
    (hl1:Tendsto (fun x => p.derivative.eval x*F x) atTop (𝓝 0))
    (hl2:Tendsto (fun x => (C α*X*p).eval x*F x) atTop (𝓝 0)) :
    (∫ x in Ioi (0:ℝ),p.eval x*densityAdjoint α F x)+
      c*(∫ x in Ioi (0:ℝ),p.eval x*F x)=
      (∫ x in Ioi (0:ℝ),h.eval x*F x)-
        (p.eval 0*deriv F 0-p.derivative.eval 0*F 0) := by
  let K:=fun x:ℝ => p.eval x*deriv F x-p.derivative.eval x*F x+
    α*x*p.eval x*F x
  have ho (x:ℝ):p.derivative.derivative.eval x=
      α*x*p.derivative.eval x-c*p.eval x+h.eval x := by
    have he:=congrArg (fun q:ℝ[X] =>q.eval x) hode
    simp only [spatialOperator,eval_sub,eval_add,eval_mul,eval_C,eval_X] at he
    linarith
  have hd (x:ℝ):HasDerivAt K
      (p.eval x*densityAdjoint α F x+c*(p.eval x*F x)-h.eval x*F x) x := by
    have hb:=p.hasDerivAt x
    have hp:=p.derivative.hasDerivAt x
    rw [ho x] at hp
    convert! ((hb.mul (hddF x).hasDerivAt).sub (hp.mul (hdF x).hasDerivAt)).add
      (((((hasDerivAt_id x).const_mul α).mul hb).mul (hdF x).hasDerivAt)) using 1 <;>
      dsimp [K,densityAdjoint] <;> ring
  have hl2':Tendsto (fun x:ℝ => α*x*p.eval x*F x) atTop (𝓝 0) := by
    simpa only [eval_mul,eval_C,eval_X] using hl2
  have hl:Tendsto K atTop (𝓝 0) := by simpa [K] using (hl0.sub hl1).add hl2'
  have hi:IntegrableOn (fun x:ℝ => p.eval x*densityAdjoint α F x+
      c*(p.eval x*F x)-h.eval x*F x) (Ioi 0) := (hiA.add (hiF.const_mul c)).sub hih
  have he:=integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi hl
  have his : IntegrableOn (fun x:ℝ =>p.eval x*densityAdjoint α F x+c*(p.eval x*F x)) (Ioi 0) := hiA.add (hiF.const_mul c)
  rw [integral_sub his hih,integral_add hiA (hiF.const_mul c),integral_const_mul] at he
  have hzero:K 0=p.eval 0*deriv F 0-p.derivative.eval 0*F 0 := by dsimp [K]; ring
  rw [hzero] at he
  linarith

private theorem residual_pair_data {N:ℕ} (hN:1≤N) (A α:ℝ) (p:ℝ[X]) :
    Differentiable ℝ (tailResidual N A α) ∧
    Differentiable ℝ (deriv (tailResidual N A α)) ∧
    IntegrableOn (fun x => p.eval x*tailResidual N A α x) (Ioi 0) ∧
    IntegrableOn (fun x => p.eval x*densityAdjoint α (tailResidual N A α) x) (Ioi 0) ∧
    Tendsto (fun x => p.eval x*deriv (tailResidual N A α) x) atTop (𝓝 0) ∧
    Tendsto (fun x => p.derivative.eval x*tailResidual N A α x) atTop (𝓝 0) ∧
    Tendsto (fun x => (C α*X*p).eval x*tailResidual N A α x) atTop (𝓝 0) := by
  have hq:originalTail N=tailJet 0 N := by simpa using (tailJet_eq_iterated 0 N hN).symm
  have hdq (x:ℝ):HasDerivAt (originalTail N) (tailJet 1 N x) x := by
    rw [hq]; exact tailJet_deriv 0 N hN x
  have hddq (x:ℝ):HasDerivAt (deriv (originalTail N)) (tailJet 2 N x) x := by
    have he:deriv (originalTail N)=tailJet 1 N := funext (fun y => (hdq y).deriv)
    rw [he]; exact tailJet_deriv 1 N hN x
  have hda:=fun x => (adjoint_deriv N hN α x).differentiableAt
  have hdda:=fun x => (adjoint_second_deriv N hN α x).differentiableAt
  have hr (x:ℝ):HasDerivAt (tailResidual N A α)
      (4*A^2*deriv (originalTail N) x-deriv (densityAdjoint α (originalTail N)) x) x :=
    ((hdq x).const_mul (4*A^2)).sub (adjoint_deriv N hN α x) |>.congr_deriv
      (by rw [(hdq x).deriv,(adjoint_deriv N hN α x).deriv])
  have hdr:Differentiable ℝ (tailResidual N A α) := fun x => (hr x).differentiableAt
  have hder:deriv (tailResidual N A α)=
      fun x => 4*A^2*deriv (originalTail N) x-deriv (densityAdjoint α (originalTail N)) x :=
    funext (fun x => (hr x).deriv)
  have hddr:Differentiable ℝ (deriv (tailResidual N A α)) := by
    rw [hder]; exact fun x => ((hddq x).const_mul (4*A^2)).sub (hdda x).hasDerivAt |>.differentiableAt
  have hlin:=adjoint_linear (4*A^2) α _ _ (fun x => (hdq x).differentiableAt)
    (fun x => (hddq x).differentiableAt) hda hdda
  have hiq (q:ℝ[X]):IntegrableOn (fun x => q.eval x*originalTail N x) (Ioi 0) := by
    simpa only [hq] using (polynomial_jet hN 0 q).1
  have hir (q:ℝ[X]):IntegrableOn (fun x => q.eval x*tailResidual N A α x) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    convert! ((hiq q).const_mul (4*A^2)).sub (polynomial_adjoint hN α q).1 using 1
    ext x; dsimp [tailResidual]; ring
  have hlr (q:ℝ[X]):Tendsto (fun x => q.eval x*tailResidual N A α x) atTop (𝓝 0) := by
    have h:=((polynomial_jet hN 0 q).2.const_mul (4*A^2)).sub (polynomial_adjoint hN α q).2
    convert! h using 1
    · ext x; dsimp [tailResidual]; rw [hq]; ring
    · ring
  refine ⟨hdr,hddr,hir p,?_,?_,hlr p.derivative,hlr (C α*X*p)⟩
  · have he:densityAdjoint α (tailResidual N A α)=
        fun x => 4*A^2*densityAdjoint α (originalTail N) x-
          densityAdjoint α (densityAdjoint α (originalTail N)) x := hlin
    rw [he]
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    convert! ((polynomial_adjoint hN α p).1.const_mul (4*A^2)).sub
      (polynomial_adjoint_square_integrable hN α p) using 1
    ext x; dsimp only [Pi.sub_apply]; ring
  · rw [hder]
    have h:=((polynomial_jet hN 1 p).2.const_mul (4*A^2)).sub
      (polynomial_adjoint_deriv_limit hN α p)
    convert! h using 1
    · ext x; dsimp only; rw [(hdq x).deriv]; ring
    · ring

private theorem five_green {N n:ℕ} (hN:1≤N) (hn:1≤n) {t:ℝ} (ht:0<t) (A:ℝ) :
    let α:=t/(2*(n:ℝ))
    let S:=4*A^2
    let Λ:=S+t
    let Q:=originalTail N
    let R:=tailResidual N A α
    let R₂:=tailSecondResidual N A α
    let I:=∫ x in Ioi (0:ℝ),originalB n t x*Q x
    let U:=∫ x in Ioi (0:ℝ),originalB n t x*R x
    Λ*I=originalFlux N+U ∧
    (Λ-2*α)*rawD n t Q= -I+rawD n t R ∧
    (Λ+2*α)*rawM2 n t Q=2*I+8*t*rawD n t Q+rawM2 n t R ∧
    (Λ-2*α)*rawD n t R= -U+rawD n t R₂ ∧
    (Λ+2*α)*rawM2 n t R=2*U+8*t*rawD n t R+rawM2 n t R₂ := by
  let α:=t/(2*(n:ℝ))
  let p:=originalPolynomial n t
  let b:=parameterPolynomial n t
  let m:=X^2*p
  let Q:=originalTail N
  let R:=tailResidual N A α
  have hq:Q=tailJet 0 N := by simpa [Q] using (tailJet_eq_iterated 0 N hN).symm
  have hdq (x:ℝ):HasDerivAt Q (tailJet 1 N x) x := by
    rw [hq]; exact tailJet_deriv 0 N hN x
  have hddq (x:ℝ):HasDerivAt (deriv Q) (tailJet 2 N x) x := by
    have he:deriv Q=tailJet 1 N := funext (fun y => (hdq y).deriv)
    rw [he]; exact tailJet_deriv 1 N hN x
  have hiQ (q:ℝ[X]):IntegrableOn (fun x =>q.eval x*Q x) (Ioi 0) := by
    simpa only [hq] using (polynomial_jet hN 0 q).1
  have hdlim (q:ℝ[X]):Tendsto (fun x =>q.eval x*deriv Q x) atTop (𝓝 0) := by
    have he:deriv Q=tailJet 1 N := funext (fun y => (hdq y).deriv)
    rw [he]; exact (polynomial_jet hN 1 q).2
  have hqlim (q:ℝ[X]):Tendsto (fun x =>q.eval x*Q x) atTop (𝓝 0) := by
    rw [hq]; exact (polynomial_jet hN 0 q).2
  have pairQ (q h:ℝ[X]) (c:ℝ) (he:spatialOperator α q+C c*q=h) :=
    polynomial_green α c q h Q (fun x =>(hdq x).differentiableAt)
      (fun x =>(hddq x).differentiableAt) he (hiQ q) (polynomial_adjoint hN α q).1
      (hiQ h) (hdlim q) (hqlim q.derivative) (hqlim (C α*X*q))
  have pairR (q h:ℝ[X]) (c:ℝ) (he:spatialOperator α q+C c*q=h) := by
    have hr:=residual_pair_data hN A α q
    have hri:IntegrableOn (fun x =>h.eval x*R x) (Ioi 0) :=
      (residual_pair_data hN A α h).2.2.1
    exact polynomial_green α c q h R hr.1 hr.2.1 he hr.2.2.1 hr.2.2.2.1 hri
      hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
  have hbode:spatialOperator α b+C (t-2*α)*b= -p := (tester_equations hn ht).1
  have hmode:spatialOperator α m+C (t+2*α)*m=C 2*p+C (8*t)*b := (tester_equations hn ht).2
  have gbQ:=pairQ b (-p) (t-2*α) hbode
  have gmQ:=pairQ m (C 2*p+C (8*t)*b) (t+2*α) hmode
  have gbR:=pairR b (-p) (t-2*α) hbode
  have gmR:=pairR m (C 2*p+C (8*t)*b) (t+2*α) hmode
  have gBQ:=original_green hn t Q (fun x =>(hdq x).differentiableAt)
    (fun x =>(hddq x).differentiableAt) (hiQ p) (polynomial_adjoint hN α p).1
    (hdlim p) (hqlim p.derivative) (hqlim (C α*X*p))
  have hb0:(b.eval 0=0 ∧ b.derivative.eval 0=0) := parameter_origin n t
  have hm0:m.eval 0=0 ∧ m.derivative.eval 0=0 := by
    simp [m,derivative_mul,derivative_pow]
  have hR (q:ℝ[X]):(∫ x in Ioi (0:ℝ),q.eval x*R x)=
      4*A^2*(∫ x in Ioi (0:ℝ),q.eval x*Q x)-
        (∫ x in Ioi (0:ℝ),q.eval x*densityAdjoint α Q x) := by
    have he:(fun x:ℝ =>q.eval x*R x)=
        fun x =>4*A^2*(q.eval x*Q x)-q.eval x*densityAdjoint α Q x := by
      ext x; dsimp [R,tailResidual,Q]; ring
    rw [he,integral_sub ((hiQ q).const_mul (4*A^2)) (polynomial_adjoint hN α q).1,
      integral_const_mul]
  have hR₂ (q:ℝ[X]):(∫ x in Ioi (0:ℝ),q.eval x*tailSecondResidual N A α x)=
      4*A^2*(∫ x in Ioi (0:ℝ),q.eval x*R x)-
        (∫ x in Ioi (0:ℝ),q.eval x*densityAdjoint α R x) := by
    have hr:=residual_pair_data hN A α q
    have he:(fun x:ℝ =>q.eval x*tailSecondResidual N A α x)=
        fun x =>4*A^2*(q.eval x*R x)-q.eval x*densityAdjoint α R x := by
      ext x; dsimp [tailSecondResidual,R]; ring
    rw [he,integral_sub (hr.2.2.1.const_mul (4*A^2)) hr.2.2.2.1,integral_const_mul]
  have he_m (x:ℝ):m.eval x=x^2*originalB n t x := by
    dsimp [m,p]; simp only [eval_mul,eval_pow,eval_X,original_polynomial_eval]
  have he_p (x:ℝ):p.eval x=originalB n t x := original_polynomial_eval n t x
  have he_b (x:ℝ):b.eval x=originalb n t x := rfl
  have he_hQ:(∫ x in Ioi (0:ℝ),(C 2*p+C (8*t)*b).eval x*Q x)=
      2*(∫ x in Ioi (0:ℝ),p.eval x*Q x)+8*t*(∫ x in Ioi (0:ℝ),b.eval x*Q x) := by
    have he:(fun x:ℝ => (C 2*p+C (8*t)*b).eval x*Q x)=
        fun x =>2*(p.eval x*Q x)+(8*t)*(b.eval x*Q x) := by
      ext x; simp only [eval_add,eval_mul,eval_C]; ring
    rw [he,integral_add ((hiQ p).const_mul 2) ((hiQ b).const_mul (8*t)),integral_const_mul,
      integral_const_mul]
  have he_hR:(∫ x in Ioi (0:ℝ),(C 2*p+C (8*t)*b).eval x*R x)=
      2*(∫ x in Ioi (0:ℝ),p.eval x*R x)+8*t*(∫ x in Ioi (0:ℝ),b.eval x*R x) := by
    have hip:IntegrableOn (fun x =>p.eval x*R x) (Ioi 0) := (residual_pair_data hN A α p).2.2.1
    have hib:IntegrableOn (fun x =>b.eval x*R x) (Ioi 0) := (residual_pair_data hN A α b).2.2.1
    have he:(fun x:ℝ => (C 2*p+C (8*t)*b).eval x*R x)=
        fun x =>2*(p.eval x*R x)+(8*t)*(b.eval x*R x) := by
      ext x; simp only [eval_add,eval_mul,eval_C]; ring
    rw [he,integral_add (hip.const_mul 2) (hib.const_mul (8*t)),integral_const_mul,integral_const_mul]
  have he_nQ:(∫ x in Ioi (0:ℝ),(-p).eval x*Q x)=
      -(∫ x in Ioi (0:ℝ),p.eval x*Q x) := by simp [eval_neg,neg_mul,integral_neg]
  have he_nR:(∫ x in Ioi (0:ℝ),(-p).eval x*R x)=
      -(∫ x in Ioi (0:ℝ),p.eval x*R x) := by simp [eval_neg,neg_mul,integral_neg]
  rw [hb0.1,hb0.2,he_nQ] at gbQ
  rw [hm0.1,hm0.2,he_hQ] at gmQ
  rw [hb0.1,hb0.2,he_nR] at gbR
  rw [hm0.1,hm0.2,he_hR] at gmR
  have hk:originalFlux N= -deriv Q 0 := flux_eq N hN
  have hRp:=hR p
  have hRb:=hR b
  have hRm:=hR m
  have hR₂b:=hR₂ b
  have hR₂m:=hR₂ m
  simp only [mul_zero,zero_mul,sub_zero,sub_self] at gbQ gmQ gbR gmR
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  dsimp [rawD,rawM2]
  simp only [he_p,he_b,he_m] at gBQ gbQ gmQ gbR gmR hRp hRb hRm hR₂b hR₂m
  simp only [original_polynomial_eval] at gBQ
  dsimp only [Q,R,α] at gBQ gbQ gmQ gbR gmR hRp hRb hRm hR₂b hR₂m hk
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


private theorem even_source_transport {N:ℕ} (hN:1≤N) (p:ℝ[X])
    (heven:∀ x:ℝ,p.eval |x|=p.eval x)
    (hraw:Integrable (fun x:ℝ =>p.eval x*sourceThetaKernel x)) :
    IntegrableOn (fun x:ℝ =>p.eval x*originalHead N x) (Ioi 0) ∧
    (∫ x:ℝ,p.eval x*sourceThetaDensity x)=
      (2/fullZ)*((∫ x in Ioi (0:ℝ),p.eval x*originalHead N x)+
        ∫ x in Ioi (0:ℝ),p.eval x*originalTail N x) := by
  have hq:tailJet 0 N=originalTail N := by simpa using tailJet_eq_iterated 0 N hN
  have hiq:IntegrableOn (fun x:ℝ =>p.eval x*originalTail N x) (Ioi 0) := by
    simpa only [hq] using (polynomial_jet hN 0 p).1
  have hih:IntegrableOn (fun x:ℝ =>p.eval x*originalHead N x) (Ioi 0) := by
    apply (hraw.integrableOn.sub hiq).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change p.eval x*sourceThetaKernel x-p.eval x*originalTail N x=p.eval x*originalHead N x
    rw [original_source_split N hx.le]
    ring
  have hkernel (x:ℝ):sourceThetaKernel |x|=sourceThetaKernel x := by
    simp only [sourceThetaKernel,abs_abs]
  have hfull:(∫ x:ℝ,p.eval x*sourceThetaKernel x)=
      2*(∫ x in Ioi (0:ℝ),p.eval x*sourceThetaKernel x) := by
    calc
      _ = ∫ x:ℝ,p.eval |x| *sourceThetaKernel |x| := by simp only [heven,hkernel]
      _ = _ := integral_comp_abs (f:=fun x:ℝ =>p.eval x*sourceThetaKernel x)
  have hray:(∫ x in Ioi (0:ℝ),p.eval x*sourceThetaKernel x)=
      (∫ x in Ioi (0:ℝ),p.eval x*originalHead N x)+
        ∫ x in Ioi (0:ℝ),p.eval x*originalTail N x := by
    rw [←integral_add hih hiq]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [original_source_split N hx.le]
    ring
  refine ⟨hih,?_⟩
  simp only [sourceThetaDensity,←mul_div_assoc,integral_div]
  rw [hfull,hray]
  dsimp [fullZ]
  ring

private theorem source_vector {N n:ℕ} (hN:1≤N) (hn:1≤n) (t:ℝ) :
    IntegrableOn (fun x =>originalb n t x*originalTail N x) (Ioi 0) ∧
    IntegrableOn (fun x =>x^2*originalB n t x*originalTail N x) (Ioi 0) ∧
    IntegrableOn (fun x =>originalb n t x*originalHead N x) (Ioi 0) ∧
    IntegrableOn (fun x =>x^2*originalB n t x*originalHead N x) (Ioi 0) ∧
    Integrable (fun x:ℝ =>originalb n t x*sourceThetaDensity x) ∧
    Integrable (fun x:ℝ =>x^2*originalB n t x*sourceThetaDensity x) ∧
    HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalTail N x)
      (rawD n t (originalTail N)) t ∧
    HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalHead N x)
      (rawD n t (originalHead N)) t ∧
    HasDerivAt (originalJ n) (fullD n t) t ∧
    fullD n t= -(sourceP n).derivative.eval (-t) ∧
    fullD n t=(2/fullZ)*(rawD n t (originalHead N)+rawD n t (originalTail N)) ∧
    fullM2 n t=(2/fullZ)*(rawM2 n t (originalHead N)+rawM2 n t (originalTail N)) ∧
    fullG n t=(2/fullZ)*(rawG n t (originalHead N)+rawG n t (originalTail N)) ∧
    rawG n t (originalTail N)=
      -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
        (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalTail N x)/(2*(2*(k:ℝ)+1)) ∧
    rawG n t (originalHead N)=
      -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
        (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalHead N x)/(2*(2*(k:ℝ)+1)) := by
  have hz:fullZ≠0 := ne_of_gt
    D5.S3.Analytic.Fourier.XiThetaTransform.source_theta_normalized.2.1
  change (CompletedZeta.xiReading (1/2)).re≠0 at hz
  have hmfull (k:ℕ):Integrable (fun x:ℝ =>x^(2*k)*sourceThetaDensity x) := by
    simpa only [sourceThetaDensity,fullZ,mul_div_assoc] using
      (SourceThetaMomentBounds.source_theta_raw_moments k).1.div_const fullZ
  have hmq (k:ℕ):IntegrableOn (fun x:ℝ =>x^(2*k)*originalTail N x) (Ioi 0) := by
    have he:tailJet 0 N=originalTail N := by simpa using tailJet_eq_iterated 0 N hN
    simpa only [eval_pow,eval_X,he] using (polynomial_jet hN 0 (X^(2*k))).1
  have hmh (k:ℕ):IntegrableOn (fun x:ℝ =>x^(2*k)*originalHead N x) (Ioi 0) := by
    apply ((SourceThetaMomentBounds.source_theta_raw_moments k).1.integrableOn.sub (hmq k)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [Pi.sub_apply]
    rw [original_source_split N hx.le]
    ring
  have vf:=finite_moments n t sourceThetaDensity volume hmfull
  have vq:=finite_moments n t (originalTail N) (volume.restrict (Ioi 0)) hmq
  have vh:=finite_moments n t (originalHead N) (volume.restrict (Ioi 0)) hmh
  have braw:Integrable (fun x:ℝ =>(parameterPolynomial n t).eval x*sourceThetaKernel x) := by
    convert! vf.2.1.mul_const fullZ using 1
    ext x; dsimp [originalb,sourceThetaDensity,fullZ] at *
    field_simp [hz]
  have mraw:Integrable (fun x:ℝ =>(X^2*originalPolynomial n t).eval x*sourceThetaKernel x) := by
    convert! vf.2.2.1.mul_const fullZ using 1
    ext x; simp only [eval_mul,eval_pow,eval_X,original_polynomial_eval]
    dsimp [sourceThetaDensity,fullZ]
    field_simp [hz]
  have beven (x:ℝ):(parameterPolynomial n t).eval |x|=(parameterPolynomial n t).eval x := by
    simp only [parameterPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
      Even.pow_abs (even_two_mul _) x]
  have meven (x:ℝ):(X^2*originalPolynomial n t).eval |x|=(X^2*originalPolynomial n t).eval x := by
    simp only [eval_mul,eval_pow,eval_X,original_polynomial_eval,originalB,
      Even.pow_abs (even_two_mul _) x, sq_abs]
  have btr:=even_source_transport hN (parameterPolynomial n t) beven braw
  have mtr:=even_source_transport hN (X^2*originalPolynomial n t) meven mraw
  have hd:HasDerivAt (originalJ n) (fullD n t) t := vf.2.2.2.2.2.2
  have hP:fullD n t= -(sourceP n).derivative.eval (-t) := by
    have he:originalJ n=fun u:ℝ =>(sourceP n).eval (-u) :=
      funext (fun u => (original_moment_bridge n u).2.1)
    have hp:=((sourceP n).hasDerivAt (-t)).comp t (hasDerivAt_id t).neg
    rw [he] at hd
    simpa only [Function.comp_def,id_eq,mul_neg,mul_one] using hd.unique hp
  have hD:fullD n t=(2/fullZ)*(rawD n t (originalHead N)+rawD n t (originalTail N)) := btr.2
  have hM:fullM2 n t=(2/fullZ)*(rawM2 n t (originalHead N)+rawM2 n t (originalTail N)) := by
    simpa only [fullM2,rawM2,eval_mul,eval_pow,eval_X,original_polynomial_eval] using mtr.2
  refine ⟨vq.2.1,vq.2.2.1,vh.2.1,vh.2.2.1,vf.2.1,vf.2.2.1,
    vq.2.2.2.2.2.2,vh.2.2.2.2.2.2,hd,hP,hD,hM,?_,
    finite_G hn t _ _ hmq,finite_G hn t _ _ hmh⟩
  dsimp [fullG,rawG]
  rw [hD,hM]
  ring


private theorem full_G_extraction {n:ℕ} (hn:1≤n) (t:ℝ) :
    fullG n t= -∑ k∈Finset.range (n+1),
      (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1)*t^k ∧
    HasDerivAt (originalJ (n+1)) (fullG n t) (((n+1:ℕ):ℝ)/(n:ℝ)*t) := by
  have hm (k:ℕ):Integrable (fun x:ℝ =>x^(2*k)*sourceThetaDensity x) := by
    simpa only [sourceThetaDensity,fullZ,mul_div_assoc] using
      (SourceThetaMomentBounds.source_theta_raw_moments k).1.div_const fullZ
  have hg:=finite_G hn t sourceThetaDensity volume hm
  have hcoeff (k:ℕ):originalCoefficient n 1 k*
      (∫ x:ℝ,x^(2*(k+1))*sourceThetaDensity x)/(2*(2*(k:ℝ)+1))=
      (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1) := by
    have hf:((2*(k+1)).factorial:ℝ)=
        (2*(k:ℝ)+2)*(2*(k:ℝ)+1)*((2*k).factorial:ℝ) := by
      rw [show 2*(k+1)=(2*k+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast; ring
    have hn0:(n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    have hf0:((2*k).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*k)
    have hk0:2*(2*(k:ℝ)+1)≠0 := by positivity
    dsimp [originalCoefficient,sourceThetaCoefficient,sourceThetaMoment]
    rw [hf]
    simp only [one_pow,mul_one]
    field_simp [hn0,hf0,hk0] <;> ring
  have he:fullG n t= -∑ k∈Finset.range (n+1),
      (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1)*t^k := by
    change fullG n t=_ at hg
    rw [hg]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have h:=congrArg (fun x:ℝ =>x*t^k) (hcoeff k)
    convert! h using 1 <;> ring
  refine ⟨he,?_⟩
  let ℓ:=((n+1:ℕ):ℝ)/(n:ℝ)
  have hpoly:(sourceP (n+1)).derivative.eval (-(ℓ*t))=
      ∑ k∈Finset.range (n+1),
        (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1)*t^k := by
    simp only [sourceP,derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,
      derivative_pow,derivative_X,mul_one,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have hn0:(n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    have hp0:((n+1:ℕ):ℝ)≠0 := by positivity
    rw [Nat.succ_descFactorial_succ]
    simp only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [neg_pow,mul_pow,pow_succ]
    dsimp [ℓ]
    rw [div_pow]
    field_simp [hn0,hp0]
    push_cast
    ring
  have hd:=((sourceP (n+1)).hasDerivAt (-(ℓ*t))).comp (ℓ*t) (hasDerivAt_id (ℓ*t)).neg
  have hJ:originalJ (n+1)=fun u:ℝ =>(sourceP (n+1)).eval (-u) :=
    funext (fun u => (original_moment_bridge (n+1) u).2.1)
  rw [hJ,he]
  convert! hd using 1
  rw [hpoly]; ring

set_option maxHeartbeats 800000 in
private theorem resolvent_algebra {A α S t Λ κ I D M U V Y W₁ W₂:ℝ}
    (hA:64≤A) (hα:0≤α) (hαA:α≤A) (ht:0<t) (hκ:0<κ)
    (hS:S=4*A^2) (hΛ:Λ=S+t)
    (g₀:Λ*I=κ+U) (g₁:(Λ-2*α)*D= -I+V)
    (g₂:(Λ+2*α)*M=2*I+8*t*D+Y)
    (g₃:(Λ-2*α)*V= -U+W₁)
    (g₄:(Λ+2*α)*Y=2*U+8*t*V+W₂)
    (hU:|U|≤64*κ/A) (hW₁:|W₁|≤550*κ/A) (hW₂:|W₂|≤1100*κ/A) :
    0<Λ ∧ Λ/2≤Λ-2*α ∧ Λ≤Λ+2*α ∧
    A*|Λ*I-κ|≤64*κ ∧ A*|Λ^2*D+κ|≤2600*κ ∧
    A*|Λ^3*M-2*κ*(S-3*t)|≤31983*Λ*κ := by
  have hA0:0<A := by linarith
  have hS0:0<S := by rw [hS]; positivity
  have hΛ0:0<Λ := by linarith
  have htΛ:t≤Λ := by linarith
  have hαΛ:2*α*A≤Λ/2 := by nlinarith
  have hm:Λ/2≤Λ-2*α := by nlinarith
  have hm0:0<Λ-2*α := by linarith
  have hp:Λ≤Λ+2*α := by linarith
  have hp0:0<Λ+2*α := by linarith
  have u:A*|U|≤64*κ := by nlinarith [(le_div_iff₀ hA0).mp hU]
  have w₁:A*|W₁|≤550*κ := by nlinarith [(le_div_iff₀ hA0).mp hW₁]
  have w₂:A*|W₂|≤1100*κ := by nlinarith [(le_div_iff₀ hA0).mp hW₂]
  have v:A*Λ*|V|≤1228*κ := by
    have hv:(Λ-2*α)*|V|≤|U|+|W₁| := by
      calc
        _ = |(Λ-2*α)*V| := by rw [abs_mul,abs_of_pos hm0]
        _ = |-U+W₁| := by rw [g₃]
        _ ≤ _ := by simpa only [abs_neg] using abs_add_le (-U) W₁
    have hv':=mul_le_mul_of_nonneg_left hv hA0.le
    have hc:=mul_le_mul_of_nonneg_right hm (abs_nonneg V)
    have hc':=mul_le_mul_of_nonneg_left hc hA0.le
    nlinarith only [hv',hc',u,w₁]
  have eI:A*|Λ*I-κ|≤64*κ := by rw [g₀]; simpa only [add_sub_cancel_left] using u
  let ED:=Λ^2*D+κ
  have heD:(Λ-2*α)*ED= -Λ*U+Λ^2*V-2*α*κ := by
    dsimp [ED]
    linear_combination -Λ*g₀+Λ^2*g₁
  have ed:A*|ED|≤2585*κ := by
    have hb:(Λ-2*α)*|ED|≤Λ*|U|+Λ^2*|V|+2*α*κ := by
      calc
        _ = |(Λ-2*α)*ED| := by rw [abs_mul,abs_of_pos hm0]
        _ = |-Λ*U+Λ^2*V-2*α*κ| := by rw [heD]
        _ ≤ |(-Λ*U+Λ^2*V)|+|2*α*κ| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (-Λ*U+Λ^2*V) (-(2*α*κ))
        _ ≤ (|-Λ*U|+|Λ^2*V|)+|2*α*κ| := by linarith [abs_add_le (-Λ*U) (Λ^2*V)]
        _ = _ := by rw [abs_mul,abs_neg,abs_of_pos hΛ0,abs_mul,abs_pow,abs_of_pos hΛ0,
            abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_nonneg hα,abs_of_pos hκ]
    have hb':=mul_le_mul_of_nonneg_left hb hA0.le
    have hu':=mul_le_mul_of_nonneg_left u hΛ0.le
    have hv':=mul_le_mul_of_nonneg_left v hΛ0.le
    have ha':=mul_le_mul_of_nonneg_right hαΛ hκ.le
    have hc:=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hm (abs_nonneg ED)) hA0.le
    have hh:A*|ED| *(Λ/2)≤(2585*κ)*(Λ/2) := by
      nlinarith only [hb',hu',hv',ha',hc]
    exact le_of_mul_le_mul_right hh (by positivity : 0<Λ/2)
  have ed':A*|ED|≤2600*κ := ed.trans (by nlinarith)
  have y:A*Λ*|Y|≤11052*κ := by
    have hy:(Λ+2*α)*|Y|≤2*|U|+8*t*|V|+|W₂| := by
      calc
        _ = |(Λ+2*α)*Y| := by rw [abs_mul,abs_of_pos hp0]
        _ = |2*U+8*t*V+W₂| := by rw [g₄]
        _ ≤ |2*U+8*t*V|+|W₂| := abs_add_le _ _
        _ ≤ (|2*U|+|8*t*V|)+|W₂| := by linarith [abs_add_le (2*U) (8*t*V)]
        _ = _ := by simp only [abs_mul,abs_of_pos ht]; norm_num
    have hy':=mul_le_mul_of_nonneg_left hy (mul_nonneg hA0.le hΛ0.le)
    have hu':=mul_le_mul_of_nonneg_left u (show 0≤2*Λ by positivity)
    have hv':=mul_le_mul_of_nonneg_left v (show 0≤8*t by positivity)
    have hw':=mul_le_mul_of_nonneg_left w₂ hΛ0.le
    have hv'':8*t*(1228*κ)≤8*Λ*(1228*κ) := by gcongr
    have hc:=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (abs_nonneg Y)) (mul_nonneg hA0.le hΛ0.le)
    have hh:(A*Λ*|Y|)*Λ≤(11052*κ)*Λ := by
      nlinarith only [hy',hu',hv',hw',hv'',hc]
    exact le_of_mul_le_mul_right hh hΛ0
  let EM:=Λ^3*M-2*κ*(S-3*t)
  have heM:(Λ+2*α)*EM=2*Λ^2*(Λ*I-κ)+8*t*Λ*ED+Λ^3*Y-4*α*κ*(S-3*t) := by
    dsimp [EM,ED]
    linear_combination Λ^3*g₂+2*κ*Λ*hΛ
  have hst:|S-3*t|≤3*Λ := by
    apply abs_le.mpr
    constructor <;> linarith
  have em:A*|EM|≤31983*Λ*κ := by
    have hb:(Λ+2*α)*|EM|≤2*Λ^2*|Λ*I-κ|+8*t*Λ*|ED|+
        Λ^3*|Y|+4*α*κ*|S-3*t| := by
      calc
        _ = |(Λ+2*α)*EM| := by rw [abs_mul,abs_of_pos hp0]
        _ = |2*Λ^2*(Λ*I-κ)+8*t*Λ*ED+Λ^3*Y-4*α*κ*(S-3*t)| := by rw [heM]
        _ ≤ |2*Λ^2*(Λ*I-κ)+8*t*Λ*ED+Λ^3*Y|+|4*α*κ*(S-3*t)| := by
          simpa only [sub_zero,zero_sub,abs_neg] using
            abs_sub_le (2*Λ^2*(Λ*I-κ)+8*t*Λ*ED+Λ^3*Y) 0 (4*α*κ*(S-3*t))
        _ ≤ (|2*Λ^2*(Λ*I-κ)+8*t*Λ*ED|+|Λ^3*Y|)+|4*α*κ*(S-3*t)| :=
          by linarith [abs_add_le (2*Λ^2*(Λ*I-κ)+8*t*Λ*ED) (Λ^3*Y)]
        _ ≤ ((|2*Λ^2*(Λ*I-κ)|+|8*t*Λ*ED|)+|Λ^3*Y|)+|4*α*κ*(S-3*t)| := by
          gcongr; exact abs_add_le _ _
        _ = _ := by simp only [abs_mul,abs_pow,abs_of_pos hΛ0,abs_of_pos ht,
            abs_of_pos hκ,abs_of_nonneg hα]; norm_num
    have hb':=mul_le_mul_of_nonneg_left hb hA0.le
    have hi':=mul_le_mul_of_nonneg_left eI (show 0≤2*Λ^2 by positivity)
    have hd':=mul_le_mul_of_nonneg_left ed' (show 0≤8*t*Λ by positivity)
    have hd'':8*t*Λ*(2600*κ)≤8*Λ*Λ*(2600*κ) := by gcongr
    have hy':=mul_le_mul_of_nonneg_left y (sq_nonneg Λ)
    have hs':=mul_le_mul_of_nonneg_left hst (show 0≤4*α*κ*A by positivity)
    have ha':=mul_le_mul_of_nonneg_right hαΛ (show 0≤6*κ*Λ by positivity)
    have hc:=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (abs_nonneg EM)) hA0.le
    have hh:(A*|EM|)*Λ≤(31983*Λ*κ)*Λ := by
      nlinarith only [hb',hi',hd',hd'',hy',hs',ha',hc]
    exact le_of_mul_le_mul_right hh hΛ0
  exact ⟨hΛ0,hm,hp,eI,ed',em⟩

open private source_degree reflected source_lowering from
  D5.S3.Zeros.Jensen.SourceJensenIntegralExtension

private theorem reflection_eval (d:ℕ) {x:ℝ} (hx:x≠0) :
    (sourceQ d).eval x=x^d*originalJ d x⁻¹ := by
  have hdeg:((sourceP d).comp (C (-1)*X)).natDegree≤d :=
    (natDegree_comp_le.trans (by simpa using source_degree d))
  letI:Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  have h:=eval₂_reflect_mul_pow (RingHom.id ℝ) (x⁻¹) d
    ((sourceP d).comp (C (-1)*X)) hdeg
  simp only [invOf_eq_inv,inv_inv,eval₂_id,eval_comp,eval_mul,eval_C,eval_X,neg_one_mul] at h
  change (sourceQ d).eval x*(x⁻¹)^d=(sourceP d).eval (-x⁻¹) at h
  rw [←(original_moment_bridge d x⁻¹).2.1] at h
  have hh:=congrArg (fun y:ℝ => y*x^d) h
  simpa only [←mul_assoc,←mul_pow,inv_mul_cancel₀ hx,mul_inv_cancel₀ hx,one_pow,mul_one,one_mul,mul_comm] using hh

private theorem reflection_derivative {d:ℕ} (hd:1≤d) {x:ℝ} (hx:x≠0) :
    x^2*(sourceQ d).derivative.eval x=
      (d:ℝ)*x^(d+1)*originalJ d x⁻¹-x^d*fullD d x⁻¹ := by
  have hm (k:ℕ):Integrable (fun y:ℝ =>y^(2*k)*sourceThetaDensity y) := by
    simpa only [sourceThetaDensity,fullZ,mul_div_assoc] using
      (SourceThetaMomentBounds.source_theta_raw_moments k).1.div_const fullZ
  have hJ:HasDerivAt (originalJ d) (fullD d x⁻¹) x⁻¹ :=
    (finite_moments d x⁻¹ sourceThetaDensity volume hm).2.2.2.2.2.2
  have h:=((hasDerivAt_id x).pow d).mul (hJ.comp x (hasDerivAt_inv hx))
  have he:(fun y:ℝ => (sourceQ d).eval y)=ᶠ[𝓝 x]
      (fun y:ℝ =>y^d*originalJ d y⁻¹) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact reflection_eval d hy
  have hh:=(sourceQ d).hasDerivAt x |>.unique (h.congr_of_eventuallyEq he)
  simp only [id_eq,Pi.pow_apply,mul_one] at hh
  rw [hh]
  have hepow:x^2*x^(d-1)=x^(d+1) := by rw [←pow_add]; congr 1; omega
  dsimp only [Function.comp_apply]
  field_simp [hx]
  linear_combination (d:ℝ)*originalJ d (1/x)*hepow

private theorem reflected_node {n:ℕ} (hn:1≤n) {t:ℝ} (ht:0<t)
    (hnode:originalJ n t=0) :
    let δ:ℝ:=(n:ℝ)/((n+1:ℕ):ℝ)
    let ξ:=δ/t
    let q:=sourceQ (n+1)
    0<ξ ∧ q.derivative.eval ξ=0 ∧
    ((n+1:ℕ):ℝ)*q.eval ξ=ξ^n*fullG n t ∧
    ξ^2*q.derivative.derivative.eval ξ= -(n:ℝ)*ξ^n*fullD n t ∧
    q.eval ξ*q.derivative.derivative.eval ξ=
      -((n:ℝ)/((n+1:ℕ):ℝ))*ξ^(2*n-2)*fullD n t*fullG n t ∧
    (fullD n t≠0 ↔ q.derivative.derivative.eval ξ≠0) ∧
    (fullD n t≠0 →
      SourceJensenPositiveExtension.sourceCoupling (n+1) ξ=
        (ξ^2/(n:ℝ))*(fullG n t/fullD n t) ∧
      (0≤SourceJensenPositiveExtension.sourceCoupling (n+1) ξ ↔
        0≤fullD n t*fullG n t)) := by
  let δ:ℝ:=(n:ℝ)/((n+1:ℕ):ℝ)
  let ξ:=δ/t
  let q:=sourceQ (n+1)
  have hn0:0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hh0:0<((n+1:ℕ):ℝ) := by positivity
  have hδ:0<δ := by dsimp [δ]; positivity
  have hξ:0<ξ := by dsimp [ξ]; positivity
  have hs:scale (n+1)=δ := by simp [scale,δ]
  have hlow:=source_lowering (n+1) (by omega)
  have hder: q.derivative=C (((n+1:ℕ):ℝ)*δ^n)*
      (sourceQ n).comp (C δ⁻¹*X) := by
    simpa only [Nat.add_sub_cancel,hs,q] using
      (source_jensen_integral_extension (n+1) (by omega)).2.1
  have hinv:ξ⁻¹=((n+1:ℕ):ℝ)/(n:ℝ)*t := by dsimp [ξ,δ]; field_simp <;> ring
  have hy:ξ*δ⁻¹=t⁻¹ := by dsimp [ξ]; field_simp <;> ring
  have hyn:(ξ*δ⁻¹)⁻¹=t := by rw [hy,inv_inv]
  have hqp:q.derivative.eval ξ=0 := by
    rw [hder]
    simp only [eval_mul,eval_C,eval_comp,eval_X]
    rw [mul_comm δ⁻¹ ξ,reflection_eval n (by positivity),hyn,hnode,mul_zero,mul_zero]
  have hD:=reflection_derivative hn (by positivity : ξ*δ⁻¹≠0)
  rw [hyn,hnode,mul_zero,zero_sub] at hD
  have hqpp:q.derivative.derivative.eval ξ=
      ((n+1:ℕ):ℝ)*δ^n*(sourceQ n).derivative.eval (ξ*δ⁻¹)*δ⁻¹ := by
    have hh:=(((sourceQ n).hasDerivAt (ξ*δ⁻¹)).comp ξ
      ((hasDerivAt_id ξ).mul_const δ⁻¹)).const_mul (((n+1:ℕ):ℝ)*δ^n)
    have he:(fun x:ℝ => q.derivative.eval x)=
        fun x =>((n+1:ℕ):ℝ)*δ^n*(sourceQ n).eval (x*δ⁻¹) := by
      ext x; rw [hder]; simp [mul_comm δ⁻¹ x]
    have hp:=q.derivative.hasDerivAt ξ
    rw [he] at hp
    convert! hp.unique hh using 1 <;> ring
  have hsecond:ξ^2*q.derivative.derivative.eval ξ= -(n:ℝ)*ξ^n*fullD n t := by
    have hnδ:((n+1:ℕ):ℝ)*δ=(n:ℝ) := by dsimp [δ]; field_simp
    have hc:δ^n*(ξ*δ⁻¹)^n=ξ^n := by
      rw [←mul_pow]
      congr 1
      field_simp <;> ring
    rw [hqpp]
    calc
      _ = ((n+1:ℕ):ℝ)*δ^(n+1)*((ξ*δ⁻¹)^2*(sourceQ n).derivative.eval (ξ*δ⁻¹)) := by
        rw [pow_succ]
        field_simp [hδ.ne'] <;> ring
      _ = ((n+1:ℕ):ℝ)*δ^(n+1)*(-((ξ*δ⁻¹)^n*fullD n t)) := by rw [hD]
      _ = -(((n+1:ℕ):ℝ)*δ)*(δ^n*(ξ*δ⁻¹)^n)*fullD n t := by rw [pow_succ]; ring
      _ = _ := by rw [hnδ,hc]
  have hG:((n+1:ℕ):ℝ)*q.eval ξ=ξ^n*fullG n t := by
    have hh:=congrArg (fun p:ℝ[X] => p.eval (-ξ⁻¹)) hlow
    simp only [eval_sub,eval_mul,eval_C,eval_X,eval_comp,Nat.add_sub_cancel,hs] at hh
    have hsmall:δ*(-ξ⁻¹)= -t := by rw [hinv]; dsimp [δ]; field_simp <;> ring
    rw [hsmall,←(original_moment_bridge n t).2.1,hnode] at hh
    have hp: -(sourceP (n+1)).derivative.eval (-ξ⁻¹)=fullG n t := by
      have he:originalJ (n+1)=fun u:ℝ =>(sourceP (n+1)).eval (-u) :=
        funext (fun u =>(original_moment_bridge (n+1) u).2.1)
      have hd:HasDerivAt (originalJ (n+1)) (fullG n t) ξ⁻¹ := by
        rw [hinv]; exact (full_G_extraction hn t).2
      have hpoly:=((sourceP (n+1)).hasDerivAt (-ξ⁻¹)).comp ξ⁻¹ (hasDerivAt_id ξ⁻¹).neg
      rw [he] at hd
      simpa only [Function.comp_def,id_eq,mul_neg,mul_one] using (hd.unique hpoly).symm
    rw [reflection_eval (n+1) hξ.ne', (original_moment_bridge (n+1) ξ⁻¹).2.1]
    have hp':(sourceP (n+1)).derivative.eval (-ξ⁻¹)= -fullG n t := by linarith
    rw [hp'] at hh
    have hh':((n+1:ℕ):ℝ)*(sourceP (n+1)).eval (-ξ⁻¹)=ξ⁻¹*fullG n t := by
      field_simp at hh
      simp only [one_div] at hh ⊢
      have h0:ξ*(((n+1:ℕ):ℝ)*(sourceP (n+1)).eval (-ξ⁻¹))=fullG n t := by nlinarith only [hh]
      calc
        _ = ξ⁻¹*(ξ*(((n+1:ℕ):ℝ)*(sourceP (n+1)).eval (-ξ⁻¹))) := by field_simp <;> ring
        _ = _ := by rw [h0]
    rw [pow_succ]
    calc
      _ = ξ^n*ξ*(((n+1:ℕ):ℝ)*(sourceP (n+1)).eval (-ξ⁻¹)) := by ring
      _ = ξ^n*ξ*(ξ⁻¹*fullG n t) := by rw [hh']
      _ = _ := by field_simp <;> ring
  have hpow:ξ^2*ξ^(2*n-2)=ξ^n*ξ^n := by
    rw [←pow_add,←pow_add]; congr 1; omega
  have hproduct:q.eval ξ*q.derivative.derivative.eval ξ=
      -((n:ℝ)/((n+1:ℕ):ℝ))*ξ^(2*n-2)*fullD n t*fullG n t := by
    apply (mul_left_cancel₀ (show ((n+1:ℕ):ℝ)*ξ^2≠0 by positivity))
    calc
      _ = (((n+1:ℕ):ℝ)*q.eval ξ)*(ξ^2*q.derivative.derivative.eval ξ) := by ring
      _ = (ξ^n*fullG n t)*(-(n:ℝ)*ξ^n*fullD n t) := by rw [hG,hsecond]
      _ = -(n:ℝ)*(ξ^2*ξ^(2*n-2))*fullD n t*fullG n t := by rw [hpow]; ring
      _ = _ := by field_simp <;> ring
  have hnonzero:fullD n t≠0 ↔ q.derivative.derivative.eval ξ≠0 := by
    have hc: -(n:ℝ)*ξ^n≠0 := mul_ne_zero (neg_ne_zero.mpr hn0.ne') (pow_ne_zero _ hξ.ne')
    constructor
    · intro hd he; rw [he,mul_zero] at hsecond
      exact (mul_ne_zero hc hd) hsecond.symm
    · intro hq hd; rw [hd,mul_zero] at hsecond
      exact hq ((mul_eq_zero.mp hsecond).resolve_left (by positivity))
  dsimp only
  refine ⟨hξ,hqp,hG,hsecond,hproduct,hnonzero,?_⟩
  intro hd
  have hqpp0:=hnonzero.mp hd
  have hcoupling:SourceJensenPositiveExtension.sourceCoupling (n+1) ξ=
      (ξ^2/(n:ℝ))*(fullG n t/fullD n t) := by
    dsimp [SourceJensenPositiveExtension.sourceCoupling]
    change -((n+1:ℕ):ℝ)*q.eval ξ/q.derivative.derivative.eval ξ=_
    have hqval:q.eval ξ=ξ^n*fullG n t/((n+1:ℕ):ℝ) := by
      apply (eq_div_iff hh0.ne').mpr
      nlinarith only [hG]
    have hpp:q.derivative.derivative.eval ξ= -(n:ℝ)*ξ^n*fullD n t/ξ^2 := by
      apply (eq_div_iff (pow_ne_zero 2 hξ.ne')).mpr
      nlinarith only [hsecond]
    rw [hqval,hpp]
    field_simp [hd,hn0.ne',hh0.ne',hξ.ne'] <;> ring
  refine ⟨hcoupling,?_⟩
  rw [hcoupling]
  have hc:0<ξ^2/(n:ℝ) := by positivity
  rw [mul_nonneg_iff_of_pos_left hc]
  have he:fullG n t/fullD n t=(fullD n t*fullG n t)/(fullD n t)^2 := by
    field_simp [hd] <;> ring
  rw [he]
  constructor
  · intro h
    have hh:=(le_div_iff₀ (sq_pos_of_ne_zero hd)).mp h
    simpa only [zero_mul] using hh
  · intro h
    exact div_nonneg h (sq_nonneg _)

end D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
