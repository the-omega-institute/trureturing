/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Parameter
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reciprocal-degree derivatives of the geometric input for compact curvature bounds. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Curvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Real bounds for the reciprocal-degree derivative, including inputs at the zero endpoint. -/

namespace RefinedBMV.FourSpectrumLift

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The first exponential moment on the unit interval. -/
def zeroCenterFirstMoment (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * Real.exp (-x*t)

private theorem exponential_weight_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ t * Real.exp (-x*t)) volume 0 1 :=
  (by fun_prop : Continuous (fun t : ℝ ↦ t * Real.exp (-x*t))).intervalIntegrable 0 1

theorem zeroCenterFirstMoment_anti : Antitone zeroCenterFirstMoment := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on zero_le_one
    (exponential_weight_integrable y) (exponential_weight_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hxy) ht.1)

theorem zeroCenterFirstMoment_zero : zeroCenterFirstMoment 0 = 1/2 := by
  unfold zeroCenterFirstMoment
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ ↦ x^2/2) t t := by
    convert ((hasDerivAt_id t).pow 2).div_const 2 using 1
    · rfl
    · norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (continuous_id.intervalIntegrable 0 1)]
  norm_num

theorem zeroCenterFirstMoment_eq {x : ℝ} (hx : x ≠ 0) :
    zeroCenterFirstMoment x = (1 - (1+x) * Real.exp (-x))/x^2 := by
  let f (t : ℝ) := -((1+x*t) * Real.exp (-x*t))/x^2
  have hd (t : ℝ) : HasDerivAt f (t * Real.exp (-x*t)) t := by
    have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-x*y)) (-x * Real.exp (-x*t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-x)).exp
    have hl : HasDerivAt (fun y : ℝ ↦ 1+x*y) x t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul x).const_add 1
    convert ((hl.mul he).neg.div_const (x^2)) using 1
    field_simp
    <;> ring
  unfold zeroCenterFirstMoment
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (exponential_weight_integrable x)]
  dsimp [f]
  simp only [mul_one, mul_zero, add_zero, Real.exp_zero]
  field_simp
  <;> ring

/-- Derivative of the geometric quotient with respect to the reciprocal degree. -/
theorem hasDerivAt_zeroCenterGeometric_parameter {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    HasDerivAt (zeroCenterGeometric c) (-9*c^2 * zeroCenterFirstMoment (3*h*c)) h := by
  have ht : 0 < 3*h*c := by positivity
  have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-3*y*c))
      (-3*c*Real.exp (-3*h*c)) h := by
    have hd := ((hasDerivAt_id h).const_mul (-3*c)).exp
    simp only [id_eq, mul_one] at hd
    have heq (y : ℝ) : -3*y*c = (-3*c)*y := by ring
    simp only [heq]
    rw [mul_comm (-3*c)]
    exact hd
  have hf := ((hasDerivAt_const h (1 : ℝ)).sub he).div (hasDerivAt_id h) hh.ne'
  have hEq : (fun y ↦ (1-Real.exp (-3*y*c))/y) =ᶠ[𝓝 h] zeroCenterGeometric c := by
    filter_upwards [lt_mem_nhds hh] with y hy
    rw [zeroCenterGeometric, ite_eq_right (ne_of_gt hy)]
  have hd := hf.congr_of_eventuallyEq hEq.symm
  convert hd using 1
  change -9*c^2 * zeroCenterFirstMoment (3*h*c) =
    (((0 - (-3*c*Real.exp (-3*h*c))) * h) - (1-Real.exp (-3*h*c)) * 1) / h^2
  rw [zeroCenterFirstMoment_eq ht.ne', show -(3*h*c) = -3*h*c by ring]
  field_simp
  <;> ring

#print axioms hasDerivAt_zeroCenterGeometric_parameter


/-- A value and its reciprocal-degree derivative. This type can also carry
rational interval expressions for the two components. -/
structure ParameterTangent (R : Type) where
  value : R
  deriv : R

namespace ParameterTangent

variable {R : Type}

def constant [Zero R] (r : R) : ParameterTangent R := ⟨r, 0⟩

instance [Zero R] : Zero (ParameterTangent R) := ⟨constant 0⟩

instance [Zero R] {n : ℕ} [OfNat R n] : OfNat (ParameterTangent R) n := ⟨constant (OfNat.ofNat n)⟩

instance [Add R] : Add (ParameterTangent R) :=
  ⟨fun a b ↦ ⟨a.value + b.value, a.deriv + b.deriv⟩⟩

instance [Sub R] : Sub (ParameterTangent R) :=
  ⟨fun a b ↦ ⟨a.value - b.value, a.deriv - b.deriv⟩⟩

instance [Neg R] : Neg (ParameterTangent R) :=
  ⟨fun a ↦ ⟨-a.value, -a.deriv⟩⟩

instance [Add R] [Mul R] : Mul (ParameterTangent R) :=
  ⟨fun a b ↦ ⟨a.value * b.value, a.deriv * b.value + a.value * b.deriv⟩⟩

instance [Sub R] [Mul R] [Div R] : Div (ParameterTangent R) :=
  ⟨fun a b ↦
    let q := a.value / b.value
    ⟨q, (a.deriv - q * b.deriv) / b.value⟩⟩

def sqrtFrom [OfNat R 2] [Mul R] [Div R] (a : ParameterTangent R) (r : R) :
    ParameterTangent R := ⟨r, a.deriv / (2 * r)⟩

private def Has (f : ℝ → ParameterTangent ℝ) (h : ℝ) : Prop :=
  HasDerivAt (fun x ↦ (f x).value) (f h).deriv h

private theorem has_constant (r h : ℝ) : Has (fun _ ↦ constant r) h :=
  hasDerivAt_const h r

private theorem Has.add {f g : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) (hg : Has g h) :
    Has (fun x ↦ f x + g x) h := HasDerivAt.add hf hg

private theorem Has.sub {f g : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) (hg : Has g h) :
    Has (fun x ↦ f x - g x) h := HasDerivAt.sub hf hg

private theorem Has.mul {f g : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) (hg : Has g h) :
    Has (fun x ↦ f x * g x) h := HasDerivAt.mul hf hg

private theorem Has.neg {f : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) :
    Has (fun x ↦ -f x) h := HasDerivAt.neg hf

private theorem Has.div {f g : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) (hg : Has g h)
    (hn : (g h).value ≠ 0) : Has (fun x ↦ f x / g x) h := by
  change HasDerivAt (fun x ↦ (f x).value / (g x).value)
    (((f h).deriv - (f h).value / (g h).value * (g h).deriv) / (g h).value) h
  convert HasDerivAt.div hf hg hn using 1
  field_simp
  <;> ring

private theorem Has.root {f : ℝ → ParameterTangent ℝ} {h : ℝ}
    (hf : Has f h) (hn : (f h).value ≠ 0) :
    Has (fun x ↦ sqrtFrom (f x) (Real.sqrt (f x).value)) h :=
  HasDerivAt.sqrt hf hn

private theorem Has.exp {f : ℝ → ParameterTangent ℝ} {h : ℝ} (hf : Has f h) :
    Has (fun x ↦ ⟨Real.exp (f x).value, Real.exp (f x).value * (f x).deriv⟩) h :=
  HasDerivAt.exp hf

end ParameterTangent

open ParameterTangent

private def parameterH (h : ℝ) : ParameterTangent ℝ := ⟨h, 1⟩

private def parameterS (c h : ℝ) : ParameterTangent ℝ :=
  ⟨zeroCenterGeometric c h, -(9*c*c) * zeroCenterFirstMoment (3*h*c)⟩

private def parameterQ (c h : ℝ) : ParameterTangent ℝ :=
  ⟨Real.exp (-3*h*c), Real.exp (-3*h*c) * (-3*c)⟩

private def parameterZ (c h : ℝ) : ParameterTangent ℝ :=
  ⟨Real.exp (-(3*(1+h))*c), Real.exp (-(3*(1+h))*c) * (-3*c)⟩

private def parameterU (c h : ℝ) : ParameterTangent ℝ :=
  ⟨Real.exp (-(1+3*h)*c), Real.exp (-(1+3*h)*c) * (-3*c)⟩

private def parameterE (c : ℝ) : ParameterTangent ℝ := constant (Real.exp (-2*c))

private def parameterRadicand (c h : ℝ) : ParameterTangent ℝ :=
  (zeroCenterRadicandJet (parameterH h) (parameterS c h) (parameterQ c h)
    (parameterZ c h) (parameterE c)).value

private def parameterRoot (c h : ℝ) : ParameterTangent ℝ :=
  sqrtFrom (parameterRadicand c h) (Real.sqrt (parameterRadicand c h).value)

/-- Lift the arithmetic curvature formula to the reciprocal-degree coordinate. -/
def zeroCenterParameterSlopeFrom {R : Type} [Zero R] [OfNat R 1] [OfNat R 2] [OfNat R 3]
    [OfNat R 4] [OfNat R 9] [Add R] [Sub R] [Neg R] [Mul R] [Div R]
    (c h s q z e u root moment : R) : R :=
  let hT : ParameterTangent R := ⟨h, 1⟩
  let sT : ParameterTangent R := ⟨s, -(9*c*c) * moment⟩
  let qT : ParameterTangent R := ⟨q, q * (-3*c)⟩
  let zT : ParameterTangent R := ⟨z, z * (-3*c)⟩
  let eT := constant e
  let uT : ParameterTangent R := ⟨u, u * (-3*c)⟩
  let rad := (zeroCenterRadicandJet hT sT qT zT eT).value
  (zeroCenterCurvature hT sT qT zT eT uT (sqrtFrom rad root)).deriv

/-- The reciprocal-degree derivative of normalized curvature at a real point. -/
def zeroCenterCurvatureParameterSlope (c h : ℝ) : ℝ :=
  zeroCenterParameterSlopeFrom c h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
    (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
    (Real.sqrt (parameterRadicand c h).value) (zeroCenterFirstMoment (3*h*c))


private def JetHas (f : ℝ → CurvatureJet (ParameterTangent ℝ)) (h : ℝ) : Prop :=
  Has (fun x ↦ (f x).value) h ∧ Has (fun x ↦ (f x).first) h ∧ Has (fun x ↦ (f x).second) h

private theorem jet_has_const (r h : ℝ) :
    JetHas (fun _ ↦ CurvatureJet.const (constant r)) h :=
  ⟨has_constant r h, has_constant 0 h, has_constant 0 h⟩

private theorem JetHas.add {f g : ℝ → CurvatureJet (ParameterTangent ℝ)} {h : ℝ}
    (hf : JetHas f h) (hg : JetHas g h) :
    JetHas (fun x ↦ CurvatureJet.add (f x) (g x)) h :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩

private theorem JetHas.sub {f g : ℝ → CurvatureJet (ParameterTangent ℝ)} {h : ℝ}
    (hf : JetHas f h) (hg : JetHas g h) :
    JetHas (fun x ↦ CurvatureJet.sub (f x) (g x)) h :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, hf.2.2.sub hg.2.2⟩

private theorem JetHas.scale {f : ℝ → CurvatureJet (ParameterTangent ℝ)}
    {a : ℝ → ParameterTangent ℝ} {h : ℝ}
    (hf : JetHas f h) (ha : Has a h) : JetHas (fun x ↦ CurvatureJet.scale (a x) (f x)) h :=
  ⟨ha.mul hf.1, ha.mul hf.2.1, ha.mul hf.2.2⟩

private theorem JetHas.mul {f g : ℝ → CurvatureJet (ParameterTangent ℝ)} {h : ℝ}
    (hf : JetHas f h) (hg : JetHas g h) :
    JetHas (fun x ↦ CurvatureJet.mul (f x) (g x)) h :=
  ⟨hf.1.mul hg.1, (hf.1.mul hg.2.1).add (hf.2.1.mul hg.1),
    ((hf.1.mul hg.2.2).add (hf.2.1.mul hg.2.1)).add (hf.2.2.mul hg.1)⟩

private theorem JetHas.quot {f g : ℝ → CurvatureJet (ParameterTangent ℝ)} {h : ℝ}
    (hf : JetHas f h) (hg : JetHas g h) (hn : (g h).value.value ≠ 0) :
    JetHas (fun x ↦ CurvatureJet.quot (f x) (g x)) h := by
  have h₀ := hf.1.div hg.1 hn
  have h₁ := (hf.2.1.sub (hg.2.1.mul h₀)).div hg.1 hn
  exact ⟨h₀, h₁, (hf.2.2.sub ((hg.2.1.mul h₁).add (hg.2.2.mul h₀))).div hg.1 hn⟩

private theorem JetHas.sqrtFrom {f : ℝ → CurvatureJet (ParameterTangent ℝ)} {h : ℝ}
    (hf : JetHas f h) (hp : 0 < (f h).value.value) :
    JetHas (fun x ↦ CurvatureJet.sqrtFrom (f x)
      (sqrtFrom (f x).value (Real.sqrt (f x).value.value))) h := by
  have hr := hf.1.root hp.ne'
  have hden := (has_constant 2 h).mul hr
  have hn : (2 : ℝ) * Real.sqrt (f h).value.value ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hp).ne'
  have h₁ := hf.2.1.div hden hn
  exact ⟨hr, h₁, (hf.2.2.sub (h₁.mul h₁)).div hden hn⟩

private theorem jet_has_exp {k e : ℝ → ParameterTangent ℝ} {h : ℝ}
    (hk : Has k h) (he : Has e h) :
    JetHas (fun x ↦ CurvatureJet.exponential (k x) (e x)) h :=
  ⟨he, hk.mul he, ((hk.mul hk).mul he).div (has_constant 2 h) two_ne_zero⟩

private theorem has_parameter_exp (a b c h : ℝ) :
    Has (fun x ↦ ⟨Real.exp (-(a+b*x)*c), Real.exp (-(a+b*x)*c) * (-b*c)⟩) h := by
  change HasDerivAt (fun x ↦ Real.exp (-(a+b*x)*c)) _ h
  have hv : HasDerivAt (fun x ↦ -(a+b*x)*c) (-b*c) h := by
    have hv' := (((hasDerivAt_id h).const_mul b).const_add a).neg.mul_const c
    change HasDerivAt (fun x ↦ -(a+b*x)*c) (-(b*1)*c) h at hv'
    simpa only [mul_one] using hv'
  exact hv.exp

private theorem parameterQ_has (c h : ℝ) : Has (parameterQ c) h := by
  convert has_parameter_exp 0 3 c h using 1
  funext x
  unfold parameterQ
  rw [show -(0+3*x)*c = -3*x*c by ring]

private theorem parameterZ_has (c h : ℝ) : Has (parameterZ c) h := by
  convert has_parameter_exp 3 3 c h using 1
  funext x
  unfold parameterZ
  rw [show -(3*(1+x))*c = -(3+3*x)*c by ring]

private theorem parameterU_has (c h : ℝ) : Has (parameterU c) h :=
  has_parameter_exp 1 3 c h

private def parameterGeomJet (c h : ℝ) : CurvatureJet (ParameterTangent ℝ) :=
  zeroCenterGeometricJet (parameterH h) (parameterS c h) (parameterQ c h)

private theorem jet_has_parameterGeom {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    JetHas (parameterGeomJet c) h := by
  have hs : Has (parameterS c) h := by
    change HasDerivAt (zeroCenterGeometric c) _ h
    convert hasDerivAt_zeroCenterGeometric_parameter hc hh using 1
    simp only [parameterS]
    ring
  have hh' : Has parameterH h := hasDerivAt_id h
  have hq := parameterQ_has c h
  exact ⟨hs, (has_constant 3 h).mul hq,
    (((has_constant 9 h).mul hh').mul hq).neg.div (has_constant 2 h) two_ne_zero⟩

private theorem parameterRadicand_value {c h : ℝ} (hh : h ≠ 0) :
    (parameterRadicand c h).value = rationalizedRadicand c h :=
  zeroCenterRadicandJet_value c h hh

private theorem jet_has_parameterQuotient {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    JetHas (fun x ↦ zeroCenterQuotientJet (parameterH x) (parameterS c x)
      (parameterQ c x) (parameterZ c x) (parameterE c) (parameterU c x) (parameterRoot c x)) h := by
  have hH : Has parameterH h := hasDerivAt_id h
  have hgeom := jet_has_parameterGeom hc hh
  have ha := hgeom.scale ((has_constant 1 h).add hH)
  have hb := hgeom.scale ((has_constant 1 h).add ((has_constant 2 h).mul hH))
  have hz := jet_has_exp (((has_constant 3 h).mul ((has_constant 1 h).add hH)).neg)
    (parameterZ_has c h)
  have hv := (jet_has_const 1 h).sub hz
  have he := jet_has_exp ((has_constant 2 h).neg) (has_constant (Real.exp (-2*c)) h)
  have hu := jet_has_exp (((has_constant 1 h).add ((has_constant 3 h).mul hH)).neg)
    (parameterU_has c h)
  have hhalf := (has_constant 1 h).div (has_constant 2 h) two_ne_zero
  have hr := ((jet_has_const 1 h).sub (hz.mul ((jet_has_const 1 h).add ha))).sub
    (((ha.mul hb).mul he).scale hhalf)
  have hrpos : 0 < (parameterRadicand c h).value := by
    rw [parameterRadicand_value hh.ne']
    apply pos_of_mul_pos_right _ (Real.exp_pos ((3+6*h)*c)).le
    exact (by positivity : 0 < 27 * (1+h) * (1+2*h) * (1+3*h) * c^4 / 24).trans_le
      (rationalized_radicand_lower hc.le hh)
  have hA : 0 < (1+h) * zeroCenterGeometric c h := by
    unfold zeroCenterGeometric
    rw [ite_eq_right hh.ne']
    exact mul_pos (by positivity) (div_pos
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr
        (mul_neg_of_neg_of_pos (by linarith) hc))) hh)
  have hD : 0 < 1 - Real.exp (-(3*(1+h))*c) + Real.sqrt (parameterRadicand c h).value :=
    add_pos_of_pos_of_nonneg
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hc)))
      (Real.sqrt_nonneg _)
  exact ((hb.scale hhalf).add (hu.mul ((jet_has_const 1 h).sub (hv.quot ha hA.ne')))).quot
    (hv.add (hr.sqrtFrom hrpos)) hD.ne'

/-- The arithmetic lift computes the actual derivative in the reciprocal-degree
coordinate throughout the positive-gap, positive-parameter region. -/
theorem hasDerivAt_zeroCenterCurvature_parameter {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    HasDerivAt (fun x ↦ zeroCenterCurvatureAt x c) (zeroCenterCurvatureParameterSlope c h) h := by
  let f (x : ℝ) := zeroCenterCurvature (parameterH x) (parameterS c x)
    (parameterQ c x) (parameterZ c x) (parameterE c) (parameterU c x) (parameterRoot c x)
  have hj := jet_has_parameterQuotient hc hh
  have hf : Has f h :=
    (((has_constant 2 h).mul hj.2.2).sub hj.2.1).add
      (hj.1.div (has_constant 4 h) (show (4 : ℝ) ≠ 0 by norm_num))
  have he : (fun x ↦ (f x).value) =ᶠ[𝓝 h] (fun x ↦ zeroCenterCurvatureAt x c) := by
    filter_upwards [lt_mem_nhds hh] with x hx
    unfold f zeroCenterCurvatureAt
    change zeroCenterCurvature x (zeroCenterGeometric c x) (Real.exp (-3*x*c))
      (Real.exp (-(3*(1+x))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*x)*c))
      (Real.sqrt (parameterRadicand c x).value) = _
    rw [parameterRadicand_value hx.ne']
  exact (show HasDerivAt (fun x ↦ (f x).value) (f h).deriv h from hf).congr_of_eventuallyEq he.symm

#print axioms hasDerivAt_zeroCenterCurvature_parameter


/-- Use the rationalized radical at positive reciprocal degree. -/
theorem zeroCenterCurvatureParameterSlope_eq {c h : ℝ} (hh : 0 < h) :
    zeroCenterCurvatureParameterSlope c h =
      zeroCenterParameterSlopeFrom c h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
        (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
        (Real.sqrt (rationalizedRadicand c h)) (zeroCenterFirstMoment (3*h*c)) := by
  unfold zeroCenterCurvatureParameterSlope
  rw [parameterRadicand_value hh.ne']

/-- Two coordinate slope bounds transport a lower bound on normalized
curvature at a rectangular center to every point in the positive rectangle. -/
theorem zeroCenterCurvatureAt_pos_of_two_slopes
    {c h a b d e L Mc Mh : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hc : c ∈ Icc a b) (hp : h ∈ Icc d e) (hd : 0 ≤ d)
    (hL : L ≤ zeroCenterCurvatureAt ((d+e)/2) ((a+b)/2))
    (hMc : 0 ≤ Mc) (hMh : 0 ≤ Mh)
    (hsC : ∀ x ∈ Icc a b, |zeroCenterCurvatureSlopeAt h x| ≤ Mc)
    (hsH : ∀ y ∈ Icc d e, 0 < y →
      |zeroCenterCurvatureParameterSlope ((a+b)/2) y| ≤ Mh)
    (hsep : Mc*((b-a)/2) + Mh*((e-d)/2) < L) :
    0 < zeroCenterCurvatureAt h c := by
  let cm := (a+b)/2
  let hm := (d+e)/2
  have he : 0 < e := hh.trans_le hp.2
  have hmpos : 0 < hm := by dsimp [hm]; linarith
  have hmh : hm ∈ Icc d e := ⟨by dsimp [hm]; linarith [hp.1, hp.2],
    by dsimp [hm]; linarith [hp.1, hp.2]⟩
  have hcm : 0 < cm := by dsimp [cm]; linarith [hc.1, hc.2]
  let s := Icc d e ∩ Ioi (0 : ℝ)
  have hxc : hm ∈ s := ⟨hmh, hmpos⟩
  have hxh : h ∈ s := ⟨hp, hh⟩
  have hdiff (y : ℝ) (hy : y ∈ s) :
      HasDerivWithinAt (fun y ↦ zeroCenterCurvatureAt y cm)
        (zeroCenterCurvatureParameterSlope cm y) s y :=
    (hasDerivAt_zeroCenterCurvature_parameter hcm hy.2).hasDerivWithinAt
  have hnorm := ((convex_Icc d e).inter (convex_Ioi _)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdiff (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hsH y hy.1 hy.2) hxc hxh
  simp only [Real.norm_eq_abs] at hnorm
  have hdist : |h-hm| ≤ (e-d)/2 := abs_le.mpr
    ⟨by dsimp [hm]; linarith [hp.1], by dsimp [hm]; linarith [hp.2]⟩
  have hv := hnorm.trans (mul_le_mul_of_nonneg_left hdist hMh)
  have hlo : L - Mh*((e-d)/2) ≤ zeroCenterCurvatureAt h cm := by
    linarith [(abs_le.mp hv).1]
  exact zeroCenterCurvatureAt_pos_of_slope hh ha hc hlo hMc hsC (by linarith)

end
end RefinedBMV.FourSpectrumLift
