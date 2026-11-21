/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticPartner
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticPartner
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticPartnerPolynomial, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature]
   utility: none
   digest: Cross-multiplied normalized observations turn the seven regular equations and the coherence equation into a polynomial system for analytic inversion. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticPartnerPolynomial
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The polynomial partner construction for the literal normalized hard-core observations. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticPartner

open PeriodicMPSAnalyticPartnerPolynomial
open PeriodicMPSUniformHardCoreFirstJet (Coord cores witness entry component regularReadout)
open PeriodicMPSUniformHardCoreTransferRecurrence
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open Filter Polynomial Complex Asymptotics
open scoped Topology

open private twoMass normalizedTwo map_raw map_chart from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
open private rawTwo_eq_trace from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreTransferRecurrence
open private mass_pos_witness from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature

noncomputable section

def imagDirection (w : Parameters) : Fin 4 → ℝ :=
  ![w.2.2, w.1 0, w.1 1, w.1 2]

/-- The fixed partner ansatz, with the last imaginary slope free. -/
def chart (ε : ℝ) (w : Parameters) : Coord :=
  fun i => witness i + (↑(imagDirection w i * ε) : ℂ) * I + ↑(w.2.1 i * ε ^ 2)

/-- The first path has slopes `(1, -s, 1, 0)` and zero real quadratic correction. -/
def original (s : ℝ) : Parameters := (![ -s, 1, 0], 0, 1)

@[simp] theorem chart_zero (w : Parameters) : chart 0 w = witness := by
  funext i
  simp [chart]

@[simp] theorem chart_re (ε : ℝ) (w : Parameters) (i : Fin 4) :
    (chart ε w i).re = (witness i).re + w.2.1 i * ε ^ 2 := by
  simp only [chart, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp] theorem chart_im (ε : ℝ) (w : Parameters) (i : Fin 4) :
    (chart ε w i).im = imagDirection w i * ε := by
  simp only [chart, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  fin_cases i <;> simp [witness]

private def imagDirectionCLM (i : Fin 4) : Parameters →L[ℝ] ℝ :=
  ![((ContinuousLinearMap.snd ℝ RealRegular ℝ).comp (ContinuousLinearMap.snd ℝ Imaginary _)),
    ((ContinuousLinearMap.proj 0 : Imaginary →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ _ _)),
    ((ContinuousLinearMap.proj 1 : Imaginary →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ _ _)),
    ((ContinuousLinearMap.proj 2 : Imaginary →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ _ _))] i

private theorem imagDirectionCLM_apply (w : Parameters) (i : Fin 4) :
    imagDirectionCLM i w = imagDirection w i := by
  fin_cases i <;> rfl

private def realDirectionCLM (i : Fin 4) : Parameters →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : RealRegular →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.fst ℝ RealRegular ℝ).comp (ContinuousLinearMap.snd ℝ Imaginary _))

private theorem realDirectionCLM_apply (w : Parameters) (i : Fin 4) :
    realDirectionCLM i w = w.2.1 i := rfl

theorem analyticAt_imagDirection (w : Parameters) (i : Fin 4) :
    AnalyticAt ℝ (fun v => imagDirection v i) w := by
  have h : (⇑(imagDirectionCLM i)) = fun v => imagDirection v i :=
    funext fun v => imagDirectionCLM_apply v i
  rw [← h]
  exact (imagDirectionCLM i).analyticAt w

theorem analyticAt_realDirection (w : Parameters) (i : Fin 4) :
    AnalyticAt ℝ (fun v : Parameters => v.2.1 i) w := (realDirectionCLM i).analyticAt w

theorem analyticAt_chart (q : ℝ × Parameters) :
    AnalyticAt ℝ (fun q : ℝ × Parameters => chart q.1 q.2) q := by
  apply AnalyticAt.pi
  intro i
  have hε := (ContinuousLinearMap.fst ℝ ℝ Parameters).analyticAt q
  have hw := (ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt q
  have hi := ((analyticAt_imagDirection q.2 i).comp hw).mul hε
  have hr := ((analyticAt_realDirection q.2 i).comp hw).mul (hε.pow 2)
  exact (analyticAt_const.add (((ofRealCLM.analyticAt _).comp hi).mul analyticAt_const)).add
    ((ofRealCLM.analyticAt _).comp hr)

@[simp] theorem chart_neg (ε : ℝ) (w : Parameters) (i : Fin 4) :
    chart (-ε) w i = star (chart ε w i) := by
  apply Complex.ext <;>
    fin_cases i <;> simp [chart, witness, imagDirection, Complex.mul_re, Complex.mul_im]

/-- Complex-valued analytic parameter functions form a subring, so the transfer
product can be formed as one finite polynomial before specializing the parameters. -/
def analyticCoefficients : Subring (Parameters → ℂ) where
  carrier := {f | ∀ w, AnalyticAt ℝ f w}
  zero_mem' := fun _ => analyticAt_const
  one_mem' := fun _ => analyticAt_const
  add_mem' hf hg := fun w => (hf w).add (hg w)
  neg_mem' hf := fun w => (hf w).neg
  mul_mem' hf hg := fun w => (hf w).mul (hg w)

abbrev Coefficients := analyticCoefficients

private def atParameter (w : Parameters) : Coefficients →+* ℂ :=
  (Pi.evalRingHom _ w).comp analyticCoefficients.subtype

private def conjCoeff : Coefficients →+* Coefficients where
  toFun a := ⟨fun w => star (a.val w), fun w =>
    (Complex.conjCLE.toContinuousLinearEquiv.analyticAt _).comp (a.property w)⟩
  map_zero' := by ext w; simp
  map_one' := by ext w; simp
  map_add' a b := by ext w; exact map_add (starRingEnd ℂ) _ _
  map_mul' a b := by ext w; exact map_mul (starRingEnd ℂ) _ _

private def paramCoordinate (i : Fin 4) : Polynomial Coefficients :=
  C ⟨fun _ => witness i, fun _ => analyticAt_const⟩ +
    C ⟨fun w => (↑(imagDirection w i) : ℂ) * I, fun w =>
      ((ofRealCLM.analyticAt _).comp (analyticAt_imagDirection w i)).mul analyticAt_const⟩ * X +
    C ⟨fun w => (↑(w.2.1 i) : ℂ), fun w =>
      (ofRealCLM.analyticAt _).comp (analyticAt_realDirection w i)⟩ * X ^ 2

private def paramChart : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial Coefficients) :=
  hardCoreChart (paramCoordinate 0) (paramCoordinate 1) (paramCoordinate 2) (paramCoordinate 3)

def evalParam (ε : ℝ) (w : Parameters) : Polynomial Coefficients →+* ℂ :=
  eval₂RingHom (atParameter w) (ε : ℂ)

private theorem evalParam_coordinate (ε : ℝ) (w : Parameters) (i : Fin 4) :
    evalParam ε w (paramCoordinate i) = chart ε w i := by
  simp [evalParam, paramCoordinate, atParameter, chart]
  ring

private theorem evalParam_chart (ε : ℝ) (w : Parameters) (i : Fin 2) :
    (evalParam ε w).mapMatrix (paramChart i) = cores (chart ε w) i := by
  rw [paramChart, map_chart]
  simp only [evalParam_coordinate, cores]

private theorem evalParam_conj (ε : ℝ) (w : Parameters) (p : Polynomial Coefficients) :
    evalParam ε w (p.map conjCoeff) = star (evalParam ε w p) := by
  change eval₂ (atParameter w) (ε : ℂ) (p.map conjCoeff) =
    starRingEnd ℂ (p.eval₂ (atParameter w) (ε : ℂ))
  rw [eval₂_map, hom_eval₂]
  have hs : starRingEnd ℂ (ε : ℂ) = (ε : ℂ) := Complex.conj_ofReal ε
  rw [hs]
  rfl

/-- The raw polynomial in ε before specializing the eight coefficients of the chart. -/
def rawFamily (r : Fin 8) (n : ℕ) : Polynomial Coefficients :=
  let B := fun i => (paramChart i).map (Polynomial.map conjCoeff)
  (binaryInsertion paramChart B (entry r).1 (entry r).2 * binaryTransfer paramChart B ^ (n - 2)).trace

theorem evalParam_rawFamily (r : Fin 8) (n : ℕ) (ε : ℝ) (w : Parameters) :
    evalParam ε w (rawFamily r (n + 4)) =
      rawTwo (cores (chart ε w)) n (entry r).1 (entry r).2 := by
  rw [rawFamily, rawTwo_eq_trace]
  have h : n + 4 - 2 = n + 2 := by omega
  rw [map_raw, h]
  have hA : (fun i => (evalParam ε w).mapMatrix (paramChart i)) = cores (chart ε w) :=
    funext (evalParam_chart ε w)
  have hB : (fun i => (evalParam ε w).mapMatrix ((paramChart i).map (Polynomial.map conjCoeff))) =
      fun i => (cores (chart ε w) i).map (starRingEnd ℂ) := by
    funext i
    rw [← evalParam_chart ε w i]
    ext a b
    exact evalParam_conj ε w (paramChart i a b)
  rw [hA, hB]

/-- The actual complex transfer polynomial in ε at fixed chart parameters. -/
def rawPolynomial (r : Fin 8) (n : ℕ) (w : Parameters) : Polynomial ℂ :=
  (rawFamily r n).map (atParameter w)

theorem rawPolynomial_eval (r : Fin 8) (n : ℕ) (w : Parameters) (ε : ℝ) :
    (rawPolynomial r (n + 4) w).eval (ε : ℂ) =
      rawTwo (cores (chart ε w)) n (entry r).1 (entry r).2 := by
  rw [rawPolynomial, eval_map]
  exact evalParam_rawFamily r n ε w

private def part (imag : Bool) : ℂ →L[ℝ] ℝ := if imag then Complex.imCLM else Complex.reCLM

def project (imag : Bool) (p : Polynomial Coefficients) : Family :=
  p.sum fun k a => monomial k (fun w => part imag (a.val w))

@[simp] private theorem coeff_project (imag : Bool) (p : Polynomial Coefficients) (k : ℕ) :
    (project imag p).coeff k = fun w => part imag ((p.coeff k).val w) := by
  classical
  rw [project, coeff_sum]
  simp only [Polynomial.sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split
  · rfl
  · rename_i hk
    have h₀ := notMem_support_iff.mp hk
    rw [h₀]
    exact (funext fun _ => ((part imag).map_zero).symm)

private theorem evaluate_project (imag : Bool) (p : Polynomial Coefficients) (ε : ℝ)
    (w : Parameters) : evaluate (project imag p) ε w = part imag (evalParam ε w p) := by
  unfold project evaluate evalParam
  rw [Polynomial.sum, eval₂_finsetSum]
  change (∑ k ∈ p.support, eval₂ (Pi.evalRingHom _ w) ε
    (monomial k (fun v => part imag ((p.coeff k).val v)))) =
      part imag (p.eval₂ (atParameter w) (ε : ℂ))
  rw [eval₂_eq_sum, Polynomial.sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval₂_monomial]
  change part imag ((p.coeff k).val w) * ε ^ k =
    part imag ((p.coeff k).val w * (ε : ℂ) ^ k)
  rw [mul_comm ((p.coeff k).val w), ← Complex.ofReal_pow, ← Complex.real_smul, map_smul,
    smul_eq_mul, mul_comm]

/-- The real and imaginary jet coefficients are the corresponding components
of the specialized raw transfer polynomial. -/
theorem coeff_project_specialized (imag : Bool) (r : Fin 8) (n k : ℕ) (w : Parameters) :
    (project imag (rawFamily r n)).coeff k w =
      if imag then ((rawPolynomial r n w).coeff k).im
      else ((rawPolynomial r n w).coeff k).re := by
  rw [coeff_project, rawPolynomial, coeff_map]
  cases imag <;> rfl

def massFamily (n : ℕ) : Family :=
  project false (rawFamily 0 n + rawFamily 1 n + rawFamily 7 n + rawFamily 6 n)

def rowData : Rows → Bool × Fin 8
  | .inl i => (true, ![3, 4, 5] i)
  | .inr (.inl i) => (false, ![1, 2, 4, 5] i)
  | .inr (.inr _) => (false, 3)

def valueFamily (i : Rows) (n : ℕ) : Family :=
  project (rowData i).1 (rawFamily (rowData i).2 n)

private def fix (w : Parameters) (p : Family) : Family :=
  p.map ((Pi.constRingHom Parameters ℝ).comp (Pi.evalRingHom _ w))

@[simp] private theorem evaluate_fix (p : Family) (u w : Parameters) (ε : ℝ) :
    evaluate (fix u p) ε w = evaluate p ε u := by
  simp [evaluate, fix, eval₂_map]
  rfl

/-- Cross multiplication uses both actual trace normalizations for each row. -/
def difference (n : ℕ) (s : ℝ) (i : Rows) : Family :=
  valueFamily i (n + 4) * fix (original s) (massFamily (n + 4)) -
    fix (original s) (valueFamily i (n + 4)) * massFamily (n + 4)

private theorem mass_eval (n : ℕ) (ε : ℝ) (w : Parameters) :
    evaluate (massFamily (n + 4)) ε w = twoMass (cores (chart ε w)) n := by
  simp only [massFamily, evaluate_project, map_add, evalParam_rawFamily, part, Bool.false_eq_true,
    ↓reduceIte, Complex.reCLM_apply, twoMass, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, Fin.sum_univ_two, entry, Matrix.cons_val_zero]
  simp
  ring

private theorem raw_conj (x : Coord) (n : ℕ) (p q : TwoBits) :
    rawTwo (cores (fun i => star (x i))) n p q = star (rawTwo (cores x) n p q) := by
  rw [rawTwo_eq_trace, rawTwo_eq_trace]
  change _ = starRingEnd ℂ _
  rw [map_raw]
  have h (i : Fin 2) : (starRingEnd ℂ).mapMatrix (cores x i) =
      cores (fun i => star (x i)) i := by
    exact map_chart _ _ _ _ _ _
  have hh (i : Fin 2) :
      (starRingEnd ℂ).mapMatrix ((cores x i).map (starRingEnd ℂ)) = cores x i := by
    ext a b
    simp
  have hc : (fun i => (cores (fun j => star (x j)) i).map (starRingEnd ℂ)) = cores x := by
    funext i
    rw [← h]
    ext a b
    simp
  simp only [h, hh, hc]

private theorem value_eval (i : Rows) (n : ℕ) (ε : ℝ) (w : Parameters) :
    evaluate (valueFamily i (n + 4)) ε w =
      part (rowData i).1 (rawTwo (cores (chart ε w)) n (entry (rowData i).2).1
        (entry (rowData i).2).2) := by
  rw [valueFamily, evaluate_project, evalParam_rawFamily]

private theorem value_neg (i : Rows) (n : ℕ) (ε : ℝ) (w : Parameters) :
    evaluate (valueFamily i (n + 4)) (-ε) w =
      if (rowData i).1 then -evaluate (valueFamily i (n + 4)) ε w
      else evaluate (valueFamily i (n + 4)) ε w := by
  have h : chart (-ε) w = fun j => star (chart ε w j) := funext (chart_neg ε w)
  simp only [value_eval, h, raw_conj]
  cases (rowData i).1 <;> simp [part]

private theorem mass_neg (n : ℕ) (ε : ℝ) (w : Parameters) :
    evaluate (massFamily (n + 4)) (-ε) w = evaluate (massFamily (n + 4)) ε w := by
  have h : chart (-ε) w = fun j => star (chart ε w j) := funext (chart_neg ε w)
  simp only [mass_eval, h, twoMass, Matrix.trace, Matrix.diag, Complex.re_sum, raw_conj]
  simp

private theorem difference_eval (n : ℕ) (s : ℝ) (i : Rows) (ε : ℝ) (w : Parameters) :
    evaluate (difference n s i) ε w =
      evaluate (valueFamily i (n + 4)) ε w * evaluate (massFamily (n + 4)) ε (original s) -
      evaluate (valueFamily i (n + 4)) ε (original s) * evaluate (massFamily (n + 4)) ε w := by
  unfold difference
  have sub_eval (p q : Family) : evaluate (p - q) ε w = evaluate p ε w - evaluate q ε w :=
    eval₂_sub _
  have mul_eval (p q : Family) : evaluate (p * q) ε w = evaluate p ε w * evaluate q ε w :=
    eval₂_mul _ _
  simp only [sub_eval, mul_eval, evaluate_fix]

private theorem difference_zero (n : ℕ) (s : ℝ) (i : Rows) (w : Parameters) :
    evaluate (difference n s i) 0 w = 0 := by
  simp only [difference_eval, value_eval, mass_eval, chart_zero, sub_self]

private theorem difference_odd (n : ℕ) (s : ℝ) (i : Fin 3) (w : Parameters) (ε : ℝ) :
    evaluate (difference n s (.inl i)) (-ε) w = -evaluate (difference n s (.inl i)) ε w := by
  simp [difference_eval, value_neg, mass_neg, rowData]
  ring

private theorem difference_even (n : ℕ) (s : ℝ) (i : Fin 4 ⊕ Unit) (w : Parameters) (ε : ℝ) :
    evaluate (difference n s (.inr i)) (-ε) w = evaluate (difference n s (.inr i)) ε w := by
  cases i <;> simp [difference_eval, value_neg, mass_neg, rowData]

private theorem analyticAt_coeff_mul (p q : Family) (k : ℕ) (w : Parameters)
    (hp : ∀ j, AnalyticAt ℝ (p.coeff j) w) (hq : ∀ j, AnalyticAt ℝ (q.coeff j) w) :
    AnalyticAt ℝ ((p * q).coeff k) w := by
  rw [coeff_mul]
  apply Finset.analyticAt_sum
  intro j _
  exact (hp j.1).mul (hq j.2)

private theorem analyticAt_coeff_project (imag : Bool) (p : Polynomial Coefficients)
    (j : ℕ) (w : Parameters) : AnalyticAt ℝ ((project imag p).coeff j) w := by
  rw [coeff_project]
  exact ((part imag).analyticAt _).comp ((p.coeff j).property w)

private theorem analyticAt_difference (n : ℕ) (s : ℝ) (i : Rows) (k : ℕ) (w : Parameters) :
    AnalyticAt ℝ ((difference n s i).coeff k) w := by
  rw [difference, coeff_sub]
  apply AnalyticAt.sub <;> apply analyticAt_coeff_mul <;> intro j
  all_goals
    first
    | simp only [fix, coeff_map, RingHom.comp_apply, Pi.evalRingHom_apply]
      exact analyticAt_const
    | exact analyticAt_coeff_project _ _ j w

private theorem component_eq_div (i : Rows) (n : ℕ) (ε : ℝ) (w : Parameters) :
    component (rowData i).1 n (rowData i).2 (chart ε w) =
      evaluate (valueFamily i (n + 4)) ε w / evaluate (massFamily (n + 4)) ε w := by
  rw [mass_eval, value_eval]
  unfold component normalizedTwo
  rw [Matrix.smul_apply, div_eq_inv_mul]
  cases (rowData i).1 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, part, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]

set_option maxHeartbeats 800000 in
/-- For a certified simple reduced root, the two physical paths have exactly
the same seven regular readouts and the same real coherence near ε = 0. -/
theorem exists_second_curve (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (w₀ : Parameters)
    (cert : LeadingCertificate (fun w => scaled (difference n s) (0, w)) w₀) :
    ∃ w : ℝ → Parameters, w 0 = w₀ ∧ AnalyticAt ℝ w 0 ∧
      ((fun ε => w (-ε)) =ᶠ[𝓝 0] w) ∧
      AnalyticAt ℝ (fun ε => chart ε (w ε)) 0 ∧
      AnalyticAt ℝ (fun ε => chart ε (original s)) 0 ∧
      HasDerivAt (fun ε => (chart ε (w ε) 0).im) w₀.2.2 0 ∧
      HasDerivAt (fun ε => (chart ε (original s) 0).im) 1 0 ∧
      (∀ᶠ ε in 𝓝 0, regularReadout n (chart ε (w ε)) = regularReadout n (chart ε (original s)) ∧
        component false n 3 (chart ε (w ε)) = component false n 3 (chart ε (original s))) := by
  obtain ⟨w, hw₀, hw, he, hEq⟩ := exists_polynomial_partner (difference n s) w₀
    (fun i k => analyticAt_difference n s i k _) (difference_zero n s)
    (difference_odd n s) (difference_even n s) cert
  have hz : AnalyticAt ℝ (fun ε => chart ε (w ε)) 0 :=
    (analyticAt_chart (0, w 0)).comp (f := fun ε : ℝ => (ε, w ε)) (analyticAt_id.prod hw)
  have hx : AnalyticAt ℝ (fun ε => chart ε (original s)) 0 :=
    (analyticAt_chart (0, original s)).comp (f := fun ε : ℝ => (ε, original s))
      (analyticAt_id.prod analyticAt_const)
  have h₂ := ((ContinuousLinearMap.snd ℝ Imaginary (RealRegular × ℝ)).analyticAt _).comp hw
  have ht := ((ContinuousLinearMap.snd ℝ RealRegular ℝ).analyticAt _).comp h₂
  have hd : HasDerivAt (fun ε => (chart ε (w ε) 0).im) w₀.2.2 0 := by
    simp only [chart_im, imagDirection, Matrix.cons_val_zero]
    have hdiff : DifferentiableAt ℝ (fun ε : ℝ => (w ε).2.2) 0 := ht.differentiableAt
    have H := hdiff.hasDerivAt.fun_mul (hasDerivAt_id (0 : ℝ))
    simpa only [id_eq, mul_zero, mul_one, zero_add, hw₀] using H
  have hd' : HasDerivAt (fun ε => (chart ε (original s) 0).im) 1 0 := by
    simp only [chart_im, imagDirection, Matrix.cons_val_zero, original, one_mul]
    exact hasDerivAt_id 0
  refine ⟨w, hw₀, hw, he, hz, hx, hd, hd', ?_⟩
  have hm (v : ℝ → Parameters) (hv : AnalyticAt ℝ v 0) :
      ∀ᶠ ε in 𝓝 0, evaluate (massFamily (n + 4)) ε (v ε) ≠ 0 := by
    have hh : AnalyticAt ℝ (fun a : ℝ × Parameters => evaluate (massFamily (n + 4)) a.1 a.2)
        (0, v 0) := analyticAt_evaluate _ _ (fun j => analyticAt_coeff_project _ _ j _)
    have hm₀ : evaluate (massFamily (n + 4)) 0 (v 0) ≠ 0 := by
      simpa only [mass_eval, chart_zero] using (mass_pos_witness n hn).ne'
    exact (hh.comp (f := fun ε : ℝ => (ε, v ε)) (analyticAt_id.prod hv)).continuousAt.eventually_ne hm₀
  filter_upwards [hEq, hm w hw, hm (fun _ => original s) analyticAt_const] with ε hε hmz hmx
  have H (i : Rows) :
      component (rowData i).1 n (rowData i).2 (chart ε (w ε)) =
        component (rowData i).1 n (rowData i).2 (chart ε (original s)) := by
    rw [component_eq_div, component_eq_div, div_eq_div_iff hmz hmx]
    have hi := hε i
    rw [difference_eval] at hi
    exact sub_eq_zero.mp hi
  have hr : (regularReadout n (chart ε (w ε))).1 = (regularReadout n (chart ε (original s))).1 := by
    funext i
    fin_cases i
    · exact H (.inr (.inl 0))
    · exact H (.inr (.inl 1))
    · exact H (.inr (.inl 2))
    · exact H (.inr (.inl 3))
  have hi : (regularReadout n (chart ε (w ε))).2 = (regularReadout n (chart ε (original s))).2 := by
    funext i
    fin_cases i
    · exact H (.inl 0)
    · exact H (.inl 1)
    · exact H (.inl 2)
  exact ⟨Prod.ext hr hi, H (.inr (.inr ()))⟩

/-- Distinct imaginary slopes separate the two chart paths at every
sufficiently small nonzero parameter. -/
theorem eventually_second_curve_ne {w : ℝ → Parameters} {t s : ℝ}
    (hz : HasDerivAt (fun ε => (chart ε (w ε) 0).im) t 0)
    (hx : HasDerivAt (fun ε => (chart ε (original s) 0).im) 1 0)
    (ht : t ≠ 1) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), chart ε (w ε) ≠ chart ε (original s) := by
  have h := (hz.sub hx).eventually_ne (c := (0 : ℝ)) (sub_ne_zero.mpr ht)
  filter_upwards [h] with ε hε hEq
  apply hε
  change (chart ε (w ε) 0).im - (chart ε (original s) 0).im = 0
  rw [hEq, sub_self]

/-- Lift the constant and quadratic coefficients of the even parameter germ.
The imaginary slopes are `(t, β, γ, δ)` at `w 0`. Their values at `w₂`
are the cubic coefficients `(a₃, b₃, c₃, d₃)`. The four real components
of `w 0` and `w₂` give the real quadratic and quartic coefficients. -/
theorem chart_taylor_four {w : ℝ → Parameters} (hw : AnalyticAt ℝ w 0)
    (he : (fun ε => w (-ε)) =ᶠ[𝓝 0] w) :
    ∃ w₂ : Parameters, ∀ i : Fin 4,
      (fun ε : ℝ => (chart ε (w ε) i).im -
        (imagDirection (w 0) i * ε + imagDirection w₂ i * ε ^ 3)) =O[𝓝 0] (fun ε => ε ^ 5) ∧
      (fun ε : ℝ => (chart ε (w ε) i).re -
        ((witness i).re + (w 0).2.1 i * ε ^ 2 + w₂.2.1 i * ε ^ 4)) =O[𝓝 0] (fun ε => ε ^ 6) := by
  obtain ⟨w₂, h⟩ := even_taylor_two hw he
  let E : ℝ → Parameters := fun ε => w ε - (w 0 + ε ^ 2 • w₂)
  have hE : E =O[𝓝 0] (fun ε : ℝ => ε ^ 4) :=
    Asymptotics.IsBigO.of_norm_right (by simpa only [norm_pow] using h)
  refine ⟨w₂, fun i => ⟨?_, ?_⟩⟩
  · let L := imagDirectionCLM i
    have hL := ((L.isBigO_comp E (𝓝 0)).trans hE).mul (isBigO_refl (fun ε : ℝ => ε) (𝓝 0))
    refine hL.congr (fun ε => ?_) (fun ε => ?_)
    · change L (w ε - (w 0 + ε ^ 2 • w₂)) * ε = _
      simp only [map_sub, map_add, map_smul, smul_eq_mul, L, imagDirectionCLM_apply, chart_im]
      ring
    · exact (pow_succ ε 4).symm
  · let L := realDirectionCLM i
    have hL := ((L.isBigO_comp E (𝓝 0)).trans hE).mul
      (isBigO_refl (fun ε : ℝ => ε ^ 2) (𝓝 0))
    refine hL.congr (fun ε => ?_) (fun ε => ?_)
    · change L (w ε - (w 0 + ε ^ 2 • w₂)) * ε ^ 2 = _
      simp only [map_sub, map_add, map_smul, smul_eq_mul, L, realDirectionCLM_apply, chart_re]
      ring
    · exact (pow_add ε 4 2).symm

/-! For the all-length application, the normalized elimination supplies
`LeadingCertificate` at `t = -B/A` with leading `γ = 1`, `δ = 0`, and
`β = -s*t`. The first-jet regular blocks acquire the common nonzero factor
given by the squared witness mass. The Taylor lift retains the cubic
`a₃` term even when a raw coefficient supplier specializes it to zero.
To apply that supplier, use the zero first derivative in the `a` direction
for the two forbidden imaginary coherences. The cubic coefficients in
those equations determine `c₃,d₃`. For the forbidden diagonal the cubic
`a₃,b₃` variations disappear at degree four by the vanishing base and
corresponding linear terms of the squared core; the mass is needed only
through degree two. The normalized quartic calculation then supplies
the nonzero coefficient of the difference used by the analytic fold. -/

#print axioms exists_second_curve
#print axioms chart_taylor_four
#print axioms eventually_second_curve_ne

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticPartner
