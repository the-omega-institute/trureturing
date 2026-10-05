/- GID: D5/S3/Quantum/Information/DinovOriginalMinimumRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DinovOriginalMinimumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause; result=D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result; claim=D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause
   digest: Two nonuniform phases lower both covariance uncertainties at a fixed joint action marginal. -/
/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#13139; Refuted)
Direct frozen dependencies: none; the proof uses pinned Mathlib.
-/
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic.Measurability
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section
open Real MeasureTheory Set
open scoped ENNReal
namespace D5.S3.Quantum.Information.DinovOriginalMinimumRefutation
local instance : MeasureSpace Real.Angle := @AddCircle.measureSpace (2 * π) ⟨by positivity⟩
abbrev action : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
def R2 (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2
def actualCoordinate (i : Bool × Bool) (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := if i.2 then (if i.1 then x.2 else x.1).2 else (if i.1 then x.2 else x.1).1
/-- Actual integral covariance, not a prescribed diagonal surrogate. -/
def actualCovariance (μ : Measure ((ℝ × ℝ) × (ℝ × ℝ))) : Matrix (Bool × Bool) (Bool × Bool) ℝ := fun i k => ProbabilityTheory.covariance (actualCoordinate i) (actualCoordinate k) μ
/-- Source within-DOF uncertainty: square root of the actual covariance block determinant. -/
def actualUncertainty (μ : Measure ((ℝ × ℝ) × (ℝ × ℝ))) (j : Bool) : ℝ := sqrt (Matrix.det !![ actualCovariance μ (j,false) (j,false), actualCovariance μ (j,false) (j,true);
    actualCovariance μ (j,true) (j,false), actualCovariance μ (j,true) (j,true)])
abbrev TorusOne := Real.Angle × ℝ
abbrev TorusTwo := TorusOne × TorusOne
abbrev CartesianTwo := (ℝ × ℝ) × (ℝ × ℝ)
abbrev torusBase : Measure TorusOne := (volume : Measure Real.Angle).prod action
abbrev torusFullBase : Measure TorusTwo := torusBase.prod torusBase
def PsiA (z : TorusOne) : ℝ × ℝ := (sqrt (2 * z.2) * z.1.sin, sqrt (2 * z.2) * z.1.cos)
def PsiA2 : TorusTwo → CartesianTwo := Prod.map PsiA PsiA
def actionProjection (z : TorusTwo) : ℝ × ℝ := (z.1.2, z.2.2)
def radialAction (x : CartesianTwo) : ℝ × ℝ := (R2 x.1 / 2, R2 x.2 / 2)
def cartesianLaw (F : CartesianTwo → ℝ) : Measure CartesianTwo := volume.withDensity (fun x => ENNReal.ofReal (F x))
/-- Pullback through the actual quotient-angle action map. -/
def sourcePullback (F : CartesianTwo → ℝ) (z : TorusTwo) : ℝ := F (PsiA2 z)
def sourceTorusLaw (F : CartesianTwo → ℝ) : Measure TorusTwo := torusFullBase.withDensity (fun z => ENNReal.ofReal (sourcePullback F z))
def sourceEntropy (F : CartesianTwo → ℝ) : ℝ := -(∫ x, F x * log (F x))
def sourceUncertainty (F : CartesianTwo → ℝ) (j : Bool) : ℝ := actualUncertainty (cartesianLaw F) j
def actionDensity (r : (ℝ × ℝ) → ℝ) : Prop := Measurable r ∧ (∀ J, 0 ≤ r J) ∧ (∫⁻ J, ENNReal.ofReal (r J) ∂action.prod action) = 1
def oneActionDensity (r : ℝ → ℝ) : Prop := Measurable r ∧ (∀ J, 0 ≤ r J) ∧ (∫⁻ J, ENNReal.ofReal (r J) ∂action) = 1
def actionLaw (r : (ℝ × ℝ) → ℝ) : Measure (ℝ × ℝ) := (action.prod action).withDensity (fun J => ENNReal.ofReal (r J))
/-- Finite entropy and finite full positive-definite covariance, with actual realization. -/
def sourceState (F : CartesianTwo → ℝ) : Prop := Measurable F ∧ (∀ x, 0 ≤ F x) ∧ IsProbabilityMeasure (cartesianLaw F) ∧ Integrable (fun x => F x * log (F x)) volume ∧
    (∀ i, MemLp (actualCoordinate i) 2 (cartesianLaw F)) ∧
    (actualCovariance (cartesianLaw F)).PosDef ∧
    Integrable (fun z => sourcePullback F z * log (sourcePullback F z)) torusFullBase ∧
    (∫ z, sourcePullback F z * log (sourcePullback F z) ∂torusFullBase) = (∫ x, F x * log (F x)) ∧
    Measure.map PsiA2 (sourceTorusLaw F) = cartesianLaw F
/-- The same action density, at the fiber and both actual law levels. -/
def commonActionMarginal (F G : CartesianTwo → ℝ) (r : (ℝ × ℝ) → ℝ) : Prop := (∀ᵐ J ∂action.prod action,
    Integrable (fun ts : Real.Angle × Real.Angle => sourcePullback F ((ts.1,J.1),(ts.2,J.2))) volume ∧
    (∫ ts : Real.Angle × Real.Angle, sourcePullback F ((ts.1,J.1),(ts.2,J.2))) = r J) ∧
  (∀ᵐ J ∂action.prod action, Integrable (fun ts : Real.Angle × Real.Angle => sourcePullback G ((ts.1,J.1),(ts.2,J.2))) volume ∧
    (∫ ts : Real.Angle × Real.Angle, sourcePullback G ((ts.1,J.1),(ts.2,J.2))) = r J) ∧
  Measure.map actionProjection (sourceTorusLaw F) = actionLaw r ∧
  Measure.map actionProjection (sourceTorusLaw G) = actionLaw r ∧
  Measure.map radialAction (cartesianLaw F) = actionLaw r ∧
  Measure.map radialAction (cartesianLaw G) = actionLaw r
/-- Uniform phases with an actually factored normalized action density. -/
def phaseUniformProduct (G : CartesianTwo → ℝ) (r : (ℝ × ℝ) → ℝ) : Prop := (sourcePullback G =ᵐ[torusFullBase] fun z => r (actionProjection z) / (2 * π)^2) ∧
  ∃ r₀ r₁ : ℝ → ℝ, oneActionDensity r₀ ∧ oneActionDensity r₁ ∧ (r =ᵐ[action.prod action] fun J => r₀ J.1 * r₁ J.2)
/-- The two-DOF necessary minimum specialization of Conjecture 3.22(ii).
The full all-n assertion entails this assertion at n=2; this definition has no n quantifier. -/
def dinovTwoDofMinimumClause : Prop := ∀ (s : ℝ) (r : (ℝ × ℝ) → ℝ) (F G : CartesianTwo → ℝ), actionDensity r → sourceState F → sourceState G → commonActionMarginal F G r → phaseUniformProduct G r →
    s ≤ sourceEntropy F → s ≤ sourceEntropy G →
    ∀ j : Bool, sourceUncertainty G j ≤ sourceUncertainty F j
set_option maxHeartbeats 8000000 in
/-- The joint analytic, transport and covariance certificates are proved in one result. -/
theorem result : ¬ dinovTwoDofMinimumClause := by
  letI : Fact (0 < (2 * π : ℝ)) := ⟨by positivity⟩
  letI : BorelSpace Real.Angle := inferInstanceAs (BorelSpace (AddCircle (2 * π)))
  letI : CompactSpace Real.Angle := inferInstanceAs (CompactSpace (AddCircle (2 * π)))
  letI : SecondCountableTopology Real.Angle := inferInstanceAs (SecondCountableTopology (AddCircle (2 * π)))
  letI : IsFiniteMeasure (volume : Measure Real.Angle) := ⟨by
      have h : (volume : Measure Real.Angle) univ = ENNReal.ofReal (2 * π) := AddCircle.measure_univ (2 * π); rw [h]; exact ENNReal.ofReal_lt_top⟩
  let q (z : ℝ × ℝ) : ℝ := sqrt (2*z.2) * sin z.1; let p (z : ℝ × ℝ) : ℝ := sqrt (2*z.2) * cos z.1; let cartesian (z : ℝ × ℝ) : ℝ × ℝ := (q z, p z)
  let angle : Measure ℝ := volume.restrict (Ioc (-π) π); let base : Measure (ℝ × ℝ) := angle.prod action; let phi (t : ℝ) : ℝ := (1 + cos (2*t)/2)/(2*π); let uniformPhase (_t : ℝ) : ℝ := 1/(2*π)
  let oneDensity (z : ℝ × ℝ) : ℝ := phi z.1 * exp (-z.2); let comparatorOneDensity (z : ℝ × ℝ) : ℝ := uniformPhase z.1 * exp (-z.2); let fullBase : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := base.prod base
  let fullDensity (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := oneDensity z.1 * oneDensity z.2; let comparatorDensity (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := comparatorOneDensity z.1 * comparatorOneDensity z.2
  have phi_cont : Continuous phi := by unfold phi; fun_prop
  have phi_nonneg (t : ℝ) : 0 ≤ phi t := by
    unfold phi; apply div_nonneg
    · have := neg_one_le_cos (2*t); linarith
    · positivity
  have phi_pos (t : ℝ) : 0 < phi t := by
    unfold phi; apply div_pos
    · have := neg_one_le_cos (2*t); linarith
    · positivity
  have phi_integrable : Integrable phi angle := (phi_cont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have exp_integrable : Integrable (fun J : ℝ => exp (-J)) action := by simpa [action, IntegrableOn] using (GammaIntegral_convergent (s := 1) (by norm_num))
  have phi_mass : ∫ t, phi t ∂angle = 1 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    have hc : IntervalIntegrable (fun t : ℝ => cos t ^ 2) volume (-π) π := (by fun_prop : Continuous (fun t : ℝ => cos t ^ 2)).intervalIntegrable _ _
    have he : phi = fun t : ℝ => ((1/2 : ℝ) + cos t ^ 2)/(2*π) := by funext t; unfold phi; rw [cos_two_mul]; ring
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hc, intervalIntegral.integral_const, integral_cos_sq]
    simp only [sin_pi, sin_neg, neg_zero, cos_pi, cos_neg, mul_zero, sub_zero]; field_simp; ring
  have uniform_mass : ∫ t, uniformPhase t ∂angle = 1 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]; simp only [uniformPhase, intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
  have exp_mass : ∫ J, exp (-J) ∂action = 1 := by exact integral_exp_neg_Ioi_zero
  have one_mass : ∫ z, oneDensity z ∂base = 1 := by simp only [oneDensity]; rw [integral_prod_mul (f := phi) (g := fun J : ℝ => exp (-J)), phi_mass, exp_mass, mul_one]
  have comparator_one_mass : ∫ z, comparatorOneDensity z ∂base = 1 := by
    simp only [comparatorOneDensity]; rw [integral_prod_mul (f := uniformPhase) (g := fun J : ℝ => exp (-J)), uniform_mass, exp_mass, mul_one]
  have full_mass : ∫ z, fullDensity z ∂fullBase = 1 := by simp only [fullDensity]; rw [integral_prod_mul (f := oneDensity) (g := oneDensity), one_mass, mul_one]
  have comparator_mass : ∫ z, comparatorDensity z ∂fullBase = 1 := by
    simp only [comparatorDensity]; rw [integral_prod_mul (f := comparatorOneDensity) (g := comparatorOneDensity), comparator_one_mass, mul_one]
  have exact_action_marginal (J₁ J₂ : ℝ) : (∫ ts : ℝ × ℝ, fullDensity ((ts.1,J₁),(ts.2,J₂)) ∂angle.prod angle) = exp (-(J₁+J₂)) := by
    simp only [fullDensity,oneDensity]
    rw [integral_prod_mul (f := fun t : ℝ => phi t * exp (-J₁)) (g := fun t : ℝ => phi t * exp (-J₂)), integral_mul_const, integral_mul_const, phi_mass, one_mul, one_mul, ← exp_add]; congr 1; ring
  have comparator_action_marginal (J₁ J₂ : ℝ) : (∫ ts : ℝ × ℝ, comparatorDensity ((ts.1,J₁),(ts.2,J₂)) ∂angle.prod angle) = exp (-(J₁+J₂)) := by
    simp only [comparatorDensity,comparatorOneDensity]
    rw [integral_prod_mul (f := fun t : ℝ => uniformPhase t * exp (-J₁)) (g := fun t : ℝ => uniformPhase t * exp (-J₂)), integral_mul_const, integral_mul_const, uniform_mass,
      one_mul, one_mul, ← exp_add]
    congr 1; ring
  have continuous_angle_integrable {h : ℝ → ℝ} (hh : Continuous h) : Integrable h angle := hh.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have one_integrable : Integrable oneDensity base := by exact phi_integrable.mul_prod exp_integrable
  have comparator_one_integrable : Integrable comparatorOneDensity base := by exact (continuous_angle_integrable (by unfold uniformPhase; fun_prop)).mul_prod exp_integrable
  have full_integrable : Integrable fullDensity fullBase := one_integrable.mul_prod one_integrable
  have comparator_integrable : Integrable comparatorDensity fullBase := comparator_one_integrable.mul_prod comparator_one_integrable
  have full_nonneg (z : (ℝ × ℝ) × (ℝ × ℝ)) : 0 ≤ fullDensity z := by
    unfold fullDensity oneDensity; exact mul_nonneg (mul_nonneg (phi_nonneg _) (exp_pos _).le) (mul_nonneg (phi_nonneg _) (exp_pos _).le)
  have full_lintegral : ∫⁻ z, ENNReal.ofReal (fullDensity z) ∂fullBase = 1 := by rw [← ofReal_integral_eq_lintegral_ofReal full_integrable (ae_of_all _ full_nonneg), full_mass]; norm_num
  have comparator_nonneg (z : (ℝ × ℝ) × (ℝ × ℝ)) : 0 ≤ comparatorDensity z := by unfold comparatorDensity comparatorOneDensity uniformPhase; positivity
  have comparator_lintegral : ∫⁻ z, ENNReal.ofReal (comparatorDensity z) ∂fullBase = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal comparator_integrable (ae_of_all _ comparator_nonneg), comparator_mass]; norm_num
  let witnessLaw : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := fullBase.withDensity (fun z => ENNReal.ofReal (fullDensity z))
  let comparatorLaw : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := fullBase.withDensity (fun z => ENNReal.ofReal (comparatorDensity z))
  have witness_probability : IsProbabilityMeasure witnessLaw := by constructor; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, full_lintegral]
  have comparator_probability : IsProbabilityMeasure comparatorLaw := by constructor; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, comparator_lintegral]
  have cos_sq_phase : ∫ t, cos t ^ 2 * phi t ∂angle = 5/8 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    have he : (fun t : ℝ => cos t ^ 2 * phi t) = fun t : ℝ => (cos t ^ 2 / 2 + cos t ^ 4)/(2*π) := by funext t; unfold phi; rw [cos_two_mul]; ring
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add ((by fun_prop : Continuous (fun t : ℝ => cos t ^ 2 / 2)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => cos t ^ 4)).intervalIntegrable _ _),
      intervalIntegral.integral_div]
    have h4 : (∫ t in (-π)..π, cos t ^ 4) = (3/4 : ℝ)*π := by have hi := integral_cos_pow (a := -π) (b := π) (n := 2); norm_num [integral_cos_sq] at hi ⊢; linarith
    rw [h4, integral_cos_sq]; simp only [sin_pi, sin_neg, neg_zero, cos_pi, cos_neg, mul_zero, sub_zero]; field_simp; ring
  have sin_sq_phase : ∫ t, sin t ^ 2 * phi t ∂angle = 3/8 := by
    have he : (fun t : ℝ => sin t ^ 2 * phi t) = fun t : ℝ => phi t - cos t ^ 2 * phi t := by
      funext t
      have ht : sin t ^ 2 = 1 - cos t ^ 2 := by nlinarith [sin_sq_add_cos_sq t]
      rw [ht]; ring
    rw [he, integral_sub (f := phi) (g := fun t : ℝ => cos t ^ 2 * phi t) phi_integrable (continuous_angle_integrable (by unfold phi; fun_prop)), phi_mass, cos_sq_phase]; norm_num
  have cos_phase_mean : ∫ t, cos t * phi t ∂angle = 0 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    have he : (fun t : ℝ => cos t * phi t) = fun t : ℝ => (cos t / 2 + cos t ^ 3)/(2*π) := by funext t; unfold phi; rw [cos_two_mul]; ring
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add ((by fun_prop : Continuous (fun t : ℝ => cos t / 2)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => cos t ^ 3)).intervalIntegrable _ _),
      intervalIntegral.integral_div, integral_cos, integral_cos_pow_three]
    simp
  have sin_phase_mean : ∫ t, sin t * phi t ∂angle = 0 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    have he : (fun t : ℝ => sin t * phi t) = fun t : ℝ => (sin t / 2 + sin t * cos t ^ 2)/(2*π) := by funext t; unfold phi; rw [cos_two_mul]; ring
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add ((by fun_prop : Continuous (fun t : ℝ => sin t / 2)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => sin t * cos t ^ 2)).intervalIntegrable _ _),
      intervalIntegral.integral_div, integral_sin, integral_sin_mul_cos_sq]
    simp
  have sin_cos_phase : ∫ t, sin t * cos t * phi t ∂angle = 0 := by
    rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    have he : (fun t : ℝ => sin t * cos t * phi t) = fun t : ℝ => (sin t * cos t / 2 + sin t * cos t ^ 3)/(2*π) := by funext t; unfold phi; rw [cos_two_mul]; ring
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add ((by fun_prop : Continuous (fun t : ℝ => sin t * cos t / 2)).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => sin t * cos t ^ 3)).intervalIntegrable _ _),
      intervalIntegral.integral_div, integral_sin_mul_cos₁]
    have hc : (∫ t in (-π)..π, sin t * cos t ^ 3) = 0 := by simpa using (integral_sin_pow_mul_cos_pow_odd (a := -π) (b := π) 1 1)
    rw [hc]; simp
  have action_first_moment : ∫ J, J * exp (-J) ∂action = 1 := by
    have hi := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) (by norm_num) (by norm_num)
    norm_num at hi; exact hi
  have action_first_integrable : Integrable (fun J : ℝ => J * exp (-J)) action := by
    have hi := GammaIntegral_convergent (s := 2) (by norm_num)
    norm_num at hi; simpa [IntegrableOn, action, mul_comm] using hi
  have phi_le_one (t : ℝ) : phi t ≤ 1 := by unfold phi; rw [div_le_iff₀ (by positivity : 0 < 2*π)]; have := cos_le_one (2*t); linarith [pi_gt_three]
  have uniform_pos (t : ℝ) : 0 < uniformPhase t := by unfold uniformPhase; positivity
  have uniform_le_one (t : ℝ) : uniformPhase t ≤ 1 := by unfold uniformPhase; rw [div_le_iff₀ (by positivity : 0 < 2*π)]; linarith [pi_gt_three]
  have one_pos (z : ℝ × ℝ) : 0 < oneDensity z := mul_pos (phi_pos _) (exp_pos _)
  have comparator_one_pos (z : ℝ × ℝ) : 0 < comparatorOneDensity z := by exact mul_pos (uniform_pos z.1) (exp_pos (-z.2))
  have full_pos (z : (ℝ × ℝ) × (ℝ × ℝ)) : 0 < fullDensity z := mul_pos (one_pos _) (one_pos _)
  have comparator_pos (z : (ℝ × ℝ) × (ℝ × ℝ)) : 0 < comparatorDensity z := mul_pos (comparator_one_pos _) (comparator_one_pos _)
  have positive_action_ae : ∀ᵐ z : ℝ × ℝ ∂base, 0 < z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {z : ℝ × ℝ | 0 < z.2})).2; exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Ioi)
  have full_positive_actions_ae : ∀ᵐ z : (ℝ × ℝ) × (ℝ × ℝ) ∂fullBase, 0 < z.1.2 ∧ 0 < z.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {z : (ℝ × ℝ) × (ℝ × ℝ) | 0 < z.1.2 ∧ 0 < z.2.2})).2
    exact positive_action_ae.mono fun _ h₁ => positive_action_ae.mono fun _ h₂ => ⟨h₁,h₂⟩
  have one_le_one (z : ℝ × ℝ) (hz : 0 ≤ z.2) : oneDensity z ≤ 1 := by
    apply mul_le_one₀ (phi_le_one _)
    · exact (exp_pos _).le
    · exact exp_le_one_iff.mpr (by linarith)
  have comparator_one_le_one (z : ℝ × ℝ) (hz : 0 ≤ z.2) : comparatorOneDensity z ≤ 1 := by
    apply mul_le_one₀ (uniform_le_one z.1)
    · exact (exp_pos _).le
    · exact exp_le_one_iff.mpr (by linarith)
  have one_entropy_integrable : Integrable (fun z => oneDensity z * log (oneDensity z)) base := by
    have he : (fun z => oneDensity z * log (oneDensity z)) = fun z : ℝ × ℝ => (phi z.1 * log (phi z.1)) * exp (-z.2) - phi z.1 * (z.2 * exp (-z.2)) := by
      funext z; unfold oneDensity; rw [log_mul (ne_of_gt (phi_pos _)) (ne_of_gt (exp_pos _)), log_exp]; ring
    rw [he]; exact ((continuous_angle_integrable (phi_cont.mul (phi_cont.log (fun t => ne_of_gt (phi_pos t))))).mul_prod exp_integrable).sub (phi_integrable.mul_prod action_first_integrable)
  have comparator_one_entropy_integrable : Integrable (fun z => comparatorOneDensity z * log (comparatorOneDensity z)) base := by
    have he : (fun z => comparatorOneDensity z * log (comparatorOneDensity z)) = fun z : ℝ × ℝ => (uniformPhase z.1 * log (uniformPhase z.1)) * exp (-z.2) - uniformPhase z.1 * (z.2 * exp (-z.2)) := by
      funext z; unfold comparatorOneDensity; rw [log_mul (ne_of_gt (uniform_pos z.1)) (ne_of_gt (exp_pos (-z.2))), log_exp]; ring
    rw [he]; exact ((continuous_angle_integrable (h := fun t : ℝ => uniformPhase t * log (uniformPhase t)) (by unfold uniformPhase; fun_prop)).mul_prod exp_integrable).sub
      ((continuous_angle_integrable (h := uniformPhase) (by unfold uniformPhase; fun_prop)).mul_prod action_first_integrable)
  have full_entropy_integrable : Integrable (fun z => fullDensity z * log (fullDensity z)) fullBase := by
    have he : (fun z => fullDensity z * log (fullDensity z)) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => (oneDensity z.1 * log (oneDensity z.1)) * oneDensity z.2 +
          oneDensity z.1 * (oneDensity z.2 * log (oneDensity z.2)) := by
      funext z; unfold fullDensity; rw [log_mul (ne_of_gt (one_pos _)) (ne_of_gt (one_pos _))]; ring
    rw [he]; exact (one_entropy_integrable.mul_prod one_integrable).add (one_integrable.mul_prod one_entropy_integrable)
  have comparator_entropy_integrable : Integrable (fun z => comparatorDensity z * log (comparatorDensity z)) fullBase := by
    have he : (fun z => comparatorDensity z * log (comparatorDensity z)) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => (comparatorOneDensity z.1 * log (comparatorOneDensity z.1)) * comparatorOneDensity z.2 +
          comparatorOneDensity z.1 * (comparatorOneDensity z.2 * log (comparatorOneDensity z.2)) := by
      funext z; unfold comparatorDensity; rw [log_mul (ne_of_gt (comparator_one_pos _)) (ne_of_gt (comparator_one_pos _))]; ring
    rw [he]; exact (comparator_one_entropy_integrable.mul_prod comparator_one_integrable).add (comparator_one_integrable.mul_prod comparator_one_entropy_integrable)
  have full_entropy_nonneg : 0 ≤ -(∫ z, fullDensity z * log (fullDensity z) ∂fullBase) := by
    rw [← integral_neg]; apply integral_nonneg_of_ae; filter_upwards [full_positive_actions_ae] with z hz
    have hle : fullDensity z ≤ 1 := mul_le_one₀ (one_le_one _ hz.1.le) (one_pos _).le (one_le_one _ hz.2.le)
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (full_pos _).le (log_nonpos (full_pos _).le hle))
  have comparator_entropy_nonneg : 0 ≤ -(∫ z, comparatorDensity z * log (comparatorDensity z) ∂fullBase) := by
    rw [← integral_neg]; apply integral_nonneg_of_ae; filter_upwards [full_positive_actions_ae] with z hz
    have hle : comparatorDensity z ≤ 1 := mul_le_one₀ (comparator_one_le_one _ hz.1.le) (comparator_one_pos _).le (comparator_one_le_one _ hz.2.le)
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (comparator_pos _).le (log_nonpos (comparator_pos _).le hle))
  have radial_sqrt_integrable : Integrable (fun J : ℝ => sqrt (2*J) * exp (-J)) action := by
    have hi := GammaIntegral_convergent (s := (3/2 : ℝ)) (by norm_num)
    norm_num at hi
    have hs : Integrable (fun J : ℝ => sqrt J * exp (-J)) action := by simpa [IntegrableOn, action, sqrt_eq_rpow, mul_comm] using hi
    convert hs.const_mul (sqrt 2) using 1; funext J; rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have q_weight_integrable : Integrable (fun z => q z * oneDensity z) base := by
    convert (continuous_angle_integrable (h := fun t : ℝ => sin t * phi t) (by unfold phi; fun_prop)).mul_prod radial_sqrt_integrable using 1; funext z; dsimp [q, oneDensity]; ring
  have p_weight_integrable : Integrable (fun z => p z * oneDensity z) base := by
    convert (continuous_angle_integrable (h := fun t : ℝ => cos t * phi t) (by unfold phi; fun_prop)).mul_prod radial_sqrt_integrable using 1; funext z; dsimp [p, oneDensity]; ring
  have q_one_mean : ∫ z, q z * oneDensity z ∂base = 0 := by
    have he : (fun z => q z * oneDensity z) = fun z : ℝ × ℝ => (sin z.1 * phi z.1) * (sqrt (2*z.2) * exp (-z.2)) := by funext z; unfold q oneDensity; ring
    rw [he, integral_prod_mul (f := fun t : ℝ => sin t * phi t) (g := fun J : ℝ => sqrt (2*J) * exp (-J)), sin_phase_mean, zero_mul]
  have p_one_mean : ∫ z, p z * oneDensity z ∂base = 0 := by
    have he : (fun z => p z * oneDensity z) = fun z : ℝ × ℝ => (cos z.1 * phi z.1) * (sqrt (2*z.2) * exp (-z.2)) := by funext z; unfold p oneDensity; ring
    rw [he, integral_prod_mul (f := fun t : ℝ => cos t * phi t) (g := fun J : ℝ => sqrt (2*J) * exp (-J)), cos_phase_mean, zero_mul]
  have q_square_ae : (fun z => q z ^ 2 * oneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (sin z.1 ^ 2 * phi z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold q oneDensity; rw [mul_pow, sq_sqrt (by positivity)]; ring
  have p_square_ae : (fun z => p z ^ 2 * oneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (cos z.1 ^ 2 * phi z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold p oneDensity; rw [mul_pow, sq_sqrt (by positivity)]; ring
  have qp_product_ae : (fun z => q z * p z * oneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (sin z.1 * cos z.1 * phi z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold q p oneDensity
    calc
      sqrt (2*z.2) * sin z.1 * (sqrt (2*z.2) * cos z.1) * (phi z.1 * exp (-z.2)) = sqrt (2*z.2) ^ 2 * (sin z.1 * cos z.1 * phi z.1 * exp (-z.2)) := by ring
      _ = _ := by rw [sq_sqrt (show 0 ≤ 2*z.2 by positivity)]; ring
  have q_square_weight_integrable : Integrable (fun z => q z ^ 2 * oneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (sin z.1 ^ 2 * phi z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => sin t ^ 2 * phi t) (by unfold phi; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr q_square_ae.symm
  have p_square_weight_integrable : Integrable (fun z => p z ^ 2 * oneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (cos z.1 ^ 2 * phi z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => cos t ^ 2 * phi t) (by unfold phi; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr p_square_ae.symm
  have qp_weight_integrable : Integrable (fun z => q z * p z * oneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (sin z.1 * cos z.1 * phi z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => sin t * cos t * phi t) (by unfold phi; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr qp_product_ae.symm
  have q_one_square : ∫ z, q z ^ 2 * oneDensity z ∂base = 3/4 := by
    rw [integral_congr_ae q_square_ae, integral_prod_mul (f := fun t : ℝ => sin t ^ 2 * phi t) (g := fun J : ℝ => 2*(J * exp (-J))), integral_const_mul, sin_sq_phase, action_first_moment]; norm_num
  have p_one_square : ∫ z, p z ^ 2 * oneDensity z ∂base = 5/4 := by
    rw [integral_congr_ae p_square_ae, integral_prod_mul (f := fun t : ℝ => cos t ^ 2 * phi t) (g := fun J : ℝ => 2*(J * exp (-J))), integral_const_mul, cos_sq_phase, action_first_moment]; norm_num
  have qp_one_product : ∫ z, q z * p z * oneDensity z ∂base = 0 := by
    rw [integral_congr_ae qp_product_ae, integral_prod_mul (f := fun t : ℝ => sin t * cos t * phi t) (g := fun J : ℝ => 2*(J * exp (-J))), sin_cos_phase, zero_mul]
  have witness_expectation (h : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) : ∫ z, h z ∂witnessLaw = ∫ z, h z * fullDensity z ∂fullBase := by
    unfold witnessLaw; rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun z => ENNReal.ofReal (fullDensity z)) by unfold fullDensity oneDensity phi; fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    congr 1; funext z; rw [ENNReal.toReal_ofReal (full_nonneg z), smul_eq_mul, mul_comm]
  have witness_fst_expectation (h : (ℝ × ℝ) → ℝ) : ∫ z, h z.1 ∂witnessLaw = ∫ z, h z * oneDensity z ∂base := by
    rw [witness_expectation]
    have he : (fun z => h z.1 * fullDensity z) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => (h z.1 * oneDensity z.1) * oneDensity z.2 := by funext z; unfold fullDensity; ring
    rw [he, integral_prod_mul (f := fun z => h z * oneDensity z) (g := oneDensity), one_mass, mul_one]
  have witness_snd_expectation (h : (ℝ × ℝ) → ℝ) : ∫ z, h z.2 ∂witnessLaw = ∫ z, h z * oneDensity z ∂base := by
    rw [witness_expectation]
    have he : (fun z => h z.2 * fullDensity z) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => oneDensity z.1 * (h z.2 * oneDensity z.2) := by funext z; unfold fullDensity; ring
    rw [he, integral_prod_mul (f := oneDensity) (g := fun z => h z * oneDensity z), one_mass, one_mul]
  let Q (j : Bool) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := q (if j then z.2 else z.1); let P (j : Bool) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := p (if j then z.2 else z.1)
  have witness_q_mean (j : Bool) : ∫ z, Q j z ∂witnessLaw = 0 := by
    cases j
    · exact (witness_fst_expectation q).trans q_one_mean
    · exact (witness_snd_expectation q).trans q_one_mean
  have witness_p_mean (j : Bool) : ∫ z, P j z ∂witnessLaw = 0 := by
    cases j
    · exact (witness_fst_expectation p).trans p_one_mean
    · exact (witness_snd_expectation p).trans p_one_mean
  have witness_q_square (j : Bool) : ∫ z, Q j z ^ 2 ∂witnessLaw = 3/4 := by
    cases j
    · exact (witness_fst_expectation (fun z => q z ^ 2)).trans q_one_square
    · exact (witness_snd_expectation (fun z => q z ^ 2)).trans q_one_square
  have witness_p_square (j : Bool) : ∫ z, P j z ^ 2 ∂witnessLaw = 5/4 := by
    cases j
    · exact (witness_fst_expectation (fun z => p z ^ 2)).trans p_one_square
    · exact (witness_snd_expectation (fun z => p z ^ 2)).trans p_one_square
  have witness_qp_product (j : Bool) : ∫ z, Q j z * P j z ∂witnessLaw = 0 := by
    cases j
    · exact (witness_fst_expectation (fun z => q z * p z)).trans qp_one_product
    · exact (witness_snd_expectation (fun z => q z * p z)).trans qp_one_product
  have witness_covariance_blocks (j : Bool) : ProbabilityTheory.covariance (Q j) (Q j) witnessLaw = 3/4 ∧ ProbabilityTheory.covariance (P j) (P j) witnessLaw = 5/4 ∧
      ProbabilityTheory.covariance (Q j) (P j) witnessLaw = 0 := by
    simp only [ProbabilityTheory.covariance, witness_q_mean, witness_p_mean, sub_zero]
    exact ⟨by simpa only [pow_two] using witness_q_square j, by simpa only [pow_two] using witness_p_square j, witness_qp_product j⟩
  have uniform_cont : Continuous uniformPhase := by unfold uniformPhase; fun_prop
  have uniform_sin_sq : ∫ t, sin t ^ 2 * uniformPhase t ∂angle = 1/2 := by
    simp only [uniformPhase]; rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π), integral_sin_sq]
    simp only [sin_pi, sin_neg, neg_zero, cos_pi, cos_neg, zero_mul, sub_zero, zero_sub]; field_simp; ring
  have uniform_cos_sq : ∫ t, cos t ^ 2 * uniformPhase t ∂angle = 1/2 := by
    simp only [uniformPhase]; rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π), integral_cos_sq]
    simp only [sin_pi, sin_neg, neg_zero, cos_pi, cos_neg, mul_zero, sub_zero, zero_sub]; field_simp; ring
  have uniform_sin_mean : ∫ t, sin t * uniformPhase t ∂angle = 0 := by
    simp only [uniformPhase]; rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π), integral_sin]; simp
  have uniform_cos_mean : ∫ t, cos t * uniformPhase t ∂angle = 0 := by
    simp only [uniformPhase]; rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π), integral_cos]; simp
  have uniform_sin_cos : ∫ t, sin t * cos t * uniformPhase t ∂angle = 0 := by
    simp only [uniformPhase]; rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π), integral_sin_mul_cos₁]; simp
  have comparator_q_weight_integrable : Integrable (fun z => q z * comparatorOneDensity z) base := by
    convert (continuous_angle_integrable (h := fun t : ℝ => sin t * uniformPhase t) (by unfold uniformPhase; fun_prop)).mul_prod radial_sqrt_integrable using 1; funext z
    dsimp [q, comparatorOneDensity]; ring
  have comparator_p_weight_integrable : Integrable (fun z => p z * comparatorOneDensity z) base := by
    convert (continuous_angle_integrable (h := fun t : ℝ => cos t * uniformPhase t) (by unfold uniformPhase; fun_prop)).mul_prod radial_sqrt_integrable using 1; funext z
    dsimp [p, comparatorOneDensity]; ring
  have comparator_q_one_mean : ∫ z, q z * comparatorOneDensity z ∂base = 0 := by
    have he : (fun z => q z * comparatorOneDensity z) = fun z : ℝ × ℝ => (sin z.1 * uniformPhase z.1) * (sqrt (2*z.2) * exp (-z.2)) := by funext z; unfold q comparatorOneDensity; ring
    rw [he, integral_prod_mul (f := fun t : ℝ => sin t * uniformPhase t) (g := fun J : ℝ => sqrt (2*J) * exp (-J)), uniform_sin_mean, zero_mul]
  have comparator_p_one_mean : ∫ z, p z * comparatorOneDensity z ∂base = 0 := by
    have he : (fun z => p z * comparatorOneDensity z) = fun z : ℝ × ℝ => (cos z.1 * uniformPhase z.1) * (sqrt (2*z.2) * exp (-z.2)) := by funext z; unfold p comparatorOneDensity; ring
    rw [he, integral_prod_mul (f := fun t : ℝ => cos t * uniformPhase t) (g := fun J : ℝ => sqrt (2*J) * exp (-J)), uniform_cos_mean, zero_mul]
  have comparator_q_square_ae : (fun z => q z ^ 2 * comparatorOneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (sin z.1 ^ 2 * uniformPhase z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold q comparatorOneDensity; rw [mul_pow, sq_sqrt (by positivity)]; ring
  have comparator_p_square_ae : (fun z => p z ^ 2 * comparatorOneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (cos z.1 ^ 2 * uniformPhase z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold p comparatorOneDensity; rw [mul_pow, sq_sqrt (by positivity)]; ring
  have comparator_qp_product_ae : (fun z => q z * p z * comparatorOneDensity z) =ᵐ[base] fun z : ℝ × ℝ => (sin z.1 * cos z.1 * uniformPhase z.1) * (2*(z.2 * exp (-z.2))) := by
    filter_upwards [positive_action_ae] with z hz; unfold q p comparatorOneDensity
    calc
      sqrt (2*z.2) * sin z.1 * (sqrt (2*z.2) * cos z.1) * (uniformPhase z.1 * exp (-z.2)) = sqrt (2*z.2) ^ 2 * (sin z.1 * cos z.1 * uniformPhase z.1 * exp (-z.2)) := by ring
      _ = _ := by rw [sq_sqrt (show 0 ≤ 2*z.2 by positivity)]; ring
  have comparator_q_square_weight_integrable : Integrable (fun z => q z ^ 2 * comparatorOneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (sin z.1 ^ 2 * uniformPhase z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => sin t ^ 2 * uniformPhase t) (by unfold uniformPhase; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr comparator_q_square_ae.symm
  have comparator_p_square_weight_integrable : Integrable (fun z => p z ^ 2 * comparatorOneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (cos z.1 ^ 2 * uniformPhase z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => cos t ^ 2 * uniformPhase t) (by unfold uniformPhase; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr comparator_p_square_ae.symm
  have comparator_qp_weight_integrable : Integrable (fun z => q z * p z * comparatorOneDensity z) base := by
    have hi : Integrable (fun z : ℝ × ℝ => (sin z.1 * cos z.1 * uniformPhase z.1) * (2*(z.2 * exp (-z.2)))) base :=
      (continuous_angle_integrable (h := fun t : ℝ => sin t * cos t * uniformPhase t) (by unfold uniformPhase; fun_prop)).mul_prod (action_first_integrable.const_mul 2)
    exact hi.congr comparator_qp_product_ae.symm
  have comparator_q_one_square : ∫ z, q z ^ 2 * comparatorOneDensity z ∂base = 1 := by
    rw [integral_congr_ae comparator_q_square_ae, integral_prod_mul (f := fun t : ℝ => sin t ^ 2 * uniformPhase t) (g := fun J : ℝ => 2*(J * exp (-J))), integral_const_mul,
      uniform_sin_sq, action_first_moment]
    norm_num
  have comparator_p_one_square : ∫ z, p z ^ 2 * comparatorOneDensity z ∂base = 1 := by
    rw [integral_congr_ae comparator_p_square_ae, integral_prod_mul (f := fun t : ℝ => cos t ^ 2 * uniformPhase t) (g := fun J : ℝ => 2*(J * exp (-J))), integral_const_mul,
      uniform_cos_sq, action_first_moment]
    norm_num
  have comparator_qp_one_product : ∫ z, q z * p z * comparatorOneDensity z ∂base = 0 := by
    rw [integral_congr_ae comparator_qp_product_ae, integral_prod_mul (f := fun t : ℝ => sin t * cos t * uniformPhase t) (g := fun J : ℝ => 2*(J * exp (-J))), uniform_sin_cos, zero_mul]
  have comparator_expectation (h : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) : ∫ z, h z ∂comparatorLaw = ∫ z, h z * comparatorDensity z ∂fullBase := by
    unfold comparatorLaw
    rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun z => ENNReal.ofReal (comparatorDensity z)) by unfold comparatorDensity comparatorOneDensity uniformPhase; fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    congr 1; funext z; rw [ENNReal.toReal_ofReal (comparator_nonneg z), smul_eq_mul, mul_comm]
  have comparator_fst_expectation (h : (ℝ × ℝ) → ℝ) : ∫ z, h z.1 ∂comparatorLaw = ∫ z, h z * comparatorOneDensity z ∂base := by
    rw [comparator_expectation]
    have he : (fun z => h z.1 * comparatorDensity z) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => (h z.1 * comparatorOneDensity z.1) * comparatorOneDensity z.2 := by funext z; unfold comparatorDensity; ring
    rw [he, integral_prod_mul (f := fun z => h z * comparatorOneDensity z) (g := comparatorOneDensity), comparator_one_mass, mul_one]
  have comparator_snd_expectation (h : (ℝ × ℝ) → ℝ) : ∫ z, h z.2 ∂comparatorLaw = ∫ z, h z * comparatorOneDensity z ∂base := by
    rw [comparator_expectation]
    have he : (fun z => h z.2 * comparatorDensity z) = fun z : (ℝ × ℝ) × (ℝ × ℝ) => comparatorOneDensity z.1 * (h z.2 * comparatorOneDensity z.2) := by funext z; unfold comparatorDensity; ring
    rw [he, integral_prod_mul (f := comparatorOneDensity) (g := fun z => h z * comparatorOneDensity z), comparator_one_mass, one_mul]
  have comparator_q_mean (j : Bool) : ∫ z, Q j z ∂comparatorLaw = 0 := by
    cases j
    · exact (comparator_fst_expectation q).trans comparator_q_one_mean
    · exact (comparator_snd_expectation q).trans comparator_q_one_mean
  have comparator_p_mean (j : Bool) : ∫ z, P j z ∂comparatorLaw = 0 := by
    cases j
    · exact (comparator_fst_expectation p).trans comparator_p_one_mean
    · exact (comparator_snd_expectation p).trans comparator_p_one_mean
  have comparator_q_square (j : Bool) : ∫ z, Q j z ^ 2 ∂comparatorLaw = 1 := by
    cases j
    · exact (comparator_fst_expectation (fun z => q z ^ 2)).trans comparator_q_one_square
    · exact (comparator_snd_expectation (fun z => q z ^ 2)).trans comparator_q_one_square
  have comparator_p_square (j : Bool) : ∫ z, P j z ^ 2 ∂comparatorLaw = 1 := by
    cases j
    · exact (comparator_fst_expectation (fun z => p z ^ 2)).trans comparator_p_one_square
    · exact (comparator_snd_expectation (fun z => p z ^ 2)).trans comparator_p_one_square
  have comparator_qp_product (j : Bool) : ∫ z, Q j z * P j z ∂comparatorLaw = 0 := by
    cases j
    · exact (comparator_fst_expectation (fun z => q z * p z)).trans comparator_qp_one_product
    · exact (comparator_snd_expectation (fun z => q z * p z)).trans comparator_qp_one_product
  have comparator_covariance_blocks (j : Bool) : ProbabilityTheory.covariance (Q j) (Q j) comparatorLaw = 1 ∧ ProbabilityTheory.covariance (P j) (P j) comparatorLaw = 1 ∧
      ProbabilityTheory.covariance (Q j) (P j) comparatorLaw = 0 := by
    simp only [ProbabilityTheory.covariance, comparator_q_mean, comparator_p_mean, sub_zero]
    exact ⟨by simpa only [pow_two] using comparator_q_square j, by simpa only [pow_two] using comparator_p_square j, comparator_qp_product j⟩
  have witness_coordinate_integrable (h : (ℝ × ℝ) → ℝ) (hh : Integrable (fun z => h z * oneDensity z) base) (j : Bool) :
      Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => h (if j then z.2 else z.1)) witnessLaw := by
    unfold witnessLaw
    rw [integrable_withDensity_iff (show Measurable (fun z => ENNReal.ofReal (fullDensity z)) by unfold fullDensity oneDensity phi; fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (full_nonneg _)]
    cases j
    · convert hh.mul_prod one_integrable using 1
      funext z; dsimp [fullDensity]; ring
    · convert one_integrable.mul_prod hh using 1
      funext z; dsimp [fullDensity]; ring
  have comparator_coordinate_integrable (h : (ℝ × ℝ) → ℝ) (hh : Integrable (fun z => h z * comparatorOneDensity z) base) (j : Bool) :
      Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => h (if j then z.2 else z.1)) comparatorLaw := by
    unfold comparatorLaw
    rw [integrable_withDensity_iff (show Measurable (fun z => ENNReal.ofReal (comparatorDensity z)) by
        unfold comparatorDensity comparatorOneDensity uniformPhase; fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (comparator_nonneg _)]
    cases j
    · convert hh.mul_prod comparator_one_integrable using 1
      funext z; dsimp [comparatorDensity]; ring
    · convert comparator_one_integrable.mul_prod hh using 1
      funext z; dsimp [comparatorDensity]; ring
  have witness_moments_integrable (j : Bool) : Integrable (Q j) witnessLaw ∧ Integrable (P j) witnessLaw ∧ Integrable (fun z => Q j z ^ 2) witnessLaw ∧ Integrable (fun z => P j z ^ 2) witnessLaw ∧
      Integrable (fun z => Q j z * P j z) witnessLaw :=
    ⟨witness_coordinate_integrable q q_weight_integrable j, witness_coordinate_integrable p p_weight_integrable j, witness_coordinate_integrable (fun z => q z ^ 2) q_square_weight_integrable j,
      witness_coordinate_integrable (fun z => p z ^ 2) p_square_weight_integrable j,
      witness_coordinate_integrable (fun z => q z * p z) qp_weight_integrable j⟩
  have comparator_moments_integrable (j : Bool) : Integrable (Q j) comparatorLaw ∧ Integrable (P j) comparatorLaw ∧ Integrable (fun z => Q j z ^ 2) comparatorLaw ∧
      Integrable (fun z => P j z ^ 2) comparatorLaw ∧
      Integrable (fun z => Q j z * P j z) comparatorLaw :=
    ⟨comparator_coordinate_integrable q comparator_q_weight_integrable j, comparator_coordinate_integrable p comparator_p_weight_integrable j,
      comparator_coordinate_integrable (fun z => q z ^ 2) comparator_q_square_weight_integrable j,
      comparator_coordinate_integrable (fun z => p z ^ 2) comparator_p_square_weight_integrable j,
      comparator_coordinate_integrable (fun z => q z * p z) comparator_qp_weight_integrable j⟩
  let uncertainty (μ : Measure ((ℝ × ℝ) × (ℝ × ℝ))) (j : Bool) : ℝ := sqrt (ProbabilityTheory.covariance (Q j) (Q j) μ * ProbabilityTheory.covariance (P j) (P j) μ -
      ProbabilityTheory.covariance (Q j) (P j) μ ^ 2)
  have strict_uncertainty_same_realization (j : Bool) : uncertainty witnessLaw j < uncertainty comparatorLaw j := by
    obtain ⟨hqq,hpp,hqp⟩ := witness_covariance_blocks j; obtain ⟨gqq,gpp,gqp⟩ := comparator_covariance_blocks j
    simp only [uncertainty, hqq,hpp,hqp,gqq,gpp,gqp, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one, sqrt_one]
    have hs := sq_sqrt (show 0 ≤ (3/4 : ℝ)*(5/4) by norm_num)
    have hp := sqrt_nonneg ((3/4 : ℝ)*(5/4)); nlinarith
  have cartesian_continuous : Continuous cartesian := by unfold cartesian q p; fun_prop
  have cartesian_measurable : Measurable cartesian := cartesian_continuous.measurable
  have zero_action_null : base {z : ℝ × ℝ | z.2 = 0} = 0 := by
    have hpos : base {z : ℝ × ℝ | ¬ 0 < z.2} = 0 := ae_iff.mp positive_action_ae; apply measure_mono_null (μ := base) ?_ hpos; intro z hz; change z.2 = 0 at hz; change ¬ 0 < z.2; rw [hz]; norm_num
  have zero_action_ae : ∀ᵐ z : ℝ × ℝ ∂base, z.2 ≠ 0 := by filter_upwards [positive_action_ae] with z hz; exact ne_of_gt hz
  have polar_source_complement_null : volume polarCoord.sourceᶜ = 0 := by simpa only [ae_eq_univ] using polarCoord_source_ae_eq_univ
  have polarCoord_unit_abs_jacobian (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      |(fderivPolarCoordSymm p).det| = p.1 := by
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
  have cartesian_jacobian_unit (t J : ℝ) (hJ : 0 < J) :
      |(sqrt (2 * J) * cos t) * (cos t / sqrt (2 * J)) - (sin t / sqrt (2 * J)) * (-sqrt (2 * J) * sin t)| = 1 := by
    have hs : 0 < sqrt (2 * J) := by positivity
    have hdet : (sqrt (2 * J) * cos t) * (cos t / sqrt (2 * J)) - (sin t / sqrt (2 * J)) * (-sqrt (2 * J) * sin t) = 1 := by field_simp [ne_of_gt hs]; nlinarith [sin_sq_add_cos_sq t]
    rw [hdet]; norm_num
  have cartesian_zero_action_value (t : ℝ) : cartesian (t, 0) = (0, 0) := by simp [cartesian, q, p]
  have cartesian_seam_value (J : ℝ) : cartesian (π, J) = (0, -sqrt (2 * J)) := by simp [cartesian, q, p]
  let oneDensityZeroExt (z : ℝ × ℝ) : ℝ := if z.2 = 0 then 0 else oneDensity z
  have oneDensityZeroExt_measurable : Measurable oneDensityZeroExt := by
    have hone : Measurable oneDensity := by unfold oneDensity phi; fun_prop
    unfold oneDensityZeroExt; exact Measurable.ite (by measurability) measurable_const hone
  have oneDensity_zero_extension_ae : (fun z : ℝ × ℝ => oneDensity z) =ᵐ[base] oneDensityZeroExt := by filter_upwards [zero_action_ae] with z hz; simp [oneDensityZeroExt, hz]
  have oneDensity_zero_extension_mass : ∫ z, oneDensityZeroExt z ∂base = 1 := by rw [← one_mass, integral_congr_ae oneDensity_zero_extension_ae.symm]
  let fullEntropyZeroExt (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := if z.1.2 = 0 ∨ z.2.2 = 0 then 0 else fullDensity z * log (fullDensity z)
  have fullEntropyZeroExt_measurable : Measurable fullEntropyZeroExt := by
    have hfull : Measurable fullDensity := by unfold fullDensity oneDensity phi; fun_prop
    have hent : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => fullDensity z * log (fullDensity z)) := by fun_prop
    unfold fullEntropyZeroExt
    exact Measurable.ite (p := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 = 0 ∨ z.2.2 = 0) (f := fun _ : (ℝ × ℝ) × (ℝ × ℝ) => (0 : ℝ)) (g := fun z : (ℝ × ℝ) × (ℝ × ℝ) => fullDensity z * log (fullDensity z))
      (by measurability) measurable_const hent
  have full_entropy_zero_extension_ae : (fun z : (ℝ × ℝ) × (ℝ × ℝ) => fullDensity z * log (fullDensity z)) =ᵐ[fullBase] fullEntropyZeroExt := by
    filter_upwards [full_positive_actions_ae] with z hz
    have hne : ¬ (z.1.2 = 0 ∨ z.2.2 = 0) := by intro h; rcases h with h | h <;> linarith
    change fullDensity z * log (fullDensity z) = (if z.1.2 = 0 ∨ z.2.2 = 0 then 0 else fullDensity z * log (fullDensity z)); rw [if_neg hne]
  have full_entropy_zero_extension_transport : ∫ z, fullEntropyZeroExt z ∂fullBase = ∫ z, fullDensity z * log (fullDensity z) ∂fullBase := by
    exact integral_congr_ae full_entropy_zero_extension_ae.symm
  have actual_cartesian_volume_map : Measure.map cartesian base = (volume : Measure (ℝ × ℝ)) := by
    let T : Set (ℝ × ℝ) := polarCoord.target; let S : Set (ℝ × ℝ) := Ioo (-π) π ×ˢ Ioi (0 : ℝ); let H : (ℝ × ℝ) → (ℝ × ℝ) := fun u => (u.2, u.1 ^ 2 / 2)
    let DH : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun u => (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![0, 1; u.1, 0]).toContinuousLinearMap
    let W : Measure (ℝ × ℝ) := ((volume : Measure (ℝ × ℝ)).restrict T).withDensity (fun u => ENNReal.ofReal u.1); have hT : MeasurableSet T := polarCoord.open_target.measurableSet
    have hDH : ∀ u, HasFDerivAt H (DH u) u := by
      intro u; dsimp [DH, H]; rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
      have hf : HasFDerivAt (fun z : ℝ × ℝ => z.1 ^ 2) ((2 * u.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) u := by simpa using (hasFDerivAt_fst (𝕜 := ℝ) (p := u)).pow 2
      convert! HasFDerivAt.prodMk (𝕜 := ℝ) hasFDerivAt_snd (hf.const_mul (1/2 : ℝ)) using 1 <;> simp [smul_smul, div_eq_mul_inv] <;> ring
    have hdet : ∀ u, (DH u).det = -u.1 := by intro u; simp [DH, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
    have hHinj : InjOn H T := by
      intro u hu v hv huv; have ht : u.2 = v.2 := congrArg Prod.fst huv
      have hr : u.1 ^ 2 = v.1 ^ 2 := by have := congrArg Prod.snd huv; dsimp [H] at this; linarith
      exact Prod.ext ((sq_eq_sq₀ (le_of_lt hu.1) (le_of_lt hv.1)).mp hr) ht
    have hHimage : H '' T = S := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu.2, by change 0 < u.1 ^ 2 / 2; exact div_pos (sq_pos_of_pos hu.1) (by norm_num)⟩
      · intro hz
        change z.1 ∈ Ioo (-π) π ∧ 0 < z.2 at hz; refine ⟨(sqrt (2*z.2), z.1), ⟨by exact sqrt_pos.2 (by linarith [hz.2]), hz.1⟩, ?_⟩; apply Prod.ext
        · rfl
        · dsimp [H]
          rw [sq_sqrt (by linarith [hz.2] : 0 ≤ 2*z.2)]; ring
    have hbase : base = (volume : Measure (ℝ × ℝ)).restrict S := by dsimp [base, angle, action, S]; rw [← restrict_Ioo_eq_restrict_Ioc]; exact Measure.prod_restrict _ _
    have hHmeas : Measurable H := by dsimp [H]; fun_prop
    have hHW : Measure.map H W = base := by
      rw [hbase, ← hHimage]; have hx := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (ℝ × ℝ)) hT.nullMeasurableSet (fun u _ => (hDH u).hasFDerivWithinAt) hHinj
      have hweight : ((volume : Measure (ℝ × ℝ)).restrict T).withDensity (fun u => ENNReal.ofReal |(DH u).det|) = W := by
        apply withDensity_congr_ae; filter_upwards [ae_restrict_mem hT] with u hu; rw [hdet, abs_neg, abs_of_pos hu.1]
      rw [hweight] at hx; exact hx
    have hPW : Measure.map polarCoord.symm W = (volume : Measure (ℝ × ℝ)) := by
      have hx := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (ℝ × ℝ)) hT.nullMeasurableSet (fun u _ => (hasFDerivAt_polarCoord_symm u).hasFDerivWithinAt) polarCoord.symm.injOn
      have hweight : ((volume : Measure (ℝ × ℝ)).restrict T).withDensity (fun u => ENNReal.ofReal |(fderivPolarCoordSymm u).det|) = W := by
        apply withDensity_congr_ae; filter_upwards [ae_restrict_mem hT] with u hu; rw [det_fderivPolarCoordSymm, abs_of_pos hu.1]
      rw [hweight, polarCoord.symm_image_target_eq_source, Measure.restrict_congr_set polarCoord_source_ae_eq_univ, Measure.restrict_univ] at hx; exact hx
    have hcomp : cartesian ∘ H =ᵐ[W] Prod.swap ∘ polarCoord.symm := by
      have hae : ∀ᵐ u ∂W, u ∈ T := (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hT); filter_upwards [hae] with u hu
      have hs : sqrt (2 * (u.1 ^ 2 / 2)) = u.1 := by convert sqrt_sq (le_of_lt hu.1) using 1 <;> congr 1 <;> ring
      change (sqrt (2 * (u.1 ^ 2 / 2)) * sin u.2, sqrt (2 * (u.1 ^ 2 / 2)) * cos u.2) = (u.1 * sin u.2, u.1 * cos u.2); rw [hs]
    rw [← hHW, Measure.map_map cartesian_measurable hHmeas, Measure.map_congr hcomp, ← Measure.map_map measurable_swap continuous_polarCoord_symm.measurable, hPW]
    exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).map_eq
  have actual_cartesian_product_volume_map : Measure.map (Prod.map cartesian cartesian) fullBase = (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) := by
    rw [← Measure.map_prod_map base base cartesian_measurable cartesian_measurable, actual_cartesian_volume_map]
    rfl
  let rho_w (x : ℝ × ℝ) : ℝ := if R2 x = 0 then 0 else exp (-R2 x / 2) * (1 + (x.2^2-x.1^2)/(2*R2 x))/(2*π); let rho_c (x : ℝ × ℝ) : ℝ := exp (-R2 x / 2)/(2*π)
  let Fw (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := rho_w x.1 * rho_w x.2; let Fc (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := rho_c x.1 * rho_c x.2
  have actual_cartesian_weighted_and_entropy_transport : Measurable Fw ∧ Measurable Fc ∧ (∀ x, 0 ≤ Fw x) ∧ (∀ x, 0 ≤ Fc x) ∧ Measure.map (Prod.map cartesian cartesian) witnessLaw =
        (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fw x)) ∧
      Measure.map (Prod.map cartesian cartesian) comparatorLaw = (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fc x)) ∧
      Integrable (fun x => Fw x * log (Fw x)) volume ∧
      Integrable (fun x => Fc x * log (Fc x)) volume ∧
      (∫ x, Fw x * log (Fw x)) = (∫ z, fullDensity z * log (fullDensity z) ∂fullBase) ∧
      (∫ x, Fc x * log (Fc x)) = (∫ z, comparatorDensity z * log (comparatorDensity z) ∂fullBase) := by
    let C2 := Prod.map cartesian cartesian; have hC : Measurable C2 := cartesian_measurable.prodMap cartesian_measurable
    have hvol : Measure.map C2 fullBase = volume := actual_cartesian_product_volume_map
    have hrw : Measurable rho_w := by
      unfold rho_w R2; exact Measurable.ite (p := fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2 = 0) (f := fun _ : ℝ × ℝ => (0 : ℝ)) (g := fun x : ℝ × ℝ => exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) *
          (1 + (x.2 ^ 2 - x.1 ^ 2) / (2 * (x.1 ^ 2 + x.2 ^ 2))) / (2 * π))
        (by measurability) measurable_const (by fun_prop)
    have hrc : Measurable rho_c := by unfold rho_c R2; fun_prop
    have hFw : Measurable Fw := (hrw.comp measurable_fst).mul (hrw.comp measurable_snd); have hFc : Measurable Fc := (hrc.comp measurable_fst).mul (hrc.comp measurable_snd)
    have hnrw : ∀ x, 0 ≤ rho_w x := by
      intro x; unfold rho_w
      split_ifs with hx
      · exact le_rfl
      · have hr : 0 < R2 x := lt_of_le_of_ne (by unfold R2; positivity) (Ne.symm hx)
        have hd : -1 ≤ (x.2^2-x.1^2)/(2*R2 x) := by apply (le_div_iff₀ (by positivity : 0 < 2*R2 x)).mpr; unfold R2; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
        apply div_nonneg
        · apply mul_nonneg (le_of_lt (exp_pos _))
          linarith
        · positivity
    have hnrc : ∀ x, 0 ≤ rho_c x := by intro x; unfold rho_c; positivity
    have hnFw : ∀ x, 0 ≤ Fw x := fun x => mul_nonneg (hnrw x.1) (hnrw x.2); have hnFc : ∀ x, 0 ≤ Fc x := fun x => mul_nonneg (hnrc x.1) (hnrc x.2)
    have hlocal : ∀ z : ℝ × ℝ, 0 < z.2 → rho_w (cartesian z) = oneDensity z ∧ rho_c (cartesian z) = comparatorOneDensity z := by
      intro z hz
      have hs : sqrt (2*z.2)^2 = 2*z.2 := sq_sqrt (by positivity)
      have hq : (cartesian z).1^2 = (2*z.2) * sin z.1 ^ 2 := by simp only [cartesian, q, mul_pow]; rw [hs]
      have hp : (cartesian z).2^2 = (2*z.2) * cos z.1 ^ 2 := by simp only [cartesian, p, mul_pow]; rw [hs]
      have hr : R2 (cartesian z) = 2*z.2 := by unfold R2; rw [hq, hp, ← mul_add, sin_sq_add_cos_sq, mul_one]
      have ha : (1 + ((cartesian z).2^2-(cartesian z).1^2)/(2*R2 (cartesian z)))/(2*π) = phi z.1 := by rw [hq, hp, hr]; unfold phi; rw [cos_two_mul']; field_simp [ne_of_gt hz]
      rw [hr] at ha; constructor
      · unfold rho_w
        rw [if_neg (by rw [hr]; positivity), hr]
        have he : -(2*z.2)/2 = -z.2 := by ring
        rw [he]; unfold oneDensity; rw [mul_div_assoc, ha]; ring
      · unfold rho_c comparatorOneDensity uniformPhase
        rw [hr]; congr 1 <;> ring
    have hw : (fun z => Fw (C2 z)) =ᵐ[fullBase] fullDensity := by
      filter_upwards [full_positive_actions_ae] with z hz; simp only [Fw, C2, Prod.map, fullDensity, (hlocal z.1 hz.1).1, (hlocal z.2 hz.2).1]
    have hc : (fun z => Fc (C2 z)) =ᵐ[fullBase] comparatorDensity := by
      filter_upwards [full_positive_actions_ae] with z hz; simp only [Fc, C2, Prod.map, comparatorDensity, (hlocal z.1 hz.1).2, (hlocal z.2 hz.2).2]
    have hpush : ∀ (D F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ), Measurable D → Measurable F → (fun z => F (C2 z)) =ᵐ[fullBase] D → Measure.map C2 (fullBase.withDensity (fun z => ENNReal.ofReal (D z))) =
          volume.withDensity (fun x => ENNReal.ofReal (F x)) := by
      intro D F hD hF hDF; apply Measure.ext_of_lintegral; intro g hg; rw [lintegral_map hg hC]; change (∫⁻ z, (g ∘ C2) z ∂fullBase.withDensity (fun z => ENNReal.ofReal (D z))) = _
      rw [lintegral_withDensity_eq_lintegral_mul fullBase hD.ennreal_ofReal (hg.comp hC), lintegral_withDensity_eq_lintegral_mul volume hF.ennreal_ofReal hg]
      calc
        _ = ∫⁻ z, ENNReal.ofReal (F (C2 z)) * g (C2 z) ∂fullBase := by apply lintegral_congr_ae; filter_upwards [hDF] with z hz; simp only [Pi.mul_apply, Function.comp_def, hz]
        _ = ∫⁻ x, (fun x => ENNReal.ofReal (F x) * g x) x ∂volume := by rw [← hvol]; simpa only [Pi.mul_apply, Function.comp_def] using (lintegral_map (hF.ennreal_ofReal.mul hg) hC).symm
        _ = _ := rfl
    have hmD : Measurable fullDensity := by unfold fullDensity oneDensity phi; fun_prop
    have hmDc : Measurable comparatorDensity := by unfold comparatorDensity comparatorOneDensity uniformPhase; fun_prop
    have hwmap := hpush fullDensity Fw hmD hFw hw; have hcmap := hpush comparatorDensity Fc hmDc hFc hc
    have hew : (fun z => Fw (C2 z) * log (Fw (C2 z))) =ᵐ[fullBase] (fun z => fullDensity z * log (fullDensity z)) := by filter_upwards [hw] with z hz; rw [hz]
    have hec : (fun z => Fc (C2 z) * log (Fc (C2 z))) =ᵐ[fullBase] (fun z => comparatorDensity z * log (comparatorDensity z)) := by filter_upwards [hc] with z hz; rw [hz]
    have hmEw : Measurable (fun x => Fw x * log (Fw x)) := hFw.mul hFw.log; have hmEc : Measurable (fun x => Fc x * log (Fc x)) := hFc.mul hFc.log
    have hiw : Integrable (fun x => Fw x * log (Fw x)) volume := by
      rw [← hvol]; apply (integrable_map_measure hmEw.aestronglyMeasurable hC.aemeasurable).mpr; exact full_entropy_integrable.congr hew.symm
    have hic : Integrable (fun x => Fc x * log (Fc x)) volume := by
      rw [← hvol]; apply (integrable_map_measure hmEc.aestronglyMeasurable hC.aemeasurable).mpr; exact comparator_entropy_integrable.congr hec.symm
    refine ⟨hFw, hFc, hnFw, hnFc, hwmap, hcmap, hiw, hic, ?_, ?_⟩
    · rw [← hvol, integral_map hC.aemeasurable hmEw.aestronglyMeasurable]
      exact integral_congr_ae hew
    · rw [← hvol, integral_map hC.aemeasurable hmEc.aestronglyMeasurable]
      exact integral_congr_ae hec
  have transient_actual_covariance_evidence : let lawW := (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fw x))
      let lawC := (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fc x))
      Measure.map (Prod.map cartesian cartesian) witnessLaw = lawW ∧
      Measure.map (Prod.map cartesian cartesian) comparatorLaw = lawC ∧
      IsProbabilityMeasure lawW ∧ IsProbabilityMeasure lawC ∧
      (∀ i, MemLp (actualCoordinate i) 2 lawW) ∧
      (∀ i, MemLp (actualCoordinate i) 2 lawC) ∧
      actualCovariance lawW = Matrix.diagonal (fun i => if i.2 then (5/4 : ℝ) else 3/4) ∧
      actualCovariance lawC = (1 : Matrix (Bool × Bool) (Bool × Bool) ℝ) ∧
      (actualCovariance lawW).PosDef ∧ (actualCovariance lawC).PosDef ∧
      (∀ j, actualUncertainty lawW j = sqrt (15/16 : ℝ)) ∧
      (∀ j, actualUncertainty lawC j = 1) ∧
      (∀ j, actualUncertainty lawW j < actualUncertainty lawC j) ∧
      lawW = ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_w x))).prod ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_w x))) ∧
      lawC = ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_c x))).prod ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_c x))) ∧
      (∀ (j l k m : Bool), j ≠ l → actualCovariance lawW (j,k) (l,m) = 0) ∧
      (∀ (j l k m : Bool), j ≠ l → actualCovariance lawC (j,k) (l,m) = 0) := by
    dsimp only; let lawW := (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fw x))
    let lawC := (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity (fun x => ENNReal.ofReal (Fc x)); let C2 := Prod.map cartesian cartesian; let Y (i : Bool × Bool) := if i.2 then P i.1 else Q i.1
    have hC2 : Measurable C2 := cartesian_measurable.prodMap cartesian_measurable; obtain ⟨mFw, mFc, nFw, nFc, hW, hC, _, _, _, _⟩ := actual_cartesian_weighted_and_entropy_transport
    change Measure.map C2 witnessLaw = lawW at hW; change Measure.map C2 comparatorLaw = lawC at hC
    have hX (i : Bool × Bool) : Measurable (actualCoordinate i) := by
      rcases i with ⟨j,k⟩
      cases j <;> cases k
      · exact measurable_fst.fst
      · exact measurable_fst.snd
      · exact measurable_snd.fst
      · exact measurable_snd.snd
    have hXY (i : Bool × Bool) : actualCoordinate i ∘ C2 = Y i := by rcases i with ⟨j,k⟩; cases j <;> cases k <;> rfl
    have hYW (i : Bool × Bool) : MemLp (Y i) 2 witnessLaw := by
      rcases i with ⟨j,k⟩
      cases k
      · exact (memLp_two_iff_integrable_sq (witness_moments_integrable j).1.aestronglyMeasurable).mpr
          (witness_moments_integrable j).2.2.1
      · exact (memLp_two_iff_integrable_sq (witness_moments_integrable j).2.1.aestronglyMeasurable).mpr
          (witness_moments_integrable j).2.2.2.1
    have hYC (i : Bool × Bool) : MemLp (Y i) 2 comparatorLaw := by
      rcases i with ⟨j,k⟩
      cases k
      · exact (memLp_two_iff_integrable_sq (comparator_moments_integrable j).1.aestronglyMeasurable).mpr
          (comparator_moments_integrable j).2.2.1
      · exact (memLp_two_iff_integrable_sq (comparator_moments_integrable j).2.1.aestronglyMeasurable).mpr
          (comparator_moments_integrable j).2.2.2.1
    have hLpW (i : Bool × Bool) : MemLp (actualCoordinate i) 2 lawW := by rw [← hW]; apply (memLp_map_measure_iff (hX i).aestronglyMeasurable hC2.aemeasurable).mpr; rw [hXY]; exact hYW i
    have hLpC (i : Bool × Bool) : MemLp (actualCoordinate i) 2 lawC := by rw [← hC]; apply (memLp_map_measure_iff (hX i).aestronglyMeasurable hC2.aemeasurable).mpr; rw [hXY]; exact hYC i
    have hCovW (i k : Bool × Bool) : actualCovariance lawW i k = ProbabilityTheory.covariance (Y i) (Y k) witnessLaw := by
      unfold actualCovariance; rw [← hW, ProbabilityTheory.covariance_map (hX i).aestronglyMeasurable (hX k).aestronglyMeasurable hC2.aemeasurable, hXY, hXY]
    have hCovC (i k : Bool × Bool) : actualCovariance lawC i k = ProbabilityTheory.covariance (Y i) (Y k) comparatorLaw := by
      unfold actualCovariance; rw [← hC, ProbabilityTheory.covariance_map (hX i).aestronglyMeasurable (hX k).aestronglyMeasurable hC2.aemeasurable, hXY, hXY]
    let μw := base.withDensity (fun z => ENNReal.ofReal (oneDensity z)); let μc := base.withDensity (fun z => ENNReal.ofReal (comparatorOneDensity z))
    have hDw : Measurable (fun z => ENNReal.ofReal (oneDensity z)) := by unfold oneDensity phi; fun_prop
    have hDc : Measurable (fun z => ENNReal.ofReal (comparatorOneDensity z)) := by unfold comparatorOneDensity uniformPhase; fun_prop
    have hpw : IsProbabilityMeasure μw := by
      constructor; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal one_integrable (ae_of_all _ (fun z => (one_pos z).le)), one_mass]; norm_num
    have hpc : IsProbabilityMeasure μc := by
      constructor; rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal comparator_one_integrable
          (ae_of_all _ (fun z => (comparator_one_pos z).le)), comparator_one_mass]
      norm_num
    letI := hpw
    letI := hpc
    have hprodW : witnessLaw = μw.prod μw := by dsimp [μw, witnessLaw]; rw [prod_withDensity hDw hDw]; apply withDensity_congr_ae; exact ae_of_all _ (fun z => ENNReal.ofReal_mul (one_pos z.1).le)
    have hprodC : comparatorLaw = μc.prod μc := by
      dsimp [μc, comparatorLaw]; rw [prod_withDensity hDc hDc]; apply withDensity_congr_ae; exact ae_of_all _ (fun z => ENNReal.ofReal_mul (comparator_one_pos z.1).le)
    let Z (k : Bool) (z : ℝ × ℝ) : ℝ := if k then p z else q z
    have hZW (k : Bool) : MemLp (Z k) 2 μw := by
      have hm : Measurable (Z k) := by cases k <;> dsimp [Z, q, p] <;> fun_prop
      apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr; dsimp [μw]; rw [integrable_withDensity_iff hDw (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (one_pos _).le, smul_eq_mul]
      cases k
      · simpa only [Z, Bool.false_eq_true, ↓reduceIte, mul_comm] using q_square_weight_integrable
      · simpa only [Z, ↓reduceIte, mul_comm] using p_square_weight_integrable
    have hZC (k : Bool) : MemLp (Z k) 2 μc := by
      have hm : Measurable (Z k) := by cases k <;> dsimp [Z, q, p] <;> fun_prop
      apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr; dsimp [μc]; rw [integrable_withDensity_iff hDc (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (comparator_one_pos _).le, smul_eq_mul]
      cases k
      · simpa only [Z, Bool.false_eq_true, ↓reduceIte, mul_comm] using comparator_q_square_weight_integrable
      · simpa only [Z, ↓reduceIte, mul_comm] using comparator_p_square_weight_integrable
    have hYf (k : Bool) : Y (false,k) = fun z => Z k z.1 := by cases k <;> rfl
    have hYt (k : Bool) : Y (true,k) = fun z => Z k z.2 := by cases k <;> rfl
    have hcrossW (k l : Bool) : ProbabilityTheory.covariance (Y (false,k)) (Y (true,l)) witnessLaw = 0 := by rw [hprodW, hYf, hYt]; exact ProbabilityTheory.covariance_fst_snd_prod (hZW k) (hZW l)
    have hcrossC (k l : Bool) : ProbabilityTheory.covariance (Y (false,k)) (Y (true,l)) comparatorLaw = 0 := by rw [hprodC, hYf, hYt]; exact ProbabilityTheory.covariance_fst_snd_prod (hZC k) (hZC l)
    have hdiagW : actualCovariance lawW = Matrix.diagonal (fun i => if i.2 then (5/4 : ℝ) else 3/4) := by
      ext ⟨j,k⟩ ⟨l,m⟩
      rw [hCovW]
      cases j <;> cases l <;> cases k <;> cases m <;> simp [Matrix.diagonal, Y]
      all_goals first
        | exact (witness_covariance_blocks _).1
        | exact (witness_covariance_blocks _).2.1
        | exact (witness_covariance_blocks _).2.2
        | exact (ProbabilityTheory.covariance_comm _ _).trans (witness_covariance_blocks _).2.2
        | exact hcrossW false false
        | exact hcrossW false true
        | exact hcrossW true false
        | exact hcrossW true true
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossW false false)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossW false true)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossW true false)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossW true true)
    have hdiagC : actualCovariance lawC = (1 : Matrix (Bool × Bool) (Bool × Bool) ℝ) := by
      ext ⟨j,k⟩ ⟨l,m⟩
      rw [hCovC]
      cases j <;> cases l <;> cases k <;> cases m <;> simp [Matrix.one_apply, Y]
      all_goals first
        | exact (comparator_covariance_blocks _).1
        | exact (comparator_covariance_blocks _).2.1
        | exact (comparator_covariance_blocks _).2.2
        | exact (ProbabilityTheory.covariance_comm _ _).trans (comparator_covariance_blocks _).2.2
        | exact hcrossC false false
        | exact hcrossC false true
        | exact hcrossC true false
        | exact hcrossC true true
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossC false false)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossC false true)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossC true false)
        | exact (ProbabilityTheory.covariance_comm _ _).trans (hcrossC true true)
    have hposW : (actualCovariance lawW).PosDef := by rw [hdiagW, Matrix.posDef_diagonal_iff]; intro i; cases i.2 <;> norm_num
    have hposC : (actualCovariance lawC).PosDef := by rw [hdiagC]; exact Matrix.PosDef.one
    have huW (j : Bool) : actualUncertainty lawW j = uncertainty witnessLaw j := by
      simp only [actualUncertainty, Matrix.det_fin_two_of, hCovW, Y, ↓reduceIte, Bool.false_eq_true, uncertainty]; rw [ProbabilityTheory.covariance_comm (X := P j) (Y := Q j)]; simp only [pow_two]
    have huC (j : Bool) : actualUncertainty lawC j = uncertainty comparatorLaw j := by
      simp only [actualUncertainty, Matrix.det_fin_two_of, hCovC, Y, ↓reduceIte, Bool.false_eq_true, uncertainty]; rw [ProbabilityTheory.covariance_comm (X := P j) (Y := Q j)]; simp only [pow_two]
    have huWval (j : Bool) : actualUncertainty lawW j = sqrt (15/16 : ℝ) := by rw [huW]; obtain ⟨hqq,hpp,hqp⟩ := witness_covariance_blocks j; norm_num [uncertainty, hqq, hpp, hqp]
    have huCval (j : Bool) : actualUncertainty lawC j = 1 := by rw [huC]; obtain ⟨hqq,hpp,hqp⟩ := comparator_covariance_blocks j; norm_num [uncertainty, hqq, hpp, hqp]
    have huStrict (j : Bool) : actualUncertainty lawW j < actualUncertainty lawC j := by rw [huW, huC]; exact strict_uncertainty_same_realization j
    have hProbW : IsProbabilityMeasure lawW := by rw [← hW]; letI := witness_probability; exact Measure.isProbabilityMeasure_map hC2.aemeasurable
    have hProbC : IsProbabilityMeasure lawC := by rw [← hC]; letI := comparator_probability; exact Measure.isProbabilityMeasure_map hC2.aemeasurable
    have hwpos : 0 < rho_w (0,1) := by norm_num [rho_w, R2]; positivity
    have hcpos : 0 < rho_c (0,1) := by unfold rho_c; positivity
    have hnrw (x : ℝ × ℝ) : 0 ≤ rho_w x := nonneg_of_mul_nonneg_left (nFw (x,(0,1))) hwpos; have hnrc (x : ℝ × ℝ) : 0 ≤ rho_c x := nonneg_of_mul_nonneg_left (nFc (x,(0,1))) hcpos
    have hrw : Measurable rho_w := by
      have hm : Measurable (fun x : ℝ × ℝ => Fw (x,(0,1)) / rho_w (0,1)) := (mFw.comp (measurable_id.prodMk measurable_const)).div_const (rho_w (0,1))
      have he : (fun x : ℝ × ℝ => Fw (x,(0,1)) / rho_w (0,1)) = rho_w := by funext x; dsimp [Fw]; exact mul_div_cancel_right₀ _ (ne_of_gt hwpos)
      exact he ▸ hm
    have hrc : Measurable rho_c := by
      have hm : Measurable (fun x : ℝ × ℝ => Fc (x,(0,1)) / rho_c (0,1)) := (mFc.comp (measurable_id.prodMk measurable_const)).div_const (rho_c (0,1))
      have he : (fun x : ℝ × ℝ => Fc (x,(0,1)) / rho_c (0,1)) = rho_c := by funext x; dsimp [Fc]; exact mul_div_cancel_right₀ _ (ne_of_gt hcpos)
      exact he ▸ hm
    have hActualProdW : lawW = ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_w x))).prod ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_w x))) := by
      dsimp [lawW]; rw [prod_withDensity hrw.ennreal_ofReal hrw.ennreal_ofReal]; apply withDensity_congr_ae; exact ae_of_all _ (fun z => ENNReal.ofReal_mul (hnrw z.1))
    have hActualProdC : lawC = ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_c x))).prod ((volume : Measure (ℝ × ℝ)).withDensity (fun x => ENNReal.ofReal (rho_c x))) := by
      dsimp [lawC]; rw [prod_withDensity hrc.ennreal_ofReal hrc.ennreal_ofReal]; apply withDensity_congr_ae; exact ae_of_all _ (fun z => ENNReal.ofReal_mul (hnrc z.1))
    have hActualCrossW (j l k m : Bool) (hjl : j ≠ l) : actualCovariance lawW (j,k) (l,m) = 0 := by rw [hdiagW]; simp [Matrix.diagonal, Prod.mk.injEq, hjl]
    have hActualCrossC (j l k m : Bool) (hjl : j ≠ l) : actualCovariance lawC (j,k) (l,m) = 0 := by rw [hdiagC]; simp [Matrix.one_apply, Prod.mk.injEq, hjl]
    exact ⟨hW, hC, hProbW, hProbC, hLpW, hLpC, hdiagW, hdiagC, hposW, hposC, huWval, huCval, huStrict, hActualProdW, hActualProdC, hActualCrossW, hActualCrossC⟩
  let K (z : ℝ × ℝ) : TorusOne := ((z.1 : Real.Angle), z.2); let K2 : CartesianTwo → TorusTwo := Prod.map K K; let phiA (t : Real.Angle) : ℝ := (1 + (2 • t).cos / 2) / (2 * π)
  let oneDensityA (z : TorusOne) : ℝ := phiA z.1 * exp (-z.2); let comparatorOneDensityA (z : TorusOne) : ℝ := (1 / (2 * π)) * exp (-z.2)
  let densityA (z : TorusTwo) : ℝ := oneDensityA z.1 * oneDensityA z.2; let comparatorDensityA (z : TorusTwo) : ℝ := comparatorOneDensityA z.1 * comparatorOneDensityA z.2
  let C2 : CartesianTwo → CartesianTwo := Prod.map cartesian cartesian; let torusWitnessLaw : Measure TorusTwo := torusFullBase.withDensity (fun z => ENNReal.ofReal (densityA z))
  let torusComparatorLaw : Measure TorusTwo := torusFullBase.withDensity (fun z => ENNReal.ofReal (comparatorDensityA z)); let chartActionProjection (z : CartesianTwo) : ℝ × ℝ := (z.1.2, z.2.2)
  let commonActionLaw : Measure (ℝ × ℝ) := (action.prod action).withDensity (fun J => ENNReal.ofReal (exp (-(J.1 + J.2))))
  -- Transient exact supplier-composition evidence; no retained declaration or admission claim.
  have quotient_weighted_bridge : (volume : Measure Real.Angle) univ = ENNReal.ofReal (2 * π) ∧ MeasurePreserving K2 fullBase torusFullBase ∧ (∀ z, densityA (K2 z) = fullDensity z) ∧
      (∀ z, comparatorDensityA (K2 z) = comparatorDensity z) ∧
      PsiA2 ∘ K2 = C2 ∧
      Measure.map K2 witnessLaw = torusWitnessLaw ∧
      Measure.map K2 comparatorLaw = torusComparatorLaw ∧
      Measure.map PsiA2 torusWitnessLaw = volume.withDensity (fun x => ENNReal.ofReal (Fw x)) ∧
      Measure.map PsiA2 torusComparatorLaw = volume.withDensity (fun x => ENNReal.ofReal (Fc x)) ∧
      Integrable (fun z => densityA z * log (densityA z)) torusFullBase ∧
      Integrable (fun z => comparatorDensityA z * log (comparatorDensityA z)) torusFullBase ∧
      (∫ z, densityA z * log (densityA z) ∂torusFullBase) = (∫ x, Fw x * log (Fw x)) ∧
      (∫ z, comparatorDensityA z * log (comparatorDensityA z) ∂torusFullBase) = (∫ x, Fc x * log (Fc x)) ∧
      0 ≤ -(∫ z, densityA z * log (densityA z) ∂torusFullBase) ∧
      0 ≤ -(∫ z, comparatorDensityA z * log (comparatorDensityA z) ∂torusFullBase) := by
    have hm : (volume : Measure Real.Angle) univ = ENNReal.ofReal (2 * π) := AddCircle.measure_univ (2 * π)
    have hangle : MeasurePreserving (fun t : ℝ => (t : Real.Angle)) angle volume := by
      have hi : -π + 2 * π = π := by ring
      convert AddCircle.measurePreserving_mk (2 * π) (-π) using 1 <;> (try simp only [hi]) <;> rfl
    have hK : MeasurePreserving K base torusBase := hangle.prod (MeasurePreserving.id action); have hK2 : MeasurePreserving K2 fullBase torusFullBase := hK.prod hK
    have hphi : ∀ t : ℝ, phiA (t : Real.Angle) = phi t := by intro t; unfold phiA phi; rw [← Real.Angle.coe_nsmul, Real.Angle.cos_coe]; simp only [nsmul_eq_mul, Nat.cast_ofNat]
    have hw : ∀ z, densityA (K2 z) = fullDensity z := by intro z; simp only [densityA, K2, Prod.map, K, oneDensityA, fullDensity, oneDensity, hphi]
    have hc : ∀ z, comparatorDensityA (K2 z) = comparatorDensity z := by intro z; rfl
    have hPsi : PsiA2 ∘ K2 = C2 := by funext z; simp only [Function.comp_def, PsiA2, K2, C2, Prod.map, K, PsiA, cartesian, q, p, Real.Angle.sin_coe, Real.Angle.cos_coe]
    have hp : Measurable PsiA := by
      exact ((Real.continuous_sqrt.comp (continuous_const.mul continuous_snd)).mul (Real.Angle.continuous_sin.comp continuous_fst)).measurable.prodMk
        ((Real.continuous_sqrt.comp (continuous_const.mul continuous_snd)).mul
        (Real.Angle.continuous_cos.comp continuous_fst)).measurable
    have hp2 : Measurable PsiA2 := hp.prodMap hp
    have hmphi : Measurable phiA := by unfold phiA; exact ((measurable_const.add ((Real.Angle.continuous_cos.comp (continuous_id.nsmul 2)).measurable.div_const 2)).div_const (2*π))
    have hmw : Measurable densityA := by
      have h1 : Measurable oneDensityA := (hmphi.comp measurable_fst).mul (Real.measurable_exp.comp measurable_snd.neg); exact (h1.comp measurable_fst).mul (h1.comp measurable_snd)
    have hmc : Measurable comparatorDensityA := by unfold comparatorDensityA comparatorOneDensityA; fun_prop
    have hmD : Measurable fullDensity := by unfold fullDensity oneDensity phi; fun_prop
    have hmDc : Measurable comparatorDensity := by unfold comparatorDensity comparatorOneDensity uniformPhase; fun_prop
    have hpush : ∀ (D : CartesianTwo → ℝ) (F : TorusTwo → ℝ), Measurable D → Measurable F → (∀ z, F (K2 z) = D z) → Measure.map K2 (fullBase.withDensity (fun z => ENNReal.ofReal (D z))) =
          torusFullBase.withDensity (fun z => ENNReal.ofReal (F z)) := by
      intro D F hD hF hDF; apply Measure.ext_of_lintegral; intro g hg; rw [lintegral_map hg hK2.measurable]; change (∫⁻ z, (g ∘ K2) z ∂fullBase.withDensity (fun z => ENNReal.ofReal (D z))) = _
      rw [lintegral_withDensity_eq_lintegral_mul fullBase hD.ennreal_ofReal (hg.comp hK2.measurable), lintegral_withDensity_eq_lintegral_mul torusFullBase hF.ennreal_ofReal hg]
      calc
        _ = ∫⁻ z, ENNReal.ofReal (F (K2 z)) * g (K2 z) ∂fullBase := by simp only [Pi.mul_apply, Function.comp_def, hDF]
        _ = ∫⁻ z, ENNReal.ofReal (F z) * g z ∂torusFullBase := by rw [← hK2.map_eq]; simpa only [Pi.mul_apply, Function.comp_def] using (lintegral_map (hF.ennreal_ofReal.mul hg) hK2.measurable).symm
    have hwmap : Measure.map K2 witnessLaw = torusWitnessLaw := hpush fullDensity densityA hmD hmw hw
    have hcmap : Measure.map K2 comparatorLaw = torusComparatorLaw := hpush comparatorDensity comparatorDensityA hmDc hmc hc
    obtain ⟨_, _, _, _, hcw, hcc, _, _, hew, hec⟩ := actual_cartesian_weighted_and_entropy_transport
    have hcartw : Measure.map PsiA2 torusWitnessLaw = volume.withDensity (fun x => ENNReal.ofReal (Fw x)) := by rw [← hwmap, Measure.map_map hp2 hK2.measurable, hPsi]; exact hcw
    have hcartc : Measure.map PsiA2 torusComparatorLaw = volume.withDensity (fun x => ENNReal.ofReal (Fc x)) := by rw [← hcmap, Measure.map_map hp2 hK2.measurable, hPsi]; exact hcc
    have hmeW : Measurable (fun z => densityA z * log (densityA z)) := hmw.mul hmw.log; have hmeC : Measurable (fun z => comparatorDensityA z * log (comparatorDensityA z)) := hmc.mul hmc.log
    have hiw : Integrable (fun z => densityA z * log (densityA z)) torusFullBase := by
      rw [← hK2.map_eq]; apply (integrable_map_measure hmeW.aestronglyMeasurable hK2.measurable.aemeasurable).mpr; simpa only [Function.comp_def, hw] using full_entropy_integrable
    have hic : Integrable (fun z => comparatorDensityA z * log (comparatorDensityA z)) torusFullBase := by
      rw [← hK2.map_eq]; apply (integrable_map_measure hmeC.aestronglyMeasurable hK2.measurable.aemeasurable).mpr; simpa only [Function.comp_def, hc] using comparator_entropy_integrable
    have hEW : (∫ z, densityA z * log (densityA z) ∂torusFullBase) = (∫ z, fullDensity z * log (fullDensity z) ∂fullBase) := by
      rw [← hK2.map_eq, integral_map hK2.measurable.aemeasurable hmeW.aestronglyMeasurable]; simp only [hw]
    have hEC : (∫ z, comparatorDensityA z * log (comparatorDensityA z) ∂torusFullBase) = (∫ z, comparatorDensity z * log (comparatorDensity z) ∂fullBase) := by
      rw [← hK2.map_eq, integral_map hK2.measurable.aemeasurable hmeC.aestronglyMeasurable]; simp only [hc]
    refine ⟨hm, hK2, hw, hc, hPsi, hwmap, hcmap, hcartw, hcartc, hiw, hic, hEW.trans hew.symm, hEC.trans hec.symm, ?_, ?_⟩
    · rw [hEW]; exact full_entropy_nonneg
    · rw [hEC]; exact comparator_entropy_nonneg
  have common_action_bridge : Measure.map actionProjection torusWitnessLaw = commonActionLaw ∧ Measure.map actionProjection torusComparatorLaw = commonActionLaw ∧
      Measure.map radialAction (volume.withDensity (fun x => ENNReal.ofReal (Fw x))) = commonActionLaw ∧
      Measure.map radialAction (volume.withDensity (fun x => ENNReal.ofReal (Fc x))) = commonActionLaw ∧
      IsProbabilityMeasure torusWitnessLaw ∧ IsProbabilityMeasure torusComparatorLaw ∧
      IsProbabilityMeasure commonActionLaw := by
    let radialLaw : Measure ℝ := action.withDensity (fun J => ENNReal.ofReal (exp (-J)))
    have hrad : Measurable (fun J : ℝ => ENNReal.ofReal (exp (-J))) := by fun_prop
    have hfull : radialLaw.prod radialLaw = commonActionLaw := by rw [prod_withDensity hrad hrad]; congr 1; funext J; rw [← ENNReal.ofReal_mul (le_of_lt (exp_pos _)), ← exp_add]; congr 1; ring
    have hfactor : ∀ (f : ℝ → ℝ), Measurable f → (∀ t, 0 ≤ f t) → (angle.withDensity (fun t => ENNReal.ofReal (f t))).prod radialLaw =
          base.withDensity (fun z => ENNReal.ofReal (f z.1 * exp (-z.2))) := by
      intro f hf hnf; rw [prod_withDensity hf.ennreal_ofReal hrad]; congr 1; funext z; exact (ENNReal.ofReal_mul (hnf z.1)).symm
    have hpair : ∀ (D : (ℝ × ℝ) → ℝ), Measurable D → (∀ z, 0 ≤ D z) → (base.withDensity (fun z => ENNReal.ofReal (D z))).prod (base.withDensity (fun z => ENNReal.ofReal (D z))) =
        fullBase.withDensity (fun z => ENNReal.ofReal (D z.1 * D z.2)) := by
      intro D hD hnD; rw [prod_withDensity hD.ennreal_ofReal hD.ennreal_ofReal]; congr 1; funext z; exact (ENNReal.ofReal_mul (hnD z.1)).symm
    have hmassW : (angle.withDensity (fun t => ENNReal.ofReal (phi t))) univ = 1 := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal phi_integrable (ae_of_all _ phi_nonneg), phi_mass]; norm_num
    have hmassC : (angle.withDensity (fun t => ENNReal.ofReal (uniformPhase t))) univ = 1 := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
          (continuous_angle_integrable uniform_cont) (ae_of_all _ (fun t => (uniform_pos t).le)), uniform_mass]
      norm_num
    have hW1 : Measure.map Prod.snd (base.withDensity (fun z => ENNReal.ofReal (oneDensity z))) = radialLaw := by
      unfold oneDensity; rw [← hfactor phi phi_cont.measurable phi_nonneg, Measure.map_snd_prod, hmassW, one_smul]
    have hC1 : Measure.map Prod.snd (base.withDensity (fun z => ENNReal.ofReal (comparatorOneDensity z))) = radialLaw := by
      unfold comparatorOneDensity; rw [← hfactor uniformPhase uniform_cont.measurable (fun t => (uniform_pos t).le), Measure.map_snd_prod, hmassC, one_smul]
    have hmOne : Measurable oneDensity := by unfold oneDensity phi; fun_prop
    have hmComp : Measurable comparatorOneDensity := by unfold comparatorOneDensity uniformPhase; fun_prop
    have hnOne : ∀ z, 0 ≤ oneDensity z := fun z => (one_pos z).le; have hnComp : ∀ z, 0 ≤ comparatorOneDensity z := fun z => (comparator_one_pos z).le
    have hwchart : Measure.map chartActionProjection witnessLaw = commonActionLaw := by
      change Measure.map (Prod.map Prod.snd Prod.snd) (fullBase.withDensity (fun z => ENNReal.ofReal (oneDensity z.1 * oneDensity z.2))) = _
      rw [← hpair oneDensity hmOne hnOne, ← Measure.map_prod_map _ _ measurable_snd measurable_snd, hW1, hfull]
    have hcchart : Measure.map chartActionProjection comparatorLaw = commonActionLaw := by
      change Measure.map (Prod.map Prod.snd Prod.snd) (fullBase.withDensity (fun z => ENNReal.ofReal (comparatorOneDensity z.1 * comparatorOneDensity z.2))) = _
      rw [← hpair comparatorOneDensity hmComp hnComp, ← Measure.map_prod_map _ _ measurable_snd measurable_snd, hC1, hfull]
    obtain ⟨_, hK2, _, _, _, hwK, hcK, _, _, _⟩ := quotient_weighted_bridge; have hap : Measurable actionProjection := measurable_snd.comp measurable_fst |>.prodMk (measurable_snd.comp measurable_snd)
    have hcap : Measurable chartActionProjection := measurable_snd.comp measurable_fst |>.prodMk (measurable_snd.comp measurable_snd)
    have hwA : Measure.map actionProjection torusWitnessLaw = commonActionLaw := by rw [← hwK, Measure.map_map hap hK2.measurable]; exact hwchart
    have hcA : Measure.map actionProjection torusComparatorLaw = commonActionLaw := by rw [← hcK, Measure.map_map hap hK2.measurable]; exact hcchart
    have hlocal : ∀ z : ℝ × ℝ, 0 ≤ z.2 → R2 (cartesian z) / 2 = z.2 := by
      intro z hz
      have hs : sqrt (2 * z.2) ^ 2 = 2 * z.2 := sq_sqrt (by positivity)
      unfold R2 cartesian q p; simp only [mul_pow, hs]; rw [← mul_add, sin_sq_add_cos_sq, mul_one]; ring
    have hAE : (radialAction ∘ C2) =ᵐ[fullBase] chartActionProjection := by filter_upwards [full_positive_actions_ae] with z hz; exact Prod.ext (hlocal z.1 hz.1.le) (hlocal z.2 hz.2.le)
    have hAEw : (radialAction ∘ C2) =ᵐ[witnessLaw] chartActionProjection := (withDensity_absolutelyContinuous _ _).ae_eq hAE
    have hAEc : (radialAction ∘ C2) =ᵐ[comparatorLaw] chartActionProjection := (withDensity_absolutelyContinuous _ _).ae_eq hAE
    have hR : Measurable radialAction := by unfold radialAction R2; fun_prop
    have hC : Measurable C2 := cartesian_measurable.prodMap cartesian_measurable; obtain ⟨_, _, _, _, hwCart, hcCart, _⟩ := actual_cartesian_weighted_and_entropy_transport
    have hwR : Measure.map radialAction (volume.withDensity (fun x => ENNReal.ofReal (Fw x))) = commonActionLaw := by
      rw [← hwCart]; change Measure.map radialAction (Measure.map C2 witnessLaw) = _; rw [Measure.map_map hR hC, Measure.map_congr hAEw]; exact hwchart
    have hcR : Measure.map radialAction (volume.withDensity (fun x => ENNReal.ofReal (Fc x))) = commonActionLaw := by
      rw [← hcCart]; change Measure.map radialAction (Measure.map C2 comparatorLaw) = _; rw [Measure.map_map hR hC, Measure.map_congr hAEc]; exact hcchart
    let : IsProbabilityMeasure witnessLaw := witness_probability; let : IsProbabilityMeasure comparatorLaw := comparator_probability
    have hpW : IsProbabilityMeasure torusWitnessLaw := by rw [← hwK]; exact Measure.isProbabilityMeasure_map hK2.measurable.aemeasurable
    have hpC : IsProbabilityMeasure torusComparatorLaw := by rw [← hcK]; exact Measure.isProbabilityMeasure_map hK2.measurable.aemeasurable
    have hpA : IsProbabilityMeasure commonActionLaw := by rw [← hwchart]; exact Measure.isProbabilityMeasure_map hcap.aemeasurable
    exact ⟨hwA, hcA, hwR, hcR, hpW, hpC, hpA⟩
  have torus_fibers_and_source_entropy : (∀ J₁ J₂ : ℝ, (∫ ts : Real.Angle × Real.Angle, densityA ((ts.1, J₁), (ts.2, J₂))) = exp (-(J₁ + J₂))) ∧ (∀ J₁ J₂ : ℝ, (∫ ts : Real.Angle × Real.Angle,
        comparatorDensityA ((ts.1, J₁), (ts.2, J₂))) = exp (-(J₁ + J₂))) ∧
      (∀ z : TorusTwo, comparatorDensityA z = exp (-(z.1.2 + z.2.2)) / (2 * π)^2) ∧
      Integrable (fun x => Fw x * log (Fw x)) volume ∧
      Integrable (fun x => Fc x * log (Fc x)) volume ∧
      0 ≤ -(∫ x, Fw x * log (Fw x)) ∧
      0 ≤ -(∫ x, Fc x * log (Fc x)) := by
    have hangle : MeasurePreserving (fun t : ℝ => (t : Real.Angle)) angle volume := by
      have hi : -π + 2 * π = π := by ring
      convert AddCircle.measurePreserving_mk (2 * π) (-π) using 1 <;> (try simp only [hi]) <;> rfl
    have hpair := hangle.prod hangle
    have hphi : ∀ t : ℝ, phiA (t : Real.Angle) = phi t := by intro t; unfold phiA phi; rw [← Real.Angle.coe_nsmul, Real.Angle.cos_coe]; simp only [nsmul_eq_mul, Nat.cast_ofNat]
    have hcont : Continuous phiA := by unfold phiA; exact (continuous_const.add ((Real.Angle.continuous_cos.comp (continuous_id.nsmul 2)).div_const 2)).div_const (2 * π)
    have hw : ∀ J₁ J₂ : ℝ, (∫ ts : Real.Angle × Real.Angle, densityA ((ts.1, J₁), (ts.2, J₂))) = exp (-(J₁ + J₂)) := by
      intro J₁ J₂
      have hmf : Measurable (fun ts : Real.Angle × Real.Angle => densityA ((ts.1, J₁), (ts.2, J₂))) := by
        unfold densityA oneDensityA; change Measurable (fun ts : Real.Angle × Real.Angle => (phiA ts.1 * exp (-J₁)) * (phiA ts.2 * exp (-J₂)))
        exact ((hcont.measurable.comp measurable_fst).mul_const (exp (-J₁))).mul ((hcont.measurable.comp measurable_snd).mul_const (exp (-J₂)))
      change (∫ ts : Real.Angle × Real.Angle, _ ∂(volume : Measure Real.Angle).prod volume) = _; rw [← hpair.map_eq, integral_map hpair.measurable.aemeasurable hmf.aestronglyMeasurable]
      simpa only [Prod.map, densityA, oneDensityA, hphi, fullDensity, oneDensity] using exact_action_marginal J₁ J₂
    have hc : ∀ J₁ J₂ : ℝ, (∫ ts : Real.Angle × Real.Angle, comparatorDensityA ((ts.1, J₁), (ts.2, J₂))) = exp (-(J₁ + J₂)) := by
      intro J₁ J₂
      have hmf : Measurable (fun ts : Real.Angle × Real.Angle => comparatorDensityA ((ts.1, J₁), (ts.2, J₂))) := by
        unfold comparatorDensityA comparatorOneDensityA; change Measurable (fun _ : Real.Angle × Real.Angle => (1 / (2 * π) * exp (-J₁)) * (1 / (2 * π) * exp (-J₂))); exact measurable_const
      change (∫ ts : Real.Angle × Real.Angle, _ ∂(volume : Measure Real.Angle).prod volume) = _; rw [← hpair.map_eq, integral_map hpair.measurable.aemeasurable hmf.aestronglyMeasurable]
      exact comparator_action_marginal J₁ J₂
    have hproduct : ∀ z : TorusTwo, comparatorDensityA z = exp (-(z.1.2 + z.2.2)) / (2 * π)^2 := by
      intro z; unfold comparatorDensityA comparatorOneDensityA; rw [show -(z.1.2 + z.2.2) = -z.1.2 + -z.2.2 by ring, exp_add]; ring
    obtain ⟨_, _, _, _, _, _, hiw, hic, hew, hec⟩ := actual_cartesian_weighted_and_entropy_transport; refine ⟨hw, hc, hproduct, hiw, hic, ?_, ?_⟩
    · rw [hew]; exact full_entropy_nonneg
    · rw [hec]; exact comparator_entropy_nonneg
  obtain ⟨mW,mC,nW,nC,_,_,iW,iC,_,_⟩ := actual_cartesian_weighted_and_entropy_transport; obtain ⟨_,_,probW,probC,lpW,lpC,_,_,pdW,pdC,valW,valC,strictWC,_,_,_,_⟩ := transient_actual_covariance_evidence
  obtain ⟨massAngle,hK2,descW,descC,hPsi,_,_,mapW,mapC,iTW,iTC,eTW,eTC,_,_⟩ := quotient_weighted_bridge; obtain ⟨actTW,actTC,actW,actC,_,_,probA⟩ := common_action_bridge
  obtain ⟨fiberW,fiberC,uniformC,_,_,entW,entC⟩ := torus_fibers_and_source_entropy
  have hlocal : ∀ z : ℝ × ℝ, 0 < z.2 → rho_w (cartesian z) = oneDensity z ∧ rho_c (cartesian z) = comparatorOneDensity z := by
    intro z hz
    have hs : sqrt (2*z.2)^2 = 2*z.2 := sq_sqrt (by positivity)
    have hq : (cartesian z).1^2 = (2*z.2) * sin z.1 ^ 2 := by simp only [cartesian, q, mul_pow]; rw [hs]
    have hp : (cartesian z).2^2 = (2*z.2) * cos z.1 ^ 2 := by simp only [cartesian, p, mul_pow]; rw [hs]
    have hr : R2 (cartesian z) = 2*z.2 := by unfold R2; rw [hq, hp, ← mul_add, sin_sq_add_cos_sq, mul_one]
    have ha : (1 + ((cartesian z).2^2-(cartesian z).1^2)/(2*R2 (cartesian z)))/(2*π) = phi z.1 := by rw [hq, hp, hr]; unfold phi; rw [cos_two_mul']; field_simp [ne_of_gt hz]
    rw [hr] at ha; constructor
    · unfold rho_w
      rw [if_neg (by rw [hr]; positivity), hr]
      have he : -(2*z.2)/2 = -z.2 := by ring
      rw [he]; unfold oneDensity; rw [mul_div_assoc, ha]; ring
    · unfold rho_c comparatorOneDensity uniformPhase
      rw [hr]; congr 1 <;> ring
  have hTlocal (z : TorusTwo) (hz : 0 < z.1.2 ∧ 0 < z.2.2) : sourcePullback Fw z = densityA z ∧ sourcePullback Fc z = comparatorDensityA z := by
    obtain ⟨t₁, ht₁⟩ := QuotientAddGroup.mk_surjective z.1.1; obtain ⟨t₂, ht₂⟩ := QuotientAddGroup.mk_surjective z.2.1; let a : CartesianTwo := ((t₁,z.1.2),(t₂,z.2.2))
    have ha : K2 a = z := by
      apply Prod.ext <;> apply Prod.ext
      · exact ht₁
      · rfl
      · exact ht₂
      · rfl
    have hca : PsiA2 (K2 a) = C2 a := congrFun hPsi a; rw [← ha, sourcePullback, sourcePullback, hca, descW, descC]; constructor
    · simp only [Fw, C2, Prod.map, fullDensity, a,
        (hlocal (t₁,z.1.2) hz.1).1, (hlocal (t₂,z.2.2) hz.2).1]
    · simp only [Fc, C2, Prod.map, comparatorDensity, a,
        (hlocal (t₁,z.1.2) hz.1).2, (hlocal (t₂,z.2.2) hz.2).2]
  have posT : ∀ᵐ z : TorusTwo ∂torusFullBase, 0 < z.1.2 ∧ 0 < z.2.2 := by
    rw [← hK2.map_eq]; apply (ae_map_iff hK2.measurable.aemeasurable (by measurability)).mpr; simpa only [K2,K,Prod.map] using full_positive_actions_ae
  have pullW : sourcePullback Fw =ᵐ[torusFullBase] densityA := posT.mono fun z hz => (hTlocal z hz).1
  have pullC : sourcePullback Fc =ᵐ[torusFullBase] comparatorDensityA := posT.mono fun z hz => (hTlocal z hz).2
  have lawTW : sourceTorusLaw Fw = torusWitnessLaw := withDensity_congr_ae (pullW.fun_comp ENNReal.ofReal)
  have lawTC : sourceTorusLaw Fc = torusComparatorLaw := withDensity_congr_ae (pullC.fun_comp ENNReal.ofReal)
  have entropyPullW : (fun z => sourcePullback Fw z * log (sourcePullback Fw z)) =ᵐ[torusFullBase] (fun z => densityA z * log (densityA z)) := by filter_upwards [pullW] with z hz; rw [hz]
  have entropyPullC : (fun z => sourcePullback Fc z * log (sourcePullback Fc z)) =ᵐ[torusFullBase] (fun z => comparatorDensityA z * log (comparatorDensityA z)) := by
    filter_upwards [pullC] with z hz; rw [hz]
  have stateW : sourceState Fw := by
    refine ⟨mW,nW,probW,iW,lpW,pdW,iTW.congr entropyPullW.symm,?_,?_⟩
    · exact (integral_congr_ae entropyPullW).trans eTW
    · rw [lawTW]; exact mapW
  have stateC : sourceState Fc := by
    refine ⟨mC,nC,probC,iC,lpC,pdC,iTC.congr entropyPullC.symm,?_,?_⟩
    · exact (integral_congr_ae entropyPullC).trans eTC
    · rw [lawTC]; exact mapC
  let r : (ℝ × ℝ) → ℝ := fun J => exp (-(J.1+J.2))
  have ar : actionDensity r := by
    refine ⟨by dsimp [r]; fun_prop,fun J => (exp_pos _).le,?_⟩; have h := probA.measure_univ; change (action.prod action).withDensity (fun J => ENNReal.ofReal (r J)) univ = 1 at h
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  have posA : ∀ᵐ J : ℝ × ℝ ∂action.prod action, 0 < J.1 ∧ 0 < J.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr; exact (ae_restrict_mem measurableSet_Ioi).mono fun _ h₁ => (ae_restrict_mem measurableSet_Ioi).mono fun _ h₂ => ⟨h₁,h₂⟩
  have hphiA : Continuous phiA := by unfold phiA; exact (continuous_const.add ((Real.Angle.continuous_cos.comp (continuous_id.nsmul 2)).div_const 2)).div_const (2 * π)
  have iFiberW (J : ℝ × ℝ) : Integrable (fun ts : Real.Angle × Real.Angle => densityA ((ts.1,J.1),(ts.2,J.2))) volume := by
    have hc : Continuous (fun ts : Real.Angle × Real.Angle => densityA ((ts.1,J.1),(ts.2,J.2))) := by
      change Continuous (fun ts : Real.Angle × Real.Angle => (phiA ts.1 * exp (-J.1)) * (phiA ts.2 * exp (-J.2)))
      exact ((hphiA.comp continuous_fst).mul_const _).mul ((hphiA.comp continuous_snd).mul_const _)
    simpa only [IntegrableOn, Measure.restrict_univ] using hc.continuousOn.integrableOn_compact (μ := (volume : Measure (Real.Angle × Real.Angle))) isCompact_univ
  have iFiberC (J : ℝ × ℝ) : Integrable (fun ts : Real.Angle × Real.Angle => comparatorDensityA ((ts.1,J.1),(ts.2,J.2))) volume := by
    dsimp only [comparatorDensityA, comparatorOneDensityA]; exact integrable_const _
  have marginal : commonActionMarginal Fw Fc r := by
    refine ⟨?_,?_,?_,?_,actW,actC⟩
    · filter_upwards [posA] with J hJ
      refine ⟨?_,?_⟩
      · exact (iFiberW J).congr (ae_of_all _ (fun ts => (hTlocal ((ts.1,J.1),(ts.2,J.2)) hJ).1.symm))
      calc
        _ = ∫ ts : Real.Angle × Real.Angle, densityA ((ts.1,J.1),(ts.2,J.2)) := by apply integral_congr_ae; exact ae_of_all _ (fun ts => (hTlocal ((ts.1,J.1),(ts.2,J.2)) hJ).1)
        _ = r J := fiberW J.1 J.2
    · filter_upwards [posA] with J hJ
      refine ⟨?_,?_⟩
      · exact (iFiberC J).congr (ae_of_all _ (fun ts => (hTlocal ((ts.1,J.1),(ts.2,J.2)) hJ).2.symm))
      calc
        (∫ ts : Real.Angle × Real.Angle, sourcePullback Fc ((ts.1,J.1),(ts.2,J.2))) = ∫ ts : Real.Angle × Real.Angle, comparatorDensityA ((ts.1,J.1),(ts.2,J.2)) := by
          apply integral_congr_ae; exact ae_of_all _ (fun ts => (hTlocal ((ts.1,J.1),(ts.2,J.2)) hJ).2)
        _ = r J := fiberC J.1 J.2
    · rw [lawTW]; exact actTW
    · rw [lawTC]; exact actTC
  have uniform : phaseUniformProduct Fc r := by
    refine ⟨?_,fun J => exp (-J),fun J => exp (-J),?_,?_,?_⟩
    · exact pullC.trans (ae_of_all _ uniformC)
    · refine ⟨by fun_prop,fun J => (exp_pos _).le,?_⟩
      rw [← ofReal_integral_eq_lintegral_ofReal exp_integrable (ae_of_all _ (fun J => (exp_pos (-J)).le)),exp_mass]; norm_num
    · refine ⟨by fun_prop,fun J => (exp_pos _).le,?_⟩
      rw [← ofReal_integral_eq_lintegral_ofReal exp_integrable (ae_of_all _ (fun J => (exp_pos (-J)).le)),exp_mass]; norm_num
    · exact ae_of_all _ (fun J => by dsimp [r]; rw [← exp_add]; congr 1; ring)
  have bothStrict : ∀ j : Bool, sourceUncertainty Fw j < sourceUncertainty Fc j := strictWC; intro hminimum; have bound := hminimum 0 r Fw Fc ar stateW stateC marginal uniform entW entC
  have hstrict := add_lt_add (bothStrict false) (bothStrict true); have hreverse := add_le_add (bound false) (bound true); exact (not_le_of_gt hstrict) hreverse
end D5.S3.Quantum.Information.DinovOriginalMinimumRefutation
