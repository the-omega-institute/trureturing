import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
import Reg.Support.DependentFamily
import Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure

/-! Typed realization contracts for the positive definite function library. -/

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
open _root_.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
open _root_.Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
open scoped ComplexOrder
noncomputable section

abbrev deficitSignature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def deficitActual : Realization deficitSignature :=
  realize deficitSignature (fun _ g t => (Q g t : ℂ)) (fun e => nomatch e)

def deficitRejected : Realization deficitSignature :=
  realize deficitSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev deficitArena : Arena where
  signature := deficitSignature
  Law R := ∀ {g : ℝ → ℝ}, Function.Even g → ContDiff ℝ 2 g →
    PositiveDefinite (fun t => (g t : ℂ)) → PositiveDefinite (R.readout () g)

private theorem deficitRejectedLaw : ¬ deficitArena.Law deficitRejected := by
  intro h
  have hp := _root_.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.const (a := 0) le_rfl
  have H := (h (g := fun _ => 0) (fun _ => rfl) contDiff_const hp 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num [deficitRejected, realize] at H

private theorem deficitDependence : ObservationalDependence deficitSignature deficitActual := by
  intro i
  refine ⟨(fun t => t ^ 4), 0, 1, ?_⟩
  have hd : deriv (fun t : ℝ => t ^ 4) = fun t => 4 * t ^ 3 := by
    funext t
    simpa using deriv_pow_field (𝕜 := ℝ) 4 t
  have hd2 : deriv (fun t : ℝ => 4 * t ^ 3) 0 = 0 := by
    rw [deriv_const_mul_field]
    norm_num [deriv_pow_field]
  norm_num [deficitActual, realize, Q, iteratedDeriv_succ, iteratedDeriv_zero, hd, hd2]

def deficitSource : Registration deficitArena (type_of% @Q_positiveDefinite) where
  actual := deficitActual
  bridge := Iff.rfl
  variation := ⟨Q_positiveDefinite, deficitRejected, deficitRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨deficitRejected, ?_, rfl, deficitRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := deficitDependence

def deficitAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Q_positiveDefinite) (Realization deficitSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.deficitUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.deficitSource
  realizationSource := none
  generated := false
  arena := .source ⟨deficitArena⟩
  objectArena := .source ⟨deficitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deficitArena ⟨deficitSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitSignature (fun _ g t => (Q g t : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms deficitAudit


abbrev translatedSignature : Signature where
  Params := Σ _ : (ℝ → ℂ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def translatedActual : Realization translatedSignature :=
  realize translatedSignature (fun _ p t => 2 * p.1 t - p.1 (t + p.2) - p.1 (t - p.2)) (fun e => nomatch e)

def translatedRejected : Realization translatedSignature :=
  realize translatedSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev translatedArena : Arena where
  signature := translatedSignature
  Law R := ∀ {f : ℝ → ℂ}, PositiveDefinite f → ∀ h : ℝ, PositiveDefinite (R.readout () ⟨f, h⟩)

private theorem translatedRejectedLaw : ¬ translatedArena.Law translatedRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD 0)

private theorem translatedDependence : ObservationalDependence translatedSignature translatedActual := by
  intro i
  refine ⟨⟨(fun t => ((t ^ 4 : ℝ) : ℂ)), 1⟩, 0, 1, ?_⟩
  norm_num [translatedActual, realize]

def translatedSource : Registration translatedArena (type_of% @difference) where
  actual := translatedActual
  bridge := Iff.rfl
  variation := ⟨difference, translatedRejected, translatedRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨translatedRejected, ?_, rfl, translatedRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := translatedDependence

def translatedAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@difference) (Realization translatedSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.translatedUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.translatedSource
  realizationSource := none
  generated := false
  arena := .source ⟨translatedArena⟩
  objectArena := .source ⟨translatedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source translatedArena ⟨translatedSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize translatedSignature (fun _ p t => 2 * p.1 t - p.1 (t + p.2) - p.1 (t - p.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms translatedAudit


abbrev curvatureSignature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def curvatureActual : Realization curvatureSignature :=
  realize curvatureSignature (fun _ g t => (-(iteratedDeriv 2 g t) : ℂ)) (fun e => nomatch e)

def curvatureRejected : Realization curvatureSignature :=
  realize curvatureSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev curvatureArena : Arena where
  signature := curvatureSignature
  Law R := ∀ {g : ℝ → ℝ}, ContDiff ℝ 2 g → PositiveDefinite (fun t => (g t : ℂ)) → PositiveDefinite (R.readout () g)

private theorem curvatureRejectedLaw : ¬ curvatureArena.Law curvatureRejected := by
  intro h
  exact negativeKernel_not_PD (h (g := fun _ => 0) contDiff_const zeroPD)

private theorem curvatureDependence : ObservationalDependence curvatureSignature curvatureActual := by
  intro i
  refine ⟨Real.cos, 0, Real.pi, ?_⟩
  have hd : deriv Real.cos = fun t => -Real.sin t := funext (fun t => Real.deriv_cos (x := t))
  have hd2 : deriv (fun t => -Real.sin t) = fun t => -Real.cos t := by
    funext t
    exact (Real.hasDerivAt_sin t).neg.deriv
  norm_num [curvatureActual, realize, iteratedDeriv_succ, iteratedDeriv_zero, hd, hd2]

def curvatureSource : Registration curvatureArena (type_of% @neg_second_deriv) where
  actual := curvatureActual
  bridge := Iff.rfl
  variation := ⟨neg_second_deriv, curvatureRejected, curvatureRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨curvatureRejected, ?_, rfl, curvatureRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := curvatureDependence

def curvatureAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neg_second_deriv) (Realization curvatureSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.curvatureUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.curvatureSource
  realizationSource := none
  generated := false
  arena := .source ⟨curvatureArena⟩
  objectArena := .source ⟨curvatureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source curvatureArena ⟨curvatureSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize curvatureSignature (fun _ g t => (-(iteratedDeriv 2 g t) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms curvatureAudit


abbrev deficitIntegralSignature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def deficitIntegralActual : Realization deficitIntegralSignature :=
  realize deficitIntegralSignature (fun _ g t => Q g t) (fun e => nomatch e)

def deficitIntegralRejected : Realization deficitIntegralSignature :=
  realize deficitIntegralSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev deficitIntegralArena : Arena where
  signature := deficitIntegralSignature
  Law R := ∀ {g : ℝ → ℝ}, Function.Even g → ContDiff ℝ 2 g → ∀ t : ℝ, R.readout () g t = ∫ u in (0 : ℝ)..1, (1 - u) * (-iteratedDeriv 2 g (u * t))

private theorem deficitIntegralRejectedLaw : ¬ deficitIntegralArena.Law deficitIntegralRejected := by
  intro h
  have H := h (g := fun _ => 0) (fun _ => rfl) contDiff_const 0
  norm_num [deficitIntegralRejected, realize, iteratedDeriv_succ, iteratedDeriv_zero] at H

private theorem deficitIntegralDependence : ObservationalDependence deficitIntegralSignature deficitIntegralActual := by
  intro i
  refine ⟨(fun t => t ^ 4), 0, 1, ?_⟩
  have hd : deriv (fun t : ℝ => t ^ 4) = fun t => 4 * t ^ 3 := by
    funext t
    simpa using deriv_pow_field (𝕜 := ℝ) 4 t
  have hd2 : deriv (fun t : ℝ => 4 * t ^ 3) 0 = 0 := by
    rw [deriv_const_mul_field]
    norm_num [deriv_pow_field]
  norm_num [deficitIntegralActual, realize, Q, iteratedDeriv_succ, iteratedDeriv_zero, hd, hd2]

def deficitIntegralSource : Registration deficitIntegralArena (type_of% @Q_integral) where
  actual := deficitIntegralActual
  bridge := Iff.rfl
  variation := ⟨Q_integral, deficitIntegralRejected, deficitIntegralRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨deficitIntegralRejected, ?_, rfl, deficitIntegralRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := deficitIntegralDependence

def deficitIntegralAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Q_integral) (Realization deficitIntegralSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.deficitIntegralUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference.deficitIntegralSource
  realizationSource := none
  generated := false
  arena := .source ⟨deficitIntegralArena⟩
  objectArena := .source ⟨deficitIntegralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deficitIntegralArena ⟨deficitIntegralSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitIntegralSignature (fun _ g t => Q g t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms deficitIntegralAudit
end
end Reg.D5.S3.Analytic.Fourier.PositiveDefinite.SecondDifference
