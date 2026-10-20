import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import Reg.Support.DependentFamily

/-! Typed realization contracts for the positive definite function library. -/

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
open _root_.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
open Filter MeasureTheory
open scoped ComplexOrder Topology BigOperators
noncomputable section
universe u

abbrev cosineSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def cosineActual : Realization cosineSignature :=
  realize cosineSignature (fun _ s t => (Real.cos (s * t) : ℂ)) (fun e => nomatch e)

def cosineRejected : Realization cosineSignature :=
  realize cosineSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev cosineArena : Arena where
  signature := cosineSignature
  Law R := ∀ s, PositiveDefinite (R.readout () s)

private theorem cosineRejectedLaw : ¬ cosineArena.Law cosineRejected := by
  intro h
  have H := (h 0 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num [cosineRejected, realize] at H

private theorem cosineDependence : ObservationalDependence cosineSignature cosineActual := by
  intro i
  refine ⟨1, 0, Real.pi, ?_⟩
  norm_num [cosineActual, realize]

def cosineSource : Registration cosineArena (type_of% @cos) where
  actual := cosineActual
  bridge := Iff.rfl
  variation := ⟨cos, cosineRejected, cosineRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cosineRejected, ?_, rfl, cosineRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := cosineDependence

def cosineAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cos) (Realization cosineSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.cosineUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.cosineSource
  realizationSource := none
  generated := false
  arena := .source ⟨cosineArena⟩
  objectArena := .source ⟨cosineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cosineArena ⟨cosineSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cosineSignature (fun _ s t => (Real.cos (s * t) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cosineAudit

theorem zeroPD : PositiveDefinite (fun _ => (0 : ℂ)) :=
  fun _ _ => Matrix.PosSemidef.zero

theorem negativeKernel_not_PD : ¬ PositiveDefinite (fun _ => (-1 : ℂ)) := by
  intro h
  have H := (h 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num at H


abbrev scalingSignature : Signature where
  Params := Σ _ : (ℝ → ℂ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalingActual : Realization scalingSignature :=
  realize scalingSignature (fun _ p t => (p.2 : ℂ) * p.1 t) (fun e => nomatch e)

def scalingRejected : Realization scalingSignature :=
  realize scalingSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev scalingArena : Arena where
  signature := scalingSignature
  Law R := ∀ {f : ℝ → ℂ}, PositiveDefinite f → ∀ {a : ℝ}, 0 ≤ a → PositiveDefinite (R.readout () ⟨f, a⟩)

private theorem scalingRejectedLaw : ¬ scalingArena.Law scalingRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD (a := 1) (by norm_num))

private theorem scalingDependence : ObservationalDependence scalingSignature scalingActual := by
  intro i
  refine ⟨⟨(fun t => (Real.cos t : ℂ)), 1⟩, 0, Real.pi, ?_⟩
  norm_num [scalingActual, realize]

def scalingSource : Registration scalingArena (type_of% @smul) where
  actual := scalingActual
  bridge := Iff.rfl
  variation := ⟨smul, scalingRejected, scalingRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalingRejected, ?_, rfl, scalingRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := scalingDependence

def scalingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smul) (Realization scalingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.scalingUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.scalingSource
  realizationSource := none
  generated := false
  arena := .source ⟨scalingArena⟩
  objectArena := .source ⟨scalingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scalingArena ⟨scalingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalingSignature (fun _ p t => (p.2 : ℂ) * p.1 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scalingAudit


abbrev productSignature : Signature where
  Params := Σ _ : (ℝ → ℂ), (ℝ → ℂ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def productActual : Realization productSignature :=
  realize productSignature (fun _ p t => p.1 t * p.2 t) (fun e => nomatch e)

def productRejected : Realization productSignature :=
  realize productSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := productSignature
  Law R := ∀ {f g : ℝ → ℂ}, PositiveDefinite f → PositiveDefinite g → PositiveDefinite (R.readout () ⟨f, g⟩)

private theorem productRejectedLaw : ¬ productArena.Law productRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD zeroPD)

private theorem productDependence : ObservationalDependence productSignature productActual := by
  intro i
  refine ⟨⟨(fun t => (Real.cos t : ℂ)), (fun _ => 1)⟩, 0, Real.pi, ?_⟩
  norm_num [productActual, realize]

def productSource : Registration productArena (type_of% @mul) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨mul, productRejected, productRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨productRejected, ?_, rfl, productRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := productDependence

def productAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mul) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.productUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.productSource
  realizationSource := none
  generated := false
  arena := .source ⟨productArena⟩
  objectArena := .source ⟨productArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena ⟨productSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize productSignature (fun _ p t => p.1 t * p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms productAudit


abbrev dilatingSignature : Signature where
  Params := Σ _ : (ℝ → ℂ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def dilatingActual : Realization dilatingSignature :=
  realize dilatingSignature (fun _ p t => p.1 (p.2 * t)) (fun e => nomatch e)

def dilatingRejected : Realization dilatingSignature :=
  realize dilatingSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev dilatingArena : Arena where
  signature := dilatingSignature
  Law R := ∀ {f : ℝ → ℂ}, PositiveDefinite f → ∀ a : ℝ, PositiveDefinite (R.readout () ⟨f, a⟩)

private theorem dilatingRejectedLaw : ¬ dilatingArena.Law dilatingRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD 1)

private theorem dilatingDependence : ObservationalDependence dilatingSignature dilatingActual := by
  intro i
  refine ⟨⟨(fun t => (Real.cos t : ℂ)), 1⟩, 0, Real.pi, ?_⟩
  norm_num [dilatingActual, realize]

def dilatingSource : Registration dilatingArena (type_of% @dilation) where
  actual := dilatingActual
  bridge := Iff.rfl
  variation := ⟨dilation, dilatingRejected, dilatingRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨dilatingRejected, ?_, rfl, dilatingRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dilatingDependence

def dilatingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dilation) (Realization dilatingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.dilatingUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.dilatingSource
  realizationSource := none
  generated := false
  arena := .source ⟨dilatingArena⟩
  objectArena := .source ⟨dilatingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dilatingArena ⟨dilatingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dilatingSignature (fun _ p t => p.1 (p.2 * t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
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

#print axioms dilatingAudit


abbrev naturalPowerSignature : Signature where
  Params := Σ _ : (ℝ → ℂ), ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def naturalPowerActual : Realization naturalPowerSignature :=
  realize naturalPowerSignature (fun _ p t => p.1 t ^ p.2) (fun e => nomatch e)

def naturalPowerRejected : Realization naturalPowerSignature :=
  realize naturalPowerSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev naturalPowerArena : Arena where
  signature := naturalPowerSignature
  Law R := ∀ {f : ℝ → ℂ}, PositiveDefinite f → ∀ n : ℕ, PositiveDefinite (R.readout () ⟨f, n⟩)

private theorem naturalPowerRejectedLaw : ¬ naturalPowerArena.Law naturalPowerRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD 1)

private theorem naturalPowerDependence : ObservationalDependence naturalPowerSignature naturalPowerActual := by
  intro i
  refine ⟨⟨(fun t => (Real.cos t : ℂ)), 1⟩, 0, Real.pi, ?_⟩
  norm_num [naturalPowerActual, realize]

def naturalPowerSource : Registration naturalPowerArena (type_of% @pow) where
  actual := naturalPowerActual
  bridge := Iff.rfl
  variation := ⟨pow, naturalPowerRejected, naturalPowerRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨naturalPowerRejected, ?_, rfl, naturalPowerRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := naturalPowerDependence

def naturalPowerAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pow) (Realization naturalPowerSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.naturalPowerUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.naturalPowerSource
  realizationSource := none
  generated := false
  arena := .source ⟨naturalPowerArena⟩
  objectArena := .source ⟨naturalPowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source naturalPowerArena ⟨naturalPowerSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize naturalPowerSignature (fun _ p t => p.1 t ^ p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
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

#print axioms naturalPowerAudit


abbrev exponentiatingSignature : Signature where
  Params := ℝ → ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def exponentiatingActual : Realization exponentiatingSignature :=
  realize exponentiatingSignature (fun _ f t => Complex.exp (f t)) (fun e => nomatch e)

def exponentiatingRejected : Realization exponentiatingSignature :=
  realize exponentiatingSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev exponentiatingArena : Arena where
  signature := exponentiatingSignature
  Law R := ∀ {f : ℝ → ℂ}, PositiveDefinite f → PositiveDefinite (R.readout () f)

private theorem exponentiatingRejectedLaw : ¬ exponentiatingArena.Law exponentiatingRejected := by
  intro h
  exact negativeKernel_not_PD (h zeroPD)

private theorem exponentiatingDependence : ObservationalDependence exponentiatingSignature exponentiatingActual := by
  intro i
  refine ⟨(fun t => (Real.cos t : ℂ)), 0, Real.pi, ?_⟩
  intro h
  have H := congrArg Complex.re h
  have hh : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  norm_num [exponentiatingActual, realize, ← Complex.ofReal_exp] at H
  norm_num [Complex.exp_re] at H

def exponentiatingSource : Registration exponentiatingArena (type_of% @exp) where
  actual := exponentiatingActual
  bridge := Iff.rfl
  variation := ⟨exp, exponentiatingRejected, exponentiatingRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exponentiatingRejected, ?_, rfl, exponentiatingRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := exponentiatingDependence

def exponentiatingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exp) (Realization exponentiatingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.exponentiatingUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.exponentiatingSource
  realizationSource := none
  generated := false
  arena := .source ⟨exponentiatingArena⟩
  objectArena := .source ⟨exponentiatingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exponentiatingArena ⟨exponentiatingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize exponentiatingSignature (fun _ f t => Complex.exp (f t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exponentiatingAudit


abbrev constantSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def constantActual : Realization constantSignature :=
  realize constantSignature (fun _ _ a => (a : ℂ)) (fun e => nomatch e)

def constantRejected : Realization constantSignature :=
  realize constantSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev constantArena : Arena where
  signature := constantSignature
  Law R := ∀ {a : ℝ}, 0 ≤ a → PositiveDefinite (fun _ => R.readout () () a)

private theorem constantRejectedLaw : ¬ constantArena.Law constantRejected := by
  intro h
  exact negativeKernel_not_PD (h (a := 0) le_rfl)

private theorem constantDependence : ObservationalDependence constantSignature constantActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [constantActual, realize]

def constantSource : Registration constantArena (type_of% @const) where
  actual := constantActual
  bridge := Iff.rfl
  variation := ⟨const, constantRejected, constantRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨constantRejected, ?_, rfl, constantRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := constantDependence

def constantAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@const) (Realization constantSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.constantUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.constantSource
  realizationSource := none
  generated := false
  arena := .source ⟨constantArena⟩
  objectArena := .source ⟨constantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source constantArena ⟨constantSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize constantSignature (fun _ _ a => (a : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms constantAudit


abbrev unitarySignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def unitaryActual : Realization unitarySignature :=
  realize unitarySignature (fun _ s t => Complex.exp ((s * t : ℝ) * Complex.I)) (fun e => nomatch e)

def unitaryRejected : Realization unitarySignature :=
  realize unitarySignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev unitaryArena : Arena where
  signature := unitarySignature
  Law R := ∀ s : ℝ, PositiveDefinite (R.readout () s)

private theorem unitaryRejectedLaw : ¬ unitaryArena.Law unitaryRejected := by
  intro h
  exact negativeKernel_not_PD (h 0)

private theorem unitaryDependence : ObservationalDependence unitarySignature unitaryActual := by
  intro i
  refine ⟨1, 0, Real.pi, ?_⟩
  norm_num [unitaryActual, realize, Complex.exp_mul_I]

def unitarySource : Registration unitaryArena (type_of% @character) where
  actual := unitaryActual
  bridge := Iff.rfl
  variation := ⟨character, unitaryRejected, unitaryRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨unitaryRejected, ?_, rfl, unitaryRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := unitaryDependence

def unitaryAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@character) (Realization unitarySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.unitaryUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.unitarySource
  realizationSource := none
  generated := false
  arena := .source ⟨unitaryArena⟩
  objectArena := .source ⟨unitaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source unitaryArena ⟨unitarySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize unitarySignature (fun _ s t => Complex.exp ((s * t : ℝ) * Complex.I)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms unitaryAudit

abbrev limitingSignature : Signature where
  Params := ℝ → ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def limitingActual : Realization limitingSignature :=
  realize limitingSignature (fun _ g t => g t) (fun e => nomatch e)

def limitingRejected : Realization limitingSignature :=
  realize limitingSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev limitingArena : Arena where
  signature := limitingSignature
  Law R := ∀ {ι : Type u} {l : Filter ι} [l.NeBot] {f : ι → ℝ → ℂ} {g : ℝ → ℂ}, (∀ i, PositiveDefinite (f i)) → (∀ t, Filter.Tendsto (fun i => f i t) l (nhds (g t))) → PositiveDefinite (R.readout () g)

private theorem limitingRejectedLaw : ¬ limitingArena.{u}.Law limitingRejected := by
  intro h
  exact negativeKernel_not_PD (h (l := pure (PUnit.unit : PUnit.{u+1})) (f := fun _ _ => 0) (g := fun _ => 0) (fun _ => zeroPD) (fun _ => tendsto_const_nhds))

private theorem limitingDependence : ObservationalDependence limitingSignature limitingActual := by
  intro i
  refine ⟨(fun t => (Real.cos t : ℂ)), 0, Real.pi, ?_⟩
  norm_num [limitingActual, realize]

def limitingSource : Registration limitingArena.{u} (type_of% @limit.{u}) where
  actual := limitingActual
  bridge := Iff.rfl
  variation := ⟨limit.{u}, limitingRejected, limitingRejectedLaw.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨limitingRejected, ?_, rfl, limitingRejectedLaw.{u}⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := limitingDependence

def limitingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@limit.{u}) (Realization limitingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.limitingUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure.limitingSource
  realizationSource := none
  generated := false
  arena := .source ⟨limitingArena.{u}⟩
  objectArena := .source ⟨limitingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source limitingArena.{u} ⟨limitingSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize limitingSignature (fun _ g t => g t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.Closure
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms limitingAudit

end
end Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
