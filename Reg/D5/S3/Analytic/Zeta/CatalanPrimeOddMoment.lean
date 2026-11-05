import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment

@[reducible] def signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun i p t => actual.readout i p t + 1) (fun e => nomatch e)

/-- The raw source's real parameter, open interval and complex coercion remain
in the law. Varying the observed zero value changes that very equality. -/
@[reducible] def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
    R.readout () () t = (1 / 2 : ℂ) - (t : ℂ)

theorem actual_law : arena.Law actual := by
  exact hurwitzZeta_apply_zero_of_mem_Ioo

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (1 / 2) (by norm_num)
  have ha := hurwitzZeta_apply_zero_of_mem_Ioo (1 / 2) (by norm_num)
  change HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) 0 + 1 = _ at hb
  rw [ha] at hb
  norm_num at hb

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 / 4 : ℝ), (3 / 4 : ℝ), ?_⟩
  change HurwitzZeta.hurwitzZeta ((1 / 4 : ℝ) : UnitAddCircle) 0 ≠
    HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) 0
  rw [hurwitzZeta_apply_zero_of_mem_Ioo _ (by norm_num),
    hurwitzZeta_apply_zero_of_mem_Ioo _ (by norm_num)]
  norm_num

def family : Registration arena (type_of% @hurwitzZeta_apply_zero_of_mem_Ioo) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def hurwitz_zero : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@hurwitzZeta_apply_zero_of_mem_Ioo) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sineActual : Realization signature :=
  realize signature (fun _ _ t => HurwitzZeta.sinZeta (t : UnitAddCircle) 1)
    (fun e => nomatch e)

def sineRejected : Realization signature :=
  realize signature (fun i p t => sineActual.readout i p t + 1) (fun e => nomatch e)

@[reducible] def sineArena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
    R.readout () () t = (Real.pi : ℂ) * ((1 / 2 : ℂ) - (t : ℂ))

theorem sine_rejected_law : ¬ sineArena.Law sineRejected := by
  intro h
  have hb := h (1 / 2) (by norm_num)
  have ha := sinZeta_one_eq_of_mem_Ioo (1 / 2) (by norm_num)
  change HurwitzZeta.sinZeta ((1 / 2 : ℝ) : UnitAddCircle) 1 + 1 = _ at hb
  rw [ha] at hb
  norm_num at hb

def sineFamily : Registration sineArena (type_of% @sinZeta_one_eq_of_mem_Ioo) where
  actual := sineActual
  bridge := Iff.rfl
  variation := ⟨sinZeta_one_eq_of_mem_Ioo, sineRejected, sine_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sineRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sine_rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (1 / 4 : ℝ), (3 / 4 : ℝ), ?_⟩
    change HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) 1 ≠
      HurwitzZeta.sinZeta ((3 / 4 : ℝ) : UnitAddCircle) 1
    rw [sinZeta_one_eq_of_mem_Ioo _ (by norm_num),
      sinZeta_one_eq_of_mem_Ioo _ (by norm_num)]
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.mul_im] at hr
    nlinarith [Real.pi_pos]

def sine_value : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@sinZeta_one_eq_of_mem_Ioo) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sineFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sineArena⟩
  objectArena := .source ⟨sineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sineArena ⟨sineFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => HurwitzZeta.sinZeta (t : UnitAddCircle) 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

@[reducible] def argumentSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def argumentActual : Realization argumentSignature :=
  realize argumentSignature (fun _ _ t =>
    Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))))
    (fun e => nomatch e)

def argumentRejected : Realization argumentSignature :=
  realize argumentSignature (fun i p t => argumentActual.readout i p t + 1)
    (fun e => nomatch e)

@[reducible] def argumentArena : Arena.{0,0,0,0,0} where
  signature := argumentSignature
  Law R := ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
    R.readout () () t = Real.pi * t - Real.pi / 2

theorem argument_rejected_law : ¬ argumentArena.Law argumentRejected := by
  intro h
  have hb := h (1 / 2) (by norm_num)
  have ha := arg_one_sub_exp_two_pi (1 / 2) (by norm_num)
  change Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    ((1 / 2 : ℝ) : ℂ))) + 1 = _ at hb
  rw [ha] at hb
  linarith

def argumentFamily : Registration argumentArena (type_of% @arg_one_sub_exp_two_pi) where
  actual := argumentActual
  bridge := Iff.rfl
  variation := ⟨arg_one_sub_exp_two_pi, argumentRejected, argument_rejected_law⟩
  sensitivity := ⟨fun i => ⟨argumentRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, argument_rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (1 / 4 : ℝ), (3 / 4 : ℝ), ?_⟩
    change Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((1 / 4 : ℝ) : ℂ))) ≠ Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) *
      Complex.I * ((3 / 4 : ℝ) : ℂ)))
    rw [arg_one_sub_exp_two_pi _ (by norm_num), arg_one_sub_exp_two_pi _ (by norm_num)]
    intro h
    nlinarith [Real.pi_pos]

def argument_value : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@arg_one_sub_exp_two_pi) (Realization argumentSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.arg_one_sub_exp_two_pi.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.argumentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨argumentArena⟩
  objectArena := .source ⟨argumentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source argumentArena ⟨argumentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize argumentSignature (fun _ _ t =>
    Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/- This mirror intentionally does not call the other sixteen source lemmas
declared_validated. Their actual telescopes, observation candidates, admission
classification, live uses and missing certificates are listed in the complete
handoff. In particular an equality of Hurwitz values does not certify a Cauchy
or Tendsto target, a uniform tail estimate, the conditional Hurwitz supplier,
the primitive functional equation route, or either character nonvanishing law.
Those need their own exact source realization, variation, sensitivity and
dependence rather than a surrogate scalar equality or this registration. -/

end Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
