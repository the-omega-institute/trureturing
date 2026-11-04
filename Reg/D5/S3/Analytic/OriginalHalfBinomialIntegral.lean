import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialIntegral
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.OriginalHalfBinomialIntegral
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialIntegral
noncomputable section

/-- The parameter is the original real radius; the state is the original series index. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r n => halfBinomial n ^ 2 * (r : ℂ) ^ n)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire source telescope and all three conclusions remain. The selected
observation is the literal series summand in the identity; its convergence and
the actual sine kernel are retained in the complete law. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (_hr0 : 0 ≤ r) (_hr1 : r < 1),
    Summable (fun n : ℕ => halfBinomial n ^ 2 * (r : ℂ) ^ n) ∧
    IntervalIntegrable (fun θ : ℝ => 1 / Real.sqrt (1 - r * Real.sin θ ^ 2))
      volume 0 (Real.pi / 2) ∧
    (∑' n : ℕ, R.readout () r n) =
      (((2 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi / 2,
        1 / Real.sqrt (1 - r * Real.sin θ ^ 2)) : ℝ) : ℂ)

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 (by norm_num) (by norm_num)).2.2
  norm_num [rejected, realize, Real.pi_ne_zero] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize, halfBinomial]

def family : Registration arena (type_of% @original_series_eq_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_series_eq_integral, rejected, rejected_not_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_not_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_series_eq_integral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.OriginalHalfBinomialIntegral.original_series_eq_integral.audit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialIntegral.family
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
    (fun _ r n => halfBinomial n ^ 2 * (r : ℂ) ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.OriginalHalfBinomialIntegral
