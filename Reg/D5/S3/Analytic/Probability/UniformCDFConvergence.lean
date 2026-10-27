import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.UniformCDFConvergence
import Reg.Support.DependentFamily

/-! Source-bound audits of the standard Gaussian characteristic function and its norm bound. -/

namespace Reg.D5.S3.Analytic.Probability.UniformCDFConvergence

open _root_.D5.S3.Analytic.Probability.UniformCDFConvergence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace CharFun

/-- Equality observes the complex value of the characteristic function. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ left right => left = right) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ left right => left ≠ right) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ u : ℝ,
    r.readout () () (charFun (gaussianReal 0 1) u) (Real.exp (-u ^ 2 / 2) : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (gaussian_charFun_standard 0)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

def source_registration : Registration arena (type_of% @gaussian_charFun_standard) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gaussian_charFun_standard, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gaussian_charFun_standard) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.UniformCDFConvergence.CharFun.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.UniformCDFConvergence.CharFun.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.UniformCDFConvergence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end CharFun

end
end Reg.D5.S3.Analytic.Probability.UniformCDFConvergence
