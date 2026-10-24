import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

/-! Faithful dependent-family audit of the shared original reciprocal tail product. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
open _root_.D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

abbrev signature : Signature where
  Params := ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ s u => ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : ℂ) {u : ℝ}, 1 < u → R.readout () s u = (u : ℂ) ^ (s - 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (2 : ℂ) (u := 2) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(3 : ℂ), (2 : ℝ), (3 : ℝ), ?_⟩
  change (((Int.fract (1 / (2 : ℝ)) : ℝ) : ℂ) * ((2 : ℝ) : ℂ) ^ ((3 : ℂ) - 1)) ≠
    (((Int.fract (1 / (3 : ℝ)) : ℝ) : ℂ) * ((3 : ℝ) : ℂ) ^ ((3 : ℂ) - 1))
  rw [fractionalMellin_tail_integrand_eq_cpow (3 : ℂ) (by norm_num : (1 : ℝ) < 2),
    fractionalMellin_tail_integrand_eq_cpow (3 : ℂ) (by norm_num : (1 : ℝ) < 3)]
  norm_num

def family : Registration arena (type_of% (@fractionalMellin_tail_integrand_eq_cpow)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fractionalMellin_tail_integrand_eq_cpow, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fractionalMellin_tail_integrand_eq_cpow)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin.fractionalMellin_tail_integrand_eq_cpow.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin.family
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
    (fun _ s u => ((Int.fract (1 / u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
