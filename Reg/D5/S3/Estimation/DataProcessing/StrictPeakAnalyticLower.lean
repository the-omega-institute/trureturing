import D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
open _root_.D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set

/-- A source tail and its quantile argument remain separate coordinates. -/
abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ G u => G u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Hypotheses stay anchored in G while interventions change the concluded moments. -/
def fullLaw (r : Realization signature) : Prop :=
  ∀ (G : ℝ → ℝ)
    (_hG : IntervalIntegrable G volume 0 1)
    (_hG2 : IntervalIntegrable (fun u => G u ^ 2) volume 0 1)
    (_hbound : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G u ∧ G u ≤ cap u),
    let X := ∫ u in (0 : ℝ)..1, r.readout () G u
    0 ≤ X ∧ X ≤ 1/3 ∧
    ∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ determinant (r.readout () G)+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ∧
      -X/15 ≤ determinant (r.readout () G) ∧
      (0 < X → X < 1/3 → -X/15 < determinant (r.readout () G))

abbrev arena : Arena where
  signature := signature
  Law := fullLaw

private theorem rejected_law : ¬ fullLaw rejected := by
  intro h
  have hb : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ cap u := by
    intro u hu
    constructor
    · norm_num
    · unfold cap
      nlinarith [hu.1,hu.2,sq_nonneg (1-u)]
  have ht := h (fun _ => 0) intervalIntegrable_const intervalIntegrable_const hb
  have hle := ht.2.1
  norm_num [rejected,realize] at hle

def family : Registration arena (type_of% @bounded_tail_lower_surface) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_tail_lower_surface,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨id,0,1,by norm_num [actual,realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_tail_lower_surface)
    (type_of% (realize signature (fun _ G u => G u) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower.bounded_tail_lower_surface.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ G u => G u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","value","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The entire continuous tail family is kept; no finite source acquisition is asserted. -/
def analysisSource : Analysis.Source (@bounded_tail_lower_surface) :=
  Analysis.Source.ofRegistration _ family .exact {
    owner := `D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","value","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}

def analysis : AuricFib.Contract.Application (@bounded_tail_lower_surface) where
  evidence := .typed {
    source := analysisSource
    plan := {task := (show Unit from ()),initial := [],additions := [[(show Unit from ())],[]]}
    acquisition := .unavailable "Continuous quantile tails; a finite source fiber is not acquired"}

namespace CapIntegral

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ u in (0 : ℝ)..1, f u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def law (r : Realization signature) : Prop := r.readout () () cap = 1/3
abbrev arena : Arena where
  signature := signature
  Law := law

private theorem rejected_law : ¬ law rejected := by norm_num [law,rejected,realize]

def family : Registration arena (type_of% cap_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cap_integral,rejected,rejected_law⟩
  sensitivity := ⟨fun _ => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim _ _)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := by
    intro _
    exact ⟨(),fun _ => 0,fun _ => 1,by norm_num [actual,realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    cap_integral
    (type_of% (realize signature
      (fun _ _ f => ∫ u in (0 : ℝ)..1, f u) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower.cap_integral.__information_unit
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower.CapIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f => ∫ u in (0 : ℝ)..1, f u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","fn","arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end CapIntegral

#print axioms family
end Reg.D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
