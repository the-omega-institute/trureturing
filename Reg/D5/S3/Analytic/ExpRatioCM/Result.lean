import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExpRatioCM.Result
import Reg.D5.S3.Analytic.ExpRatioCM.Extraction

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.ExpRatioCM.Defs
open _root_.D5.S3.Analytic.ExpRatioCM.Result
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.ExpRatioCM.Result

abbrev signature := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.momentSignature
abbrev actual := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.ratioActual
abbrev secondActual := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.secondRatioActual
abbrev rejectedFamily := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.zeroMoment

namespace EveryTail

def arena : Arena where
  signature := signature
  Law R := ∀ (i : ℕ), 3 ≤ i → ∀ T : ℝ,
    ∃ (k : ℕ) (t : ℝ), T < t ∧ 0 < t ∧
      (-1 : ℝ) ^ k * iteratedDeriv k (R.readout () i) t < 0 ∧
      (-1 : ℝ) ^ k * iteratedDeriv k (ratioG i) t < 0

private theorem rejected : ¬ arena.Law rejectedFamily := by
  intro h
  obtain ⟨k, t, _, _, hf, _⟩ := h 3 (by norm_num) 0
  simpa [rejectedFamily, _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.zeroMoment,
    realize] using hf

def family : Registration arena (type_of% @failure_on_every_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@failure_on_every_tail, rejectedFamily, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejectedFamily rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.FirstRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@failure_on_every_tail) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.EveryTail.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.EveryTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end EveryTail

namespace Failure

def arena : Arena where
  signature := signature
  Law R := ∀ (i : ℕ), 3 ≤ i →
    ¬ CompletelyMonotoneOn (R.readout () i) ∧ ¬ CompletelyMonotoneOn (ratioG i)

private theorem rejected : ¬ arena.Law rejectedFamily := by
  intro h
  exact (h 3 (by norm_num)).1
    _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.zero_cm

def family : Registration arena (type_of% @not_cm_of_three_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@not_cm_of_three_le, rejectedFamily, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejectedFamily rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.FirstRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@not_cm_of_three_le) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.Failure.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.Failure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Failure

namespace First

def arena : Arena where
  signature := signature
  Law R := ∀ i : ℕ, CompletelyMonotoneOn (R.readout () i) ↔ i ≤ 2

private theorem rejected : ¬ arena.Law rejectedFamily := by
  intro h
  have hf := (h 3).mp _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.zero_cm
  omega

def family : Registration arena (type_of% @classification) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@classification, rejectedFamily, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejectedFamily rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.FirstRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classification) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.First.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.First.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end First

namespace Second

def arena : Arena where
  signature := signature
  Law R := ∀ i : ℕ, CompletelyMonotoneOn (R.readout () i) ↔ i ≤ 2

private theorem rejected : ¬ arena.Law rejectedFamily := by
  intro h
  have hf := (h 3).mp _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.zero_cm
  omega

def family : Registration arena (type_of% @classificationG) where
  actual := secondActual
  bridge := Iff.rfl
  variation := ⟨@classificationG, rejectedFamily, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law secondActual rejectedFamily rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.SecondRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classificationG) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.Second.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Result.Second.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioG i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Second

end Reg.D5.S3.Analytic.ExpRatioCM.Result
end
