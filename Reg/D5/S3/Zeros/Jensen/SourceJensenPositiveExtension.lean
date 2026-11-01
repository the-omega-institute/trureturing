import D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.Jensen.SourceJensenPositiveExtension

open _root_.D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ[X]) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ p => LaguerreAt p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ (p : ℝ[X]), p.Splits → ∀ x : ℝ, f.readout () () p x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (by simp) 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, X ^ 2 + 1, ?_⟩
  intro he
  have h : LaguerreAt (X ^ 2 + 1) 0 := Eq.mp (congrFun he 0) (by simp [actual, realize, LaguerreAt])
  norm_num [LaguerreAt, Polynomial.derivative_add, Polynomial.derivative_pow] at h

def family : Registration arena (type_of% (@laguerre_splits)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨laguerre_splits, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@laguerre_splits) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Zeros.Jensen.SourceJensenPositiveExtension.laguerre_splits.__information_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.SourceJensenPositiveExtension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => LaguerreAt p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
