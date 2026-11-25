import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzCothStripMode
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the compensated lower mode integral. -/

noncomputable section

open PetzCothStripMode MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.PetzCothStripMode

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ω : ℝ, Integrable (lowerMode ω) ∧
    R.readout () () (∫ s, lowerMode ω s)
      (if ω = 0 then 0 else (ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1)

private theorem rejectedLaw : ¬ arena.Law rejected :=
  fun law => (law 0).2

def family : Registration arena (type_of% @integral_lowerMode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_lowerMode, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_lowerMode) (Realization signature) Unit Unit where
  unitName := `PetzCothStripMode.integral_lowerMode.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzCothStripMode.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzCothStripMode
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PetzCothStripMode
