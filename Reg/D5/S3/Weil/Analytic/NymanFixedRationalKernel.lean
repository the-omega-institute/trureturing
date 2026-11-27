import D5.S3.Weil.Analytic.NymanFixedRationalKernel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source registration for the agreement of rational and real kernel values. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Analytic.NymanFixedRationalKernel

open _root_.NymanFixedRationalKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => b u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : ℚ, (bRat u : ℝ) = R.readout () () u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : (bRat 0 : ℝ) = 1 := h 0
  rw [bRat_cast, Rat.cast_zero, b_zero_left (by norm_num)] at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 7 / 6, ?_⟩
  norm_num [actual, realize, b, c, A, Fin.sum_univ_succ]

def family : Registration arena (type_of% (@bRat_cast)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bRat_cast, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bRat_cast) (Realization signature) Unit Unit where
  unitName := `NymanFixedRationalKernel.bRat_cast.__information_unit
  realizationName := `Reg.D5.S3.Weil.Analytic.NymanFixedRationalKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => b u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Analytic.NymanFixedRationalKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.Analytic.NymanFixedRationalKernel
