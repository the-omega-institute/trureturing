import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.FactorialJensenKernelBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.FactorialJensenKernelBound
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Zeros.Jensen.FactorialJensenKernelBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.cosh x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ) (M : ℝ), 0 ≤ M →
    evenFactorialSum n M ≤ F.readout () () (Real.sqrt M)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 (by norm_num)
  norm_num [rejected, realize, evenFactorialSum] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.cosh 0 ≠ Real.cosh 1
  rw [Real.cosh_zero]
  exact ne_of_lt (Real.one_lt_cosh.mpr (by norm_num : (1 : ℝ) ≠ 0))

def family : Registration arena (type_of% (@even_sum_le_cosh)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨even_sum_le_cosh, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@even_sum_le_cosh) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.FactorialJensenKernelBound.unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.FactorialJensenKernelBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.cosh x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.FactorialJensenKernelBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Zeros.Jensen.FactorialJensenKernelBound
