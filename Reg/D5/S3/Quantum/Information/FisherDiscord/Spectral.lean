import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FisherDiscord.Spectral
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source realizations for the spectral information formulas. -/

namespace Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral
open _root_.D5.S3.Quantum.Information.FisherDiscord.Spectral
open _root_.D5.S3.Quantum.Information.FisherDiscord.Defs
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev kernelSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def kernelActual : Realization kernelSignature :=
  realize kernelSignature (fun _ a b => pairKernel a b) (fun e => nomatch e)

def kernelRejected : Realization kernelSignature :=
  realize kernelSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ R.readout () a b

private theorem kernelRejected_law : ¬ kernelArena.Law kernelRejected := by
  intro h
  have he := h 0 0 (by norm_num) (by norm_num)
  norm_num [kernelRejected, realize] at he

def kernelSource : Registration kernelArena (type_of% @pairKernel_nonneg) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨pairKernel_nonneg, kernelRejected, kernelRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    kernelArena.Law kernelActual kernelRejected kernelRejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 4, ?_⟩
    norm_num [kernelActual, realize, pairKernel]

def kernelAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pairKernel_nonneg) (Realization kernelSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.kernelAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral.kernelSource
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ a b => pairKernel a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FisherDiscord.Spectral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Quantum.Information.FisherDiscord.Spectral
