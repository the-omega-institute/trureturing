import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
open _root_.D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
open _root_.D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PredictiveThermodynamic.Physical (Assignment)

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The scalar entry at a fixed size, mode and row, with the column as state. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ N : ℕ, Σ _j : Fin N, Assignment N) (fun p => Assignment p.1) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p t => fullC p.2.1 p.2.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
/-- Retain every size, mode, row and column of the entry formula. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (j : Fin N) (s t : Assignment N),
    R.readout () ⟨N, j, s⟩ t =
      if t j = true ∧ s = Function.update t j false
      then (-1 : ℂ) ^ prefixCount t j else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (0 : Fin 1) (Function.update (fun _ => true) 0 false) (fun _ => true)
  norm_num [rejected, realize, prefixCount] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, Function.update (fun _ => true) 0 false⟩,
    (fun _ => false), (fun _ => true), ?_⟩
  change fullC (0 : Fin 1) (Function.update (fun _ => true) 0 false) (fun _ => false) ≠
    fullC (0 : Fin 1) (Function.update (fun _ => true) 0 false) (fun _ => true)
  rw [fullC_entry, fullC_entry]
  norm_num [prefixCount]

def source_registration : Registration arena (type_of% @fullC_entry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fullC_entry, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fullC_entry) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => fullC p.2.1 p.2.2 t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
