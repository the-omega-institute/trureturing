import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the normalized Walsh matrix's unitarity. -/

namespace Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation

open _root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the source membership relation as its submonoid operand varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Submonoid (Matrix (Fin 4) (Fin 4) ℂ))
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ S U => U ∈ S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain the complete unitarity assertion at the published Walsh matrix. -/
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (Matrix.unitaryGroup (Fin 4) ℂ) u4

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⊤, ⊥, ?_⟩
  intro h
  have hz : (0 : Matrix (Fin 4) (Fin 4) ℂ) ∈
      (⊥ : Submonoid (Matrix (Fin 4) (Fin 4) ℂ)) :=
    Eq.mp (congrFun h 0) (show (0 : Matrix (Fin 4) (Fin 4) ℂ) ∈
      (⊤ : Submonoid (Matrix (Fin 4) (Fin 4) ℂ)) from trivial)
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0)
    (Submonoid.mem_bot.mp hz)
  norm_num at hentry

def source_registration : Registration arena (type_of% u4_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨u4_unitary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.u4_unitary)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S U => U ∈ S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.u4_unitary
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
