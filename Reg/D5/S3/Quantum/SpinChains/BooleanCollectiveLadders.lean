import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the actual primitive dimension at each rank. -/

namespace Reg.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
open _root_.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ S t => Module.finrank ℂ (primitive (2 * S) t))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original telescope, with only the observed primitive dimension replaced. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ S t : ℕ, t ≤ S →
    R.readout () S t = (2 * S).choose t - previousChoose (2 * S) t

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 (by decide)
  norm_num [rejected, realize, previousChoose] at he

/-- At four sites, the primitive dimensions at ranks zero and one differ. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change Module.finrank ℂ (primitive (2 * 2) 0) ≠
    Module.finrank ℂ (primitive (2 * 2) 1)
  rw [primitive_multiplicity 2 0 (by decide), primitive_multiplicity 2 1 (by decide)]
  norm_num [previousChoose]

def source_registration : Registration arena
    (∀ S t : ℕ, t ≤ S → Module.finrank ℂ (primitive (2 * S) t) =
      (2 * S).choose t - previousChoose (2 * S) t) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨primitive_multiplicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders.primitive_multiplicity)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders.multiplicity_unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ S t => Module.finrank ℂ (primitive (2 * S) t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
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
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
