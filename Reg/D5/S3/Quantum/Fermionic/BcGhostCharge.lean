import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostCharge

/-! Source-family candidate for the original pointwise ghost-number identity. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostCharge

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostCharge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => ghostNumber v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, R.readout () () v = ∑ᶠ n : ℤ, normalTerm n v

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem number_singleton : ghostNumber (ket {1}) = ket {1} := by
  simp [ghostNumber, ket, charge]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (ket {1})
  change (0 : Fock) = ∑ᶠ n : ℤ, normalTerm n (ket {1}) at hz
  rw [← ghost_number_normal_sum, number_singleton] at hz
  simpa [ket] using hz

def family : Registration arena (type_of% @ghost_number_normal_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghost_number_normal_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 0, ket {1}, ?_⟩
    change ghostNumber 0 ≠ ghostNumber (ket {1})
    rw [map_zero, number_singleton]
    simp [ket]

def normal_sum_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ghost_number_normal_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.normalSumUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => ghostNumber v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCharge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.BcGhostCharge
