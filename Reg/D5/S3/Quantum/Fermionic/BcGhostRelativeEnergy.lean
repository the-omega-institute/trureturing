import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro
open _root_.D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => L 0 (ket S)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ S : Finset ℕ, R.readout () () S =
    (energy S : ℂ) • ket S

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h ({1} : Finset ℕ)
  change (0 : Fock) = (energy ({1} : Finset ℕ) : ℂ) • ket {1} at hz
  have hc := congrArg (fun v : Fock => v {1}) hz
  norm_num [energy, siteEnergy_one, ket] at hc

def family : Registration arena (type_of% @L_zero_ket) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨L_zero_ket, rejected, rejected_law⟩
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
    refine ⟨(), (), ({1} : Finset ℕ), ?_⟩
    change L 0 (ket {1}) ≠ L 0 (ket ∅)
    rw [L_zero_ket, L_zero_ket]
    norm_num [energy, siteEnergy, siteMode, siteSign, ket]

def l_zero_ket_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@L_zero_ket) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.lZeroKetUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => L 0 (ket S)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Finset ℕ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
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

end Reg.D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
