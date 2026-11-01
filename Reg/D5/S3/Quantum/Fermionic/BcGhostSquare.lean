import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostSquare

open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostSquare
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private create_ket annihilate_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic
open private squareAnomaly_b squareAnomaly_vacuum from D5.S3.Quantum.Fermionic.BcGhostSquare

namespace Square
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
  (fun _ _ x => (Qg*Qg) x) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, R.readout () () v = squareAnomaly v
def rejected : Realization signature := realize signature
  (fun _ _ x => vacuum) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun v : Fock => v ∅) (h 0)
  norm_num [rejected, realize, vacuum, ket] at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (b (-2) vacuum) := by
  intro h
  change (Qg*Qg) 0 = (Qg*Qg) (b (-2) vacuum) at h
  rw [square_anomaly] at h
  have hv := LinearMap.congr_fun (squareAnomaly_b (-2)) vacuum
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    squareAnomaly_vacuum, map_zero, sub_zero] at hv
  have he := congrArg (fun v : Fock => v {7}) h
  rw [map_zero, hv] at he
  norm_num [anomalyCoefficient, c, create_vacuum, ket] at he

def family : Registration arena (type_of% @square_anomaly) where
  actual := actual
  bridge := by
    change (Qg*Qg = squareAnomaly) ↔ (∀ v : Fock, (Qg*Qg) v = squareAnomaly v)
    exact LinearMap.ext_iff
  variation := ⟨by intro v; exact LinearMap.congr_fun square_anomaly v, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, b (-2) vacuum, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@square_anomaly) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostSquare.Square.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostSquare.Square.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (Qg*Qg) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostSquare
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Square

end Reg.D5.S3.Quantum.Fermionic.BcGhostSquare
