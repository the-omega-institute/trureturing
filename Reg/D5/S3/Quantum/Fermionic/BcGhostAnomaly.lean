import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.Fermionic.BcGhostBRST
import Reg.D5.S3.Quantum.Fermionic.BcGhostCubic
import D5.S3.Quantum.Fermionic.BcGhostAnomaly

open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.C (R_zero_vacuum R_two_vacuum)
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open LeanInformationAudit
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

namespace Mixed
abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x => Qg*L x-L x*Qg) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℤ, R.readout () () r = ((26/12 : ℂ) * ((r : ℂ)^3-r)) • c r
def rejected : Realization signature := realize signature
  (fun _ _ x => 1) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 0)
  norm_num [rejected, realize, vacuum, ket] at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (-2) := by
  intro h
  change Qg*L 0-L 0*Qg = Qg*L (-2)-L (-2)*Qg at h
  rw [mixed_anomaly, mixed_anomaly] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {7}) h
  norm_num [c, create_vacuum, ket] at he

def family : Registration arena (type_of% @mixed_anomaly) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_anomaly, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, -2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@mixed_anomaly) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Mixed.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Mixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Qg*L x-L x*Qg) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostAnomaly
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mixed


namespace Covariance
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ r => R r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m r : ℤ, L m*R.readout () m r-R.readout () m r*L m = ((-2*m-r : ℤ) : ℂ) • R.readout () m (m+r)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 0 1)
  norm_num [rejected, realize, vacuum, ket] at he
  simp only [LinearMap.neg_apply, Module.End.one_apply, Finsupp.neg_apply,
    Finsupp.single_eq_same] at he
  norm_num at he
private theorem actual_dependence : actual.readout () 0 0 ≠ actual.readout () 0 2 := by
  intro h
  change R 0 = R 2 at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {1,5}) h
  norm_num [R_zero_vacuum, R_two_vacuum, ket] at he

def family : Registration arena (type_of% @R_covariance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨R_covariance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨0, 0, 2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@R_covariance) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Covariance.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Covariance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => R r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostAnomaly
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Covariance


namespace Parity
abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ v => Qg v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, parity (R.readout () () v)+R.readout () () (parity v) = 0
def rejected : Realization signature := realize signature (fun _ _ v => v) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun v : Fock => v ∅) (h vacuum)
  norm_num [rejected, realize, vacuum, parity_ket] at he
  simp only [ket, Finsupp.add_apply, Finsupp.single_eq_same] at he
  norm_num at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (b (-2) vacuum) := by
  change Qg 0 ≠ Qg (b (-2) vacuum)
  exact _root_.Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Vacuum.actual_dependence

def family : Registration arena (type_of% @Qg_odd) where
  actual := actual
  bridge := by
    change (parity*Qg+Qg*parity = 0) ↔
      (∀ v : Fock, parity (Qg v)+Qg (parity v) = 0)
    constructor
    · intro h v; exact LinearMap.congr_fun h v
    · intro h; apply LinearMap.ext; intro v; exact h v
  variation := ⟨by intro v; exact LinearMap.congr_fun Qg_odd v, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, b (-2) vacuum, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@Qg_odd) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Parity.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly.Parity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => Qg v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostAnomaly
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Parity

end Reg.D5.S3.Quantum.Fermionic.BcGhostAnomaly
