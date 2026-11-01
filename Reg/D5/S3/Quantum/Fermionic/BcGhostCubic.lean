import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostCubic
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private create_ket annihilate_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

namespace Cubic
abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ × ℤ → Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => fun pq : ℤ × ℤ => cubic pq.1 pq.2 v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, Function.HasFiniteSupport (R.readout () () v)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => vacuum) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0
  have hv : (vacuum : Fock) ≠ 0 := by simp [vacuum, ket]
  change (Function.support (fun _ : ℤ × ℤ => vacuum)).Finite at hf
  have he : Function.support (fun _ : ℤ × ℤ => vacuum) = Set.univ := by
    ext pq
    simp [hv]
  rw [he] at hf
  exact Set.infinite_univ hf
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (ket {0}) := by
  intro h
  have he := congrArg (fun f : ℤ × ℤ → Fock => f (0,2) {0,3}) h
  norm_num [actual, realize, cubicTerm, cubic, b, c, create_vacuum,
    create_ket, annihilate_ket, phase, lowerCount, ket] at he

def family : Registration arena (type_of% @cubic_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_finite, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, ket {0}, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@cubic_finite) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Cubic.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Cubic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => fun pq : ℤ × ℤ => cubic pq.1 pq.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCubic
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
end Cubic

namespace Weighted
abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ × ℤ → Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => fun pq : ℤ × ℤ => cubicTerm pq v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, Function.HasFiniteSupport (R.readout () () v)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => vacuum) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0
  have hv : (vacuum : Fock) ≠ 0 := by simp [vacuum, ket]
  change (Function.support (fun _ : ℤ × ℤ => vacuum)).Finite at hf
  have he : Function.support (fun _ : ℤ × ℤ => vacuum) = Set.univ := by
    ext pq
    simp [hv]
  rw [he] at hf
  exact Set.infinite_univ hf
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (ket {0}) := by
  intro h
  have he := congrArg (fun f : ℤ × ℤ → Fock => f (0,2) {0,3}) h
  norm_num [actual, realize, cubicTerm, cubic, b, c, create_vacuum,
    create_ket, annihilate_ket, phase, lowerCount, ket] at he

def family : Registration arena (type_of% @cubicTerm_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubicTerm_finite, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, ket {0}, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@cubicTerm_finite) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Weighted.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Weighted.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => fun pq : ℤ × ℤ => cubicTerm pq v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCubic
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
end Weighted

end Reg.D5.S3.Quantum.Fermionic.BcGhostCubic
