import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostBRST

open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private create_ket annihilate_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

namespace B
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
  (fun _ _ x => Qg*b x+b x*Qg) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℤ, R.readout () () r = L r
def rejected : Realization signature := realize signature
  (fun _ _ x => 1) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 0)
  norm_num [rejected, realize, L_vacuum_nonneg 0 (by omega), vacuum, ket] at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (-2) := by
  intro h
  change Qg*b 0+b 0*Qg = Qg*b (-2)+b (-2)*Qg at h
  rw [ward_b, ward_b] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0,3}) h
  rw [L_vacuum_nonneg 0 (by omega), L_vacuum] at he
  have hI : Finset.Icc (0 : ℤ) 1 = {0,1} := by decide
  rw [hI] at he
  norm_num [b, c, create_vacuum, create_ket, phase, lowerCount, ket] at he

def family : Registration arena (type_of% @ward_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_b, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, -2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ward_b) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.B.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.B.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Qg*b x+b x*Qg) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostBRST
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
end B

namespace C
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
  (fun _ _ x => Qg*c x+c x*Qg) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℤ, R.readout () () r = _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.R r
def rejected : Realization signature := realize signature
  (fun _ _ x => 1) (fun e => nomatch e)
private theorem R_two_vacuum : R 2 vacuum = 0 := by
  change (∑ᶠ p : ℤ, rTerm 2 p vacuum) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : 2 ≤ p
  · simp [rTerm, c_swap p (2-p), Module.End.mul_apply, ghost_vacuum.2.1 p hp]
  by_cases hq : 2 ≤ 2-p
  · simp [rTerm, Module.End.mul_apply, ghost_vacuum.2.1 (2-p) hq]
  have he : p = 1 := by omega
  subst p
  norm_num [rTerm]
private theorem R_zero_vacuum : R 0 vacuum = (2 : ℂ) • ket {1,5} := by
  classical
  change (∑ᶠ p : ℤ, rTerm 0 p vacuum) = _
  rw [finsum_eq_sum_of_support_subset _ (s := {-1,0,1}) (by
    intro p hp
    by_contra hn
    have he : p ≤ -2 ∨ 2 ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    rcases he with he | he
    · exact hp (by simp [rTerm, Module.End.mul_apply, ghost_vacuum.2.1 (-p) (by omega)])
    · exact hp (by simp [rTerm, c_swap p (-p), Module.End.mul_apply,
        ghost_vacuum.2.1 p he]))]
  norm_num [rTerm, c, create_vacuum, create_ket, phase, lowerCount, ket]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 2)
  norm_num [rejected, realize, R_two_vacuum, vacuum, ket] at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 2 := by
  intro h
  change Qg*c 0+c 0*Qg = Qg*c 2+c 2*Qg at h
  rw [ward_c, ward_c] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {1,5}) h
  norm_num [R_zero_vacuum, R_two_vacuum, ket] at he

def family : Registration arena (type_of% @ward_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_c, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, 2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ward_c) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.C.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRST.C.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Qg*c x+c x*Qg) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostBRST
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
end C

end Reg.D5.S3.Quantum.Fermionic.BcGhostBRST
