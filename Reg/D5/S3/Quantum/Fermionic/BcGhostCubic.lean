import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostBRST

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostCubic
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostBRST
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (normal)
open LeanInformationAudit

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
    create_ket, annihilate_ket, phase, lowerCount] at he
  simp only [ket] at he
  have hs : ({3,0} : Finset ℕ) = {0,3} := by decide
  rw [hs, Finsupp.single_eq_same] at he
  norm_num at he

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
    create_ket, annihilate_ket, phase, lowerCount] at he
  simp only [ket] at he
  have hs : ({3,0} : Finset ℕ) = {0,3} := by decide
  rw [hs, Finsupp.single_eq_same] at he
  norm_num at he

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

namespace Vacuum
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro
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
  Law R := R.readout () () vacuum = 0
def rejected : Realization signature := realize signature (fun _ _ _ => vacuum) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun v : Fock => v ∅) h
  norm_num [rejected, realize, vacuum, ket] at he
theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (b (-2) vacuum) := by
  intro h
  change Qg 0 = Qg (b (-2) vacuum) at h
  have hv := LinearMap.congr_fun (ward_b (-2)) vacuum
  simp only [LinearMap.add_apply, Module.End.mul_apply, Qg_vacuum, map_zero, add_zero] at hv
  rw [map_zero, hv] at h
  have he := congrArg (fun v : Fock => v {0,3}) h
  rw [L_vacuum] at he
  have hI : Finset.Icc (0 : ℤ) 1 = {0,1} := by decide
  simp only [show (-2 : ℤ) + 2 = 0 by decide] at he
  rw [hI] at he
  norm_num [b, c, create_vacuum, create_ket, phase, lowerCount] at he
  simp only [ket] at he
  have hz (z : ℂ) : (Finsupp.single ({2,1} : Finset ℕ) z) {0,3} = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  rw [hz] at he
  norm_num at he

def family : Registration arena (type_of% @Qg_vacuum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Qg_vacuum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, b (-2) vacuum, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@Qg_vacuum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Vacuum.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.Vacuum.family
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
    owner := `D5.S3.Quantum.Fermionic.BcGhostCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Vacuum


namespace BilinearB
abbrev signature : Signature where
  Params := ℤ × ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ pq r => cubic pq.1 pq.2*b r+b r*cubic pq.1 pq.2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q r : ℤ, R.readout () (p,q) r = (if q+r = 0 then normal (-p-q) p else 0)-(if p+r = 0 then normal (-p-q) q else 0)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 1 1 0)
  norm_num [rejected, realize, vacuum, ket] at he
private theorem actual_dependence : actual.readout () (0,2) (-2) ≠ actual.readout () (0,2) (-3) := by
  intro h
  change cubic 0 2*b (-2)+b (-2)*cubic 0 2 = cubic 0 2*b (-3)+b (-3)*cubic 0 2 at h
  rw [cubic_b, cubic_b] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0,3}) h
  norm_num [normal, b, c, create_vacuum, create_ket, phase, lowerCount] at he <;>
    norm_num [ket, Finset.filter_insert, Finset.insert_comm, ← Finsupp.single_add] at he

def family : Registration arena (type_of% @cubic_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_b, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(0,2), -2, -3, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@cubic_b) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.BilinearB.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.BilinearB.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ pq r => cubic pq.1 pq.2*b r+b r*cubic pq.1 pq.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCubic
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end BilinearB

namespace BilinearC
abbrev signature : Signature where
  Params := ℤ × ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ pq r => cubic pq.1 pq.2*c r+c r*cubic pq.1 pq.2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q r : ℤ, R.readout () (p,q) r = if -p-q+r = 0 then c p*c q else 0
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 1 1 0)
  norm_num [rejected, realize, vacuum, ket] at he
private theorem actual_dependence : actual.readout () (0,2) 2 ≠ actual.readout () (0,2) 3 := by
  intro h
  change cubic 0 2*c 2+c 2*cubic 0 2 = cubic 0 2*c 3+c 3*cubic 0 2 at h
  rw [cubic_c, cubic_c] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A (ket {0}) {3}) h
  norm_num [c, annihilate_ket, create_vacuum, create_ket, phase, lowerCount] at he <;>
    norm_num [ket, Finset.filter_insert, Finset.insert_comm, ← Finsupp.single_add] at he

def family : Registration arena (type_of% @cubic_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_c, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(0,2), 2, 3, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@cubic_c) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.BilinearC.auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCubic.BilinearC.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ pq r => cubic pq.1 pq.2*c r+c r*cubic pq.1 pq.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCubic
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end BilinearC

end Reg.D5.S3.Quantum.Fermionic.BcGhostCubic
