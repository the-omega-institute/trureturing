import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState

/-! Source-family audit attempts for the literal original endpoints. The shifted
mode and closed-statement source selectors remain absent. This file does not
claim declared validation; compiled family proofs alone do not supply selectors. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped VertexOperator
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateField
open _root_.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
open _root_.D5.S3.VertexAlgebra.FieldNormalProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private current_on_generators from D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

namespace Conformal
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
  (fun _ _ m => (Y Omega) [[m + 1]]) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℤ, R.readout () () m = _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 0)
  change (1 : Module.End ℂ Fock) vacuum ∅ =
    _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 vacuum ∅ at he
  rw [L_vacuum_nonneg 0 (by omega)] at he
  norm_num [vacuum, ket] at he
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (-2) := by
  intro h
  change (Y Omega) [[0 + 1]] = (Y Omega) [[-2 + 1]] at h
  rw [conformal_modes, conformal_modes] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0,3}) h
  rw [L_vacuum_nonneg 0 (by omega), L_vacuum] at he
  have hI : Finset.Icc (0 : ℤ) 1 = {0,1} := by decide
  simp only [show (-2 : ℤ) + 2 = 0 by decide] at he
  rw [hI] at he
  norm_num [b, c, create_vacuum, create_ket, phase, lowerCount] at he
  simp only [ket] at he
  have hz (z : ℂ) : (Finsupp.single ({2,1} : Finset ℕ) z) {0,3} = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  rw [hz] at he
  norm_num at he

def family : Registration arena (type_of% @conformal_modes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conformal_modes, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, -2, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@conformal_modes) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Conformal.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Conformal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => (Y Omega) [[m + 1]]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Conformal

namespace Odd
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
  (fun _ _ a => parity a) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () Jg = (-1 : ℂ) ^ 1 • Jg
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun a : Fock => a {0,1,3}) h
  norm_num [rejected, realize, Jg, ket] at he
private theorem actual_dependence : actual.readout () () vacuum ≠ actual.readout () () 0 := by
  intro h
  change parity vacuum = parity 0 at h
  have hv : parity vacuum = vacuum := by simp [vacuum, parity_ket]
  rw [map_zero, hv] at h
  have he := congrArg (fun a : Fock => a ∅) h
  norm_num [vacuum, ket] at he

def family : Registration arena (type_of% @current_odd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_odd, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), vacuum, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@current_odd) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Odd.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Odd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => parity a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Odd

namespace Current
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
  (fun _ _ n => (Y Jg) [[n]]) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 0 = _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) h
  change (1 : Module.End ℂ Fock) vacuum ∅ =
    _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg vacuum ∅ at he
  rw [_root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg_vacuum] at he
  norm_num [vacuum, ket] at he
private theorem actual_dependence : actual.readout () () (-1) ≠ actual.readout () () 0 := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0,1,3}) h
  change ((Y Jg) [[-1]]) vacuum {0,1,3} = ((Y Jg) [[0]]) vacuum {0,1,3} at he
  rw [stateField_creation.2.1, stateField_creation.2.2.1 Jg 0 (by omega)] at he
  norm_num [Jg, ket] at he

def family : Registration arena (type_of% @current_zero_mode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_zero_mode, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), -1, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@current_zero_mode) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Current.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Current.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (Y Jg) [[n]]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Current

namespace Derivation
abbrev signature : Signature where
  Params := ℕ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p a n => _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg * ((Y a) [[n]]) -
    ((-1 : ℂ) ^ p) • (((Y a) [[n]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg))
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Fock) (p : ℕ), parity a = (-1 : ℂ) ^ p • a → ∀ n : ℤ,
    R.readout () p a n = (Y (_root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg a)) [[n]]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum ∅) (h 0 0 (by simp) 0)
  norm_num [rejected, realize, vacuum, ket] at he
private theorem actual_dependence : actual.readout () 1 (ket {0}) ≠ actual.readout () 1 0 := by
  intro h
  have qg : _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg (ket {0}) = Omega := by
    rw [← current_zero_mode]
    exact current_on_generators.1
  have first : actual.readout () 1 (ket {0}) (-1) = (Y Omega) [[-1]] := by
    change _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg * ((Y (ket {0})) [[-1]]) -
      ((-1 : ℂ) ^ 1) • (((Y (ket {0})) [[-1]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg) = _
    rw [Qg_signed_derivation (ket {0}) 1 (by simp [parity_ket]) (-1), qg]
  have he := congrArg (fun A : ℤ → Module.End ℂ Fock => A (-1) vacuum {0,3}) h
  change actual.readout () 1 (ket {0}) (-1) vacuum {0,3} =
    actual.readout () 1 0 (-1) vacuum {0,3} at he
  rw [first, stateField_creation.2.1] at he
  have hz (z : ℂ) : (Finsupp.single ({1,2} : Finset ℕ) z) {0,3} = 0 :=
    Finsupp.single_eq_of_ne (by decide)
  norm_num [actual, realize, Omega, ket, hz] at he

def family : Registration arena (type_of% @Qg_signed_derivation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Qg_signed_derivation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨1, ket {0}, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@Qg_signed_derivation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Derivation.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState.Derivation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a n => _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg * ((Y a) [[n]]) -
      ((-1 : ℂ) ^ p) • (((Y a) [[n]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostBRST.Qg))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Derivation

end Reg.D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
