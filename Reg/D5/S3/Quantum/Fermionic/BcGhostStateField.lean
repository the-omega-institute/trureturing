import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostStateField

/-! Faithful source-family audit attempts. The closed creation and translation
conjunctions have no supplied source selector; this is missing binding evidence,
not a claim of declared validation. Parity has a direct two-binder selector. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped VertexOperator
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostStateField
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateField
open _root_.D5.S3.VertexAlgebra.FieldNormalProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Creation
abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := VertexOperator ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ a => Y a) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () vacuum = identityField ∧
    (∀ a : Fock, ((R.readout () () a) [[-1]]) vacuum = a) ∧
    (∀ (a : Fock) (n : ℤ), 0 ≤ n → ((R.readout () () a) [[n]]) vacuum = 0) ∧
    (∀ n : ℤ, ((R.readout () () (ket {0})) [[n]]) = b (n - 1)) ∧
    (∀ n : ℤ, ((R.readout () () (ket {1})) [[n]]) = c (n + 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h.2.1 vacuum
  change (0 : Fock) = vacuum at hz
  have bad := congrArg (fun v : Fock => v ∅) hz
  norm_num [vacuum, ket] at bad
private theorem actual_dependence : actual.readout () () vacuum ≠ actual.readout () () 0 := by
  intro h
  have hz := congrArg (fun A : VertexOperator ℂ Fock => (A [[-1]]) vacuum) h
  change ((Y vacuum) [[-1]]) vacuum = ((Y 0) [[-1]]) vacuum at hz
  rw [stateField_creation.2.1, stateField_creation.2.1] at hz
  simpa [vacuum, ket] using hz

def family : Registration arena (type_of% @stateField_creation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_creation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), vacuum, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stateField_creation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Creation.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Creation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => Y a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Creation

namespace Translation
abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ a n => _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) * ((Y a) [[n]]) -
    ((Y a) [[n]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) vacuum = 0 ∧
    ∀ (a : Fock) (n : ℤ), R.readout () () a n = -(n : ℂ) • ((Y a) [[n - 1]])
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h.2 (ket {0}) (-1)
  change (0 : Module.End ℂ Fock) = -((-1 : ℤ) : ℂ) • ((Y (ket {0})) [[-1 - 1]]) at hz
  rw [stateField_creation.2.2.2.1] at hz
  have he := LinearMap.congr_fun hz vacuum
  norm_num [b, create_vacuum, ket] at he
  have bad := congrArg (fun v : Fock => v {2}) he
  norm_num at bad
private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () (ket {0}) := by
  intro h
  have hz := congrArg (fun f : ℤ → Module.End ℂ Fock => f (-1)) h
  change _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) * ((Y 0) [[-1]]) -
      ((Y 0) [[-1]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) =
    _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) * ((Y (ket {0})) [[-1]]) -
      ((Y (ket {0})) [[-1]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) at hz
  rw [stateField_translation.2, stateField_translation.2,
    stateField_creation.2.2.2.1] at hz
  have he := LinearMap.congr_fun hz vacuum
  norm_num [b, create_vacuum, ket] at he
  have bad := congrArg (fun v : Fock => v {2}) he
  norm_num at bad

def family : Registration arena (type_of% @stateField_translation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_translation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), 0, ket {0}, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stateField_translation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Translation.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Translation.family
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
    (fun _ _ a n => _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1) * ((Y a) [[n]]) -
      ((Y a) [[n]]) * _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Translation

namespace Parity
abbrev signature : Signature where
  Params := ℤ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n a => parity * ((Y a) [[n]])) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Fock) (n : ℤ), R.readout () n a = ((Y (parity a)) [[n]]) * parity
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
private theorem parity_vacuum : parity vacuum = vacuum := by
  change parity (ket ∅) = ket ∅
  rw [parity_ket]
  simp
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h vacuum (-1)
  change (0 : Module.End ℂ Fock) = ((Y (parity vacuum)) [[-1]]) * parity at hz
  have he := LinearMap.congr_fun hz vacuum
  simp only [Module.End.mul_apply, parity_vacuum, stateField_creation.2.1] at he
  have bad := congrArg (fun v : Fock => v ∅) he
  norm_num [vacuum, ket] at bad
private theorem actual_dependence : actual.readout () (-1) vacuum ≠ actual.readout () (-1) 0 := by
  intro h
  have hz := LinearMap.congr_fun h vacuum
  change parity (((Y vacuum) [[-1]]) vacuum) = parity (((Y 0) [[-1]]) vacuum) at hz
  rw [stateField_creation.2.1, stateField_creation.2.1, parity_vacuum, map_zero] at hz
  simpa [vacuum, ket] using hz

def family : Registration arena (type_of% @stateField_parity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_parity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨-1, vacuum, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stateField_parity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Parity.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateField.Parity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => parity * ((Y a) [[n]])) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostStateField
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Parity
end Reg.D5.S3.Quantum.Fermionic.BcGhostStateField
