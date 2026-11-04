import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate

/-! Faithful field-family registration attempt. The source occurrence selector
is still absent; no declared-validation status is claimed. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped VertexOperator
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateField
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
open _root_.D5.S3.VertexAlgebra.FieldNormalProduct
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
def rejected : Realization signature := realize signature
  (fun _ _ _ => identityField) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : Fock) (p q : ℕ),
    parity a = (-1 : ℂ) ^ p • a → parity b = (-1 : ℂ) ^ q • b → ∀ (r n : ℤ),
    let left : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((R.readout () () a) [[r - (i : ℤ)]])
          (((R.readout () () b) [[n + (i : ℤ)]]) c))
    let right : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((R.readout () () b) [[r + n - (i : ℤ)]])
          (((R.readout () () a) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (((R.readout () () (((R.readout () () a) [[r]]) b)) [[n]]) c) =
        (∑ᶠ i : ℕ, left i) -
          (((-1 : ℂ) ^ r) * ((-1 : ℂ) ^ (p * q))) • (∑ᶠ i : ℕ, right i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have law := h 0 0 vacuum 0 0 (by simp) (by simp) (-2) (-1)
  have modes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  have first (i : ℕ) : (-2 : ℤ) - i ≠ -1 := by omega
  have second (i : ℕ) : (i : ℤ) ≠ -1 := by omega
  have bad := law.2.2
  simp [rejected, realize, modes, first, second] at bad
  simpa [vacuum, ket] using bad
private theorem actual_dependence : actual.readout () () vacuum ≠ actual.readout () () 0 := by
  intro h
  have hz := congrArg (fun A : VertexOperator ℂ Fock => (A [[-1]]) vacuum) h
  change ((Y vacuum) [[-1]]) vacuum = ((Y 0) [[-1]]) vacuum at hz
  rw [stateField_creation.2.1, stateField_creation.2.1] at hz
  simpa [vacuum, ket] using hz

def family : Registration arena (type_of% @stateField_iterate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_iterate, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), vacuum, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stateField_iterate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate.family
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
end Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
