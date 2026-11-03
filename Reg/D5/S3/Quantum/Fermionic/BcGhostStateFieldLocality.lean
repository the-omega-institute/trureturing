import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality

/-! Faithful field-family registration attempt. The source occurrence selector
is still absent; no declared-validation status is claimed. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped VertexOperator
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateField
open _root_.D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
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
  Law R := ∀ (a b : Fock) (p q : ℕ),
    parity a = (-1 : ℂ) ^ p • a → parity b = (-1 : ℂ) ^ q • b →
      ∃ N, delta^[N] (fun m n =>
        ((R.readout () () a) [[m]]) * ((R.readout () () b) [[n]]) -
          (-1 : ℂ) ^ (p * q) •
            (((R.readout () () b) [[n]]) * ((R.readout () () a) [[m]]))) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := h 0 0 1 1 (by simp) (by simp)
  let D : ℤ → ℤ → Module.End ℂ Fock := fun m n =>
    ((identityField : VertexOperator ℂ Fock) [[m]]) * (identityField [[n]]) +
      (identityField [[n]]) * (identityField [[m]])
  simp only [one_mul, pow_one, neg_one_smul, sub_neg_eq_add] at hN
  change delta^[N] D = 0 at hN
  have modes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  have tail (k : ℕ) (m n : ℤ) (hn : 0 ≤ n) : delta^[k] D m n = 0 := by
    induction k generalizing m n with
    | zero => simp [D, modes, show n ≠ -1 by omega]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change delta^[k] D (m + 1) n - delta^[k] D m (n + 1) = 0
      rw [ih _ _ hn, ih _ _ (by omega), sub_self]
  have head (k : ℕ) (m : ℤ) : delta^[k] D m (-1) =
      if m + k = -1 then (2 : ℂ) • (LinearMap.id : Module.End ℂ Fock) else 0 := by
    induction k generalizing m with
    | zero =>
      simp only [Function.iterate_zero_apply, D, modes, Nat.cast_zero, add_zero]
      split_ifs <;> simp [Module.End.mul_eq_comp, two_smul]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change delta^[k] D (m + 1) (-1) - delta^[k] D m 0 = _
      rw [tail k m 0 (by omega), sub_zero, ih]
      rw [show m + 1 + (k : ℤ) = m + (k + 1 : ℕ) by push_cast; omega]
  have bad := congrFun (congrFun hN (-1 - N)) (-1)
  rw [head, if_pos (by omega)] at bad
  have vector := congrArg (fun A : Module.End ℂ Fock => (A vacuum) ∅) bad
  norm_num [vacuum, ket] at vector
private theorem actual_dependence : actual.readout () () vacuum ≠ actual.readout () () 0 := by
  intro h
  have hz := congrArg (fun A : VertexOperator ℂ Fock => (A [[-1]]) vacuum) h
  change ((Y vacuum) [[-1]]) vacuum = ((Y 0) [[-1]]) vacuum at hz
  rw [stateField_creation.2.1, stateField_creation.2.1] at hz
  simpa [vacuum, ket] using hz

def family : Registration arena (type_of% @stateField_locality) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_locality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨(), vacuum, 0, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@stateField_locality) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality.family
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
end Reg.D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
