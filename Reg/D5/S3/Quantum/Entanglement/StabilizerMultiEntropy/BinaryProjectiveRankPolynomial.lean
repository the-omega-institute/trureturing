import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
import Mathlib.Algebra.Field.ULift

/-! Source audit of the normalized rank sum as an observation of the dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open scoped Classical

universe u
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ∀ R : Type u, Field R → R → R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ d => normalizedRankFamily d) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ R F _ => letI := F; (0 : R)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (d : ℕ),
    let observed := r.readout () () d
    ∀ {R : Type u} [F : Field R] (q : R), q ≠ 0 →
      observed R F q = ∏ j : Fin d, (1-(2 : R)^j.val/q)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h 0 (R := ULift.{u} ℚ) 1 one_ne_zero
  change (0 : ULift.{u} ℚ) = ∏ j : Fin 0, (1 - (2 : ULift.{u} ℚ)^j.val / 1) at hh
  simp at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨(),0,1,?_⟩
  intro h
  have hc := congrFun (congrFun (congrFun h (ULift.{u} ℚ)) inferInstance) 1
  change normalizedRankSum 0 (1 : ULift.{u} ℚ) = normalizedRankSum 1 (1 : ULift.{u} ℚ) at hc
  have h0 : normalizedRankSum 0 (1 : ULift.{u} ℚ) = 1 := by
    simpa [normalizedRankFamily] using (normalized_factor 0 (1 : ULift.{u} ℚ) one_ne_zero)
  have h1 : normalizedRankSum 1 (1 : ULift.{u} ℚ) = 0 := by
    simpa [normalizedRankFamily] using (normalized_factor 1 (1 : ULift.{u} ℚ) one_ne_zero)
  rw [h0,h1] at hc
  exact one_ne_zero hc

def source_registration : Registration arena.{u} (type_of% @normalized_factor.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_factor,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_factor.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial.normalized_factor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => normalizedRankFamily d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
