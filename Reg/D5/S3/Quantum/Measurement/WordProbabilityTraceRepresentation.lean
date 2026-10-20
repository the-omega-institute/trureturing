import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation
import Reg.Support.DependentFamily

/-! A dependent-family audit of the operational word probability trace readout. -/

open scoped CStarAlgebra ComplexOrder

namespace Reg.D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation

open _root_.D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation
open _root_.D5.S3.Quantum.Fibers.OperatorSystemTowerStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

abbrev signature : Signature where
  Params := ℕ
  State d := MatrixAlgebra (Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ state => Matrix.trace state) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {Alphabet : Type u}
    (instrument : Alphabet → MatrixAlgebra (Fin d) →CP MatrixAlgebra (Fin d))
    (state : MatrixAlgebra (Fin d)) (word : List Alphabet),
    operationalWordProbability instrument state word =
      R.readout () d
        (word.foldl (fun current generator => instrument generator current) state)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (d := 1) (Alphabet := PEmpty)
    (fun generator => nomatch generator) 0 []
  norm_num [operationalWordProbability, rejected, realize, Matrix.trace, Matrix.diag,
    CStarMatrix.zero_apply] at hz

def family : Registration arena.{u}
    (type_of% (@operational_probability_eq_trace_foldl.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@operational_probability_eq_trace_foldl.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl,
        rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
      Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)
    norm_num [Matrix.trace_one]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@operational_probability_eq_trace_foldl.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ state => Matrix.trace state)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation
