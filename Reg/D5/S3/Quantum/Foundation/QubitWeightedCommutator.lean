import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.QubitWeightedCommutator

/-! The complete qubit inequality as a family of Frobenius commutator readouts. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open _root_.D5.S3.Quantum.Foundation.QubitWeightedCommutator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Foundation.QubitWeightedCommutator

abbrev Q := Matrix (Fin 2) (Fin 2) ℂ

abbrev signature : Signature where
  Params := Q
  State _ := Q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X W => ‖X * W - W * X‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X W b : Q) (_hb : b.PosSemidef) (_ht : b.trace = 1),
    R.readout () X W ≤
      Real.sqrt 2 * ‖CFC.sqrt b * (X * W - W * X)‖ +
        (1 + Real.sqrt 2) * ‖X * Wᴴ - Wᴴ * X‖

theorem source_equivalence :
    (type_of% @qubit_weighted_commutator_bound) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let b : Q := Matrix.diagonal ![1, 0]
  have hb : b.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  have ht : b.trace = 1 := by norm_num [b, Matrix.trace_fin_two]
  have hh := h 0 0 b hb ht
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let W : Q := !![0, 1; 0, 0]
  let X : Q := !![1, 0; 0, 0]
  refine ⟨X, 0, W, ?_⟩
  change ‖X * (0 : Q) - 0 * X‖ ≠ ‖X * W - W * X‖
  simp only [zero_mul, mul_zero, sub_zero, norm_zero, ne_eq, eq_comm (a := (0 : ℝ)),
    norm_eq_zero]
  intro he
  have hh := congrArg (fun A : Q => A 0 1) he
  norm_num [X, W, Matrix.mul_apply, Fin.sum_univ_two] at hh

def family : Registration arena (type_of% @qubit_weighted_commutator_bound) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨qubit_weighted_commutator_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@qubit_weighted_commutator_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.QubitWeightedCommutator.qubit_weighted_commutator_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.QubitWeightedCommutator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X W => ‖X * W - W * X‖)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.QubitWeightedCommutator
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_equivalence
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Foundation.QubitWeightedCommutator
