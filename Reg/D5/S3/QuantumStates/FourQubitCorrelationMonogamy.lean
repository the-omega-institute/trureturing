import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumStates.FourQubitCorrelationMonogamy
import Reg.Support.DependentFamily

/-! Squared-correlation readout on normalized four-qubit vectors. -/

namespace Reg.D5.S3.QuantumStates.FourQubitCorrelationMonogamy

open _root_.D5.S3.QuantumStates.FourQubitCorrelationMonogamy
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.Quantum.PureState.PureStateHandshake
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := (Fin 4 → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ ψ => ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation ψ X i j ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ ψ : (Fin 4 → Fin 2) → ℂ, star ψ ⬝ᵥ ψ = 1 → r.readout () () ψ ≤ 3

private def productVector : (Fin 4 → Fin 2) → ℂ := Pi.single ![0, 0, 0, 0] 1

private def parityVector : (Fin 4 → Fin 2) → ℂ :=
  Pi.single ![0, 0, 0, 0] (1 / 2) + Pi.single ![0, 0, 1, 1] (1 / 2) +
    Pi.single ![0, 1, 0, 1] (1 / 2) + Pi.single ![0, 1, 1, 0] (1 / 2)

private theorem product_normalized : star productVector ⬝ᵥ productVector = 1 := by
  simp [productVector, Pi.star_single]

private theorem trace_single (a b : Fin 4 → Fin 2) (x y : ℂ)
    (M : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ) :
    trace (vecMulVec (Pi.single a x) (Pi.single b y) * M) = x * (y * M b a) := by
  simp [vecMulVec_mul, trace_vecMulVec, single_dotProduct, mul_left_comm]

private theorem product_value :
    (∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation productVector X i j ^ 2) = 3 := by
  norm_num [correlation, productVector, rankOneDensity, Pi.star_single, trace_single,
    Fin.sum_univ_succ, wordOp, tensorOp, Fin.prod_univ_succ, twoBodyWord,
    pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem parity_value :
    (∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation parityVector X i j ^ 2) = 0 := by
  norm_num [correlation, parityVector, rankOneDensity, star_add, Pi.star_single,
    add_vecMulVec, vecMulVec_add, Matrix.add_mul, trace_add, trace_single,
    Fin.sum_univ_succ, wordOp, tensorOp, Fin.prod_univ_succ, twoBodyWord,
    pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h productVector product_normalized
  change (4 : ℝ) ≤ 3 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), productVector, parityVector, ?_⟩
  change (∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation productVector X i j ^ 2) ≠
    ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation parityVector X i j ^ 2
  rw [product_value, parity_value]
  norm_num

def source_registration :
    Registration arena _root_.D5.S3.QuantumStates.FourQubitCorrelationMonogamy.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.QuantumStates.FourQubitCorrelationMonogamy.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumStates.FourQubitCorrelationMonogamy.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumStates.FourQubitCorrelationMonogamy.unit
  realizationName := `Reg.D5.S3.QuantumStates.FourQubitCorrelationMonogamy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ ψ => ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation ψ X i j ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumStates.FourQubitCorrelationMonogamy
    definition := some {
      owner := `D5.S3.QuantumStates.FourQubitCorrelationMonogamy
      name := `D5.S3.QuantumStates.FourQubitCorrelationMonogamy.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumStates.FourQubitCorrelationMonogamy
