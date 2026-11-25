import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit

/-! Source-bound registration of the trace-log inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit

namespace Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (_ : ∀ i, (X i).PosSemidef) (_ : ∀ i, (X i).trace = 1),
    let A := ∑ i, (![88 / 141, 25 / 141, 28 / 141] : Fin 3 → ℝ) i • X i
    let C := ∑ i, (![66 / 141, 15 / 141, 12 / 141] : Fin 3 → ℝ) i • X i
    R.readout () () (A * (CFC.log A - CFC.log C)).trace.re
      (((113 / 141 : ℝ) * Real.log (113 / 81) + (28 / 141) * Real.log (7 / 3)) -
        (3 * (1 - (X 0 * X 1).trace.re) + 11 * (X 0 * X 2).trace.re) / 63360)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : Fin 2 → ℂ := ![1, 0]
  let P := Matrix.vecMulVec v (star v)
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have ht : P.trace = 1 := by
    rw [Matrix.trace_vecMulVec]
    simp [v, dotProduct, Fin.sum_univ_two]
  exact h (fun _ => P) (fun _ => hP) (fun _ => ht)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h' := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at h'
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (h'.mp le_rfl)

def family : Registration arena (type_of% @traceLog_le_benchmark_sub_margin) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceLog_le_benchmark_sub_margin, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@traceLog_le_benchmark_sub_margin) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit.traceLog_le_benchmark_sub_margin.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciMixedQubit
