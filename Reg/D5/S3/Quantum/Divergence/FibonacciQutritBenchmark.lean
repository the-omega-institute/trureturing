import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.FibonacciQutritBenchmark

/-! Source-bound registration of the benchmark value and the positive-reference bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
open private Mat matrix traceLog benchmark ray diagReal ray_sum
  from D5.S3.Quantum.Divergence.FibonacciQutritBenchmark

namespace Reg.D5.S3.Quantum.Divergence.FibonacciQutritBenchmark

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace attainment

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

set_option linter.unusedVariables false in
abbrev arena : Arena where
  signature := signature
  Law R' := ∀ (a b c e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e),
    ∃ P Q R : DensityState (Fin 3),
      matrix P * matrix Q = 0 ∧ matrix P * matrix R = 0 ∧ matrix Q * matrix R = 0 ∧
      ((a + b) • matrix P + c • matrix Q + e • matrix R).PosDef ∧
      R'.readout () ()
        (traceLog ((4 / 3 * a + 5 / 3 * b) • matrix P + (7 / 3 * c) • matrix Q)
          ((a + b) • matrix P + c • matrix Q + e • matrix R)) (benchmark a b c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, hf⟩ := h 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at h
  have hfalse := h.mp (rfl : (0 : ℝ) = 0)
  norm_num at hfalse

def family : Registration arena (type_of% @classical_benchmark_attained) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@classical_benchmark_attained, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classical_benchmark_attained) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FibonacciQutritBenchmark.classical_benchmark_attained.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritBenchmark.attainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end attainment

namespace comparison

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

set_option linter.unusedVariables false in
abbrev arena : Arena where
  signature := signature
  Law R' := ∀ (a b c e : ℝ) (X₁ X₂ X₃ X₀ : DensityState (Fin 3))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hγ : a + b + c + e = 1) (hp : 4 / 3 * a + 5 / 3 * b + 7 / 3 * c = 1)
    (hemax : e ≤ 8 / 19) (hbmax : b ≤ e / 2) (hsmin : 11 / 19 ≤ a + b + c)
    (hemin : (a + b + c) / 3 ≤ e),
    let C := a • matrix X₁ + b • matrix X₂ + c • matrix X₃
    let A := (4 / 3 * a) • matrix X₁ + (5 / 3 * b) • matrix X₂ + (7 / 3 * c) • matrix X₃
    let B := C + e • matrix X₀
    C.PosDef →
    R'.readout () () (traceLog A C) (benchmark a b c + 1 / 114) ∧
      (benchmark a b c ≤ traceLog A B →
        (A * (CFC.log B - CFC.log C)).trace.re ≤ 1 / 114 ∧
        ∃ (T : Mat (Fin 3) →ₗ[ℝ] Mat (Fin 2 ⊕ Unit))
          (Y₁ Y₂ Y₃ Y₀ : DensityState (Fin 2 ⊕ Unit)),
          matrix Y₁ = T (matrix X₁) ∧ matrix Y₂ = T (matrix X₂) ∧ matrix Y₃ = T (matrix X₃) ∧
          let C' := a • matrix Y₁ + b • matrix Y₂ + c • matrix Y₃
          let A' := (4 / 3 * a) • matrix Y₁ + (5 / 3 * b) • matrix Y₂ + (7 / 3 * c) • matrix Y₃
          let B' := C' + e • matrix Y₀
          C'.rank ≤ 2 ∧ B'.PosDef ∧ traceLog A B < traceLog A' B')

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hC : ((1 / 3 : ℝ) • matrix (ray 0) + (1 / 10 : ℝ) • matrix (ray 1) +
      (1 / 6 : ℝ) • matrix (ray 2)).PosDef := by
    rw [ray_sum]
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    fin_cases i <;> norm_num
  exact (h (1 / 3) (1 / 10) (1 / 6) (2 / 5) (ray 0) (ray 1) (ray 2) (ray 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hC).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at h
  have hfalse := h.mp (le_rfl : (0 : ℝ) ≤ 0)
  norm_num at hfalse

def family : Registration arena (type_of% @full_rank_benchmark_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_rank_benchmark_comparison, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_rank_benchmark_comparison) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FibonacciQutritBenchmark.full_rank_benchmark_comparison.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritBenchmark.comparison.family
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
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end comparison

end Reg.D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
