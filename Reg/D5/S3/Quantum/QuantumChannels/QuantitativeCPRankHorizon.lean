import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon

structure Parameters where
  d : ℕ
  T : CompletelyPositiveMap (CStarMatrix (Fin d) (Fin d) ℂ)
    (CStarMatrix (Fin d) (Fin d) ℂ)

abbrev signature : Signature where
  Params := Parameters
  State p := CStarMatrix (Fin p.d) (Fin p.d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p P => Real.sqrt ‖(1 - P) * p.T P * (1 - P)‖)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}
    (T : CompletelyPositiveMap (CStarMatrix (Fin d) (Fin d) ℂ)
      (CStarMatrix (Fin d) (Fin d) ℂ)) (_hT : T 1 ≤ 1)
    (P X σ : CStarMatrix (Fin d) (Fin d) ℂ)
    (_hP : IsStarProjection P) (_hXP : X ≤ P)
    (_hσ : 0 ≤ σ) (_hσtr : Matrix.trace (CStarMatrix.ofMatrix.symm σ) = 1),
    let α := R.readout () ⟨d, T⟩ P
    ∀ n : ℕ,
      T^[n] X ≤ P + (2 * (n : ℝ) * α) • 1 ∧
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[n] X))).re ≤
        (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * P))).re + 2 * (n : ℝ) * α

/-- Both readout states extend to the complete source hypotheses with the same map,
input and trace-one observation. -/
theorem sourceDependence : ∃ (p : Parameters)
    (P₀ P₁ X σ : CStarMatrix (Fin p.d) (Fin p.d) ℂ),
    p.T 1 ≤ 1 ∧ IsStarProjection P₀ ∧ IsStarProjection P₁ ∧
    X ≤ P₀ ∧ X ≤ P₁ ∧ 0 ≤ σ ∧
    Matrix.trace (CStarMatrix.ofMatrix.symm σ) = 1 ∧
    ∀ i, actual.readout i p P₀ ≠ actual.readout i p P₁ := by
  let T := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.reindexₐ ℂ ℂ (Equiv.swap (0 : Fin 2) 1))
  let P : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![1, 0; 0, 0]
  have hP : IsStarProjection P := by
    constructor
    · change P * P = P
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [P, CStarMatrix.mul_apply, Fin.sum_univ_two]
    · change star P = P
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [P, CStarMatrix.star_apply]
  have hT : T 1 ≤ 1 := by
    change (CStarMatrix.reindexₐ ℂ ℂ (Equiv.swap (0 : Fin 2) 1)) 1 ≤ 1
    rw [map_one]
  refine ⟨⟨2, T⟩, 0, P, 0, P, hT, IsStarProjection.zero _, hP,
    le_rfl, hP.nonneg, hP.nonneg, ?_, ?_⟩
  · change Matrix.trace (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 1
    norm_num [Matrix.trace, Fin.sum_univ_succ]
  · intro i
    change Real.sqrt ‖(1 - (0 : CStarMatrix (Fin 2) (Fin 2) ℂ)) *
      T 0 * (1 - 0)‖ ≠ Real.sqrt ‖(1 - P) * T P * (1 - P)‖
    simp only [map_zero, sub_zero, mul_zero, zero_mul, norm_zero, Real.sqrt_zero]
    intro hz
    have he := norm_eq_zero.mp ((Real.sqrt_eq_zero (norm_nonneg _)).mp hz.symm)
    have hentry := congrArg (fun Y : CStarMatrix (Fin 2) (Fin 2) ℂ =>
      Y 1 1) he
    have hswap : T P 1 1 = 1 := by rfl
    norm_num [CStarMatrix.mul_apply, Fin.sum_univ_two, P] at hentry
    exact zero_ne_one (hentry.symm.trans hswap)

def family : Registration arena (type_of% @coherent_compression_trace_transfer) := by
  let idCP := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (StarAlgHom.id ℂ (CStarMatrix (Fin 1) (Fin 1) ℂ))
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h idCP (by exact le_rfl) 0 0 1 (IsStarProjection.zero _)
      le_rfl zero_le_one (by simp [Matrix.trace]) 1
    have hh' := hh.2
    norm_num [rejected, realize, Function.iterate_succ_apply', idCP,
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap,
      Matrix.trace, Fin.sum_univ_succ] at hh'
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨coherent_compression_trace_transfer, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hbad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  · intro i
    obtain ⟨p, P₀, P₁, X, σ, hT, hP₀, hP₁, hX₀, hX₁, hσ, hσtr, hdep⟩ :=
      sourceDependence
    exact ⟨p, P₀, P₁, hdep i⟩

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@coherent_compression_trace_transfer)
      (type_of% (realize signature
        (fun _ p P => Real.sqrt ‖(1 - P) * p.T P * (1 - P)‖)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon.coherent_compression_trace_transfer.information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon.family
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
    (fun _ p P => Real.sqrt ‖(1 - P) * p.T P * (1 - P)‖)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
