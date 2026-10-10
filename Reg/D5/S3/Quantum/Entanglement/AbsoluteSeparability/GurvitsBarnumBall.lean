import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall

abbrev matrixSignature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ Q => Q) (fun e => nomatch e)

theorem matrix_dependence : ObservationalDependence matrixSignature matrixActual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h (0, 0)) (0, 0)
  change (0 : ℂ) = 1 at he
  norm_num at he

abbrev vectorSignature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Fin p.1 × Fin p.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace TraceBound

abbrev traceSignature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization traceSignature :=
  realize traceSignature (fun _ _ H => (trace H).re) (fun e => nomatch e)

def rejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := traceSignature
  Law R := ∀ {m n : ℕ} (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    H.IsHermitian → blockPositive H →
      0 ≤ R.readout () ⟨m, n⟩ H ∧
        (∑ u, ∑ v, ‖H u v‖ ^ 2) ≤ (trace H).re ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (m := 1) (n := 1) 0 (by simp) (by
    intro a b
    simp [blockPositive])).1
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @frobSq_le_trace_sq_of_blockPositive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨frobSq_le_trace_sq_of_blockPositive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    change (trace (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)).re ≠
      (trace (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)).re
    norm_num [Matrix.trace]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@frobSq_le_trace_sq_of_blockPositive) (Realization traceSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.TraceBound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.TraceBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize traceSignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end TraceBound

namespace Ball

def rejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {m n : ℕ} (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    A.PosSemidef → ∀ (c : ℝ), 0 ≤ c →
      (∑ u, ∑ v, ‖(A - (c : ℂ) • 1) u v‖ ^ 2) ≤ c ^ 2 →
        separableCone (R.readout () ⟨m, n⟩ A)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) 0 PosSemidef.zero 0 (by norm_num) (by simp)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena (type_of% @separableCone_of_frob_ball) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨separableCone_of_frob_ball, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := matrix_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separableCone_of_frob_ball) (Realization matrixSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.Ball.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.Ball.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize matrixSignature matrixActual.readout matrixActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Ball

namespace RankOneComplement

def actual : Realization vectorSignature := realize vectorSignature
  (fun _ _ ψ => 1 - vecMulVec ψ (star ψ)) (fun e => nomatch e)

def rejected : Realization vectorSignature :=
  realize vectorSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := vectorSignature
  Law R := ∀ {m n : ℕ} (ψ : Fin m × Fin n → ℂ),
    (∑ u, ‖ψ u‖ ^ 2) = 1 → separableCone (R.readout () ⟨m, n⟩ ψ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) (fun _ => 1) (by simp)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena (type_of% @separableCone_one_sub_rankOne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separableCone_one_sub_rankOne, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrFun (congrFun h (0, 0)) (0, 0)
    change
      (1 - vecMulVec (fun _ : Fin 1 × Fin 1 => (0 : ℂ))
        (star (fun _ : Fin 1 × Fin 1 => (0 : ℂ)))) (0, 0) (0, 0) =
      (1 - vecMulVec (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
        (star (fun _ : Fin 1 × Fin 1 => (1 : ℂ)))) (0, 0) (0, 0) at he
    norm_num [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separableCone_one_sub_rankOne) (Realization vectorSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.RankOneComplement.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.RankOneComplement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize vectorSignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end RankOneComplement

namespace ProjectionRay

def rejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => (2 : ℂ) • 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {m n : ℕ} (Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    Q.IsHermitian → Q * Q = Q → ∀ (ell : ℝ), trace Q = (ell : ℂ) → 1 ≤ ell →
      separableCone (((ell : ℂ) + 1) • 1 - (2 : ℂ) • R.readout () ⟨m, n⟩ Q)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) 1 isHermitian_one (by simp) 1 (by simp) (by norm_num)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤
    (((1 : ℂ) + 1) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) -
      (2 : ℂ) • ((2 : ℂ) • 1)) (0, 0) (0, 0) at hd
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Complex.le_def] at hd

def family : Registration arena (type_of% @separableCone_scaled_one_sub_two_projection) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨separableCone_scaled_one_sub_two_projection, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := matrix_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separableCone_scaled_one_sub_two_projection) (Realization matrixSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.ProjectionRay.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.ProjectionRay.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize matrixSignature matrixActual.readout matrixActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end ProjectionRay

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
