import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence
import Reg.Support.SingleDependentReadout

/-! The two readouts retain the left and right operands of each congruence inequality. -/

noncomputable section

universe u

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence

open _root_.DerivativeFreeHarmonicCongruence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit
open Matrix RHLinalg
open scoped ComplexOrder MatrixOrder

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev quadraticArena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (W X Q : Matrix ι ι ℂ) (_ : W.PosDef) (_ : X.IsHermitian) (_ : Q.IsHermitian)
    (_ : Q * Q = Q) (_ : Commute W Q) (t : ℝ),
    R.readout () () (2 * t * harmonicDelta X Q - t ^ 2 * rtrace (W⁻¹ * harmonicB X Q))
      (harmonicValue (CFC.sqrt W) X Q)

private abbrev optimizedArena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (W X Q : Matrix ι ι ℂ) (_ : W.PosDef) (_ : X.IsHermitian) (_ : Q.IsHermitian)
    (_ : Q * Q = Q) (_ : Commute W Q) (_ : 0 < harmonicDelta X Q),
    R.readout () () (harmonicDelta X Q ^ 2 / rtrace (W⁻¹ * harmonicB X Q))
      (harmonicValue (CFC.sqrt W) X Q)

private theorem rejected_quadratic : ¬ quadraticArena.{u}.Law rejected := by
  intro h
  let ι := ULift.{u} Unit
  exact @h ι inferInstance inferInstance 1 1 1 Matrix.PosDef.one
    Matrix.isHermitian_one Matrix.isHermitian_one (one_mul _) (Commute.refl _) 0

private theorem rejected_optimized : ¬ optimizedArena.{u}.Law rejected := by
  intro h
  let ι := ULift.{u} Unit
  have hδ : 0 < harmonicDelta (1 : Matrix ι ι ℂ) 1 := by
    unfold harmonicDelta
    rw [one_mul]
    have htrace : rtrace (1 : Matrix ι ι ℂ) = 1 := by
      simp [rtrace, Matrix.trace_one, Fintype.card_unique]
    rw [htrace]
    have hnonneg : 0 ≤
        _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.posTrace
          (-(1 : Matrix ι ι ℂ)) :=
      (RCLike.nonneg_iff.mp (CFC.posPart_nonneg (-(1 : Matrix ι ι ℂ))).posSemidef.trace_nonneg).1
    linarith
  exact @h ι inferInstance inferInstance 1 1 1 Matrix.PosDef.one
    Matrix.isHermitian_one Matrix.isHermitian_one (one_mul _) (Commute.refl _) hδ

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def quadraticFamily : Registration quadraticArena.{u}
    (type_of% @derivative_free_harmonic_congruence.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@derivative_free_harmonic_congruence.{u}, rejected, rejected_quadratic⟩
  sensitivity := sensitivity quadraticArena.Law actual rejected rejected_quadratic
  dependence := dependence

def optimizedFamily : Registration optimizedArena.{u}
    (type_of% @derivative_free_harmonic_congruence_optimized.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@derivative_free_harmonic_congruence_optimized.{u}, rejected, rejected_optimized⟩
  sensitivity := sensitivity optimizedArena.Law actual rejected rejected_optimized
  dependence := dependence

def quadraticAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@derivative_free_harmonic_congruence.{u}) (Realization signature) Unit Unit where
  unitName := `DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence.quadraticFamily
  realizationSource := none
  generated := false
  arena := .source ⟨quadraticArena⟩
  objectArena := .source ⟨quadraticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quadraticArena ⟨quadraticFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def optimizedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@derivative_free_harmonic_congruence_optimized.{u}) (Realization signature) Unit Unit where
  unitName := `DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence_optimized.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence.optimizedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨optimizedArena⟩
  objectArena := .source ⟨optimizedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source optimizedArena ⟨optimizedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence
