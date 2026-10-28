import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-readout registration for the actual full-axis integral budget. -/

noncomputable section
universe u v
open Matrix MeasureTheory Set
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget

/-- Observe the integrability assertion and the actual integral inequality together. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ),
    let M := supported_relative_modular_model Φ ρ σ support
    let w : ℝ → (M.data.J × M.data.I → ℂ) := fun t =>
      (M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
        M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t * (star (w t) ⬝ᵥ w t).re) (Ioi 0))
      ((∫ t in Ioi (0 : ℝ), t * (star (w t) ⬝ᵥ w t).re) ≤
        finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ : DensityState a := ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag, CStarMatrix.one_apply_eq]⟩
  let Φ : QuantumChannel a b := {
    toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b))
    trace_preserving := by
      intro X
      change Matrix.trace (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b) X) = Matrix.trace X
      simp [Matrix.trace, Matrix.diag, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply]
      change X ((Equiv.ofUnique a b).symm default) ((Equiv.ofUnique a b).symm default) =
        X default default
      simp only [Subsingleton.elim ((Equiv.ofUnique a b).symm default) (default : a)] }
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance Φ ρ ρ (supportContained_refl ρ)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @entropy_defect_resolvent_integral_budget.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_defect_resolvent_integral_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_defect_resolvent_integral_budget.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
