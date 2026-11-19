import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiConditionalBKM
import Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Divergence.UmegakiKernelContraction
open _root_.D5.S3.Quantum.Divergence.UmegakiConditionalBKM
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction (Q identityChannel identity_endpoint)
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiConditionalBKM

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {R a : Type u} [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a]
      {b : Type u} [Fintype b] [DecidableEq b]
      (N : QuantumChannel a b) (c : ℝ) (hN : (act N 1).PosDef)
      (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound N c)
      (ρ σ : DensityState (R × a))
      (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef)
      (hσ : (CStarMatrix.ofMatrix.symm σ.1).PosDef),
    F.readout () ()
      (finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) -
        finiteTraceLogRelativeEntropy (marginalRight (referenceState N ρ))
          (marginalRight (referenceState N σ)))
      (c * (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)))

theorem source_equivalence :
    (type_of% @faithful_conditional_relativeEntropy_contraction.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private def faithfulSingleton : DensityState (Q.{u} × Q.{u}) :=
  ⟨1, zero_le_one, by
    change Matrix.trace (1 : Matrix (Q × Q) (Q × Q) ℂ) = 1
    simp [Matrix.trace_one]⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 1 Matrix.PosDef.one (by simp)
    identity_endpoint faithfulSingleton faithfulSingleton Matrix.PosDef.one Matrix.PosDef.one

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u}
    (type_of% @faithful_conditional_relativeEntropy_contraction.{u}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@faithful_conditional_relativeEntropy_contraction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@faithful_conditional_relativeEntropy_contraction.{u})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalBKM.faithful_conditional_relativeEntropy_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalBKM.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiConditionalBKM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def residualActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private abbrev residualArena : Arena where
  signature := signature
  Law F := ∀ {R a : Type u} [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a] [Nonempty a]
      (Z H : Matrix (R × a) (R × a) ℂ) (t : ℝ)
      (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () ()
      (_root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q Z H t -
        _root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q (partialTraceRight Z) (partialTraceRight H) t)
      (_root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q Z (residual Z H t) t)

private theorem residual_equivalence :
    (type_of% @quadratic_difference_eq_residual.{u}) ↔ residualArena.{u}.Law residualActual :=
  Iff.rfl

private theorem residual_rejected : ¬ residualArena.{u}.Law rejected := by
  intro h
  exact h (R := Q) (a := Q) 1 0 0 Matrix.PosDef.one (by simp)

private theorem residual_dependence : ObservationalDependence signature residualActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [residualActual, realize] at hh

def residualFamily : Registration residualArena.{u}
    (type_of% @quadratic_difference_eq_residual.{u}) where
  actual := residualActual
  bridge := residual_equivalence
  variation := ⟨@quadratic_difference_eq_residual, rejected, residual_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    residualArena.{u}.Law residualActual rejected residual_rejected
  dependence := residual_dependence

def residualAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quadratic_difference_eq_residual.{u})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalBKM.quadratic_difference_eq_residual.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residualFamily
  realizationSource := none
  generated := false
  arena := .source ⟨residualArena.{u}⟩
  objectArena := .source ⟨residualArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residualArena.{u} ⟨residualFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiConditionalBKM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiConditionalBKM
