import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Hiai.GeometricTraceConvexity
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Hiai.GeometricTraceConvexity
open D5.S3.Quantum.Hiai.InverseMeanVariational
open D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Hiai.GeometricTraceConvexity

abbrev signature : Signature where
  Params := Σ d : Type u, Σ _ : Fintype d, Σ _ : DecidableEq d, Σ _ : ℝ, ℝ
  State p := Matrix p.1 p.1 ℂ × Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z =>
    @geometricTrace p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 z.1 z.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p z =>
    letI : Fintype p.1 := p.2.1;
    -((Matrix.trace z.1).re ^ 2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [ft : Fintype d] [de : DecidableEq d] {α p : ℝ},
    α ∈ Set.Icc (1 : ℝ) 2 → p ∈ Set.Icc (1 / 2 : ℝ) 1 →
    ConvexOn ℝ (@supportPairDomain d ft) (R.readout () ⟨d, ft, de, α, p⟩)

private theorem zero_mem {d : Type u} [Fintype d] [DecidableEq d] :
    (0, 0) ∈ (supportPairDomain : Set (Matrix d d ℂ × Matrix d d ℂ)) := by
  exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero, by simp⟩

private theorem one_mem {d : Type u} [Fintype d] [DecidableEq d] :
    (1, 1) ∈ (supportPairDomain : Set (Matrix d d ℂ × Matrix d d ℂ)) := by
  exact ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one, fun _ h => h⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc := h (d := ULift.{u} (Fin 1)) (α := 1) (p := 1)
    (by norm_num) (by norm_num)
  have hi := hc.2 zero_mem one_mem
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [rejected, realize, Matrix.trace] at hi

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 1), inferInstance, inferInstance, 1, 1⟩, (0, 0), (1, 1), ?_⟩
  change geometricTrace 1 1 (0 : Matrix (ULift.{u} (Fin 1)) _ ℂ) 0 ≠
    geometricTrace 1 1 (1 : Matrix (ULift.{u} (Fin 1)) _ ℂ) 1
  letI : Pow (Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) ℝ := ⟨CFC.rpow⟩
  have hz (q : ℝ) (hq : q ≠ 0) :
      (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) ^ q = 0 :=
    CFC.zero_rpow hq
  norm_num [geometricTrace, geometricMean, tracePower, Matrix.trace,
    hz, CFC.one_rpow]

def family : Registration arena.{u} (type_of% (@geometric_trace_support_convex.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@geometric_trace_support_convex, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@geometric_trace_support_convex.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Hiai.GeometricTraceConvexity.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.GeometricTraceConvexity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.GeometricTraceConvexity
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Hiai.GeometricTraceConvexity
