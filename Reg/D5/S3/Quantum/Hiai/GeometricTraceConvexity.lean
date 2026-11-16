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
  Params := Type u
  State d := Set (Matrix d d ℂ × Matrix d d ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := (Matrix d d ℂ × Matrix d d ℂ → ℝ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s f => ConvexOn ℝ s f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [ft : Fintype d] [de : DecidableEq d] {α p : ℝ},
    α ∈ Set.Icc (1 : ℝ) 2 → p ∈ Set.Icc (1 / 2 : ℝ) 1 →
    R.readout () d (@supportPairDomain d ft)
      (fun z => geometricTrace α p z.1 z.2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} (Fin 1)) (α := 1) (p := 1)
    (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let d := ULift.{u} (Fin 1)
  let f : Matrix d d ℂ × Matrix d d ℂ → ℝ := fun z => -((Matrix.trace z.1).re ^ 2)
  refine ⟨d, ∅, Set.univ, ?_⟩
  intro he
  have hz : ConvexOn ℝ (∅ : Set (Matrix d d ℂ × Matrix d d ℂ)) f :=
    ⟨convex_empty, by intro x hx; exact False.elim hx⟩
  have hc : ConvexOn ℝ (Set.univ : Set (Matrix d d ℂ × Matrix d d ℂ)) f :=
    Eq.mp (congrFun he f) hz
  have hi := hc.2 (x := (0, 0)) (y := (1, 1)) (by trivial) (by trivial)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [f, Matrix.trace] at hi

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
  localNames := false
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
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
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
