import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.OperatorConvexCurvature
import Reg.Support.DependentFamily

/-! Exact source-law bridges retaining the domain-aware CFC hypotheses.
The bridges alone are not four-slot declared-validated registrations. -/

open Set Matrix MeasureTheory LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature

noncomputable section
namespace Reg.D5.S3.Quantum.Lieb.OperatorConvexCurvature

structure MatrixInputs where
  f : ℝ → ℝ
  convex : ConvexOn ℝ (Ioi 0) f
  matrixConvex : LownerHeinzCore.OperatorConvexOn
    (𝓐 := Matrix (Fin 2) (Fin 2) ℂ) (Ioi 0) f

abbrev affineSignature : Signature where
  Params := MatrixInputs
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def affineActual : Realization affineSignature :=
  realize affineSignature (fun _ a x => a.f x) (fun e => nomatch e)

abbrev affineArena : Arena where
  signature := affineSignature
  Law R := ∀ (p : MatrixInputs) (a b α γ : ℝ), 0 < a → a < b →
    (∀ x ∈ Ioo a b, p.f x = α * x + γ) →
    ∀ x ∈ Ioi 0, R.readout () p x = α * x + γ

theorem affine_source_bridge : (type_of% (@affine_of_matrixConvex)) ↔
    affineArena.Law affineActual := by
  constructor
  · intro h p a b α γ ha hab he
    exact h p.convex p.matrixConvex a b α γ ha hab he
  · intro h f hf hm a b α γ ha hab he
    exact h ⟨f, hf, hm⟩ a b α γ ha hab he

theorem convex_source_bridge : (type_of% (@convexOn_of_operatorConvexOnAll)) ↔
    ∀ {f : ℝ → ℝ}, LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f →
      ConvexOn ℝ (Ioi 0) f := Iff.rfl

structure OperatorInputs where
  f : ℝ → ℝ
  operatorConvex : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f
  convex : ConvexOn ℝ (Ioi 0) f

abbrev curvatureSignature : Signature where
  Params := Unit
  State _ := OperatorInputs
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure Positive
  Anchor := Empty
  finiteAnchor := inferInstance

def curvatureActual : Realization curvatureSignature :=
  realize curvatureSignature (fun _ _ p => curvature p.convex) (fun e => nomatch e)

abbrev curvatureArena : Arena where
  signature := curvatureSignature
  Law R := ∀ p : OperatorInputs,
    (¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, p.f x = α * x + β) →
    (R.readout () () p).support = univ

theorem curvature_source_bridge : (type_of% (@operatorConvex_curvature_full_support)) ↔
    curvatureArena.Law curvatureActual := by
  constructor
  · intro h p hn
    exact h (@p.operatorConvex) hn
  · intro h f hc hn
    exact h ⟨f, @hc, convexOn_of_operatorConvexOnAll (f := f) (@hc)⟩ hn

#print axioms affine_source_bridge
#print axioms convex_source_bridge
#print axioms curvature_source_bridge

end Reg.D5.S3.Quantum.Lieb.OperatorConvexCurvature
