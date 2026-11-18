import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.CurvatureAffineRigidity
import Reg.Support.DependentFamily

/-! Exact source-law bridge for the curvature-support supplier.
This bridge alone is not a four-slot declared-validated registration. -/

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Analytic.Convexity.CurvatureAffineRigidity

noncomputable section
namespace Reg.D5.S3.Analytic.Convexity.CurvatureAffineRigidity

structure Inputs where
  f : ℝ → ℝ
  convex : ConvexOn ℝ (Ioi 0) f

abbrev signature : Signature where
  Params := Unit
  State _ := Inputs
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure Positive
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => curvature a.convex) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Inputs,
    (∀ (u v α β : ℝ), 0 < u → u < v →
      (∀ x ∈ Ioo u v, a.f x = α*x+β) → ∀ x ∈ Ioi 0, a.f x = α*x+β) →
    (¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, a.f x = α*x+β) →
    (R.readout () () a).support = univ

theorem source_bridge : (type_of% (@full_support_of_affine_rigidity)) ↔ arena.Law actual := by
  constructor
  · intro h a hr hn
    exact h a.convex hr hn
  · intro h f hf hr hn
    exact h ⟨f, hf⟩ hr hn

#print axioms source_bridge

end Reg.D5.S3.Analytic.Convexity.CurvatureAffineRigidity
