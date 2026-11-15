import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

/-! Source-bound equality audits retain the complete all-L1 source telescopes. -/

namespace Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

open Matrix MeasureTheory Set
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open _root_.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Unit
  State _ := EReal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := EReal → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ left right => left = right) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ left right => left ≠ right) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : EReal) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

namespace Identification

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type v} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ),
    r.readout () () (allL1Value.{u} hf A B) (maximalValue hf A B)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let hf : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ioi 0)
  exact h hf (0 : Matrix (ULift.{v} Unit) _ ℂ) 0
    (allL1Value_eq_maximalValue hf _ _)

def source_registration : Registration arena.{u,v} (type_of% @allL1Value_eq_maximalValue.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@allL1Value_eq_maximalValue.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@allL1Value_eq_maximalValue.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.Identification.unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.Identification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Identification

namespace Sufficiency

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type v} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef),
    (let S := A + B
     let C := D5.S3.Quantum.Divergence.MaximalHockeyStickSupport.normalize S A
     let P := interiorProjection C
     (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) →
    r.readout () () (allL1Value.{u} hf A B) (hockeyValue hf A B)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let hf : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ioi 0)
  have hc : let S := (0 : Matrix (ULift.{v} Unit) _ ℂ) + 0
      let C := D5.S3.Quantum.Divergence.MaximalHockeyStickSupport.normalize S 0
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by simp
  exact h hf (0 : Matrix (ULift.{v} Unit) _ ℂ) 0
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero hc
    (D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq
      hf _ _ Matrix.PosSemidef.zero Matrix.PosSemidef.zero hc)

def source_registration : Registration arena.{u,v} (type_of% @D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.commute_implies_integrated_eq.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.Sufficiency.unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex.Sufficiency.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Sufficiency

end
end Reg.D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
