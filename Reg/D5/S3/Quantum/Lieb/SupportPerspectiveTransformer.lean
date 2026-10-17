/- Source candidates only. Current kernel, source reconstruction, enrollment
and binding checks are pending; no registration is asserted validated. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
import Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Lieb.PositiveMapJensen
open LownerHeinzTheorem JensenOperatorInequality LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
universe u v

open _root_.D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open _root_.D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open Reg.D5.S3.Quantum.Lieb.PositiveMapJensen

namespace Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransformer

namespace Transformer
open FunctionObservation

def arena : Arena where
  signature := signature
  Law r := ∀ {a b : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {f : ℝ → ℝ}
    (hconv : OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix a a ℂ →ₚ[ℂ] Matrix b b ℂ)
    (A B : Matrix a a ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ x : a → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0),
    supportedPerspective (r.readout () () f) (Φ A) (Φ B) ≤
      Φ (supportedPerspective f A B)

private theorem actual_law : arena.{u}.Law actual := by
  exact @supportedPerspective_transformer.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  have h := hall (f := fun _ => 0) (@zero_convex.{u}) continuousOn_const
    (PositiveLinearMap.id ℂ (Matrix n n ℂ)) 0 1
    Matrix.PosSemidef.zero Matrix.PosSemidef.one (by intro x hx; simp)
  apply not_one_le_zero (n := n)
  simpa [rejected, realize, supportedPerspective] using h

def family : Registration arena.{u} (type_of% (@supportedPerspective_transformer.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- Source occurrence coordinates are authored candidates, pending extraction. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@supportedPerspective_transformer.{u}) (Realization FunctionObservation.signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransformer.Transformer.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransformer.Transformer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FunctionObservation.signature
    FunctionObservation.actual.readout FunctionObservation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Transformer

end Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
