import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Bound
import Reg.Support.DependentFamily

/-! The three-factor gap reads the real trace of the commutator square. -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Bound

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV (balancedWords)
open _root_.RefinedBMV.Tracial (wordMean_three_trace_gap)
open LeanInformationAudit
open scoped ComplexOrder

noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ A : Type u, Σ cstar : CStarAlgebra A, Σ order : PartialOrder A,
    letI := cstar
    letI := order
    A →P[ℂ] ℂ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x =>
    letI := p.2.1
    letI := p.2.2.1
    (p.2.2.2 x).re) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [cstar : CStarAlgebra A] [order : PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (_hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (_ha : 0 ≤ a) (_hb : 0 ≤ b),
    3 * (R.readout () ⟨A, cstar, order, τ⟩ (star (a * b - b * a) * (a * b - b * a))) ^ 2 ≤
      40 * (τ (a * b)).re *
        (((balancedWords 3 3).map fun w =>
          τ ((w.map fun letter => if letter then a else b).prod)).sum /
          ((balancedWords 3 3).length : ℂ) - τ ((a * b) ^ 3)).re

private abbrev Scalar := ULift.{u} Unit → ℂ

private def scalarTrace : Scalar.{u} →P[ℂ] ℂ where
  toLinearMap := LinearMap.proj (⟨()⟩ : ULift.{u} Unit)
  monotone' := by
    intro a b hab
    change a ⟨()⟩ ≤ b ⟨()⟩
    exact hab ⟨()⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have impossible := h (A := Scalar.{u}) scalarTrace
    (fun a b => congrArg scalarTrace (mul_comm a b)) 0 0 le_rfl le_rfl
  norm_num [rejected, realize] at impossible

private theorem depends : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨Scalar.{u}, inferInstance, inferInstance, scalarTrace⟩, 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def gapFamily : Registration arena.{u} (type_of% @wordMean_three_trace_gap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wordMean_three_trace_gap.{u}, rejected, rejected_law⟩
  sensitivity :=
    ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
      fun e => nomatch e⟩
  dependence := depends

def gapRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@wordMean_three_trace_gap.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `RefinedBMV.Tracial.wordMean_three_trace_gap.__information_unit
  realizationName := ``gapFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨gapFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x =>
    letI := p.2.1
    letI := p.2.2.1
    (p.2.2.2 x).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Bound
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms gapRegistration

end
end Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Bound
