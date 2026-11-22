import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal

open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Stream → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => shiftedMagnitude e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 1601) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (e : ℤ) (δ : ℝ), 0 < δ → ∀ j : ℕ,
    streamMeasure {ω : Stream | (|(e : ℝ)| + (max 1 (20 / δ))^2) *
      ((j : ℝ) + 1)^2 < R.readout () () e j ω} ≤ ENNReal.ofReal δ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 (1 / 2) (by norm_num) 0
  change streamMeasure {ω : Stream | (|((0 : ℤ) : ℝ)| + (max 1 (20 / (1 / 2)))^2) *
      (((0 : ℕ) : ℝ) + 1)^2 < (1601 : ℝ)} ≤ ENNReal.ofReal (1 / 2) at hz
  have he : ({ω : Stream | (|((0 : ℤ) : ℝ)| + (max 1 (20 / (1 / 2)))^2) *
      (((0 : ℕ) : ℝ) + 1)^2 < (1601 : ℝ)} : Set Stream) = Set.univ := by
    ext ω
    norm_num
  rw [he, measure_univ, ← ENNReal.ofReal_one] at hz
  exact (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2) ((ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hz)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  let ω : Stream := fun _ => ⟨false, .terminal 0
    (_root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel.indecomposableWitness false 1)⟩
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) ω
  change shiftedMagnitude 0 0 ω = shiftedMagnitude 1 0 ω at he
  norm_num [shiftedMagnitude, streamDiscrepancy] at he

def family : Registration arena (type_of% @actual_uniform_quadratic_marginal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_uniform_quadratic_marginal, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_uniform_quadratic_marginal) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => shiftedMagnitude e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
    definition := none
    coordinates := #[]
    readouts := #[{
      path :=  #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
