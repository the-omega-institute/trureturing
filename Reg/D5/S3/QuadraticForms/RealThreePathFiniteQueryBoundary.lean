import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary
import Reg.Support.DependentFamily

/-! The original menu observation controls the finite closure in the source statement. -/

open _root_.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary
open _root_.D5.S3.QuadraticForms.RealThreePathPolar
open _root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ContDiff

namespace Reg.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Finset (ℂ × ℂ × ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset (ℂ × ℂ × ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ menu => menu) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law Z := ∀ (menu : Finset (ℂ × ℂ × ℝ)) (ε : ℝ) (_hε : 0 < ε),
    let S := phaseClosure ((Z.readout () () menu).biUnion readPoints)
    ∃ q : ℂ → ℝ, q = perturbedReadout S ε ∧
    (0 ∈ S) ∧ (∀ r ∈ menu, readPoints r ⊆ S) ∧
    ContDiff ℝ ∞ q ∧ (∀ z, 0 ≤ q z) ∧ (∀ z, z ≠ 0 → 0 < q z) ∧
    q 0 = 0 ∧ (∀ z, q (omega * z) = q z) ∧ (∀ z, q (-z) = q z) ∧
    (∀ a ∈ S, q a = Complex.normSq a) ∧
    (∀ r ∈ menu, Passes q r) ∧ ¬ Balance (fun z : ℂ => omega * z) q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hz, hreads, rest⟩ := h {((1 : ℂ), (0 : ℂ), (0 : ℝ))} 1 (by norm_num)
  have hh := hreads ((1 : ℂ), (0 : ℂ), (0 : ℝ)) (by simp)
    (show (1 : ℂ) ∈ readPoints ((1 : ℂ), (0 : ℂ), (0 : ℝ)) by simp [readPoints])
  simpa [rejected, realize, phaseClosure, orbit] using hh

def evidence : Registration arena
    (type_of% @_root_.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary.finite_query_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary.finite_query_boundary,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ∅, {((0 : ℂ), (0 : ℂ), (0 : ℝ))}, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary.finite_query_boundary)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary.unit
  realizationName := `Reg.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ menu => menu) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary
