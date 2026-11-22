import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.ShlykConvexityIndex
import Reg.Support.DependentFamily

/-! Source-bound audit of the positive part size in the target partition weight. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Partitions.ShlykConvexityIndex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Partitions.ShlykConvexityIndex

abbrev signature : Signature where
  Params := ℕ
  State := Fin
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s.val + 1) (fun e => nomatch e)

private def zeroSize : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f :=
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∃ x : Fin n → ℕ,
        (∑ s, f.readout () n s * x s) = n ∧
        (∃ (y : Fin k → Fin n → ℕ) (weights : Fin k → ℝ),
          Function.Injective y ∧ (∀ j, y j ≠ x) ∧
          (∀ j, (∑ s, (s.val + 1) * y j s) = n) ∧
          (∀ j, 0 < weights j) ∧ (∑ j, weights j) = 1 ∧
          (∀ s, (x s : ℝ) = ∑ j, weights j * (y j s : ℝ))) ∧
        ∀ (r : ℕ) (y : Fin r → Fin n → ℕ) (weights : Fin r → ℝ),
          Function.Injective y → (∀ j, y j ≠ x) →
          (∀ j, (∑ s, (s.val + 1) * y j s) = n) →
          (∀ j, 0 < weights j) → (∑ j, weights j) = 1 →
          (∀ s, (x s : ℝ) = ∑ j, weights j * (y j s : ℝ)) → k ≤ r

private theorem zeroSize_fails : ¬ arena.Law zeroSize := by
  intro law
  obtain ⟨N, hN⟩ := law 2 le_rfl
  obtain ⟨x, hx, _⟩ := hN (N + 1) (Nat.lt_succ_self N)
  simp [zeroSize, realize] at hx

def family : Registration arena (type_of% shlyk_eventual_convexity_index) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shlyk_eventual_convexity_index, zeroSize, zeroSize_fails⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨zeroSize, ?_, rfl, zeroSize_fails⟩
      rintro ⟨⟩ h
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    rintro ⟨⟩
    exact ⟨2, 0, 1, by decide⟩

set_option linter.style.longLine false in
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    shlyk_eventual_convexity_index (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.ShlykConvexityIndex.shlyk_eventual_convexity_index.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ShlykConvexityIndex.family
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
    owner := `D5.S3.Combinatorics.Partitions.ShlykConvexityIndex
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "arg", "body",
        "fn", "arg", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.ShlykConvexityIndex
