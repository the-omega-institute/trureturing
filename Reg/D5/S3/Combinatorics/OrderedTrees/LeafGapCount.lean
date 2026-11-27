import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.OrderedTrees.LeafGapCount

/-! Source-bound audit of the ordered leaf-gap count. -/

open _root_.D5.S3.Combinatorics.OrderedTrees.LeafPruning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

open scoped BigOperators

private theorem count_five : count 5 = 1 := by
  rw [count_eq_sum]
  simp

namespace Reg.D5.S3.Combinatorics.OrderedTrees.LeafGapCount.CountSum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => count x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () () n = ∑ u ∈ Finset.range (n - 4), (2 * u + 1) * (n + u - 1).choose (2 * u + 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 5
  change 0 = _ at he
  rw [← count_eq_sum 5, count_five] at he
  exact Nat.zero_ne_one he

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  change count 0 ≠ count 5
  rw [count_eq_zero_of_lt_five 0 (by decide), count_five]
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_sum, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_sum) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.LeafPruning.count_eq_sum.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.LeafGapCount.CountSum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => count x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.OrderedTrees.LeafGapCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.LeafGapCount.CountSum
