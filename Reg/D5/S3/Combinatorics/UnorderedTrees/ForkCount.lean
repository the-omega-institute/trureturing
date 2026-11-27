import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.UnorderedTrees.ForkCount

/-! Source-bound audit of the unordered fork-decoration count. -/

open _root_.D5.S3.Combinatorics.UnorderedTrees.ParentTree
open _root_.D5.S3.Combinatorics.UnorderedTrees.ForkCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

open scoped BigOperators

noncomputable section

private theorem count_five : a 5 = 1 := by rw [count_by_arms]; decide
private theorem count_zero : a 0 = 0 := by rw [count_by_arms]; decide

namespace Reg.D5.S3.Combinatorics.UnorderedTrees.ForkCount.CountSum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => a x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () () n =
      (∑ m ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - (4 + 2 * m)),
        (n - 4 - 2 * m).choose (b + 1)) +
      (∑ v ∈ Finset.range (n - 5), (v + 1) * (n - 3).choose (v + 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 5
  change 0 = _ at he
  rw [← count_by_arms 5, count_five] at he
  exact Nat.zero_ne_one he

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  change a 0 ≠ a 5
  rw [count_zero, count_five]
  exact Nat.zero_ne_one

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.UnorderedTrees.ForkCount.count_by_arms) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.UnorderedTrees.ForkCount.count_by_arms, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.UnorderedTrees.ForkCount.count_by_arms) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.UnorderedTrees.ForkCount.count_by_arms.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.UnorderedTrees.ForkCount.CountSum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => a x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.UnorderedTrees.ForkCount
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

end Reg.D5.S3.Combinatorics.UnorderedTrees.ForkCount.CountSum
