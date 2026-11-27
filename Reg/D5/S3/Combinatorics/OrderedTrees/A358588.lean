import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.OrderedTrees.A358588

/-! Source-bound audit of the complete ordered rooted-tree enumeration endpoint. -/

open _root_.D5.S3.Combinatorics.OrderedTrees.LeafPruning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

open PowerSeries
open scoped PowerSeries

private theorem count_five : count 5 = 1 :=
  (D5.S3.Combinatorics.OrderedTrees.A358588.result 5).2.2.2.1.2.2.2.2.1

namespace Reg.D5.S3.Combinatorics.OrderedTrees.A358588.ActualTreeCount

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => count x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (Set.Finite {t : Tree | t.vertices = n ∧ t.height = t.internal} ∧
      R.readout () () n = Set.ncard {t : Tree | t.vertices = n ∧ t.height = t.internal}) ∧
    count 0 = 0 ∧
    mk (fun k ↦ (count k : ℤ)) =
      X^5 * (1 - X + X^2) * invOfUnit ((1 - X)^3 * (1 - 3 * X + X^2)^2) 1 ∧
    (count 1 = 0 ∧ count 2 = 0 ∧ count 3 = 0 ∧ count 4 = 0 ∧
      count 5 = 1 ∧ count 6 = 8 ∧ count 7 = 41) ∧
    (7 < n →
      (count n : ℤ) = 9 * count (n - 1) - 32 * count (n - 2) + 58 * count (n - 3) -
        58 * count (n - 4) + 32 * count (n - 5) - 9 * count (n - 6) + count (n - 7))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 5).1.2
  change 0 = Set.ncard {t : Tree | t.vertices = 5 ∧ t.height = t.internal} at he
  rw [← (count_spec 5).2, count_five] at he
  exact Nat.zero_ne_one he

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  change count 0 ≠ count 5
  rw [count_eq_zero_of_lt_five 0 (by decide), count_five]
  decide

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.OrderedTrees.A358588.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.OrderedTrees.A358588.result, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.OrderedTrees.A358588.result) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.OrderedTrees.A358588.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.OrderedTrees.A358588.ActualTreeCount.sourceRegistration
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
    owner := `D5.S3.Combinatorics.OrderedTrees.A358588
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.OrderedTrees.A358588.ActualTreeCount
