import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.UnorderedTrees.A358587

/-! Source-bound audit of the complete unordered rooted-tree enumeration endpoint. -/

open _root_.D5.S3.Combinatorics.UnorderedTrees.ParentTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

open PowerSeries
open scoped PowerSeries

noncomputable section

namespace Reg.D5.S3.Combinatorics.UnorderedTrees.A358587.ActualTreeCount

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (Set.Finite {T : TreeClass n | classHeight T = classInternalCount T} ∧
      R.readout () () n = Set.ncard {T : TreeClass n | classHeight T = classInternalCount T}) ∧
    R.readout () () 0 = 0 ∧
    mk (fun k ↦ (R.readout () () k : ℤ)) =
      X^5 * (X^2 - X + 1) * invOfUnit ((X - 1)^2 * (X + 1) * (2*X - 1)^2) 1 ∧
    (R.readout () () 1 = 0 ∧ R.readout () () 2 = 0 ∧ R.readout () () 3 = 0 ∧
      R.readout () () 4 = 0 ∧ R.readout () () 5 = 1 ∧ R.readout () () 6 = 4 ∧
      R.readout () () 7 = 14) ∧
    (7 < n →
      (R.readout () () n : ℤ) = 5 * R.readout () () (n - 1) - 7 * R.readout () () (n - 2) -
        R.readout () () (n - 3) + 8 * R.readout () () (n - 4) - 4 * R.readout () () (n - 5))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Nat.zero_ne_one (h 5).2.2.2.1.2.2.2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  have h := _root_.D5.S3.Combinatorics.UnorderedTrees.A358587.result 5
  change a 0 ≠ a 5
  rw [h.2.1, h.2.2.2.1.2.2.2.2.1]
  exact Nat.zero_ne_one

def sourceRegistration :
    Registration arena
      (type_of% @D5.S3.Combinatorics.UnorderedTrees.A358587.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.UnorderedTrees.A358587.result, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Combinatorics.UnorderedTrees.A358587.result) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.UnorderedTrees.A358587.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.UnorderedTrees.A358587.ActualTreeCount.sourceRegistration
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
    owner := `D5.S3.Combinatorics.UnorderedTrees.A358587
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

end Reg.D5.S3.Combinatorics.UnorderedTrees.A358587.ActualTreeCount
