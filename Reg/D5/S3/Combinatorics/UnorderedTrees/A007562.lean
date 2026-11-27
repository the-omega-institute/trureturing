import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.UnorderedTrees.A007562

/-! Source-bound audit of the normalized planted count. -/

namespace Reg.D5.S3.Combinatorics.UnorderedTrees.A007562

open _root_.D5.S3.Combinatorics.UnorderedTrees.ParentTree
open _root_.D5.S3.Combinatorics.UnorderedTrees.A007562
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)

set_option autoImplicit false

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => normalizedCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 2 ≤ n → plantedCount n = leafChildCount n) ∧
    (plantedCount 1 = 0 ∧ R.readout () () 1 = 1 ∧ leafChildCount 1 = 1) ∧
    (∀ n : ℕ, 0 < n → R.readout () () n = leafChildCount n)

private theorem rejected_law : ¬ arena.Law rejected :=
  fun h => Nat.zero_ne_one h.2.1.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  have noTree : IsEmpty (Tree (Fin 0)) := ⟨fun T => Fin.elim0 T.root⟩
  have noClass : IsEmpty (TreeClass 0) := ⟨fun x => Quotient.inductionOn x noTree.false⟩
  have : IsEmpty (ParityClass 0) := ⟨fun x => noClass.false x.1⟩
  have hzero : normalizedCount 0 = 0 := Nat.card_of_isEmpty
  refine ⟨(), 0, 1, ?_⟩
  change normalizedCount 0 ≠ normalizedCount 1
  rw [hzero, result.2.1.2.1]
  exact Nat.zero_ne_one

def sourceRegistration :
    Registration arena (type_of% @_root_.D5.S3.Combinatorics.UnorderedTrees.A007562.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.UnorderedTrees.A007562.result)
      (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.UnorderedTrees.A007562.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.UnorderedTrees.A007562.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => normalizedCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.UnorderedTrees.A007562
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.UnorderedTrees.A007562
