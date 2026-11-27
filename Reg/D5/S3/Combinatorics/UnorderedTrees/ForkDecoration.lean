import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.UnorderedTrees.A358587

/-! Source-bound audit of the size-preserving decoration count. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.UnorderedTrees.ParentTree
open _root_.D5.S3.Combinatorics.UnorderedTrees.ForkDecoration
open Reg.Support.SingleDependentReadout (sensitivity)
set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.UnorderedTrees.ForkDecoration

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Nat) (fun _ => Nat)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ n : Nat, Nat.card (Weighted n) = r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Nat.card (Weighted 5) = 0 := h 5
  have hOne := (_root_.D5.S3.Combinatorics.UnorderedTrees.A358587.result 5).2.2.2.1.2.2.2.2.1
  rw [card_weighted, hOne] at hz
  exact Nat.one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 5, ?_⟩
  have h := _root_.D5.S3.Combinatorics.UnorderedTrees.A358587.result 5
  change a 0 ≠ a 5
  rw [h.2.1, h.2.2.2.1.2.2.2.2.1]
  exact Nat.zero_ne_one

def sourceRegistration : Registration arena (type_of% @card_weighted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_weighted, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@card_weighted) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.UnorderedTrees.ForkDecoration.card_weighted.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.UnorderedTrees.ForkDecoration.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.UnorderedTrees.ForkDecoration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.UnorderedTrees.ForkDecoration
