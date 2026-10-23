import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open _root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

namespace Reg.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

namespace increasing_tree_card

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => Nat.card {P : IntervalForest n // IsTree P}) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : Nat, r.readout () () n = n.factorial

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 0
  change (0 : Nat) = (0).factorial at hx
  norm_num at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 2, ?_⟩
  change Nat.card {P : IntervalForest (0) // IsTree P} ≠ Nat.card {P : IntervalForest (2) // IsTree P}
  have hx := increasing_tree_card 0
  have hy := increasing_tree_card 2
  rw [hx, hy]
  norm_num [Finset.sum_range_succ]

noncomputable def registration : Registration arena (∀ n : Nat, Nat.card {P : IntervalForest n // IsTree P} = n.factorial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.increasing_tree_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.increasing_tree_card)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => Nat.card {P : IntervalForest n // IsTree P}) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.increasing_tree_card.information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.increasing_tree_card.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => Nat.card {P : IntervalForest n // IsTree P}) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end increasing_tree_card

end Reg.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
