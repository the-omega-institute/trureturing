import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open _root_.D5.S3.Combinatorics.PriorityLattice.ForestCovers
open _root_.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace gamma_formula

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
  realize signature (fun _ _ n => idealCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : Nat, 1 ≤ n → r.readout () () n = n ^ 2 - n + 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 (by omega)
  change (0 : Nat) = (1) ^ 2 - (1) + 2 at hx
  norm_num at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 1, 2, ?_⟩
  change idealCount (1) ≠ idealCount (2)
  have hx := gamma_formula 1 (by omega)
  have hy := gamma_formula 2 (by omega)
  rw [hx, hy]
  norm_num [Finset.sum_range_succ]

noncomputable def registration : Registration arena (∀ n : Nat, 1 ≤ n → idealCount n = n ^ 2 - n + 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gamma_formula, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gamma_formula)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => idealCount n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gamma_formula.information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gamma_formula.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => idealCount n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end gamma_formula

namespace gammaPos_formula

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
  realize signature (fun _ _ n => positiveIdealCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : Nat, 1 ≤ n → r.readout () () n = n ^ 2 + 2 - 2*n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 (by omega)
  change (0 : Nat) = (1) ^ 2 + 2 - 2*(1) at hx
  norm_num at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 1, 2, ?_⟩
  change positiveIdealCount (1) ≠ positiveIdealCount (2)
  have hx := gammaPos_formula 1 (by omega)
  have hy := gammaPos_formula 2 (by omega)
  rw [hx, hy]
  norm_num [Finset.sum_range_succ]

noncomputable def registration : Registration arena (∀ n : Nat, 1 ≤ n → positiveIdealCount n = n ^ 2 + 2 - 2*n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gammaPos_formula, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gammaPos_formula)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => positiveIdealCount n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gammaPos_formula.information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.gammaPos_formula.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => positiveIdealCount n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end gammaPos_formula

end Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals
