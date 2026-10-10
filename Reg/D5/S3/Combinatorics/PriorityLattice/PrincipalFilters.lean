import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open _root_.D5.S3.Combinatorics.PriorityLattice.ForestCovers
open _root_.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace FilterCount

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
  realize signature (fun _ _ n => theta n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : Nat, 1 ≤ n → r.readout () () n = ∑ k ∈ Finset.range (n+1), k.factorial

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 (by omega)
  change (0 : Nat) = ∑ k ∈ Finset.range ((1)+1), k.factorial at hx
  norm_num [Finset.sum_range_succ, Nat.factorial] at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 1, 2, ?_⟩
  change theta (1) ≠ theta (2)
  have hx := result 1 (by omega)
  have hy := result 2 (by omega)
  change theta 1 = _ at hx
  change theta 2 = _ at hy
  rw [hx, hy]
  norm_num [Finset.sum_range_succ, Nat.factorial]

noncomputable def registration : Registration arena (claimTheta) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.result, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.result)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => theta n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.FilterCount.information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.FilterCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => theta n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.PriorityLattice.PrincipalFilters, definition := some { owner := `D5.S3.Combinatorics.PriorityLattice.PrincipalFilters, name := `D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.claimTheta, path := #[] }, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end FilterCount

end Reg.D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
