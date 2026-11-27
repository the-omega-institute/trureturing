import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary

open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State := Nat.Partition
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (_hr : 1 ≤ r),
    IsLeast {n : ℕ | 0 < n ∧ ∃ p q : Nat.Partition n,
      (graph n).Adj p q ∧ R.readout ⟨0, by decide⟩ n p = r ∧
        R.readout ⟨1, by decide⟩ n q = r + 1}
      (triangular (r + 1) + 1)

def actual : Realization signature :=
  realize signature (fun _ _ p => localDimension p) (fun e => nomatch e)

private def rejected (i : Fin 2) : Realization signature :=
  realize signature (fun j n p => if j = i then 0 else actual.readout j n p)
    actual.anchor

private theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨_, p, q, _, hp, hq⟩ := (h 1 (by decide)).1
  fin_cases i
  · simp [rejected, realize] at hp
  · simp [rejected, realize] at hq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨_, p, q, _, hp, hq⟩ := (boundary_result 1 (by decide)).1
  refine ⟨4, p, q, ?_⟩
  change localDimension p ≠ localDimension q
  rw [hp, hq]
  decide

private theorem actual_bridge : (type_of% @boundary_result) ↔ arena.Law actual :=
  Iff.rfl

def source_registration : Registration arena (type_of% @boundary_result) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp boundary_result, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext n p
      simp only [rejected, realize]
      split
      · rename_i h
        exact (hj h).elim
      · rfl
    · intro i
      exact nomatch i
  dependence := actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@boundary_result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => localDimension p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "arg", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "arg", "body",
        "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyBoundary
