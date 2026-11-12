import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Hall.PrescribedDifferences
import Reg.Support.DependentFamily

/-! The occurrence-sum readout retains the complete finite abelian source law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Reg.D5.S3.FiniteGroups.Hall.PrescribedDifferences

open _root_.D5.S3.FiniteGroups.Hall.PrescribedDifferences
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The carrier and its additive structure are parameters; every label occurrence is a state. -/
abbrev signature : Signature where
  Params := Σ G : Type u, AddCommGroup G
  State p := Fin (Nat.card p.1) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p r => letI := p.2; ∑ i, r i) (fun e => nomatch e)

/-- All original binders and both sides of the iff remain in the source law. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (G : Type u) [hG : AddCommGroup G] [Finite G]
    (r : Fin (Nat.card G) → G),
    (∃ x : Fin (Nat.card G) ≃ G, Function.Bijective (fun i => x i + r i)) ↔
      R.readout () ⟨G, hG⟩ r = 0

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ p _ => letI := p.2; 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q := ULift.{u} (ZMod 2)
  let r : Fin (Nat.card Q) → Q := fun i => if i.val = 0 then 1 else 0
  have hs : (∑ i, r i) = 1 := by
    simp [r]
  have hh := (h Q r).mpr (by rfl)
  have hz := (numbering_iff_sum_eq_zero Q r).mp hh
  rw [hs] at hz
  exact one_ne_zero hz

noncomputable def sourceRegistration : Registration arena.{u}
    (type_of% (@numbering_iff_sum_eq_zero.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨numbering_iff_sum_eq_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let Q := ULift.{u} (ZMod 2)
    let r : Fin (Nat.card Q) → Q := fun i => if i.val = 0 then 1 else 0
    refine ⟨⟨Q, inferInstance⟩, (fun _ => 0), r, ?_⟩
    change (∑ _ : Fin (Nat.card Q), (0 : Q)) ≠ ∑ i, r i
    simp [r]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@numbering_iff_sum_eq_zero.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.Hall.PrescribedDifferences.numbering_iff_sum_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Hall.PrescribedDifferences.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p r => letI := p.2; ∑ i, r i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Hall.PrescribedDifferences
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.Hall.PrescribedDifferences
