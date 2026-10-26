import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeParentFamily
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeParentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ThreeParentFamily

abbrev signature : Signature where
  Params := ℕ
  State r := Fin (r + 4)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r => actualSource (r + 4) (11 * 2 ^ (r - 1) - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, 4 ≤ r →
    let f := R.readout () r
    (∃ word : List (Fin (r + 4)), word.Nodup ∧ word.toFinset = Finset.univ ∧
      ∀ n : ℕ,
        ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) (8 * 2 ^ r - 11) ∧
        ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) (8 * 2 ^ r - 1)) ∧
    ∀ (word : List (Fin (r + 4))), word.toFinset = Finset.univ →
      ∀ L B : ℤ,
        (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc L B) →
          8 * (2 : ℤ) ^ r - 11 ≤ B - L

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, _, hcomplete, hheight⟩ := (h 4 (by decide)).1
  have hm : (0 : Fin 8) ∈ word := List.mem_toFinset.mp (by rw [hcomplete]; simp)
  cases word with
  | nil => simp at hm
  | cons x xs =>
    have hh := (hheight 1).1.1
    change 0 ≤ ([-1] : List ℤ).sum at hh
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨4, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

def source_registration : Registration arena (type_of% (@sharp_actual_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_actual_family, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ThreeParentFamily.sharp_actual_family)
    (type_of% (realize signature
      (fun _ r => actualSource (r + 4) (11 * 2 ^ (r - 1) - 1)) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeParentFamily.sharp_actual_family.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeParentFamily.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r => actualSource (r + 4) (11 * 2 ^ (r - 1) - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeParentFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
end Reg.D5.S3.Combinatorics.Circle.ThreeParentFamily
