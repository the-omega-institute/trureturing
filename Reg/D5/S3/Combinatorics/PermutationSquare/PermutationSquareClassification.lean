import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for First-Entry-Four and Complete Square-Avoider Classification -/

namespace Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification

open _root_.D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareStructure
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FirstEntryFourStructure

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    (∀ n : ℕ, 4 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      ((square p).drop (n - 4)).Perm [1, 2, 3, 4] ∧
      (square p).getD (O.readout () () n - 1) 0 = 4 ∧
      ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) =
        {n, p.idxOf 2 + 1, p.idxOf 3 + 1}) ∧
    (∀ n : ℕ, 5 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      p.getD 1 0 = 3 ∧
      ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨
       (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2) ∨
       (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n))) ∧
    (∀ n : ℕ, 7 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      let M := (p.drop 2).take (n - 6)
      ¬ NonnestingDefs.Occurs [3, 1, 2] M ∧ ¬ NonnestingDefs.Occurs [3, 2, 1] M ∧
      (((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨
        (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2)) →
        {v : ℕ | v ∈ M} = {v : ℕ | 5 ≤ v ∧ v ≤ n - 2}) ∧
      ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) →
        {v : ℕ | v ∈ M} = ({v : ℕ | 5 ≤ v ∧ v ≤ n - 3} ∪ {n - 1}) ∧
        p.getD (n - 5) 0 = n - 1))

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hc4 := seven_families_admissible_and_distinct.2.2.2.2.2.1 4 (by omega)
  have hbad : (square (familyC 4)).getD (1 - 1) 0 = 4 :=
    (h.1 4 (by omega) (familyC 4) hc4 (by decide)).2.1
  revert hbad
  decide

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@first_entry_four_structure)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_entry_four_structure, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@first_entry_four_structure)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.FirstEntryFourStructure.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.FirstEntryFourStructure.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstEntryFourStructure

namespace FirstEntryFourClassification

attribute [local instance 2000] Classical.propDecidable

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    ∀ n : ℕ, 4 ≤ n →
      (∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔
        (p = familyC (O.readout () () n) ∨ (6 ≤ n ∧ p = familyA n) ∨
          (7 ≤ n ∧ p = familyB n) ∨ (9 ≤ n ∧ p = familyD n))) ∧
      {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4}.ncard =
        (if n ≤ 5 then 1 else if n = 6 then 2 else if n ≤ 8 then 3 else 4)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have h5 := ((h 5 (by omega)).1 (familyC 0)).mpr (Or.inl rfl)
  have hlen := h5.1.2.1.1.length_eq
  simp [familyC] at hlen

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@first_entry_four_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_entry_four_classification, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@first_entry_four_classification)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.FirstEntryFourClassification.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.FirstEntryFourClassification.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstEntryFourClassification

namespace IndecomposableClassificationGeNine

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    ∀ n : ℕ, 9 ≤ n → ∀ p : List ℕ,
      p ∈ indecomposableAvoiders n ↔
        (p = familyI (O.readout () () n) ∨ p = familyJ n ∨ (∃ j ≤ (n - 6) / 2, p = familyK n j) ∨
          p = familyA n ∨ p = familyD n ∨ p = familyB n ∨ p = familyC n)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have h9 : familyI 0 ∈ indecomposableAvoiders 9 :=
    (h 9 (by omega) (familyI 0)).mpr (Or.inl rfl)
  have hlen := h9.2.1.1.length_eq
  simp [familyI] at hlen

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@indecomposable_classification_ge_nine)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨indecomposable_classification_ge_nine, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@indecomposable_classification_ge_nine)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.IndecomposableClassificationGeNine.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification.IndecomposableClassificationGeNine.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IndecomposableClassificationGeNine

end Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
