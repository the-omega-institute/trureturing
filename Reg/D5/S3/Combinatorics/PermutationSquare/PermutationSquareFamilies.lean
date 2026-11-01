import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Explicit Square-Avoider Families -/

namespace Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies

open _root_.D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareStructure
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace IndecomposableShapeAndPrefixIff

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    b 0 = 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      indecomposableAvoiders (O.readout () () n) = {p | p ∈ avoiders n ∧ sumIndecomposable p} ∧
      b n = {p | p ∈ avoiders n ∧ sumIndecomposable p}.ncard) ∧
    (∀ (n : ℕ) (p : List ℕ), p.Perm (List.range' 1 n) →
      (sumIndecomposable p ↔
        ¬ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
          (Finset.Icc 1 k).image (fun i => p.getD (i - 1) 0) = Finset.Icc 1 k)) ∧
    (∀ (n : ℕ) (p : List ℕ), 1 ≤ n → p.Perm (List.range' 1 n) → p.getLast? = some 1 →
      sumIndecomposable p) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ p ∈ indecomposableAvoiders n,
      let m := p.getD 0 0
      let posN := p.idxOf n + 1
      let q := square p
      (p.getD (n - 1) 0 = 1 ∧ p.getLast? = some 1) ∧
      (2 ≤ m ∧ m ≤ 4 ∧
        ∀ u v : ℕ, 2 ≤ u → u < v → v ≤ m - 1 → 1 < p.idxOf v + 1 ∧ p.idxOf v + 1 < p.idxOf u + 1) ∧
      (q.getD (posN - 1) 0 = 1 ∧ q.getD (n - 1) 0 = m ∧
        (∀ i j : ℕ, posN + 1 ≤ i → i < j → j ≤ n → q.getD (i - 1) 0 < q.getD (j - 1) 0) ∧
        n + 1 ≤ posN + m ∧ n - m + 1 ≤ posN ∧ (m = 2 → posN = n - 1)) ∧
      (∀ i j : ℕ, posN + 1 ≤ i → i < j → j ≤ n → p.getD (j - 1) 0 < p.getD (i - 1) 0) ∧
      (∀ u : ℕ, 2 ≤ u → u ≤ m - 1 → 1 < p.idxOf u + 1) ∧ n - 3 ≤ posN ∧ posN ≤ n - 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := seven_families_admissible_and_distinct.1 2 (by omega)
  have h2 : indecomposableAvoiders 0 = {p | p ∈ avoiders 2 ∧ sumIndecomposable p} :=
    (h.2.1 2 (by omega)).1
  have h0 : familyI 2 ∈ indecomposableAvoiders 0 := by
    rw [h2]
    exact ⟨hf.2.1, hf.2.2⟩
  have hlen := h0.2.1.1.length_eq
  simp [familyI] at hlen

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@indecomposable_shape_and_prefix_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨indecomposable_shape_and_prefix_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@indecomposable_shape_and_prefix_iff)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.IndecomposableShapeAndPrefixIff.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.IndecomposableShapeAndPrefixIff.evidence
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
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IndecomposableShapeAndPrefixIff

namespace SevenFamiliesAdmissibleAndDistinct

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    (∀ n : ℕ, 2 ≤ n → familyI (O.readout () () n) ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 5 ≤ n → familyJ n ∈ indecomposableAvoiders n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 6 ≤ n → familyA n ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 7 ≤ n → familyB n ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 4 ≤ n → familyC n ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 9 ≤ n → familyD n ∈ indecomposableAvoiders n) ∧
    (∀ n j₁ j₂ : ℕ, 6 ≤ n → j₁ ≤ (n - 6) / 2 → j₂ ≤ (n - 6) / 2 →
      familyK n j₁ = familyK n j₂ → j₁ = j₂) ∧
    (∀ n : ℕ, 5 ≤ n → familyI n ≠ familyJ n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyI n ≠ familyK n j) ∧
    (∀ n : ℕ, 6 ≤ n → familyI n ≠ familyA n) ∧
    (∀ n : ℕ, 7 ≤ n → familyI n ≠ familyB n) ∧
    (∀ n : ℕ, 4 ≤ n → familyI n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyI n ≠ familyD n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyJ n ≠ familyK n j) ∧
    (∀ n : ℕ, 6 ≤ n → familyJ n ≠ familyA n) ∧
    (∀ n : ℕ, 7 ≤ n → familyJ n ≠ familyB n) ∧
    (∀ n : ℕ, 5 ≤ n → familyJ n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyJ n ≠ familyD n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyA n) ∧
    (∀ n j : ℕ, 7 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyB n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyC n) ∧
    (∀ n j : ℕ, 9 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyD n) ∧
    (∀ n : ℕ, 7 ≤ n → familyA n ≠ familyB n) ∧
    (∀ n : ℕ, 6 ≤ n → familyA n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyA n ≠ familyD n) ∧
    (∀ n : ℕ, 7 ≤ n → familyB n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyB n ≠ familyD n) ∧
    (∀ n : ℕ, 9 ≤ n → familyC n ≠ familyD n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : familyI 0 ∈ indecomposableAvoiders 2 := h.1 2 (by omega)
  have hlen := h0.2.1.1.length_eq
  simp [familyI] at hlen

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@seven_families_admissible_and_distinct)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨seven_families_admissible_and_distinct, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@seven_families_admissible_and_distinct)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.SevenFamiliesAdmissibleAndDistinct.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.SevenFamiliesAdmissibleAndDistinct.evidence
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
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SevenFamiliesAdmissibleAndDistinct

namespace FirstEntryTwoAndThreeClassification

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    (∀ n : ℕ, 4 ≤ n →
      (∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 2) ↔
        (p = familyI n ∨ (5 ≤ n ∧ p = familyJ n) ∨
          (6 ≤ n ∧ ∃ j ≤ (n - 6) / 2, p = familyK n j))) ∧
      {p ∈ indecomposableAvoiders n | p.getD 0 0 = 2}.ncard =
        (if n = 4 then 1 else O.readout () () n / 2)) ∧
    (∀ n : ℕ, 5 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 ≠ 3)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : {p ∈ indecomposableAvoiders 5 | p.getD 0 0 = 2}.ncard = 0 := by
    have hr := (h.1 5 (by omega)).2
    change {p ∈ indecomposableAvoiders 5 | p.getD 0 0 = 2}.ncard = (if 5 = 4 then 1 else 0 / 2) at hr
    simpa using hr
  have hgood : {p ∈ indecomposableAvoiders 5 | p.getD 0 0 = 2}.ncard = 2 := by
    simpa using (first_entry_two_and_three_classification.1 5 (by omega)).2
  omega

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@first_entry_two_and_three_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_entry_two_and_three_classification, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@first_entry_two_and_three_classification)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.FirstEntryTwoAndThreeClassification.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies.FirstEntryTwoAndThreeClassification.evidence
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
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstEntryTwoAndThreeClassification

end Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
