import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev classificationSignature : Signature where
  Params := ℕ
  State d := Finset (Fin (3 * d))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actualSum : Realization classificationSignature :=
  realize classificationSignature (fun _ d A =>
    ∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i)
    (fun e => nomatch e)

def rejectedSum : Realization classificationSignature :=
  realize classificationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev classificationArena : Arena where
  signature := classificationSignature
  Law R := ∀ (d : ℕ) (hd : 3 ≤ d) (_h19 : ¬19 ∣ (2 ^ (d + 1) - 3))
    (A : Finset (Fin (3 * d))), R.readout () d A = 0 ↔
      ∃! B : Finset (Fin d), A = phaseLift d B ∧
        ((⟨d - 3, by omega⟩ : Fin d) ∈ B ↔ (⟨d - 1, by omega⟩ : Fin d) ∈ B)

private theorem rejected_classification : ¬ classificationArena.Law rejectedSum := by
  intro h
  have emptyZero : (∑ i ∈ (∅ : Finset (Fin 9)),
      actualSource 9 ((2 ^ 3 - 1) * (2 ^ (3 + 1) - 3)) i) = 0 := by simp
  have hc := (actual_zero_iff_phase_pair 3 (by decide) (by decide) ∅).mp emptyZero
  have hh := (h 3 (by decide) (by decide) ∅).mpr hc
  norm_num [rejectedSum, realize] at hh

noncomputable def classificationRegistration :
    Registration classificationArena (type_of% (@actual_zero_iff_phase_pair)) where
  actual := actualSum
  bridge := Iff.rfl
  variation := ⟨actual_zero_iff_phase_pair, rejectedSum, rejected_classification⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedSum, ?_, rfl, rejected_classification⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨3, ∅, {⟨0, by decide⟩}, ?_⟩
    norm_num [actualSum, realize, actualSource, centered, modulus]

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actualCount : Realization countSignature :=
  realize countSignature (fun _ _ d =>
    (Finset.univ.filter (fun A : Finset (Fin (3 * d)) =>
      (∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0)).card)
    (fun e => nomatch e)

def rejectedCount : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ (d : ℕ) (_hd : 3 ≤ d) (_h19 : ¬19 ∣ (2 ^ (d + 1) - 3)),
    R.readout () () d = 2 ^ (d - 1)

private theorem rejected_count : ¬ countArena.Law rejectedCount := by
  intro h
  have hh := h 3 (by decide) (by decide)
  norm_num [rejectedCount, realize] at hh

noncomputable def countRegistration :
    Registration countArena (type_of% (@actual_zero_subsets_card)) where
  actual := actualCount
  bridge := Iff.rfl
  variation := ⟨actual_zero_subsets_card, rejectedCount, rejected_count⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCount, ?_, rfl, rejected_count⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    change (Finset.univ.filter (fun A : Finset (Fin (3 * 3)) =>
      (∑ k ∈ A, actualSource (3 * 3) ((2 ^ 3 - 1) * (2 ^ (3 + 1) - 3)) k) = 0)).card ≠
      (Finset.univ.filter (fun A : Finset (Fin (3 * 4)) =>
      (∑ k ∈ A, actualSource (3 * 4) ((2 ^ 4 - 1) * (2 ^ (4 + 1) - 3)) k) = 0)).card
    rw [actual_zero_subsets_card 3 (by decide) (by decide),
      actual_zero_subsets_card 4 (by decide) (by decide)]
    norm_num

noncomputable def classificationAudit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_zero_iff_phase_pair) (Realization classificationSignature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily.actual_zero_iff_phase_pair.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily.classificationRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classificationRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize classificationSignature (fun _ d A =>
    ∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def countAudit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_zero_subsets_card) (Realization countSignature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily.actual_zero_subsets_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily.countRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ d =>
    (Finset.univ.filter (fun A : Finset (Fin (3 * d)) =>
      (∑ i ∈ A, actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0)).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
