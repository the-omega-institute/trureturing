import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.OriginalRowBounds
import Reg.Support.DependentFamily

/-! # Source-bound audit of uniform actual own-row bounds -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.OriginalRowBounds

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.M5FullWordConsumer
open _root_.D5.S3.Combinatorics.Circle.OriginalRowBounds

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => actualSource p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 10) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t L : ℕ} {a b : ℤ} {p : Fin k},
    RowCore k t L a b p → ∀ (x : Fin k),
    quarter k ≤ |actualSource k t x| → ∀ (i : ℕ),
    i < (largeOffsets t x).card →
    let s := R.readout () ⟨k, t⟩
    let c := |s (advance (sourceParent t x i) 1)|
    let f := (2 : ℤ) ^ sourceLength t x i
    sourceLength t x i ≤ L ∧ 1 ≤ f ∧ f ≤ (2 : ℤ) ^ L ∧
      quarter k ≤ f * c ∧ f * c ≤ halfCapacity k

private theorem control : RowCore 2 1 0 1 1 (0 : Fin 2) := by
  have hs : actualSource 2 1 = (![1, -1] : Fin 2 → ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  refine {
    dimension := by decide
    nonzero := ?_
    a_positive := by norm_num
    a_le_b := by norm_num
    negative_minimum := ?_
    positive_minimum := ?_
    negative_attained := ⟨1, by rw [hs]; rfl⟩
    p_maximum := ?_
    p_row := {
      proper := by decide
      parent_large := ?_
      small := ?_
      terminal_large := ?_ } }
  · intro i; fin_cases i <;> norm_num [hs]
  · intro i; fin_cases i <;> norm_num [hs]
  · intro i; fin_cases i <;> norm_num [hs]
  · intro i; fin_cases i <;> norm_num [hs]
  · norm_num [hs, quarter]
  · intro j hj; omega
  · norm_num [advance, hs, quarter, finRotate_apply]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : quarter 2 ≤ |actualSource 2 1 (0 : Fin 2)| := by
    norm_num [quarter, actualSource, centered, modulus]
  have hm : (0 : Fin 2) ∈ largeOffsets 1 (0 : Fin 2) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Fin.val_zero, advance, Function.iterate_zero_apply] using hx
  have hi : 0 < (largeOffsets 1 (0 : Fin 2)).card := Finset.card_pos.mpr ⟨0, hm⟩
  obtain ⟨_, hf, _, _, hc⟩ := h control 0 hx 0 hi
  change (2 : ℤ) ^ sourceLength 1 (0 : Fin 2) 0 * |(10 : ℤ)| ≤ halfCapacity 2 at hc
  norm_num [halfCapacity] at hc
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

def source_registration : Registration arena (type_of% (@computed_row_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@computed_row_bounds, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.OriginalRowBounds.computed_row_bounds)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.OriginalRowBounds.computed_row_bounds.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.OriginalRowBounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => actualSource p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.OriginalRowBounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.OriginalRowBounds
