import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic

/-! Whole-family cardinality readouts of the actual convex state carriers. -/

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry

open _root_.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
open _root_.D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem missing_not_separated {n : ℕ} {I : Set (Fin 3 × Fin n)}
    (hm : ∃ r, ∀ x, (r, x) ∉ I) : ¬ Separated I := by
  obtain ⟨r, hr⟩ := hm
  rintro ⟨E, hE⟩
  apply hr (E.a r)
  rw [← hE]
  exact ⟨le_rfl, E.nonempty r⟩

private theorem missing_lower (n : ℕ) : 3 * n ≤ (missingRowStates n).card := by
  classical
  have hm : Set.MapsTo (fun p : Fin 3 × Fin n => ({p} : Set (Fin 3 × Fin n)))
      (Finset.univ : Finset (Fin 3 × Fin n)) (missingRowStates n) := by
    intro p _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Set.ordConnected_singleton⟩, ?_⟩
    rcases p with ⟨r, x⟩
    fin_cases r
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
  have hi : Set.InjOn (fun p : Fin 3 × Fin n => ({p} : Set (Fin 3 × Fin n)))
      (Finset.univ : Finset (Fin 3 × Fin n)) := by
    intro p _ q _ he
    exact Set.singleton_injective he
  simpa using Finset.card_le_card_of_injOn _ hm hi

private theorem exceptional_lower (n : ℕ) : 3 * n ≤ (exceptionalGeometry n).card := by
  classical
  apply (missing_lower n).trans
  apply Finset.card_le_card
  intro I hI
  obtain ⟨hc, hm⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨hc, missing_not_separated hm⟩

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

namespace missing

def actual : Realization signature :=
  realize signature (fun _ _ n => (missingRowStates n).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => 3 * n ^ 4 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 2 ≤ n → R.readout () () n ≤ 3 * n ^ 4

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 2) (by decide)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 2, 100, ?_⟩
  intro he
  dsimp only [actual, realize] at he
  have hu := missing_row_bound (n := 2) (by decide)
  have hl := missing_lower 100
  rw [← he] at hl
  exact (by norm_num : ¬ (3 * 100 : ℕ) ≤ 3 * 2 ^ 4) (hl.trans hu)

def source_registration : Registration arena (type_of% @missing_row_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨missing_row_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@missing_row_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry.missing.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry.missing.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end missing

namespace exceptional

def actual : Realization signature :=
  realize signature (fun _ _ n => (exceptionalGeometry n).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => 233 * n ^ 5 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 11 ≤ n → R.readout () () n ≤ 233 * n ^ 5

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 11) (by decide)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 11, 100000000, ?_⟩
  intro he
  dsimp only [actual, realize] at he
  have hu := exceptional_geometry_bound (n := 11) (by decide)
  have hl := exceptional_lower 100000000
  rw [← he] at hl
  exact (by norm_num : ¬ (3 * 100000000 : ℕ) ≤ 233 * 11 ^ 5) (hl.trans hu)

def source_registration : Registration arena (type_of% @exceptional_geometry_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exceptional_geometry_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exceptional_geometry_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry.exceptional.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry.exceptional.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end exceptional
end
end Reg.D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
