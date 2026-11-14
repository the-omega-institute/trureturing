import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
import Reg.Support.SingleDependentReadout

/-! Source-family registrations for unbounded bishop counts. -/

namespace Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth

open _root_.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

private theorem count_one : count 1 = 1 := by
  classical
  have hind : (bishopGraph 1).IsIndepSet (↑(Finset.univ : Finset (Cell 1)) : Set (Cell 1)) := by
    intro p _ q _ hpq
    exact (hpq (Subsingleton.elim p q)).elim
  have hfull : ∀ M : Placement 1, M.val = Finset.univ := by
    intro M
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    exact M.property.2 _ hind (Finset.subset_univ _)
  change Fintype.card (Placement 1) = 1
  apply Fintype.card_eq_one_iff.mpr
  let M : Placement 1 := Classical.choice inferInstance
  exact ⟨M, fun Q => Subtype.ext ((hfull Q).trans (hfull M).symm)⟩


namespace LowerBound

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun m => count (4 * m + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, m ^ (6 * m) ≤ R.readout () () m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have hb := count_lower_bound 2
  rw [show (2 : ℕ) ^ (6 * 2) = 4096 by norm_num] at hb
  have hz := count_one
  dsimp only [actual, realize]
  change 4096 ≤ count 9 at hb
  change count 1 ≠ count 9
  rw [hz]
  omega

def source_registration : Registration arena (type_of% @count_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@count_lower_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.LowerBound.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.LowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => fun m => count (4 * m + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LowerBound

namespace RatioBound

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun m => count (4 * m + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 50 ≤ m → 4 ^ m * (4 * m + 1) ^ (4 * m) ≤ R.readout () () m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 50 (by omega)
  have hp : 0 < 4 ^ 50 * (4 * 50 + 1) ^ (4 * 50) := by positivity
  change 4 ^ 50 * (4 * 50 + 1) ^ (4 * 50) ≤ 0 at he
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have hb := count_lower_bound 2
  rw [show (2 : ℕ) ^ (6 * 2) = 4096 by norm_num] at hb
  have hz := count_one
  dsimp only [actual, realize]
  change 4096 ≤ count 9 at hb
  change count 1 ≠ count 9
  rw [hz]
  omega

def source_registration : Registration arena (type_of% @ratio_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ratio_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ratio_lower_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.RatioBound.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.RatioBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => fun m => count (4 * m + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end RatioBound

namespace SourceDictionary

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun n => (sourceFamily n).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = count n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1
  change 0 = count 1 at he
  rw [count_one] at he
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 9, ?_⟩
  dsimp only [actual, realize]
  rw [source_family_card, source_family_card, count_one]
  have hb := count_lower_bound 2
  rw [show (2 : ℕ) ^ (6 * 2) = 4096 by norm_num] at hb
  change 4096 ≤ count 9 at hb
  omega

def source_registration : Registration arena (type_of% @source_family_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_family_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@source_family_card) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.SourceDictionary.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth.SourceDictionary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => fun n => (sourceFamily n).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SourceDictionary

end
end Reg.D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
