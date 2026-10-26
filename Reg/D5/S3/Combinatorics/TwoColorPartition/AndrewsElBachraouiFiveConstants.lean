import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
import Reg.Support.SingleDependentReadout
import Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

/-! Source-bound readouts for the original coefficient proof. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
open Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
open PowerSeries Finset

namespace Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants

open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants

namespace Subset

abbrev signature : Signature where
  Params := Type
  State α := Finset α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature :=
  realize signature (fun _ (α : Type) s => ∑ S ∈ s.powerset,
    (-1 : ℝ)^S.card / (2*S.card+1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {α : Type} (s : Finset α),
    r.readout () α s = ∏ i ∈ range s.card, (2*(i : ℝ)+2)/(2*i+3)
noncomputable def bad : Realization signature :=
  realize signature (fun _ _ s => (∏ i ∈ range s.card, (2*(i : ℝ)+2)/(2*i+3))+1)
    (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h (α := Unit) ∅
  norm_num [bad, realize] at hx
noncomputable def registration : Registration arena (type_of% (@subset_constant)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@subset_constant, bad, bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_not_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Unit, ∅, {()}, ?_⟩
    change (∑ S ∈ (∅ : Finset Unit).powerset, (-1 : ℝ)^S.card / (2*S.card+1)) ≠
      (∑ S ∈ ({()} : Finset Unit).powerset, (-1 : ℝ)^S.card / (2*S.card+1))
    rw [show ({()} : Finset Unit) = insert () ∅ from rfl, powerset_insert]
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.subset_constant)
    (type_of% (realize signature (fun _ (α : Type) s => ∑ S ∈ s.powerset, (-1 : ℝ)^S.card / (2*S.card+1)) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.subset_constant.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.Subset.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ (α : Type) s => ∑ S ∈ s.powerset, (-1 : ℝ)^S.card / (2*S.card+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Subset

namespace Gap

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ) (fun _ => ℝ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ h => rationalConstant h-productConstant h)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ h : ℕ, 1 ≤ h → 0 < r.readout () () h
noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 1 (by decide)
  norm_num [bad, realize] at hx
noncomputable def registration : Registration arena (type_of% (@leading_gap_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨leading_gap_pos, bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change rationalConstant 0-productConstant 0 ≠ rationalConstant 1-productConstant 1
    norm_num [rationalConstant, productConstant, oddProd, prod_range_succ]
    linarith [Real.pi_pos]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.leading_gap_pos)
    (type_of% (realize signature (fun _ _ h => rationalConstant h-productConstant h) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.leading_gap_pos.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants.Gap.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ h => rationalConstant h-productConstant h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
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
  options := #[]

end Gap

end Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
