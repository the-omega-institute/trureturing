import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.TwoReplyProfile

/-! Source-owned full-profile variation, sensitivity and dependence. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting
open _root_.D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.FullFutureProfile

abbrev signature : Signature where
  Params := Σ _B : ℕ, ℚ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p y => @decide (SameFuture p.1 p.2 y) (Classical.propDecidable _)) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => true) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro _
  refine ⟨⟨1,1⟩,1,2,?_⟩
  intro he
  have ht : actual.readout () ⟨1,1⟩ 1 = true := by
    apply decide_eq_true
    intro _ _ _ _
    rfl
  have hf : actual.readout () ⟨1,1⟩ 2 ≠ true := by
    intro h
    have hf : SameFuture 1 1 2 := of_decide_eq_true h
    have hh := hf [] 1 le_rfl le_rfl
    norm_num [attain,reply] at hh
  apply hf
  rw [← he]
  exact ht

def arena : Arena where
  signature := signature
  Law R := ∀ {B : ℕ} {x y : ℚ}, 0 < x → 0 < y →
    (SameInstant B x y ↔ R.readout () ⟨B,x⟩ y = true)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (B := 1) (x := 1) (y := 2) (by norm_num) (by norm_num)).mpr rfl
  have hb := hh 1 le_rfl le_rfl
  norm_num [reply] at hb

def family : Registration arena (type_of% (@instantaneous_iff_full_future)) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [arena,actual,realize,decide_eq_true_eq] using
    @instantaneous_iff_full_future,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@instantaneous_iff_full_future) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.instantaneous_iff_full_future.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.FullFutureProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => @decide (SameFuture p.1 p.2 y) (Classical.propDecidable _)) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.FullFutureProfile

namespace Reg.D5.S3.Observer.RationalRouting.ContainingCell

abbrev signature : Signature where
  Params := Σ _B : ℕ, ℚ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ By x => @decide ((containingCell By.1 By.2).Contains x)
    (inferInstanceAs (Decidable (0 < x ∧ (containingCell By.1 By.2).lower ≤ x ∧
      x < (containingCell By.1 By.2).upper)))) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => true) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro _
  refine ⟨⟨1,1⟩,1,0,?_⟩
  intro he
  have ht : actual.readout () ⟨1,1⟩ 1 = true := by
    have hh := (containing_cell_exact 1 le_rfl (by norm_num) 1).mpr
      ⟨by norm_num,fun _ _ _ => rfl⟩
    simpa only [actual,realize,ProfileCell.Contains,Bool.and_eq_true,decide_eq_true_eq]
      using hh
  have hf : actual.readout () ⟨1,1⟩ 0 ≠ true := by
    intro h
    have hh : (containingCell 1 1).Contains 0 := by
      simpa only [actual,realize,ProfileCell.Contains,Bool.and_eq_true,decide_eq_true_eq]
        using h
    exact (lt_irrefl 0) hh.1
  apply hf
  rw [← he]
  exact ht

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ), 1 ≤ B → ∀ {y : ℚ}, 0 < y → ∀ x : ℚ,
    R.readout () ⟨B,y⟩ x = true ↔ 0 < x ∧ SameInstant B x y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 le_rfl (y := 1) (by norm_num) 0).mp rfl
  norm_num at hh

def family : Registration arena (type_of% (@containing_cell_exact)) where
  actual := actual
  bridge := by simp only [arena,actual,realize,ProfileCell.Contains,Bool.and_eq_true,decide_eq_true_eq]
  variation := ⟨by simpa only [arena,actual,realize,ProfileCell.Contains,Bool.and_eq_true,decide_eq_true_eq] using
    @containing_cell_exact,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@containing_cell_exact) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.containing_cell_exact.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.ContainingCell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ By x => @decide ((containingCell By.1 By.2).Contains x)
    (inferInstanceAs (Decidable (0 < x ∧ (containingCell By.1 By.2).lower ≤ x ∧
      x < (containingCell By.1 By.2).upper)))) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.ContainingCell

namespace Reg.D5.S3.Observer.RationalRouting.CellEvaluator

abbrev signature : Signature where
  Params := Σ _B : ℕ, Σ _y : ℚ, List Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ Byw m => (containingCell Byw.1 Byw.2.1).evaluate Byw.2.2 m) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => 0) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro _
  refine ⟨⟨1,1,[]⟩,1,2,?_⟩
  norm_num [actual,realize,ProfileCell.evaluate,containingCell,
    ProfileCell.representative,reply,attain,step]

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ), 1 ≤ B → ∀ {y : ℚ}, 0 < y →
    (containingCell B y).Contains (containingCell B y).representative ∧
    ∀ x : ℚ, (containingCell B y).Contains x → ∀ w : List Bool,
      ∀ m : ℕ, 1 ≤ m → m ≤ B →
        R.readout () ⟨B,y,w⟩ m = reply m (attain w x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : (containingCell 1 1).Contains 1 :=
    (containing_cell_exact 1 le_rfl (by norm_num) 1).mpr ⟨by norm_num,fun _ _ _ => rfl⟩
  have hh := (h 1 le_rfl (y := 1) (by norm_num)).2 1 hc [] 1 le_rfl le_rfl
  norm_num [rejected,realize,attain,reply] at hh

def family : Registration arena (type_of% (@containing_cell_evaluator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@containing_cell_evaluator,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@containing_cell_evaluator) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.containing_cell_evaluator.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.CellEvaluator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ Byw m => (containingCell Byw.1 Byw.2.1).evaluate Byw.2.2 m) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[0,2,6]
    readouts := #[{
      path := #["body","body","body","body","arg","body","body","body","body","body","body","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.CellEvaluator

namespace Reg.D5.S3.Observer.RationalRouting.FastContainingCell

abbrev signature : Signature where
  Params := ℕ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProfileCell
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ B y => fastContainingCell B y) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => ⟨0,1⟩) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro _
  refine ⟨1,1,2,?_⟩
  change fastContainingCell 1 1 ≠ fastContainingCell 1 2
  rw [fast_containing_cell_eq,fast_containing_cell_eq]
  intro h
  have hh := congrArg ProfileCell.lower h
  norm_num [containingCell,reply] at hh

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ) (y : ℚ), R.readout () B y = containingCell B y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg ProfileCell.lower (h 1 1)
  norm_num [rejected,realize,containingCell,reply] at hh

def family : Registration arena (type_of% (@fast_containing_cell_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fast_containing_cell_eq,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fast_containing_cell_eq) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.fast_containing_cell_eq.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.FastContainingCell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ B y => fastContainingCell B y) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.FastContainingCell

