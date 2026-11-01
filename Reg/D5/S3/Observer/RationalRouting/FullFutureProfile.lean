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
  Params := ℕ
  State _ := ℚ × ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ B xy => SameFuture B xy.1 xy.2) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1,(1,1),(1,2),?_⟩
  intro he
  have ht : actual.readout () 1 (1,1) := fun _ _ _ _ => rfl
  have hf : ¬ actual.readout () 1 (1,2) := by
    intro h
    have hh := h [] 1 le_rfl le_rfl
    norm_num [attain,reply] at hh
  exact hf (Eq.mp he ht)

def arena : Arena where
  signature := signature
  Law R := ∀ {B : ℕ} {x y : ℚ}, 0 < x → 0 < y →
    (SameInstant B x y ↔ R.readout () B (x,y))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (B := 1) (x := 1) (y := 2) (by norm_num) (by norm_num)).mpr trivial
  have hb := hh 1 le_rfl le_rfl
  norm_num [reply] at hb

def family : Registration arena (type_of% (@instantaneous_iff_full_future)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@instantaneous_iff_full_future,rejected,rejected_law⟩
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
  readout := some (realize signature (fun _ B xy => SameFuture B xy.1 xy.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.FullFutureProfile

namespace Reg.D5.S3.Observer.RationalRouting.ContainingCell

abbrev signature : Signature where
  Params := ℕ × ℚ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ By x => (containingCell By.1 By.2).Contains x) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(1,1),1,0,?_⟩
  intro he
  have ht : actual.readout () (1,1) 1 :=
    (containing_cell_exact 1 le_rfl (by norm_num) 1).mpr ⟨by norm_num,fun _ _ _ => rfl⟩
  have hf : ¬ actual.readout () (1,1) 0 := by
    intro h
    exact (lt_irrefl 0) h.1
  exact hf (Eq.mp he ht)

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ), 1 ≤ B → ∀ {y : ℚ}, 0 < y → ∀ x : ℚ,
    R.readout () (B,y) x ↔ 0 < x ∧ SameInstant B x y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 le_rfl (y := 1) (by norm_num) 0).mp trivial
  norm_num at hh

def family : Registration arena (type_of% (@containing_cell_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@containing_cell_exact,rejected,rejected_law⟩
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
  readout := some (realize signature (fun _ By x => (containingCell By.1 By.2).Contains x) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.ContainingCell

namespace Reg.D5.S3.Observer.RationalRouting.CellEvaluator

abbrev signature : Signature where
  Params := ℕ × ℚ × ℕ
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ Bym w => (containingCell Bym.1 Bym.2.1).evaluate w Bym.2.2) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => 0) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(1,1,1),[],[true],?_⟩
  norm_num [actual,realize,ProfileCell.evaluate,containingCell,
    ProfileCell.representative,reply,attain,step]

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ), 1 ≤ B → ∀ {y : ℚ}, 0 < y →
    (containingCell B y).Contains (containingCell B y).representative ∧
    ∀ x : ℚ, (containingCell B y).Contains x → ∀ w : List Bool,
      ∀ m : ℕ, 1 ≤ m → m ≤ B →
        R.readout () (B,y,m) w = reply m (attain w x)

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
  readout := some (realize signature (fun _ Bym w => (containingCell Bym.1 Bym.2.1).evaluate w Bym.2.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.FullFutureProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","body","body","body","body","body","body","fn","arg"]
      stateBinder := 6
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
    coordinates := #[]
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

