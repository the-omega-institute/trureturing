import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
import Reg.Support.DependentFamily

/-! Typed source-coordinate readouts and their whole-family interventions. -/
open _root_.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
private def ones : Rows 1 1 := ⟨fun _ => 1, fun _ _ _ => le_rfl⟩
private def stair : Rows 2 1 := ⟨fun i => if i=0 then 1 else 0, by decide⟩

namespace diagrammem
abbrev signature : Signature where
  Params := (H : ℕ) × (U : ℕ) × Rows H U × ℕ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p i => ∃ hi : i < p.1, p.2.2.2 < (p.2.2.1.val ⟨i,hi⟩).val) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (H U : ℕ) (r : Rows H U) (i j : ℕ), (i,j) ∈ diagram r ↔ f.readout () ⟨H,U,r,j⟩ i
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 ones 0 0
  simp [rejected, realize, diagram_mem, ones] at hh
def family : Registration arena (type_of% @diagram_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagram_mem, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,1,ones,0⟩,0,1,?_⟩
    simp [actual, realize, ones]
def registration : Contract.Registration (@diagram_mem) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.diagram_mem.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.diagrammem.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
    definition := none
    coordinates := #[0,1,2,4]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end diagrammem

namespace diagramrowlen
abbrev signature : Signature where
  Params := (H : ℕ) × (U : ℕ) × Rows H U
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p i => (p.2.2.val i).val) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (H U : ℕ) (r : Rows H U) (i : Fin H), (diagram r).rowLen i = f.readout () ⟨H,U,r⟩ i
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 ones 0
  rw [diagram_rowLen] at hh
  norm_num [ones, rejected, realize] at hh
def family : Registration arena (type_of% @diagram_rowLen) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagram_rowLen, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨2,1,stair⟩,0,1,?_⟩
    norm_num [actual, realize, stair]
def registration : Contract.Registration (@diagram_rowLen) (type_of% actual) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.diagram_rowLen.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.diagramrowlen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fin
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end diagramrowlen

namespace conjugateinvolutive
abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := Rows p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Rows p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ r => conjugate (conjugate r)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (H U : ℕ) (r : Rows H U), f.readout () ⟨H,U⟩ r = r
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun z : Rows 1 1 => (z.val 0).val) (h 1 1 ones)
  norm_num [rejected, realize, ones] at hh
def family : Registration arena (type_of% @conjugate_involutive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conjugate_involutive, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,1⟩,ones,⟨fun _ => 0, fun _ _ _ => le_rfl⟩,?_⟩
    intro he
    have hh := congrArg (fun z : Rows 1 1 => (z.val 0).val) he
    norm_num [actual, realize, conjugate_involutive, ones] at hh
def registration : Contract.Registration (@conjugate_involutive) (type_of% actual) (ℕ → ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.conjugate_involutive.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.conjugateinvolutive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Rows
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fun","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end conjugateinvolutive

namespace boardrowcount
abbrev signature : Signature where
  Params := (U : ℕ) × (H : ℕ) × Board U H
  State p := Fin p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p i => ((boardRowsEquiv p.1 p.2.1 p.2.2).val i).val) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (U H : ℕ) (b : Board U H) (i : Fin H), Fintype.card {j : Fin U // i.val < (b.val j).val} = f.readout () ⟨U,H,b⟩ i
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 ((boardRowsEquiv 1 1).symm ones) 0
  rw [board_row_count] at hh
  norm_num [rejected, realize, ones, Equiv.apply_symm_apply] at hh
def family : Registration arena (type_of% @board_row_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@board_row_count, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      change Unit at j
      exact (hj (by cases j; cases i; rfl)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,2,(boardRowsEquiv 1 2).symm stair⟩,0,1,?_⟩
    norm_num [actual, realize, Equiv.apply_symm_apply, stair]
def registration : Contract.Registration (@board_row_count) (type_of% actual) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.board_row_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates.boardrowcount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fin
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boardrowcount

end Reg.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
