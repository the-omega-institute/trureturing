import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Polyomino.UXPentominoBounds

/-! Board area and minimum-area observations for the U and X pentomino bounds. -/

namespace Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory (Point)
open _root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates (squareGrid)
open _root_.D5.S3.Combinatorics.Polyomino.LPolyominoSkippedSequence (instances IsPolyomino a)
open _root_.D5.S3.Combinatorics.Polyomino.UXPentominoBounds

private theorem self_count_pos (T : Finset Point) (hT : T.Nonempty) :
    0 < (instances T T).card := by
  classical
  obtain ⟨c, hc⟩ := hT
  apply Finset.card_pos.mpr
  refine ⟨0, mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact mem_biUnion.mpr ⟨c, hc, mem_image.mpr ⟨c, hc, sub_self c⟩⟩
  · intro v hv
    simpa using hv

private theorem singleton_board : IsPolyomino ({0} : Finset Point) := by
  refine ⟨⟨0, by simp⟩, ?_⟩
  intro p hp q hq
  rw [mem_singleton.mp hp, mem_singleton.mp hq]

private abbrev boardSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset Point) (fun _ => ℕ)

def area : Realization boardSignature :=
  realize boardSignature (fun _ _ P => P.card) (fun e => nomatch e)

def erasedArea : Realization boardSignature :=
  realize boardSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem area_dependence : ObservationalDependence boardSignature area := by
  intro i
  exact ⟨(), ∅, {0}, Nat.zero_ne_one⟩

private def boundArena (T : Finset Point) : Arena where
  signature := boardSignature
  Law R := ∀ P : Finset Point, 0 < (instances P T).card →
    (instances P T).card + 2 ≤ R.readout () () P ∧
      8 * (instances P T).card ≤ (P.card - (instances P T).card - 2) ^ 2 + 4

private theorem erased_bound (T : Finset Point) (hT : T.Nonempty) :
    ¬ (boundArena T).Law erasedArea := by
  intro h
  have hzero := (h T (self_count_pos T hT)).1
  change (instances T T).card + 2 ≤ 0 at hzero
  omega

def uFamily : Registration (boundArena U) (type_of% (@u_card_bound)) where
  actual := area
  bridge := Iff.rfl
  variation := ⟨u_card_bound, erasedArea, erased_bound U (by decide)⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ area erasedArea
    (erased_bound U (by decide))
  dependence := area_dependence

def xFamily : Registration (boundArena X) (type_of% (@x_card_bound)) where
  actual := area
  bridge := Iff.rfl
  variation := ⟨x_card_bound, erasedArea, erased_bound X (by decide)⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ area erasedArea
    (erased_bound X (by decide))
  dependence := area_dependence

def transferArena : Arena where
  signature := boardSignature
  Law R := ∀ P : Finset Point, IsPolyomino P →
    ∃ Q : Finset Point, IsPolyomino Q ∧ (instances P X).card ≤ (instances Q U).card ∧
      Q.card = R.readout () () P

private theorem erased_transfer : ¬ transferArena.Law erasedArea := by
  intro h
  obtain ⟨Q, hQ, _, hz⟩ := h {0} singleton_board
  exact (Nat.ne_of_gt (card_pos.mpr hQ.1)) hz

def transferFamily : Registration transferArena (type_of% (@u_board_of_x_board)) where
  actual := area
  bridge := Iff.rfl
  variation := ⟨u_board_of_x_board, erasedArea, erased_transfer⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ area erasedArea erased_transfer
  dependence := area_dependence

private theorem x_board : IsPolyomino X := by
  have hz : (0 : Point) ∈ X := by decide
  have toOrigin (p : Point) (hp : p ∈ X) : p = 0 ∨ squareGrid.Adj p 0 := by
    simp only [X, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact Or.inl rfl | exact Or.inr (by decide)
  refine ⟨⟨0, hz⟩, ?_⟩
  intro p hp q hq
  have inward : Relation.ReflTransGen (fun v w => v ∈ X ∧ w ∈ X ∧ squareGrid.Adj v w)
      p 0 := by
    rcases toOrigin p hp with rfl | h
    · exact .refl
    · exact .single ⟨hp, hz, h⟩
  have outward : Relation.ReflTransGen (fun v w => v ∈ X ∧ w ∈ X ∧ squareGrid.Adj v w)
      0 q := by
    rcases toOrigin q hq with rfl | h
    · exact .refl
    · exact .single ⟨hz, hq, squareGrid.symm.symm _ _ h⟩
  exact inward.trans outward

private theorem x_one_gt_one : 1 < a X 1 := by
  let sizes : Set ℕ := {s | ∃ P : Finset Point,
    IsPolyomino P ∧ 1 ≤ (instances P X).card ∧ P.card = s}
  have hX : sizes.Nonempty := ⟨X.card, X, x_board, self_count_pos X (by decide), rfl⟩
  obtain ⟨P, _, hP, hcard⟩ := Nat.sInf_mem hX
  change 1 < sInf sizes
  rw [← hcard]
  have h := (x_card_bound P hP).1
  omega

private theorem x_zero_le_one : a X 0 ≤ 1 := by
  apply Nat.sInf_le
  exact ⟨{0}, singleton_board, Nat.zero_le _, by simp⟩

private abbrev thresholdSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

noncomputable def xMinimum : Realization thresholdSignature :=
  realize thresholdSignature (fun _ _ N => a X N) (fun e => nomatch e)

def erasedMinimum : Realization thresholdSignature :=
  realize thresholdSignature (fun _ _ _ => 0) (fun e => nomatch e)

def equalityArena : Arena where
  signature := thresholdSignature
  Law R := ∀ N : ℕ, 0 < N → a U N = R.readout () () N

private theorem erased_equality : ¬ equalityArena.Law erasedMinimum := by
  intro h
  have hzero := h 1 (by decide)
  change a U 1 = 0 at hzero
  rw [same_minimum 1 (by decide)] at hzero
  have := x_one_gt_one
  omega

noncomputable def equalityFamily : Registration equalityArena (type_of% (@same_minimum)) where
  actual := xMinimum
  bridge := Iff.rfl
  variation := ⟨same_minimum, erasedMinimum, erased_equality⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ xMinimum erasedMinimum
    erased_equality
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change a X 0 ≠ a X 1
    exact Nat.ne_of_lt (lt_of_le_of_lt x_zero_le_one x_one_gt_one)

noncomputable def uBoundRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.u_card_bound)
      (Realization boardSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds.u_card_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.uFamily
  realizationSource := none
  generated := false
  arena := .source ⟨(boundArena U)⟩
  objectArena := .source ⟨(boundArena U)⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (boundArena U) ⟨uFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boardSignature area.readout area.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def xBoundRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.x_card_bound)
      (Realization boardSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds.x_card_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.xFamily
  realizationSource := none
  generated := false
  arena := .source ⟨(boundArena X)⟩
  objectArena := .source ⟨(boundArena X)⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (boundArena X) ⟨xFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boardSignature area.readout area.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def transferRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.u_board_of_x_board)
      (Realization boardSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds.u_board_of_x_board.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.transferFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transferArena⟩
  objectArena := .source ⟨transferArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transferArena ⟨transferFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boardSignature area.readout area.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def equalityRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.same_minimum)
      (Realization thresholdSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds.same_minimum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds.equalityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨equalityArena⟩
  objectArena := .source ⟨equalityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalityArena ⟨equalityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature xMinimum.readout xMinimum.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.UXPentominoBounds
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Polyomino.UXPentominoBounds
