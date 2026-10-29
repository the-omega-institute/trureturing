import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.BarreseAllWidths
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.BarreseAllWidths
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.BarreseAllWidths

namespace allwidthcount

abbrev signature : Signature where
  Params := ℕ
  State p := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ r a => count r (a.getD 0 0) a ⟨a.getD 0 0,Nat.lt_succ_self _⟩) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (r : ℕ) (a : List ℕ), (Nat.card (ShapeFiber (r+1) a) : ℤ) = f.readout () r a

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 []
  rw [all_width_count] at hh
  norm_num [rejected, realize, count, transition, gauss] at hh

def family : Registration arena (type_of% @all_width_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨all_width_count, rejected, bad⟩
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
    refine ⟨0,[],[0,1],?_⟩
    norm_num [actual, realize, count, transition, gauss, Fin.sum_univ_succ, Polynomial.coeff_one]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@all_width_count) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseAllWidths.all_width_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseAllWidths.allwidthcount.family
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
  escapeFrom := some (List ℕ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.BarreseAllWidths
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end allwidthcount

namespace widthbound
abbrev signature : Signature where
  Params := ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ a => a.getD 0 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (r : ℕ) (a : List ℕ) (μ : ShapeFiber (r+1) a),
    μ.val.rowLen 0 ≤ f.readout () r a
private def ones : Rows 1 1 := ⟨fun _ => 1, fun _ _ _ => le_rfl⟩
private def oneShape : ShapeFiber 1 [1] := ⟨diagram ones, by
  intro p
  by_cases hp : p = 0
  · subst p
    simpa [shapeLevel, ones] using diagram_rowLen ones (0 : Fin 1)
  · have hz : (diagram ones).rowLen p = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      have hh := YoungDiagram.mem_iff_lt_rowLen.mpr h
      obtain ⟨hi,_⟩ := (diagram_mem ones p 0).mp hh
      omega
    simp only [shapeLevel, Fin.sum_univ_one, Fin.val_zero, Nat.mul_one,
      Nat.one_mul, Nat.add_zero, hz]
    rw [List.getD_eq_default [1] 0 (show [1].length ≤ p by simpa using (show 1 ≤ p by omega))]⟩
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 [1] oneShape
  change (diagram ones).rowLen 0 ≤ 0 at hh
  have hx := diagram_rowLen ones (0 : Fin 1)
  change (diagram ones).rowLen 0 = 1 at hx
  omega

def family : Registration arena (type_of% @width_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨width_bound, rejected, bad⟩
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
    refine ⟨0,[],[1],?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@width_bound) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseAllWidths.width_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseAllWidths.widthbound.family
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
  escapeFrom := some (List ℕ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.BarreseAllWidths
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end widthbound

end Reg.D5.S3.Combinatorics.Partitions.BarreseAllWidths
