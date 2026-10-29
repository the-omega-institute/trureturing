import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
namespace source2015count
abbrev signature : Signature where
  Params := (m : ℕ) × PLift (0 < m)
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p c => if (∀ x ∈ c, 0 < x) then
    count (p.1-1) (c.reverse.getD 0 0) c.reverse
      ⟨c.reverse.getD 0 0,Nat.lt_succ_self _⟩ else 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (m : ℕ) (hm : 0 < m) (c : List ℕ),
    (Nat.card (LFiber m c) : ℤ) = f.readout () ⟨m,⟨hm⟩⟩ c
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) []
  rw [source2015_count 1 (by decide)] at hh
  norm_num [rejected, realize, count] at hh
def family : Registration arena (type_of% @source2015_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source2015_count, rejected, bad⟩
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
    refine ⟨⟨1,⟨by decide⟩⟩,[],[0],?_⟩
    simp [actual, realize, count]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@source2015_count) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseSourceNormalization.source2015_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization.source2015count.family
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
    owner := `D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end source2015count
namespace loperatorcount
abbrev signature : Signature where
  Params := (m : ℕ) × PLift (0 < m)
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p c => if (∀ x ∈ c, 0 < x) then
    count (p.1-1) (c.reverse.getD 0 0) c.reverse
      ⟨c.reverse.getD 0 0,Nat.lt_succ_self _⟩ else 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (m : ℕ) (hm : 0 < m) (c : List ℕ),
    (Nat.card {b : PositiveColumns // lOperator m b = c} : ℤ) = f.readout () ⟨m,⟨hm⟩⟩ c
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) []
  rw [lOperator_count 1 (by decide)] at hh
  norm_num [rejected, realize, count] at hh
def family : Registration arena (type_of% @lOperator_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lOperator_count, rejected, bad⟩
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
    refine ⟨⟨1,⟨by decide⟩⟩,[],[0],?_⟩
    simp [actual, realize, count]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@lOperator_count) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseSourceNormalization.lOperator_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization.loperatorcount.family
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
    owner := `D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end loperatorcount

end Reg.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
