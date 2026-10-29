import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer

abbrev signature : Signature where
  Params := (r : ℕ) × (U : ℕ) × (a : ℕ) × Fin (U+1)
  State p := Fin (p.2.1+1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => transition p.1 p.2.1 p.2.2.1 p.2.2.2 v) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (r U a : ℕ) (u v : Fin (U+1)),
    (Fintype.card (Level r U u.val v.val a) : ℤ) = f.readout () ⟨r,U,a,u⟩ v

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 0 0
  rw [level_card] at hh
  norm_num [rejected, realize, transition, gauss] at hh

def family : Registration arena (type_of% @level_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨level_card, rejected, bad⟩
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
    refine ⟨⟨0,1,0,1⟩,0,1,?_⟩
    norm_num [actual, realize, transition, gauss]

def registration : Contract.Registration (@level_card) (type_of% actual) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersLevelTransfer.level_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer.family
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
    owner := `D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
