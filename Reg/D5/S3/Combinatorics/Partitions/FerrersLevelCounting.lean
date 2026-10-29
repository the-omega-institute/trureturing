import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.FerrersLevelCounting
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.FerrersLevelCounting

namespace pathscard

abbrev signature : Signature where
  Params := (r : ℕ) × (U : ℕ) × List ℕ
  State p := Fin (p.2.1+1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => count p.1 p.2.1 p.2.2 u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (r U : ℕ) (a : List ℕ) (u : Fin (U+1)), (Fintype.card (Paths r U a u) : ℤ) = f.readout () ⟨r,U,a⟩ u

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 [] 0
  rw [paths_card] at hh
  norm_num [rejected, realize, count, transition, gauss] at hh

def family : Registration arena (type_of% @paths_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨paths_card, rejected, bad⟩
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
    refine ⟨⟨0,1,[1]⟩,0,1,?_⟩
    norm_num [actual, realize, count, transition, gauss, Fin.sum_univ_succ, Polynomial.coeff_one]

def registration : Contract.Registration (@paths_card) (type_of% actual) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.FerrersLevelCounting.paths_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.FerrersLevelCounting.pathscard.family
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
    owner := `D5.S3.Combinatorics.Partitions.FerrersLevelCounting
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

end pathscard

end Reg.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
