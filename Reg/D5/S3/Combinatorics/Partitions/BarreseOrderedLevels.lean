import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open _root_.D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.BarreseOrderedLevels

namespace nativecount

abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p a => count p.1 p.2 a ⟨p.2,Nat.lt_succ_self _⟩) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (r U : ℕ) (a : List ℕ), (Fintype.card (NativeFiber (r+1) U a) : ℤ) = f.readout () ⟨r,U⟩ a

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 []
  rw [native_count] at hh
  norm_num [rejected, realize, count, transition, gauss] at hh

def family : Registration arena (type_of% @native_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_count, rejected, bad⟩
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
    refine ⟨⟨0,0⟩,[],[1],?_⟩
    norm_num [actual, realize, count, transition, gauss, Fin.sum_univ_succ, Polynomial.coeff_one]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@native_count) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseOrderedLevels.native_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseOrderedLevels.nativecount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
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

end nativecount

namespace source2023count
abbrev signature : Signature where
  Params := (m : ℕ) × (n : ℕ) × PLift (0 < m)
  State p := Fin p.2.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p l => count (p.1-1) p.2.1 (List.ofFn (fun i => l i.rev))
    ⟨p.2.1,Nat.lt_succ_self _⟩) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (m n : ℕ) (hm : 0 < m) (l : Fin n → ℕ),
    (Fintype.card {b : Board n (m*n) // ∀ p : Fin n, levelTotal b p = l p.rev} : ℤ) =
      f.readout () ⟨m,n,⟨hm⟩⟩ l
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 (by decide) (fun i => nomatch i)
  rw [source2023_count 1 0 (by decide)] at hh
  norm_num [rejected, realize, count] at hh
def family : Registration arena (type_of% @source2023_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source2023_count, rejected, bad⟩
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
    refine ⟨⟨1,1,⟨by decide⟩⟩,(fun _ => 0),(fun _ => 2),?_⟩
    norm_num [actual, realize, count, transition, gauss, Fin.sum_univ_succ,
      List.ofFn_succ, Polynomial.coeff_one]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@source2023_count) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.BarreseOrderedLevels.source2023_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.BarreseOrderedLevels.source2023count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
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

end source2023count

end Reg.D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
