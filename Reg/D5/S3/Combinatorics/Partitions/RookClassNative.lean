import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.RookClassNative
import Reg.Support.DependentFamily

/-! Source-bound audit of the literal one-rook area readout. -/

open _root_.D5.S3.Combinatorics.Partitions.RookClassNative
open _root_.D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.RookClassNative.OneRook

private def empty : PositiveColumns := ⟨[],by
  constructor
  · exact (show ([] : List ℕ).Pairwise (· ≤ ·) from by simp).sortedLE
  · simp⟩
private def one : PositiveColumns := ⟨[1],by decide⟩

abbrev signature : Signature where
  Params := ℕ
  State _ := PositiveColumns
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ b => area b) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law f := ∀ (m : ℕ) (b : PositiveColumns), rookCount m b 1 = f.readout () m b

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 one
  rw [rookCount_one] at hh
  norm_num [rejected,realize,area,one] at hh

def family : Registration arena (type_of% @rookCount_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rookCount_one, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1,empty,one,?_⟩
    norm_num [actual,realize,area,empty,one]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rookCount_one) (type_of% actual) Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.RookClassNative.rookCount_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.RookClassNative.OneRook.family
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
  escapeFrom := some PositiveColumns
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.RookClassNative
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

end Reg.D5.S3.Combinatorics.Partitions.RookClassNative.OneRook
