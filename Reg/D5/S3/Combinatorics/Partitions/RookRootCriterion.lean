import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.RookRootCriterion
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.RookRootCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.RookRootCriterion

abbrev signature : Signature where
  Params := (m : ℕ) × PLift (0 < m) × ℕ
  State p := Fin p.2.2 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p d => SingletonColumns p.1 d) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f := ∀ (m : ℕ) (hm : 0 < m) (N : ℕ) (d : Fin N → ℕ),
    Monotone d → (RootFloorCriterion m (root m d) ↔ f.readout () ⟨m,⟨hm⟩,N⟩ d)

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) 1 (fun _ => 0) (fun _ _ _ => le_rfl)
  change RootFloorCriterion 1 (root 1 (fun _ : Fin 1 => 0)) ↔ False at hh
  apply hh.mp
  intro i j _ hi
  simp at hi

def family : Registration arena (type_of% @rootFloorCriterion_iff_singleton) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rootFloorCriterion_iff_singleton, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro i
    refine ⟨⟨2,⟨by decide⟩,2⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change SingletonColumns 2 (fun _ : Fin 2 => 0) ≠ SingletonColumns 2 (fun _ : Fin 2 => 1)
    have hgood : SingletonColumns 2 (fun _ : Fin 2 => 0) := by decide
    have hbad : ¬ SingletonColumns 2 (fun _ : Fin 2 => 1) := by decide
    exact fun h => hbad (h.mp hgood)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rootFloorCriterion_iff_singleton) (type_of% actual) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.RookRootCriterion.rootFloorCriterion_iff_singleton.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.RookRootCriterion.family
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
  escapeFrom := some (fun N : ℕ => Fin N → ℕ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.RookRootCriterion
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.RookRootCriterion
