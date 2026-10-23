import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

namespace Reg.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open _root_.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape

/-- The state is the actual proposed family on Nat, with all three source clauses. -/
def certificate (M : Branch → Set ℕ) : Prop :=
  (∀ x, natBranch x ⊆ M x) ∧
    (∀ x y, x ≠ y → (M x ∩ M y).Finite) ∧ MADFamily (Set.range M) ∧
    (∀ x, ConvergesOn natValue (M x) (limitValue x))

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Branch → Set ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ M => certificate M) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ p, ∃ M, r.readout () p M

abbrev sourceScope := type_of% (@exists_branch_labeled_mad)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h _
    exact h
  · intro h
    exact h ()

theorem actual_positive : arena.Law actual := source_bridge.mp exists_branch_labeled_mad

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, hM⟩ := h ()
  exact hM

def emptyFamily : Branch → Set ℕ := fun _ => ∅

theorem empty_invalid : ¬ certificate emptyFamily := by
  intro h
  let x : Branch := fun _ => (false, false)
  have hn : wordEquivNat (wordPrefix x 0) ∈ natBranch x :=
    ⟨wordPrefix x 0, ⟨0, rfl⟩, rfl⟩
  exact h.1 x hn

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨M, hM⟩ := actual_positive ()
    refine ⟨(), M, emptyFamily, ?_⟩
    intro h
    change certificate M = certificate emptyFamily at h
    exact empty_invalid (h ▸ hM)

/-- The source selection remains unspecified. This records compiled family evidence,
without asserting validated raw occurrence reconstruction or source binding. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_branch_labeled_mad) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily.exists_branch_labeled_mad.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ M => certificate M) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Branch → Set ℕ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

universe v

/-- The original finite-union supplier is now exposed for direct consumption.
Its whole source telescope is checked here; raw occurrence/sourceSelection and
faithful variation of this finite-family arena remain unfinished under #16293.
This exact scope check does not assert validated four-slot reconstruction. -/
abbrev finiteUnionSourceScope := type_of% (@finite_sUnion_converges.{v})

theorem finite_union_source_actual : finiteUnionSourceScope.{v} := @finite_sUnion_converges.{v}

end Reg.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
