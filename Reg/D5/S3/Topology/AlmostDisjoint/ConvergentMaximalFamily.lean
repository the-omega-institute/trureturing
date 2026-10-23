import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily

namespace Reg.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily

open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape

/-- All original source clauses, including actual unrestricted maximality. -/
def certificate (M : Set (Set Word)) : Prop :=
  Set.range branchSet ⊆ M ∧ MADFamily M ∧
    ∀ A ∈ M, ∃ r : unitInterval, ConvergesOn wordValue A r

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Set (Set Word)
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

abbrev sourceScope := type_of% (@exists_convergent_mad)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h _
    exact h
  · intro h
    exact h ()

theorem actual_positive : arena.Law actual := source_bridge.mp exists_convergent_mad

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, hM⟩ := h ()
  exact hM

def emptyFamily : Set (Set Word) := ∅

theorem empty_invalid : ¬ certificate emptyFamily := by
  intro h
  let x : Branch := fun _ => (false, false)
  exact h.1 (Set.mem_range_self x)

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
      (@exists_convergent_mad) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily.exists_convergent_mad.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily.familyRegistration
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
  escapeFrom := some (Set (Set Word))
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
