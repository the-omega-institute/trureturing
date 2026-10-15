import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination

namespace Reg.D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination

open Set Filter _root_.Topology
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open _root_.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open _root_.D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal
open _root_.D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
open _root_.D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape

def certificate (N : Branch → Set ℕ) : Prop :=
  (∀ x, natBranch x ⊆ N x) ∧ MADFamily (range N) ∧
  (∀ x, ConvergesOn natValue (N x) (limitValue x)) ∧
  (∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal N (natValue ⁻¹' V)) ∧
  ¬ ∃ D : Set ℕ, Partitions N D ∧
    {n | (natValue n : ℝ) ≤ (1 : ℝ)/3} ⊆ D ∧
    D ⊆ {n | (natValue n : ℝ) < (2 : ℝ)/3}

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
  DependentFamily.realize signature (fun _ _ N => certificate N) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ p, ∃ N, r.readout () p N

abbrev sourceScope := type_of% (@exists_mad_no_threshold_partitioner)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h _
    exact h
  · intro h
    exact h ()

theorem actual_positive : arena.Law actual :=
  source_bridge.mp exists_mad_no_threshold_partitioner

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N,hN⟩ := h ()
  exact hN

def emptyFamily : Branch → Set ℕ := fun _ => ∅

theorem empty_invalid : ¬ certificate emptyFamily := by
  intro h
  let x : Branch := fun _ => (false,false)
  have hn : wordEquivNat (wordPrefix x 0) ∈ natBranch x :=
    ⟨wordPrefix x 0,⟨0,rfl⟩,rfl⟩
  exact h.1 x hn

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨N,hN⟩ := actual_positive ()
    refine ⟨(),N,emptyFamily,?_⟩
    intro h
    change certificate N = certificate emptyFamily at h
    exact empty_invalid (h ▸ hN)

/-- This attempt retains all five clauses and actual family variation. Raw source
reconstruction/sourceSelection is unfinished; no validated audit is asserted.
The same missing boundary is disclosed under issue #16293. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_mad_no_threshold_partitioner) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination.exists_mad_no_threshold_partitioner.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination.familyRegistration
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
    (fun _ _ N => certificate N) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Branch → Set ℕ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination
