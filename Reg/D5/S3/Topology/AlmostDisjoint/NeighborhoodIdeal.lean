import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal

/-!
The source state is the actual natural-number family. The readout retains
all branch, AD, maximality, convergence and neighborhood-ideal conclusions.
Source occurrence selection remains unspecified, so this is an unresolved
registration attempt rather than a validated binding.
-/

open Set Filter Topology

namespace Reg.D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open _root_.D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open _root_.D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open _root_.D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
open _root_.D5.S3.ConceptDynamics.InformationEscape

def certificate (M : Branch → Set ℕ) : Prop :=
  (∀ x, natBranch x ⊆ M x) ∧
  (∀ x y, x ≠ y → (M x ∩ M y).Finite) ∧ MADFamily (range M) ∧
  (∀ x, ConvergesOn natValue (M x) (limitValue x)) ∧
  ∀ (r : unitInterval) (V : Set unitInterval), V ∈ 𝓝 r →
    ¬ InFiniteUnionIdeal M (natValue ⁻¹' V)

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
  Law := fun r => ∀ P, ∃ M, r.readout () P M

abbrev existenceScope := type_of% (@exists_mad_with_no_small_neighborhood)

theorem source_bridge : existenceScope ↔ arena.Law actual := by
  constructor
  · intro h _
    exact h
  · intro h
    exact h ()

theorem actual_positive : arena.Law actual :=
  source_bridge.mp exists_mad_with_no_small_neighborhood

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hfalse⟩ := h ()
  exact hfalse

private theorem empty_invalid : ¬ certificate (fun _ => ∅) := by
  intro h
  let x : Branch := fun _ => (false, false)
  have hn : wordEquivNat (wordPrefix x 0) ∈ natBranch x :=
    ⟨wordPrefix x 0, ⟨0, rfl⟩, rfl⟩
  exact h.1 x hn

def familyRegistration : DependentFamily.Registration arena existenceScope where
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
    refine ⟨(), M, (fun _ => ∅), ?_⟩
    intro h
    change certificate M = certificate (fun _ => ∅) at h
    exact empty_invalid (h ▸ hM)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_mad_with_no_small_neighborhood)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal.exists_mad_with_no_small_neighborhood.__information_unit
  realizationName := `Reg.D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal.familyRegistration
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
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev thresholdScope := type_of% (@threshold_common_color_support)

theorem threshold_actual : thresholdScope := @threshold_common_color_support

end Reg.D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
