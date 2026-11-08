import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.LiLiZhaoFiniteCRT

/-!
# Common-open intersection source family

The actual observation is nonempty intersection of two arbitrary subsets of
Nat. The source law restricts both subsets to nonempty common opens and
retains their actual shared intersection. The bridge and whole-family
variation, sensitivity and observational dependence are typed evidence.
Raw reconstruction of this readout inside IsIrreducible remains unspecified;
this is an unfinished registration, not a validated four-slot audit.
-/

namespace Reg.D5.S3.Topology.LiLiZhaoFiniteCRT

open _root_.D5.S3.Topology.LiLiZhaoFiniteCRT
open _root_.D5.S3.ConceptDynamics.InformationEscape

abbrev sourceScope := type_of% (@commonTopology_univ_irreducible)

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Set ℕ × Set ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ _ uv => (uv.1 ∩ uv.2).Nonempty) (fun e => Empty.elim e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ U V : Set ℕ,
    @IsOpen ℕ commonTopology U → @IsOpen ℕ commonTopology V →
    U.Nonempty → V.Nonempty → r.readout () () (U, V)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h U V hU hV hUn hVn
    change (U ∩ V).Nonempty
    simpa only [Set.univ_inter] using
      h.2 U V hU hV (by simpa only [Set.univ_inter] using hUn)
        (by simpa only [Set.univ_inter] using hVn)
  · intro h
    refine ⟨Set.univ_nonempty, ?_⟩
    intro U V hU hV hUn hVn
    have hv := h U V hU hV (by simpa only [Set.univ_inter] using hUn)
      (by simpa only [Set.univ_inter] using hVn)
    change (U ∩ V).Nonempty at hv
    simpa only [Set.univ_inter] using hv

theorem actual_positive : arena.Law actual :=
  source_bridge.mp commonTopology_univ_irreducible

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun e => Empty.elim e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h Set.univ Set.univ (@isOpen_univ ℕ commonTopology)
    (@isOpen_univ ℕ commonTopology) Set.univ_nonempty Set.univ_nonempty

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
    · intro e
      exact Empty.elim e
  dependence := by
    intro i
    refine ⟨(), (Set.univ, Set.univ), (∅, Set.univ), ?_⟩
    change (Set.univ ∩ Set.univ : Set ℕ).Nonempty ≠ (∅ ∩ Set.univ : Set ℕ).Nonempty
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@commonTopology_univ_irreducible)
      (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Topology.LiLiZhaoFiniteCRT.commonTopology_univ_irreducible.__information_unit
  realizationName := `Reg.D5.S3.Topology.LiLiZhaoFiniteCRT.familyRegistration
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
    (fun _ _ uv => (uv.1 ∩ uv.2).Nonempty) (fun e => Empty.elim e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.LiLiZhaoFiniteCRT
