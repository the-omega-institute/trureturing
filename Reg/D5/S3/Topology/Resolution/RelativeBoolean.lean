import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Resolution.RelativeBoolean

/-!
# Actual fiber-membership source family

Parameters retain the complete singleton-fiber telescope. The actual readout
is membership of a resolution point in the original projection fiber. The
source bridge is exact set extensionality. Raw source selection and the
escape-origin identity are not supplied by this family evidence.
-/

namespace Reg.D5.S3.Topology.Resolution.RelativeBoolean

open Set
open _root_.D5.S3.Topology.Resolution.RelativeBoolean
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure Inputs where
  X : Type u
  topX : TopologicalSpace X
  C : Set X
  c : X
  hc : c ∈ C

def State (P : Inputs.{u}) : Type u := letI := P.topX; Space P.C

def membership (P : Inputs.{u}) (y : State P) : Prop :=
  letI := P.topX
  projection P.C y = P.c

def singleton (P : Inputs.{u}) (y : State P) : Prop :=
  letI := P.topX
  y = point P.C P.c

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P y => membership P y) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ P y, r.readout () P y ↔ singleton P y

abbrev sourceScope := type_of% (@fiber_singleton.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P y
    let := P.topX
    exact Set.ext_iff.mp (@h P.X P.topX P.C P.c P.hc) y
  · intro h X topX C c hc
    apply Set.ext
    intro y
    exact h ⟨X, topX, C, c, hc⟩ y

theorem actual_positive : arena.{u}.Law actual.{u} := source_bridge.mp (@fiber_singleton.{u})

def sample : Inputs.{u} where
  X := ULift.{u} Bool
  topX := inferInstance
  C := univ
  c := ULift.up false
  hc := mem_univ _

noncomputable def firstPoint : State sample.{u} := by
  letI := sample.{u}.topX
  exact point _ (ULift.up false)

noncomputable def secondPoint : State sample.{u} := by
  letI := sample.{u}.topX
  exact point _ (ULift.up true)

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h sample firstPoint).mpr rfl

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
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
    cases i
    refine ⟨sample, firstPoint, secondPoint, ?_⟩
    intro heq
    have hp : actual.readout () sample firstPoint := rfl
    rw [heq] at hp
    change (ULift.up true : ULift.{u} Bool) = ULift.up false at hp
    cases congrArg ULift.down hp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@fiber_singleton.{u}) (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Topology.Resolution.RelativeBoolean.fiber_singleton.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.RelativeBoolean.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ P y => membership P y) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Resolution.RelativeBoolean
