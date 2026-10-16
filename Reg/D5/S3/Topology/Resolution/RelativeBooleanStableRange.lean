import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Resolution.RelativeBooleanStableRange

/-!
# Stable-image membership as a source-bound family

The family retains arbitrary source carriers, topologies and continuous maps.
Its state is an actual point of the relative graph closure and its readout is
membership in the actual upstairs stable range. The original equality is
reconstructed by extensionality, without a supplied equality hypothesis.
Raw source selection and the escape-origin binding remain unresolved.
-/

namespace Reg.D5.S3.Topology.Resolution.RelativeBooleanStableRange

open Set Function
open _root_.D5.S1.Dynamics
open _root_.D5.S3.Topology.Resolution.RelativeBoolean
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure Inputs where
  X : Type u
  topX : TopologicalSpace X
  f : X → X
  hf : @Continuous X X topX topX f

def State (P : Inputs.{u}) : Type u :=
  letI := P.topX
  Space (StableRange.core P.f)

def upstairs (P : Inputs.{u}) (y : State P) : Prop :=
  letI := P.topX
  y ∈ StableRange.core (stableLift P.f P.hf)

def downstairs (P : Inputs.{u}) (y : State P) : Prop :=
  letI := P.topX
  projection (StableRange.core P.f) y ∈ StableRange.core P.f

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
  DependentFamily.realize signature (fun _ P y => upstairs P y) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ P y, r.readout () P y ↔ downstairs P y

abbrev sourceScope := type_of% (@stable_range_lift_eq_preimage.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P y
    let := P.topX
    exact Set.ext_iff.mp (@h P.X P.topX P.f P.hf) y
  · intro h X topX f hf
    apply Set.ext
    intro y
    exact h ⟨X, topX, f, hf⟩ y

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@stable_range_lift_eq_preimage.{u})

def sample : Inputs.{u} where
  X := ULift.{u} Bool
  topX := inferInstance
  f := fun _ => ULift.up false
  hf := continuous_const

noncomputable def stablePoint : State sample.{u} := by
  letI := sample.{u}.topX
  exact point _ (ULift.up false)
noncomputable def transientPoint : State sample.{u} := by
  letI := sample.{u}.topX
  exact point _ (ULift.up true)

theorem stable_mem : downstairs sample.{u} stablePoint := by
  change ULift.up false ∈ StableRange.core (fun _ : ULift.{u} Bool => ULift.up false)
  apply mem_iInter.mpr
  intro n
  refine ⟨ULift.up false, ?_⟩
  cases n with
  | zero => rfl
  | succ n => rw [Function.iterate_succ_apply']

theorem transient_not_mem : ¬ downstairs sample.{u} transientPoint := by
  intro h
  obtain ⟨a, ha⟩ := mem_iInter.mp h 1
  change (ULift.up false : ULift.{u} Bool) = ULift.up true at ha
  have hbad : (false : Bool) = true := congrArg ULift.down ha
  cases hbad

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h sample stablePoint).mpr stable_mem

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
    refine ⟨sample, stablePoint, transientPoint, ?_⟩
    intro heq
    have hs := (actual_positive sample stablePoint).mpr stable_mem
    rw [heq] at hs
    have ht : actual.readout () sample transientPoint := hs
    exact transient_not_mem ((actual_positive sample transientPoint).mp ht)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@stable_range_lift_eq_preimage.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Topology.Resolution.RelativeBoolean.stable_range_lift_eq_preimage.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.RelativeBooleanStableRange.familyRegistration
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
    (fun _ P y => upstairs P y) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Resolution.RelativeBooleanStableRange
