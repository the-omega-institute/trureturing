/- UNCOMPILED PRIVATE CANDIDATE. No Lean/Lake/producer execution is claimed.
   Intended placement, after a separately authorized check: the source owner's
   Reg/D5/S3/Topology/Measures/RegularSignedLift.lean. This file is not enrolled
   or integrated and does not replace any accepted or unresolved source.
   The source observation is the original topology argument of Regular in the
   conclusion, not the sum-valued observer attempted in A2. -/

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.RegularSignedLift
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic

namespace Reg.D5.S3.Topology.Measures.RegularSignedLift.TopologyOccurrenceCandidate

set_option autoImplicit false
universe u

open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape

abbrev originalScope :=
  type_of% (@_root_.D5.S3.Topology.Measures.RegularSignedLift.regular_add.{u})

-- One selected coordinate: the original K binder. No dictionary coordinate.
abbrev signature : DependentFamily.Signature where
  Params := Type u
  State := fun K => TopologicalSpace K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ K => TopologicalSpace K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ t => t)
    (fun a => Empty.elim a)

-- Keep every original binder, including binder modes and arbitrary instances.
-- Only the topology argument of the conclusion's Regular is an observation.
def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r =>
    ∀ {K : Type u} [t : TopologicalSpace K] [CompactSpace K] [T2Space K]
      [m : MeasurableSpace K] [BorelSpace K]
      {μ ν : Measure K} [μ.Regular] [ν.Regular],
      @Measure.Regular K m (r.readout () K t) (μ + ν)

theorem source_bridge : originalScope.{u} ↔ arena.{u}.Law actual.{u} := by
  rfl

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp
    (@_root_.D5.S3.Topology.Measures.RegularSignedLift.regular_add.{u})

-- In Mathlib's order, top is indiscrete and bottom is discrete.
def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ _ => ⊤)
    (fun a => Empty.elim a)

-- A general mathematical counterexample, with no topology assumption on K.
private theorem dirac_not_regular_indiscrete {K : Type u}
    [m : MeasurableSpace K] [MeasurableSingletonClass K]
    (a b : K) (hab : a ≠ b) :
    ¬ @Measure.Regular K m ⊤ (Measure.dirac a) := by
  intro h
  letI : TopologicalSpace K := ⊤
  letI : (Measure.dirac a).Regular := h
  have hzero : (Measure.dirac a) ({b} : Set K) < (1 : ENNReal) := by
    simp [hab, Ne.symm hab]
  obtain ⟨U, hAU, hUopen, hsmall⟩ :=
    ({b} : Set K).exists_isOpen_lt_of_lt (μ := Measure.dirac a) 1 hzero
  have hbU : b ∈ U := hAU (by simp)
  rcases (IndiscreteTopology.isOpen_iff U).mp hUopen with hEmpty | hUniv
  · simpa [hEmpty] using hbU
  · simpa [hUniv] using hsmall

private abbrev Witness := ULift.{u} Bool
private def leftPoint : Witness.{u} := ULift.up false
private def rightPoint : Witness.{u} := ULift.up true

-- These local instances are used only in the nontrivial witness fiber.
-- The signature and Law retain every original carrier, including empty ones.
private theorem witness_dirac_regular :
    @Measure.Regular Witness.{u} (@borel Witness.{u} ⊥)
      ⊥ (@Measure.dirac Witness.{u} (@borel Witness.{u} ⊥)
        leftPoint.{u}) := by
  letI : TopologicalSpace Witness.{u} := ⊥
  letI : DiscreteTopology Witness.{u} := discreteTopology_bot _
  letI : MeasurableSpace Witness.{u} := borel Witness.{u}
  letI : BorelSpace Witness.{u} := ⟨rfl⟩
  infer_instance

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI : TopologicalSpace Witness.{u} := ⊥
  letI : DiscreteTopology Witness.{u} := discreteTopology_bot _
  letI : MeasurableSpace Witness.{u} := borel Witness.{u}
  letI : BorelSpace Witness.{u} := ⟨rfl⟩
  letI : (Measure.dirac leftPoint.{u}).Regular := witness_dirac_regular.{u}
  have hz := @h Witness.{u} inferInstance inferInstance inferInstance
    inferInstance inferInstance (Measure.dirac leftPoint.{u}) 0
    inferInstance inferInstance
  have hr : @Measure.Regular Witness.{u} inferInstance ⊤
      (Measure.dirac leftPoint.{u}) := by
    simpa only [arena, rejected, DependentFamily.realize, add_zero] using hz
  exact dirac_not_regular_indiscrete leftPoint.{u} rightPoint.{u}
    (by simp [leftPoint, rightPoint]) hr

private theorem discrete_ne_indiscrete :
    (⊥ : TopologicalSpace Witness.{u}) ≠ ⊤ := by
  intro h
  letI : TopologicalSpace Witness.{u} := ⊤
  have ho : IsOpen ({leftPoint.{u}} : Set Witness.{u}) := by
    change IsOpen[(⊤ : TopologicalSpace Witness.{u})] _
    rw [← h]
    trivial
  rcases (IndiscreteTopology.isOpen_iff _).mp ho with hEmpty | hUniv
  · have ha : leftPoint.{u} ∈ ({leftPoint.{u}} : Set Witness.{u}) := by simp
    simpa [hEmpty] using ha
  · have hb : rightPoint.{u} ∈ ({leftPoint.{u}} : Set Witness.{u}) := by
      rw [hUniv]
      trivial
    simpa [leftPoint, rightPoint] using hb

theorem actual_dependence :
    DependentFamily.ObservationalDependence signature.{u} actual.{u} := by
  intro i
  exact ⟨Witness.{u}, ⊥, ⊤, discrete_ne_indiscrete.{u}⟩

noncomputable def familyRegistration :
    DependentFamily.Registration arena.{u} originalScope.{u} where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨actual_positive.{u}, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := actual_dependence.{u}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Topology.Measures.RegularSignedLift.regular_add)
      (DependentFamily.Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Topology.Measures.RegularSignedLift.regular_add.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.RegularSignedLift.TopologyOccurrenceCandidate.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u} (fun _ _ t => t)
    (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.RegularSignedLift
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Measures.RegularSignedLift.TopologyOccurrenceCandidate
