import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.RegularSignedLift

/-!
# Original order-unit positivity scope

The source scope retains every compact topological carrier, including the
empty carrier, and both arbitrary regular measures. The dependent-family arena
below preserves the complete source telescope, uses the actual sum readout,
and proves the source bridge, rejection of an infinite-mass intervention, whole-family variation,
fixed-role sensitivity and observational dependence. The source selector
remains subject to the current dictionary-dependent-coordinate contract; the
producer report is the authority for whether this registration can be closed
as a source binding.
-/

namespace Reg.D5.S3.Topology.Measures.RegularSignedLift

universe u

set_option autoImplicit false

open Set Filter MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.Measures.RegularSignedLift

theorem order_unit_positive_actual : type_of% (@positive_of_norm_le_one.{u}) :=
  @positive_of_norm_le_one.{u}

/- Same-delivery source binding for the exposed sum-regularity supplier. The
faithful arena retains both measures and their actual Regular dictionaries on
every compact Hausdorff Borel carrier. The two summands may be zero and the
carrier may be empty; the dependent arena and its proofs below retain the
whole-family law, sensitivity and dependence. -/
theorem regular_add_actual : type_of% (@regular_add.{u}) :=
  @regular_add.{u}

abbrev regularScope := type_of% (@regular_add.{u})

structure SourceInputs where
  K : Type u
  topK : TopologicalSpace K
  compactK : @CompactSpace K topK
  t2K : @T2Space K topK
  measurableK : MeasurableSpace K
  borelK : @BorelSpace K topK measurableK

attribute [instance] SourceInputs.topK SourceInputs.compactK SourceInputs.t2K
  SourceInputs.measurableK SourceInputs.borelK

structure SourceState (p : SourceInputs.{u}) where
  μ : @Measure p.K p.measurableK
  ν : @Measure p.K p.measurableK
  hμ : @Measure.Regular p.K p.measurableK p.topK μ
  hν : @Measure.Regular p.K p.measurableK p.topK ν

abbrev signature : DependentFamily.Signature where
  Params := SourceInputs.{u}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => @Measure p.K p.measurableK
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def observed (p : SourceInputs.{u}) (st : SourceState p) :
    @Measure p.K p.measurableK := st.μ + st.ν

noncomputable def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ p st => observed p st)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ p st,
    letI := p.topK
    letI := p.compactK
    letI := p.t2K
    letI := p.measurableK
    letI := p.borelK
    letI := st.hμ
    letI := st.hν
    (r.readout () p st).Regular

theorem source_bridge : regularScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p st
    letI := p.topK
    letI := p.compactK
    letI := p.t2K
    letI := p.measurableK
    letI := p.borelK
    letI := st.hμ
    letI := st.hν
    exact h (μ := st.μ) (ν := st.ν)
  · intro h K topK compactK t2K measurableK borelK μ ν hμ hν
    let p : SourceInputs.{u} :=
      { K := K, topK := topK, compactK := compactK, t2K := t2K,
        measurableK := measurableK, borelK := borelK }
    let st : SourceState p :=
      { μ := μ, ν := ν, hμ := hμ, hν := hν }
    exact h p st

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@regular_add.{u})

noncomputable def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ st => (⊤ : ENNReal) • st.μ)
    (fun a => Empty.elim a)

private abbrev unitInputs : SourceInputs.{u} :=
  { K := ULift.{u} Unit, topK := inferInstance, compactK := inferInstance,
    t2K := inferInstance, measurableK := inferInstance, borelK := inferInstance }

private noncomputable abbrev unitState : SourceState unitInputs.{u} :=
  { μ := Measure.dirac (ULift.up ()), ν := 0,
    hμ := inferInstance, hν := inferInstance }

/-- The rejected readout has infinite mass on a compact singleton, so it
violates original regularity itself. No output-equality clause is added. -/
theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hz := h unitInputs.{u} unitState.{u}
  change ((⊤ : ENNReal) • Measure.dirac (ULift.up () : ULift.{u} Unit)).Regular at hz
  letI := hz
  have hfinite := (isCompact_univ : IsCompact (Set.univ : Set (ULift.{u} Unit))).measure_lt_top
    (μ := (⊤ : ENNReal) • Measure.dirac (ULift.up ()))
  simpa using hfinite

private theorem actual_dependence :
    DependentFamily.ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨unitInputs.{u},
    ({ μ := 0, ν := 0, hμ := inferInstance, hν := inferInstance }),
    unitState.{u}, ?_⟩
  intro h
  have heq' : (0 : Measure (ULift.{u} Unit)) + 0 =
      Measure.dirac (ULift.up ()) + 0 := by
    simpa [actual, DependentFamily.realize, observed, unitInputs, unitState] using h
  have hv := congrArg (fun m : Measure (ULift.{u} Unit) => m Set.univ) heq'
  norm_num at hv

noncomputable def familyRegistration : DependentFamily.Registration arena.{u} regularScope.{u} where
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
      (@regular_add) (DependentFamily.Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Topology.Measures.RegularSignedLift.regular_add.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.RegularSignedLift.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ p st => observed p st) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.RegularSignedLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/- The current producer still records any source-selector contract gap for
this target under https://github.com/the-omega-institute/trureturing/issues/24319.
The older finite-family issue 24040 is not used to cover this extension. -/

end Reg.D5.S3.Topology.Measures.RegularSignedLift

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
  let : TopologicalSpace K := ⊤
  let : (Measure.dirac a).Regular := h
  have hzero : (Measure.dirac a) ({b} : Set K) < (1 : ENNReal) := by
    simp [hab]
  obtain ⟨U, hAU, hUopen, hsmall⟩ :=
    ({b} : Set K).exists_isOpen_lt_of_lt (μ := Measure.dirac a) 1 hzero
  have hbU : b ∈ U := hAU (by simp)
  rcases (IndiscreteTopology.isOpen_iff U).mp hUopen with hEmpty | hUniv
  · simp [hEmpty] at hbU
  · simp [hUniv] at hsmall

private abbrev Witness := ULift.{u} Bool
private def leftPoint : Witness.{u} := ULift.up false
private def rightPoint : Witness.{u} := ULift.up true

-- These local instances are used only in the nontrivial witness fiber.
-- The signature and Law retain every original carrier, including empty ones.
private theorem witness_dirac_regular :
    @Measure.Regular Witness.{u} (@borel Witness.{u} ⊥)
      ⊥ (@Measure.dirac Witness.{u} (@borel Witness.{u} ⊥)
        leftPoint.{u}) := by
  let : TopologicalSpace Witness.{u} := ⊥
  let : DiscreteTopology Witness.{u} := discreteTopology_bot _
  let : MeasurableSpace Witness.{u} := borel Witness.{u}
  let : BorelSpace Witness.{u} := ⟨rfl⟩
  infer_instance

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let : TopologicalSpace Witness.{u} := ⊥
  let : DiscreteTopology Witness.{u} := discreteTopology_bot _
  let : MeasurableSpace Witness.{u} := borel Witness.{u}
  let : BorelSpace Witness.{u} := ⟨rfl⟩
  let : (Measure.dirac leftPoint.{u}).Regular := witness_dirac_regular.{u}
  have hz := @h Witness.{u} inferInstance inferInstance inferInstance
    inferInstance inferInstance (Measure.dirac leftPoint.{u}) 0
    inferInstance inferInstance
  have hr : @Measure.Regular Witness.{u} inferInstance ⊤
      (Measure.dirac leftPoint.{u}) := by
    change @Measure.Regular Witness.{u} inferInstance ⊤
      (Measure.dirac leftPoint.{u} + 0) at hz
    simpa only [add_zero] using hz
  exact dirac_not_regular_indiscrete leftPoint.{u} rightPoint.{u}
    (by simp [leftPoint, rightPoint]) hr

private theorem discrete_ne_indiscrete :
    (⊥ : TopologicalSpace Witness.{u}) ≠ ⊤ := by
  intro h
  let : TopologicalSpace Witness.{u} := ⊤
  have ho : IsOpen ({leftPoint.{u}} : Set Witness.{u}) := by
    change @IsOpen Witness.{u} (⊤ : TopologicalSpace Witness.{u}) _
    rw [← h]
    trivial
  rcases (IndiscreteTopology.isOpen_iff _).mp ho with hEmpty | hUniv
  · have ha : leftPoint.{u} ∈ ({leftPoint.{u}} : Set Witness.{u}) := by simp
    simp [hEmpty] at ha
  · have hb : rightPoint.{u} ∈ ({leftPoint.{u}} : Set Witness.{u}) := by
      rw [hUniv]
      trivial
    simp [leftPoint, rightPoint] at hb

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
  unitName := `D5.S3.Topology.Measures.RegularSignedLift.regular_add.__information_topology_occurrence_unit
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

