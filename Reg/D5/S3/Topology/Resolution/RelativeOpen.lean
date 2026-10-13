import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Resolution.RelativeOpen

/-!
# Full relative-resolution source family

The source parameters retain three independent universes, all topology
instances, the original maps and every hypothesis. States retain an actual
carrier, its topology and its map to the original T. The readout tests the
whole resolution certificate, including the conditional metrizability of
that same carrier. Kernel family evidence and a typed four-slot declaration
remain distinct from validated raw source-selection and binding evidence.
-/

namespace Reg.D5.S3.Topology.Resolution.RelativeOpen

open _root_.Topology TopologicalSpace
open _root_.D5.S3.Topology.Resolution.RelativeOpen
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe uB uT uK

structure SourceInputs where
  B : Type uB
  T : Type uT
  K : Type uK
  topB : TopologicalSpace B
  compactB : @CompactSpace B topB
  hausdorffB : @T2Space B topB
  disconnectedB : @TotallyDisconnectedSpace B topB
  topT : TopologicalSpace T
  compactT : @CompactSpace T topT
  hausdorffT : @T2Space T topT
  metricK : MetricSpace K
  compactK : letI := metricK; CompactSpace K
  p : T → B
  u : T → K
  hp : @Continuous T B topT topB p
  hpopen : @IsOpenMap T B topT topB p
  hpon : Function.Surjective p
  hu : letI := topT; letI := metricK; Continuous u
  he : letI := topT; letI := topB; letI := metricK
       IsEmbedding (fun t => (p t, u t))

def SourceState (P : SourceInputs.{uB, uT, uK}) :=
  Σ Z : Type uB, TopologicalSpace Z × (Z → P.T)

def certificate (P : SourceInputs.{uB, uT, uK}) (w : SourceState P) : Prop :=
  letI := P.topB
  letI := P.topT
  letI := w.2.1
  CompactSpace w.1 ∧ T2Space w.1 ∧ TotallyDisconnectedSpace w.1 ∧
    Continuous w.2.2 ∧ Function.Surjective w.2.2 ∧
    IsOpenMap (P.p ∘ w.2.2) ∧ Function.Surjective (P.p ∘ w.2.2) ∧
    (MetrizableSpace P.B → MetrizableSpace w.1)

def signature : DependentFamily.Signature where
  Params := SourceInputs.{uB, uT, uK}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{uB, uT, uK} :=
  DependentFamily.realize signature.{uB, uT, uK} (fun _ P w => certificate P w)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{uB, uT, uK}
  Law := fun r => ∀ P, ∃ w, r.readout () P w

abbrev resolutionScope := type_of% (@exists_relative_open_resolution.{uB, uT, uK})

theorem source_bridge : resolutionScope.{uB, uT, uK} ↔
    arena.{uB, uT, uK}.Law actual.{uB, uT, uK} := by
  constructor
  · intro h P
    let := P.topB
    let := P.compactB
    let := P.hausdorffB
    let := P.disconnectedB
    let := P.topT
    let := P.compactT
    let := P.hausdorffT
    let := P.metricK
    let := P.compactK
    obtain ⟨Z, tz, hc, hh, hd, r, hr, hs, ho, hq, hm⟩ :=
      h P.p P.u P.hp P.hpopen P.hpon P.hu P.he
    exact ⟨⟨Z, tz, r⟩, hc, hh, hd, hr, hs, ho, hq, hm⟩
  · intro h B T K topB compactB hausdorffB disconnectedB topT compactT hausdorffT
      metricK compactK p u hp hpopen hpon hu he
    let P : SourceInputs := ⟨B, T, K, topB, compactB, hausdorffB, disconnectedB,
      topT, compactT, hausdorffT, metricK, compactK, p, u, hp, hpopen, hpon, hu, he⟩
    obtain ⟨⟨Z, tz, r⟩, hw⟩ := h P
    exact ⟨Z, tz, hw.1, hw.2.1, hw.2.2.1, r, hw.2.2.2⟩

theorem resolution_actual : resolutionScope.{uB, uT, uK} :=
  @exists_relative_open_resolution.{uB, uT, uK}

theorem actual_positive : arena.{uB, uT, uK}.Law actual.{uB, uT, uK} :=
  source_bridge.mp resolution_actual

def unitInputs : SourceInputs.{uB, uT, uK} where
  B := PUnit.{uB+1}
  T := PUnit.{uT+1}
  K := PUnit.{uK+1}
  topB := inferInstance
  compactB := inferInstance
  hausdorffB := inferInstance
  disconnectedB := inferInstance
  topT := inferInstance
  compactT := inferInstance
  hausdorffT := inferInstance
  metricK := inferInstance
  compactK := inferInstance
  p := fun _ => PUnit.unit
  u := fun _ => PUnit.unit
  hp := continuous_const
  hpopen := fun _ _ => isOpen_discrete _
  hpon := fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩
  hu := continuous_const
  he := (continuous_const.prodMk continuous_const).isClosedEmbedding
    (fun x y _ => Subsingleton.elim x y) |>.isEmbedding

def rejected : DependentFamily.Realization signature.{uB, uT, uK} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{uB, uT, uK}.Law rejected := by
  intro h
  obtain ⟨w, hw⟩ := h unitInputs
  exact hw

def emptyState : SourceState unitInputs.{uB, uT, uK} :=
  ⟨ULift.{uB} Empty, inferInstance, fun z => nomatch z.down⟩

theorem empty_invalid : ¬ certificate unitInputs.{uB, uT, uK} emptyState := by
  intro h
  obtain ⟨z, _⟩ := h.2.2.2.2.1 PUnit.unit
  exact z.down.elim

def familyRegistration : DependentFamily.Registration
    arena.{uB, uT, uK} resolutionScope.{uB, uT, uK} where
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
    obtain ⟨w, hw⟩ := actual_positive unitInputs.{uB, uT, uK}
    refine ⟨unitInputs, w, emptyState, ?_⟩
    intro h
    have hcert : certificate unitInputs w := hw
    change certificate unitInputs w = certificate unitInputs emptyState at h
    rw [h] at hcert
    exact empty_invalid hcert

/- The dependent template is enrolled by Reg.Support.DependentFamily.
The raw occurrence selection is unspecified: this declaration therefore
does not assert a validated source reconstruction or binding. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_relative_open_resolution.{uB, uT, uK})
      (DependentFamily.Realization signature.{uB, uT, uK}) Unit Unit where
  unitName := `D5.S3.Topology.Resolution.RelativeOpen.exists_relative_open_resolution.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.RelativeOpen.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uB, uT, uK}⟩
  objectArena := .source ⟨arena.{uB, uT, uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{uB, uT, uK}
    (fun _ P w => certificate P w) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Resolution.RelativeOpen
