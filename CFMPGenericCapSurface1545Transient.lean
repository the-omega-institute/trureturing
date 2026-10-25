import CFMPGenericCapAtlas1532Transient
import CFMPGenericCompactHausdorff1418Transient
import CFMPLiteralSixPairing1333Transient
import Mathlib.Geometry.Manifold.ChartedSpace

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd LocalNoEdgeReversal)
open D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate
open D5.S3.Geometry.Gluing.RawFaceCompactHausdorff1418Candidate
open D5.S3.Geometry.Gluing.LiteralSixPairingCandidate (literalPairing localNoEdgeReversal)
open Topology Set

theorem partial_chart {X : Type*} [TopologicalSpace X] (x : X) (hx : PlaneChartAt X x) :
    ∃ e : OpenPartialHomeomorph X (ℝ × ℝ), x ∈ e.source := by
  obtain ⟨U,hU,hxU,V,hV,⟨e⟩⟩ := hx
  let VO : TopologicalSpace.Opens (ℝ × ℝ) := ⟨V,hV⟩
  let ev : OpenPartialHomeomorph ↥U (ℝ × ℝ) :=
    e.toOpenPartialHomeomorph.trans (VO.openPartialHomeomorphSubtypeCoe ⟨e ⟨x,hxU⟩⟩)
  let p := ev.lift_openEmbedding hU.isOpenEmbedding_subtypeVal
  refine ⟨p,?_⟩
  change x ∈ Subtype.val '' ev.source
  refine ⟨⟨x,hxU⟩,?_,rfl⟩
  simp [ev,OpenPartialHomeomorph.trans_source]

def chartedSpaceOfPlaneCharts {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, PlaneChartAt X x) : ChartedSpace (ℝ × ℝ) X where
  atlas := Set.univ
  chartAt x := Classical.choose (partial_chart x (h x))
  mem_chart_source x := Classical.choose_spec (partial_chart x (h x))
  chart_mem_atlas _ := Set.mem_univ _

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

def actualCapChartedSpace (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) :
    ChartedSpace (ℝ × ℝ) ↥(quotientSlice P ν) :=
  chartedSpaceOfPlaneCharts (every_actual_cap_point_chart P ν hNR)

theorem actual_cap_second_countable (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) :
    SecondCountableTopology ↥(quotientSlice P ν) := by
  letI : CompactSpace ↥(quotientSlice P ν) := original_cap_compact P ν
  letI : ChartedSpace (ℝ × ℝ) ↥(quotientSlice P ν) := actualCapChartedSpace P ν hNR
  exact ChartedSpace.secondCountable_of_sigmaCompact (ℝ × ℝ) ↥(quotientSlice P ν)

theorem actual_cap_surface_structure (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) :
    Nonempty (ChartedSpace (ℝ × ℝ) ↥(quotientSlice P ν)) ∧
      T2Space ↥(quotientSlice P ν) ∧ SecondCountableTopology ↥(quotientSlice P ν) ∧
      CompactSpace ↥(quotientSlice P ν) :=
  ⟨⟨actualCapChartedSpace P ν hNR⟩,original_cap_t2 P ν,
    actual_cap_second_countable P ν hNR,original_cap_compact P ν⟩

section Literal
variable [TopologicalSpace (Fin 6)] [DiscreteTopology (Fin 6)]

theorem literal_cap_surface_structure (ν : Vertex literalPairing) :
    Nonempty (ChartedSpace (ℝ × ℝ) ↥(quotientSlice literalPairing ν)) ∧
      T2Space ↥(quotientSlice literalPairing ν) ∧
      SecondCountableTopology ↥(quotientSlice literalPairing ν) ∧
      CompactSpace ↥(quotientSlice literalPairing ν) :=
  actual_cap_surface_structure literalPairing ν localNoEdgeReversal
end Literal

end D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.partial_chart,
      ``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.chartedSpaceOfPlaneCharts,
      ``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.actualCapChartedSpace,
      ``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.actual_cap_second_countable,
      ``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.actual_cap_surface_structure,
      ``D5.S3.Geometry.Gluing.RawFaceCapSurface1545Candidate.literal_cap_surface_structure] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1545 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1545 disallowed {ax}"
    Lean.logInfo m!"CFMP1545 CHECKED {name} axioms={axioms}"
