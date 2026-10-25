import CFMPGenericCapEdge1526Transient
import CFMPGenericCapDisk1307Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd LocalNoEdgeReversal)
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate (chooseOrientation)
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate (Neighborhood quotientNeighborhood actual_open_quotient_neighborhood)
open D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate (actualOpenDiskChart)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (OpenDisk)
open Topology Set

/-- Existence of an open chart to an open subset of the real plane. -/
def PlaneChartAt (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ Nonempty (↥U ≃ₜ ↥V)

theorem transport {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) (hx : PlaneChartAt X x) : PlaneChartAt Y (h x) := by
  obtain ⟨U,hU,hxU,V,hV,⟨e⟩⟩ := hx
  exact ⟨h '' U,h.isOpenMap U hU,⟨x,hxU,rfl⟩,V,hV,⟨(h.image U).symm.trans e⟩⟩

theorem zero_pattern (j : Fin 4) (β : Fin 4 → ℝ) (hj : β j = 0)
    (_hpos : ∀ i, 0 ≤ β i) (hs : (∑ i, β i) = 1) :
    (∀ f, f ≠ j → β f ≠ 0) ∨
      (∃ f, f ≠ j ∧ β f = 0 ∧ ∀ g, g ≠ j → β g = 0 → g = f) ∨
      (∃ k, k ≠ j ∧ 1/2 < β k) := by
  classical
  by_cases hI : ∀ f, f ≠ j → β f ≠ 0
  · exact Or.inl hI
  · right
    push Not at hI
    obtain ⟨f,hfj,hf⟩ := hI
    by_cases hE : ∀ g, g ≠ j → β g = 0 → g = f
    · exact Or.inl ⟨f,hfj,hf,hE⟩
    · right
      push Not at hE
      obtain ⟨g,hgj,hg,hgf⟩ := hE
      by_contra hnone
      push Not at hnone
      simp [Fin.forall_fin_succ] at hnone
      fin_cases j <;> fin_cases f <;> fin_cases g <;>
        simp_all [Fin.sum_univ_succ] <;> linarith

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

theorem dominant_chart (P : RawFacePairing T) (c : T × Fin 4)
    (β : Fin 4 → ℝ) (hj : β c.2 = 0) (hpos : ∀ i, 0 ≤ β i) (hs : (∑ i, β i) = 1)
    (k : Fin 4) (hk : k ≠ c.2) (hdom : 1/2 < β k)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) :
    PlaneChartAt (PointQuotient P (label P c))
      ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := label P c))))
        ⟨(c,β),hj,hpos,hs,rfl⟩) := by
  let d : OrderedEnd T := ⟨(c,k),hk.symm⟩
  let x : Point P (label P c) := ⟨(c,β),hj,hpos,hs,rfl⟩
  let U := quotientNeighborhood P (ν := label P c) d.val
  have hx : x ∈ Neighborhood P d.val := ⟨k,hdom,Relation.EqvGen.refl _⟩
  have hU : IsOpen U := (actual_open_quotient_neighborhood P d.val).2.1
  let D : Set ℂ := {z | ‖z‖ < 1}
  let h : ℂ ≃ₜ (ℝ × ℝ) := Complex.equivRealProdCLM.toHomeomorph
  have hD : IsOpen D := isOpen_lt continuous_norm continuous_const
  refine ⟨U,hU,⟨x,hx,rfl⟩,h '' D,h.isOpenMap D hD,?_⟩
  exact ⟨(actualOpenDiskChart P (chooseOrientation P) d (hNR d)).trans (h.image D)⟩

theorem every_original_point_chart (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) (x : Point P ν) :
    PlaneChartAt (PointQuotient P ν)
      ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) x) := by
  rcases x with ⟨⟨c,β⟩,hj,hpos,hs,hl⟩
  subst ν
  let x : Point P (label P c) := ⟨(c,β),hj,hpos,hs,rfl⟩
  rcases zero_pattern c.2 β hj hpos hs with hI | hE | hD
  · have hi : Interior P x := hI
    have hx : x ∈ InteriorPatch P (label P c) c := ⟨rfl,hi⟩
    refine ⟨quotientInteriorPatch P (label P c) c,
      (actual_open_interior_quotient P (label P c) c).2,⟨x,hx,rfl⟩,
      {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1},open_triangle_domain,?_⟩
    exact ⟨(originalInteriorChart P (label P c) c.1 c.2 rfl).symm⟩
  · obtain ⟨f,hf⟩ := hE
    obtain ⟨U,hU,hxU,a,b,δ,hδ,⟨e⟩⟩ := every_original_edge_chart P (label P c) x f hf
    exact ⟨U,hU,hxU,rectangle a b δ,rectangle_open a b δ,⟨e⟩⟩
  · obtain ⟨k,hk,hdom⟩ := hD
    exact dominant_chart P c β hj hpos hs k hk hdom hNR

theorem every_original_quotient_chart (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) (z : PointQuotient P ν) :
    PlaneChartAt (PointQuotient P ν) z := by
  induction z using Quotient.inductionOn with
  | h x => exact every_original_point_chart P ν hNR x

theorem every_actual_cap_point_chart (P : RawFacePairing T) (ν : Vertex P)
    (hNR : ∀ d : OrderedEnd T, LocalNoEdgeReversal P d) (z : ↥(quotientSlice P ν)) :
    PlaneChartAt ↥(quotientSlice P ν) z := by
  let h := actualSliceQuotientHomeomorph P ν
  have hx := every_original_quotient_chart P ν hNR (h.symm z)
  simpa only [Homeomorph.apply_symm_apply] using transport h (h.symm z) hx

end D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.transport,
      ``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.zero_pattern,
      ``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.dominant_chart,
      ``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.every_original_point_chart,
      ``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.every_original_quotient_chart,
      ``D5.S3.Geometry.Gluing.RawFaceCapAtlas1532Candidate.every_actual_cap_point_chart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1532 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1532 disallowed {ax}"
    Lean.logInfo m!"CFMP1532 CHECKED {name} axioms={axioms}"
