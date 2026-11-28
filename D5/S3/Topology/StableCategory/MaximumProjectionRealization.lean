/- GID: D5/S3/Topology/StableCategory/MaximumProjectionRealization
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/MaximumProjectionRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximum-selector realizations are homotopic to barycentric subdivision. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrderComplexNullhomotopy

/-!
# Realization of iterated maximum projections

A supported selector and the iterated barycentric homeomorphism both carry
each closed subdivided simplex into its original carrier. Interpolation in
the original coordinates gives one continuous homotopy on the realization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.MaximumProjectionRealization

open D5.S3.Geometry.FiniteConeCollapse (faceSimplex realization realization_mem_iff)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (faceImage sd vertexOfFace)
open GeometricGraphTermination (realizedVertexMap)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem)
open OrderComplexNullhomotopy
  (orderComplex orderVertex maximumSelector maximumSelector_simplicial maximumSelector_supported)
open OrderComplexNullhomotopy (maximumProjection orderHomVertices realizedOrderHom)
open StableCategory.LebesgueStarAssignment
  (DepthVertices depthComplex iteratedRealization iteratedRealization_barycentric_formula)
open StableCategory.OrdinaryContiguityLift (Simplicial)
open StableCategory.TerminalCarrierIteration (originalSupport_mono)
open scoped BigOperators ContinuousMap unitInterval

open private convex_faceSimplex faceSimplex_mono from D5.S3.Geometry.FiniteConeCollapse
open private extendVertexMap linearMap_mem_faceImage mem_faceImage_iff from
  D5.S3.Topology.GeometricGraphTermination
open private vertexCoordinates_eq_zero_of_not_mem_originalSupport from
  D5.S3.Topology.SimplicialNullhomotopyApproximation
open private depthFintype depthDecEq from D5.S3.Topology.StableCategory.LebesgueStarAssignment

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X]
variable {A : PreAbstractSimplicialComplex X}

private theorem iteratedRealization_mem_carrier (r : ℕ) {s : Finset (DepthVertices A r)} :
    letI : Fintype (DepthVertices A r) := depthFintype A r
    letI : DecidableEq (DepthVertices A r) := depthDecEq A r
    ∀ p : Space (depthComplex A r), p.val ∈ faceSimplex s →
      (iteratedRealization A r p).val ∈ faceSimplex (originalSupport A r s) := by
  letI : Fintype (DepthVertices A r) := depthFintype A r
  letI : DecidableEq (DepthVertices A r) := depthDecEq A r
  change ∀ p : Space (depthComplex A r), p.val ∈ faceSimplex s →
    (iteratedRealization A r p).val ∈ faceSimplex (originalSupport A r s)
  intro p hp
  obtain ⟨_, _, hcoords⟩ := (realization_mem_iff A _).mp (iteratedRealization A r p).property
  refine ⟨hcoords.1, hcoords.2.1, ?_⟩
  intro y hy
  rw [iteratedRealization_barycentric_formula A r p]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ s
  · rw [vertexCoordinates_eq_zero_of_not_mem_originalSupport (A := A) r hv hy, mul_zero]
  · rw [hp.2.2 v hv, zero_mul]

/-- Every supported simplicial selector realizes a map homotopic to the
iterated barycentric homeomorphism. -/
def supportedSelectorHomotopy (r : ℕ) (fallback : Vertex A)
    (select : Vertex (depthComplex A r) → Vertex A) (hselect : Simplicial select)
    (hsupport : ∀ x, (select x).val ∈ originalSupport A r {x.val}) :
    letI : Fintype (DepthVertices A r) := depthFintype A r
    letI : DecidableEq (DepthVertices A r) := depthDecEq A r
    (realizedVertexMap fallback select hselect).Homotopy
      (toContinuousMap (iteratedRealization A r)) := by
  letI : Fintype (DepthVertices A r) := depthFintype A r
  letI : DecidableEq (DepthVertices A r) := depthDecEq A r
  let F := realizedVertexMap fallback select hselect
  let e := iteratedRealization A r
  have hF {s : Finset (DepthVertices A r)} (hs : s ∈ depthComplex A r)
      (p : Space (depthComplex A r)) (hp : p.val ∈ faceSimplex s) :
      (F p).val ∈ faceSimplex (originalSupport A r s) := by
    have hsub : faceImage select hs ⊆ originalSupport A r s := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff select hs).mp hy
      exact originalSupport_mono A r (Finset.singleton_subset_iff.mpr hx) (hsupport x)
    exact faceSimplex_mono hsub (linearMap_mem_faceImage fallback select hs hp)
  let segment (z : I × Space (depthComplex A r)) : X → ℝ :=
    (1 - (z.1 : ℝ)) • (F z.2).val + (z.1 : ℝ) • (e z.2).val
  have hsegment (z : I × Space (depthComplex A r)) : segment z ∈ realization A := by
    obtain ⟨s, hs, hp⟩ := (realization_mem_iff (depthComplex A r) _).mp z.2.property
    refine (realization_mem_iff A _).mpr ⟨_, originalSupport_mem r hs, ?_⟩
    exact convex_faceSimplex (originalSupport A r s) (hF hs z.2 hp)
      (iteratedRealization_mem_carrier r z.2 hp) (sub_nonneg.mpr z.1.property.2)
      z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))
  have ht : Continuous (fun z : I × Space (depthComplex A r) => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hleft : Continuous (fun z : I × Space (depthComplex A r) => (F z.2).val) :=
    continuous_subtype_val.comp (F.continuous.comp continuous_snd)
  have hright : Continuous (fun z : I × Space (depthComplex A r) => (e z.2).val) :=
    continuous_subtype_val.comp (e.continuous.comp continuous_snd)
  exact
    { toFun := fun z => ⟨segment z, hsegment z⟩
      continuous_toFun := (((continuous_const.sub ht).smul hleft).add (ht.smul hright)).subtype_mk _
      map_zero_left := by
        intro p
        apply Subtype.ext
        change segment (0, p) = (F p).val
        simp [segment]
      map_one_left := by
        intro p
        apply Subtype.ext
        change segment (1, p) = (e p).val
        simp [segment] }

/-- At every depth the affine maximum selector is homotopic to the
barycentric subdivision homeomorphism. -/
def maximumSelectorHomotopy [PartialOrder X] (fallback : X) (r : ℕ) :
    letI : Fintype (DepthVertices (orderComplex X) r) := depthFintype (orderComplex X) r
    letI : DecidableEq (DepthVertices (orderComplex X) r) := depthDecEq (orderComplex X) r
    (realizedVertexMap (orderVertex fallback) (maximumSelector r)
      (maximumSelector_simplicial r)).Homotopy
      (toContinuousMap (iteratedRealization (orderComplex X) r)) :=
  supportedSelectorHomotopy r (orderVertex fallback) (maximumSelector r)
    (maximumSelector_simplicial r) (maximumSelector_supported r)

private theorem orderComplex_face_eq_sd {V : Type} (K : PreAbstractSimplicialComplex V) :
    orderComplex (Face K) = sd K := by
  apply SetLike.ext
  intro s
  constructor
  · intro hs
    refine ⟨hs.1, ?_, fun a _ => a.property⟩
    intro a ha b hb hab
    exact (hs.2 ha hb hab).imp (fun h => lt_of_le_of_ne h hab) (fun h => lt_of_le_of_ne h hab.symm)
  · intro hs
    exact ⟨hs.1, hs.2.1.mono_rel (fun _ _ h => h.le)⟩

/-- The order complex of the face poset and the subdivision have the same
realization in the coordinates indexed by faces. -/
def faceOrderComplexHomeomorph {V : Type} (K : PreAbstractSimplicialComplex V)
    [DecidableEq (Face K)] : Space (orderComplex (Face K)) ≃ₜ Space (sd K) :=
  Homeomorph.setCongr (congrArg realization (orderComplex_face_eq_sd K))

/-- The realized `(r + 1)`-fold maximum from the order complex of the
depth-`r` face poset is homotopic to its barycentric homeomorphism. -/
def maximumProjectionHomotopy [PartialOrder X] (fallback : X) (r : ℕ) :
    letI : Fintype (Face (depthComplex (orderComplex X) r)) :=
      depthFintype (orderComplex X) (r + 1)
    letI : DecidableEq (Face (depthComplex (orderComplex X) r)) :=
      depthDecEq (orderComplex X) (r + 1)
    (realizedOrderHom fallback (maximumProjection X r)).Homotopy
      (toContinuousMap ((faceOrderComplexHomeomorph (depthComplex (orderComplex X) r)).trans
        (iteratedRealization (orderComplex X) (r + 1)))) := by
  let K := depthComplex (orderComplex X) r
  letI : Fintype (Face K) := depthFintype (orderComplex X) (r + 1)
  letI : DecidableEq (Face K) := depthDecEq (orderComplex X) (r + 1)
  letI : Fintype (DepthVertices (orderComplex X) (r + 1)) := depthFintype (orderComplex X) (r + 1)
  let e := faceOrderComplexHomeomorph K
  let H := (maximumSelectorHomotopy fallback (r + 1)).compContinuousMap (toContinuousMap e)
  refine H.cast ?_ rfl
  have hlabels :
      extendVertexMap (orderVertex fallback) (maximumSelector (r + 1)) =
        extendVertexMap (orderVertex fallback) (orderHomVertices (maximumProjection X r)) := by
    classical
    funext a
    change Face K at a
    let v := vertexOfFace K a
    let w := orderVertex a
    unfold extendVertexMap
    have hv : ({a} : Finset (Face K)) ∈ depthComplex (orderComplex X) (r + 1) := v.property
    have hw : ({a} : Finset (Face K)) ∈ orderComplex (Face (depthComplex (orderComplex X) r)) :=
      w.property
    simp only [dite_eq_left hv, dite_eq_left hw, maximumSelector, orderHomVertices,
      orderVertex, OrderComplexNullhomotopy.vertexProjection]
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  change FunOnFinite.linearMap ℝ ℝ
      (extendVertexMap (orderVertex fallback) (maximumSelector (r + 1))) (e p).val =
    FunOnFinite.linearMap ℝ ℝ
      (extendVertexMap (orderVertex fallback) (orderHomVertices (maximumProjection X r))) p.val
  rw [hlabels, show (e p).val = p.val from rfl]
  rfl

end

end D5.S3.Topology.MaximumProjectionRealization
