/- GID: D5/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BeamColimits/FiniteRelabelBeamTransport
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual finite graph relabels transport edge fibers, beam endpoints and row colimits. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.TypedPositiveSplitWord
import D5.S3.ConceptDynamics.Coding.BeamColimits.CountedMatrixBeamColimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.FiniteRelabelBeamTransport
open EssentialWordRealization ZeroWindowRelabeling
open StandardBeamGeometry StandardBeamEndpointRows StandardBeamCoordinates
open StandardBeamColimitCuts StandardTaggedBeams StandardBeamIdentification
open InertGroupBlockConjugacy (stationaryTransition)
open scoped BigOperators Matrix

universe u v w d
variable {V : Type u} {E : Type v} {W : Type w} {D : Type d}
variable {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

/-- Essentiality uses both endpoint equations of the actual edge bijection. -/
def essential (r : Relabel G H) (hG : Essential G) : Essential H where
  incoming v := by
    obtain ⟨e, he⟩ := hG.incoming (r.vertex.symm v)
    exact ⟨r.edge e, (r.target e).trans (by rw [he, r.vertex.apply_symm_apply])⟩
  outgoing v := by
    obtain ⟨e, he⟩ := hG.outgoing (r.vertex.symm v)
    exact ⟨r.edge e, (r.source e).trans (by rw [he, r.vertex.apply_symm_apply])⟩

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]

/-- Reindex a row by the vertex bijection, keeping all integer coefficients. -/
def reindex (r : Relabel G H) : (V → ℤ) →ₗ[ℤ] (W → ℤ) where
  toFun z v := z (r.vertex.symm v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reindex_single (r : Relabel G H) (v : V) (c : ℤ) :
    reindex r (Pi.single v c) = Pi.single (r.vertex v) c := by
  classical
  funext w
  by_cases h : r.vertex.symm w = v
  · have hw : w = r.vertex v := by rw [← h, r.vertex.apply_symm_apply]
    subst w
    simp [reindex]
  · have hw : w ≠ r.vertex v := by
      intro hw
      apply h
      rw [hw, r.vertex.symm_apply_apply]
    simp [reindex, Pi.single_apply, h, hw, Ne.symm hw]

/-- Parallel edges, including repeated targets, remain individually numbered. -/
def outgoingEquiv (r : Relabel G H) (v : V) : Out G v ≃ Out H (r.vertex v) where
  toFun e := ⟨r.edge e.val, (r.source e.val).trans (congrArg r.vertex e.property)⟩
  invFun e := ⟨r.edge.symm e.val, by
    apply r.vertex.injective
    exact (r.source (r.edge.symm e.val)).symm.trans (by
      rw [r.edge.apply_symm_apply]
      exact e.property)⟩
  left_inv e := Subtype.ext (r.edge.symm_apply_apply e.val)
  right_inv e := Subtype.ext (r.edge.apply_symm_apply e.val)

theorem reindex_adjacency (r : Relabel G H) (v : V) :
    reindex r (adjacency G v) = adjacency H (r.vertex v) := by
  classical
  change reindex r (∑ e : Out G v, Pi.single (G.target e.val) 1) =
    ∑ e : Out H (r.vertex v), Pi.single (H.target e.val) 1
  rw [map_sum]
  apply Fintype.sum_equiv (outgoingEquiv r v)
  intro e
  rw [reindex_single]
  exact congrArg (fun t : W => (Pi.single t (1 : ℤ) : W → ℤ)) (r.target e.val).symm

/-- The stationary transition square is derived from the edge-fibre bijection. -/
theorem reindex_step (r : Relabel G H) (z : V → ℤ) :
    reindex r (rowTransition G z) = rowTransition H (reindex r z) := by
  classical
  funext w
  change (∑ v : V, z v * adjacency G v (r.vertex.symm w)) =
    ∑ v : W, z (r.vertex.symm v) * adjacency H v w
  apply Fintype.sum_equiv r.vertex
  intro v
  rw [r.vertex.symm_apply_apply]
  exact congrArg (fun c : ℤ => z v * c)
    (congrFun (reindex_adjacency r v) w)

theorem reindex_power (r : Relabel G H) (k : ℕ) (z : V → ℤ) :
    reindex r (((rowTransition G) ^ k) z) =
      ((rowTransition H) ^ k) (reindex r z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, reindex_step, ih]
    rw [pow_succ', Module.End.mul_apply]

def rowMap (r : Relabel G H) : RowLimit G →ₗ[ℤ] RowLimit H :=
  Module.DirectLimit.map (fun _ : ℕ => reindex r) (by
    intro i j hij
    apply LinearMap.ext
    intro z
    exact reindex_power r (j-i) z)

@[simp] theorem rowMap_stage (r : Relabel G H) (N : ℕ) (z : V → ℤ) :
    rowMap r (stage (rowTransition G) N z) =
      stage (rowTransition H) N (reindex r z) := by
  simp only [rowMap, stage, Module.DirectLimit.map_apply_of]

theorem rowMap_intStage (r : Relabel G H) (N : ℤ) (z : V → ℤ) :
    rowMap r (intStage (rowTransition G) N z) =
      intStage (rowTransition H) N (reindex r z) := by
  change rowMap r (stage (rowTransition G) N.toNat
    (((rowTransition G) ^ (-N).toNat) z)) = _
  rw [rowMap_stage, reindex_power]
  rfl

theorem rowMap_inverse (r : Relabel G H) (x : RowLimit G) :
    rowMap r.symm (rowMap r x) = x := by
  obtain ⟨N, z, hz⟩ := Module.DirectLimit.exists_of x
  change stage (rowTransition G) N z = x at hz
  rw [← hz, rowMap_stage, rowMap_stage]
  congr 1
  funext v
  exact congrArg z (r.vertex.symm_apply_apply v)

def rowEquiv (r : Relabel G H) : RowLimit G ≃ₗ[ℤ] RowLimit H where
  toFun := rowMap r
  invFun := rowMap r.symm
  map_add' := (rowMap r).map_add
  map_smul' := (rowMap r).map_smul
  left_inv := rowMap_inverse r
  right_inv := rowMap_inverse r.symm

section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]

/-- Relabeling changes no cut, including negative cuts. -/
theorem image_ray (r : Relabel G H) (alpha : History G) (N : ℤ) :
    r.homeomorph '' ray G alpha N = ray H (r.homeomorph alpha) N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    exact congrArg r.edge (hx k hk)
  · intro hy
    refine ⟨r.homeomorph.symm y, ?_, r.homeomorph.apply_symm_apply y⟩
    intro k hk
    apply r.edge.injective
    change r.edge (r.edge.symm (y.val k)) = r.edge (alpha.val k)
    rw [r.edge.apply_symm_apply]
    exact hy k hk

theorem image_endpoint (r : Relabel G H) (alpha : History G) (N : ℤ) :
    endpoint H (r.homeomorph alpha) N = r.vertex (endpoint G alpha N) :=
  r.target (alpha.val N)

/-- The intrinsic partition is transported as actual subsets, not endpoints. -/
def partsEquiv (r : Relabel G H) (U : Set (History G)) (N : ℤ) :
    Parts G U N ≃ Parts H (r.homeomorph '' U) N where
  toFun P := ⟨⟨r.homeomorph '' P.val.val,
    r.homeomorph (RayAt.representative G P.val), by
      rw [RayAt.set_eq G P.val, image_ray]⟩,
    Set.image_mono P.property⟩
  invFun Q := ⟨⟨r.homeomorph.symm '' Q.val.val,
    r.homeomorph.symm (RayAt.representative H Q.val), by
      rw [RayAt.set_eq H Q.val]
      exact image_ray r.symm _ N⟩, by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, he⟩ := Q.property hy
    simpa only [← he, r.homeomorph.symm_apply_apply] using hz⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change r.homeomorph.symm '' (r.homeomorph '' P.val.val) = P.val.val
    simp only [Set.image_image, Function.comp_def, Homeomorph.symm_apply_apply,
      Set.image_id']
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    change r.homeomorph '' (r.homeomorph.symm '' Q.val.val) = Q.val.val
    simp only [Set.image_image, Function.comp_def, Homeomorph.apply_symm_apply,
      Set.image_id']

theorem parts_endpoint (r : Relabel G H) (U : Set (History G)) (N : ℤ)
    (P : Parts G U N) :
    RayAt.endpoint H ((partsEquiv r U N P).val) = r.vertex (RayAt.endpoint G P.val) := by
  let x := RayAt.representative G P.val
  have hx : x ∈ P.val.val := by rw [RayAt.set_eq G P.val]; exact self_mem_ray G x N
  exact (RayAt.endpoint_of_mem H (partsEquiv r U N P).val (r.homeomorph x) ⟨x, hx, rfl⟩).trans
    (image_endpoint r x N)

theorem image_atCut (r : Relabel G H) {U : Set (History G)} {N : ℤ}
    (hU : AtCut G U N) : AtCut H (r.homeomorph '' U) N := by
  letI : Finite (Parts G U N) := hU.1
  haveI : Finite (Parts H (r.homeomorph '' U) N) :=
    Finite.of_equiv _ (partsEquiv r U N)
  refine ⟨inferInstance, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  rw [← image_ray]
  exact Set.image_mono (hU.2 x hx)

theorem endpointRow_image (r : Relabel G H) {U : Set (History G)} {N : ℤ}
    (hU : AtCut G U N) :
    letI : Finite (Parts G U N) := hU.1
    letI : Finite (Parts H (r.homeomorph '' U) N) := (image_atCut r hU).1
    endpointRow H (r.homeomorph '' U) N = reindex r (endpointRow G U N) := by
  letI : Finite (Parts G U N) := hU.1
  letI : Finite (Parts H (r.homeomorph '' U) N) := (image_atCut r hU).1
  letI : Fintype (Parts G U N) := Fintype.ofFinite _
  letI : Fintype (Parts H (r.homeomorph '' U) N) := Fintype.ofFinite _
  unfold endpointRow
  rw [map_sum]
  symm
  apply Fintype.sum_equiv (partsEquiv r U N)
  intro P
  rw [reindex_single, parts_endpoint]

def imageBeam (r : Relabel G H) (U : Beam G) : Beam H :=
  ⟨r.homeomorph '' U.val, by
    obtain ⟨N, hN⟩ := U.property
    exact ⟨N, image_atCut r hN⟩⟩

theorem beam_coordinate (r : Relabel G H) (hG : Essential G) (hH : Essential H)
    (U : Beam G) :
    beamCoordinate H (imageBeam r U) = rowMap r (beamCoordinate G U) := by
  obtain ⟨N, hN⟩ := U.property
  letI : Finite (Parts G U.val N) := hN.1
  letI : Finite (Parts H (r.homeomorph '' U.val) N) := (image_atCut r hN).1
  rw [beamCoordinate_at H hH _ N (image_atCut r hN), beamCoordinate_at G hG U N hN]
  unfold coordinateAt
  change intStage (rowTransition H) N (endpointRow H (r.homeomorph '' U.val) N) =
    rowMap r (intStage (rowTransition G) N (endpointRow G U.val N))
  rw [endpointRow_image r hN, rowMap_intStage]

def imageObject (r : Relabel G H) (A : Object G) : Object H :=
  ⟨ULift.{d} (Fin (Fintype.card A.Tag)), inferInstance,
    fun i => imageBeam r (A.beam ((Fintype.equivFin A.Tag).symm i.down))⟩

theorem object_coordinate (r : Relabel G H) (hG : Essential G) (hH : Essential H)
    (A : Object G) :
    objectValue H (imageObject r A) = rowMap r (objectValue G A) := by
  unfold objectValue
  rw [map_sum]
  let e : (imageObject r A).Tag ≃ A.Tag :=
    Equiv.ulift.trans (Fintype.equivFin A.Tag).symm
  apply Fintype.sum_equiv e
  intro i
  exact beam_coordinate r hG hH (A.beam _)

/-- Conjugate only after the actual subset/coordinate diagram is proved. -/
def beamEquiv (r : Relabel G H) (hG : Essential G) (hH : Essential H) :
    BeamGroup G hG ≃ₗ[ℤ] BeamGroup H hH :=
  (beamRowEquiv G hG).trans ((rowEquiv r).trans (beamRowEquiv H hH).symm)

theorem beamEquiv_coordinate (r : Relabel G H) (hG : Essential G) (hH : Essential H)
    (x : BeamGroup G hG) :
    F H hH (beamEquiv r hG hH x) = rowMap r (F G hG x) := by
  exact (beamRowEquiv H hH).apply_symm_apply _

theorem beamEquiv_object (r : Relabel G H) (hG : Essential G) (hH : Essential H)
    (A : Object G) :
    beamEquiv r hG hH (objectGroup G hG A) = objectGroup H hH (imageObject r A) := by
  apply F_injective H hH
  rw [beamEquiv_coordinate, F_objectGroup, F_objectGroup, object_coordinate r hG hH]

end Topology
end Finite
end D5.S3.ConceptDynamics.Coding.FiniteRelabelBeamTransport
