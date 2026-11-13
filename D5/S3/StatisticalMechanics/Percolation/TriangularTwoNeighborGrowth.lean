/- GID: D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact two-neighbor hexagon growth and fixed-radius lattice geometry. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22020
admission_basis: escape-witness
escape_witness: D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.exact_shape
MarkeyA400701.directions: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: MarkeyA400701.windowGraph, AxialGrowth.Two, AxialGrowth.moves_image, AxialGrowth.two_transform, AxialGrowth.first_step, AxialGrowth.second_step, CircleGrowth.directions_neg, CircleGrowth.directions_q, CircleGrowth.unit_int_directions, CircleGrowth.embed_adjacent, CircleGrowth.intersection_lattice, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.window_adj, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.grown_bounds, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state.
MarkeyA400701.coordinates: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: MarkeyA400701.windowGraph, MarkeyA400701.seed, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.coordinates_injective, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.window_adj, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.window_surjective, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.lattice_shape_count.
MarkeyA400701.windowGraph: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: MarkeyA400701.latticeCount, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.window_adj, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.lattice_shape_count.
MarkeyA400701.seed: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: MarkeyA400701.latticeCount, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.lattice_shape_count.
MarkeyA400701.latticeCount: proof_shape: bind-only; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51]; escape_witness: none; consumers: D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.MarkeyA400701.claim, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.lattice_shape_count, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.MarkeyA400701.result.
HexGrowth.moves: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.TwoOld, HexGrowth.two_old_bounded, HexGrowth.expanded_has_two, AxialGrowth.moves_image, AxialGrowth.two_transform.
HexGrowth.Hex: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.TwoOld, HexGrowth.hex_persists, HexGrowth.two_old_bounded, HexGrowth.expanded_has_two, HexGrowth.hex_update, AxialGrowth.H, AxialGrowth.two_transform, AxialGrowth.expanded_next, AxialGrowth.shape_step.
HexGrowth.TwoOld: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.two_old_bounded, HexGrowth.expanded_has_two, HexGrowth.hex_update, AxialGrowth.two_transform, AxialGrowth.shape_step.
HexGrowth.hex_persists: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.hex_update.
HexGrowth.two_old_bounded: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.hex_update.
HexGrowth.expanded_has_two: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexGrowth.hex_update.
HexGrowth.hex_update: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.shape_step.
AxialGrowth.transform: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.H, AxialGrowth.transform_add, AxialGrowth.two_transform, AxialGrowth.expanded_next, AxialGrowth.shape_step.
AxialGrowth.H: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.two_transform, AxialGrowth.expanded_next, AxialGrowth.shape_step, AxialGrowth.second_step, AxialGrowth.exact_shape, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.shape_mem, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.H_coe, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.H_card, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.grown_coe, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertex_card.
AxialGrowth.Two: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.next, AxialGrowth.two_transform, AxialGrowth.shape_step, AxialGrowth.first_step, AxialGrowth.second_step, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.grown_bounds, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state.
AxialGrowth.next: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.shape_step, AxialGrowth.second_step, AxialGrowth.exact_shape.
AxialGrowth.initial: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.first_step, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.initial_two, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
AxialGrowth.grown: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.first_step, AxialGrowth.second_step, AxialGrowth.exact_shape, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.grown_coe, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertex_card, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.first_four, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.grown_bounds, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.finite_state, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.lattice_shape_count.
AxialGrowth.linear_injective: proof_shape: bind-only; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: AxialGrowth.two_transform.
AxialGrowth.moves_image: proof_shape: bind-only; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: AxialGrowth.two_transform.
AxialGrowth.transform_add: proof_shape: bind-only; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: AxialGrowth.two_transform.
AxialGrowth.two_transform: proof_shape: bind-only; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: AxialGrowth.shape_step.
AxialGrowth.expanded_next: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.shape_step.
AxialGrowth.shape_step: proof_shape: bind-only; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: AxialGrowth.exact_shape.
AxialGrowth.first: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.first_y_bounds, AxialGrowth.first_step, AxialGrowth.second_step, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.first_four.
AxialGrowth.first_y_bounds: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.first_step, AxialGrowth.second_step.
AxialGrowth.first_step: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.second_step, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.first_four.
AxialGrowth.second_step: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: AxialGrowth.exact_shape.
AxialGrowth.exact_shape: proof_shape: content; direct frozen dependencies: D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: AxialGrowth.exact_shape; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.grown_coe, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertex_card.
HexCircleArithmetic.q_nonneg: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexCircleArithmetic.displacement_le_four.
HexCircleArithmetic.displacement_le_four: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexCircleArithmetic.integer_center_intersection.
HexCircleArithmetic.displacement_bounds: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexCircleArithmetic.integer_center_intersection.
HexCircleArithmetic.UnitNeighbor: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexCircleArithmetic.integer_center_intersection, CircleGrowth.unit_int_directions, CircleGrowth.intersection_lattice.
HexCircleArithmetic.integer_center_intersection: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.intersection_lattice.
HexEmbedding.axial: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.embed, HexEmbedding.axial_re, HexEmbedding.axial_im, HexEmbedding.axial_injective, HexEmbedding.axial_surjective, HexEmbedding.embed_injective, HexEmbedding.axial_dist_sq, HexEmbedding.frame_unit_iff, CircleGrowth.embed_adjacent, CircleGrowth.intersection_lattice, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
HexEmbedding.frame: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.embed, HexEmbedding.frame_surjective, HexEmbedding.frame_zero, HexEmbedding.frame_one, HexEmbedding.frame_dist, HexEmbedding.frame_unit_iff, CircleGrowth.embed_adjacent, CircleGrowth.intersection_lattice, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
HexEmbedding.embed: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.embed_injective, CircleGrowth.intersection_lattice, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertex_card, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.first_four.
HexEmbedding.axial_re: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.axial_injective, HexEmbedding.axial_surjective, HexEmbedding.axial_dist_sq.
HexEmbedding.axial_im: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.axial_injective, HexEmbedding.axial_surjective, HexEmbedding.axial_dist_sq.
HexEmbedding.axial_injective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.embed_injective.
HexEmbedding.axial_surjective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.intersection_lattice.
HexEmbedding.frame_injective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.embed_injective.
HexEmbedding.frame_surjective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.intersection_lattice.
HexEmbedding.frame_zero: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
HexEmbedding.frame_one: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
HexEmbedding.embed_injective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertex_card, D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.first_four.
HexEmbedding.frame_dist: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.frame_unit_iff.
HexEmbedding.axial_dist_sq: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: HexEmbedding.frame_unit_iff.
HexEmbedding.frame_unit_iff: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.embed_adjacent, CircleGrowth.intersection_lattice.
CircleGrowth.directions_neg: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image, D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference.WindowTransport.window_adj.
CircleGrowth.directions_q: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.embed_adjacent.
CircleGrowth.unit_int_directions: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: CircleGrowth.intersection_lattice.
CircleGrowth.embed_adjacent: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
CircleGrowth.intersection_lattice: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: D5.S3.Geometry.ShannonFixedRadiusCircleVertices.CircleGrowth.vertices_image.
-/
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.InnerProductSpace.PiL2
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
import D5.S3.Arith.ModularForms.CubicThetaLattice





/-! Exact lattice growth and circle-vertex identities. -/
noncomputable section
namespace D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth


namespace MarkeyA400701

/-- The six unit displacements in axial coordinates of the triangular lattice. -/
def directions : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (1, -1), (-1, 0), (0, -1), (-1, 1)}

/-- At horizon n the window has a spare layer beyond the unit-speed reachable region. -/
def coordinates (n : ℕ) (p : Fin (2 * n + 7) × Fin (2 * n + 3)) : ℤ × ℤ :=
  ((p.1.val : ℤ) - (n : ℤ) - 1, (p.2.val : ℤ) - (n : ℤ) - 1)

/-- Induced triangular-lattice graph on that window; no wraparound edges. -/
def windowGraph (n : ℕ) : SimpleGraph (Fin (2 * n + 7) × Fin (2 * n + 3)) :=
  SimpleGraph.fromRel fun p q => coordinates n q - coordinates n p ∈ directions

/-- Exactly the five consecutive sites (0,0), ..., (4,0). -/
def seed (n : ℕ) : Finset (Fin (2 * n + 7) × Fin (2 * n + 3)) :=
  Finset.univ.filter fun p =>
    0 ≤ (coordinates n p).1 ∧ (coordinates n p).1 ≤ 4 ∧ (coordinates n p).2 = 0

/-- Simultaneous threshold-two growth, reusing the existing D5 step definition. -/
noncomputable def latticeCount (n : ℕ) : ℕ := by
  classical
  exact ((D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.step
    (windowGraph n) 2)^[n] (seed n)).card

end MarkeyA400701

namespace HexGrowth

private def moves : Finset (ℤ × ℤ) := {(1,1), (-1,2), (2,-1), (-1,-1), (1,-2), (-2,1)}

def Hex (A L : ℤ) (p : (ℤ × ℤ)) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ L ∧ 0 ≤ p.2 ∧ p.2 ≤ L ∧
  A ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 2*L-A

private def TwoOld (A L : ℤ) (p : (ℤ × ℤ)) : Prop :=
  ∃ d ∈ moves, ∃ e ∈ moves, d ≠ e ∧ Hex A L (p+d) ∧ Hex A L (p+e)

set_option maxRecDepth 2000
set_option maxHeartbeats 4000000

private theorem hex_persists (A L : ℤ) (p : (ℤ × ℤ)) (h : Hex A L p) : Hex (A+1) (L+2) (p+(1,1)) := by
  unfold Hex at *; dsimp at *; omega

private theorem two_old_bounded (A L : ℤ) (p : (ℤ × ℤ)) (h : TwoOld A L p) : Hex (A+1) (L+2) (p+(1,1)) := by
  rcases p with ⟨x,y⟩
  rcases h with ⟨d,hd,e,he,hde,hdh,heh⟩
  simp only [moves, Finset.mem_insert, Finset.mem_singleton] at hd he
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [Hex, Prod.mk_add_mk] <;> omega

private theorem expanded_has_two (A L : ℤ) (p : (ℤ × ℤ)) (hA : 3 ≤ A) (hL : A+2 ≤ L)
    (hp : Hex (A+1) (L+2) (p+(1,1))) (hn : ¬ Hex A L p) : TwoOld A L p := by
  rcases p with ⟨x,y⟩
  have mk (d e : (ℤ × ℤ)) (hd : d ∈ moves) (he : e ∈ moves) (hne : d ≠ e)
      (h1 : Hex A L ((x,y)+d)) (h2 : Hex A L ((x,y)+e)) : TwoOld A L (x,y) :=
    ⟨d,hd,e,he,hne,h1,h2⟩
  unfold Hex at hp
  dsimp at hp
  by_cases hsum : x+y = A-1
  · by_cases hx : 1 ≤ x
    · apply mk (1,1) (-1,2) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (1,1) (2,-1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  by_cases hsum' : x+y = 2*L-A+1
  · by_cases hx : x ≤ L-1
    · apply mk (-1,-1) (1,-2) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (-1,-1) (-2,1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  by_cases hx : x = -1
  · by_cases hy : y ≤ A+1
    · apply mk (2,-1) (1,1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (2,-1) (1,-2) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  by_cases hx' : x = L+1
  · by_cases hy : L-y ≤ A+1
    · apply mk (-2,1) (-1,-1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (-2,1) (-1,2) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  by_cases hy : y = -1
  · by_cases hx : x ≤ A+1
    · apply mk (-1,2) (1,1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (-1,2) (-2,1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  by_cases hy' : y = L+1
  · by_cases hx : L-x ≤ A+1
    · apply mk (1,-2) (-1,-1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
    · apply mk (1,-2) (2,-1) <;> norm_num [moves, Hex, Prod.mk_add_mk] <;> omega
  exact False.elim (hn (by unfold Hex; dsimp; omega))

private theorem hex_update (A L : ℤ) (p : (ℤ × ℤ)) (hA : 3 ≤ A) (hL : A+2 ≤ L) :
    Hex (A+1) (L+2) (p+(1,1)) ↔ Hex A L p ∨ TwoOld A L p := by
  constructor
  · intro hp
    by_cases h : Hex A L p
    · exact Or.inl h
    · exact Or.inr (expanded_has_two A L p hA hL hp h)
  · rintro (h|h)
    · exact hex_persists A L p h
    · exact two_old_bounded A L p h

end HexGrowth

namespace AxialGrowth

def transform (n : ℕ) (p : (ℤ × ℤ)) : (ℤ × ℤ) := (p.1-p.2+n,p.1+2*p.2+n)

def H (m n : ℕ) : Set (ℤ × ℤ) :=
  {p | HexGrowth.Hex ((n:ℤ)+1) ((m:ℤ)-1+2*n) (transform n p)}

def Two (S : Set (ℤ × ℤ)) (p : (ℤ × ℤ)) : Prop :=
  ∃ d ∈ MarkeyA400701.directions, ∃ e ∈ MarkeyA400701.directions,
    d ≠ e ∧ p+d ∈ S ∧ p+e ∈ S

def next (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := S ∪ {p | Two S p}

def initial (m : ℕ) : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ p.1 < m ∧ p.2=0}

def grown (m : ℕ) : ℕ → Set (ℤ × ℤ)
  | 0 => initial m
  | n+1 => next (grown m n)

private theorem linear_injective : Function.Injective D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling := by
  rintro ⟨x,y⟩ ⟨u,v⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling] at hx hy
  apply Prod.ext <;> dsimp <;> omega

private theorem moves_image : HexGrowth.moves = MarkeyA400701.directions.image D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling := by
  exact Finset.val_inj.mp rfl

private theorem transform_add (n : ℕ) (p d : (ℤ × ℤ)) :
    transform n (p+d) = transform n p + D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling d := by
  ext <;> simp [transform,D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling] <;> ring

private theorem two_transform (m n : ℕ) (p : (ℤ × ℤ)) :
    HexGrowth.TwoOld ((n:ℤ)+1) ((m:ℤ)-1+2*n) (transform n p) ↔ Two (H m n) p := by
  constructor
  · rintro ⟨d,hd,e,he,hde,h1,h2⟩
    rw [moves_image] at hd he
    obtain ⟨dd,hdd,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ee,hee,rfl⟩ := Finset.mem_image.mp he
    refine ⟨dd,hdd,ee,hee,?_,?_,?_⟩
    · exact fun h => hde (congrArg D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling h)
    · simpa only [H,Set.mem_setOf_eq,transform_add] using h1
    · simpa only [H,Set.mem_setOf_eq,transform_add] using h2
  · rintro ⟨d,hd,e,he,hde,h1,h2⟩
    refine ⟨D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling d,?_,D5.S3.Arith.ModularForms.CubicThetaLattice.normTripling e,?_,?_,?_,?_⟩
    · rw [moves_image]; exact Finset.mem_image_of_mem _ hd
    · rw [moves_image]; exact Finset.mem_image_of_mem _ he
    · exact fun h => hde (linear_injective h)
    · simpa only [H,Set.mem_setOf_eq,transform_add] using h1
    · simpa only [H,Set.mem_setOf_eq,transform_add] using h2

private theorem expanded_next (m n : ℕ) (p : (ℤ × ℤ)) :
    p ∈ H m (n+1) ↔ HexGrowth.Hex (((n:ℤ)+1)+1) (((m:ℤ)-1+2*n)+2) (transform n p+(1,1)) := by
  simp only [H,Set.mem_setOf_eq,HexGrowth.Hex,transform,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,
    Nat.cast_add,Nat.cast_one]
  omega

private theorem shape_step (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    next (H m n) = H m (n+1) := by
  ext p
  rw [expanded_next,HexGrowth.hex_update _ _ _ (by omega) (by omega),two_transform]
  rfl

def first (m : ℕ) : Set (ℤ × ℤ) := {p |
  (p.2=0 ∧ 0 ≤ p.1 ∧ p.1 < m) ∨
  (p.2=1 ∧ 0 ≤ p.1 ∧ p.1 < (m:ℤ)-1) ∨
  (p.2= -1 ∧ 1 ≤ p.1 ∧ p.1 < m)}

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

private theorem first_y_bounds (m : ℕ) (p : (ℤ × ℤ)) (hp : p ∈ first m) :
    -1 ≤ p.2 ∧ p.2 ≤ 1 := by
  rcases p with ⟨x,y⟩
  simp only [first,Set.mem_setOf_eq] at hp
  omega

theorem first_step (m : ℕ) : grown m 1 = first m := by
  ext p
  rcases p with ⟨x,y⟩
  simp only [grown,next,Set.mem_union,Set.mem_setOf_eq]
  by_cases hy : -1 ≤ y ∧ y ≤ 1
  · obtain ⟨hlo,hhi⟩ := hy
    interval_cases y <;>
      simp [Two,initial,MarkeyA400701.directions,first] <;> omega
  · constructor
    · rintro (hp|hp)
      · simp only [initial,Set.mem_setOf_eq] at hp
        omega
      · obtain ⟨d,hd,e,he,hde,h1,h2⟩ := hp
        simp only [MarkeyA400701.directions,Finset.mem_insert,Finset.mem_singleton] at hd
        rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp only [initial,Set.mem_setOf_eq,Prod.mk_add_mk] at h1 <;> omega
    · intro hp
      have hb := first_y_bounds _ _ hp
      omega

private theorem second_step (m : ℕ) (hm : m=2 ∨ m=5) : grown m 2 = H m 2 := by
  change next (grown m 1) = H m 2
  rw [first_step m]
  ext p
  rcases p with ⟨x,y⟩
  rcases hm with rfl|rfl
  all_goals
    by_cases hy : -2 ≤ y ∧ y ≤ 2
    · obtain ⟨hlo,hhi⟩ := hy
      interval_cases y <;>
        simp [next,Two,first,MarkeyA400701.directions,H,HexGrowth.Hex,transform] <;>
        omega
    · constructor
      · rintro (hp|hp)
        · have hb := first_y_bounds _ _ hp
          omega
        · obtain ⟨d,hd,e,he,hde,h1,h2⟩ := hp
          have hb := first_y_bounds _ _ h1
          simp only [MarkeyA400701.directions,Finset.mem_insert,Finset.mem_singleton] at hd
          rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp only [Prod.mk_add_mk] at hb <;> omega
      · intro hp
        simp only [H,Set.mem_setOf_eq,HexGrowth.Hex,transform] at hp
        norm_num at hp
        omega

theorem exact_shape (m n : ℕ) (hm : m=2 ∨ m=5) (hn : 2 ≤ n) : grown m n = H m n := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
  induction k with
  | zero => simpa using second_step m hm
  | succ k ih =>
    rw [show k+1+2=(k+2)+1 by omega,grown,ih (by omega),shape_step m (k+2) (by omega) (by omega)]

end AxialGrowth

set_option autoImplicit false
set_option maxRecDepth 2000

namespace HexCircleArithmetic

private theorem q_nonneg (x y : ℝ) : 0 ≤ ((x)*(x)+(x)*(y)+(y)*(y)) := by
  nlinarith [sq_nonneg (2*x+y), sq_nonneg y]

private theorem displacement_le_four (a b x y : ℝ) (h1 : ((x)*(x)+(x)*(y)+(y)*(y)) = 1)
    (h2 : (((x-a))*((x-a))+((x-a))*((y-b))+((y-b))*((y-b))) = 1) : ((a)*(a)+(a)*(b)+(b)*(b)) ≤ 4 := by
  have h := q_nonneg (2*x-a) (2*y-b)
  nlinarith

private theorem displacement_bounds (a b : ℤ) (hq : (((a:ℝ))*((a:ℝ))+((a:ℝ))*((b:ℝ))+((b:ℝ))*((b:ℝ))) ≤ 4) :
    -2 ≤ a ∧ a ≤ 2 ∧ -2 ≤ b ∧ b ≤ 2 := by
  have hi : a*a+a*b+b*b ≤ 4 := by exact_mod_cast hq
  have ha : 3*a*a ≤ 16 := by nlinarith [sq_nonneg (a+2*b)]
  have hb : 3*b*b ≤ 16 := by nlinarith [sq_nonneg (2*a+b)]
  constructor
  · by_contra h
    have : a ≤ -3 := by omega
    nlinarith [sq_nonneg (a+3)]
  constructor
  · by_contra h
    have : 3 ≤ a := by omega
    nlinarith [sq_nonneg (a-3)]
  constructor
  · by_contra h
    have : b ≤ -3 := by omega
    nlinarith [sq_nonneg (b+3)]
  · by_contra h
    have : 3 ≤ b := by omega
    nlinarith [sq_nonneg (b-3)]

private def UnitNeighbor (x y : ℝ) : Prop :=
  (x=1 ∧ y=0) ∨ (x=0 ∧ y=1) ∨ (x=1 ∧ y= -1) ∨
  (x= -1 ∧ y=0) ∨ (x=0 ∧ y= -1) ∨ (x= -1 ∧ y=1)

set_option maxHeartbeats 2000000

private theorem integer_center_intersection (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) (x y : ℝ)
    (h1 : ((x)*(x)+(x)*(y)+(y)*(y)) = 1) (h2 : (((x-(a:ℝ)))*((x-(a:ℝ)))+((x-(a:ℝ)))*((y-(b:ℝ)))+((y-(b:ℝ)))*((y-(b:ℝ)))) = 1) :
    UnitNeighbor x y ∧ UnitNeighbor (x-(a:ℝ)) (y-(b:ℝ)) := by
  have hq := displacement_le_four (a:ℝ) (b:ℝ) x y h1 h2
  obtain ⟨ha,ha',hb,hb'⟩ := displacement_bounds a b hq
  interval_cases a <;> interval_cases b
  all_goals norm_num at *
  · have hl : (-4:ℝ)*x+(-2:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(-1:ℝ))^2+(y-(0:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(-1:ℝ) := by nlinarith [sq_nonneg (y-(0:ℝ))]
    have hyy : y=(0:ℝ) := by nlinarith [sq_nonneg (x-(-1:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-3:ℝ)*x+(0:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (y-(0:ℝ))*(y-(1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-2:ℝ)*x+(2:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(-1:ℝ))^2+(y-(1:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(-1:ℝ) := by nlinarith [sq_nonneg (y-(1:ℝ))]
    have hyy : y=(1:ℝ) := by nlinarith [sq_nonneg (x-(-1:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-3:ℝ)*x+(-3:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(-1:ℝ))*(x-(0:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-2:ℝ)*x+(-1:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(0:ℝ))*(x-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-1:ℝ)*x+(1:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(0:ℝ))*(x-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (0:ℝ)*x+(3:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(0:ℝ))*(x-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-2:ℝ)*x+(-4:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(0:ℝ))^2+(y-(-1:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(0:ℝ) := by nlinarith [sq_nonneg (y-(-1:ℝ))]
    have hyy : y=(-1:ℝ) := by nlinarith [sq_nonneg (x-(0:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (-1:ℝ)*x+(-2:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(1:ℝ))*(x-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (1:ℝ)*x+(2:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(1:ℝ))*(x-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(-1:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (2:ℝ)*x+(4:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(0:ℝ))^2+(y-(1:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(0:ℝ) := by nlinarith [sq_nonneg (y-(1:ℝ))]
    have hyy : y=(1:ℝ) := by nlinarith [sq_nonneg (x-(0:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (0:ℝ)*x+(-3:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(1:ℝ))*(x-(0:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (1:ℝ)*x+(-1:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(1:ℝ))*(x-(0:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (2:ℝ)*x+(1:ℝ)*y-(1:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(0:ℝ))*(x-(1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (3:ℝ)*x+(3:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (x-(1:ℝ))*(x-(0:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(0:ℝ) := by linarith
      have hyy : y=(1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (2:ℝ)*x+(-2:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(1:ℝ))^2+(y-(-1:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(1:ℝ) := by nlinarith [sq_nonneg (y-(-1:ℝ))]
    have hyy : y=(-1:ℝ) := by nlinarith [sq_nonneg (x-(1:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (3:ℝ)*x+(0:ℝ)*y-(3:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have hf : (y-(0:ℝ))*(y-(-1:ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz|hz
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(0:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
    · have hxx : x=(1:ℝ) := by linarith
      have hyy : y=(-1:ℝ) := by linarith
      norm_num [UnitNeighbor,hxx,hyy]
  · have hl : (4:ℝ)*x+(2:ℝ)*y-(4:ℝ) = 0 := by nlinarith
    have hx := congrArg (fun z : ℝ => z*x) hl
    have hy := congrArg (fun z : ℝ => z*y) hl
    have he : (x-(1:ℝ))^2+(y-(0:ℝ))^2 = 0 := by nlinarith
    have hxx : x=(1:ℝ) := by nlinarith [sq_nonneg (y-(0:ℝ))]
    have hyy : y=(0:ℝ) := by nlinarith [sq_nonneg (x-(1:ℝ))]
    norm_num [UnitNeighbor,hxx,hyy]

end HexCircleArithmetic

namespace HexEmbedding

def axial (x y : ℝ) : ℂ := (x+y/2 : ℝ) + (Real.sqrt 3*y/2 : ℝ)*Complex.I

def frame (a b : (EuclideanSpace ℝ (Fin 2))) (z : ℂ) : (EuclideanSpace ℝ (Fin 2)) :=
  Complex.orthonormalBasisOneI.repr
    (AffineMap.lineMap (Complex.orthonormalBasisOneI.repr.symm a)
      (Complex.orthonormalBasisOneI.repr.symm b) z)

def embed (a b : (EuclideanSpace ℝ (Fin 2))) (p : ℤ×ℤ) : (EuclideanSpace ℝ (Fin 2)) := frame a b (axial p.1 p.2)

private theorem axial_re (x y : ℝ) : (axial x y).re = x+y/2 := by simp [axial]
private theorem axial_im (x y : ℝ) : (axial x y).im = Real.sqrt 3*y/2 := by simp [axial]

private theorem axial_injective : Function.Injective (fun p : ℝ×ℝ => axial p.1 p.2) := by
  rintro ⟨x,y⟩ ⟨u,v⟩ h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [axial_re,axial_im] at hr hi
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply Prod.ext <;> dsimp <;> nlinarith

private theorem axial_surjective : Function.Surjective (fun p : ℝ×ℝ => axial p.1 p.2) := by
  intro z
  refine ⟨(z.re-z.im/Real.sqrt 3,2*z.im/Real.sqrt 3),?_⟩
  apply Complex.ext
  · simp only [axial_re]
    ring
  · simp only [axial_im]
    have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp

private theorem frame_injective (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) : Function.Injective (frame a b) := by
  exact Complex.orthonormalBasisOneI.repr.injective.comp
    (AffineMap.lineMap_injective ℂ (fun h => hab (Complex.orthonormalBasisOneI.repr.symm.injective h)))

private theorem frame_surjective (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) : Function.Surjective (frame a b) := by
  have hba : Complex.orthonormalBasisOneI.repr.symm b-Complex.orthonormalBasisOneI.repr.symm a ≠ 0 := by
    intro h
    apply hab
    exact (Complex.orthonormalBasisOneI.repr.symm.injective (sub_eq_zero.mp h)).symm
  intro p
  refine ⟨(Complex.orthonormalBasisOneI.repr.symm p-Complex.orthonormalBasisOneI.repr.symm a)/(Complex.orthonormalBasisOneI.repr.symm b-Complex.orthonormalBasisOneI.repr.symm a),?_⟩
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  simp only [frame,AffineMap.lineMap_apply_ring',LinearIsometryEquiv.symm_apply_apply]
  field_simp; ring

theorem frame_zero (a b : (EuclideanSpace ℝ (Fin 2))) : frame a b 0 = a := by
  simp only [frame, AffineMap.lineMap_apply_zero, LinearIsometryEquiv.apply_symm_apply]

theorem frame_one (a b : (EuclideanSpace ℝ (Fin 2))) : frame a b 1 = b := by
  simp only [frame, AffineMap.lineMap_apply_one, LinearIsometryEquiv.apply_symm_apply]

theorem embed_injective (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) : Function.Injective (embed a b) := by
  intro p r h
  have hh : ((p.1:ℝ),(p.2:ℝ)) = ((r.1:ℝ),(r.2:ℝ)) :=
    @axial_injective ((p.1:ℝ),(p.2:ℝ)) ((r.1:ℝ),(r.2:ℝ))
      (@frame_injective a b hab (axial p.1 p.2) (axial r.1 r.2) h)
  apply Prod.ext
  · have he : (p.1:ℝ)=(r.1:ℝ) := (Prod.ext_iff.mp hh).1
    exact_mod_cast he
  · have he : (p.2:ℝ)=(r.2:ℝ) := (Prod.ext_iff.mp hh).2
    exact_mod_cast he

private theorem frame_dist (a b : (EuclideanSpace ℝ (Fin 2))) (z w : ℂ) :
    dist (frame a b z) (frame a b w) = dist a b * dist z w := by
  simp only [frame, Complex.orthonormalBasisOneI.repr.dist_map,
    dist_lineMap_lineMap, Complex.orthonormalBasisOneI.repr.symm.dist_map]
  exact mul_comm _ _

private theorem axial_dist_sq (x y u v : ℝ) :
    dist (axial x y) (axial u v)^2 = (((x-u))*((x-u))+((x-u))*((y-v))+((y-v))*((y-v))) := by
  rw [dist_eq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,axial_re,axial_im]
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  ring_nf
  simp only [hs]
  ring

private theorem frame_unit_iff (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) (x y u v : ℝ) :
    dist (frame a b (axial x y)) (frame a b (axial u v)) = dist a b ↔
      (((x-u))*((x-u))+((x-u))*((y-v))+((y-v))*((y-v))) = 1 := by
  have hr : 0 < dist a b := dist_pos.mpr hab
  rw [frame_dist]
  constructor
  · intro h
    have he : dist (axial x y) (axial u v) = 1 := by nlinarith
    rw [← axial_dist_sq,he]
    norm_num
  · intro h
    have he : dist (axial x y) (axial u v) = 1 := by
      have hh := axial_dist_sq x y u v
      rw [h] at hh
      nlinarith [(dist_nonneg : 0 ≤ dist (axial x y) (axial u v))]
    rw [he,mul_one]

end HexEmbedding

namespace CircleGrowth
open HexEmbedding

theorem directions_neg (p : ℤ×ℤ) :
    -p ∈ MarkeyA400701.directions ↔ p ∈ MarkeyA400701.directions := by
  rcases p with ⟨x,y⟩
  simp [MarkeyA400701.directions,Prod.ext_iff]
  omega

private theorem directions_q (p : ℤ×ℤ) (hp : p ∈ MarkeyA400701.directions) :
    (((p.1:ℝ))*((p.1:ℝ))+((p.1:ℝ))*((p.2:ℝ))+((p.2:ℝ))*((p.2:ℝ))) = 1 := by
  simp only [MarkeyA400701.directions,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

private theorem unit_int_directions (p : ℤ×ℤ) :
    HexCircleArithmetic.UnitNeighbor (p.1:ℝ) (p.2:ℝ) ↔ p ∈ MarkeyA400701.directions := by
  rcases p with ⟨x,y⟩
  simp only [HexCircleArithmetic.UnitNeighbor,MarkeyA400701.directions,
    Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  norm_cast

theorem embed_adjacent (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) (u v : ℤ×ℤ)
    (h : u-v ∈ MarkeyA400701.directions) : dist (embed a b u) (embed a b v)=dist a b := by
  apply (frame_unit_iff a b hab _ _ _ _).mpr
  have hq := directions_q (u-v) h
  simpa only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub] using hq

theorem intersection_lattice (a b : (EuclideanSpace ℝ (Fin 2))) (hab : a ≠ b) (u v : ℤ×ℤ) (huv : u ≠ v)
    (p : (EuclideanSpace ℝ (Fin 2))) (hu : dist p (embed a b u)=dist a b)
    (hv : dist p (embed a b v)=dist a b) :
    ∃ w : ℤ×ℤ, embed a b w=p ∧
      w-u ∈ MarkeyA400701.directions ∧ w-v ∈ MarkeyA400701.directions := by
  obtain ⟨z,rfl⟩ := frame_surjective a b hab p
  obtain ⟨⟨x,y⟩,rfl⟩ := axial_surjective z
  have huq := (frame_unit_iff a b hab x y u.1 u.2).mp hu
  have hvq := (frame_unit_iff a b hab x y v.1 v.2).mp hv
  have hd : v.1-u.1 ≠ 0 ∨ v.2-u.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply huv
    apply Prod.ext <;> omega
  have hxu : x-(u.1:ℝ)-((v.1-u.1:ℤ):ℝ) = x-(v.1:ℝ) := by
    push_cast
    ring
  have hyu : y-(u.2:ℝ)-((v.2-u.2:ℤ):ℝ) = y-(v.2:ℝ) := by
    push_cast
    ring
  have hi := HexCircleArithmetic.integer_center_intersection (v.1-u.1) (v.2-u.2) hd
    (x-u.1) (y-u.2) huq (by rw [hxu,hyu]; exact hvq)
  rw [hxu,hyu] at hi
  have mk (d : ℤ×ℤ) (hx : x-(u.1:ℝ)=(d.1:ℝ)) (hy : y-(u.2:ℝ)=(d.2:ℝ)) :
      ∃ w : ℤ×ℤ, embed a b w=frame a b (axial x y) ∧
        w-u ∈ MarkeyA400701.directions ∧ w-v ∈ MarkeyA400701.directions := by
    refine ⟨u+d,?_,?_,?_⟩
    · unfold embed
      congr 1
      congr 1 <;> simp only [Prod.fst_add,Prod.snd_add,Int.cast_add] <;> linarith
    · have hdir : d ∈ MarkeyA400701.directions :=
        (unit_int_directions d).mp (by simpa only [hx,hy] using hi.1)
      simpa only [add_sub_cancel_left] using hdir
    · have hxv : (((u+d-v).1:ℤ):ℝ)=x-(v.1:ℝ) := by
        simp only [Prod.fst_sub,Prod.fst_add,Int.cast_sub,Int.cast_add]
        linarith
      have hyv : (((u+d-v).2:ℤ):ℝ)=y-(v.2:ℝ) := by
        simp only [Prod.snd_sub,Prod.snd_add,Int.cast_sub,Int.cast_add]
        linarith
      apply (unit_int_directions _).mp
      rw [hxv,hyv]
      exact hi.2
  rcases hi.1 with h|h|h|h|h|h
  · exact mk (1,0) (by simpa using h.1) (by simpa using h.2)
  · exact mk (0,1) (by simpa using h.1) (by simpa using h.2)
  · exact mk (1,-1) (by simpa using h.1) (by simpa using h.2)
  · exact mk (-1,0) (by simpa using h.1) (by simpa using h.2)
  · exact mk (0,-1) (by simpa using h.1) (by simpa using h.2)
  · exact mk (-1,1) (by simpa using h.1) (by simpa using h.2)

end CircleGrowth

end D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth
end
