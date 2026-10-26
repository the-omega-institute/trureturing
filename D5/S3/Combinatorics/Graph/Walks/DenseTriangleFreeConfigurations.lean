/- GID: D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.pentagon_hom; premises=D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.a3_independent_bound,D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.myc_independent_bound,D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.myc_total_weight
   digest: Dense triangle-free configurations exclude induced hexagons. -/

/-
admission_basis: escape-witness: HaggHexagon.no_hexagon
escape_witness: D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations.HaggHexagon.no_hexagon
Direct frozen dependencies:
  none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20094
HaggFinitePatterns.A3Edges: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.A3, HaggFinitePatterns.instDecidableAdjA3, HaggLocalConfigurations.twin_edge_zero_two; Direct frozen dependencies: none
HaggFinitePatterns.MycEdges: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.Myc, HaggFinitePatterns.instDecidableAdjMyc, HaggLocalConfigurations.myc_of_hexagon_configuration; Direct frozen dependencies: none
HaggFinitePatterns.A3: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.a3_independent_bound, HaggFinitePatterns.instDecidableAdjA3, HaggForbidden.no_a3, HaggLocalConfigurations.twin_edge_zero_two, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.transfer_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_with_neighbor, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.every_vertex_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.pentagon_partition; Direct frozen dependencies: none
HaggFinitePatterns.instDecidableAdjA3: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.a3_independent_bound; Direct frozen dependencies: none
HaggFinitePatterns.Myc: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.instDecidableAdjMyc, HaggFinitePatterns.myc_independent_bound, HaggForbidden.no_myc, HaggHexagon.myc_of_anchor, HaggHexagon.myc_of_hexagon, HaggHexagon.no_hexagon, HaggLocalConfigurations.myc_of_hexagon_configuration; Direct frozen dependencies: none
HaggFinitePatterns.instDecidableAdjMyc: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.myc_independent_bound; Direct frozen dependencies: none
HaggFinitePatterns.mycWeight: proof_shape: bind-only; escape_witness: none; consumers: HaggFinitePatterns.myc_independent_bound, HaggFinitePatterns.myc_total_weight, HaggForbidden.no_myc; Direct frozen dependencies: none
HaggFinitePatterns.a3_independent_bound: proof_shape: bind-only; escape_witness: none; consumers: HaggForbidden.no_a3; Direct frozen dependencies: none
HaggFinitePatterns.myc_independent_bound: proof_shape: bind-only; escape_witness: none; consumers: HaggForbidden.no_myc; Direct frozen dependencies: none
HaggFinitePatterns.myc_total_weight: proof_shape: bind-only; escape_witness: none; consumers: HaggForbidden.no_myc; Direct frozen dependencies: none
HaggLocalConfigurations.pentagon_edge_iff: proof_shape: bind-only; escape_witness: none; consumers: HaggLocalConfigurations.twin_edge_zero_two, HaggLocalConfigurations.twin_of_two, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.old_base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggBipartiteAlternative.pentagon_of_missing_cross, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.every_vertex_twin; Direct frozen dependencies: none
HaggLocalConfigurations.Pentagon: proof_shape: bind-only; escape_witness: none; consumers: HaggLocalConfigurations.twin_edge_zero_two, HaggLocalConfigurations.twin_of_two, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.old_base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.replace_pentagon, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.transfer_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggBipartiteAlternative.pentagon_of_missing_cross, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggBipartiteAlternative.two_sides_of_no_pentagon, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.adjacency_of_twins, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_with_neighbor, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.base_transition, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.every_vertex_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.pentagon_partition, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggLocalConfigurations.Twin: proof_shape: bind-only; escape_witness: none; consumers: HaggLocalConfigurations.twin_edge_zero_two, HaggLocalConfigurations.twin_of_two, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.old_base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.replace_pentagon, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.transfer_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.adjacency_of_twins, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_with_neighbor, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.every_vertex_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.pentagon_partition; Direct frozen dependencies: none
HaggLocalConfigurations.NoHex: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.no_hexagon, HaggLocalConfigurations.twin_edge_zero_two, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.transfer_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_with_neighbor, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.every_vertex_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.pentagon_partition, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggLocalConfigurations.twin_of_two: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.base_twin, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggFullAttachment.attachment_zero; Direct frozen dependencies: none
HaggLocalConfigurations.myc_of_hexagon_configuration: proof_shape: content; escape_witness: HaggLocalConfigurations.myc_of_hexagon_configuration; consumers: HaggHexagon.myc_of_anchor; Direct frozen dependencies: none
HaggLocalConfigurations.twin_edge_zero_two: proof_shape: content; escape_witness: HaggLocalConfigurations.twin_edge_zero_two; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggAttachment.twin_edge; Direct frozen dependencies: none
DenseDegreeCounting.weighted_degree_identity: proof_shape: bind-only; escape_witness: none; consumers: DenseDegreeCounting.weighted_degree_bound; Direct frozen dependencies: none
DenseDegreeCounting.weighted_degree_bound: proof_shape: bind-only; escape_witness: none; consumers: DenseDegreeCounting.exists_many_adjacent, DenseDegreeCounting.hom_weighted_degree_bound; Direct frozen dependencies: none
DenseDegreeCounting.hom_weighted_degree_bound: proof_shape: bind-only; escape_witness: none; consumers: HaggForbidden.no_a3, HaggForbidden.no_myc; Direct frozen dependencies: none
DenseDegreeCounting.exists_many_adjacent: proof_shape: bind-only; escape_witness: none; consumers: HaggForbidden.d2, HaggForbidden.d3; Direct frozen dependencies: none
HaggForbidden.triangle_free_of_clique_free: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.VertexDeletionBridges.neighbors_independent, D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggForbidden.no_a3: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggForbidden.no_myc: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggForbidden.d2: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HaggForbidden.d3: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
HexIndependentPatterns.hexEdges: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.hexagon_triple, HexIndependentPatterns.Hex, HexIndependentPatterns.instDecidableAdjHex; Direct frozen dependencies: none
HexIndependentPatterns.seedEdges: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.seed_quad, HexIndependentPatterns.Seed, HexIndependentPatterns.instDecidableAdjSeed; Direct frozen dependencies: none
HexIndependentPatterns.Hex: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.hexagon_triple, HexIndependentPatterns.hex_patterns, HexIndependentPatterns.instDecidableAdjHex; Direct frozen dependencies: none
HexIndependentPatterns.instDecidableAdjHex: proof_shape: bind-only; escape_witness: none; consumers: HexIndependentPatterns.hex_patterns; Direct frozen dependencies: none
HexIndependentPatterns.Seed: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.seed_quad, HexIndependentPatterns.instDecidableAdjSeed, HexIndependentPatterns.seed_patterns; Direct frozen dependencies: none
HexIndependentPatterns.instDecidableAdjSeed: proof_shape: bind-only; escape_witness: none; consumers: HexIndependentPatterns.seed_patterns; Direct frozen dependencies: none
HexIndependentPatterns.hex_patterns: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.hexagon_triple; Direct frozen dependencies: none
HexIndependentPatterns.seed_patterns: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.seed_quad; Direct frozen dependencies: none
HaggHexagon.D2: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.hexagon_triple, HaggHexagon.myc_of_anchor, HaggHexagon.myc_of_hexagon, HaggHexagon.no_hexagon; Direct frozen dependencies: none
HaggHexagon.D3: proof_shape: bind-only; escape_witness: none; consumers: HaggHexagon.myc_of_hexagon, HaggHexagon.no_hexagon, HaggHexagon.seed_quad; Direct frozen dependencies: none
HaggHexagon.hexagon_triple: proof_shape: content; escape_witness: HaggHexagon.hexagon_triple; consumers: HaggHexagon.myc_of_anchor, HaggHexagon.no_hexagon; Direct frozen dependencies: none
HaggHexagon.myc_of_anchor: proof_shape: content; escape_witness: HaggHexagon.myc_of_anchor; consumers: HaggHexagon.myc_of_hexagon; Direct frozen dependencies: none
HaggHexagon.seed_quad: proof_shape: content; escape_witness: HaggHexagon.seed_quad; consumers: HaggHexagon.myc_of_hexagon; Direct frozen dependencies: none
HaggHexagon.myc_of_hexagon: proof_shape: content; escape_witness: HaggHexagon.myc_of_hexagon; consumers: HaggHexagon.no_hexagon; Direct frozen dependencies: none
HaggHexagon.no_hexagon: proof_shape: content; escape_witness: HaggHexagon.no_hexagon; consumers: D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism.HaggkvistDense.pentagon_hom; Direct frozen dependencies: none
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations



namespace HaggFinitePatterns
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def A3Edges : Finset (Fin 8 × Fin 8) := {(0, 3), (0, 4), (0, 5), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (3, 0), (3, 6), (3, 7), (4, 0), (4, 1), (4, 7), (5, 0), (5, 1), (5, 2), (6, 1), (6, 2), (6, 3), (7, 2), (7, 3), (7, 4)}

def MycEdges : Finset (Fin 11 × Fin 11) := {(0, 1), (0, 4), (0, 6), (0, 9), (1, 0), (1, 2), (1, 5), (1, 7), (2, 1), (2, 3), (2, 6), (2, 8), (3, 2), (3, 4), (3, 7), (3, 9), (4, 0), (4, 3), (4, 5), (4, 8), (5, 1), (5, 4), (5, 10), (6, 0), (6, 2), (6, 10), (7, 1), (7, 3), (7, 10), (8, 2), (8, 4), (8, 10), (9, 0), (9, 3), (9, 10), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9)}

def A3 : SimpleGraph (Fin 8) where
  Adj i j := (i,j) ∈ A3Edges
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private instance instDecidableAdjA3 : DecidableRel A3.Adj := fun i j => inferInstanceAs (Decidable ((i,j) ∈ A3Edges))

def Myc : SimpleGraph (Fin 11) where
  Adj i j := (i,j) ∈ MycEdges
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private instance instDecidableAdjMyc : DecidableRel Myc.Adj := fun i j => inferInstanceAs (Decidable ((i,j) ∈ MycEdges))

private def mycWeight (i : Fin 11) : ℕ := if i.val < 5 then 3 else if i.val < 10 then 2 else 4

/-- The eight-vertex Andrásfai graph has no independent four-set. -/
private theorem a3_independent_bound : ∀ S : Finset (Fin 8),
    (∀ i ∈ S, ∀ j ∈ S, ¬ A3.Adj i j) → S.card ≤ 3 := by
  all_goals decide +kernel

/-- A fractional-coloring dual on the Mycielski graph has total weight 29 and capacity ten. -/
private theorem myc_independent_bound : ∀ S : Finset (Fin 11),
    (∀ i ∈ S, ∀ j ∈ S, ¬ Myc.Adj i j) → ∑ i ∈ S, mycWeight i ≤ 10 := by
  all_goals decide +kernel

/-- The dual's normalization. -/
private theorem myc_total_weight : (∑ i, mycWeight i) = 29 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

end HaggFinitePatterns


namespace HaggLocalConfigurations
open HaggFinitePatterns
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {V : Type*} (G : SimpleGraph V)

/-- Multiplication by three gives the step-two ordering of the five-cycle. -/
theorem pentagon_edge_iff (i j : Fin 5) :
    ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j ↔
      j = i + 2 ∨ j = i + 3 := by
  revert i j
  decide +kernel



def Pentagon (p : Fin 5 → V) : Prop := ∀ i j, ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j → G.Adj (p i) (p j)

def Twin (p : Fin 5 → V) (x : V) (i : Fin 5) : Prop :=
  ∀ j, G.Adj x (p j) ↔ ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j

def NoHex : Prop := ∀ a b c d e f : V,
  G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a →
  G.Adj a d ∨ G.Adj b e ∨ G.Adj c f

/-- Two pentagon neighbors determine the full base-neighborhood of a vertex. -/
theorem twin_of_two (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (p : Fin 5 → V) (hp : Pentagon G p)
    (x : V) (i : Fin 5) (ha : G.Adj x (p (i + 2))) (hb : G.Adj x (p (i + 3))) :
    Twin G p x i := by
  have h02 := hp 0 2 (by decide)
  have h03 := hp 0 3 (by decide)
  have h13 := hp 1 3 (by decide)
  have h14 := hp 1 4 (by decide)
  have h24 := hp 2 4 (by decide)
  intro j
  fin_cases i <;> fin_cases j <;> simp only [pentagon_edge_iff] at ha hb ⊢
  all_goals norm_num at ha hb ⊢
  all_goals first | assumption | exact hG ha h02.symm | exact hG hb h03.symm |
    exact hG ha h13.symm | exact hG hb h14.symm |
    exact hG ha h24.symm | exact hG hb h02 | exact hG ha h03 |
    exact hG hb h13 | exact hG ha h14 | exact hG hb h24 |
    exact hG ha h02 | exact hG hb h03 | exact hG ha h13 | exact hG hb h14 |
    exact hG ha h24 | exact hG hb h02.symm | exact hG ha h03.symm |
    exact hG hb h13.symm | exact hG ha h14.symm | exact hG hb h24.symm

/-- The explicit eleven-vertex configuration constructed from a hexagon is Mycielski's graph. -/
private theorem myc_of_hexagon_configuration
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 x q : V)
    (h01 : G.Adj a1 b2) (h02 : G.Adj a1 b3) (h03 : G.Adj a1 c1)
    (h04 : G.Adj a2 b1) (h05 : G.Adj a2 b3) (h06 : G.Adj a2 c2)
    (h07 : G.Adj a2 q) (h08 : G.Adj a3 b1) (h09 : G.Adj a3 b2)
    (h10 : G.Adj a3 c3) (h11 : G.Adj b1 c1) (h12 : G.Adj b1 x)
    (h13 : G.Adj b2 c2) (h14 : G.Adj b2 x) (h15 : G.Adj b2 q)
    (h16 : G.Adj b3 c3) (h17 : G.Adj b3 x) (h18 : G.Adj c1 c2)
    (h19 : G.Adj c1 c3) (h20 : G.Adj c3 q) : Nonempty (Myc →g G) := by
  refine ⟨{ toFun := ![a2,b3,c3,c1,b1,x,q,a1,a3,c2,b2], map_rel' := ?_ }⟩
  intro i j hij
  change (i,j) ∈ MycEdges at hij
  simp only [MycEdges, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hij
  rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals norm_num
  all_goals first | assumption | exact h01.symm | exact h02.symm | exact h03.symm |
    exact h04.symm | exact h05.symm | exact h06.symm | exact h07.symm |
    exact h08.symm | exact h09.symm | exact h10.symm | exact h11.symm |
    exact h12.symm | exact h13.symm | exact h14.symm | exact h15.symm |
    exact h16.symm | exact h17.symm | exact h18.symm | exact h19.symm | exact h20.symm

/-- A missing edge between adjacent pentagon twin classes would force the eight-vertex obstruction. -/
theorem twin_edge_zero_two (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hn : NoHex G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hA3 : ¬ Nonempty (A3 →g G))
    (p : Fin 5 → V) (hp : Pentagon G p) (x y : V)
    (hx : Twin G p x 0) (hy : Twin G p y 2) : G.Adj x y := by
  by_contra hxy
  obtain ⟨r, hxr, hyr⟩ := hc x y hxy
  have hx2 := (hx 2).mpr (by decide)
  have hx3 := (hx 3).mpr (by decide)
  have hy0 := (hy 0).mpr (by decide)
  have hy4 := (hy 4).mpr (by decide)
  have h02 := hp 0 2 (by decide)
  have h03 := hp 0 3 (by decide)
  have h13 := hp 1 3 (by decide)
  have h14 := hp 1 4 (by decide)
  have h24 := hp 2 4 (by decide)
  have hr1 : G.Adj r (p 1) := by
    have h := hn x r y (p 4) (p 1) (p 3) hxr hyr.symm hy4 h14.symm h13 hx3.symm
    rcases h with h | h | h
    · have := (hx 4).mp h; simp only [pentagon_edge_iff] at this
      norm_num at this
    · exact h
    · have := (hy 3).mp h; simp only [pentagon_edge_iff] at this
      norm_num at this
  apply hA3
  refine ⟨{ toFun := ![p 0,x,p 1,y,p 2,p 3,r,p 4], map_rel' := ?_ }⟩
  intro i j hij
  change (i,j) ∈ A3Edges at hij
  simp only [A3Edges, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hij
  rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals norm_num
  all_goals first | assumption | exact hx2.symm | exact hx3.symm | exact hy0.symm |
    exact hy4.symm | exact hxr.symm | exact hyr.symm | exact hr1.symm |
    exact h02.symm | exact h03.symm | exact h13.symm | exact h14.symm | exact h24.symm

end HaggLocalConfigurations


namespace DenseDegreeCounting
open HaggLocalConfigurations
open Finset

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


/-- A weighted sum of degrees equals the same incidences counted at their other endpoint. -/
private theorem weighted_degree_identity (f : I → V) (w : I → ℕ) :
    ∑ i, w i * G.degree (f i) =
      ∑ v : V, ∑ i, if G.Adj v (f i) then w i else 0 := by
  classical
  have hd (a : V) : G.degree a = ∑ v : V, if G.Adj v a then 1 else 0 := by
    simp only [G.adj_comm]
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  simp_rw [hd, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  exact Finset.sum_comm

/-- A uniform bound on the weight seen by each vertex bounds the minimum degree. -/
private theorem weighted_degree_bound (f : I → V) (w : I → ℕ) (B : ℕ)
    (hB : ∀ v, (∑ i, if G.Adj v (f i) then w i else 0) ≤ B) :
    (∑ i, w i) * G.minDegree ≤ B * Fintype.card V := by
  calc
    (∑ i, w i) * G.minDegree = ∑ i, w i * G.minDegree := by rw [Finset.sum_mul]
    _ ≤ ∑ i, w i * G.degree (f i) :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (G.minDegree_le_degree (f i)))
    _ = ∑ v : V, ∑ i, if G.Adj v (f i) then w i else 0 :=
      weighted_degree_identity G f w
    _ ≤ ∑ _v : V, B := Finset.sum_le_sum fun v _ => hB v
    _ = B * Fintype.card V := by simp [Nat.mul_comm]

/-- Every homomorphic image of a weighted finite graph obeys its independent-set bound. -/
private theorem hom_weighted_degree_bound (F : SimpleGraph I) (f : F →g G)
    (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (w : I → ℕ) (B : ℕ)
    (hB : ∀ S : Finset I, (∀ i ∈ S, ∀ j ∈ S, ¬ F.Adj i j) → ∑ i ∈ S, w i ≤ B) :
    (∑ i, w i) * G.minDegree ≤ B * Fintype.card V := by
  classical
  apply weighted_degree_bound G f w B
  intro v
  rw [← Finset.sum_filter]
  apply hB
  intro i hi j hj hij
  exact hG (Finset.mem_filter.mp hi).2 (f.map_adj hij) (Finset.mem_filter.mp hj).2

/-- The dense-degree hypothesis supplies a common neighbor of more than k sequence positions. -/
private theorem exists_many_adjacent (f : I → V) (k : ℕ)
    (h : k * Fintype.card V < Fintype.card I * G.minDegree) :
    ∃ v : V, k < (Finset.univ.filter fun i : I => G.Adj v (f i)).card := by
  classical
  by_contra hnot
  push_neg at hnot
  have hb := weighted_degree_bound G f (fun _ => 1) k (fun v => by
    simpa [Finset.sum_filter] using hnot v)
  simpa using (not_lt_of_ge (by simpa using hb)) h

end DenseDegreeCounting

namespace HaggForbidden
open DenseDegreeCounting HaggFinitePatterns HaggLocalConfigurations
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The usual triangle-free predicate supplies the relational form used by degree counting. -/
theorem triangle_free_of_clique_free (h : G.CliqueFree 3) : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c) := by
  all_goals
    intro a b c hab hbc hac
    exact h {a,b,c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

/-- The strict three-eighths threshold excludes the eight-vertex Andrásfai graph. -/
theorem no_a3 (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd : 3 * Fintype.card V < 8 * G.minDegree) :
    ¬ Nonempty (A3 →g G) := by
  all_goals
    rintro ⟨f⟩
    have h := hom_weighted_degree_bound G A3 f hG (fun _ => 1) 3 (by
      intro S hS
      simpa using a3_independent_bound S hS)
    norm_num at h
    omega

/-- The Mycielski dual has capacity ten and total weight 29, so it is excluded at three-eighths. -/
theorem no_myc (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd : 3 * Fintype.card V < 8 * G.minDegree) :
    ¬ Nonempty (Myc →g G) := by
  all_goals
    rintro ⟨f⟩
    have h := hom_weighted_degree_bound G Myc f hG mycWeight 10 myc_independent_bound
    rw [myc_total_weight] at h
    omega

/-- The same threshold implies the common-neighbor property on six sequence positions. -/
theorem d2 (hd : 3 * Fintype.card V < 8 * G.minDegree) (f : Fin 6 → V) :
    ∃ v : V, 3 ≤ (univ.filter fun i : Fin 6 => G.Adj v (f i)).card := by
  all_goals
    have h := exists_many_adjacent G f 2 (by simp; omega)
    simpa only [Nat.succ_le_iff] using h

/-- The common-neighbor property on nine positions is also available. -/
theorem d3 (hd : 3 * Fintype.card V < 8 * G.minDegree) (f : Fin 9 → V) :
    ∃ v : V, 4 ≤ (univ.filter fun i : Fin 9 => G.Adj v (f i)).card := by
  all_goals
    have h := exists_many_adjacent G f 3 (by simp; omega)
    simpa only [Nat.succ_le_iff] using h

end HaggForbidden

namespace HexIndependentPatterns
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private def hexEdges : Finset (Fin 6 × Fin 6) := {(0,4),(0,5),(1,3),(1,5),(2,3),(2,4),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1)}

private def seedEdges : Finset (Fin 9 × Fin 9) := {(0,4),(0,5),(0,6),(1,3),(1,5),(1,7),(2,3),(2,4),(2,8),(3,1),(3,2),(3,6),(4,0),(4,2),(4,7),(5,0),(5,1),(5,8),(6,0),(6,3),(7,1),(7,4),(8,2),(8,5)}

private def Hex : SimpleGraph (Fin 6) where
  Adj i j := (i,j) ∈ hexEdges
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
private instance instDecidableAdjHex : DecidableRel Hex.Adj := fun i j => inferInstanceAs (Decidable ((i,j) ∈ hexEdges))

private def Seed : SimpleGraph (Fin 9) where
  Adj i j := (i,j) ∈ seedEdges
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
private instance instDecidableAdjSeed : DecidableRel Seed.Adj := fun i j => inferInstanceAs (Decidable ((i,j) ∈ seedEdges))

/-- A hexagon's independent triples are its two color classes. -/
private theorem hex_patterns : ∀ S : Finset (Fin 6),
    (∀ i ∈ S, ∀ j ∈ S, ¬ Hex.Adj i j) → 3 ≤ S.card →
    ({0,1,2} : Finset (Fin 6)) ⊆ S ∨ ({3,4,5} : Finset (Fin 6)) ⊆ S := by
  all_goals
    decide +kernel

/-- The nine-position hexagon seed has exactly the three indicated independent four-patterns. -/
private theorem seed_patterns : ∀ S : Finset (Fin 9),
    (∀ i ∈ S, ∀ j ∈ S, ¬ Seed.Adj i j) → 4 ≤ S.card →
    ({0,3,7,8} : Finset (Fin 9)) ⊆ S ∨
    ({1,4,6,8} : Finset (Fin 9)) ⊆ S ∨
    ({2,5,6,7} : Finset (Fin 9)) ⊆ S := by
  all_goals
    decide +kernel

end HexIndependentPatterns

namespace HaggHexagon
open Finset HaggFinitePatterns HaggLocalConfigurations HexIndependentPatterns
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

def D2 : Prop := ∀ f : Fin 6 → V,
  ∃ x, 3 ≤ (univ.filter fun i => G.Adj x (f i)).card

def D3 : Prop := ∀ f : Fin 9 → V,
  ∃ x, 4 ≤ (univ.filter fun i => G.Adj x (f i)).card

/-- A common neighbor of three hexagon positions sees an entire alternating triple. -/
private theorem hexagon_triple (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd : D2 G)
    (a1 a2 a3 b1 b2 b3 : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2) :
    ∃ x, (G.Adj x a1 ∧ G.Adj x a2 ∧ G.Adj x a3) ∨
      (G.Adj x b1 ∧ G.Adj x b2 ∧ G.Adj x b3) := by
  all_goals
    let f : Hex →g G :=
      { toFun := ![a1,a2,a3,b1,b2,b3]
        map_rel' := by
          intro i j hij
          change (i,j) ∈ hexEdges at hij
          simp only [hexEdges, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hij
          rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          all_goals norm_num
          all_goals first | assumption | exact h12.symm | exact h13.symm |
            exact h21.symm | exact h23.symm | exact h31.symm | exact h32.symm }
    obtain ⟨x, hx⟩ := hd f
    let S : Finset (Fin 6) := univ.filter fun i => G.Adj x (f i)
    have hS : ∀ i ∈ S, ∀ j ∈ S, ¬ Hex.Adj i j := by
      intro i hi j hj hij
      exact hG (mem_filter.mp hi).2 (f.map_adj hij) (mem_filter.mp hj).2
    have hxS (i : Fin 6) (hi : i ∈ S) : G.Adj x (f i) := (mem_filter.mp hi).2
    rcases hex_patterns S hS hx with h | h
    · refine ⟨x, Or.inl ?_⟩
      exact ⟨hxS 0 (h (by decide)), hxS 1 (h (by decide)), hxS 2 (h (by decide))⟩
    · refine ⟨x, Or.inr ?_⟩
      exact ⟨hxS 3 (h (by decide)), hxS 4 (h (by decide)), hxS 5 (h (by decide))⟩

/-- Once the first attachment sees the other two, the second hexagon forces Mycielski's graph. -/
private theorem myc_of_anchor (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd : D2 G)
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 x : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2)
    (ha1 : G.Adj a1 c1) (ha2 : G.Adj a2 c2) (ha3 : G.Adj a3 c3)
    (hb1 : G.Adj b1 c1) (hb2 : G.Adj b2 c2) (hb3 : G.Adj b3 c3)
    (hx1 : G.Adj b1 x) (hx2 : G.Adj b2 x) (hx3 : G.Adj b3 x)
    (hc2 : G.Adj c1 c2) (hc3 : G.Adj c1 c3) : Nonempty (Myc →g G) := by
  all_goals
    obtain ⟨q, hq | hq⟩ := hexagon_triple G hG hd a2 b2 c3 a3 b3 c2
      h23 ha2 h32.symm hb2 ha3.symm hb3.symm
    · exact myc_of_hexagon_configuration G a1 a2 a3 b1 b2 b3 c1 c2 c3 x q
        h12 h13 ha1 h21 h23 ha2 hq.1.symm h31 h32 ha3 hb1 hx1 hb2 hx2 hq.2.1.symm
        hb3 hx3 hc2 hc3 hq.2.2.symm
    · exact myc_of_hexagon_configuration G a1 a3 a2 b1 b3 b2 c1 c3 c2 x q
        h13 h12 ha1 h31 h32 ha3 hq.1.symm h21 h23 ha2 hb1 hx1 hb3 hx3 hq.2.1.symm
        hb2 hx2 hc3 hc2 hq.2.2.symm

/-- The D3 seed supplies an anchor for one of the three matched opposite pairs. -/
private theorem seed_quad (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd : D3 G)
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2)
    (ha1 : G.Adj a1 c1) (ha2 : G.Adj a2 c2) (ha3 : G.Adj a3 c3)
    (hb1 : G.Adj b1 c1) (hb2 : G.Adj b2 c2) (hb3 : G.Adj b3 c3) :
    ∃ t, (G.Adj a1 t ∧ G.Adj b1 t ∧ G.Adj t c2 ∧ G.Adj t c3) ∨
      (G.Adj a2 t ∧ G.Adj b2 t ∧ G.Adj t c1 ∧ G.Adj t c3) ∨
      (G.Adj a3 t ∧ G.Adj b3 t ∧ G.Adj t c1 ∧ G.Adj t c2) := by
  all_goals
    let f : Seed →g G :=
      { toFun := ![a1,a2,a3,b1,b2,b3,c1,c2,c3]
        map_rel' := by
          intro i j hij
          change (i,j) ∈ seedEdges at hij
          simp only [seedEdges, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hij
          rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          all_goals norm_num
          all_goals first | assumption | exact h12.symm | exact h13.symm |
            exact h21.symm | exact h23.symm | exact h31.symm | exact h32.symm |
            exact ha1.symm | exact ha2.symm | exact ha3.symm |
            exact hb1.symm | exact hb2.symm | exact hb3.symm }
    obtain ⟨t, ht⟩ := hd f
    let S : Finset (Fin 9) := univ.filter fun i => G.Adj t (f i)
    have hS : ∀ i ∈ S, ∀ j ∈ S, ¬ Seed.Adj i j := by
      intro i hi j hj hij
      exact hG (mem_filter.mp hi).2 (f.map_adj hij) (mem_filter.mp hj).2
    have htS (i : Fin 9) (hi : i ∈ S) : G.Adj t (f i) := (mem_filter.mp hi).2
    rcases seed_patterns S hS ht with h | h | h
    · exact ⟨t, Or.inl ⟨(htS 0 (h (by decide))).symm, (htS 3 (h (by decide))).symm,
          htS 7 (h (by decide)), htS 8 (h (by decide))⟩⟩
    · exact ⟨t, Or.inr (Or.inl ⟨(htS 1 (h (by decide))).symm, (htS 4 (h (by decide))).symm,
          htS 6 (h (by decide)), htS 8 (h (by decide))⟩)⟩
    · exact ⟨t, Or.inr (Or.inr ⟨(htS 2 (h (by decide))).symm, (htS 5 (h (by decide))).symm,
          htS 6 (h (by decide)), htS 7 (h (by decide))⟩)⟩

/-- A hexagon with no opposite chord forces the Mycielski obstruction. -/
private theorem myc_of_hexagon (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd2 : D2 G) (hd3 : D3 G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (a1 a2 a3 b1 b2 b3 : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2)
    (hn1 : ¬ G.Adj a1 b1) (hn2 : ¬ G.Adj a2 b2) (hn3 : ¬ G.Adj a3 b3)
    (x : V) (hx1 : G.Adj b1 x) (hx2 : G.Adj b2 x) (hx3 : G.Adj b3 x) :
    Nonempty (Myc →g G) := by
  all_goals
    obtain ⟨c1, ha1, hb1⟩ := hc a1 b1 hn1
    obtain ⟨c2, ha2, hb2⟩ := hc a2 b2 hn2
    obtain ⟨c3, ha3, hb3⟩ := hc a3 b3 hn3
    obtain ⟨t, ht | ht | ht⟩ := seed_quad G hG hd3 a1 a2 a3 b1 b2 b3 c1 c2 c3
      h12 h13 h21 h23 h31 h32 ha1 ha2 ha3 hb1 hb2 hb3
    · exact myc_of_anchor G hG hd2 a1 a2 a3 b1 b2 b3 t c2 c3 x
        h12 h13 h21 h23 h31 h32 ht.1 ha2 ha3 ht.2.1 hb2 hb3 hx1 hx2 hx3
        ht.2.2.1 ht.2.2.2
    · exact myc_of_anchor G hG hd2 a2 a1 a3 b2 b1 b3 t c1 c3 x
        h21 h23 h12 h13 h32 h31 ht.1 ha1 ha3 ht.2.1 hb1 hb3 hx2 hx1 hx3
        ht.2.2.1 ht.2.2.2
    · exact myc_of_anchor G hG hd2 a3 a1 a2 b3 b1 b2 t c1 c2 x
        h31 h32 h13 h12 h23 h21 ht.1 ha1 ha2 ht.2.1 hb1 hb2 hx3 hx1 hx2
        ht.2.2.1 ht.2.2.2

/-- Maximal triangle-free graphs with D2 and D3 and no Mycielski image have no induced hexagon. -/
theorem no_hexagon (hG : (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj a c)) (hd2 : D2 G) (hd3 : D3 G)
    (hc : ∀ a b, ¬ G.Adj a b → ∃ r, G.Adj a r ∧ G.Adj b r)
    (hm : ¬ Nonempty (Myc →g G)) : NoHex G := by
  all_goals
    intro a b c d e f hab hbc hcd hde hef hfa
    by_contra hn
    push_neg at hn
    obtain ⟨x, hx | hx⟩ := hexagon_triple G hG hd2 a c e d f b
      hfa.symm hab hcd hbc.symm hde.symm hef
    · exact hm (myc_of_hexagon G hG hd2 hd3 hc d f b a c e
        hcd.symm hde hfa hef.symm hab.symm hbc (fun h => hn.1 h.symm) (fun h => hn.2.2 h.symm) hn.2.1 x
        hx.1.symm hx.2.1.symm hx.2.2.symm)
    · exact hm (myc_of_hexagon G hG hd2 hd3 hc a c e d f b
        hfa.symm hab hcd hbc.symm hde.symm hef hn.1 hn.2.2 (fun h => hn.2.1 h.symm) x
        hx.1.symm hx.2.1.symm hx.2.2.symm)

end HaggHexagon

end D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations
