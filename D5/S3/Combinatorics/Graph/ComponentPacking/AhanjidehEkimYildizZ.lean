/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result; premises=D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.support_independent,D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.independent_support_fits
   digest: The odd-degree extremal matching formula for d at least 21. -/

/-
admission_basis: open-problem-resolution (#19633; Proved)
escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment
Direct frozen dependencies:
  FD1: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.EdgeDisjoint; statement_id: sha256:e0621d80b5258a7670cf151ef794f2095ad3d03e1bac4de398f62415c214f340
  FD2: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.cnt; statement_id: sha256:daa5f847faca0cc75ac950f323e0788dc30826310bb24737edd1385f0af49ca3
  FD3: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingCount; statement_id: sha256:258789cbbcb3edc4325996e0c573029bc6df6732a312a65c87328d9a7d198b3a
  FD4: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingNumber; statement_id: sha256:bc48fae608e0bfa6a8bfa38cfb3ae56515a1a1e764b8141835e629d5b6380311
  FD5: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingsIn; statement_id: sha256:f043c9eef981ed80fbda5d586601e97dd3f30a3821b2b8a32d64bd91b3044fbd
  FD6: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingsIn_eq_empty; statement_id: sha256:6e3d64271bc2e696a5b673dc46b49301e394f50043ba30f3b5cc607ae06192ad
  FD7: D5/S3/Zeros/Convolution/MatchingFiber; Lean name: D5.S3.Zeros.Convolution.MatchingFiber.Matching; statement_id: sha256:5985a336685d711a5801b13ec52b3d5ee14d0dce784d74ec1904eb78c9002586
  FD8: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: _private.D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.0.D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.instDecidableEdgeDisjointOfFintypeOfDecidableEq; statement_id: sha256:952bfdb17a40231ac661e796e06d8c3f298519cca124948548158522043dac66
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20094
ExceptionalSupport.support_independent: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension; Direct frozen dependencies: none
ExceptionalSupport.independent_support_fits: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension; Direct frozen dependencies: none
Z: proof_shape: bind-only; escape_witness: none; consumers: AEYInfimum.Z_eq_of_attainment, claim, result; Direct frozen dependencies: FD4
claim: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: FD4
AEYLowerDense.relabel_edge: proof_shape: bind-only; escape_witness: none; consumers: AEYLowerDense.no_small_dense, ExceptionalLower.no_order_59; Direct frozen dependencies: none
AEYLowerDense.no_small_dense: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map; consumers: AEYLowerDense.lower_or_exception; Direct frozen dependencies: none
AEYLowerDense.lower_or_exception: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map; consumers: ExceptionalLower.lower; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
VertexDeletionBridges.deleted_degree: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension, ExceptionalLower.no_order_59, ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
VertexDeletionBridges.neighbors_independent: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension, ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
VertexDeletionBridges.deleted_neighbor_count: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension, ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
VertexDeletionBridges.extend_hom: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension, ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
IndependentBipartiteSupport.confined_to_one_color: proof_shape: content; escape_witness: IndependentBipartiteSupport.confined_to_one_color; consumers: ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
PentagonIndependentSubset.sum_counts: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension; Direct frozen dependencies: none
PentagonIndependentSubset.adjacent_counts_le_defect: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalHomExtension.extension; Direct frozen dependencies: none
ExceptionalHomExtension.extension: proof_shape: content; escape_witness: ExceptionalHomExtension.extension; consumers: ExceptionalLower.no_order_59; Direct frozen dependencies: none
ExceptionalNonbipartite.no_two_color: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching.PerfectMatchingBipartiteBalance.color_balance; consumers: ExceptionalLower.no_order_59; Direct frozen dependencies: none
ExceptionalLower.doubled_edge: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalLower.surjective; Direct frozen dependencies: none
ExceptionalLower.surjective: proof_shape: bind-only; escape_witness: none; consumers: ExceptionalLower.no_order_59; Direct frozen dependencies: none
ExceptionalLower.no_order_59: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map; consumers: ExceptionalLower.lower; Direct frozen dependencies: none
ExceptionalLower.lower: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map; consumers: AEYInfimum.Z_eq_of_attainment; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
AEYInfimum.Z_eq_of_attainment: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map; consumers: result; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
result: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment; consumers: settling theorem; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
-/

import D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations
import D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism
import D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
import D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction
import D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper
import D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
open D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations
open D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism
open D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
open D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction
open D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper
open D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching

namespace ExceptionalSupport
open Finset

/-- The deficient vertex has neighbors in an independent set of pentagon classes. -/
private theorem support_independent (a w : Fin 5 → ℕ)
    (ha : ∑ i, a i = 6) (hw : ∑ i, w i = 22)
    (hbound : ∀ i, w i ≤ 14 - a (i + 2) - a (i + 3))
    (hlocal : ∀ i, 0 < w i → w (i + 4) + w (i + 1) ≤ a i) :
    ∀ i, w i = 0 ∨ w (i + 1) = 0 := by
  all_goals
    have b0 := hbound 0; have b1 := hbound 1; have b2 := hbound 2
    have b3 := hbound 3; have b4 := hbound 4
    have l0 := hlocal 0; have l1 := hlocal 1; have l2 := hlocal 2
    have l3 := hlocal 3; have l4 := hlocal 4
    norm_num [Fin.sum_univ_succ] at ha hw b0 b1 b2 b3 b4 l0 l1 l2 l3 l4
    intro i
    fin_cases i <;> norm_num <;> omega

/-- An independent subset of the pentagon lies in one vertex's neighbor pair. -/
private theorem independent_support_fits (w : Fin 5 → ℕ)
    (h : ∀ i, w i = 0 ∨ w (i + 1) = 0) :
    ∃ j : Fin 5, ∀ i, 0 < w i → i = j + 4 ∨ i = j + 1 := by
  all_goals
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    have h3 := h 3; have h4 := h 4
    norm_num at h0 h1 h2 h3 h4
    by_cases p0 : 0 < w 0 <;> by_cases p1 : 0 < w 1 <;>
      by_cases p2 : 0 < w 2 <;> by_cases p3 : 0 < w 3 <;>
      by_cases p4 : 0 < w 4
    all_goals first | omega | skip
    all_goals
      first
      | (refine ⟨0, ?_⟩; intro i; fin_cases i <;> norm_num <;> omega)
      | (refine ⟨1, ?_⟩; intro i; fin_cases i <;> norm_num <;> omega)
      | (refine ⟨2, ?_⟩; intro i; fin_cases i <;> norm_num <;> omega)
      | (refine ⟨3, ?_⟩; intro i; fin_cases i <;> norm_num <;> omega)
      | (refine ⟨4, ?_⟩; intro i; fin_cases i <;> norm_num <;> omega)

end ExceptionalSupport

open Classical in
/-- Definition 4.2: `Z(d)` is the smallest natural number `n` such that there exists a `d`-regular (if `d` is even) or
almost `d`-regular (if `d` is odd) triangle-free and factor-critical graph `G` with `ν(G) = n`. -/
noncomputable def Z (d : ℕ) : ℕ :=
  sInf {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    (if Even d then G.IsRegularOfDegree d else IsAlmostRegular G d) ∧ G.CliqueFree 3 ∧
      IsFactorCritical G ∧ matchingNumber G = m}

/-- Conjecture 6.5: for `d ≥ 21` and odd, `Z(d) = ⌊5(d + 1)/4⌋`. -/
def claim : Prop :=
  ∀ d : ℕ, 21 ≤ d → Odd d → Z d = 5 * (d + 1) / 4


set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace AEYLowerDense
open AhanjidehEkimYildizZ HaggLocalConfigurations PentagonDefectCounting PentagonSurjectiveLower
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

/-- The two cyclic labellings of the pentagon differ by multiplication by three. -/
private theorem relabel_edge (i j : Fin 5) (h : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj i j) : (SimpleGraph.cycleGraph 5).Adj (3 * i) (3 * j) := by
  exact SimpleGraph.cycleGraph_adj.mpr h

/-- A triangle-free almost-regular factor-critical graph cannot have the forbidden small order in the dense regime. -/
private theorem no_small_dense {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hd : 21 ≤ d) (hod : Odd d) (htri : G.CliqueFree 3)
    (hfc : IsFactorCritical G) (hr : IsAlmostRegular G d)
    (hN : N ≤ 2 * (5 * (d + 1) / 4) - 1)
    (hdense : 3 * N < 8 * (d - 1)) : False := by
  all_goals
    classical
    obtain ⟨w, hw, hv⟩ := hr
    letI : Nonempty (Fin N) := ⟨w⟩
    have hmin : d - 1 ≤ G.minDegree :=
      G.le_minDegree_of_forall_le_degree _ (fun x => by
        by_cases hx : x = w
        · rw [hx, hw] <;> omega
        · rw [hv x hx]; omega)
    have hdG : 3 * Fintype.card (Fin N) < 8 * G.minDegree := by simp only [Fintype.card_fin]; omega
    obtain ⟨f, hf⟩ := HaggkvistDense.pentagon_hom G htri hdG
    have hedge : ∃ a b, G.Adj a b := by
      obtain ⟨b, hb⟩ := (G.degree_pos_iff_exists_adj w).mp (by omega)
      exact ⟨w,b,hb⟩
    have hn := FactorCriticalNonbipartite.no_two_color G hfc hedge
    have honto := PentagonImage.surjective_of_not_two_color G f hf hn
    let g : Fin N → Fin 5 := fun x => 3 * f x
    have hg : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (g x) (g y) := fun {_ _} h => relabel_edge _ _ (hf h)
    have hgo : Function.Surjective g := by
      intro i
      obtain ⟨x, hx⟩ := honto (2 * i)
      refine ⟨x, ?_⟩
      dsimp [g]
      rw [hx]
      fin_cases i <;> rfl
    have hdeg (x : Fin N) : (G.degree x : ℤ) = d - if x = w then 1 else 0 := by
      by_cases hx : x = w
      · subst x; rw [hw]; simp; omega
      · rw [hv x hx]; simp [hx]
    have hodd := FactorCriticalParity.odd_order G hfc (by have := w.isLt; omega)
    exact no_small_surjective_map G g hg hgo d hd hod (by simpa using hodd)
      (by simpa using hN) w hdeg

/-- Apart from the singled-out degree-23 order, the conjectured lower bound follows. -/
private theorem lower_or_exception {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hd : 21 ≤ d) (hod : Odd d) (htri : G.CliqueFree 3)
    (hfc : IsFactorCritical G) (hr : IsAlmostRegular G d) :
    5 * (d + 1) / 4 ≤ matchingNumber G ∨ (d = 23 ∧ N = 59) := by
  all_goals
    by_cases h : 5 * (d + 1) / 4 ≤ matchingNumber G
    · exact Or.inl h
    · have horder := FactorCriticalOrder.almost_regular_order_eq G hfc hr
      have hN : N ≤ 2 * (5 * (d + 1) / 4) - 1 := by omega
      rcases OrderArithmetic.threshold_or_exception d N hd hod hN with hden | he
      · exact False.elim (no_small_dense G hd hod htri hfc hr hN hden)
      · exact Or.inr he

end AEYLowerDense

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace VertexDeletionBridges
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deleting one vertex removes exactly its incident edge from each remaining degree. -/
private theorem deleted_degree (v : V) (x : ({v}ᶜ : Set V)) :
    (G.induce ({v}ᶜ : Set V)).degree x =
      G.degree x.val - if G.Adj x.val v then 1 else 0 := by
  all_goals
    classical
    have hset : G.neighborFinset x.val ∩ ({v}ᶜ : Set V).toFinset =
        (G.neighborFinset x.val).erase v := by
      ext y
      simp [and_comm]
    have hc := congrArg Finset.card (G.map_neighborFinset_induce
      (s := ({v}ᶜ : Set V)) x)
    simp only [card_map, SimpleGraph.card_neighborFinset_eq_degree] at hc
    rw [hc, hset]
    by_cases h : G.Adj x.val v
    · rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr h),
        G.card_neighborFinset_eq_degree, if_pos h]
    · rw [erase_eq_of_notMem (by simpa using h),
        G.card_neighborFinset_eq_degree, if_neg h, Nat.sub_zero]

/-- In a triangle-free graph, two neighbors of a deleted vertex cannot be adjacent. -/
private theorem neighbors_independent (hG : G.CliqueFree 3) (v x y : V)
    (hx : G.Adj v x) (hy : G.Adj v y) : ¬ G.Adj x y := by
  exact HaggForbidden.triangle_free_of_clique_free G hG
    (id (SimpleGraph.adj_symm G hx)) hy

/-- The surviving vertices adjacent to the deleted vertex are exactly its original neighborhood. -/
private theorem deleted_neighbor_count (v : V) :
    (univ.filter fun x : ({v}ᶜ : Set V) => G.Adj v x.val).card = G.degree v := by
  all_goals
    classical
    let S : Finset ({v}ᶜ : Set V) := univ.filter fun x => G.Adj v x.val
    have himage : S.image Subtype.val = G.neighborFinset v := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hy).2
      · intro hx
        have hvx := (G.mem_neighborFinset _ _).mp hx
        have hne : x ≠ v := hvx.ne.symm
        exact mem_image.mpr ⟨⟨x, by simpa using hne⟩,
          mem_filter.mpr ⟨mem_univ _, hvx⟩, rfl⟩
    change S.card = _
    rw [← card_image_of_injective S Subtype.val_injective,
      himage, G.card_neighborFinset_eq_degree]

/-- A homomorphism after vertex deletion extends whenever the deleted neighborhood fits one target neighborhood. -/
private theorem extend_hom {W : Type*} (H : SimpleGraph W) (v : V)
    (f : (G.induce ({v}ᶜ : Set V)) →g H) (a : W)
    (hfit : ∀ x : ({v}ᶜ : Set V), G.Adj v x.val → H.Adj a (f x)) :
    Nonempty (G →g H) := by
  all_goals
    classical
    let g : V → W := fun x => if hx : x = v then a else f ⟨x, by simpa using hx⟩
    refine ⟨{toFun := g, map_rel' := ?_}⟩
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y ≠ v := hxy.ne.symm
      simpa only [g, dif_pos rfl, dif_neg hy] using hfit ⟨y, by simpa using hy⟩ hxy
    · by_cases hy : y = v
      · subst y
        simpa only [g, dif_neg hx, dif_pos rfl] using
          (hfit ⟨x, by simpa using hx⟩ hxy.symm).symm
      · simpa only [g, dif_neg hx, dif_neg hy] using
          f.map_adj (show (G.induce ({v}ᶜ : Set V)).Adj
            ⟨x, by simpa using hx⟩ ⟨y, by simpa using hy⟩ from hxy)

end VertexDeletionBridges

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace IndependentBipartiteSupport
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An independent set meeting both sides of a dense balanced bipartite graph has size at most twice the omission bound. -/
private theorem confined_to_one_color (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (P : V → Prop) [DecidablePred P]
    (hP : ∀ x y, P x → P y → ¬ G.Adj x y)
    (b δ : ℕ) (hparts : ∀ i, (univ.filter fun x => c x = i).card = b)
    (hmin : ∀ x, δ ≤ G.degree x)
    (hlarge : 2 * (b - δ) < (univ.filter P).card) :
    ∃ i : Fin 2, ∀ x, P x → c x = i := by
  all_goals
    classical
    let W (i : Fin 2) := univ.filter fun x => c x = i ∧ P x
    have hbound (x : V) (hx : P x) (i : Fin 2) (hi : c x ≠ i) :
        δ + (W i).card ≤ b := by
      have hd : Disjoint (G.neighborFinset x) (W i) := by
        apply disjoint_left.mpr
        intro y hxy hy
        exact hP x y hx (mem_filter.mp hy).2.2 ((G.mem_neighborFinset _ _).mp hxy)
      have hsub : G.neighborFinset x ∪ W i ⊆ univ.filter fun y => c y = i := by
        intro y hy
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rcases mem_union.mp hy with hxy | hy
        · have hne := hc ((G.mem_neighborFinset _ _).mp hxy)
          omega
        · exact (mem_filter.mp hy).2.1
      have hcard := card_le_card hsub
      rw [card_union_of_disjoint hd, G.card_neighborFinset_eq_degree, hparts i] at hcard
      exact (Nat.add_le_add_right (hmin x) _).trans hcard
    by_cases h0 : ∃ x, P x ∧ c x = 0
    · by_cases h1 : ∃ x, P x ∧ c x = 1
      · obtain ⟨x, hx, hx0⟩ := h0
        obtain ⟨y, hy, hy1⟩ := h1
        have hb0 := hbound y hy 0 (by simp [hy1])
        have hb1 := hbound x hx 1 (by simp [hx0])
        have hsplit : (W 0).card + (W 1).card = (univ.filter P).card := by
          have hpartition : W 0 ∪ W 1 = univ.filter P := by
            ext z
            have hz : c z = 0 ∨ c z = 1 := by omega
            simp only [W, mem_union, mem_filter, mem_univ, true_and]
            tauto
          have hdis : Disjoint (W 0) (W 1) := by
            apply disjoint_left.mpr
            intro z hz0 hz1
            have ha := (mem_filter.mp hz0).2.1
            have hb := (mem_filter.mp hz1).2.1
            omega
          rw [← card_union_of_disjoint hdis, hpartition]
        omega
      · refine ⟨0, ?_⟩
        intro x hx
        have hnx : c x ≠ 1 := fun h => h1 ⟨x,hx,h⟩
        omega
    · refine ⟨1, ?_⟩
      intro x hx
      have hnx : c x ≠ 0 := fun h => h0 ⟨x,hx,h⟩
      omega

end IndependentBipartiteSupport

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace PentagonIndependentSubset
open Finset PentagonDefectCounting PentagonClassObstruction
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The counts of an independently selected subset partition its cardinality. -/
private theorem sum_counts (f : V → Fin 5) (P : V → Prop) [DecidablePred P] :
    ∑ i, (univ.filter fun x => f x = i ∧ P x).card = (univ.filter P).card := by
  classical
  simpa [Finset.filter_filter, and_comm] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ f)

/-- A selected vertex cannot see any other selected vertex in a triangle-free neighborhood. -/
private theorem adjacent_counts_le_defect (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin 5) (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y))
    (P : V → Prop) [DecidablePred P]
    (hindependent : ∀ x y, P x → P y → ¬ G.Adj x y)
    (x : V) (hx : P x) :
    ((univ.filter fun y => f y = f x + 4 ∧ P y).card : ℤ) +
      (univ.filter fun y => f y = f x + 1 ∧ P y).card ≤
      (NeighborTotal (ClassSize f) (f x) : ℤ) - G.degree x := by
  all_goals
    classical
    have hne : f x + 4 ≠ f x + 1 :=
      (by decide : ∀ i : Fin 5, i + 4 ≠ i + 1) (f x)
    have hpoint (y : V) :
        (if f y = f x + 4 ∧ P y then (1 : ℤ) else 0) +
        (if f y = f x + 1 ∧ P y then 1 else 0) ≤ DefectWeight G f x y := by
      by_cases hy : P y
      · have hnon := hindependent x y hx hy
        by_cases h4 : f y = f x + 4 <;> by_cases h1 : f y = f x + 1
        all_goals first
          | exact False.elim (hne (h4.symm.trans h1))
          | simp [DefectWeight, cycle_five_adjacency, hy, hnon, h4, h1]
      · have hn : 0 ≤ DefectWeight G f x y := by
          unfold DefectWeight
          split_ifs <;> norm_num
        simpa [hy] using hn
    have hsum := sum_le_sum (fun y (_ : y ∈ univ) => hpoint y)
    rw [sum_add_distrib, defect_row G f hf x] at hsum
    simpa [NeighborTotal, Finset.sum_filter] using hsum

end PentagonIndependentSubset

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ExceptionalHomExtension
open Finset PentagonDefectCounting PentagonClassDegrees PentagonClassObstruction
open PentagonIndependentSubset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At degree 23 and order 59, every surjective pentagon map after deleting the deficient vertex extends. -/
private theorem extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (horder : Fintype.card V = 59) (htri : G.CliqueFree 3)
    (hdef : G.degree v = 22) (hregular : ∀ x, x ≠ v → G.degree x = 23)
    (f : ({v}ᶜ : Set V) → Fin 5)
    (hf : ∀ ⦃x y : ({v}ᶜ : Set V)⦄,
      (G.induce ({v}ᶜ : Set V)).Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y))
    (honto : Function.Surjective f) :
    ∃ g : V → Fin 5, ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (g x) (g y) := by
  all_goals
    classical
    let H := G.induce ({v}ᶜ : Set V)
    let P : ({v}ᶜ : Set V) → Prop := fun x => G.Adj v x.val
    let s := ClassSize f
    let a : Fin 5 → ℕ := fun i => NeighborTotal s i - 22
    let w : Fin 5 → ℕ := fun i => (univ.filter fun x => f x = i ∧ P x).card
    have hcard : Fintype.card ({v}ᶜ : Set V) = 58 := by
      change Fintype.card {x : V // ¬ x = v} = 58
      rw [Fintype.card_subtype_compl]
      simp [horder]
    have hdegrees (x : ({v}ᶜ : Set V)) : H.degree x = 23 - if P x then 1 else 0 := by
      have hh := VertexDeletionBridges.deleted_degree G v x
      rw [hregular x.val (by exact x.2)] at hh
      simpa only [H, P, G.adj_comm] using hh
    have hmin (x : ({v}ᶜ : Set V)) : 22 ≤ H.degree x := by
      rw [hdegrees]
      split_ifs <;> norm_num
    have ht (i : Fin 5) : 22 ≤ NeighborTotal s i := by
      obtain ⟨x, hx⟩ := honto i
      have hh := degree_le_permitted H f hf x
      simpa only [s, NeighborTotal, hx] using (hmin x).trans hh
    have htotals (i : Fin 5) : NeighborTotal s i = 22 + a i := by
      have hh := ht i
      dsimp [a]
      omega
    have hsumS : ∑ i, s i = 58 := by simpa only [s, hcard] using sum_class_sizes f
    have ht0 := htotals 0; have ht1 := htotals 1; have ht2 := htotals 2
    have ht3 := htotals 3; have ht4 := htotals 4
    have hsumS' := hsumS
    norm_num [NeighborTotal, Fin.sum_univ_succ] at ht0 ht1 ht2 ht3 ht4 hsumS'
    have hsumA : ∑ i, a i = 6 := by
      norm_num [Fin.sum_univ_succ]
      omega
    have hsize (i : Fin 5) : s i = 14 - a (i + 2) - a (i + 3) := by
      have hp := htotals (i + 2)
      have hq := htotals (i + 3)
      fin_cases i <;> norm_num [NeighborTotal] at hp hq ⊢ <;> omega
    have hsumW : ∑ i, w i = 22 := by
      have hh := sum_counts f P
      have hn := VertexDeletionBridges.deleted_neighbor_count G v
      simpa only [w, P, hn, hdef] using hh
    have hbound (i : Fin 5) : w i ≤ 14 - a (i + 2) - a (i + 3) := by
      rw [← hsize]
      apply card_le_card
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.1⟩
    have hindependent : ∀ x y : ({v}ᶜ : Set V), P x → P y → ¬ H.Adj x y := by
      intro x y hx hy hxy
      exact VertexDeletionBridges.neighbors_independent G htri v x.val y.val hx hy hxy
    have hlocal (i : Fin 5) (hi : 0 < w i) : w (i + 4) + w (i + 1) ≤ a i := by
      obtain ⟨x, hx⟩ := card_pos.mp hi
      have hlabel := (mem_filter.mp hx).2.1
      have hPx : P x := (mem_filter.mp hx).2.2
      have hh := adjacent_counts_le_defect H f hf P hindependent x hPx
      have hd : H.degree x = 22 := by simp [hdegrees, hPx]
      rw [hlabel, hd] at hh
      change (w (i + 4) : ℤ) + w (i + 1) ≤ (NeighborTotal s i : ℤ) - 22 at hh
      rw [htotals i] at hh
      push_cast at hh
      omega
    have hsupport := ExceptionalSupport.support_independent a w hsumA hsumW hbound hlocal
    obtain ⟨j, hj⟩ := ExceptionalSupport.independent_support_fits w hsupport
    let fH : H →g (SimpleGraph.cycleGraph 5) := {toFun := f, map_rel' := fun h => hf h}
    have hfit (x : ({v}ᶜ : Set V)) (hx : G.Adj v x.val) : (SimpleGraph.cycleGraph 5).Adj j (fH x) := by
      have hpos : 0 < w (f x) := card_pos.mpr
        ⟨x, mem_filter.mpr ⟨mem_univ _, rfl, hx⟩⟩
      exact (cycle_five_adjacency _ _).mpr (hj (f x) hpos)
    obtain ⟨g⟩ := VertexDeletionBridges.extend_hom G (SimpleGraph.cycleGraph 5) v fH j hfit
    exact ⟨g, fun {_ _} h => g.map_adj h⟩

end ExceptionalHomExtension

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ExceptionalNonbipartite
open Finset AhanjidehEkimYildizZ

/-- In the degree-23 exception, deleting the deficient vertex leaves a nonbipartite graph. -/
private theorem no_two_color {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (horder : N = 59) (htri : G.CliqueFree 3) (hfc : IsFactorCritical G)
    (v : Fin N) (hdef : G.degree v = 22)
    (hregular : ∀ x, x ≠ v → G.degree x = 23) :
    ¬ ∃ c : ({v}ᶜ : Set (Fin N)) → Fin 2,
      ∀ ⦃x y⦄, (G.induce ({v}ᶜ : Set (Fin N))).Adj x y → c x ≠ c y := by
  all_goals
    classical
    rintro ⟨c, hc⟩
    let H := G.induce ({v}ᶜ : Set (Fin N))
    let P : ({v}ᶜ : Set (Fin N)) → Prop := fun x => G.Adj v x.val
    obtain ⟨M, hM⟩ := hfc v
    have hbalance := PerfectMatchingBipartiteBalance.color_balance H M hM c hc
    simp only [Fintype.card_subtype] at hbalance
    have hcard : Fintype.card ({v}ᶜ : Set (Fin N)) = 58 := by
      change Fintype.card {x : Fin N // ¬ x = v} = 58
      rw [Fintype.card_subtype_compl]
      simp [horder]
    have hsplit := card_filter_add_card_filter_not
      (s := (univ : Finset ({v}ᶜ : Set (Fin N)))) (fun x => c x = 0)
    have hone : (univ.filter fun x => ¬ c x = 0) = (univ.filter fun x => c x = 1) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      omega
    rw [hone, card_univ, hcard] at hsplit
    have hp0 : (univ.filter fun x => c x = 0).card = 29 := by
      omega
    have hp1 : (univ.filter fun x => c x = 1).card = 29 := by omega
    have hparts (i : Fin 2) : (univ.filter fun x => c x = i).card = 29 := by
      fin_cases i
      · exact hp0
      · exact hp1
    have hmin (x : ({v}ᶜ : Set (Fin N))) : 22 ≤ H.degree x := by
      have hh := VertexDeletionBridges.deleted_degree G v x
      rw [hregular x.val (by exact x.2)] at hh
      change 22 ≤ (G.induce ({v}ᶜ : Set (Fin N))).degree x
      split_ifs at hh <;> omega
    have hindependent : ∀ x y, P x → P y → ¬ H.Adj x y := by
      intro x y hx hy hxy
      exact VertexDeletionBridges.neighbors_independent G htri v x.val y.val hx hy hxy
    have hsize : (univ.filter P).card = 22 := by
      simpa only [P, hdef] using VertexDeletionBridges.deleted_neighbor_count G v
    obtain ⟨i, hi⟩ := IndependentBipartiteSupport.confined_to_one_color H c hc P
      hindependent 29 22 hparts hmin (by rw [hsize]; norm_num)
    let fH : H →g (⊤ : SimpleGraph (Fin 2)) :=
      {toFun := c, map_rel' := fun h => (SimpleGraph.top_adj _ _).mpr (hc h)}
    have hfit (x : ({v}ᶜ : Set (Fin N))) (hx : G.Adj v x.val) :
        (⊤ : SimpleGraph (Fin 2)).Adj (i + 1) (fH x) := by
      apply (SimpleGraph.top_adj _ _).mpr
      change i + 1 ≠ c x
      rw [hi x hx]
      fin_cases i <;> decide
    obtain ⟨g⟩ := VertexDeletionBridges.extend_hom G ⊤ v fH (i + 1) hfit
    have hedge : ∃ a b, G.Adj a b := by
      obtain ⟨b,hb⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
      exact ⟨v,b,hb⟩
    exact FactorCriticalNonbipartite.no_two_color G hfc hedge
      ⟨g, fun {_ _} h => (SimpleGraph.top_adj _ _).mp (g.map_adj h)⟩

end ExceptionalNonbipartite

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ExceptionalLower
open AhanjidehEkimYildizZ HaggLocalConfigurations PentagonDefectCounting
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

/-- Doubling the ±1 coordinates recovers the ±2 labeling. -/
private theorem doubled_edge (i j : Fin 5) (h : (SimpleGraph.cycleGraph 5).Adj i j) : ((SimpleGraph.cycleGraph 5).comap (fun i : Fin 5 => 3 * i)).Adj (2 * i) (2 * j) := by
  change (SimpleGraph.cycleGraph 5).Adj (3 * (2 * i)) (3 * (2 * j))
  simpa only [← mul_assoc, show (3 : Fin 5) * 2 = 1 from rfl, one_mul] using h

/-- Every cyclic pentagon map from a nonbipartite graph is onto. -/
private theorem surjective (G : SimpleGraph (Fin N)) (f : Fin N → Fin 5)
    (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y))
    (hn : ¬ ∃ c : Fin N → Fin 2, ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    Function.Surjective f := by
  all_goals
    have honto := PentagonImage.surjective_of_not_two_color G (fun x => 2 * f x)
      (fun {_ _} h => doubled_edge _ _ (hf h)) hn
    have hinj : Function.Injective (fun i : Fin 5 => 2 * i) := by decide
    intro i
    obtain ⟨x, hx⟩ := honto (2 * i)
    exact ⟨x, hinj hx⟩

/-- The exceptional order 59 cannot occur at degree 23. -/
private theorem no_order_59 (G : SimpleGraph (Fin 59)) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hfc : IsFactorCritical G) (hr : IsAlmostRegular G 23) : False := by
  all_goals
    classical
    obtain ⟨v,hv,hreg⟩ := hr
    norm_num at hv
    let H := G.induce ({v}ᶜ : Set (Fin 59))
    have hcard : Fintype.card ({v}ᶜ : Set (Fin 59)) = 58 := by
      change Fintype.card {x : Fin 59 // ¬ x = v} = 58
      rw [Fintype.card_subtype_compl]
      simp
    have hmin (x : ({v}ᶜ : Set (Fin 59))) : 22 ≤ H.degree x := by
      have hh := VertexDeletionBridges.deleted_degree G v x
      rw [hreg x.val (by exact x.2)] at hh
      change 22 ≤ (G.induce ({v}ᶜ : Set (Fin 59))).degree x
      split_ifs at hh <;> omega
    letI : Nonempty ({v}ᶜ : Set (Fin 59)) := Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
    have hdelta : 22 ≤ H.minDegree := H.le_minDegree_of_forall_le_degree _ hmin
    have hdense : 3 * Fintype.card ({v}ᶜ : Set (Fin 59)) < 8 * H.minDegree := by
      rw [hcard]
      omega
    have htriH : H.CliqueFree 3 :=
      (G.cliqueFree_induce_iff _ 3).mpr htri.cliqueFreeOn
    obtain ⟨f,hf⟩ := HaggkvistDense.pentagon_hom H htriH hdense
    have hn := ExceptionalNonbipartite.no_two_color G rfl htri hfc v hv hreg
    have honto := PentagonImage.surjective_of_not_two_color H f hf hn
    let f' : ({v}ᶜ : Set (Fin 59)) → Fin 5 := fun x => 3 * f x
    have hf' : ∀ ⦃x y⦄, H.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f' x) (f' y) :=
      fun {_ _} h => AEYLowerDense.relabel_edge _ _ (hf h)
    have honto' : Function.Surjective f' := by
      intro i
      obtain ⟨x,hx⟩ := honto (2 * i)
      refine ⟨x, ?_⟩
      dsimp [f']
      rw [hx]
      fin_cases i <;> rfl
    obtain ⟨g,hg⟩ := ExceptionalHomExtension.extension G v (by simp) htri hv hreg f' hf' honto'
    have hedge : ∃ a b, G.Adj a b := by
      obtain ⟨b,hb⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
      exact ⟨v,b,hb⟩
    have hnG := FactorCriticalNonbipartite.no_two_color G hfc hedge
    have hgo := surjective G g hg hnG
    have hdegrees (x : Fin 59) : (G.degree x : ℤ) = 23 - if x = v then 1 else 0 := by
      by_cases hx : x = v
      · subst x; simp [hv]
      · simp [hreg x hx, hx]
    exact PentagonSurjectiveLower.no_small_surjective_map G g hg hgo 23
      (by norm_num) (by decide) (by decide) (by norm_num) v hdegrees

/-- Every graph admissible for an odd degree at least 21 has at least the conjectured matching number. -/
private theorem lower {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hd : 21 ≤ d) (hod : Odd d) (htri : G.CliqueFree 3)
    (hfc : IsFactorCritical G) (hr : IsAlmostRegular G d) :
    5 * (d + 1) / 4 ≤ matchingNumber G := by
  all_goals
    rcases AEYLowerDense.lower_or_exception G hd hod htri hfc hr with h | ⟨rfl,rfl⟩
    · exact h
    · exact False.elim (no_order_59 G htri hfc hr)

end ExceptionalLower

namespace AEYInfimum
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

/-- A graph attaining the proposed value combines with the universal lower bound in the binding infimum definition. -/
private theorem Z_eq_of_attainment {d N : ℕ} (hd : 21 ≤ d) (hod : Odd d)
    (G : SimpleGraph (Fin N)) [hdec : DecidableRel G.Adj]
    (hr : IsAlmostRegular G d) (htri : G.CliqueFree 3) (hfc : IsFactorCritical G)
    (hmatching : matchingNumber G = 5 * (d + 1) / 4) :
    Z d = 5 * (d + 1) / 4 := by
  all_goals
    classical
    have hne : ¬ Even d := Nat.not_even_iff_odd.mpr hod
    have hrC : @IsAlmostRegular N G (fun a b => Classical.propDecidable (G.Adj a b)) d := by
      have he : hdec = (fun a b => Classical.propDecidable (G.Adj a b)) :=
        Subsingleton.elim _ _
      exact Eq.mp (congrArg (fun q : DecidableRel G.Adj => @IsAlmostRegular N G q d) he) hr
    let S : Set ℕ := {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (if Even d then G.IsRegularOfDegree d else IsAlmostRegular G d) ∧ G.CliqueFree 3 ∧
        IsFactorCritical G ∧ matchingNumber G = m}
    have hmem : 5 * (d + 1) / 4 ∈ S :=
      ⟨N,G,by simpa only [if_neg hne] using hrC,htri,hfc,hmatching⟩
    have hmin : sInf S ∈ S := Nat.sInf_mem ⟨_,hmem⟩
    obtain ⟨n,H,hreg,htriH,hfcH,hmatchingH⟩ := hmin
    have hrH : IsAlmostRegular H d := by simpa only [if_neg hne] using hreg
    have hlo := ExceptionalLower.lower H hd hod htriH hfcH hrH
    rw [hmatchingH] at hlo
    exact le_antisymm (Nat.sInf_le hmem) hlo

end AEYInfimum


set_option maxHeartbeats 1000000

/-- Ahanjideh–Ekim–Yıldız Conjecture 6.5 in the unchanged binding conventions. -/
theorem result : claim := by
  all_goals
    classical
    intro d hd hod
    let k := d / 4
    have hk : 5 ≤ k := by dsimp [k]; omega
    have hres : d = 4 * k + 1 ∨ d = 4 * k + 3 := by
      rcases hod with ⟨m,hm⟩
      dsimp [k]
      omega
    rcases hres with h | h
    · obtain ⟨N,G,hr,htri,hfc,hm⟩ := AEYUpperAttainment.attainment false k hk
      simp only [Bool.false_eq_true, if_false] at hr hm
      rw [← h] at hr hm
      exact AEYInfimum.Z_eq_of_attainment hd hod G hr htri hfc hm
    · obtain ⟨N,G,hr,htri,hfc,hm⟩ := AEYUpperAttainment.attainment true k hk
      simp only [if_true] at hr hm
      rw [← h] at hr hm
      exact AEYInfimum.Z_eq_of_attainment hd hod G hr htri hfc hm


end D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ
