/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factor-critical parity and the finite matching-number interface. -/

/-
admission_basis: escape-witness: DenseBalancedHall.exists_equiv_of_omission_bound
escape_witness: D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching.PerfectMatchingBipartiteBalance.color_balance
Direct frozen dependencies:
  FD1: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.EdgeDisjoint; statement_id: sha256:e0621d80b5258a7670cf151ef794f2095ad3d03e1bac4de398f62415c214f340
  FD2: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.cnt; statement_id: sha256:daa5f847faca0cc75ac950f323e0788dc30826310bb24737edd1385f0af49ca3
  FD3: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingCount; statement_id: sha256:258789cbbcb3edc4325996e0c573029bc6df6732a312a65c87328d9a7d198b3a
  FD4: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingNumber; statement_id: sha256:bc48fae608e0bfa6a8bfa38cfb3ae56515a1a1e764b8141835e629d5b6380311
  FD5: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingsIn; statement_id: sha256:f043c9eef981ed80fbda5d586601e97dd3f30a3821b2b8a32d64bd91b3044fbd
  FD6: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.matchingsIn_eq_empty; statement_id: sha256:6e3d64271bc2e696a5b673dc46b49301e394f50043ba30f3b5cc607ae06192ad
  FD7: D5/S3/Zeros/Convolution/MatchingFiber; Lean name: D5.S3.Zeros.Convolution.MatchingFiber.Matching; statement_id: sha256:5985a336685d711a5801b13ec52b3d5ee14d0dce784d74ec1904eb78c9002586
  FD8: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation; Lean name: _private.D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.0.D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.instDecidableEdgeDisjointOfFintypeOfDecidableEq; statement_id: sha256:952bfdb17a40231ac661e796e06d8c3f298519cca124948548158522043dac66
Utility none: the matching, parity and Hall arguments are uniform in the finite carriers; no finite certificate or enumeration settles a fixed instance.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20094
IsAlmostRegular: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYInfimum.Z_eq_of_attainment, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.lower_or_exception, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.lower, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.Z, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.result, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment, FactorCriticalOrder.almost_regular_order_eq; Direct frozen dependencies: none
IsFactorCritical: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYInfimum.Z_eq_of_attainment, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.lower_or_exception, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.lower, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalNonbipartite.no_two_color, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.Z, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.result, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment, FactorCriticalNonbipartite.no_two_color, FactorCriticalOrder.almost_regular_order_eq, FactorCriticalOrder.order_eq, FactorCriticalParity.odd_order; Direct frozen dependencies: none
FactorCriticalParity.odd_order: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, FactorCriticalOrder.order_eq; Direct frozen dependencies: none
MatchingCountBridge.matchingCount_eq_cnt: proof_shape: bind-only; escape_witness: none; consumers: MatchingCountBridge.matchingCount_eq_zero_of_card_lt, MatchingCountBridge.matchingCount_pos_of_matching, MatchingCountBridge.matchingNumber_le; Direct frozen dependencies: FD1, FD2, FD3, FD5, FD8, FD7
MatchingCountBridge.matchingCount_eq_zero_of_card_lt: proof_shape: bind-only; escape_witness: none; consumers: MatchingCountBridge.le_matchingNumber_of_pos, MatchingCountBridge.matchingNumber_le; Direct frozen dependencies: FD1, FD2, FD3, FD5, FD6, FD8, FD7
MatchingCountBridge.matchingNumber_le: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalOrder.order_eq; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
MatchingCountBridge.matchingCount_pos_of_matching: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalOrder.order_eq; Direct frozen dependencies: FD1, FD2, FD3, FD5, FD8, FD7
MatchingCountBridge.matching_card_vertices: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalOrder.order_eq; Direct frozen dependencies: none
MatchingCountBridge.le_matchingNumber_of_pos: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalOrder.order_eq; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
FactorCriticalOrder.order_eq: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalOrder.almost_regular_order_eq; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
FactorCriticalOrder.almost_regular_order_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.lower_or_exception, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
DenseBalancedHall.exists_equiv_of_omission_bound: proof_shape: content; escape_witness: DenseBalancedHall.exists_equiv_of_omission_bound; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.PentagonPairMatching.exists_perfect_matching; Direct frozen dependencies: none
PerfectMatchingBipartiteBalance.color_balance: proof_shape: content; escape_witness: PerfectMatchingBipartiteBalance.color_balance; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalNonbipartite.no_two_color, FactorCriticalNonbipartite.no_two_color; Direct frozen dependencies: none
PerfectMatchingBipartiteBalance.deleted_color_count: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper.AEYConstructionProperties.deleted_class_size, FactorCriticalNonbipartite.no_two_color; Direct frozen dependencies: none
FactorCriticalNonbipartite.no_two_color: proof_shape: content; escape_witness: PerfectMatchingBipartiteBalance.color_balance; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.AEYLowerDense.no_small_dense, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalLower.no_order_59, D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.ExceptionalNonbipartite.no_two_color; Direct frozen dependencies: none
-/

import D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
import D5.S3.Zeros.Convolution.MatchingFiber
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching


def IsAlmostRegular {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∃ w, G.degree w = d - 1 ∧ ∀ v, v ≠ w → G.degree v = d

/-- Section 2: `G` is factor-critical if `G \ v` has a perfect matching for all `v ∈ V(G)`. -/
def IsFactorCritical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, ∃ M : (G.induce ({v}ᶜ : Set (Fin n))).Subgraph, M.IsPerfectMatching


namespace FactorCriticalParity

/-- Deleting any vertex from a nonempty factor-critical graph shows that its order is odd. -/
theorem odd_order {N : ℕ} (G : SimpleGraph (Fin N)) (hG : IsFactorCritical G)
    (hne : 0 < N) : Odd N := by
  all_goals
    classical
    let v : Fin N := ⟨0, hne⟩
    obtain ⟨M, hM⟩ := hG v
    have he := hM.even_card
    have hc : Fintype.card ({v}ᶜ : Set (Fin N)) = N - 1 := by
      change Fintype.card {x : Fin N // ¬ x = v} = N - 1
      rw [Fintype.card_subtype_compl]
      simp
    rw [hc] at he
    rcases he with ⟨k, hk⟩
    exact ⟨k, by omega⟩


end FactorCriticalParity
namespace MatchingCountBridge
open Classical
open Finset
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
/-- The frozen matching count equals the owner's finite matching enumeration for every graph. -/
private theorem matchingCount_eq_cnt {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : ℕ) : matchingCount G i = cnt G.edgeFinset i := by
  all_goals
    classical
    have hdis : ∀ e f : Sym2 (Fin n), Disjoint e.toFinset f.toFinset ↔ EdgeDisjoint e f := by
      intro e f
      unfold EdgeDisjoint
      simp only [Finset.disjoint_left, Sym2.mem_toFinset]
    have hiff : ∀ M : Finset (Sym2 (Fin n)), M ∈ matchingsIn G.edgeFinset i ↔
        (M.card = i ∧ (∀ e ∈ M, ¬ e.IsDiag) ∧
          (M : Set (Sym2 (Fin n))).Pairwise (fun e f => Disjoint e.toFinset f.toFinset)) ∧
        ∀ e ∈ M, e ∈ G.edgeSet := by
      intro M
      unfold matchingsIn
      simp only [mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hc⟩, hp⟩
        refine ⟨⟨hc, fun e he => G.not_isDiag_of_mem_edgeSet
          (SimpleGraph.mem_edgeFinset.mp (hsub he)), fun e he f hf hef => (hdis e f).mpr
          (hp e (mem_coe.mp he) f (mem_coe.mp hf) hef)⟩,
          fun e he => SimpleGraph.mem_edgeFinset.mp (hsub he)⟩
      · rintro ⟨⟨hc, -, hp⟩, hE⟩
        exact ⟨⟨fun e he => SimpleGraph.mem_edgeFinset.mpr (hE e he), hc⟩,
          fun e he f hf hef => (hdis e f).mp (hp (mem_coe.mpr he) (mem_coe.mpr hf) hef)⟩
    unfold matchingCount D5.S3.Zeros.Convolution.MatchingFiber.Matching
    unfold cnt
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr
      { toFun := fun M => ⟨M.1.1, (hiff M.1.1).mpr ⟨M.1.2, M.2⟩⟩
        invFun := fun S => ⟨⟨S.1, ((hiff S.1).mp S.2).1⟩, ((hiff S.1).mp S.2).2⟩
        left_inv := fun M => rfl
        right_inv := fun S => rfl }

/-- No matching can cover more vertices than the graph has. -/
private theorem matchingCount_eq_zero_of_card_lt {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : ℕ) (hi : n < 2 * i) : matchingCount G i = 0 := by
  all_goals
    have hz : matchingsIn G.edgeFinset i = ∅ :=
      matchingsIn_eq_empty _ univ (by simp)
        (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)) i
        (by simpa using hi)
    rw [matchingCount_eq_cnt]
    unfold cnt
    rw [hz, Finset.card_empty]

/-- The binding matching number is at most half the graph's order. -/
private theorem matchingNumber_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    matchingNumber G ≤ n / 2 := by
  all_goals
    unfold matchingNumber
    apply csSup_le
    · refine ⟨0, ?_⟩
      change 0 < matchingCount G 0
      rw [matchingCount_eq_cnt]
      unfold cnt
      have hempty : (∅ : Finset (Sym2 (Fin n))) ∈ matchingsIn G.edgeFinset 0 := by
        unfold matchingsIn
        simp
      exact Finset.card_pos.mpr ⟨_, hempty⟩
    · intro i hi
      by_contra hn
      have hni : n < 2 * i := by omega
      have hz := matchingCount_eq_zero_of_card_lt G i hni
      simp [hz] at hi

/-- A Mathlib subgraph matching is a positive term of the binding matching-count sequence. -/
private theorem matchingCount_pos_of_matching {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) :
    0 < matchingCount G M.spanningCoe.edgeFinset.card := by
  all_goals
    classical
    have hsub : M.spanningCoe.edgeFinset ⊆ G.edgeFinset := by
      intro e he
      apply SimpleGraph.mem_edgeFinset.mpr
      have hh := SimpleGraph.mem_edgeFinset.mp he
      exact SimpleGraph.edgeSet_mono M.spanningCoe_le hh
    have hpair : ∀ e ∈ M.spanningCoe.edgeFinset, ∀ f ∈ M.spanningCoe.edgeFinset,
        e ≠ f → EdgeDisjoint e f := by
      intro e he f hf hef v hve hvf
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hvf
      have he' : M.Adj v w := SimpleGraph.mem_edgeFinset.mp he
      have hf' : M.Adj v u := SimpleGraph.mem_edgeFinset.mp hf
      exact hef (congrArg (fun z => s(v,z)) (hM.eq_of_adj_left he' hf'))
    rw [matchingCount_eq_cnt]
    unfold cnt
    apply Finset.card_pos.mpr
    refine ⟨M.spanningCoe.edgeFinset, ?_⟩
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, rfl⟩, hpair⟩

/-- The number of edges in a subgraph matching is half its vertex count. -/
private theorem matching_card_vertices {n : ℕ} (G : SimpleGraph (Fin n))
    (M : G.Subgraph) (hM : M.IsMatching) :
    2 * M.spanningCoe.edgeFinset.card = M.verts.toFinset.card := by
  all_goals
    classical
    have hdegree (v : Fin n) : M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
      rw [SimpleGraph.Subgraph.degree_spanningCoe]
      by_cases hv : v ∈ M.verts
      · simpa [hv] using (SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hM v hv)
      · simpa [hv] using SimpleGraph.Subgraph.degree_of_notMem_verts (G' := M) hv
    rw [← M.spanningCoe.sum_degrees_eq_twice_card_edges]
    simp only [hdegree]
    simp

/-- Every positive term is bounded by the binding supremum. -/
private theorem le_matchingNumber_of_pos {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : ℕ) (hi : 0 < matchingCount G i) : i ≤ matchingNumber G := by
  all_goals
    unfold matchingNumber
    apply le_csSup
    · refine ⟨n / 2, ?_⟩
      intro k hk
      by_contra hn
      have hz := matchingCount_eq_zero_of_card_lt G k (by omega)
      simp [hz] at hk
    · exact hi

end MatchingCountBridge
namespace FactorCriticalOrder
open MatchingCountBridge
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

/-- For nonempty factor-critical graphs, order is twice the binding matching number plus one. -/
private theorem order_eq {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : IsFactorCritical G) (hne : 0 < N) : N = 2 * matchingNumber G + 1 := by
  all_goals
    classical
    let v : Fin N := ⟨0, hne⟩
    obtain ⟨M, hM⟩ := hG v
    let f : G.induce ({v}ᶜ : Set (Fin N)) →g G :=
      { toFun := Subtype.val, map_rel' := fun h => h }
    let L : G.Subgraph := M.map f
    have hL : L.IsMatching := SimpleGraph.Subgraph.IsMatching.map f Subtype.val_injective hM.1
    have hverts : L.verts = ({v}ᶜ : Set (Fin N)) := by
      change f '' M.verts = _
      rw [hM.2.verts_eq_univ]
      ext x
      constructor
      · rintro ⟨y,hy,hyx⟩
        change y.val = x at hyx
        subst x
        exact y.2
      · intro hx
        exact ⟨⟨x,hx⟩,Set.mem_univ _,rfl⟩
    have hcount := matching_card_vertices G L hL
    rw [hverts] at hcount
    simp only [Set.toFinset_compl, Set.toFinset_singleton, Finset.card_compl,
      Fintype.card_fin, Finset.card_singleton] at hcount
    have hlo := le_matchingNumber_of_pos G _ (matchingCount_pos_of_matching G L hL)
    have hhi := matchingNumber_le G
    have hp := FactorCriticalParity.odd_order G hG hne
    rcases hp with ⟨k, hk⟩
    omega

/-- An almost-regular factor-critical graph is nonempty, so the order bridge applies. -/
theorem almost_regular_order_eq {N d : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : IsFactorCritical G) (hr : IsAlmostRegular G d) : N = 2 * matchingNumber G + 1 := by
  all_goals
    obtain ⟨v, _⟩ := hr
    exact order_eq G hG (by have := v.isLt; omega)

end FactorCriticalOrder
namespace DenseBalancedHall
open Finset Function
variable {A B : Type*} [Fintype A] [Fintype B]

/-- A balanced relation with at most r omissions in each row and column has a transversal if 2r≤n. -/
theorem exists_equiv_of_omission_bound (R : A → B → Prop) [DecidableRel R]
    (r : ℕ) (hcard : Fintype.card A = Fintype.card B)
    (hn : 2 * r ≤ Fintype.card B)
    (hrow : ∀ a, (univ.filter fun b => ¬ R a b).card ≤ r)
    (hcol : ∀ b, (univ.filter fun a => ¬ R a b).card ≤ r) :
    ∃ f : A ≃ B, ∀ a, R a (f a) := by
  all_goals
    classical
    have hHall : ∀ S : Finset A, S.card ≤ (univ.filter fun b => ∃ a ∈ S, R a b).card := by
      intro S
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha⟩ := hS
        by_cases hsmall : S.card ≤ Fintype.card B - r
        · have hsplit := card_filter_add_card_filter_not (s := (univ : Finset B)) (p := R a)
          change (univ.filter fun b : B => R a b).card +
            (univ.filter fun b : B => ¬ R a b).card = Fintype.card B at hsplit
          have hsub : (univ.filter fun b => R a b) ⊆ (univ.filter fun b => ∃ a ∈ S, R a b) := by
            intro b hb
            exact mem_filter.mpr ⟨mem_univ b, a, ha, (mem_filter.mp hb).2⟩
          have hle := card_le_card hsub
          have hrowa := hrow a
          have hneigh : Fintype.card B - r ≤ (univ.filter fun b : B => R a b).card := by omega
          exact hsmall.trans (hneigh.trans hle)
        · have hrS : r < S.card := by omega
          have hfull : (univ.filter fun b => ∃ a ∈ S, R a b) = univ := by
            apply filter_eq_self.mpr
            intro b _
            by_contra hb
            push_neg at hb
            have hsub : S ⊆ (univ.filter fun a => ¬ R a b) := by
              intro a ha
              exact mem_filter.mpr ⟨mem_univ a, hb a ha⟩
            have hle := (card_le_card hsub).trans (hcol b)
            omega
          rw [hfull, card_univ, ← hcard]
          exact card_le_univ S
      · simpa only [not_nonempty_iff_eq_empty.mp hS, card_empty] using
          Nat.zero_le (univ.filter fun b => ∃ a ∈ S, R a b).card
    obtain ⟨f, hf, hRf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hHall
    have hs : Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩ |>.2
    exact ⟨Equiv.ofBijective f ⟨hf, hs⟩, hRf⟩

end DenseBalancedHall
namespace PerfectMatchingBipartiteBalance
open Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- A perfect matching gives equal cardinalities to the two classes of any proper two-coloring. -/
theorem color_balance (M : G.Subgraph) (hM : M.IsPerfectMatching)
    (c : V → Fin 2) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    Fintype.card {x // c x = 0} = Fintype.card {x // c x = 1} := by
  all_goals
    classical
    have hall := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
    choose p hp hu using hall
    have hinv (x : V) : p (p x) = x := (hu (p x) x (hp x).symm).symm
    have hcol (x : V) : c x ≠ c (p x) := hc (M.adj_sub (hp x))
    let e : {x // c x = 0} ≃ {x // c x = 1} :=
      { toFun := fun x => ⟨p x, by
          have hh := hcol x
          have hx := x.2
          have hb := (c (p x)).isLt
          omega⟩
        invFun := fun x => ⟨p x, by
          have hh := hcol x
          have hx := x.2
          have hb := (c (p x)).isLt
          omega⟩
        left_inv := fun x => Subtype.ext (hinv x)
        right_inv := fun x => Subtype.ext (hinv x) }
    exact Fintype.card_congr e

/-- Counting a color class after deleting v removes one exactly when v has that color. -/
theorem deleted_color_count [DecidableEq V] {C : Type*} [DecidableEq C]
    (c : V → C) (i : C) (v : V) :
    Fintype.card {x : ({v}ᶜ : Set V) // c x = i} =
      (univ.filter fun x : V => c x = i).card - if c v = i then 1 else 0 := by
  all_goals
    classical
    have he : Fintype.card {x : ({v}ᶜ : Set V) // c x = i} =
        (univ.filter fun x : V => c x = i ∧ x ≠ v).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine
        { toFun := fun x => ⟨x.1.1, mem_filter.mpr ⟨mem_univ _,x.2,x.1.2⟩⟩
          invFun := fun x => ⟨⟨x.1, by simpa using (mem_filter.mp x.2).2.2⟩, (mem_filter.mp x.2).2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [he]
    have herase : (univ.filter fun x : V => c x = i ∧ x ≠ v) =
        (univ.filter fun x : V => c x = i).erase v := by ext x; simp [and_comm, and_left_comm]
    rw [herase, Finset.card_erase_eq_ite]
    by_cases hcv : c v = i <;> simp [hcv]

end PerfectMatchingBipartiteBalance
namespace FactorCriticalNonbipartite
open PerfectMatchingBipartiteBalance
open Finset

/-- A factor-critical graph containing an edge admits no proper two-coloring. -/
theorem no_two_color {N : ℕ} (G : SimpleGraph (Fin N))
    (hG : IsFactorCritical G) (ha : ∃ a b, G.Adj a b) :
    ¬ ∃ c : Fin N → Fin 2, ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by
  all_goals
    classical
    rintro ⟨c, hc⟩
    obtain ⟨a, b, hab⟩ := ha
    have hne := hc hab
    have hbal (v : Fin N) :
        (univ.filter fun x : Fin N => c x = 0).card - (if c v = 0 then 1 else 0) =
        (univ.filter fun x : Fin N => c x = 1).card - (if c v = 1 then 1 else 0) := by
      obtain ⟨M, hM⟩ := hG v
      have hh := color_balance (G.induce ({v}ᶜ : Set (Fin N))) M hM
        (fun x => c x.1) (fun {_ _} h => hc h)
      simpa only [deleted_color_count] using hh
    have ha0 : c a = 0 ∨ c a = 1 := by omega
    have hb0 : c b = 0 ∨ c b = 1 := by omega
    have hlefta : 0 < (univ.filter fun x : Fin N => c x = c a).card :=
      card_pos.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    have hleftb : 0 < (univ.filter fun x : Fin N => c x = c b).card :=
      card_pos.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    have hba := hbal a
    have hbb := hbal b
    rcases ha0 with ha0 | ha0 <;> rcases hb0 with hb0 | hb0
    all_goals simp only [ha0, hb0, Fin.reduceEq, if_true, if_false, Nat.sub_zero] at hne hba hbb hlefta hleftb
    all_goals try contradiction
    all_goals omega

end FactorCriticalNonbipartite

end D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
