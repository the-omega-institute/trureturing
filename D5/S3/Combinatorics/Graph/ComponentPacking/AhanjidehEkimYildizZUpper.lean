/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.attainment; premises=D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.split_sizes,D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.degree_small,D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.degree_large
   digest: Almost-regular factor-critical pentagon graphs attain the upper bound. -/

/-
admission_basis: escape-witness: AEYUpperAttainment.attainment
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
PentagonPairSizes.BaseSize: proof_shape: bind-only; escape_witness: none; consumers: AEYConstructionProperties.class_size, AEYConstructionProperties.deleted_class_size, AEYUpperAbstract.allowed_le_degree_add_two, PentagonPairSizes.RemainingSize, PentagonPairSizes.split_sizes; Direct frozen dependencies: none
PentagonPairSizes.RemainingSize: proof_shape: bind-only; escape_witness: none; consumers: AEYConstructionProperties.deleted_class_size, AEYUpperAbstract.factor_critical, PentagonPairSizes.split_sizes; Direct frozen dependencies: none
PentagonPairSizes.PairSize: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.factor_critical, PentagonPairSizes.split_sizes; Direct frozen dependencies: none
PentagonPairSizes.split_sizes: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.factor_critical; Direct frozen dependencies: none
PairMatchingAssembly.exists_perfect_matching_of_pairs: proof_shape: bind-only; escape_witness: none; consumers: PentagonPairMatching.exists_perfect_matching; Direct frozen dependencies: none
PentagonPairMatching.restricted_count_le: proof_shape: bind-only; escape_witness: none; consumers: PentagonPairMatching.exists_perfect_matching; Direct frozen dependencies: none
PentagonPairMatching.exists_perfect_matching: proof_shape: content; escape_witness: PentagonPairMatching.exists_perfect_matching; consumers: AEYUpperAbstract.factor_critical; Direct frozen dependencies: none
AEYConstruction.BagSize: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.B, AEYConstruction.Deleted, AEYConstruction.instDecidableAdjB, AEYConstruction.instDecidableDeleted, AEYConstruction.order, AEYConstruction.triangle_free, AEYConstructionProperties.class_map_adj, AEYConstructionProperties.class_size, AEYConstructionProperties.deleted_class_size, AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAbstract.class_omissions, AEYUpperAbstract.factor_critical, AEYUpperAttainment.attainment, ConstructionRows.degree_bag_sum, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.BagClass: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.B, AEYConstruction.instDecidableAdjB, AEYConstruction.triangle_free, AEYConstructionProperties.class_map_adj, AEYConstructionProperties.class_size, AEYConstructionProperties.deleted_class_size, AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAbstract.class_omissions, AEYUpperAbstract.factor_critical, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.PairedBags: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.B, AEYConstruction.Deleted, AEYConstruction.instDecidableDeleted, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.Deleted: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.B, AEYConstruction.instDecidableAdjB, AEYConstruction.instDecidableDeleted, AEYConstruction.triangle_free, AEYConstructionProperties.class_map_adj, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.instDecidableDeleted: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.instDecidableAdjB; Direct frozen dependencies: none
AEYConstruction.B: proof_shape: bind-only; escape_witness: none; consumers: AEYConstruction.instDecidableAdjB, AEYConstruction.triangle_free, AEYConstructionProperties.class_map_adj, AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAbstract.class_omissions, AEYUpperAbstract.factor_critical, AEYUpperAttainment.attainment, ConstructionRows.degree_bag_sum, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.instDecidableAdjB: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAbstract.class_omissions, AEYUpperAbstract.factor_critical, AEYUpperAttainment.attainment, ConstructionRows.degree_bag_sum, ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
AEYConstruction.order: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAttainment.attainment; Direct frozen dependencies: none
AEYConstruction.triangle_free: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAttainment.attainment; Direct frozen dependencies: none
ConstructionRows.count_equal: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.count_unequal; Direct frozen dependencies: none
ConstructionRows.count_unequal: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.count_unequal_left; Direct frozen dependencies: none
ConstructionRows.count_unequal_left: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
ConstructionRows.degree_bag_sum: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.degree_large, ConstructionRows.degree_small; Direct frozen dependencies: none
ConstructionRows.count_avoid_two: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.count_forward_avoiding, ConstructionRows.count_reverse_avoiding; Direct frozen dependencies: none
ConstructionRows.count_forward_avoiding: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.degree_large; Direct frozen dependencies: none
ConstructionRows.count_reverse_avoiding: proof_shape: bind-only; escape_witness: none; consumers: ConstructionRows.degree_large; Direct frozen dependencies: none
ConstructionRows.degree_small: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAttainment.attainment; Direct frozen dependencies: none
ConstructionRows.degree_large: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.allowed_le_degree_add_two, AEYUpperAttainment.attainment; Direct frozen dependencies: none
AEYConstructionProperties.class_size: proof_shape: bind-only; escape_witness: none; consumers: AEYConstructionProperties.deleted_class_size, AEYUpperAbstract.allowed_le_degree_add_two; Direct frozen dependencies: none
AEYConstructionProperties.class_map_adj: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.class_omissions; Direct frozen dependencies: none
AEYConstructionProperties.deleted_class_size: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.factor_critical; Direct frozen dependencies: none
GraphOmissionBound.class_missing_le: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.class_omissions; Direct frozen dependencies: none
GraphOmissionBound.deleted_class_missing_le: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.factor_critical; Direct frozen dependencies: none
AEYUpperAbstract.allowed_le_degree_add_two: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.class_omissions; Direct frozen dependencies: none
AEYUpperAbstract.class_omissions: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAbstract.factor_critical; Direct frozen dependencies: none
AEYUpperAbstract.factor_critical: proof_shape: content; escape_witness: PentagonPairMatching.exists_perfect_matching; consumers: AEYUpperAttainment.attainment; Direct frozen dependencies: none
FactorCriticalTransport.perfect_matching_map: proof_shape: bind-only; escape_witness: none; consumers: FactorCriticalTransport.factor_critical; Direct frozen dependencies: none
FactorCriticalTransport.factor_critical: proof_shape: bind-only; escape_witness: none; consumers: AEYUpperAttainment.attainment; Direct frozen dependencies: none
AEYUpperAttainment.attainment: proof_shape: content; escape_witness: AEYUpperAttainment.attainment; consumers: D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.result; Direct frozen dependencies: FD1, FD2, FD3, FD4, FD5, FD6, FD8, FD7
-/

import D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
import D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction
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

namespace D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper
open D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching
open D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction
open PentagonDefectCounting
open D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching

namespace PentagonPairSizes
open Finset

private def BaseSize (large : Bool) (k : ℕ) (i : Fin 5) : ℕ :=
  2 * k + 1 + if large then (![0,1,2,2,1] : Fin 5 → ℕ) i else 0

private def RemainingSize (large : Bool) (k : ℕ) (deleted i : Fin 5) : ℕ :=
  BaseSize large k i - if i = deleted then 1 else 0

private def PairSize (s : Fin 5 → ℕ) (i : Fin 5) : ℕ :=
  (s i + s (i + 1) + s (i + 3) - (s (i + 2) + s (i + 4))) / 2

/-- Uniform adjacent-pair partitions survive deletion of a vertex from either B_d size pattern. -/
private theorem split_sizes (large : Bool) (k : ℕ) (hk : 5 ≤ k) (deleted i : Fin 5) :
    let s := RemainingSize large k deleted
    PairSize s (i + 4) + PairSize s i = s i ∧
    k ≤ PairSize s i ∧ PairSize s i ≤ k + 2 := by
  all_goals
    cases large <;> fin_cases deleted <;> fin_cases i <;>
      norm_num [RemainingSize, BaseSize, PairSize] <;> omega


end PentagonPairSizes


set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PairMatchingAssembly
open Set
variable {V ι : Type*} (G : SimpleGraph V)

/-- Disjoint matched pairs of vertex sets covering the graph assemble to a perfect matching. -/
private theorem exists_perfect_matching_of_pairs (S T : ι → Set V)
    (hwithin : ∀ i, Disjoint (S i) (T i))
    (hbetween : Pairwise fun i j => Disjoint (S i ∪ T i) (S j ∪ T j))
    (hcover : ∀ x : V, ∃ i, x ∈ S i ∪ T i)
    (e : ∀ i, S i ≃ T i) (he : ∀ i (x : S i), G.Adj x (e i x)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  all_goals
    classical
    have hpieces : ∀ i, ∃ M : G.Subgraph,
        M.verts = S i ∪ T i ∧ M.IsMatching := by
      intro i
      exact SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
        (hwithin i) (e i) (he i)
    choose M hverts hmatching using hpieces
    refine ⟨⨆ i, M i, ?_, ?_⟩
    · apply SimpleGraph.Subgraph.IsMatching.iSup hmatching
      intro i j hij
      rw [(hmatching i).support_eq_verts, (hmatching j).support_eq_verts,
        hverts i, hverts j]
      exact hbetween hij
    · intro x
      obtain ⟨i, hi⟩ := hcover x
      rw [SimpleGraph.Subgraph.verts_iSup]
      exact Set.mem_iUnion.mpr ⟨i, by rwa [hverts i]⟩

end PairMatchingAssembly

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace PentagonPairMatching
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting a finite predicate to a smaller set cannot increase its count. -/
private theorem restricted_count_le (S T : Finset V) (hST : S ⊆ T)
    (p : V → Prop) [DecidablePred p] :
    (univ.filter fun x : S => p x.val).card ≤ (T.filter p).card := by
  all_goals
    classical
    apply card_le_card_of_injOn (fun x : S => x.val)
    · intro x hx
      exact mem_filter.mpr ⟨hST x.2, (mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy

/-- A nearly complete cyclic blow-up has a perfect matching whenever its class sizes admit large balanced pair allocations. -/
private theorem exists_perfect_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin 5) (r : Fin 5 → ℕ)
    (hsizes : ∀ i, (univ.filter fun x => f x = i).card = r (i + 4) + r i)
    (hr : ∀ i, 4 ≤ r i)
    (hmiss : ∀ x : V, ∀ j : Fin 5, (j = f x + 4 ∨ j = f x + 1) →
      (univ.filter fun y => f y = j ∧ ¬ G.Adj x y).card ≤ 2) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  all_goals
    classical
    let A (i : Fin 5) : Finset V := univ.filter fun x => f x = i
    have hex (i : Fin 5) : ∃ L : Finset V, L ⊆ A i ∧ L.card = r (i + 4) :=
      exists_subset_card_eq (by rw [show (A i).card = _ from hsizes i]; omega)
    choose L hLA hLc using hex
    let R (i : Fin 5) : Finset V := A i \ L i
    have hlabelL {i : Fin 5} {x : V} (hx : x ∈ L i) : f x = i :=
      (mem_filter.mp (hLA i hx)).2
    have hlabelR {i : Fin 5} {x : V} (hx : x ∈ R i) : f x = i :=
      (mem_filter.mp (mem_sdiff.mp hx).1).2
    have hRc (i : Fin 5) : (R i).card = r i := by
      dsimp [R]
      rw [card_sdiff_of_subset (hLA i), hLc i,
        show (A i).card = _ from hsizes i]
      omega
    have hnextprev (i : Fin 5) : i + 1 + 4 = i := by exact add_eq_of_eq_add_neg rfl
    have hprevnext (i : Fin 5) : i + 4 + 1 = i := by exact add_eq_of_eq_add_neg rfl
    have he (i : Fin 5) : ∃ e : (R i : Set V) ≃ (L (i + 1) : Set V),
        ∀ x, G.Adj x.val (e x).val := by
      apply DenseBalancedHall.exists_equiv_of_omission_bound
        (fun (x : (R i : Set V)) (y : (L (i + 1) : Set V)) => G.Adj x.val y.val) 2
      · simp only [Finset.coe_sort_coe, Fintype.card_coe, hRc, hLc, hnextprev]
      · simpa only [Finset.coe_sort_coe, Fintype.card_coe, hLc, hnextprev] using hr i
      · intro x
        have hsub : L (i + 1) ⊆ A (i + 1) := hLA _
        have hcount := restricted_count_le (L (i + 1)) (A (i + 1)) hsub
          (fun y => ¬ G.Adj x.val y)
        have heq : (A (i + 1)).filter (fun y => ¬ G.Adj x.val y) =
            univ.filter (fun y => f y = i + 1 ∧ ¬ G.Adj x.val y) := by
          exact filter_filter (fun x => f x = i + 1) (fun y => ¬ G.Adj x.val y) univ
        rw [heq] at hcount
        exact hcount.trans (hmiss x.val (i + 1) (Or.inr (by rw [hlabelR x.2])))
      · intro y
        have hsub : R i ⊆ A i := sdiff_subset
        have hcount := restricted_count_le (R i) (A i) hsub
          (fun x => ¬ G.Adj x y.val)
        have heq : (A i).filter (fun x => ¬ G.Adj x y.val) =
            univ.filter (fun x => f x = i ∧ ¬ G.Adj y.val x) := by
          ext x; simp [A, G.adj_comm, and_assoc]
        rw [heq] at hcount
        exact hcount.trans (hmiss y.val i (Or.inl (by rw [hlabelL y.2, hnextprev])))
    choose e he using he
    apply PairMatchingAssembly.exists_perfect_matching_of_pairs G
      (fun i => (R i : Set V)) (fun i => (L (i + 1) : Set V)) ?_ ?_ ?_ e he
    · intro i
      apply Set.disjoint_left.mpr
      intro x hxR hxL
      have hlabel := (hlabelR hxR).symm.trans (hlabelL hxL)
      have hne : i ≠ i + 1 := by fin_cases i <;> decide
      exact hne hlabel
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro x hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hij ((hlabelR hx).symm.trans (hlabelR hy))
      · have hlabel := (hlabelR hx).symm.trans (hlabelL hy)
        have hh := (mem_sdiff.mp hx).2
        exact hh (hlabel.symm ▸ hy)
      · have hlabel := (hlabelL hx).symm.trans (hlabelR hy)
        have hh := (mem_sdiff.mp hy).2
        exact hh (hlabel ▸ hx)
      · exact hij (add_right_cancel ((hlabelL hx).symm.trans (hlabelL hy)))
    · intro x
      by_cases hx : x ∈ L (f x)
      · refine ⟨f x + 4, Or.inr ?_⟩
        change x ∈ L (f x + 4 + 1)
        simpa only [hprevnext] using hx
      · exact ⟨f x, Or.inl (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, rfl⟩, hx⟩)⟩

end PentagonPairMatching
namespace AEYConstruction
open Finset

private abbrev BagSize (large : Bool) (k : ℕ) (b : Fin 13) : ℕ :=
  match b.val with
  | 0 | 3 | 6 => 1
  | 5 | 8 | 9 | 11 => if large then k + 1 else k
  | 10 | 12 => if large then k + 2 else k + 1
  | _ => k

private def BagClass : Fin 13 → Fin 5 := ![0,0,0,4,4,4,1,1,1,3,3,2,2]



private def PairedBags : Finset (Fin 13 × Fin 13) :=
  {(0,3),(0,6),(1,4),(2,7),(5,9),(8,11),(10,12)}

private def Deleted (large : Bool) (k : ℕ) (x y : (Σ b : Fin 13, Fin (BagSize large k b))) : Prop :=
  (((x.1,y.1) ∈ PairedBags ∨ (y.1,x.1) ∈ PairedBags) ∧ x.2.val = y.2.val) ∨
  (large = true ∧
    (((x.1 = 9 ∧ y.1 = 11) ∨ (y.1 = 9 ∧ x.1 = 11)) ∧ x.2.val = y.2.val)) ∨
  (large = true ∧
    ((x.1 = 10 ∧ y.1 = 12 ∧ y.2.val = (x.2.val + 1) % (k + 2)) ∨
      (y.1 = 10 ∧ x.1 = 12 ∧ x.2.val = (y.2.val + 1) % (k + 2))))
private instance instDecidableDeleted (large : Bool) (k : ℕ) : DecidableRel (Deleted large k) := by
  intro x y
  unfold Deleted
  infer_instance

private def B (large : Bool) (k : ℕ) : SimpleGraph ((Σ b : Fin 13, Fin (BagSize large k b))) where
  Adj x y := (SimpleGraph.cycleGraph 5).Adj (BagClass x.1) (BagClass y.1) ∧ ¬ Deleted large k x y
  symm := ⟨by
    intro x y hxy
    constructor
    · exact hxy.1.symm
    · intro hyx
      apply hxy.2
      unfold Deleted at hyx ⊢
      have heq : x.2.val = y.2.val ↔ y.2.val = x.2.val := eq_comm
      tauto⟩
  loopless := ⟨by
    intro x hx
    exact (SimpleGraph.cycleGraph 5).irrefl hx.1⟩
private instance instDecidableAdjB (large : Bool) (k : ℕ) : DecidableRel (B large k).Adj := by
  intro x y
  change Decidable ((SimpleGraph.cycleGraph 5).Adj (BagClass x.1) (BagClass y.1) ∧ ¬ Deleted large k x y)
  infer_instance

/-- The exact Figure-2 reconstruction has the claimed uniform order. -/
private theorem order (large : Bool) (k : ℕ) :
    Fintype.card ((Σ b : Fin 13, Fin (BagSize large k b))) = 2 * (5 * ((4 * k + if large then 3 else 1) + 1) / 4) + 1 := by
  all_goals
    change Fintype.card (Sigma _) = _
    rw [Fintype.card_sigma]
    cases large <;> norm_num [BagSize, Fin.sum_univ_succ] <;> omega

/-- Triangle-freeness follows from the five cyclic classes, independently of the deleted matchings. -/
private theorem triangle_free (large : Bool) (k : ℕ) : (B large k).CliqueFree 3 := by
  all_goals
    classical
    intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    have htf : ∀ i j l : Fin 5, (SimpleGraph.cycleGraph 5).Adj i j → (SimpleGraph.cycleGraph 5).Adj j l → ¬ (SimpleGraph.cycleGraph 5).Adj i l := by decide
    exact htf _ _ _ hab.1 hbc.1 hac.1

end AEYConstruction

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000


set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ConstructionRows
open Finset AEYConstruction
open Classical

/-- A bounded natural value occurs exactly once in a finite interval. -/
private theorem count_equal (n a : ℕ) :
    (univ.filter fun x : Fin n => x.val = a).card = if a < n then 1 else 0 := by
  all_goals
    by_cases h : a < n
    · have heq : (univ.filter fun x : Fin n => x.val = a) = {⟨a,h⟩} := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hx; exact Fin.ext hx
        · intro hx; exact congrArg Fin.val hx
      simp [heq, h]
    · have heq : (univ.filter fun x : Fin n => x.val = a) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro x _ hx
        exact h (hx ▸ x.isLt)
      simp [heq, h]

/-- Excluding one value subtracts one exactly when that value lies in the interval. -/
private theorem count_unequal (n a : ℕ) :
    (univ.filter fun x : Fin n => x.val ≠ a).card = n - if a < n then 1 else 0 := by
  all_goals
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun x => x.val = a)
    rw [card_univ, Fintype.card_fin] at hc
    change (univ.filter fun x : Fin n => x.val = a).card +
      (univ.filter fun x : Fin n => x.val ≠ a).card = n at hc
    rw [count_equal] at hc
    omega

/-- The same one-position omission with the fixed endpoint written first. -/
private theorem count_unequal_left (n a : ℕ) :
    (univ.filter fun x : Fin n => ¬ a = x.val).card = n - if a < n then 1 else 0 := by
  all_goals simpa only [ne_comm] using count_unequal n a

/-- Each row of the thirteen-bag graph counts separately over its target bags. -/
private theorem degree_bag_sum (large : Bool) (k : ℕ) (x : (Σ b : Fin 13, Fin (BagSize large k b))) :
    (B large k).degree x = ∑ b : Fin 13,
      (univ.filter fun y : Fin (BagSize large k b) => (B large k).Adj x ⟨b,y⟩).card := by
  classical
  simpa [← Finset.filter_sigma, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using
    (Finset.card_sigma (univ : Finset (Fin 13))
      (fun b => univ.filter fun y : Fin (BagSize large k b) => (B large k).Adj x ⟨b,y⟩))

/-- Two distinct omitted positions remove exactly two entries of a finite interval. -/
private theorem count_avoid_two (n a b : ℕ) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (univ.filter fun y : Fin n => y.val ≠ a ∧ y.val ≠ b).card = n - 2 := by
  all_goals
    have hne : (⟨a,ha⟩ : Fin n) ≠ ⟨b,hb⟩ := fun h => hab (congrArg Fin.val h)
    have heq : (univ.filter fun y : Fin n => y.val ≠ a ∧ y.val ≠ b) =
        univ \ {⟨a,ha⟩,⟨b,hb⟩} := by
      ext y
      simp [Fin.ext_iff, not_or, and_comm]
    rw [heq, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_pair hne]

/-- The diagonal and cyclic successor matching have disjoint positions when n≥2. -/
private theorem count_forward_avoiding (n : ℕ) (hn : 2 ≤ n) (x : Fin n) :
    (univ.filter fun y : Fin n =>
      ¬ x.val = y.val ∧ ¬ y.val = (x.val + 1) % n).card = n - 2 := by
  all_goals
    have hb : (x.val + 1) % n < n := Nat.mod_lt _ (by omega)
    have hne : x.val ≠ (x.val + 1) % n := by
      by_cases h : x.val + 1 < n
      · rw [Nat.mod_eq_of_lt h]
        omega
      · have he : x.val + 1 = n := by have := x.isLt; omega
        rw [he, Nat.mod_self]
        have := x.isLt
        omega
    simpa only [not_or, ne_comm] using
      count_avoid_two n x.val ((x.val + 1) % n) x.isLt hb hne

/-- The same two matching omissions have the same count from their other endpoint. -/
private theorem count_reverse_avoiding (n : ℕ) (hn : 2 ≤ n) (x : Fin n) :
    (univ.filter fun y : Fin n =>
      ¬ x.val = y.val ∧ ¬ x.val = (y.val + 1) % n).card = n - 2 := by
  all_goals
    let b := if x.val = 0 then n - 1 else x.val - 1
    have hb : b < n := by dsimp [b]; split_ifs <;> have := x.isLt <;> omega
    have hne : x.val ≠ b := by dsimp [b]; split_ifs <;> have := x.isLt <;> omega
    have hinverse (y : Fin n) : x.val = (y.val + 1) % n ↔ y.val = b := by
      by_cases hy : y.val + 1 < n
      · rw [Nat.mod_eq_of_lt hy]
        dsimp [b]
        split_ifs <;> have := x.isLt <;> have := y.isLt <;> omega
      · have he : y.val + 1 = n := by have := y.isLt; omega
        rw [he, Nat.mod_self]
        dsimp [b]
        split_ifs <;> have := x.isLt <;> have := y.isLt <;> omega
    have heq : (univ.filter fun y : Fin n =>
        ¬ x.val = y.val ∧ ¬ x.val = (y.val + 1) % n) =
        univ.filter (fun y : Fin n => y.val ≠ x.val ∧ y.val ≠ b) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, not_or, hinverse, ne_comm]
    rw [heq]
    exact count_avoid_two n x.val b x.isLt hb hne

/-- In the residue class d=4k+1, only the singleton first bag has the deficient degree. -/
private theorem degree_small (k : ℕ) (hk : 5 ≤ k) (x : (Σ b : Fin 13, Fin (BagSize false k b))) :
    (B false k).degree x = 4 * k + 1 - if x.1 = 0 then 1 else 0 := by
  all_goals
    rcases x with ⟨b,x⟩
    fin_cases b
    all_goals dsimp only
    all_goals rw [degree_bag_sum]
    all_goals have hx := x.isLt
    all_goals norm_num [BagSize] at hx
    all_goals
      simp [B, cycle_five_adjacency, BagClass, Deleted, PairedBags, BagSize,
        Fin.sum_univ_succ, count_unequal, count_unequal_left, ne_comm, hx,
        show 0 < k from by omega]
    all_goals try simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin]
    all_goals omega


end ConstructionRows

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ConstructionRows
open Finset AEYConstruction Classical
/-- The additional two shifted matchings produce the same unique deficiency for d=4k+3. -/
private theorem degree_large (k : ℕ) (hk : 5 ≤ k) (x : (Σ b : Fin 13, Fin (BagSize true k b))) :
    (B true k).degree x = 4 * k + 3 - if x.1 = 0 then 1 else 0 := by
  all_goals
    rcases x with ⟨b,x⟩
    fin_cases b
    all_goals dsimp only
    all_goals rw [degree_bag_sum]
    all_goals have hx := x.isLt
    all_goals norm_num [BagSize] at hx
    all_goals
      have hn : 2 ≤ k + 2 := by exact Nat.le_add_left 2 k
      have hforward (z : Fin (k + 2)) :
          (univ.filter fun y : Fin (k + 2) =>
            ¬ z.val = y.val ∧ ¬ y.val = (z.val + 1) % (k + 2)).card = k := by
        simpa [Nat.add_sub_cancel] using count_forward_avoiding (k + 2) hn z
      have hreverse (z : Fin (k + 2)) :
          (univ.filter fun y : Fin (k + 2) =>
            ¬ z.val = y.val ∧ ¬ z.val = (y.val + 1) % (k + 2)).card = k := by
        simpa [Nat.add_sub_cancel] using count_reverse_avoiding (k + 2) hn z
      have hmod (z : Fin (k + 2)) : (z.val + 1) % (k + 2) < k + 2 :=
        Nat.mod_lt _ (by omega)
      simp [B, cycle_five_adjacency, BagClass, Deleted, PairedBags, BagSize,
        Fin.sum_univ_succ, count_unequal, count_unequal_left,
        count_forward_avoiding, count_reverse_avoiding, hforward, hreverse,
        hmod, ne_comm, hx]
    all_goals try simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin]
    all_goals try omega
    · change 1 + (k + (k + 1 + (k + 1 +
        (univ.filter fun y : Fin (k + 2) =>
          ¬ x.val = y.val ∧ ¬ y.val = (x.val + 1) % (k + 2)).card))) = 4 * k + 3
      rw [hforward ⟨x.val, hx⟩]
      omega
    · change 1 + (k + (k + 1 + (k + 1 +
        (univ.filter fun y : Fin (k + 2) =>
          ¬ x.val = y.val ∧ ¬ x.val = (y.val + 1) % (k + 2)).card))) = 4 * k + 3
      rw [hreverse ⟨x.val, hx⟩]
      omega


end ConstructionRows

namespace AEYConstructionProperties
open Finset AEYConstruction PentagonDefectCounting PentagonPairSizes


/-- The thirteen named bags have the five cyclic class sizes used in the matching partition. -/
private theorem class_size (large : Bool) (k : ℕ) (i : Fin 5) :
    ClassSize ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) i = BaseSize large k i := by
  all_goals
    classical
    simp only [ClassSize, card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_sigma]
    cases large <;> fin_cases i <;>
      norm_num [BagClass, BagSize, BaseSize, Fin.sum_univ_succ] <;> omega

/-- The class map is a homomorphism to cyclic pentagon adjacency. -/
private theorem class_map_adj (large : Bool) (k : ℕ) {x y : (Σ b : Fin 13, Fin (BagSize large k b))}
    (h : (B large k).Adj x y) : (SimpleGraph.cycleGraph 5).Adj ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x) ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) y) := by
  all_goals exact h.1

/-- Vertex deletion subtracts one from precisely its own cyclic class. -/
private theorem deleted_class_size (large : Bool) (k : ℕ) (v : (Σ b : Fin 13, Fin (BagSize large k b))) (i : Fin 5) :
    ClassSize (fun x : ({v}ᶜ : Set ((Σ b : Fin 13, Fin (BagSize large k b)))) => (fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x.val) i =
      RemainingSize large k ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) v) i := by
  all_goals
    classical
    have hh := PerfectMatchingBipartiteBalance.deleted_color_count ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) i v
    rw [Fintype.card_subtype] at hh
    change ClassSize (fun x : ({v}ᶜ : Set ((Σ b : Fin 13, Fin (BagSize large k b)))) => (fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x.val) i =
      ClassSize ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) i - if (fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) v = i then 1 else 0 at hh
    simpa only [RemainingSize, class_size, eq_comm] using hh

end AEYConstructionProperties

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace GraphOmissionBound
open Finset PentagonDefectCounting
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Missing neighbors in a single permitted class are bounded by the full missing degree. -/
private theorem class_missing_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin 5) (hf : ∀ ⦃x y⦄, G.Adj x y → (SimpleGraph.cycleGraph 5).Adj (f x) (f y))
    (x : V) (j : Fin 5) (hj : (SimpleGraph.cycleGraph 5).Adj (f x) j) :
    ((univ.filter fun y => f y = j ∧ ¬ G.Adj x y).card : ℤ) ≤
      (ClassSize f (f x + 4) : ℤ) + ClassSize f (f x + 1) - G.degree x := by
  all_goals
    classical
    have hpoint (y : V) :
        (if f y = j ∧ ¬ G.Adj x y then (1 : ℤ) else 0) ≤ DefectWeight G f x y := by
      by_cases h : f y = j ∧ ¬ G.Adj x y
      · simp [DefectWeight, h.1, h.2, hj]
      · have hh : 0 ≤ DefectWeight G f x y := by
          unfold DefectWeight
          split_ifs <;> norm_num
        simpa only [if_neg h] using hh
    have hsum := sum_le_sum (fun y (_ : y ∈ univ) => hpoint y)
    rw [defect_row G f hf x] at hsum
    simpa [Finset.sum_filter] using hsum

/-- Deleting vertices cannot add missing neighbors to any fixed class. -/
private theorem deleted_class_missing_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin 5) (v : V) (x : ({v}ᶜ : Set V)) (j : Fin 5) :
    (univ.filter fun y : ({v}ᶜ : Set V) => f y.val = j ∧
      ¬ (G.induce ({v}ᶜ : Set V)).Adj x y).card ≤
    (univ.filter fun y : V => f y = j ∧ ¬ G.Adj x.val y).card := by
  all_goals
    classical
    apply card_le_card_of_injOn (fun y : ({v}ᶜ : Set V) => y.val)
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩
    · intro y _ z _ hyz
      exact Subtype.ext hyz

end GraphOmissionBound

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace AEYUpperAbstract
open Finset AEYConstruction AEYConstructionProperties PentagonPairSizes PentagonDefectCounting

/-- Every reconstructed vertex has at most two omissions in its complete cyclic blow-up row. -/
private theorem allowed_le_degree_add_two (large : Bool) (k : ℕ) (hk : 5 ≤ k)
    (x : (Σ b : Fin 13, Fin (BagSize large k b))) :
    ClassSize ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x + 4) +
      ClassSize ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x + 1) ≤ (B large k).degree x + 2 := by
  all_goals
    rw [class_size, class_size]
    cases large
    · rw [ConstructionRows.degree_small k hk]
      rcases x with ⟨b,x⟩
      fin_cases b <;> norm_num [BagClass, BaseSize] <;> omega
    · rw [ConstructionRows.degree_large k hk]
      rcases x with ⟨b,x⟩
      fin_cases b <;> norm_num [BagClass, BaseSize] <;> omega

/-- Each adjacent class omits at most two neighbors, uniformly in the unbounded construction parameter. -/
private theorem class_omissions (large : Bool) (k : ℕ) (hk : 5 ≤ k)
    (x : (Σ b : Fin 13, Fin (BagSize large k b))) (j : Fin 5) (hj : (SimpleGraph.cycleGraph 5).Adj ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x) j) :
    (univ.filter fun y => (fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) y = j ∧ ¬ (B large k).Adj x y).card ≤ 2 := by
  all_goals
    have hh := GraphOmissionBound.class_missing_le (B large k) ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1))
      (fun {_ _} h => class_map_adj large k h) x j hj
    have hb := allowed_le_degree_add_two large k hk x
    dsimp only at hh hb ⊢
    omega

/-- Deleting any vertex from either residue family leaves a perfect matching. -/
private theorem factor_critical (large : Bool) (k : ℕ) (hk : 5 ≤ k) (v : (Σ b : Fin 13, Fin (BagSize large k b))) :
    ∃ M : ((B large k).induce ({v}ᶜ : Set ((Σ b : Fin 13, Fin (BagSize large k b))))).Subgraph,
      M.IsPerfectMatching := by
  all_goals
    classical
    let H := (B large k).induce ({v}ᶜ : Set ((Σ b : Fin 13, Fin (BagSize large k b))))
    let f : ({v}ᶜ : Set ((Σ b : Fin 13, Fin (BagSize large k b)))) → Fin 5 := fun x => (fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) x.val
    let s := RemainingSize large k ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) v)
    let r := PairSize s
    apply PentagonPairMatching.exists_perfect_matching H f r
    · intro i
      have hh := (split_sizes large k hk ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) v) i).1
      have hs := deleted_class_size large k v i
      change ClassSize f i = _
      rw [hs]
      exact hh.symm
    · intro i
      have hh := (split_sizes large k hk ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1) v) i).2.1
      exact (by omega : 4 ≤ k).trans hh
    · intro x j hj
      have hh := GraphOmissionBound.deleted_class_missing_le (B large k)
        ((fun x : (Σ b : Fin 13, Fin (BagSize large k b)) => BagClass x.1)) v x j
      exact hh.trans (class_omissions large k hk x.val j ((cycle_five_adjacency _ _).mpr hj))

end AEYUpperAbstract

set_option maxHeartbeats 1000000
namespace FactorCriticalTransport
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism maps a perfect matching to a perfect matching. -/
private theorem perfect_matching_map (e : G ≃g H) (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    (M.map e.toHom).IsPerfectMatching := by
  all_goals
    refine ⟨SimpleGraph.Subgraph.IsMatching.map e.toHom e.injective hM.1, ?_⟩
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    exact ⟨x,hM.2 x,rfl⟩

/-- Factor-criticality is preserved under a graph isomorphism. -/
private theorem factor_critical (e : G ≃g H)
    (hG : ∀ v : V, ∃ M : (G.induce ({v}ᶜ : Set V)).Subgraph, M.IsPerfectMatching) :
    ∀ w : W, ∃ M : (H.induce ({w}ᶜ : Set W)).Subgraph, M.IsPerfectMatching := by
  all_goals
    intro w
    let v := e.symm w
    have hsets : Set.BijOn e ({v}ᶜ : Set V) ({w}ᶜ : Set W) := by
      refine ⟨?_, e.injective.injOn, ?_⟩
      · intro x hx
        change x ≠ v at hx
        change e x ≠ w
        intro h
        apply hx
        apply e.injective
        simpa only [v, e.apply_symm_apply] using h
      · intro y hy
        change y ≠ w at hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        change e.symm y ≠ v
        intro h
        apply hy
        have hh := congrArg e h
        simpa only [v, e.apply_symm_apply] using hh
    let eD := e.induce hsets
    obtain ⟨M,hM⟩ := hG v
    exact ⟨M.map eD.toHom, perfect_matching_map eD M hM⟩

end FactorCriticalTransport

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace AEYUpperAttainment
open Classical
open AEYConstruction
open D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

/-- The exact bag construction gives an admissible graph attaining the proposed matching number. -/
theorem attainment (large : Bool) (k : ℕ) (hk : 5 ≤ k) :
    let d := 4 * k + if large then 3 else 1
    ∃ N : ℕ, ∃ G : SimpleGraph (Fin N),
      IsAlmostRegular G d ∧ G.CliqueFree 3 ∧ IsFactorCritical G ∧
      matchingNumber G = 5 * (d + 1) / 4 := by
  all_goals
    classical
    let d := 4 * k + if large then 3 else 1
    let Q := 5 * (d + 1) / 4
    have horder : Fintype.card ((Σ b : Fin 13, Fin (BagSize large k b))) = 2 * Q + 1 := order large k
    let H := (B large k).overFin horder
    let e := (B large k).overFinIso horder
    have hsize0 : BagSize large k 0 = 1 := by exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
    let v : (Σ b : Fin 13, Fin (BagSize large k b)) := ⟨0,⟨0,by rw [hsize0]; omega⟩⟩
    have hfirst (x : (Σ b : Fin 13, Fin (BagSize large k b))) (hx : x.1 = 0) : x = v := by
      rcases x with ⟨b,x⟩
      change b = 0 at hx
      subst b
      haveI : Subsingleton (Fin (BagSize large k 0)) := by rw [hsize0]; infer_instance
      exact congrArg (Sigma.mk 0) (Subsingleton.elim x v.2)
    have hdegree (x : (Σ b : Fin 13, Fin (BagSize large k b))) :
        (B large k).degree x = d - if x.1 = 0 then 1 else 0 := by
      cases large
      · exact ConstructionRows.degree_small k hk x
      · exact ConstructionRows.degree_large k hk x
    have hv : (B large k).degree v = d - 1 := by
      exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (hdegree v)) k)
    have hreg (x : (Σ b : Fin 13, Fin (BagSize large k b))) (hx : x ≠ v) : (B large k).degree x = d := by
      rw [hdegree, if_neg (fun h => hx (hfirst x h)), Nat.sub_zero]
    have hr : IsAlmostRegular H d := by
      refine ⟨e v, ?_, ?_⟩
      · exact (e.degree_eq v).trans hv
      · intro y hy
        obtain ⟨x,rfl⟩ := e.surjective y
        rw [e.degree_eq]
        exact hreg x (fun h => hy (congrArg e h))
    have htri : H.CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap ⟨e.symm.toCopy⟩ (triangle_free large k)
    have hfc : IsFactorCritical H :=
      FactorCriticalTransport.factor_critical e (AEYUpperAbstract.factor_critical large k hk)
    have hmatching : matchingNumber H = Q := by
      have hh := FactorCriticalOrder.almost_regular_order_eq H hfc hr
      omega
    exact ⟨2 * Q + 1,H,hr,htri,hfc,hmatching⟩

end AEYUpperAttainment


set_option maxHeartbeats 1000000

end D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper
