/- GID: D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Hall.Basic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.VertexCover, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DeleteEdges]
   utility: none
   digest: Small support witnesses for finite vertex-cover number. -/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import OmegaBuild.Commands

compile_only_with_mathlib

/-! # Small support witnesses for finite vertex-cover number -/

open scoped ENat

namespace CriticalVertexCover

open SimpleGraph

def CoverAtLeast {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  (r : ℕ∞) ≤ G.vertexCoverNum

/-- A finite edge-minimal reduction to the critical-cover regime. -/
private theorem exists_edge_minimal_cover_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hG : CoverAtLeast G r) :
    ∃ H : G.Subgraph,
      CoverAtLeast H.spanningCoe r ∧
        ∀ e ∈ H.spanningCoe.edgeSet,
          ¬ CoverAtLeast (H.spanningCoe.deleteEdges ({e} : Set (Sym2 V))) r := by
  classical
  let C : Finset G.Subgraph :=
    Finset.univ.filter (fun H => CoverAtLeast H.spanningCoe r)
  have htop : (⊤ : G.Subgraph) ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [CoverAtLeast] using hG
  let M : Finset ℕ := C.image (fun H => H.spanningCoe.edgeSet.ncard)
  have hM : M.Nonempty := by
    exact ⟨(⊤ : G.Subgraph).spanningCoe.edgeSet.ncard,
      Finset.mem_image.mpr ⟨⊤, htop, rfl⟩⟩
  let μ := M.min' hM
  have hμ : μ ∈ M := Finset.min'_mem M hM
  obtain ⟨H, hHC, hHμ⟩ := Finset.mem_image.mp hμ
  refine ⟨H, (Finset.mem_filter.mp hHC).2, ?_⟩
  intro e he hdel
  let K : G.Subgraph :=
    SimpleGraph.toSubgraph (H.spanningCoe.deleteEdges ({e} : Set (Sym2 V)))
      ((SimpleGraph.deleteEdges_le ({e} : Set (Sym2 V))).trans H.spanningCoe_le)
  have hKgraph : K.spanningCoe = H.spanningCoe.deleteEdges ({e} : Set (Sym2 V)) := by
    rfl
  have hKC : K ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hKgraph]
    exact hdel
  have hKmem : K.spanningCoe.edgeSet.ncard ∈ M :=
    Finset.mem_image.mpr ⟨K, hKC, rfl⟩
  have hmin : μ ≤ K.spanningCoe.edgeSet.ncard := Finset.min'_le M _ hKmem
  have hcard : K.spanningCoe.edgeSet.ncard < H.spanningCoe.edgeSet.ncard := by
    rw [hKgraph]
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_lt_of_mem he
  rw [← hHμ] at hmin
  exact (Nat.not_lt_of_ge hmin) hcard

/-- The edge-minimal reduction has exact cover number once `r ≥ 1`. -/
private theorem exists_critical_cover_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 1 ≤ r)
    (hG : CoverAtLeast G r) :
    ∃ H : G.Subgraph,
      H.spanningCoe.vertexCoverNum = (r : ℕ∞) ∧
        ∀ e ∈ H.spanningCoe.edgeSet,
          ¬ CoverAtLeast (H.spanningCoe.deleteEdges ({e} : Set (Sym2 V))) r := by
  obtain ⟨H, hH, hcritical⟩ := exists_edge_minimal_cover_subgraph G r hG
  have hne : H.spanningCoe ≠ (⊥ : SimpleGraph V) := by
    intro hbot
    have hzero : H.spanningCoe.vertexCoverNum = 0 := by simp [hbot]
    change (r : ℕ∞) ≤ H.spanningCoe.vertexCoverNum at hH
    have hz : (r : ℕ∞) ≤ 0 := by simpa [hzero] using hH
    have hrzero : r ≤ 0 := ENat.natCast_le_natCast.mp (by simpa using hz)
    omega
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hcrit_uv := hcritical s(u, v) (by simpa using huv)
  have hlt : (H.spanningCoe.deleteEdges ({s(u, v)} : Set (Sym2 V))).vertexCoverNum <
      (r : ℕ∞) := lt_of_not_ge hcrit_uv
  obtain ⟨c, hc_eq, hc_cover⟩ :=
    SimpleGraph.vertexCoverNum_exists (H.spanningCoe.deleteEdges ({s(u, v)} : Set (Sym2 V)))
  have hle : c.encard + 1 ≤ (r : ℕ∞) := by
    rw [hc_eq]
    exact (ENat.add_one_le_iff (SimpleGraph.vertexCoverNum_ne_top_of_finite
      (G := H.spanningCoe.deleteEdges ({s(u, v)} : Set (Sym2 V))))).2 hlt
  have hcover : H.spanningCoe.IsVertexCover (insert u c) := by
    intro a b hab
    by_cases he : s(a, b) = s(u, v)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
    · have hab' : (H.spanningCoe.deleteEdges ({s(u, v)} : Set (Sym2 V))).Adj a b := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hab, he⟩
      rcases hc_cover hab' with ha | hb
      · exact Or.inl (Set.mem_insert_of_mem _ ha)
      · exact Or.inr (Set.mem_insert_of_mem _ hb)
  have hupper : H.spanningCoe.vertexCoverNum ≤ (r : ℕ∞) := by
    exact hcover.vertexCoverNum_le.trans ((Set.encard_insert_le c u).trans hle)
  exact ⟨H, le_antisymm hupper hH, hcritical⟩

/-- Conditional completion of Lemma 3.1. The only explicit supplier is the
Erdős--Gallai bound for edge-critical graphs. -/
private theorem exists_small_cover_witness_of_erdos_gallai_supplier
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 1 ≤ r)
    (hG : CoverAtLeast G r)
    (hEG : ∀ (J : SimpleGraph V),
      J.vertexCoverNum = (r : ℕ∞) →
      (∀ e ∈ J.edgeSet,
        ¬ CoverAtLeast (J.deleteEdges ({e} : Set (Sym2 V))) r) →
      J.support.ncard ≤ 2 * r) :
    ∃ H : G.Subgraph,
      H.spanningCoe.vertexCoverNum = (r : ℕ∞) ∧
        H.spanningCoe.support.ncard ≤ 2 * r := by
  obtain ⟨H, hτ, hcritical⟩ := exists_critical_cover_subgraph G r hr hG
  have hs := hEG H.spanningCoe hτ hcritical
  exact ⟨H, hτ, hs⟩

/-- Erdős–Gallai support bound for edge-critical graphs, as used in
arXiv:2611.34386v1, Lemma 3.1. -/
private theorem erdos_gallai_critical_support_bound
    {V : Type*} [Finite V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ)
    (hτ : G.vertexCoverNum = (r : ℕ∞))
    (hcritical : ∀ e ∈ G.edgeSet,
      (G.deleteEdges ({e} : Set (Sym2 V))).vertexCoverNum < (r : ℕ∞)) :
    G.support.ncard ≤ 2 * r := by
  classical
  obtain ⟨C₀, hC₀card, hC₀cover⟩ := G.vertexCoverNum_exists
  let P := G.support.toFinite.toFinset
  let C := P ∩ C₀.toFinite.toFinset
  let I := P \ C
  have hCsub : C ⊆ P := Finset.inter_subset_left
  have hCcover : G.IsVertexCover (C : Set V) := by
    intro x y hxy
    rcases hC₀cover hxy with hx | hy
    · exact Or.inl (Finset.mem_inter.mpr ⟨by simpa [P] using hxy.mem_support_left,
        by simpa using hx⟩)
    · exact Or.inr (Finset.mem_inter.mpr ⟨by simpa [P] using hxy.mem_support_right,
        by simpa using hy⟩)
  have hCcard : C.card = r := by
    apply le_antisymm
    · have hle : C.card ≤ C₀.toFinite.toFinset.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hcard : (↑C₀.toFinite.toFinset.card : ℕ∞) = (r : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, hC₀card, hτ]
      exact hle.trans (ENat.natCast_inj.mp hcard).le
    · have hle := hCcover.vertexCoverNum_le
      rw [hτ, Set.encard_coe_eq_coe_finsetCard] at hle
      exact ENat.natCast_le_natCast.mp hle
  let N (x : V) := C.filter (G.Adj x)
  have hNeighbor {x y : V} (hx : x ∈ I) (hxy : G.Adj x y) : y ∈ N x := by
    have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
    have hy : y ∈ C := (hCcover hxy).resolve_left hxC
    exact Finset.mem_filter.mpr ⟨hy, hxy⟩
  have hNsub (U : Finset V) : U.biUnion N ⊆ C := by
    intro y hy
    obtain ⟨x, _, hyN⟩ := Finset.mem_biUnion.mp hy
    exact (Finset.mem_filter.mp hyN).1
  have hHall : ∀ U : Finset V, U ⊆ I → U.card ≤ (U.biUnion N).card := by
    intro U hUI
    by_contra! hbad
    have hdeficient : ∃ k : ℕ, ∃ S : Finset V,
        S.card = k ∧ S ⊆ I ∧ (S.biUnion N).card < S.card :=
      ⟨U.card, U, rfl, hUI, hbad⟩
    obtain ⟨S, hSsize, hSI, hSdef⟩ := Nat.find_spec hdeficient
    have hProper {W : Finset V} (hWS : W ⊂ S) : W.card ≤ (W.biUnion N).card := by
      by_contra! hw
      have hlt : W.card < Nat.find hdeficient := hSsize ▸ Finset.card_lt_card hWS
      exact Nat.find_min hdeficient hlt ⟨W, rfl, hWS.le.trans hSI, hw⟩
    have hSne : S.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hSdef)
    obtain ⟨a, haS⟩ := hSne
    have haP : a ∈ P := (Finset.mem_sdiff.mp (hSI haS)).1
    have haSupp : a ∈ G.support := by simpa [P] using haP
    obtain ⟨b, hab⟩ := G.mem_support.mp haSupp
    let T := S.biUnion N
    have hbT : b ∈ T := Finset.mem_biUnion.mpr ⟨a, haS, hNeighbor (hSI haS) hab⟩
    have hTC : T ⊆ C := hNsub S
    have hST {x : V} (hx : x ∈ S) : x ∉ T :=
      fun hxT => (Finset.mem_sdiff.mp (hSI hx)).2 (hTC hxT)
    have hNbrT {x y : V} (hx : x ∈ S) (hxy : G.Adj x y) : y ∈ T :=
      Finset.mem_biUnion.mpr ⟨x, hx, hNeighbor (hSI hx) hxy⟩

    -- Proper subsets meet Hall's condition, and deficiency leaves exactly one vertex unmatched.
    let A := S.erase a
    have hAS : A ⊆ S := Finset.erase_subset _ _
    have hAT : (A.biUnion N) ⊆ T := Finset.biUnion_subset_biUnion_of_subset_left _ hAS
    have hAcard : A.card = T.card := by
      apply le_antisymm
      · exact (hProper (Finset.erase_ssubset haS)).trans (Finset.card_le_card hAT)
      · have hsize : A.card + 1 = S.card := Finset.card_erase_add_one haS
        have hlt : T.card < A.card + 1 := hsize.symm ▸ hSdef
        exact Nat.le_of_lt_succ hlt
    have hAHall (W : Finset ↥A) : W.card ≤ (W.biUnion fun x => N x.val).card := by
      let val : ↥A ↪ V := Function.Embedding.subtype _
      have hWA : W.map val ⊆ A := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hW : W.map val ⊂ S :=
        lt_of_le_of_lt hWA (Finset.erase_ssubset haS)
      have hUnion : (W.map val).biUnion N = W.biUnion (fun x => N x.val) := by
        ext y
        simp only [Finset.mem_biUnion, Finset.mem_map]
        constructor
        · rintro ⟨z, ⟨x, hx, rfl⟩, hy⟩
          exact ⟨x, hx, hy⟩
        · rintro ⟨x, hx, hy⟩
          exact ⟨x.val, ⟨x, hx, rfl⟩, hy⟩
      simpa only [Finset.card_map, hUnion] using hProper hW
    obtain ⟨f, hfInj, hfN⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective (fun x : ↥A => N x.val)).mp hAHall
    let fT (x : ↥A) : ↥T := ⟨f x, Finset.mem_biUnion.mpr ⟨x.val, hAS x.property, hfN x⟩⟩
    have hfT : Function.Bijective fT :=
      (Fintype.bijective_iff_injective_and_card fT).mpr
        ⟨fun _ _ h => hfInj (congrArg Subtype.val h), by simpa only [Fintype.card_coe] using hAcard⟩
    let matching := Equiv.ofBijective fT hfT
    let left (y : ↥T) : V := (matching.symm y).val
    have hleftA (y : ↥T) : left y ∈ A := (matching.symm y).property
    have hleftS (y : ↥T) : left y ∈ S := hAS (hleftA y)
    have hleftInj : Function.Injective left :=
      Subtype.val_injective.comp matching.symm.injective
    have hmatchAdj (y : ↥T) : G.Adj (left y) y.val := by
      have hy : f (matching.symm y) = y.val :=
        congrArg Subtype.val (matching.apply_symm_apply y)
      rw [← hy]
      exact (Finset.mem_filter.mp (hfN (matching.symm y))).2

    let J := G.deleteEdges ({s(a, b)} : Set (Sym2 V))
    have hJlt : J.vertexCoverNum < (r : ℕ∞) := hcritical s(a, b) (by simpa using hab)
    obtain ⟨D₀, hD₀card, hD₀cover⟩ := J.vertexCoverNum_exists
    let D := D₀.toFinite.toFinset
    have hDcover : J.IsVertexCover (D : Set V) := by simpa [D] using hD₀cover
    have hDlt : D.card < r := by
      apply ENat.natCast_lt_natCast.mp
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, hD₀card]
      exact hJlt
    have hhit (y : ↥T) : left y ∈ D ∨ y.val ∈ D := by
      apply hDcover
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hmatchAdj y, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or]
      exact ⟨fun h => (Finset.mem_erase.mp (hleftA y)).1 h.1,
        fun h => hST (hleftS y) (h.1.symm ▸ hbT)⟩

    -- Pick a covered endpoint of each matched edge in the deleted graph.
    let Q := D ∩ (S ∪ T)
    let pick (y : ↥T) : V := if left y ∈ D then left y else y.val
    have hpick (y : ↥T) : pick y ∈ Q := by
      by_cases hy : left y ∈ D
      · simp only [pick, ite_eq_left hy]
        exact Finset.mem_inter.mpr ⟨hy, Finset.mem_union_left T (hleftS y)⟩
      · simp only [pick, ite_eq_right hy]
        exact Finset.mem_inter.mpr
          ⟨(hhit y).resolve_left hy, Finset.mem_union_right S y.property⟩
    have hpickInj : Function.Injective pick := by
      intro y z hyz
      by_cases hy : left y ∈ D <;> by_cases hz : left z ∈ D <;> simp [pick, hy, hz] at hyz
      · exact hleftInj hyz
      · exact (hST (hleftS y) (hyz.symm ▸ z.property)).elim
      · exact (hST (hleftS z) (hyz ▸ y.property)).elim
      · exact hyz
    have hTleQ : T.card ≤ Q.card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective (fun y : ↥T => (⟨pick y, hpick y⟩ : ↥Q))
          (fun _ _ h => hpickInj (congrArg Subtype.val h))
    let R := (D \ (S ∪ T)) ∪ T
    have hRle : R.card ≤ D.card := by
      have hpartition : (D \ (S ∪ T)).card + Q.card = D.card := by
        simpa only [Q, Finset.sdiff_inter_self_left] using
          Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : Q ⊆ D)
      exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hTleQ _).trans_eq hpartition)
    have hRcover : G.IsVertexCover (R : Set V) := by
      intro x y hxy
      change x ∈ R ∨ y ∈ R
      by_contra! hmiss
      have hxT : x ∉ T := fun h => hmiss.1 (Finset.mem_union_right _ h)
      have hyT : y ∉ T := fun h => hmiss.2 (Finset.mem_union_right _ h)
      have hxS : x ∉ S := fun h => hyT (hNbrT h hxy)
      have hyS : y ∉ S := fun h => hxT (hNbrT h hxy.symm)
      have hxyJ : J.Adj x y := by
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or]
        exact ⟨fun h => hxS (h.1.symm ▸ haS), fun h => hyS (h.2.symm ▸ haS)⟩
      rcases hDcover hxyJ with hxD | hyD
      · exact hmiss.1 (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hxD, fun h => (Finset.mem_union.mp h).elim hxS hxT⟩))
      · exact hmiss.2 (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hyD, fun h => (Finset.mem_union.mp h).elim hyS hyT⟩))
    have hRlower := hRcover.vertexCoverNum_le
    rw [hτ, Set.encard_coe_eq_coe_finsetCard] at hRlower
    exact (Nat.not_lt_of_ge (ENat.natCast_le_natCast.mp hRlower)) (hRle.trans_lt hDlt)

  have hIcard : I.card ≤ C.card :=
    (hHall I (fun _ h => h)).trans (Finset.card_le_card (hNsub I))
  have hpartition : I.card + C.card = P.card := Finset.card_sdiff_add_card_eq_card hCsub
  rw [Set.ncard_eq_toFinset_card]
  change P.card ≤ 2 * r
  omega

theorem exists_small_cover_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 1 ≤ r)
    (hG : CoverAtLeast G r) :
    ∃ H : G.Subgraph,
      H.spanningCoe.vertexCoverNum = (r : ℕ∞) ∧
        H.spanningCoe.support.ncard ≤ 2 * r := by
  apply exists_small_cover_witness_of_erdos_gallai_supplier G r hr hG
  intro J hτ hcritical
  exact erdos_gallai_critical_support_bound J r hτ (fun e he => lt_of_not_ge (hcritical e he))

end CriticalVertexCover
