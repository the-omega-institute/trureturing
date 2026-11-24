/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Twelve capped tetrahedra without singleton triangle cofaces cannot use eight vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TetrahedronLinkBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CappedTriangleLinkFive
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Preimage

/-! At order twelve, each vertex link on an eight-vertex support attains
the lower bound of six triangles. It is a triangular bipyramid. The
complement of the support graph has degree two, so no vertex neighborhood
can contain the nine edges of a bipyramid. -/

set_option autoImplicit false

namespace Q9TetrahedronEightVertex

open Finset
open scoped BigOperators
open Q9TriangleSupportReduction (support incident link NoSingletonEdges)

variable {V : Type*} [DecidableEq V]

/-- Edges with both endpoints in the specified vertex set, as two-element finsets. -/
noncomputable def edgesIn (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact (S.powersetCard 2).filter (fun e : Finset V => G.IsClique (e : Set V))

private theorem mem_edgesIn {G : SimpleGraph V} {S e : Finset V} :
    e ∈ edgesIn G S ↔ e ⊆ S ∧ e.card = 2 ∧ G.IsClique (e : Set V) := by
  classical
  simp only [edgesIn, mem_filter, mem_powersetCard, and_assoc]

private theorem pair_mem_edgesIn {G : SimpleGraph V} {S : Finset V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (h : G.Adj x y) :
    ({x, y} : Finset V) ∈ edgesIn G S :=
  mem_edgesIn.mpr ⟨insert_subset hx (singleton_subset_iff.mpr hy),
    card_pair_eq_two_iff.mpr h.ne,
    by rw [coe_pair, SimpleGraph.isClique_pair]; exact fun _ => h⟩

private theorem card_incident_edgesIn (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x : V} (hx : x ∈ S) :
    (incident (edgesIn G S) x).card = (S.filter (G.Adj x)).card := by
  have hImage :
      (S.filter (G.Adj x)).image (fun y => ({x, y} : Finset V)) =
        incident (edgesIn G S) x := by
    ext e
    constructor
    · intro he
      obtain ⟨y, hy, rfl⟩ := mem_image.mp he
      obtain ⟨hyS, hxy⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨pair_mem_edgesIn hx hyS hxy, mem_insert_self _ _⟩
    · intro he
      obtain ⟨heG, hxe⟩ := mem_filter.mp he
      obtain ⟨hSub, hCard, hClique⟩ := mem_edgesIn.mp heG
      have hErase : (e.erase x).card = 1 := by rw [card_erase_of_mem hxe, hCard]
      obtain ⟨y, hy⟩ := card_eq_one.mp hErase
      have hyErase : y ∈ e.erase x := by
        simpa only [hy] using mem_singleton_self y
      obtain ⟨hyx, hye⟩ := mem_erase.mp hyErase
      refine mem_image.mpr ⟨y, mem_filter.mpr ⟨hSub hye, hClique hxe hye hyx.symm⟩, ?_⟩
      simpa only [hy] using (insert_erase hxe)
  rw [← hImage]
  apply card_image_of_injOn
  intro y hy z hz heq
  have hyx := (mem_filter.mp (mem_coe.mp hy)).2.ne'
  have hzx := (mem_filter.mp (mem_coe.mp hz)).2.ne'
  have heq' := congrArg (erase · x) heq
  change (({x, y} : Finset V).erase x) = ({x, z} : Finset V).erase x at heq'
  rw [erase_insert (notMem_singleton.mpr hyx.symm),
    erase_insert (notMem_singleton.mpr hzx.symm)] at heq'
  exact mem_singleton.mp (heq' ▸ mem_singleton_self y)

/-- The complement of a 5-regular graph on eight vertices has at least
four edges wholly inside the neighborhood of any vertex of the original graph. -/
theorem four_le_complement_edges_in_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = 8) (hDegree : ∀ x ∈ S, (S.filter (G.Adj x)).card = 5)
    {v : V} (hv : v ∈ S) :
    4 ≤ (edgesIn Gᶜ (S.filter (G.Adj v))).card := by
  classical
  let N := S.filter (G.Adj v)
  let B := (S.erase v) \ N
  let D := edgesIn Gᶜ S
  let I := edgesIn Gᶜ N
  let P := incident D v
  let Q := D \ (I ∪ P)
  have hComp (x : V) (hx : x ∈ S) : (incident D x).card = 2 := by
    have hEq : S.filter (Gᶜ.Adj x) = (S.erase x) \ S.filter (G.Adj x) := by
      ext y
      simp only [mem_filter, SimpleGraph.compl_adj, mem_sdiff, mem_erase]
      constructor
      · rintro ⟨hyS, hxy, hAdj⟩
        exact ⟨⟨hxy.symm, hyS⟩, fun h => hAdj h.2⟩
      · rintro ⟨⟨hyx, hyS⟩, hNot⟩
        exact ⟨hyS, hyx.symm, fun h => hNot ⟨hyS, h⟩⟩
    have hSub : S.filter (G.Adj x) ⊆ S.erase x :=
      fun y hy => mem_erase.mpr ⟨(mem_filter.mp hy).2.ne', (mem_filter.mp hy).1⟩
    change (incident (edgesIn Gᶜ S) x).card = 2
    rw [card_incident_edgesIn Gᶜ hx, hEq, card_sdiff_of_subset hSub,
      card_erase_of_mem hx, hS, hDegree x hx]
  have hD : D.card = 8 := by
    have hCount : S.card * 2 = D.card * 2 := by
      refine card_mul_eq_card_mul (fun x (e : Finset V) => x ∈ e)
        (s := S) (t := D) hComp ?_
      intro e he
      obtain ⟨heS, heCard, _⟩ := mem_edgesIn.mp he
      change (S.filter (· ∈ e)).card = 2
      rw [filter_mem_eq_inter, inter_eq_right.mpr heS, heCard]
    omega
  have hNSub : N ⊆ S.erase v :=
    fun y hy => mem_erase.mpr ⟨(mem_filter.mp hy).2.ne', (mem_filter.mp hy).1⟩
  have hB : B.card = 2 := by
    change ((S.erase v) \ N).card = 2
    rw [card_sdiff_of_subset hNSub, card_erase_of_mem hv, hS]
    change 8 - 1 - (S.filter (G.Adj v)).card = 2
    rw [hDegree v hv]
  -- Every remaining removed edge meets a nonneighbor other than the pivot.
  -- Each such vertex has only one complement edge besides its edge to the pivot.
  have hQ : Q.card ≤ 2 := by
    have hCount : Q.card * 1 ≤ B.card * 1 := by
      refine card_mul_le_card_mul (fun (e : Finset V) x => x ∈ e)
        (s := Q) (t := B) ?_ ?_
      · intro e he
        obtain ⟨heD, heOut⟩ := mem_sdiff.mp he
        obtain ⟨heS, heCard, heClique⟩ := mem_edgesIn.mp heD
        have heN : ¬e ⊆ N := fun h =>
          heOut (mem_union_left _ (mem_edgesIn.mpr ⟨h, heCard, heClique⟩))
        have hev : v ∉ e :=
          fun h => heOut (mem_union_right _ (mem_filter.mpr ⟨heD, h⟩))
        obtain ⟨x, hxe, hxN⟩ := Finset.not_subset.mp heN
        have hxv : x ≠ v := by
          rintro rfl
          exact hev hxe
        exact card_pos.mpr
          ⟨x, mem_filter.mpr ⟨mem_sdiff.mpr
            ⟨mem_erase.mpr ⟨hxv, heS hxe⟩, hxN⟩, hxe⟩⟩
      · intro x hx
        obtain ⟨hxErase, hxN⟩ := mem_sdiff.mp hx
        obtain ⟨hxv, hxS⟩ := mem_erase.mp hxErase
        have hAdj : Gᶜ.Adj v x := (SimpleGraph.compl_adj _ _ _).mpr
          ⟨hxv.symm, fun h => hxN (mem_filter.mpr ⟨hxS, h⟩)⟩
        have hPair := pair_mem_edgesIn hv hxS hAdj
        have hPairAtX : ({v, x} : Finset V) ∈ incident D x :=
          mem_filter.mpr ⟨hPair, by simp⟩
        have hSub : Q.bipartiteBelow (fun (e : Finset V) y => y ∈ e) x ⊆
            (incident D x).erase ({v, x} : Finset V) := by
          intro e he
          obtain ⟨heQ, hxe⟩ := mem_filter.mp he
          obtain ⟨heD, heOut⟩ := mem_sdiff.mp heQ
          refine mem_erase.mpr ⟨?_, mem_filter.mpr ⟨heD, hxe⟩⟩
          rintro rfl
          exact heOut (mem_union_right _ (mem_filter.mpr ⟨hPair, mem_insert_self _ _⟩))
        exact (card_le_card hSub).trans (by rw [card_erase_of_mem hPairAtX, hComp x hxS])
    omega
  have hUnion := card_union_le I P
  have hSubset : I ∪ P ⊆ D := by
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨heN, heCard, heClique⟩ := mem_edgesIn.mp he
      exact mem_edgesIn.mpr ⟨heN.trans (filter_subset _ _), heCard, heClique⟩
    · exact (mem_filter.mp he).1
  have hSplit : Q.card + (I ∪ P).card = D.card := card_sdiff_add_card_eq_card hSubset
  have hP : P.card = 2 := hComp v hv
  change 4 ≤ I.card
  omega

/-- A vertex of a 5-regular graph on eight vertices spans at most six
edges among its five neighbors. -/
theorem edges_in_neighbors_le_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = 8) (hDegree : ∀ x ∈ S, (S.filter (G.Adj x)).card = 5)
    {v : V} (hv : v ∈ S) :
    (edgesIn G (S.filter (G.Adj v))).card ≤ 6 := by
  classical
  let N := S.filter (G.Adj v)
  have hComp := four_le_complement_edges_in_neighbors G S hS hDegree hv
  have hEdges : edgesIn G N =
      (N.powersetCard 2).filter (fun e : Finset V => G.IsClique (e : Set V)) := by
    ext e
    simp only [edgesIn, mem_filter]
  have hFilter : edgesIn Gᶜ N =
      (N.powersetCard 2).filter (fun e : Finset V => ¬G.IsClique (e : Set V)) := by
    ext e
    simp only [edgesIn, mem_filter]
    apply and_congr_right
    intro he
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
    simp only [coe_pair, SimpleGraph.isClique_pair, SimpleGraph.compl_adj]
    constructor
    · intro h hAdj
      exact (h hxy).2 (hAdj hxy)
    · intro h _
      exact ⟨hxy, fun hAdj => h (fun _ => hAdj)⟩
  have hSplit := card_filter_add_card_filter_not (s := N.powersetCard 2)
    (fun e : Finset V => G.IsClique (e : Set V))
  rw [← hEdges, ← hFilter, card_powersetCard, show N.card = 5 from hDegree v hv] at hSplit
  change (edgesIn G N).card + (edgesIn Gᶜ N).card = 10 at hSplit
  change 4 ≤ (edgesIn Gᶜ N).card at hComp
  change (edgesIn G N).card ≤ 6
  omega

private theorem sum_incident_eq {C : Finset (Finset V)} {k : ℕ}
    (hRank : ∀ t ∈ C, t.card = k) :
    (∑ x ∈ support C, (incident C x).card) = C.card * k := by
  calc
    _ = ∑ t ∈ C, ((support C).filter (· ∈ t)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x (t : Finset V) => x ∈ t)
    _ = ∑ _t ∈ C, k := by
      apply sum_congr rfl
      intro t ht
      rw [filter_mem_eq_inter, inter_eq_right.mpr
        (show t ⊆ support _ from subset_biUnion_of_mem id ht), hRank t ht]
    _ = C.card * k := by rw [sum_const, Nat.nsmul_eq_mul]

private theorem incident_eq_of_saturated {C : Finset (Finset V)} {k d : ℕ}
    (hRank : ∀ t ∈ C, t.card = k)
    (hLower : ∀ x ∈ support C, d ≤ (incident C x).card)
    (hTotal : C.card * k = (support C).card * d)
    {x : V} (hx : x ∈ support C) : (incident C x).card = d := by
  have hSum := sum_incident_eq hRank
  rw [hTotal, ← sum_erase_add (support C) (fun y => (incident C y).card) hx] at hSum
  have hRest : ((support C).erase x).card * d ≤
      ∑ y ∈ (support C).erase x, (incident C y).card := by
    simpa only [Nat.nsmul_eq_mul] using
      ((support C).erase x).card_nsmul_le_sum (fun y => (incident C y).card) d
        (fun y hy => hLower y (mem_of_mem_erase hy))
  have hCard := card_erase_add_one hx
  have hProduct : ((support C).erase x).card * d + d = (support C).card * d := by
    calc
      _ = (((support C).erase x).card + 1) * d := (Nat.succ_mul _ _).symm
      _ = _ := by rw [hCard]
  have hxLower := hLower x hx
  omega

private theorem exists_other_triangle {T : Finset (Finset V)} (hNo : NoSingletonEdges T)
    {e t : Finset V} (he : e.card = 2) (ht : t ∈ T) (het : e ⊆ t) :
    ∃ u ∈ T, e ⊆ u ∧ u ≠ t := by
  let W := T.filter (e ⊆ ·)
  have htW : t ∈ W := mem_filter.mpr ⟨ht, het⟩
  have hPos : 0 < W.card := card_pos.mpr ⟨t, htW⟩
  have hNe : W.card ≠ 1 := hNo e he
  have hErase := card_erase_add_one htW
  obtain ⟨u, hu⟩ : (W.erase t).Nonempty := card_pos.mp (by omega)
  obtain ⟨hut, huW⟩ := mem_erase.mp hu
  exact ⟨u, (mem_filter.mp huW).1, (mem_filter.mp huW).2, hut⟩

-- The cofaces of xz and xu must share the only remaining triangle at x.
private theorem third_triangle {T : Finset (Finset V)}
    (hRank : ∀ t ∈ T, t.card = 3) (hNo : NoSingletonEdges T)
    {x y z u : V} (hxz : x ≠ z) (hxu : x ≠ u) (hyz : y ≠ z)
    (hyu : y ≠ u) (hzu : z ≠ u)
    (ht : ({x, y, z} : Finset V) ∈ T) (hs : ({x, y, u} : Finset V) ∈ T)
    (hDeg : (incident T x).card = 3) :
    ({x, z, u} : Finset V) ∈ T := by
  let t : Finset V := {x, y, z}
  let s : Finset V := {x, y, u}
  have hzNotS : z ∉ s := by simp [s, hxz.symm, hyz.symm, hzu]
  have huNotT : u ∉ t := by simp [t, hxu.symm, hyu.symm, hzu.symm]
  have hst : s ≠ t := by
    intro h
    apply hzNotS
    rw [h]
    simp [t]
  have htI : t ∈ incident T x := mem_filter.mpr ⟨ht, by simp [t]⟩
  have hsI : s ∈ (incident T x).erase t :=
    mem_erase.mpr ⟨hst, mem_filter.mpr ⟨hs, by simp [s]⟩⟩
  let W := ((incident T x).erase t).erase s
  have hW : W.card = 1 := by
    dsimp only [W]
    rw [card_erase_of_mem hsI, card_erase_of_mem htI, hDeg]
  obtain ⟨f, hf, hfSub, hft⟩ := exists_other_triangle hNo
    (card_pair_eq_two_iff.mpr hxz) ht
    (show ({x, z} : Finset V) ⊆ t by simp [t, insert_subset_iff])
  obtain ⟨g, hg, hgSub, hgs⟩ := exists_other_triangle hNo
    (card_pair_eq_two_iff.mpr hxu) hs
    (show ({x, u} : Finset V) ⊆ s by simp [s, insert_subset_iff])
  have hxf : x ∈ f := hfSub (by simp)
  have hzf : z ∈ f := hfSub (by simp)
  have hxg : x ∈ g := hgSub (by simp)
  have hug : u ∈ g := hgSub (by simp)
  have hfs : f ≠ s := by
    rintro rfl
    exact hzNotS hzf
  have hgt : g ≠ t := by
    rintro rfl
    exact huNotT hug
  have hfW : f ∈ W := mem_erase.mpr
    ⟨hfs, mem_erase.mpr ⟨hft, mem_filter.mpr ⟨hf, hxf⟩⟩⟩
  have hgW : g ∈ W := mem_erase.mpr
    ⟨hgs, mem_erase.mpr ⟨hgt, mem_filter.mpr ⟨hg, hxg⟩⟩⟩
  have hfg := (card_le_one.mp hW.le) f hfW g hgW
  have huf : u ∈ f := by rwa [hfg]
  have hEq : ({x, z, u} : Finset V) = f := by
    apply eq_of_subset_of_card_le
    · exact insert_subset hxf (insert_subset hzf (singleton_subset_iff.mpr huf))
    · rw [hRank f hf]
      simp [card_insert_of_notMem, hxz, hxu, hzu]
  rwa [hEq]

-- Saturation on six used vertices forces the boundary of a tetrahedron.
private theorem six_triangle_support_card {T : Finset (Finset V)}
    (hRank : ∀ t ∈ T, t.card = 3) (hNo : NoSingletonEdges T)
    (hCap : ∀ W : Finset V, W.card ≤ 4 → (T.filter (· ⊆ W)).card ≤ 3)
    (hSix : T.card = 6) : (support T).card = 5 := by
  have hLower (x : V) (hx : x ∈ support T) : 3 ≤ (incident T x).card :=
    Q9TriangleSupportReduction.three_le_degree hRank hNo hx
  have hCount : (support T).card * 3 ≤ T.card * 3 := by
    refine card_mul_le_card_mul (fun x (t : Finset V) => x ∈ t)
      (s := support T) (t := T) hLower ?_
    intro t ht
    change ((support T).filter (· ∈ t)).card ≤ 3
    rw [filter_mem_eq_inter, inter_eq_right.mpr
        (show t ⊆ support _ from subset_biUnion_of_mem id ht), hRank t ht]
  have hFive : 5 ≤ (support T).card := by
    by_contra h
    have hc := hCap (support T) (by omega)
    have hf : T.filter (· ⊆ support T) = T :=
      filter_true_of_mem fun t ht => subset_biUnion_of_mem id ht
    rw [hf, hSix] at hc
    omega
  by_contra hNotFive
  have hSize : (support T).card = 6 := by omega
  have hDegree (x : V) (hx : x ∈ support T) : (incident T x).card = 3 :=
    incident_eq_of_saturated hRank hLower (by rw [hSix, hSize]) hx
  obtain ⟨t, ht⟩ : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (hRank t ht)
  let e : Finset V := {x, y}
  have he : e.card = 2 := card_pair_eq_two_iff.mpr hxy
  obtain ⟨s, hs, hes, hst⟩ := exists_other_triangle hNo he ht
    (show e ⊆ ({x, y, z} : Finset V) by simp [e, insert_subset_iff])
  have hDiff : (s \ e).card = 1 := by rw [card_sdiff_of_subset hes, hRank s hs, he]
  obtain ⟨u, hu⟩ := card_eq_one.mp hDiff
  have ⟨hus, hue⟩ := mem_sdiff.mp (show u ∈ s \ e by simp [hu])
  have hxu : x ≠ u := fun h => hue (by simp [e, ← h])
  have hyu : y ≠ u := fun h => hue (by simp [e, ← h])
  have hsEq : ({x, y, u} : Finset V) = s := by
    have hIns : insert u e = s := by
      apply eq_of_subset_of_card_le (insert_subset hus hes)
      rw [card_insert_of_notMem hue, he, hRank s hs]
    calc
      ({x, y, u} : Finset V) = insert u e := by ext a; simp [e, or_comm, or_left_comm]
      _ = s := hIns
  have hzu : z ≠ u := by
    intro h
    exact hst (by simpa only [← h] using hsEq.symm)
  have hxyu : ({x, y, u} : Finset V) ∈ T := by rwa [hsEq]
  have hxs : x ∈ support T := subset_biUnion_of_mem id ht (by simp)
  have hys : y ∈ support T := subset_biUnion_of_mem id ht (by simp)
  have hxzu := third_triangle hRank hNo hxz hxu hyz hyu hzu ht hxyu (hDegree x hxs)
  have hyzu := third_triangle hRank hNo hyz hyu hxz hxu hzu
    (show ({y, x, z} : Finset V) ∈ T by simpa only [insert_comm y x] using ht)
    (show ({y, x, u} : Finset V) ∈ T by simpa only [insert_comm y x, hsEq] using hs)
    (hDegree y hys)
  let W : Finset V := {x, y, z, u}
  have hW : W.card = 4 := by
    simp [W, card_insert_of_notMem, hxy, hxz, hxu, hyz, hyu, hzu]
  have hErase (a : V) (ha : a ∈ W) : W.erase a ∈ T := by
    simp only [W, mem_insert, mem_singleton] at ha
    rcases ha with ha | ha | ha | ha
    · subst a
      dsimp only [W]
      rw [erase_insert (show x ∉ ({y, z, u} : Finset V) by simp [hxy, hxz, hxu])]
      exact hyzu
    · subst a
      dsimp only [W]
      rw [erase_insert_of_ne hxy,
        erase_insert (show y ∉ ({z, u} : Finset V) by simp [hyz, hyu])]
      exact hxzu
    · subst a
      dsimp only [W]
      rw [erase_insert_of_ne hxz, erase_insert_of_ne hyz, erase_insert (notMem_singleton.mpr hzu)]
      exact hxyu
    · subst a
      simpa [W, erase_insert_of_ne, hxu, hyu, hzu, insert_empty_eq] using ht
  have hAll : W.powersetCard 3 ⊆ T.filter (· ⊆ W) := by
    intro q hq
    obtain ⟨hqW, hqCard⟩ := mem_powersetCard.mp hq
    obtain ⟨a, ha⟩ : (W \ q).Nonempty := card_pos.mp (by
      rw [card_sdiff_of_subset hqW, hW, hqCard]; decide)
    obtain ⟨haW, haq⟩ := mem_sdiff.mp ha
    have hqEq : q = W.erase a :=
      eq_of_subset_of_card_le (subset_erase.mpr ⟨hqW, haq⟩) (by
        rw [card_erase_of_mem haW, hW, hqCard])
    exact mem_filter.mpr ⟨by rw [hqEq]; exact hErase a haW, hqW⟩
  have hBound := (card_le_card hAll).trans (hCap W hW.le)
  rw [card_powersetCard, hW] at hBound
  exact (by decide : ¬ (Nat.choose 4 3 ≤ 3)) hBound

private def faceEdges (T : Finset (Finset V)) : Finset (Finset V) :=
  T.biUnion (·.powersetCard 2)

private theorem bipyramid_has_nine_edges (T : Finset (Finset V))
    (hRank : ∀ t ∈ T, t.card = 3) (hNo : NoSingletonEdges T)
    (hCap : ∀ W : Finset V, W.card ≤ 4 → (T.filter (· ⊆ W)).card ≤ 3)
    (hSix : T.card = 6) : 9 ≤ (faceEdges T).card := by
  classical
  let X := support T
  have hX : Fintype.card X = 5 := (Fintype.card_coe X).trans
    (six_triangle_support_card hRank hNo hCap hSix)
  let e : X ≃ Fin 5 := Fintype.equivFinOfCardEq hX
  let emb : Fin 5 ↪ V := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let f : Finset (Fin 5) ↪ Finset V := (mapEmbedding emb).toEmbedding
  let U := T.preimage f f.injective.injOn
  have hMap : U.map f = T := by
    ext t
    constructor
    · intro ht
      obtain ⟨a, ha, rfl⟩ := mem_map.mp ht
      exact mem_preimage.mp ha
    · intro ht
      let a := (t.subtype (· ∈ X)).map e.toEmbedding
      have hEmb : e.toEmbedding.trans emb = Function.Embedding.subtype (· ∈ X) := by
        apply Function.Embedding.ext
        intro y
        change (e.symm (e y)).val = y.val
        rw [Equiv.symm_apply_apply]
      have ha : f a = t := by
        change ((t.subtype (· ∈ X)).map e.toEmbedding).map emb = t
        rw [map_map, hEmb]
        exact subtype_map_of_mem (subset_biUnion_of_mem id ht)
      exact mem_map.mpr ⟨a, mem_preimage.mpr (by rw [ha]; exact ht), ha⟩
  have hURank (t : Finset (Fin 5)) (ht : t ∈ U) : t.card = 3 := by
    have h := hRank (f t) (mem_preimage.mp ht)
    change (t.map emb).card = 3 at h
    simpa only [card_map] using h
  have hUCard : U.card = 6 := by rw [← card_map f, hMap, hSix]
  have hUNo (a : Finset (Fin 5)) (ha : a.card = 2) :
      (U.filter (a ⊆ ·)).card ≠ 1 := by
    have hFilter : T.filter (a.map emb ⊆ ·) = (U.filter (a ⊆ ·)).map f := by
      rw [← hMap, filter_map]
      congr 1
      ext t
      simp [Function.comp_def, f]
    have h := hNo (a.map emb) (by simpa only [card_map] using ha)
    rwa [hFilter, card_map] at h
  have hUCap (a : Finset (Fin 5)) (ha : a.card = 4) :
      (U.filter (· ⊆ a)).card ≤ 3 := by
    have hFilter : T.filter (· ⊆ a.map emb) = (U.filter (· ⊆ a)).map f := by
      rw [← hMap, filter_map]
      congr 1
      ext t
      simp [Function.comp_def, f]
    have h := hCap (a.map emb) (by rw [card_map, ha])
    rwa [hFilter, card_map] at h
  obtain ⟨_, part, hPart, hClass⟩ := Q9CappedTriangleLinkFive.triangular_bipyramid U
    hURank (card_pos.mp (by omega)) hUNo hUCap
  let A := ((univ : Finset (Fin 5)).powersetCard 2).erase part
  have hACard : A.card = 9 := by
    have hPartMem : part ∈ (univ : Finset (Fin 5)).powersetCard 2 :=
      mem_powersetCard.mpr ⟨subset_univ _, hPart⟩
    dsimp only [A]
    rw [card_erase_of_mem hPartMem, card_powersetCard, card_univ, Fintype.card_fin]
    decide
  have hCovered : A.map f ⊆ faceEdges T := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    obtain ⟨haNe, haMem⟩ := mem_erase.mp ha
    have haCard := (mem_powersetCard.mp haMem).2
    have hInter : (a ∩ part).card ≤ 1 := by
      have hLe := card_le_card (inter_subset_left : a ∩ part ⊆ a)
      by_contra h
      have haEq : a ∩ part = a :=
        eq_of_subset_of_card_le inter_subset_left (by omega)
      have hSub : a ⊆ part := by
        rw [← haEq]
        exact inter_subset_right
      exact haNe (eq_of_subset_of_card_le hSub (by omega))
    have hExtend : ∃ x ∉ a, ((insert x a) ∩ part).card = 1 := by
      by_cases hZero : (a ∩ part).card = 0
      · have hDiff : 0 < (part \ a).card := by
          rw [card_sdiff, hPart, hZero]
          decide
        obtain ⟨x, hx⟩ := card_pos.mp hDiff
        obtain ⟨hxPart, hxNotA⟩ := mem_sdiff.mp hx
        refine ⟨x, hxNotA, ?_⟩
        rw [insert_inter_of_mem hxPart,
          card_insert_of_notMem (fun h => hxNotA (mem_inter.mp h).1), hZero]
      · have hSize := card_union_le a part
        have hDiff : 0 < ((univ : Finset (Fin 5)) \ (a ∪ part)).card := by
          rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
          omega
        obtain ⟨x, hx⟩ := card_pos.mp hDiff
        have hxNot := (mem_sdiff.mp hx).2
        refine ⟨x, fun h => hxNot (mem_union_left _ h), ?_⟩
        rw [insert_inter_of_notMem (fun h => hxNot (mem_union_right _ h))]
        omega
    obtain ⟨x, hxa, hOne⟩ := hExtend
    have ht : insert x a ∈ U := (hClass _).mpr
      ⟨by rw [card_insert_of_notMem hxa, haCard], hOne⟩
    refine mem_biUnion.mpr ⟨f (insert x a), mem_preimage.mp ht, mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · exact map_subset_map.mpr (subset_insert _ _)
    · change (a.map emb).card = 2
      rw [card_map, haCard]
  have h := card_le_card hCovered
  rwa [card_map, hACard] at h

-- Reinserting the pivot makes erasure injective on its incident faces.
private theorem card_link_filter (C : Finset (Finset V)) (v : V)
    (p : Finset V → Prop) [DecidablePred p] :
    ((link C v).filter p).card = (C.filter fun t => v ∈ t ∧ p (t.erase v)).card := by
  unfold link incident
  rw [filter_image, filter_filter]
  apply card_image_of_injOn
  apply (erase_injOn' v).mono
  intro t ht
  exact (mem_filter.mp (mem_coe.mp ht)).2.1

private def skeleton (C : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ t ∈ C, x ∈ t ∧ y ∈ t
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨t, ht, hx, hy⟩ := h.2
    exact ⟨t, ht, hy, hx⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem neighbors_skeleton_eq (C : Finset (Finset V)) (v : V)
    [DecidableRel (skeleton C).Adj] :
    (support C).filter ((skeleton C).Adj v) = support (link C v) := by
  ext x
  simp only [mem_filter, support, mem_biUnion, id_eq]
  constructor
  · rintro ⟨_, hvx, t, ht, hv, hx⟩
    exact ⟨t.erase v, mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, hv⟩, rfl⟩,
      mem_erase.mpr ⟨hvx.symm, hx⟩⟩
  · rintro ⟨e, he, hxe⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    obtain ⟨htC, hvt⟩ := mem_filter.mp ht
    obtain ⟨hxv, hxt⟩ := mem_erase.mp hxe
    exact ⟨⟨t, htC, hxt⟩, hxv.symm, t, htC, hvt, hxt⟩

/-- Twelve tetrahedra on exactly eight used vertices violate the five-set
cap or have a triangle contained in exactly one tetrahedron. -/
theorem tetrahedra_card_ne_twelve_on_eight_vertices (C : Finset (Finset V))
    (hRank : ∀ t ∈ C, t.card = 4) (hNo : Q9TetrahedronLinkBound.NoSingletonTriangles C)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3)
    (hEight : (support C).card = 8) : C.card ≠ 12 := by
  classical
  intro hTwelve
  have hLower (v : V) (hv : v ∈ support C) : 6 ≤ (incident C v).card :=
    Q9TetrahedronLinkBound.six_le_degree hRank hNo hCap hv
  have hSix (v : V) (hv : v ∈ support C) : (link C v).card = 6 := by
    have hCard : (link C v).card = (incident C v).card := by
      simpa only [filter_true, and_true, incident] using
        card_link_filter C v (fun _ => True)
    rw [hCard]
    exact incident_eq_of_saturated hRank hLower (by rw [hTwelve, hEight]) hv
  have hRankLink (v : V) (e : Finset V) (he : e ∈ link C v) : e.card = 3 := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    obtain ⟨htC, hvt⟩ := mem_filter.mp ht
    rw [card_erase_of_mem hvt, hRank t htC]
  have hNoLink (v : V) : NoSingletonEdges (link C v) := by
    intro e he
    rw [card_link_filter C v (e ⊆ ·)]
    by_cases hve : v ∈ e
    · have hEmpty : (C.filter fun t => v ∈ t ∧ e ⊆ t.erase v) = ∅ :=
        filter_eq_empty_iff.mpr fun t _ ht => notMem_erase v t (ht.2 hve)
      simp [hEmpty]
    · have hFilter : (C.filter fun t => v ∈ t ∧ e ⊆ t.erase v) =
          C.filter (insert v e ⊆ ·) := by
        apply filter_congr
        intro t _
        rw [insert_subset_iff, subset_erase]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hve⟩⟩
      rw [hFilter]
      exact hNo (insert v e) (by rw [card_insert_of_notMem hve, he])
  have hCapLink (v : V) (W : Finset V) (hW : W.card ≤ 4) :
      ((link C v).filter (· ⊆ W)).card ≤ 3 := by
    rw [card_link_filter C v (· ⊆ W)]
    have hSize : (insert v W).card ≤ 5 :=
      (card_insert_le v W).trans (Nat.add_le_add_right hW 1)
    refine (card_le_card ?_).trans (hCap (insert v W) hSize)
    intro t ht
    obtain ⟨htC, _, htW⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨htC, subset_insert_iff.mpr htW⟩
  let G := skeleton C
  let : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have hRegular (v : V) (hv : v ∈ support C) :
      ((support C).filter (G.Adj v)).card = 5 := by
    rw [neighbors_skeleton_eq C v]
    exact six_triangle_support_card (hRankLink v) (hNoLink v) (hCapLink v) (hSix v hv)
  obtain ⟨v, hv⟩ : (support C).Nonempty := card_pos.mp (by omega)
  have hMax := edges_in_neighbors_le_six G (support C) hEight hRegular hv
  have hMin :=
    bipyramid_has_nine_edges (link C v) (hRankLink v) (hNoLink v) (hCapLink v) (hSix v hv)
  have hSub : faceEdges (link C v) ⊆ edgesIn G ((support C).filter (G.Adj v)) := by
    intro e he
    obtain ⟨s, hs, hse⟩ := mem_biUnion.mp he
    obtain ⟨heS, heCard⟩ := mem_powersetCard.mp hse
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    obtain ⟨htC, _⟩ := mem_filter.mp ht
    refine mem_edgesIn.mpr ⟨?_, heCard, ?_⟩
    · rw [neighbors_skeleton_eq C v]
      exact heS.trans (subset_biUnion_of_mem id hs)
    · intro x hx y hy hxy
      exact ⟨hxy, t, htC, mem_of_mem_erase (heS hx), mem_of_mem_erase (heS hy)⟩
  have hCard := card_le_card hSub
  omega

end Q9TetrahedronEightVertex
