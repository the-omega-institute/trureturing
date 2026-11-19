/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualCountingProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualCountingProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound crossing incidences from each ball and from the residual graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualMatchingProbe

/-! Degree accounting for a coordinate half containing neither ball center. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private incidences incidences_symm incidences_add from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

private lemma directed_internal_twice {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (rank : V → ℕ)
    (hdiff : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → rank u ≠ rank v) :
    incidences G S S =
      2 * ∑ u ∈ S, (S.filter (fun v => G.Adj u v ∧ rank u < rank v)).card := by
  classical
  let up (u v : V) := G.Adj u v ∧ rank u < rank v
  let down (u v : V) := G.Adj u v ∧ rank v < rank u
  have hpart (u : V) (hu : u ∈ S) : (S.filter (G.Adj u)).card =
      (S.filter (up u)).card + (S.filter (down u)).card := by
    have hs : S.filter (G.Adj u) = S.filter (up u) ∪ S.filter (down u) := by
      ext v
      simp only [up,down,mem_filter,mem_union]
      constructor
      · rintro ⟨hv,h⟩
        exact (lt_or_gt_of_ne (hdiff u hu v hv h)).elim
          (fun hl => Or.inl ⟨hv,h,hl⟩) (fun hl => Or.inr ⟨hv,h,hl⟩)
      · rintro (⟨hv,h,_⟩ | ⟨hv,h,_⟩) <;> exact ⟨hv,h⟩
    rw [hs, card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact lt_asymm (mem_filter.mp hv).2.2 (mem_filter.mp hv').2.2
  have heq : (∑ u ∈ S, (S.filter (up u)).card) = ∑ u ∈ S, (S.filter (down u)).card := by
    change (∑ u ∈ S, (S.bipartiteAbove up u).card) = _
    rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    apply sum_congr rfl
    intro v _
    congr 1
    ext u
    simp only [mem_bipartiteBelow,mem_filter,up,down,G.adj_comm]
  calc
    incidences G S S = ∑ u ∈ S, ((S.filter (up u)).card + (S.filter (down u)).card) :=
      sum_congr rfl hpart
    _ = _ := by rw [sum_add_distrib, ← heq, two_mul]

private lemma internal_and_crossing_incidence_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H S U W : Finset V) (rank : V → ℕ)
    (hunion : H = S ∪ U) (hdis : Disjoint S U)
    (huw : Disjoint U W)
    (hdiff : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → rank u ≠ rank v)
    (hcap : ∀ u ∈ S, ((S.filter (fun v => G.Adj u v ∧ rank u < rank v)).card +
      ((U ∪ W).filter (G.Adj u)).card) = 2) :
    incidences G H H + 2 * incidences G S W = 4 * S.card + incidences G U U := by
  have hall := sum_congr (s₁ := S) rfl hcap
  have hc := incidences_add G S U W huw
  have hcross : (∑ u ∈ S, ((U ∪ W).filter (G.Adj u)).card) =
      incidences G S U + incidences G S W := by
    simpa only [incidences, Finset.bipartiteAbove] using hc
  rw [sum_add_distrib, hcross] at hall
  have hconst : (∑ _u ∈ S, (2 : ℕ)) = 2 * S.card := by simp [Nat.mul_comm]
  rw [hconst] at hall
  have hs := directed_internal_twice G S rank hdiff
  have hdec : incidences G H H =
      incidences G S S + 2 * incidences G S U + incidences G U U := by
    rw [hunion, incidences_add G (S ∪ U) S U hdis,
      incidences_symm G (S ∪ U) S, incidences_symm G (S ∪ U) U,
      incidences_add G S S U hdis, incidences_add G U S U hdis,
      incidences_symm G U S]
    omega
  omega

open private HammingSeven.ball HammingSeven.ball_walk hamming_le_walk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private second third mem_second third_witness from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private second_distance third_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private edge_moves_between_shells from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9PartnerGraphProbe
open private no_cross_between_distant_balls from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyDiameterUpperProbe

private lemma ball_has_predecessor {C : Finset (Q 9)}
    {r u : (C : Set (Q 9))} (hu : u ∈ HammingSeven.ball
      ((hypercube 9).induce (C : Set (Q 9))) r) (hne : u ≠ r) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    ∃ v ∈ HammingSeven.ball G r, G.Adj u v ∧
      hammingDist r.val v.val < hammingDist r.val u.val := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  change u ∈ insert r (second G r) ∪ (G.neighborFinset r ∪ third G r) at hu
  rcases mem_union.mp hu with hu | hu
  · rcases mem_insert.mp hu with he | hu
    · exact (hne he).elim
    obtain ⟨v,hrv,hvu,_⟩ := mem_second.mp hu
    have hvdist : hammingDist r.val v.val = 1 := hrv
    exact ⟨v,mem_union_right _ (mem_union_left _ ((G.mem_neighborFinset r v).mpr hrv)),
      hvu.symm,by rw [hvdist,second_distance hu]; omega⟩
  · rcases mem_union.mp hu with hu | hu
    · have hru : G.Adj r u := (G.mem_neighborFinset r u).mp hu
      have hdist : hammingDist r.val u.val = 1 := hru
      exact ⟨r,mem_union_left _ (mem_insert_self _ _),hru.symm,
        by rw [hammingDist_self,hdist]; omega⟩
    · obtain ⟨_,v,_,_,hvu,_,_,hv,_⟩ := third_witness hu
      exact ⟨v,mem_union_left _ (mem_insert_of_mem hv),hvu.symm,
        by rw [second_distance hv,third_distance hu]; omega⟩

open private crossing_neighbor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualMatchingProbe

open private endpoint_eq_of_short_paths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

private lemma ball_walk_exact {C : Finset (Q 9)} {r u : (C : Set (Q 9))}
    (hu : u ∈ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) r) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    ∃ p : G.Walk r u, p.length = hammingDist r.val u.val := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  change u ∈ insert r (second G r) ∪ (G.neighborFinset r ∪ third G r) at hu
  rcases mem_union.mp hu with hu | hu
  · rcases mem_insert.mp hu with rfl | hu
    · exact ⟨.nil, by simp⟩
    · obtain ⟨v,hrv,hvu,_⟩ := mem_second.mp hu
      exact ⟨.cons hrv (.cons hvu .nil), by rw [second_distance hu]; rfl⟩
  · rcases mem_union.mp hu with hu | hu
    · have h : G.Adj r u := (G.mem_neighborFinset r u).mp hu
      exact ⟨.cons h .nil, (show hammingDist r.val u.val = 1 from h).symm⟩
    · obtain ⟨a,b,hra,hab,hbu,_,_,_,_⟩ := third_witness hu
      exact ⟨.cons hra (.cons hab (.cons hbu .nil)), by rw [third_distance hu]; rfl⟩

private lemma ball_predecessor_unique {C : Finset (Q 9)} (hb : IsBalanced C)
    {r u v z : (C : Set (Q 9))}
    (hv : v ∈ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) r)
    (hz : z ∈ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) r)
    (hu : hammingDist r.val u.val ≤ 3)
    (huv : (hypercube 9).Adj u.val v.val) (huz : (hypercube 9).Adj u.val z.val)
    (hltv : hammingDist r.val v.val < hammingDist r.val u.val)
    (hltz : hammingDist r.val z.val < hammingDist r.val u.val) : v = z := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  obtain ⟨p,hp⟩ := ball_walk_exact hv
  obtain ⟨q,hq⟩ := ball_walk_exact hz
  have hvstep : hammingDist r.val v.val + 1 = hammingDist r.val u.val := by
    obtain h | h := edge_moves_between_shells (x := r.val) huv <;> omega
  have hzstep : hammingDist r.val z.val + 1 = hammingDist r.val u.val := by
    obtain h | h := edge_moves_between_shells (x := r.val) huz <;> omega
  let pv : G.Walk r u := p.append (.cons (show G.Adj v u from huv.symm) .nil)
  let qz : G.Walk r u := q.append (.cons (show G.Adj z u from huz.symm) .nil)
  have hpv : pv.length = hammingDist r.val u.val := by
    simpa [pv,hp] using hvstep
  have hqz : qz.length = hammingDist r.val u.val := by
    simpa [qz,hq] using hzstep
  obtain ⟨m,hm⟩ := pv.reachable.exists_walk_length_eq_dist
  have hmLow := hamming_le_walk m
  rw [hm] at hmLow
  have hmHigh := G.dist_le pv
  have hd : G.dist r u = hammingDist r.val u.val := by omega
  have he := endpoint_eq_of_short_paths (BalancedCubeGirth.eight_le_egirth C hb)
    (pv.isPath_of_length_eq_dist (hpv.trans hd.symm))
    (qz.isPath_of_length_eq_dist (hqz.trans hd.symm)) (by omega)
  have hvLast : pv.getVert p.length = v := by simp [pv, Walk.getVert_append]
  have hzLast : qz.getVert q.length = z := by simp [qz, Walk.getVert_append]
  have hlen : p.length = q.length := by omega
  rw [he,hlen] at hvLast
  exact hvLast.symm.trans hzLast

set_option maxHeartbeats 650000 in
-- Finite neighbor filters are compared under two local names for the induced graph.
private lemma ball_half_internal_and_crossing_eq {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
    let H := univ.filter (fun w : (C : Set (Q 9)) => w.val k ≠ x.val k)
    let W := (univ \ B) \ H
    incidences G H H + 2 * incidences G (H ∩ B) W =
      4 * (H ∩ B).card + incidences G (H \ B) (H \ B) := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B' := HammingSeven.ball G y
  let B := A ∪ B'
  let H := univ.filter (fun w : (C : Set (Q 9)) => w.val k ≠ x.val k)
  let W := (univ \ B) \ H
  have hx : x ∉ H := by simp [H]
  have hy : y ∉ H := by simp [H,hk]
  have hWH : Disjoint W H := sdiff_disjoint
  have hW : W ⊆ univ \ B := sdiff_subset
  let S := H ∩ B
  let U := H \ B
  let rank (v : (C : Set (Q 9))) := min (hammingDist x.val v.val) (hammingDist y.val v.val)
  have hdist (r v : (C : Set (Q 9))) (hv : v ∈ HammingSeven.ball G r) :
      hammingDist r.val v.val ≤ 3 := by
    obtain ⟨p,hp⟩ := HammingSeven.ball_walk hv
    exact (hamming_le_walk p).trans hp
  have rank_x (v : (C : Set (Q 9))) (hv : v ∈ A) : rank v = hammingDist x.val v.val := by
    have h₁ := hdist x v hv
    have h₂ := hammingDist_triangle x.val v.val y.val
    rw [hxy,hammingDist_comm v.val y.val] at h₂
    exact min_eq_left (by omega)
  have rank_y (v : (C : Set (Q 9))) (hv : v ∈ B') : rank v = hammingDist y.val v.val := by
    have h₁ := hdist y v hv
    have h₂ := hammingDist_triangle x.val v.val y.val
    rw [hxy,hammingDist_comm v.val y.val] at h₂
    exact min_eq_right (by omega)
  have hcross {a b : (C : Set (Q 9))} (ha : a ∈ A) (hb : b ∈ B') : ¬G.Adj a b :=
    no_cross_between_distant_balls x y hxy ha hb
  have hdiff : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → rank u ≠ rank v := by
    intro u hu v hv huv he
    rcases mem_union.mp (mem_inter.mp hu).2 with huA | huB <;>
      rcases mem_union.mp (mem_inter.mp hv).2 with hvA | hvB
    · rw [rank_x u huA,rank_x v hvA] at he
      have hadj : (hypercube 9).Adj u.val v.val := huv
      obtain h | h := edge_moves_between_shells (x := x.val) hadj <;> omega
    · exact hcross huA hvB huv
    · exact hcross hvA huB huv.symm
    · rw [rank_y u huB,rank_y v hvB] at he
      have hadj : (hypercube 9).Adj u.val v.val := huv
      obtain h | h := edge_moves_between_shells (x := y.val) hadj <;> omega
  have hU : H = S ∪ U := by ext v; simp [S,U]; tauto
  have hdis : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (mem_sdiff.mp hv').2 (mem_inter.mp hv).2
  have hUW : Disjoint U W := (hWH.symm).mono sdiff_subset (Subset.refl _)
  change incidences G H H + 2 * incidences G S W = 4 * S.card + incidences G U U
  apply internal_and_crossing_incidence_eq G H S U W rank hU hdis hUW hdiff
  intro u hu
  let children := S.filter (fun v => G.Adj u v ∧ rank u < rank v)
  let external := (U ∪ W).filter (G.Adj u)
  have hpred : ∃ v ∈ B, G.Adj u v ∧ rank v < rank u := by
    rcases mem_union.mp (mem_inter.mp hu).2 with huA | huB
    · obtain ⟨v,hv,huv,hlt⟩ := ball_has_predecessor huA
        (fun h => hx (h ▸ (mem_inter.mp hu).1))
      exact ⟨v,mem_union_left _ hv,huv,by rwa [rank_x v hv,rank_x u huA]⟩
    · obtain ⟨v,hv,huv,hlt⟩ := ball_has_predecessor huB
        (fun h => hy (h ▸ (mem_inter.mp hu).1))
      exact ⟨v,mem_union_right _ hv,huv,by rwa [rank_y v hv,rank_y u huB]⟩
  obtain ⟨v,hvB,huv,hlt⟩ := hpred
  have out_of_balls {z : (C : Set (Q 9))} (hz : z ∈ U ∪ W) : z ∉ B :=
    (mem_union.mp hz).elim (fun h => (mem_sdiff.mp h).2) (fun h => (mem_sdiff.mp (hW h)).2)
  have hd : Disjoint children external := by
    apply Finset.disjoint_left.mpr
    intro z hz he
    exact out_of_balls (mem_filter.mp he).1 (mem_inter.mp (mem_filter.mp hz).1).2
  have hvnot : v ∉ children ∪ external := fun h =>
    (mem_union.mp h).elim (fun c => lt_asymm hlt (mem_filter.mp c).2.2)
      (fun ext => out_of_balls (mem_filter.mp ext).1 hvB)
  have hsubset : insert v (children ∪ external) ⊆ G.neighborFinset u := by
    intro z hz
    apply (G.mem_neighborFinset u z).mpr
    rcases mem_insert.mp hz with rfl | hz
    · exact huv
    · exact (mem_union.mp hz).elim (fun h => (mem_filter.mp h).2.1)
        (fun h => (mem_filter.mp h).2)
  have hpredUnique (z : (C : Set (Q 9))) (hzB : z ∈ B) (huz : G.Adj u z)
      (hzlt : rank z < rank u) : z = v := by
    have huB := (mem_inter.mp hu).2
    rcases mem_union.mp huB with hux | huy
    · have hzA : z ∈ A := (mem_union.mp hzB).resolve_right (fun h => hcross hux h huz)
      have hvA : v ∈ A := (mem_union.mp hvB).resolve_right (fun h => hcross hux h huv)
      rw [rank_x z hzA,rank_x u hux] at hzlt
      rw [rank_x v hvA,rank_x u hux] at hlt
      exact ball_predecessor_unique hb hzA hvA (hdist x u hux) huz huv hzlt hlt
    · have hzB' : z ∈ B' := (mem_union.mp hzB).resolve_left (fun h => hcross h huy huz.symm)
      have hvB' : v ∈ B' := (mem_union.mp hvB).resolve_left (fun h => hcross h huy huv.symm)
      rw [rank_y z hzB',rank_y u huy] at hzlt
      rw [rank_y v hvB',rank_y u huy] at hlt
      exact ball_predecessor_unique hb hzB' hvB' (hdist y u huy) huz huv hzlt hlt
  have crossing_lowers (r z : (C : Set (Q 9))) (huz : G.Adj u z)
      (hub : u.val k ≠ r.val k) (hzb : z.val k = r.val k) :
      hammingDist r.val z.val < hammingDist r.val u.val := by
    have hflip : z.val = BalancedCriticalSpectrum.flip u.val k :=
      crossing_neighbor huz (fun h => hub (h.symm.trans hzb))
    have hmem : k ∈ diff u.val r.val := mem_filter.mpr ⟨mem_univ _,hub⟩
    rw [hammingDist_comm r.val z.val,hammingDist_comm r.val u.val]
    change (diff z.val r.val).card < (diff u.val r.val).card
    rw [hflip,diff_flip,ite_eq_left hmem,card_erase_of_mem hmem]
    have hp := card_pos.mpr ⟨k,hmem⟩
    omega
  have upward_in_half (z : (C : Set (Q 9))) (hzB : z ∈ B) (huz : G.Adj u z)
      (hp : rank u < rank z) : z ∈ H := by
    by_contra h
    have hzbit : z.val k = x.val k := by simpa [H] using h
    have hubit := (mem_filter.mp (mem_inter.mp hu).1).2
    rcases mem_union.mp (mem_inter.mp hu).2 with hux | huy
    · have hzA := (mem_union.mp hzB).resolve_right (fun h => hcross hux h huz)
      rw [rank_x u hux,rank_x z hzA] at hp
      exact (not_lt_of_gt hp) (crossing_lowers x z huz hubit hzbit)
    · have hzB' := (mem_union.mp hzB).resolve_left (fun h => hcross h huy huz.symm)
      rw [rank_y u huy,rank_y z hzB'] at hp
      have hubit' : u.val k ≠ y.val k := fun e => hubit (e.trans hk.symm)
      exact (not_lt_of_gt hp) (crossing_lowers y z huz hubit' (hzbit.trans hk))
  have heq : insert v (children ∪ external) = G.neighborFinset u := by
    apply Subset.antisymm hsubset
    intro z hz
    have huz : G.Adj u z := (G.mem_neighborFinset u z).mp hz
    by_cases hzB : z ∈ B
    · have hrank : rank u ≠ rank z := by
        rcases mem_union.mp (mem_inter.mp hu).2 with hux | huy
        · have hzA := (mem_union.mp hzB).resolve_right (fun h => hcross hux h huz)
          rw [rank_x u hux,rank_x z hzA]
          have ha : (hypercube 9).Adj u.val z.val := huz
          obtain h | h := edge_moves_between_shells (x := x.val) ha <;> omega
        · have hzB' := (mem_union.mp hzB).resolve_left (fun h => hcross h huy huz.symm)
          rw [rank_y u huy,rank_y z hzB']
          have ha : (hypercube 9).Adj u.val z.val := huz
          obtain h | h := edge_moves_between_shells (x := y.val) ha <;> omega
      rcases lt_or_gt_of_ne hrank with hp | hp
      · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr
          ⟨mem_inter.mpr ⟨upward_in_half z hzB huz hp,hzB⟩,huz,hp⟩))
      · rw [hpredUnique z hzB huz hp]
        exact mem_insert_self _ _
    · have hzU : z ∈ U ∪ W := by
        by_cases hzH : z ∈ H
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hzH,hzB⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hzB⟩,hzH⟩)
      exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hzU,huz⟩))
  have h := congrArg Finset.card heq
  rw [card_insert_of_notMem hvnot,card_union_of_disjoint hd,
    G.card_neighborFinset_eq_degree,hr.degree_eq] at h
  change children.card + external.card = 2
  omega

#print axioms ball_half_internal_and_crossing_eq

open BalancedCriticalSpectrum (directionEdges direction_edge_count)

private lemma incidence_eq_neighbor_inter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) :
    incidences G S T = ∑ z ∈ S, (G.neighborFinset z ∩ T).card := by
  apply sum_congr rfl
  intro z _
  congr 1
  ext v
  simp only [mem_bipartiteAbove,mem_inter,G.mem_neighborFinset,and_comm]

private lemma cube_cut_incidences {C : Finset (Q 9)} (k : Fin 9) (b : Bool) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let H := univ.filter (fun x : (C : Set (Q 9)) => x.val k ≠ b)
    incidences G H (univ \ H) = directionEdges C k := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let H := univ.filter (fun x : (C : Set (Q 9)) => x.val k ≠ b)
  let F (t : Bool) := C.filter (fun x => x k = t ∧ BalancedCriticalSpectrum.flip x k ∈ C)
  have hpoint (z : (C : Set (Q 9))) (hz : z ∈ H) :
      (G.neighborFinset z ∩ (univ \ H)).card = if BalancedCriticalSpectrum.flip z.val k ∈ C then 1 else 0 := by
    have hbit := (mem_filter.mp hz).2
    by_cases h : BalancedCriticalSpectrum.flip z.val k ∈ C
    · let v : (C : Set (Q 9)) := ⟨BalancedCriticalSpectrum.flip z.val k,h⟩
      have he : G.neighborFinset z ∩ (univ \ H) = {v} := by
        ext a
        simp only [mem_inter,G.mem_neighborFinset,mem_sdiff,mem_univ,true_and,mem_singleton]
        constructor
        · rintro ⟨hadj,ha⟩
          have hae : a.val k = b := by simpa [H] using ha
          have hneq : a.val k ≠ z.val k := fun h => hbit (h.symm.trans hae)
          exact Subtype.ext (crossing_neighbor hadj hneq)
        · rintro rfl
          refine ⟨BalancedCriticalSpectrum.flip_adj _ _,?_⟩
          cases hb : b <;> cases hz' : z.val k <;> simp_all [H,v]
      rw [he,card_singleton,ite_eq_left h]
    · have he : G.neighborFinset z ∩ (univ \ H) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haN,haO⟩ := mem_inter.mp ha
        have hae : a.val k = b := by simpa [H] using (mem_sdiff.mp haO).2
        have hneq : a.val k ≠ z.val k := fun h => hbit (h.symm.trans hae)
        have he := crossing_neighbor ((G.mem_neighborFinset z a).mp haN) hneq
        exact h (he ▸ a.property)
      rw [he,card_empty,ite_eq_right h]
  have hcount : (H.filter (fun z => BalancedCriticalSpectrum.flip z.val k ∈ C)).card = (F (!b)).card := by
    apply card_bij (fun z _ => z.val)
    · intro z hz
      obtain ⟨hzH,hcross⟩ := mem_filter.mp hz
      have hbit := (mem_filter.mp hzH).2
      refine mem_filter.mpr ⟨z.property,?_,hcross⟩
      change z.val k ≠ b at hbit
      exact Bool.eq_not_of_ne hbit
    · intro a _ z _ h
      exact Subtype.ext h
    · intro z hz
      obtain ⟨hzC,hbit,hcross⟩ := mem_filter.mp hz
      refine ⟨⟨z,hzC⟩,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,hcross⟩,rfl⟩
      cases b <;> simp_all
  have hswap : (F true).card = (F false).card := by
    apply card_bij (fun z _ => BalancedCriticalSpectrum.flip z k)
    · intro z hz
      obtain ⟨hzC,hb,hf⟩ := mem_filter.mp hz
      simp [F,hb,hf,hzC]
    · intro a _ z _ h
      have he := congrArg (fun x => BalancedCriticalSpectrum.flip x k) h
      simpa using he
    · intro z hz
      obtain ⟨hzC,hb,hf⟩ := mem_filter.mp hz
      exact ⟨BalancedCriticalSpectrum.flip z k,by simp [F,hb,hf,hzC],by simp⟩
  change incidences G H (univ \ H) = (F false).card
  rw [incidence_eq_neighbor_inter]
  calc
    _ = ∑ z ∈ H, if BalancedCriticalSpectrum.flip z.val k ∈ C then 1 else 0 := sum_congr rfl hpoint
    _ = (H.filter (fun z => BalancedCriticalSpectrum.flip z.val k ∈ C)).card := (card_filter _ _).symm
    _ = (F false).card := by rw [hcount]; cases b <;> simp_all

#print axioms cube_cut_incidences

open private isolated_crossing_card_le_degree_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualMatchingProbe
open private residual_opposite_half_has_no_isolated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualHalfProbe

private lemma sum_incidence_eq_const_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) (d : ℕ)
    (h : ∀ z ∈ S, (G.neighborFinset z ∩ T).card = d) :
    incidences G S T = d * S.card := by
  rw [incidence_eq_neighbor_inter]
  calc
    _ = ∑ _z ∈ S, d := sum_congr rfl h
    _ = _ := by simp [Nat.mul_comm]

open private sixty_six_distance_eight_residual from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualProbe
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

set_option maxHeartbeats 1100000 in
-- Degree sums and parity filters repeatedly normalize the induced graph on the support.
private lemma cross_from_residual_bound {C : Finset (Q 9)}
    (hc : C.card = 66) (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
    let R := univ \ B
    let H := univ.filter (fun w : (C : Set (Q 9)) => w.val k ≠ x.val k)
    let W := R \ H
    let P := R ∩ paritySide C (cubeParity x.val)
    let T := R ∩ paritySide C (!cubeParity x.val)
    incidences G (H ∩ B) W + (P ∩ H).card ≤
      incidences G (P \ H) (T \ H) + incidences G (P ∩ H) T := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
  let R := univ \ B
  let H := univ.filter (fun w : (C : Set (Q 9)) => w.val k ≠ x.val k)
  let P := R ∩ paritySide C (cubeParity x.val)
  let T := R ∩ paritySide C (!cubeParity x.val)
  let U := P ∩ H
  let W := R \ H
  let S := H ∩ B
  let d (w : (C : Set (Q 9))) := (G.neighborFinset w ∩ R).card
  let crossing := W.filter (fun w => (G.neighborFinset w ∩ S).Nonempty)
  let Q0 := crossing.filter (fun w => d w = 0)
  let Qp := crossing.filter (fun w => d w ≠ 0)
  let M := (R ∩ H).filter (fun w => d w = 2)
  obtain ⟨_,_,hT⟩ := sixty_six_distance_eight_residual hc hr hb x y hxy
  change ∀ w ∈ T, G.neighborFinset w ⊆ P at hT
  have hPR : P ⊆ R := inter_subset_left
  have hTR : T ⊆ R := inter_subset_left
  have hpar (w : (C : Set (Q 9))) :
      cubeParity w.val ≠ cubeParity x.val ↔ cubeParity w.val = !cubeParity x.val := by
    cases cubeParity w.val <;> cases cubeParity x.val <;> decide
  have hroot {w : (C : Set (Q 9))} (hw : w ∈ R) (hn : w ∉ T) : w ∈ P := by
    refine mem_inter.mpr ⟨hw,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    by_contra h
    exact hn (mem_inter.mpr ⟨hw,mem_filter.mpr ⟨mem_univ _,(hpar w).mp h⟩⟩)
  have hPT (w : (C : Set (Q 9))) (hw : w ∈ P) :
      G.neighborFinset w ∩ R = G.neighborFinset w ∩ T := by
    ext z
    constructor
    · intro hz
      obtain ⟨hn,hr'⟩ := mem_inter.mp hz
      have he := (mem_filter.mp (mem_inter.mp hw).2).2
      have hadj : G.Adj w z := (G.mem_neighborFinset w z).mp hn
      have hzpar : cubeParity z.val ≠ cubeParity x.val :=
        fun h => cubeParity_ne_of_adj hadj (he.trans h.symm)
      exact mem_inter.mpr ⟨hn,mem_inter.mpr
        ⟨hr',mem_filter.mpr ⟨mem_univ _,(hpar z).mp hzpar⟩⟩⟩
    · intro hz
      exact mem_inter.mpr ⟨(mem_inter.mp hz).1,hTR (mem_inter.mp hz).2⟩
  have hMsub : M ⊆ U.filter (fun w => d w = 2) := by
    intro w hw
    obtain ⟨hwU,h2⟩ := mem_filter.mp hw
    obtain ⟨hwR,hwH⟩ := mem_inter.mp hwU
    have hn : w ∉ T := by
      intro h
      have he : G.neighborFinset w ∩ R = G.neighborFinset w :=
        inter_eq_left.mpr ((hT w h).trans hPR)
      change (G.neighborFinset w ∩ R).card = 2 at h2
      rw [he,G.card_neighborFinset_eq_degree,hr.degree_eq] at h2
      omega
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨hroot hwR hn,hwH⟩,h2⟩
  have hQ (w : (C : Set (Q 9))) (hw : w ∈ W) :
      (G.neighborFinset w ∩ S).card ≤ 1 := by
    apply card_le_one.mpr
    intro v hv z hz
    have hwbit : w.val k = x.val k := by simpa [H] using (mem_sdiff.mp hw).2
    have he {a : (C : Set (Q 9))} (ha : a ∈ G.neighborFinset w ∩ S) :
        a.val = BalancedCriticalSpectrum.flip w.val k := by
      apply crossing_neighbor ((G.mem_neighborFinset w a).mp (mem_inter.mp ha).1)
      have habit := (mem_filter.mp (mem_inter.mp (mem_inter.mp ha).2).1).2
      exact fun h => habit (h.trans hwbit)
    exact Subtype.ext ((he hv).trans (he hz).symm)
  have hq : incidences G S W = crossing.card := by
    rw [incidences_symm,incidence_eq_neighbor_inter,card_filter]
    apply sum_congr rfl
    intro w hw
    have hle := hQ w hw
    change (G.neighborFinset w ∩ S).card =
      (if (G.neighborFinset w ∩ S).Nonempty then 1 else 0)
    by_cases h : (G.neighborFinset w ∩ S).Nonempty
    · have hp := card_pos.mpr h
      rw [ite_eq_left h]
      omega
    · exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)).trans (ite_eq_right h).symm
  have hparts : crossing.card = Q0.card + Qp.card := by
    have h := card_filter_add_card_filter_not (s := crossing) (fun w => d w = 0)
    exact h.symm
  have hzero : Q0.card ≤ M.card := by
    have h := isolated_crossing_card_le_degree_two hr hb x y hxy k hk
    change (R.filter (fun w => w.val k = x.val k ∧ d w = 0 ∧
      ∃ z ∈ B, G.Adj z w ∧ z.val k ≠ x.val k)).card ≤
        (R.filter (fun a => a.val k ≠ x.val k ∧ d a = 2)).card at h
    have e0 : Q0 = R.filter (fun w => w.val k = x.val k ∧ d w = 0 ∧
        ∃ z ∈ B, G.Adj z w ∧ z.val k ≠ x.val k) := by
      ext w
      simp only [Q0,crossing,W,S,H,mem_filter,mem_sdiff,mem_inter,mem_univ,true_and,
        not_not,Finset.Nonempty,G.mem_neighborFinset]
      constructor
      · rintro ⟨⟨⟨hw,hwbit⟩,⟨z,hzw,hzbit,hzB⟩⟩,hz0⟩
        exact ⟨hw,hwbit,hz0,z,hzB,hzw.symm,hzbit⟩
      · rintro ⟨hw,hwbit,hw0,z,hzB,hzw,hzbit⟩
        exact ⟨⟨⟨hw,hwbit⟩,⟨z,hzw.symm,hzbit,hzB⟩⟩,hw0⟩
    have eM : M = R.filter (fun a => a.val k ≠ x.val k ∧ d a = 2) := by
      ext w
      simp only [M,H,mem_filter,mem_inter,mem_univ,true_and,and_assoc]
    rwa [← e0,← eM] at h
  have hQp : Qp ⊆ P \ H := by
    intro w hw
    obtain ⟨hwW,hn⟩ := mem_filter.mp (mem_filter.mp hw).1
    obtain ⟨z,hz⟩ := hn
    have hzN := (mem_inter.mp hz).1
    have hzB := (mem_inter.mp (mem_inter.mp hz).2).2
    have hwP : w ∈ P := hroot (mem_sdiff.mp hwW).1
      (fun h => (mem_sdiff.mp (hPR (hT w h hzN))).2 hzB)
    exact mem_sdiff.mpr ⟨hwP,(mem_sdiff.mp hwW).2⟩
  have hpos : Qp.card ≤ incidences G (P \ H) (T \ H) := by
    rw [incidence_eq_neighbor_inter]
    calc
      _ = ∑ _w ∈ Qp, (1 : ℕ) := by simp
      _ ≤ ∑ w ∈ Qp, (G.neighborFinset w ∩ (T \ H)).card := by
        apply sum_le_sum
        intro w hw
        obtain ⟨hwQ,hd⟩ := mem_filter.mp hw
        obtain ⟨hwW,hattach⟩ := mem_filter.mp hwQ
        have hwbit : w.val k = x.val k := by simpa [H] using (mem_sdiff.mp hwW).2
        obtain ⟨z,hz⟩ := hattach
        have hzd := (mem_inter.mp hz).2
        have hzbit := (mem_filter.mp (mem_inter.mp hzd).1).2
        have hzEq : z.val = BalancedCriticalSpectrum.flip w.val k :=
          crossing_neighbor ((G.mem_neighborFinset w z).mp (mem_inter.mp hz).1)
            (fun h => hzbit (h.trans hwbit))
        have hs : G.neighborFinset w ∩ R ⊆ G.neighborFinset w ∩ (T \ H) := by
          rw [hPT w (mem_sdiff.mp (hQp hw)).1]
          intro a ha
          obtain ⟨haN,haT⟩ := mem_inter.mp ha
          have haR := hTR haT
          refine mem_inter.mpr ⟨haN,mem_sdiff.mpr ⟨haT,?_⟩⟩
          intro haH
          have haBit := (mem_filter.mp haH).2
          have haEq : a.val = BalancedCriticalSpectrum.flip w.val k :=
            crossing_neighbor ((G.mem_neighborFinset w a).mp haN)
              (fun h => haBit (h.trans hwbit))
          have he : a = z := Subtype.ext (haEq.trans hzEq.symm)
          exact (mem_sdiff.mp haR).2 (he ▸ (mem_inter.mp hzd).2)
        exact (Nat.pos_of_ne_zero hd).trans_le (card_le_card hs)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        hQp (fun _ _ _ => Nat.zero_le _)
  have hdelta : (U.filter (fun w => d w = 2)).card + U.card ≤ incidences G U T := by
    rw [incidence_eq_neighbor_inter,card_filter,card_eq_sum_ones,← sum_add_distrib]
    apply sum_le_sum
    intro w hw
    have hwP := (mem_inter.mp hw).1
    have hwR := hPR hwP
    have hwH := (mem_filter.mp (mem_inter.mp hw).2).2
    have hd : 0 < d w := residual_opposite_half_has_no_isolated hc hr hb x y hxy k hk w hwR hwH
    have ht : (G.neighborFinset w ∩ T).card = d w :=
      congrArg Finset.card (hPT w hwP).symm
    exact le_trans (show (if d w = 2 then 1 else 0) + 1 ≤ d w by
      split_ifs <;> omega) ht.ge
  change incidences G S W + U.card ≤ incidences G (P \ H) (T \ H) + incidences G U T
  have hM := card_le_card hMsub
  omega

#print axioms cross_from_residual_bound
