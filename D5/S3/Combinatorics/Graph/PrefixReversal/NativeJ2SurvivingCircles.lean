/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingCircles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingCircles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual native-circle survival and exact lower and contact ownership. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingSeams
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open Equiv Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

open private first_a_cut second_a_cut from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels

open private surviving_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

private theorem j2_edge_generator_unique {m : Nat} (x y g h : Configuration m)
    (hg : g * g = 1) (he : s(x, x * g) = s(y, y * h)) : g = h := by
  rcases Sym2.eq_iff.mp he with ⟨hxy, hend⟩ | ⟨hxy, hend⟩
  · subst y
    exact mul_left_cancel hend
  · rw [← hend] at hxy
    have hgh : g * h = 1 := mul_left_cancel (by
      simpa only [mul_assoc, mul_one] using hxy.symm)
    have ht := congrArg (g * ·) hgh
    simpa only [← mul_assoc, hg, one_mul, mul_one] using ht.symm

/-- Every actual c step avoids all six marked b cuts, regardless of its owner. -/
private theorem j2_c_not_marked {m : Nat} (hm : 5 ≤ m) (x : Configuration m) :
    ¬ MarkedCut m s(x, x * c m) := by
  rintro ⟨p, he⟩
  rw [native_j2_marked_edge] at he
  have hcb : c m = b m := j2_edge_generator_unique _ _ _ _ (c_sq m) he
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hv := congrArg (fun f : Configuration m => (f i).val) hcb
  simp only [c_apply, b_apply, i, lt_self_iff_false, if_false, Nat.sub_self] at hv
  rw [if_pos (by omega : m - 1 < m)] at hv
  omega

private theorem j2_c_ne_one {m : Nat} (hm : 5 ≤ m) : c m ≠ 1 := by
  intro he
  have hv := congrArg (fun z : Configuration m => (z ⟨0, by omega⟩).val) he
  simp only [c_apply, Fin.val_mk, Equiv.Perm.one_apply,
    if_pos (by omega : 0 < m - 1)] at hv
  omega

/-- All the above seam witnesses produce edges in the very same independent
F2-minus-six-cuts graph used by the actual component theorem. -/
private theorem j2_c_survives {m : Nat} (hm : 5 ≤ m) (x : Configuration m)
    (hs : F2Seam m s(x, x * c m)) :
    (survivingGraph m).Adj x (x * c m) := by
  apply (surviving_adj_iff m x (x * c m)).mpr
  refine ⟨⟨Or.inr hs, j2_c_not_marked hm x⟩, ?_⟩
  intro he
  apply j2_c_ne_one hm
  exact mul_left_cancel (by simpa only [mul_one] using he.symm)


private def j2_h_contact_index {m : ℕ} (hm : 5 ≤ m) : Fin (m - 2) :=
  ⟨m - 3, by omega⟩

private theorem j2_h_cut_domain {m : ℕ} (hm : 5 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m)
    (hv : Circle (NativeCoreSplicing.cutStart p) v) : CoreDomain m v := by
  have hp := (native_cut_circle_iff (by omega : 4 ≤ m) p v).mp hv
  exact (native_t_circle_partition (by omega : 4 ≤ m) v).mpr
    ⟨p, hp, fun q hq => native_t_circle_owner_unique (by omega : 4 ≤ m) v q p hq hp⟩

private theorem j2_h_gap_star {m : ℕ} (hm : 5 ≤ m) (j : Fin (m - 2))
    (i : Fin m) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v) :
    SupplierStar (contactAnchor j) v :=
  (native_star_circle_partition (by omega : 3 ≤ m) (contactAnchor j) v).mpr ⟨i, hv⟩

private theorem j2_h_lower_star {m : ℕ} (hm : 5 ≤ m) (j : Fin (m - 2))
    (v : Configuration m) (hv : Circle (lowerPort j) v) :
    SupplierStar (a m * c m) v := by
  apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) v).mpr
  exact ⟨⟨j.val, by have hj := j.isLt; omega⟩, hv⟩

private theorem j2_h_gap_no_core {m : ℕ} (hm : 5 ≤ m) (j : Fin (m - 2))
    (i : Fin m) (hi : i.val ≠ 0) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v) : ¬ CoreDomain m v := by
  intro hcore
  have hc := (contact_star_core_intersection (by omega : 4 ≤ m) j v).mp
    ⟨hcore, j2_h_gap_star hm j i v hv⟩
  let zero : Fin m := ⟨0, by omega⟩
  have hz : gapAnchor (contactAnchor j) zero = contactAnchor j := by
    simp [gapAnchor, zero]
  have hzero : Circle (gapAnchor (contactAnchor j) zero) v := hz ▸ hc
  exact Set.disjoint_left.mp (native_circle_gap_disjoint (by omega : 3 ≤ m)
    (contactAnchor j) (by intro he; exact hi (congrArg Fin.val he))) hv hzero

private theorem j2_h_gap_owner_unique {m : ℕ} (hm : 5 ≤ m)
    (j k : Fin (m - 2)) (i l : Fin m) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v)
    (hw : Circle (gapAnchor (contactAnchor k) l) v) : j = k ∧ i = l := by
  have hjk : j = k := by
    by_contra hne
    exact Set.disjoint_left.mp (contact_stars_pairwise_disjoint j k hne)
      (j2_h_gap_star hm j i v hv) (j2_h_gap_star hm k l v hw)
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (native_circle_gap_disjoint (by omega : 3 ≤ m)
    (contactAnchor j) hne) hv hw

/-- The actual six marked edges have owners only in the last three lower
circles or in gaps zero, m-1, m-2 of the final contact supplier. -/
private theorem j2_h_marked_owner_inventory {m : ℕ} (hm : 5 ≤ m)
    (q : Fin 3 × Bool) :
    (∃ i : Fin m, m - 3 ≤ i.val ∧
      Circle (NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)))
        (port m (q.1, q.2, false))) ∨
    ∃ i : Fin m, (i.val = 0 ∨ i.val = m - 1 ∨ i.val = m - 2) ∧
      Circle (gapAnchor (contactAnchor (j2_h_contact_index hm)) i)
        (port m (q.1, q.2, false)) := by
  have hp := native_j2_port_circle hm (q.1, q.2, false)
  rcases q with ⟨r, t⟩
  fin_cases r <;> cases t <;> simp only [rightOwner, Fin.val_mk] at hp
  · left
    refine ⟨⟨m - 1, by omega⟩, by simp only [Fin.val_mk]; omega, ?_⟩
    rw [(first_a_cut (by omega : 4 ≤ m)).1]
    exact hp
  · left
    refine ⟨⟨m - 2, by omega⟩, by simp only [Fin.val_mk]; omega, ?_⟩
    rw [(second_a_cut (by omega : 4 ≤ m)).1]
    exact hp
  · right
    refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
    simp only [gapAnchor, Fin.val_mk, pow_zero, mul_one]
    exact hp
  · left
    refine ⟨⟨m - 3, by omega⟩, le_rfl, ?_⟩
    simp only [NativeCoreSplicing.cutStart, Fin.val_mk,
      if_neg (by omega : m - 3 ≠ m - 1), tCircleAnchor, gapAnchor,
      lowerPort, j2_h_contact_index]
    exact hp
  · right
    exact ⟨⟨m - 1, by omega⟩, Or.inr (Or.inl rfl), hp⟩
  · right
    exact ⟨⟨m - 2, by omega⟩, Or.inr (Or.inr rfl), hp⟩

private theorem j2_h_lower_domain {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (v : Configuration m)
    (hv : Circle (lowerPort j) v) : F2Domain m v := by
  left
  apply j2_h_cut_domain hm (.inl ⟨j.val, by have h := j.isLt; omega⟩) v
  simpa only [NativeCoreSplicing.cutStart, Fin.val_mk,
    if_neg (by have h := j.isLt; omega : j.val ≠ m - 1), tCircleAnchor, gapAnchor, lowerPort] using hv

private theorem j2_h_lower_deleted {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (e : Sym2 (Configuration m))
    (he : NativeCircleEdge (lowerPort j) e) (hd : F2DeletedEdge m e) :
    e = s(lowerPort j, lowerPort j * b m) := by
  rcases hd with ⟨p, hp⟩ | ⟨k, i, hki⟩
  · have hv := native_circle_edge_endpoint (lowerPort j)
      (NativeCoreSplicing.cutStart p) e he (hp ▸ Sym2.mem_mk_left _ _)
    let q : Fin m ⊕ Fin (m - 2) := .inl ⟨j.val, by have h := j.isLt; omega⟩
    have hq : Circle (tCircleAnchor q) (NativeCoreSplicing.cutStart p) := hv
    have hqp : q = p := native_t_circle_owner_unique (by omega : 4 ≤ m)
      (NativeCoreSplicing.cutStart p) q p hq
      ((native_cut_circle_iff (by omega : 4 ≤ m) p _).mp (Or.inl rfl))
    rw [← hqp] at hp
    simpa only [q, NativeCoreSplicing.cutStart, cutGenerator, Fin.val_mk,
      if_neg (by have h := j.isLt; omega : j.val ≠ m - 1),
      if_neg (by have h := j.isLt; omega : ¬ m - 2 ≤ j.val),
      tCircleAnchor, gapAnchor, lowerPort] using hp
  · have hv := native_circle_edge_endpoint (lowerPort j)
      (gapAnchor (contactAnchor k) i) e he (hki ▸ Sym2.mem_mk_left _ _)
    exact (Set.disjoint_left.mp (contact_star_lower_disjoint (by omega : 4 ≤ m) k)
      (j2_h_gap_star hm k i _ (Or.inl rfl)) (j2_h_lower_star hm j _ hv)).elim

private theorem j2_h_lower_unmarked {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (hj : j.val < m - 3) (q : Fin 3 × Bool) :
    ¬ Circle (lowerPort j) (port m (q.1, q.2, false)) := by
  intro hv
  rcases j2_h_marked_owner_inventory hm q with ⟨i, hi, howner⟩ | ⟨i, _, howner⟩
  · let p : Fin m ⊕ Fin (m - 2) := .inl ⟨j.val, by have h := j.isLt; omega⟩
    have hp : Circle (tCircleAnchor p) (port m (q.1, q.2, false)) := hv
    have he := native_t_circle_owner_unique (by omega : 4 ≤ m) _ p (.inl i) hp
      ((native_cut_circle_iff (by omega : 4 ≤ m) (.inl i) _).mp howner)
    have hi' : j.val = i.val := congrArg
      (fun x : Fin m ⊕ Fin (m - 2) => x.elim Fin.val Fin.val) he
    omega
  · exact Set.disjoint_left.mp
      (contact_star_lower_disjoint (by omega : 4 ≤ m) (j2_h_contact_index hm))
      (j2_h_gap_star hm _ i _ howner) (j2_h_lower_star hm j _ hv)

private theorem j2_h_newgap_domain {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor (j2_h_contact_index hm)) i) v) :
    F2Domain m v := by
  right
  exact ⟨j2_h_contact_index hm, by simp only [j2_h_contact_index, Fin.val_mk]; omega,
    j2_h_gap_star hm _ i v hv⟩

private theorem j2_h_newgap_deleted {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (hi : i.val ≠ 0) (e : Sym2 (Configuration m))
    (he : NativeCircleEdge (gapAnchor (contactAnchor (j2_h_contact_index hm)) i) e)
    (hd : F2DeletedEdge m e) :
    e = s(gapAnchor (contactAnchor (j2_h_contact_index hm)) i,
      gapAnchor (contactAnchor (j2_h_contact_index hm)) i * b m) := by
  rcases hd with ⟨p, hp⟩ | ⟨k, l, hkl⟩
  · have hv := native_circle_edge_endpoint _ (NativeCoreSplicing.cutStart p) e he
      (hp ▸ Sym2.mem_mk_left _ _)
    exact (j2_h_gap_no_core hm _ i hi _ hv
      (j2_h_cut_domain hm p _ (Or.inl rfl))).elim
  · have hv := native_circle_edge_endpoint _ (gapAnchor (contactAnchor k) l) e he
      (hkl ▸ Sym2.mem_mk_left _ _)
    obtain ⟨hjk, hil⟩ := j2_h_gap_owner_unique hm (j2_h_contact_index hm) k i l _
      hv (Or.inl rfl)
    subst k
    subst l
    exact hkl

private theorem j2_h_newgap_unmarked {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (hi0 : 1 ≤ i.val) (hi : i.val ≤ m - 3) (q : Fin 3 × Bool) :
    ¬ Circle (gapAnchor (contactAnchor (j2_h_contact_index hm)) i)
      (port m (q.1, q.2, false)) := by
  intro hv
  rcases j2_h_marked_owner_inventory hm q with ⟨l, _, howner⟩ | ⟨l, hl, howner⟩
  · exact j2_h_gap_no_core hm _ i (by omega) _ hv
      (j2_h_cut_domain hm (.inl l) _ howner)
  · obtain ⟨_, hil⟩ := j2_h_gap_owner_unique hm (j2_h_contact_index hm)
      (j2_h_contact_index hm) i l _ hv howner
    have hval : i.val = l.val := congrArg Fin.val hil
    rcases hl with hl | hl | hl <;> omega

private theorem native_b_complement_survives {m : ℕ} (hm : 5 ≤ m)
    (z : Configuration m)
    (hdomain : ∀ x, Circle z x → F2Domain m x)
    (hdeleted : ∀ e, NativeCircleEdge z e → F2DeletedEdge m e → e = s(z, z * b m))
    (hmarked : ∀ p : Fin 3 × Bool, ¬ Circle z (port m (p.1, p.2, false))) :
    ∃ w : (survivingGraph m).Walk z (z * b m),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        w.support = List.scanl (· * ·) z (uWord m m) ∧
        ∀ x, x ∈ w.support ↔ Circle z x := by
  classical
  obtain ⟨raw, hpath, hlength, hsupport, hcircle⟩ :=
    native_b_complement (by omega : 3 ≤ m) z
  let q := raw.mapLe (SimpleGraph.deleteEdges_le _)
  have hqpath : q.IsPath := hpath.mapLe _
  have hqlength : q.length = 2 * (m + 1) - 1 := by simpa [q] using hlength
  have hqsupport : q.support = List.scanl (· * ·) z (uWord m m) := by
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hsupport
  have hqcircle : ∀ x, x ∈ q.support ↔ Circle z x := by
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hcircle
  have hinventory := native_complement_full_edge_inventory
    (by omega : 3 ≤ m) z (b m) (Or.inr rfl) q hqpath hqlength hqcircle
  have htransfer : ∀ e, e ∈ q.edges → e ∈ (survivingGraph m).edgeSet := by
    intro e he
    obtain ⟨hnative, hcut⟩ := (hinventory e).mp he
    have hf2native : F2NativeEdge m e := by
      obtain ⟨x, g, hx, hg, hxe⟩ := hnative
      exact (native_f2_native_edge_catalog (by omega : 4 ≤ m) e).mpr
          ⟨x, g, hdomain x hx, hg, hxe⟩
    have hnotdeleted : ¬ F2DeletedEdge m e := fun hd => hcut (hdeleted e hnative hd)
    have hnotmarked : ¬ MarkedCut m e := by
      rintro ⟨p, hp⟩
      apply hmarked p
      apply native_circle_edge_endpoint z _ e hnative
      rw [hp]
      exact Sym2.mem_mk_left _ _
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    change (survivingGraph m).Adj x y
    exact (surviving_adj_iff m x y).mpr
      ⟨⟨Or.inl ⟨hf2native, hnotdeleted⟩, hnotmarked⟩, (q.adj_of_mem_edges he).ne⟩
  let w := q.transfer (survivingGraph m) htransfer
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    simpa only [w, SimpleGraph.Walk.support_transfer] using hqpath.support_nodup
  · simpa only [w, SimpleGraph.Walk.length_transfer] using hqlength
  · simpa only [w, SimpleGraph.Walk.support_transfer] using hqsupport
  · simpa only [w, SimpleGraph.Walk.support_transfer] using hqcircle


private theorem j2_h_lower_survives {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (hj : j.val < m - 3) :
    ∃ w : (survivingGraph m).Walk (lowerPort j) (lowerPort j * b m),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        w.support = List.scanl (· * ·) (lowerPort j) (uWord m m) ∧
        ∀ x, x ∈ w.support ↔ Circle (lowerPort j) x :=
  native_b_complement_survives hm (lowerPort j) (j2_h_lower_domain hm j)
    (j2_h_lower_deleted hm j) (j2_h_lower_unmarked hm j hj)

private theorem j2_h_newgap_survives {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (hi0 : 1 ≤ i.val) (hi : i.val ≤ m - 3) :
    ∃ w : (survivingGraph m).Walk
        (gapAnchor (contactAnchor (j2_h_contact_index hm)) i)
        (gapAnchor (contactAnchor (j2_h_contact_index hm)) i * b m),
      w.IsPath ∧ w.length = 2 * (m + 1) - 1 ∧
        w.support = List.scanl (· * ·)
          (gapAnchor (contactAnchor (j2_h_contact_index hm)) i) (uWord m m) ∧
        ∀ x, x ∈ w.support ↔ Circle
          (gapAnchor (contactAnchor (j2_h_contact_index hm)) i) x :=
  native_b_complement_survives hm _ (j2_h_newgap_domain hm i)
    (j2_h_newgap_deleted hm i (by omega)) (j2_h_newgap_unmarked hm i hi0 hi)

private theorem scanl_chain_cons {m : ℕ} (G : SimpleGraph (Configuration m))
    (z g : Configuration m) (l : List (Configuration m))
    (hg : G.Adj z (z * g))
    (hl : (List.scanl (· * ·) (z * g) l).IsChain G.Adj) :
    (List.scanl (· * ·) z (g :: l)).IsChain G.Adj := by
  rw [List.scanl_cons, List.isChain_cons]
  refine ⟨?_, hl⟩
  intro y hy
  simp only [List.head?_scanl, Option.mem_some_iff] at hy
  subst y
  exact hg

/- UNCOMPILED private-consumer candidate, to be pasted after scanl_chain_cons.
It supplies literal short U/AB scanl chains once their actual coordinate
edges are established in survivingGraph, without assuming a path or using
the graph's degree bound. The C row has TWO F2 b cuts, at rotations 0,m-1;
the marked b edge has rotation m. Its B range 1..m-2 avoids all three.
-/


end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
