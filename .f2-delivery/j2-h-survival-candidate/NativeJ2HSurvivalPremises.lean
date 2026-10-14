import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory

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
  fin_cases r <;> cases t
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
    simpa only [gapAnchor, Fin.val_mk, pow_zero, mul_one] using hp
  · left
    refine ⟨⟨m - 3, by omega⟩, le_rfl, ?_⟩
    simpa only [NativeCoreSplicing.cutStart, Fin.val_mk,
      if_neg (by omega : m - 3 ≠ m - 1), tCircleAnchor, gapAnchor, lowerPort] using hp
  · right
    exact ⟨⟨m - 1, by omega⟩, Or.inr (Or.inl rfl), hp⟩
  · right
    exact ⟨⟨m - 2, by omega⟩, Or.inr (Or.inr rfl), hp⟩

private theorem j2_h_lower_domain {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (hj : j.val < m - 3) (v : Configuration m)
    (hv : Circle (lowerPort j) v) : F2Domain m v := by
  left
  apply j2_h_cut_domain hm (.inl ⟨j.val, by have h := j.isLt; omega⟩) v
  simpa only [NativeCoreSplicing.cutStart, Fin.val_mk,
    if_neg (by omega : j.val ≠ m - 1), tCircleAnchor, gapAnchor, lowerPort] using hv

private theorem j2_h_lower_deleted {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (hj : j.val < m - 3) (e : Sym2 (Configuration m))
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
      if_neg (by omega : j.val ≠ m - 1), if_neg (by omega : ¬ m - 2 ≤ j.val),
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

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
