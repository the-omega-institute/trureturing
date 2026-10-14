/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual F2 cycle has exactly its uncut native circles and literal seams. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeInventory
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreEdgeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreEdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeInventory

/-- All original native edges of the disjoint core and new complete circles. -/
def F2NativeEdge (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  (∃ p : Fin m ⊕ Fin (m - 2), NativeCircleEdge (cutStart p) e) ∨
    ∃ j : Fin (m - 2), ∃ i : Fin m, i.val ≠ 0 ∧
      NativeCircleEdge (gapAnchor (contactAnchor j) i) e

/-- The complete literal old-edge cut set: all T cuts, and one b cut at
every gap of every remaining supplier, including its gap-zero contact. -/
def F2DeletedEdge (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  CoreDeletedEdge m e ∨ ∃ j : Fin (m - 2), ∃ i : Fin m,
    e = s(gapAnchor (contactAnchor j) i, gapAnchor (contactAnchor j) i * b m)

/-- All actual T and E connections, specified without a chosen cycle. -/
def F2Seam (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  TSeam m e ∨ ∃ j : Fin (m - 2), ESeam (contactAnchor j) e

private def ContactDeleted (m k : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ∃ j : Fin (m - 2), j.val < k ∧ e = s(contactAnchor j, contactAnchor j * b m)

private def FlatPartial (m k : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ((CoreUncut m e ∨ TSeam m e) ∧ ¬ ContactDeleted m k e) ∨
    ∃ j : Fin (m - 2), j.val < k ∧ (NewUncut (contactAnchor j) e ∨ ESeam (contactAnchor j) e)

private theorem core_circle_in_domain {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m) (hv : Circle (cutStart p) v) :
    CoreDomain m v := by
  have hp := (native_cut_circle_iff hm p v).mp hv
  exact (native_t_circle_partition hm v).mpr
    ⟨p, hp, fun q hq => native_t_circle_owner_unique hm v q p hq hp⟩

private theorem gap_in_star {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (i : Fin m) (v : Configuration m) (hv : Circle (gapAnchor (contactAnchor j) i) v) :
    SupplierStar (contactAnchor j) v :=
  (native_star_circle_partition (by omega : 3 ≤ m) (contactAnchor j) v).mpr ⟨i, hv⟩

private theorem new_circle_no_core {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (i : Fin m) (hi : i.val ≠ 0) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v) : ¬ CoreDomain m v := by
  intro hcore
  have hc := (contact_star_core_intersection hm j v).mp ⟨hcore, gap_in_star hm j i v hv⟩
  let zero : Fin m := ⟨0, by omega⟩
  have hz : gapAnchor (contactAnchor j) zero = contactAnchor j := by simp [gapAnchor, zero]
  have hzero : Circle (gapAnchor (contactAnchor j) zero) v := hz ▸ hc
  exact Set.disjoint_left.mp (native_circle_gap_disjoint (by omega : 3 ≤ m)
    (contactAnchor j) (by intro he; exact hi (congrArg Fin.val he))) hv hzero

private theorem new_circle_owner_unique {m : ℕ} (hm : 4 ≤ m)
    (j k : Fin (m - 2)) (i l : Fin m) (v : Configuration m)
    (hv : Circle (gapAnchor (contactAnchor j) i) v)
    (hw : Circle (gapAnchor (contactAnchor k) l) v) : j = k ∧ i = l := by
  have hjk : j = k := by
    by_contra hne
    exact Set.disjoint_left.mp (contact_stars_pairwise_disjoint j k hne)
      (gap_in_star hm j i v hv) (gap_in_star hm k l v hw)
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (native_circle_gap_disjoint (by omega : 3 ≤ m)
    (contactAnchor j) hne) hv hw

private theorem edge_generator_unique {m : ℕ} (x y g h : Configuration m)
    (hg : g * g = 1) (he : s(x, x * g) = s(y, y * h)) : g = h := by
  rcases Sym2.eq_iff.mp he with ⟨hxy, hend⟩ | ⟨hxy, hend⟩
  · subst y
    exact mul_left_cancel hend
  · rw [← hend] at hxy
    have hgh : g * h = 1 := mul_left_cancel (by
      simpa only [mul_assoc, mul_one] using hxy.symm)
    have ht := congrArg (g * ·) hgh
    simpa only [← mul_assoc, hg, one_mul, mul_one] using ht.symm

private theorem c_ne_native {m : ℕ} (hm : 4 ≤ m) (g : Configuration m)
    (hg : g = a m ∨ g = b m) : c m ≠ g := by
  rcases hg with rfl | rfl
  · intro he
    have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) he
    simp only [c_apply, Fin.val_last, a_apply, Fin.val_rev, Nat.sub_self] at hv
    rw [if_neg (by omega : ¬ m < m - 1)] at hv
    omega
  · intro he
    let i : Fin (m + 1) := ⟨m - 1, by omega⟩
    have hv := congrArg (fun f : Configuration m => (f i).val) he
    simp only [c_apply, b_apply, i, lt_self_iff_false, if_false, Nat.sub_self] at hv
    rw [if_pos (by omega : m - 1 < m)] at hv
    omega

private theorem deleted_native {m : ℕ} (e : Sym2 (Configuration m))
    (he : F2DeletedEdge m e) :
    ∃ x g : Configuration m, (g = a m ∨ g = b m) ∧ e = s(x, x * g) := by
  rcases he with ⟨p, hp⟩ | ⟨j, i, hi⟩
  · refine ⟨cutStart p, cutGenerator p, ?_, hp⟩
    cases p with
    | inl i => simp only [cutGenerator]; split <;> simp
    | inr j => exact Or.inr rfl
  · exact ⟨gapAnchor (contactAnchor j) i, b m, Or.inr rfl, hi⟩

private theorem seam_c {m : ℕ} (e : Sym2 (Configuration m)) (he : F2Seam m e) :
    ∃ x : Configuration m, e = s(x, x * c m) := by
  rcases he with ⟨p, hp⟩ | ⟨j, i, hi⟩
  · exact ⟨cutStart p * cutGenerator p, hp⟩
  · exact ⟨gapAnchor (contactAnchor j) i * b m, hi⟩

private theorem deleted_seam_disjoint {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) (hd : F2DeletedEdge m e) : ¬ F2Seam m e := by
  obtain ⟨x, g, hg, hx⟩ := deleted_native e hd
  intro hs
  obtain ⟨y, hy⟩ := seam_c e hs
  exact c_ne_native hm g hg (edge_generator_unique y x (c m) g (c_sq m) (hy.symm.trans hx))

private theorem contact_deleted_full {m : ℕ} (hm : 4 ≤ m) (k : ℕ)
    (e : Sym2 (Configuration m)) (hd : ContactDeleted m k e) : F2DeletedEdge m e := by
  obtain ⟨j, _, hj⟩ := hd
  refine Or.inr ⟨j, ⟨0, by omega⟩, ?_⟩
  simpa only [gapAnchor, pow_zero, mul_one] using hj

private theorem new_uncut_disjoint {m : ℕ} (hm : 4 ≤ m)
    (j : Fin (m - 2)) (e : Sym2 (Configuration m)) (hd : F2DeletedEdge m e) :
    ¬ NewUncut (contactAnchor j) e := by
  rintro ⟨i, hi, hn, hne⟩
  rcases hd with ⟨p, hp⟩ | ⟨k, l, hl⟩
  · have hmem : cutStart p ∈ e := hp ▸ Sym2.mem_mk_left _ _
    have hv := native_circle_edge_endpoint _ (cutStart p) e hn hmem
    exact new_circle_no_core hm j i hi _ hv
      (core_circle_in_domain hm p _ (Or.inl rfl))
  · have hmem : gapAnchor (contactAnchor k) l ∈ e := hl ▸ Sym2.mem_mk_left _ _
    have hv := native_circle_edge_endpoint _ _ e hn hmem
    obtain ⟨hjk, hil⟩ := new_circle_owner_unique hm j k i l _ hv (Or.inl rfl)
    subst k
    subst l
    exact hne hl

private theorem added_contact_disjoint {m : ℕ} (hm : 4 ≤ m)
    (j : Fin (m - 2)) (k : ℕ) (e : Sym2 (Configuration m))
    (he : NewUncut (contactAnchor j) e ∨ ESeam (contactAnchor j) e) :
    ¬ ContactDeleted m k e := by
  intro hd
  have hfull := contact_deleted_full hm k e hd
  rcases he with hn | hs
  · exact new_uncut_disjoint hm j e hfull hn
  · exact deleted_seam_disjoint hm e hfull (Or.inr ⟨j, hs⟩)

private theorem contact_deleted_succ {m : ℕ} (k : ℕ) (j : Fin (m - 2))
    (hj : j.val = k) (e : Sym2 (Configuration m)) :
    ContactDeleted m (k + 1) e ↔ ContactDeleted m k e ∨
      e = s(contactAnchor j, contactAnchor j * b m) := by
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hik : i.val < k
    · exact Or.inl ⟨i, hik, he⟩
    · have hij : i = j := Fin.ext (by omega)
      exact Or.inr (hij ▸ he)
  · rintro (hd | he)
    · obtain ⟨i, hi, he⟩ := hd
      exact ⟨i, by omega, he⟩
    · exact ⟨j, by omega, he⟩

private theorem partial_edge_flat {m : ℕ} (hm : 4 ≤ m) (k : ℕ) (hk : k ≤ m - 2)
    (e : Sym2 (Configuration m)) : PartialEdge m k e ↔ FlatPartial m k e := by
  classical
  revert hk
  induction k with
  | zero =>
    intro _
    simp [PartialEdge, FlatPartial, ContactDeleted]
  | succ k ih =>
    intro hk
    let j : Fin (m - 2) := ⟨k, by omega⟩
    rw [PartialEdge, dif_pos (by omega : k < m - 2), ih (by omega)]
    change ((FlatPartial m k e ∧ e ≠ s(contactAnchor j, contactAnchor j * b m)) ∨
      NewUncut (contactAnchor j) e ∨ ESeam (contactAnchor j) e) ↔ _
    constructor
    · rintro (⟨hold, hne⟩ | ha)
      · rcases hold with ⟨hc, hd⟩ | ⟨i, hi, ha⟩
        · exact Or.inl ⟨hc, fun h => by
            rcases (contact_deleted_succ k j rfl e).mp h with h | h
            · exact hd h
            · exact hne h⟩
        · exact Or.inr ⟨i, by omega, ha⟩
      · exact Or.inr ⟨j, by simp only [j]; omega, ha⟩
    · rintro (⟨hc, hd⟩ | ⟨i, hi, ha⟩)
      · left
        exact ⟨Or.inl ⟨hc, fun h => hd ((contact_deleted_succ k j rfl e).mpr (Or.inl h))⟩,
          fun h => hd ((contact_deleted_succ k j rfl e).mpr (Or.inr h))⟩
      · by_cases hik : i.val < k
        · left
          refine ⟨Or.inr ⟨i, hik, ha⟩, ?_⟩
          intro he
          exact added_contact_disjoint hm i (k + 1) e ha
            ((contact_deleted_succ k j rfl e).mpr (Or.inr he))
        · have hij : i = j := Fin.ext (by simp only [j]; omega)
          exact Or.inr (hij ▸ ha)

private theorem retained_core_disjoint {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) (hc : CoreUncut m e)
    (hn : ¬ ContactDeleted m (m - 2) e) : ¬ F2DeletedEdge m e := by
  rintro (hd | ⟨j, i, he⟩)
  · exact native_t_deleted_edge_disjoint hm e hd (Or.inl hc)
  · by_cases hi : i.val = 0
    · apply hn
      refine ⟨j, j.isLt, ?_⟩
      simpa only [gapAnchor, hi, pow_zero, mul_one] using he
    · obtain ⟨p, hp, _⟩ := hc
      have hmem : gapAnchor (contactAnchor j) i ∈ e := he ▸ Sym2.mem_mk_left _ _
      have hv := native_circle_edge_endpoint _ _ e hp hmem
      exact new_circle_no_core hm j i hi _ (Or.inl rfl) (core_circle_in_domain hm p _ hv)

private theorem flat_full_iff {m : ℕ} (hm : 4 ≤ m) (e : Sym2 (Configuration m)) :
    FlatPartial m (m - 2) e ↔ (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e := by
  constructor
  · rintro (⟨hc | hs, hd⟩ | ⟨j, _, hn | hs⟩)
    · obtain ⟨p, hp, hne⟩ := hc
      exact Or.inl ⟨Or.inl ⟨p, hp⟩, retained_core_disjoint hm e ⟨p, hp, hne⟩ hd⟩
    · exact Or.inr (Or.inl hs)
    · obtain ⟨i, hi, hp, hne⟩ := hn
      exact Or.inl ⟨Or.inr ⟨j, i, hi, hp⟩,
        fun hd => new_uncut_disjoint hm j e hd ⟨i, hi, hp, hne⟩⟩
    · exact Or.inr (Or.inr ⟨j, hs⟩)
  · rintro (⟨hc | ⟨j, i, hi, hn⟩, hd⟩ | hs)
    · obtain ⟨p, hp⟩ := hc
      exact Or.inl ⟨Or.inl ⟨p, hp, fun he => hd (Or.inl ⟨p, he⟩)⟩,
        fun h => hd (contact_deleted_full hm (m - 2) e h)⟩
    · exact Or.inr ⟨j, j.isLt, Or.inl ⟨i, hi, hn, fun he => hd (Or.inr ⟨j, i, he⟩)⟩⟩
    · rcases hs with hs | ⟨j, hs⟩
      · exact Or.inl ⟨Or.inr hs, fun h =>
          deleted_seam_disjoint hm e (contact_deleted_full hm (m - 2) e h) (Or.inl hs)⟩
      · exact Or.inr ⟨j, j.isLt, Or.inr hs⟩

/-- Every independently enumerated native cut is absent from the complete
closed inventory, including every new supplier cut and every contact cut. -/
theorem native_f2_deleted_edge_disjoint {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) (hd : F2DeletedEdge m e) :
    ¬ ((F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) := by
  rintro (⟨_, hn⟩ | hs)
  · exact hn hd
  · exact deleted_seam_disjoint hm e hd hs

/-- One actual Hamilton cycle has all original native-circle edges except
exactly the full literal T/E cut set, together with all actual T/E c seams. -/
theorem native_f2_hamiltonian_cycle_with_closed_inventory {m : ℕ} (hm : 4 ≤ m) :
    ∃ base : {v : Configuration m // F2Domain m v},
      ∃ w : (domainGraph (F2Domain m)).Walk base base,
        w.IsHamiltonianCycle ∧ ∀ e : Sym2 (Configuration m),
          e ∈ w.edges.map (Sym2.map Subtype.val) ↔
            (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e := by
  obtain ⟨base, w, hw, hinv⟩ := native_f2_hamiltonian_cycle_with_edge_inventory hm
  refine ⟨base, w, hw, fun e => (hinv e).trans ?_⟩
  exact (partial_edge_flat hm (m - 2) (by omega) e).trans (flat_full_iff hm e)

#print axioms native_f2_deleted_edge_disjoint
#print axioms native_f2_hamiltonian_cycle_with_closed_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
