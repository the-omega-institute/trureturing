/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One F2 Hamilton cycle has exactly the independently defined native edge inventory. -/

import D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeInventory

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration

/-- An independent finite recipe for every raw edge after the first k contacts.
At each actual contact it removes that b edge, adds the new circles minus their
literal b cuts, and adds the actual E c connections. It contains no chosen walk. -/
def PartialEdge (m : ℕ) : ℕ → Sym2 (Configuration m) → Prop
  | 0, e => CoreUncut m e ∨ TSeam m e
  | k + 1, e => if hk : k < m - 2 then
      (PartialEdge m k e ∧
        e ≠ s(contactAnchor ⟨k, hk⟩, contactAnchor ⟨k, hk⟩ * b m)) ∨
        NewUncut (contactAnchor ⟨k, hk⟩) e ∨ ESeam (contactAnchor ⟨k, hk⟩) e
    else PartialEdge m k e

private theorem contact_endpoints {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    CoreDomain m (contactAnchor j) ∧ SupplierStar (contactAnchor j) (contactAnchor j) ∧
      CoreDomain m (contactAnchor j * b m) ∧
        SupplierStar (contactAnchor j) (contactAnchor j * b m) := by
  have hs := (contact_star_core_intersection hm j (contactAnchor j)).mpr (Or.inl rfl)
  obtain ⟨w, _, _, _, hsupport⟩ := native_b_complement (by omega : 3 ≤ m) (contactAnchor j)
  have hb := (contact_star_core_intersection hm j (contactAnchor j * b m)).mpr
    ((hsupport _).mp w.end_mem_support)
  exact ⟨hs.1, hs.2, hb.1, hb.2⟩

private theorem contact_edge_distinct {m : ℕ} (hm : 4 ≤ m) (i j : Fin (m - 2))
    (hij : i ≠ j) :
    s(contactAnchor i, contactAnchor i * b m) ≠
      s(contactAnchor j, contactAnchor j * b m) := by
  intro he
  have hi := (contact_endpoints hm i).2.1
  have hj := contact_endpoints hm j
  rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨he, _⟩
  · exact Set.disjoint_left.mp (contact_stars_pairwise_disjoint i j hij) hi (he.symm ▸ hj.2.1)
  · exact Set.disjoint_left.mp (contact_stars_pairwise_disjoint i j hij) hi (he.symm ▸ hj.2.2.2)

private theorem partial_next_intersection {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (v : Configuration m) :
    (PartialDomain m j.val v ∧ SupplierStar (contactAnchor j) v) ↔ Circle (contactAnchor j) v := by
  constructor
  · rintro ⟨hc | ⟨i, hi, hs⟩, hj⟩
    · exact (contact_star_core_intersection hm j v).mp ⟨hc, hj⟩
    · have hij : i ≠ j := by intro he; subst i; omega
      exact (Set.disjoint_left.mp (contact_stars_pairwise_disjoint i j hij) hs hj).elim
  · intro hv
    obtain ⟨hc, hs⟩ := (contact_star_core_intersection hm j v).mpr hv
    exact ⟨Or.inl hc, hs⟩

private theorem partial_successor {m k : ℕ} (j : Fin (m - 2)) (hj : j.val = k) :
    GraftDomain (PartialDomain m k) (contactAnchor j) = PartialDomain m (k + 1) := by
  funext v
  apply propext
  constructor
  · rintro ((hc | ⟨i, hi, hs⟩) | hs)
    · exact Or.inl hc
    · exact Or.inr ⟨i, by omega, hs⟩
    · exact Or.inr ⟨j, by omega, hs⟩
  · rintro (hc | ⟨i, hi, hs⟩)
    · exact Or.inl (Or.inl hc)
    · by_cases hik : i.val < k
      · exact Or.inl (Or.inr ⟨i, hik, hs⟩)
      · have he : i = j := Fin.ext (by omega)
        exact Or.inr (he ▸ hs)

private def KeepsPending {m : ℕ} {U : Configuration m → Prop}
    (k : ℕ) {base : {v : Configuration m // U v}}
    (w : (domainGraph U).Walk base base) : Prop :=
  ∀ j : Fin (m - 2), k ≤ j.val →
    ∀ x y : {v : Configuration m // U v}, x.val = contactAnchor j →
      y.val = contactAnchor j * b m → s(x, y) ∈ w.edges

private theorem partial_cycle_inventory {m : ℕ} (hm : 4 ≤ m) (k : ℕ) (hk : k ≤ m - 2) :
    ∃ base : {v : Configuration m // PartialDomain m k v},
      ∃ w : (domainGraph (PartialDomain m k)).Walk base base,
        w.IsHamiltonianCycle ∧ KeepsPending k w ∧
          ∀ e : Sym2 (Configuration m),
            e ∈ w.edges.map (Sym2.map Subtype.val) ↔ PartialEdge m k e := by
  classical
  revert hk
  induction k with
  | zero =>
    intro _
    have hdomain : PartialDomain m 0 = CoreDomain m := by
      funext v
      apply propext
      simp only [PartialDomain, Nat.not_lt_zero, false_and, exists_false, or_false]
    obtain ⟨base, _, w, hw, _, hretains, hinv⟩ :=
      native_core_hamiltonian_cycle_with_full_inventory hm
    have hcert : ∃ base : {v : Configuration m // CoreDomain m v},
        ∃ w : (domainGraph (CoreDomain m)).Walk base base,
          w.IsHamiltonianCycle ∧ KeepsPending 0 w ∧
            ∀ e : Sym2 (Configuration m),
              e ∈ w.edges.map (Sym2.map Subtype.val) ↔ PartialEdge m 0 e := by
      refine ⟨base, w, hw, ?_, hinv⟩
      intro j _ x y hx hy
      apply hretains x y (b m) (Or.inr rfl)
      · rw [hx, hy]
      · simpa only [hx, hy] using contact_b_edge_not_deleted hm j
    exact hdomain.symm ▸ hcert
  | succ k ih =>
    intro hk
    obtain ⟨base, w, hw, hremaining, holdinv⟩ := ih (by omega : k ≤ m - 2)
    let j : Fin (m - 2) := ⟨k, by omega⟩
    have hj := contact_endpoints hm j
    let x : {v : Configuration m // PartialDomain m k v} := ⟨contactAnchor j, Or.inl hj.1⟩
    let y : {v : Configuration m // PartialDomain m k v} := ⟨contactAnchor j * b m, Or.inl hj.2.2.1⟩
    have he : s(x, y) ∈ w.edges := hremaining j (by simp only [j]; omega) x y rfl rfl
    have hc : ∀ v, PartialDomain m k v ∧ SupplierStar x.val v ↔ Circle x.val v := by
      intro v
      simpa only [x, j] using partial_next_intersection hm j v
    obtain ⟨start, _, q, hq, hretains, _, _, hinv⟩ :=
      native_one_contact_graft (by omega : 3 ≤ m) (PartialDomain m k) w hw x y rfl he hc
    have hpending : KeepsPending (k + 1) q := by
      intro future hfuture u v hu hv
      have hfj : future ≠ j := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [j] at hval
        omega
      have hverts := contact_endpoints hm future
      let u0 : {v : Configuration m // PartialDomain m k v} :=
        ⟨u.val, Or.inl (hu.symm ▸ hverts.1)⟩
      let v0 : {v : Configuration m // PartialDomain m k v} :=
        ⟨v.val, Or.inl (hv.symm ▸ hverts.2.2.1)⟩
      have hold : s(u0, v0) ∈ w.edges := hremaining future (by omega) u0 v0 hu hv
      have hne : s(u0, v0) ≠ s(x, y) := by
        intro heq
        have hraw := congrArg (Sym2.map Subtype.val) heq
        change s(u.val, v.val) = s(contactAnchor j, contactAnchor j * b m) at hraw
        rw [hu, hv] at hraw
        exact contact_edge_distinct hm future j hfj hraw
      have hu0 : liftOld x.val u0 = u := Subtype.ext rfl
      have hv0 : liftOld x.val v0 = v := Subtype.ext rfl
      simpa only [hu0, hv0] using hretains u0 v0 hold hne
    have hfull : ∀ e : Sym2 (Configuration m),
        e ∈ q.edges.map (Sym2.map Subtype.val) ↔ PartialEdge m (k + 1) e := by
      intro e
      rw [hinv e]
      simp only [PartialEdge, dif_pos (by omega : k < m - 2)]
      change ((e ∈ w.edges.map (Sym2.map Subtype.val) ∧
        e ≠ s(contactAnchor j, contactAnchor j * b m)) ∨
          NewUncut (contactAnchor j) e ∨ ESeam (contactAnchor j) e) ↔ _
      rw [holdinv e]
    have hcert : ∃ start : {v : Configuration m // GraftDomain (PartialDomain m k) x.val v},
        ∃ q : (domainGraph (GraftDomain (PartialDomain m k) x.val)).Walk start start,
          q.IsHamiltonianCycle ∧ KeepsPending (k + 1) q ∧
            ∀ e : Sym2 (Configuration m),
              e ∈ q.edges.map (Sym2.map Subtype.val) ↔ PartialEdge m (k + 1) e :=
      ⟨start, q, hq, hpending, hfull⟩
    have hdomain : GraftDomain (PartialDomain m k) x.val = PartialDomain m (k + 1) :=
      partial_successor j rfl
    exact hdomain ▸ hcert

/-- The Hamilton cycle and the complete arbitrary raw-edge iff are earned along
the same finite sequence of literal contact grafts. -/
theorem native_f2_hamiltonian_cycle_with_edge_inventory {m : ℕ} (hm : 4 ≤ m) :
    ∃ base : {v : Configuration m // F2Domain m v},
      ∃ w : (domainGraph (F2Domain m)).Walk base base,
        w.IsHamiltonianCycle ∧ ∀ e : Sym2 (Configuration m),
          e ∈ w.edges.map (Sym2.map Subtype.val) ↔ PartialEdge m (m - 2) e := by
  obtain ⟨base, w, hw, _, hinv⟩ := partial_cycle_inventory hm (m - 2) (by omega)
  exact ⟨base, w, hw, hinv⟩

#print axioms native_f2_hamiltonian_cycle_with_edge_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeInventory
