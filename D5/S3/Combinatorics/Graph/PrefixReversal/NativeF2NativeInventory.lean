/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual native F2 edge is retained exactly outside the full literal cut set. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification

private theorem core_circle_domain {m : ℕ} (hm : 4 ≤ m)
    (p : Fin m ⊕ Fin (m - 2)) (v : Configuration m) (hv : Circle (cutStart p) v) :
    CoreDomain m v := by
  have hp := (native_cut_circle_iff hm p v).mp hv
  exact (native_t_circle_partition hm v).mpr
    ⟨p, hp, fun q hq => native_t_circle_owner_unique hm v q p hq hp⟩

private theorem gap_domain {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (i : Fin m) (v : Configuration m) (hv : Circle (gapAnchor (contactAnchor j) i) v) :
    F2Domain m v := by
  exact Or.inr ⟨j, j.isLt,
    (native_star_circle_partition (by omega : 3 ≤ m) (contactAnchor j) v).mpr ⟨i, hv⟩⟩

/-- The independent full-circle catalog is precisely the set of native a/b
edges based at actual vertices of the independently specified F2 domain. -/
theorem native_f2_native_edge_catalog {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) :
    F2NativeEdge m e ↔ ∃ x g : Configuration m,
      F2Domain m x ∧ (g = a m ∨ g = b m) ∧ e = s(x, x * g) := by
  constructor
  · rintro (⟨p, x, g, hx, hg, he⟩ | ⟨j, i, _, x, g, hx, hg, he⟩)
    · exact ⟨x, g, Or.inl (core_circle_domain hm p x hx), hg, he⟩
    · exact ⟨x, g, gap_domain hm j i x hx, hg, he⟩
  · rintro ⟨x, g, hd, hg, rfl⟩
    have hcore : CoreDomain m x → F2NativeEdge m s(x, x * g) := by
      intro hc
      obtain ⟨p, hp, _⟩ := (native_t_circle_partition hm x).mp hc
      exact Or.inl ⟨p, x, g, (native_cut_circle_iff hm p x).mpr hp, hg, rfl⟩
    rcases hd with hc | ⟨j, _, hs⟩
    · exact hcore hc
    · obtain ⟨i, hi⟩ := (native_star_circle_partition (by omega : 3 ≤ m)
        (contactAnchor j) x).mp hs
      by_cases hiz : i.val = 0
      · have hz : gapAnchor (contactAnchor j) i = contactAnchor j := by simp [gapAnchor, hiz]
        exact hcore ((contact_star_core_intersection hm j x).mpr (hz ▸ hi)).1
      · exact Or.inr ⟨j, i, hiz, x, g, hi, hg, rfl⟩

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

private theorem native_not_seam {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) (hn : F2NativeEdge m e) : ¬ F2Seam m e := by
  obtain ⟨x, g, _, hg, hx⟩ := (native_f2_native_edge_catalog hm e).mp hn
  intro hs
  have hc : ∃ y : Configuration m, e = s(y, y * c m) := by
    rcases hs with ⟨p, hp⟩ | ⟨j, i, hi⟩
    · exact ⟨cutStart p * cutGenerator p, hp⟩
    · exact ⟨gapAnchor (contactAnchor j) i * b m, hi⟩
  obtain ⟨y, hy⟩ := hc
  exact c_ne_native hm g hg (edge_generator_unique y x (c m) g (c_sq m) (hy.symm.trans hx))

/-- The same actual Hamilton witness retains every actual native edge
precisely when it is outside the complete independently defined cut set. -/
theorem native_f2_hamiltonian_cycle_with_native_edge_inventory {m : ℕ} (hm : 4 ≤ m) :
    ∃ base : {v : Configuration m // F2Domain m v},
      ∃ w : (domainGraph (F2Domain m)).Walk base base,
        w.IsHamiltonianCycle ∧
          (∀ e : Sym2 (Configuration m),
            e ∈ w.edges.map (Sym2.map Subtype.val) ↔
              (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧
          ∀ x g : Configuration m,
          F2Domain m x → (g = a m ∨ g = b m) →
            (s(x, x * g) ∈ w.edges.map (Sym2.map Subtype.val) ↔
              ¬ F2DeletedEdge m s(x, x * g)) := by
  obtain ⟨base, w, hw, hinv⟩ := native_f2_hamiltonian_cycle_with_closed_inventory hm
  refine ⟨base, w, hw, hinv, ?_⟩
  intro x g hx hg
  have hn : F2NativeEdge m s(x, x * g) :=
    (native_f2_native_edge_catalog hm _).mpr ⟨x, g, hx, hg, rfl⟩
  have hs : ¬ F2Seam m s(x, x * g) := native_not_seam hm _ hn
  simpa only [hn, true_and, hs, or_false] using hinv (s(x, x * g))

#print axioms native_f2_native_edge_catalog
#print axioms native_f2_hamiltonian_cycle_with_native_edge_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
