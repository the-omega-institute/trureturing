/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual permutation lies in a complete frame layer with three residual labels. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
import D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open private triple_orientations from
  D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

private theorem residual_mem {m k : ℕ} (F : SupplyFrame m k) (x : Fin (m + 1)) :
    x ∈ F.terminal :: F.base ↔ x ∉ F.selected.toFinset := by
  have hn : (F.selected ++ (F.base ++ [F.terminal])).Nodup := by
    simpa only [List.append_assoc] using F.full_nodup
  have hd := (List.nodup_append'.mp hn).2.2
  constructor
  · intro hx hs
    have hrest : x ∈ F.base ++ [F.terminal] := by simpa [or_comm] using hx
    exact List.disjoint_left.mp hd (List.mem_toFinset.mp hs) hrest
  · intro hs
    have hall := F.full_labels x
    have hrest : x ∈ F.base ++ [F.terminal] := by
      have hall' : x ∈ F.selected ∨ x ∈ F.base ++ [F.terminal] := by
        simpa only [List.append_assoc, List.mem_append] using hall
      exact hall'.resolve_left (fun h => hs (List.mem_toFinset.mpr h))
    simpa [or_comm] using hrest

private theorem residual_nodup {m k : ℕ} (F : SupplyFrame m k) :
    (F.terminal :: F.base).Nodup := by
  have hn : (F.selected ++ (F.base ++ [F.terminal])).Nodup := by
    simpa only [List.append_assoc] using F.full_nodup
  have hb := (List.nodup_append'.mp hn).2.1
  exact (show (F.base ++ [F.terminal]).Perm ([F.terminal] ++ F.base) from
    List.perm_append_comm).nodup_iff.mp hb

private theorem three_label_layer {m : ℕ} (S : Finset (Fin (m + 1)))
    (B : List (Fin (m + 1))) (hB : B.length = 3) (hn : B.Nodup)
    (hmem : ∀ x, x ∈ B ↔ x ∉ S) (v : Configuration m) :
    Layer S (B : Cycle (Fin (m + 1))) v := by
  let l := (List.ofFn v).filter (fun x => decide (x ∉ S))
  have hp : l.Perm B := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_ofFn.mpr v.injective).filter _) hn).mpr
    intro x
    simp only [List.mem_filter, List.mem_ofFn, decide_eq_true_eq]
    constructor
    · exact fun h => (hmem x).mpr h.2
    · intro h
      exact ⟨⟨v.symm x, v.apply_symm_apply x⟩, (hmem x).mp h⟩
  obtain ⟨a, b, c, htriple⟩ := List.length_eq_three.mp hB
  rw [htriple] at hp ⊢
  change (l : Cycle (Fin (m + 1))) = ([a, b, c] : Cycle _) ∨
    (l : Cycle (Fin (m + 1))) = ([a, b, c] : Cycle _).reverse
  rcases triple_orientations hp with h | h
  · exact Or.inl h
  · right
    apply h.trans
    rw [Cycle.reverse_coe]
    exact Cycle.coe_eq_coe.mpr ⟨1, rfl⟩

/-- The final marked residual bracelet contains exactly three labels, so
its two oriented circles exhaust every permutation after actual deletion.
No cardinality comparison or Hamiltonian candidate earns coverage. -/
theorem native_three_label_frame_domain {m k : ℕ} (F : SupplyFrame m k)
    (hbase : F.base.length = 2) (v : Configuration m) :
    Layer F.selected.toFinset (F.terminal :: F.base : Cycle (Fin (m + 1))) v :=
  three_label_layer F.selected.toFinset (F.terminal :: F.base)
    (by simp only [List.length_cons, hbase]) (residual_nodup F) (residual_mem F) v

private theorem parent_residual_mem {m k : ℕ} (F : SupplyFrame m k)
    (x : Fin (m + 1)) : x ∈ F.base ↔ x ∉ insert F.terminal F.selected.toFinset := by
  have hd := (List.nodup_append'.mp F.full_nodup).2.2
  constructor
  · intro hx hs
    rcases Finset.mem_insert.mp hs with he | hs
    · exact List.disjoint_left.mp hd (List.mem_append.mpr (Or.inr hx))
        (by simp only [List.mem_singleton]; exact he)
    · exact List.disjoint_left.mp
        (List.nodup_append'.mp (List.nodup_append'.mp F.full_nodup).1).2.2
        (List.mem_toFinset.mp hs) hx
  · intro hs
    have hall := F.full_labels x
    simp only [List.mem_append, List.mem_singleton] at hall
    rcases hall with (hall | hall) | hall
    · exact (hs (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hall))).elim
    · exact hall
    · exact (hs (Finset.mem_insert.mpr (Or.inl hall))).elim

/-- The last outer supply erases its terminal as well as the selected
labels. A three-label base therefore makes the independently specified
parent domain the whole permutation group, before choosing its cycle. -/
theorem native_three_label_parent_domain {m k : ℕ} (F : SupplyFrame m k)
    (hbase : F.base.length = 3) (v : Configuration m) :
    Layer (insert F.terminal F.selected.toFinset) (F.base : Cycle (Fin (m + 1))) v :=
  three_label_layer (insert F.terminal F.selected.toFinset) F.base hbase
    (List.nodup_append'.mp (List.nodup_append'.mp F.full_nodup).1).2.1
    (parent_residual_mem F) v

/-- Forgetting the already earned full-layer membership is an actual graph
isomorphism to the complete three-generator Cayley graph. Thus the final
recursive cycle is transported once without losing any vertex or edge. -/
noncomputable def fullDomainIso {m k : ℕ} (F : SupplyFrame m k)
    (hbase : F.base.length = 2) :
    domainGraph (Layer F.selected.toFinset (F.terminal :: F.base : Cycle _)) ≃g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) where
  toEquiv := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun v => ⟨⟨v, native_three_label_frame_domain F hbase v⟩, rfl⟩⟩
  map_rel_iff' := Iff.rfl

/-- The actual outer parent graph at the three-label stopping layer is
the full native Cayley graph by the identity on configurations. -/
noncomputable def fullParentDomainIso {m k : ℕ} (F : SupplyFrame m k)
    (hbase : F.base.length = 3) :
    domainGraph (Layer (insert F.terminal F.selected.toFinset) (F.base : Cycle _)) ≃g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) where
  toEquiv := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun v => ⟨⟨v, native_three_label_parent_domain F hbase v⟩, rfl⟩⟩
  map_rel_iff' := Iff.rfl

#print axioms native_three_label_frame_domain
#print axioms native_three_label_parent_domain
#print axioms fullDomainIso
#print axioms fullParentDomainIso

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain
