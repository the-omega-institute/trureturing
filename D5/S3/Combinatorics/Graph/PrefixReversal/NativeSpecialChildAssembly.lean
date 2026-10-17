/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete actual cycle partitions and proved native seams construct Hamilton paths on the special child. -/
/- candidate, conditional on the previous actual child cycle,
   its genuine b-cut membership, and its earned E/O slice endpoint law.
   Full special support and reordering are conclusions, never inputs.
   Install the Domains / ActualCyclePieceReordering candidates under the
   imported canonical names before compilation. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
import D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
import D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering
open private even_route_seam_step odd_route_seam_step
  even_route_last1_eq odd_route_last3_eq from
  D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary

private theorem frame_k_lt_m {m k : ℕ} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) : k < m := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  omega

abbrev SpecialDomain {m k : ℕ} (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) :=
  ChildDomain (childGap F ⟨0, by omega⟩)

private theorem native_special_port_domain {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (p : Port k) :
    SpecialDomain F hB (specialPort F p) := by
  let i : Fin m := ⟨p.1.val, by have hp := p.1.isLt; have hk := frame_k_lt_m F hB; omega⟩
  have hc := native_supply_cut_child_domain hm F (by omega) i
  have hg : supplyGap F (by omega) i = ⟨0, by omega⟩ := by
    apply Fin.ext
    simp only [supplyGap, i, Fin.val_mk, if_pos (show p.1.val ≤ k by have h := p.1.isLt; omega)]
  rw [hg] at hc
  rcases p with ⟨j, side⟩
  fin_cases side
  · exact hc.1
  · exact hc.2

noncomputable def specialVertex {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (p : Port k) :
    {x : Configuration m // SpecialDomain F hB x} :=
  ⟨specialPort F p, native_special_port_domain hm F hB p⟩

noncomputable def specialCut {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (i : Fin (k + 1)) :
    Sym2 {x : Configuration m // SpecialDomain F hB x} :=
  s(specialVertex hm F hB (i, 0), specialVertex hm F hB (i, 1))

noncomputable def specialCuts {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) :
    Finset (Sym2 {x : Configuration m // SpecialDomain F hB x}) := by
  classical
  exact Finset.univ.image (specialCut hm F hB)

private theorem special_cut_injective {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) :
    Function.Injective (specialCut hm F hB) := by
  intro i j he
  have h := congrArg (Sym2.map Subtype.val) he
  change s(specialPort F (i, 0), specialPort F (i, 1)) =
    s(specialPort F (j, 0), specialPort F (j, 1)) at h
  rcases Sym2.eq_iff.mp h with ⟨hs, _⟩ | ⟨hs, _⟩
  · exact congrArg Prod.fst (native_special_port_injective hm F (frame_k_lt_m F hB) hs)
  · have hh := native_special_port_injective hm F (frame_k_lt_m F hB) hs
    have hz := congrArg (fun p : Port k => p.2.val) hh
    norm_num at hz

private theorem special_cuts_nonempty {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) : (specialCuts hm F hB).Nonempty := by
  classical
  exact ⟨specialCut hm F hB 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

private theorem special_cuts_card {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) : (specialCuts hm F hB).card = k + 1 := by
  classical
  rw [specialCuts, Finset.card_image_of_injective _ (special_cut_injective hm F hB)]
  simp only [Finset.card_univ, Fintype.card_fin]

private theorem native_internal_seam_adj {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (p q : Port k)
    (hs : internalSeam k (code p) (code q)) :
    (domainGraph (SpecialDomain F hB)).Adj
      (specialVertex hm F hB p) (specialVertex hm F hB q) := by
  change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
    (specialPort F p) (specialPort F q)
  rcases hs with ⟨hp, hq, _, hi⟩ | ⟨hq, hp, _, hi⟩
  · change p.2.val = 1 at hp
    change q.2.val = 0 at hq
    change q.1.val = p.1.val + 1 at hi
    simp only [specialPort, if_neg (by omega : ¬ p.2.val = 0), if_pos hq]
    rw [hi]
    exact ((native_anchored_supply_coordinates hm F).1 p.1.val).2.2.2
  · change q.2.val = 1 at hq
    change p.2.val = 0 at hp
    change p.1.val = q.1.val + 1 at hi
    simp only [specialPort, if_pos hp, if_neg (by omega : ¬ q.2.val = 0)]
    rw [hi]
    exact (((native_anchored_supply_coordinates hm F).1 q.1.val).2.2.2).symm

/-- The only inductive endpoint input is a law about every actual slice
of this actual previous cycle. Native seams supply all graph connections. -/
theorem native_special_child_assembled {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edgeSet)
    (B : RawPort → RawPort → Prop) (route : Fin (2 * (k + 1)) → Port k)
    (honce : ∀ p q : Port k, B (code p) (code q) →
      ∃! i : Fin (k + 1), s(p, q) = routeEdge route i)
    (hpair : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
        (special_cuts_nonempty hm F hB) hcuts,
      ∃ p q : Port k, z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧ B (code p) (code q))
    (hseams : ∀ i (hi : i + 1 < k + 1), internalSeam k
      (code (route ⟨2 * i + 1, by omega⟩)) (code (route ⟨2 * (i + 1), by omega⟩))) :
    ∃ ordered : Fin (k + 1) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (route ⟨0, by omega⟩))
        (specialVertex hm F hB (route ⟨2 * (k + 1) - 1, by omega⟩)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start =
        specialVertex hm F hB (route ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish =
        specialVertex hm F hB (route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0) (List.ofFn fun i : Fin k => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB := by
  classical
  let actualRoute := fun i => specialVertex hm F hB (route i)
  have hmatch : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
      (special_cuts_nonempty hm F hB) hcuts,
      ∃ i : Fin (k + 1), s(z.start, z.finish) = routeEdge actualRoute i := by
    intro z hz
    obtain ⟨p, q, hs, hf, hb⟩ := hpair z hz
    obtain ⟨i, hi, _⟩ := honce p q hb
    refine ⟨i, ?_⟩
    have hs' : z.start = specialVertex hm F hB p := Subtype.ext hs
    have hf' : z.finish = specialVertex hm F hB q := Subtype.ext hf
    rw [hs', hf']
    simpa only [routeEdge, Sym2.map_mk, actualRoute] using
      congrArg (Sym2.map (specialVertex hm F hB)) hi
  obtain ⟨ordered, q, hq, hend, hs, he, hinv⟩ :=
    actual_cycle_slices_joined (specialCuts hm F hB) w hw
      (special_cuts_nonempty hm F hB) hcuts k (special_cuts_card hm F hB)
      actualRoute hmatch
      (fun i hi => native_internal_seam_adj hm F hB _ _ (hseams i hi))
  exact ⟨ordered, q, hq, hend, hs, he, hinv⟩

/-- Consume the actual supplied partition of the same previous cycle.
Its support and edge inventories earn its cardinality, and its native
endpoint law earns the complete route without selecting new slices. -/
theorem native_special_child_from_actual_partition {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (pieces : List (Piece (domainGraph (SpecialDomain F hB))))
    (hs : (pieces.flatMap fun z => z.walk.support).Perm w.support.tail)
    (he : (pieces.flatMap fun z => z.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ specialCuts hm F hB)))
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edges)
    (B : RawPort → RawPort → Prop) (route : Fin (2 * (k + 1)) → Port k)
    (honce : ∀ p q : Port k, B (code p) (code q) →
      ∃! i : Fin (k + 1), s(p, q) = routeEdge route i)
    (hpair : ∀ z ∈ pieces,
      ∃ p q : Port k, z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧ B (code p) (code q))
    (hseams : ∀ i (hi : i + 1 < k + 1), internalSeam k
      (code (route ⟨2 * i + 1, by omega⟩)) (code (route ⟨2 * (i + 1), by omega⟩))) :
    ∃ ordered : Fin (k + 1) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (route ⟨0, by omega⟩))
        (specialVertex hm F hB (route ⟨2 * (k + 1) - 1, by omega⟩)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start =
        specialVertex hm F hB (route ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish =
        specialVertex hm F hB (route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0) (List.ofFn fun i : Fin k => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB := by
  classical
  let actualRoute := fun i => specialVertex hm F hB (route i)
  have hmatch : ∀ z ∈ pieces,
      ∃ i : Fin (k + 1), s(z.start, z.finish) = routeEdge actualRoute i := by
    intro z hz
    obtain ⟨p, q, hs, hf, hb⟩ := hpair z hz
    obtain ⟨i, hi, _⟩ := honce p q hb
    refine ⟨i, ?_⟩
    have hs' : z.start = specialVertex hm F hB p := Subtype.ext hs
    have hf' : z.finish = specialVertex hm F hB q := Subtype.ext hf
    rw [hs', hf']
    simpa only [routeEdge, Sym2.map_mk, actualRoute] using
      congrArg (Sym2.map (specialVertex hm F hB)) hi
  obtain ⟨hcount, hedges, hlen⟩ :=
    actual_cycle_partition_inventory (specialCuts hm F hB) w hw pieces hs he hcuts
  obtain ⟨ordered, q, hq, hend, hs, he, hinv⟩ :=
    actual_partition_pieces_joined (specialCuts hm F hB) w pieces k hcount hedges
      (hlen.trans (special_cuts_card hm F hB)) actualRoute hmatch
      (fun i hi => native_internal_seam_adj hm F hB _ _ (hseams i hi))
  exact ⟨ordered, q, hq, hend, hs, he, hinv⟩

#print axioms native_special_child_from_actual_partition

#print axioms native_special_child_assembled

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
