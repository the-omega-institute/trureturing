/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentRetention
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentRetention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same literal J2 outer parent retains its protected-a and remaining-b edges and classifies every c edge. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSelectedCInvariant

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentRetention

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private j2SpecialMap j2_special_map_bijective from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open private old_base_bound outer_base_bound pChildIndex from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private special_child_path from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
open private native_child_frame_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains

private structure Invariants {m : ℕ} (F : SupplyFrame m 2)
    (D : Configuration m → Prop) {base : {x // D x}}
    (w : (domainGraph D).Walk base base) : Prop where
  keepA : ∀ (x y : {z // D z}), y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(protectedP F (by omega), protectedQ F (by omega)) →
    s(x, y) ∈ w.edges
  keepB : ∀ (x y : {z // D z}), y.val = x.val * b m →
    x.val (Fin.last m) ∉ F.selected.toFinset → s(x, y) ∈ w.edges
  cLabels : ∀ e ∈ w.edges, ∀ x : Configuration m,
    Sym2.map Subtype.val e = s(x, x * c m) → x (Fin.last m) ∈ F.selected.toFinset

private theorem seed_invariants {m : ℕ} (F : SupplyFrame m 2) (S : SeedFor F) :
    Invariants F (FrameDomain F) S.walk := by
  refine ⟨S.keepsProtectedA, S.keepsRemainingB, ?_⟩
  intro e he x hx
  induction e using Sym2.inductionOn with
  | _ v z =>
    rw [Sym2.map_mk] at hx
    rcases Sym2.eq_iff.mp hx with ⟨hv, hz⟩ | ⟨hz, hv⟩
    · have hy : z.val = v.val * c m := by rw [hv, hz]
      simpa only [hv] using S.selectedC v z hy he
    · have hy : v.val = z.val * c m := by rw [hv, hz]
      have he' : s(z, v) ∈ S.walk.edges := by simpa only [Sym2.eq_swap] using he
      simpa only [hv] using S.selectedC z v hy he'

private theorem invariants_map {m : ℕ} (F : SupplyFrame m 2)
    {D E : Configuration m → Prop} {a : {x // D x}}
    (w : (domainGraph D).Walk a a) (h : Invariants F D w)
    (f : domainGraph D →g domainGraph E) (hf : Function.Bijective f)
    (hval : ∀ x, (f x).val = x.val) : Invariants F E (w.map f) := by
  constructor
  · intro x y hy hp
    obtain ⟨x', rfl⟩ := hf.surjective x
    obtain ⟨y', rfl⟩ := hf.surjective y
    rw [hval, hval] at hy hp
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), h.keepA x' y' hy hp, rfl⟩
  · intro x y hy ht
    obtain ⟨x', rfl⟩ := hf.surjective x
    obtain ⟨y', rfl⟩ := hf.surjective y
    rw [hval, hval] at hy
    rw [hval] at ht
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), h.keepB x' y' hy ht, rfl⟩
  · intro e he x hx
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    have hraw : Sym2.map Subtype.val (Sym2.map f e') = Sym2.map Subtype.val e' := by
      rw [Sym2.map_map]
      congr 1
      funext z
      exact hval z
    exact h.cLabels e' he' x (hraw.symm.trans hx)

private theorem invariants_of_edges {m : ℕ} (F : SupplyFrame m 2)
    (D : Configuration m → Prop) {a b : {x // D x}}
    (w : (domainGraph D).Walk a a) (v : (domainGraph D).Walk b b)
    (h : Invariants F D w) (he : v.edges = w.edges) : Invariants F D v := by
  constructor
  · intro x y hy hp; rw [he]; exact h.keepA x y hy hp
  · intro x y hy ht; rw [he]; exact h.keepB x y hy ht
  · intro e hm x hx; rw [he] at hm; exact h.cLabels e hm x hx

private theorem invariants_same_selected {m : ℕ} (F G : SupplyFrame m 2)
    (hs : G.selected = F.selected) (D : Configuration m → Prop)
    {base : {x // D x}} (w : (domainGraph D).Walk base base)
    (h : Invariants F D w) : Invariants G D w := by
  constructor
  · intro x y hy hp
    apply h.keepA x y hy
    simpa only [protectedP, protectedQ, hs] using hp
  · intro x y hy ht
    exact h.keepB x y hy (by simpa only [hs] using ht)
  · intro e he x hx
    simpa only [hs] using h.cLabels e he x hx

private theorem old_p_invariants {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (P : RawSeedFor hm F) (C : OldPCycleFor hm F A u hbase hA P) :
    Invariants (outerFrame F A u hbase)
      (ChildDomain (childGap (outerFrame F A u hbase) (pChildIndex F A u hbase))) C.cycle.walk := by
  have h := invariants_map F P.seed.walk (seed_invariants F P.seed)
    (j2SpecialMap F (old_base_bound F A u hbase hA))
    (j2_special_map_bijective F _) (fun _ => rfl)
  have h' := invariants_map F _ h (pMarkedChildMap F A u hbase hA)
    (p_marked_child_map_bijective F A u hbase hA) (fun _ => rfl)
  have he := congrArg (fun w => w.edges) C.mappedWalk
  simp only [SimpleGraph.Walk.edges_copy] at he
  exact invariants_same_selected F (outerFrame F A u hbase) rfl _ _
    (invariants_of_edges F _ _ _ h' he)

private theorem ordinary_invariants {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val)
    (S : RawSeedFor hm (nativeChildFrame F j))
    (C : OrdinaryCycleFor hm F hB j hj S) :
    Invariants F (ChildDomain (childGap F j)) C.cycle.walk := by
  let G := nativeChildFrame F j
  have h := invariants_map G S.seed.walk (seed_invariants G S.seed)
    (j2SpecialMap G (native_child_frame_base_bound F hB j))
    (j2_special_map_bijective G _) (fun _ => rfl)
  have h' := invariants_map G _ h (childMarkedDomainMap F hB j)
    (child_marked_domain_map_bijective F hB j) (fun _ => rfl)
  have he := congrArg (fun w => w.edges) C.mappedWalk
  simp only [SimpleGraph.Walk.edges_copy] at he
  exact invariants_same_selected G F rfl _ _ (invariants_of_edges G _ _ _ h' he)

private theorem outer_child_invariants {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA)
    (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val) :
    Invariants (outerFrame F A u hbase) (ChildDomain (childGap (outerFrame F A u hbase) j))
      (W.children j hj).walk := by
  by_cases he : j = pChildIndex F A u hbase
  · subst j
    rw [W.oldPAttached]
    exact old_p_invariants hm F A u hbase hA W.P W.oldP
  · rw [W.otherAttached j hj he]
    exact ordinary_invariants hm (outerFrame F A u hbase) _ j hj
      (W.otherSeeds j hj) (W.otherCycles j hj)


private structure OpenInvariants {m : ℕ} (F : SupplyFrame m 2)
    (D : Configuration m → Prop) {base finish : {x // D x}}
    (w : (domainGraph D).Walk base finish) : Prop where
  keepA : ∀ (x y : {z // D z}), y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(protectedP F (by omega), protectedQ F (by omega)) →
    s(x, y) ∈ w.edges
  keepB : ∀ (x y : {z // D z}), y.val = x.val * b m →
    x.val (Fin.last m) ∉ F.selected.toFinset → x.val (Fin.last m) ≠ F.terminal →
    s(x, y) ∈ w.edges
  cLabels : ∀ e ∈ w.edges, ∀ x : Configuration m,
    Sym2.map Subtype.val e = s(x, x * c m) →
      x (Fin.last m) ∈ insert F.terminal F.selected.toFinset

private theorem outer_opened_invariants {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA)
    (j : Fin (outerFrame F A u hbase).base.length) :
    OpenInvariants (outerFrame F A u hbase)
      (ChildDomain (childGap (outerFrame F A u hbase) j)) (W.paths j).piece.walk := by
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  by_cases hj : 0 < j.val
  · have h := outer_child_invariants hm F A u hbase hA W j hj
    constructor
    · intro x y hy hp
      exact native_other_path_keeps_a (by omega) O hBO j hj (W.children j hj).walk
        (W.paths j) (W.ordinaryInventory j hj) x y hy (h.keepA x y hy hp)
    · intro x y hy ht hn
      exact native_other_path_keeps_remaining_b (by omega) O hBO j hj (W.children j hj).walk
        (W.paths j) (W.ordinaryInventory j hj) x y hy hn (h.keepB x y hy ht)
    · intro e he x hx
      exact Finset.mem_insert_of_mem
        (h.cLabels e ((W.ordinaryInventory j hj e).mp he).1 x hx)
  · have hj0 : j = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) hBO⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    subst j
    rw [W.specialPath]
    change OpenInvariants O (SpecialDomain O hBO) W.special.path
    have h := invariants_map O W.Q.seed.walk (seed_invariants O W.Q.seed)
      (j2SpecialMap O hBO) (j2_special_map_bijective O hBO) (fun _ => rfl)
    let p := W.special.ordered 0
    let ps := List.ofFn fun i : Fin 2 => W.special.ordered i.succ
    have hlist : p :: ps = List.ofFn W.special.ordered := by
      exact (List.ofFn_succ (f := W.special.ordered)).symm
    have hinv : ∀ e, e ∈ ((p :: ps).flatMap fun z => z.walk.edges) ↔
        e ∈ (W.Q.seed.walk.map (j2SpecialMap O hBO)).edgeSet ∧
          e ∉ specialCuts (by omega : 3 ≤ m) O hBO := by
      rw [hlist]
      exact W.special.uncutInventory
    constructor
    · intro x y hy hp
      exact native_special_path_keeps_a (by omega) O hBO _ p ps hinv W.special.path
        W.special.edges x y hy (h.keepA x y hy hp)
    · intro x y hy ht hn
      exact native_special_path_keeps_remaining_b (by omega) O hBO _ p ps hinv W.special.path
        W.special.edges x y hy hn (h.keepB x y hy ht)
    · intro e he x hx
      apply native_special_path_c_labels (by omega) O hBO _ h.cLabels p ps hinv ?_
        W.special.path W.special.edges e he x hx
      intro z hz
      rw [hlist] at hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨_, congrArg Subtype.val (W.special.orderedPorts i).2⟩

private theorem outer_edges {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    W.cycle.edges =
      s(W.base, (W.pieces ⟨(outerFrame F A u hbase).base.length - 1, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩).finish) ::
      (chainEdges (W.pieces ⟨0, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩)
        (List.ofFn fun i : Fin ((outerFrame F A u hbase).base.length - 1) =>
          W.pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse := by
  have he := W.edges
  have hlast : pChildIndex F A u hbase =
      ⟨(outerFrame F A u hbase).base.length - 1, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩ := by
    apply Fin.ext
    simp only [pChildIndex, outerFrame, List.length_append, List.length_singleton, Fin.val_mk]
    omega
  simpa only [hlast] using he

/-- These three earned invariants belong to the same retained outer
parent W.cycle. Every supplier and actual opening is attached to W;
only supplier b edges are removed, and every new c seam is classified. -/
theorem native_j2_outer_parent_retention {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    (∀ (x y : {z : Configuration m // ParentDomain (outerFrame F A u hbase) z}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP F (by omega), protectedQ F (by omega)) →
      s(x, y) ∈ W.cycle.edges) ∧
    (∀ (x y : {z : Configuration m // ParentDomain (outerFrame F A u hbase) z}),
      y.val = x.val * b m →
      x.val (Fin.last m) ∉ insert u F.selected.toFinset →
      s(x, y) ∈ W.cycle.edges) ∧
    (∀ x : Configuration m, s(x, x * c m) ∈ W.cycle.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ insert u F.selected.toFinset) := by
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  have hi := outer_opened_invariants hm F A u hbase hA W
  have he := outer_edges hm F A u hbase hA W
  refine ⟨?_, ?_, ?_⟩
  · intro x y hy hp
    have hr := native_parent_cycle_keeps_protected_a O hBO (protectedP F (by omega))
      (protectedQ F (by omega)) W.paths (fun j => (hi j).keepA)
      W.pieces W.childPieces W.cycle he x y hy hp
    obtain ⟨e, he, hmap⟩ := List.mem_map.mp hr
    have heq : e = s(x, y) := (Sym2.map.injective Subtype.val_injective) hmap
    exact heq ▸ he
  · intro x y hy ht
    have hr := native_parent_cycle_keeps_remaining_b O hBO W.paths (fun j => (hi j).keepB)
      W.pieces W.childPieces W.cycle he x y hy ht
    obtain ⟨e, he, hmap⟩ := List.mem_map.mp hr
    have heq : e = s(x, y) := (Sym2.map.injective Subtype.val_injective) hmap
    exact heq ▸ he
  · intro x hx
    exact native_parent_cycle_c_labels (by omega) O hBO W.paths (fun j => (hi j).cLabels)
      W.pieces W.childPieces W.baseCoordinate W.cycle he x hx

#print axioms native_j2_outer_parent_retention

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentRetention
