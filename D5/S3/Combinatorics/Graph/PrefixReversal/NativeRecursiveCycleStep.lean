/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Specified child cycles and literal supplier cuts construct the complete actual parent with attached inventories. -/
/- actual recursive cycle step.
   Special coverage is earned by the real E/O slice assembly. Ordinary
   paths are real single-cut complements of previous child cycles. The
   full independent parent domain is earned by NativeOuterChildAssembly.
   This is not yet an all-n induction: the next J-state still needs its
   own b-cut membership and E/O endpoint propagation. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly

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
open private special_cuts_nonempty from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly
open private parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly

private theorem ordinary_port_domain {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val) :
    ChildDomain (childGap F j) (rightPort F (k + j.val)) ∧
      ChildDomain (childGap F j) (leftPort F (k + j.val)) := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  let i : Fin m := ⟨k + j.val, by have h := j.isLt; omega⟩
  have hg : supplyGap F (by omega) i = j := by
    apply Fin.ext
    simp only [supplyGap, i, Fin.val_mk, if_neg (by omega : ¬ k + j.val ≤ k)]
    omega
  have hc := native_supply_cut_child_domain hm F (by omega) i
  simpa only [hg, i, Fin.val_mk] using hc

noncomputable def ordinaryRight {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val) :
    {x : Configuration m // ChildDomain (childGap F j) x} :=
  ⟨rightPort F (k + j.val), (ordinary_port_domain hm F hB j hj).1⟩

noncomputable def ordinaryLeft {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val) :
    {x : Configuration m // ChildDomain (childGap F j) x} :=
  ⟨leftPort F (k + j.val), (ordinary_port_domain hm F hB j hj).2⟩

private theorem ordinary_child_open {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val)
    {a : {x : Configuration m // ChildDomain (childGap F j) x}}
    (w : (domainGraph (ChildDomain (childGap F j))).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcut : s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) ∈ w.edgeSet) :
    ∃ q : ActualChildPath F j,
      ∀ e, e ∈ q.piece.walk.edges ↔ e ∈ w.edges ∧
        e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) := by
  obtain ⟨raw, hraw, hinv⟩ := exists_open_cycle_at_edge w hw hcut
  refine ⟨⟨⟨ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj, raw.reverse⟩,
    ?_, rfl, ?_⟩, ?_⟩
  · simp only [ordinaryRight, childStartIndex, if_neg (by omega : ¬ j.val = 0)]
  · intro v
    simpa only [SimpleGraph.Walk.support_reverse, List.count_reverse] using hraw v
  · intro e
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hinv e

private noncomputable def special_child_path {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1)))
    (hq : q.IsHamiltonian) : ActualChildPath F ⟨0, by omega⟩ :=
  ⟨⟨_, _, q⟩, rfl, rfl, hq⟩

/-- Genuine prior cycles and their actual one-cut membership are the only
ordinary-child inputs. This contains no parent coverage certificate. -/
def OtherChildCycles {m k : ℕ} (hm : 3 ≤ m) (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) : Prop :=
  ∀ (j : Fin F.base.length) (hj : 0 < j.val),
    ∃ a : {x : Configuration m // ChildDomain (childGap F j) x},
      ∃ w : (domainGraph (ChildDomain (childGap F j))).Walk a a,
      w.IsHamiltonianCycle ∧
        s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) ∈ w.edgeSet

/-- The exact ordinary prior cycle chosen from the full induction state.
Keeping its walk as data lets its actual J and restored-half states be
used after opening; the parent constructor only chooses an opening path. -/
structure SpecifiedOrdinaryCycle {m k : ℕ} (hm : 3 ≤ m) (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val) where
  base : {x : Configuration m // ChildDomain (childGap F j) x}
  walk : (domainGraph (ChildDomain (childGap F j))).Walk base base
  hamiltonian : walk.IsHamiltonianCycle
  cut : s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) ∈ walk.edgeSet

/-- Construct the parent from these particular prior cycles. Every
ordinary complement inventory is about the corresponding supplied walk,
so the P old-cycle/J/half witnesses cannot become detached from the cycle
used in the same current parent. Its complete domain is still earned by
the independent child partition, with all literal inventories retained. -/
theorem recursive_cycle_from_specified_children_with_inventory {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1)))
    (hq : q.IsHamiltonian)
    (children : ∀ (j : Fin F.base.length) (hj : 0 < j.val),
      SpecifiedOrdinaryCycle hm F hB j hj) :
    ∃ paths : ∀ j : Fin F.base.length, ActualChildPath F j,
      (paths ⟨0, by omega⟩).piece = (special_child_path hm F hB q hq).piece ∧
      (∀ (j : Fin F.base.length) (hj : 0 < j.val), ∀ e,
        e ∈ (paths j).piece.walk.edges ↔ e ∈ (children j hj).walk.edges ∧
          e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj)) ∧
      ∃ pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)),
      ∃ a : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk a a,
      (∀ j, pieces j = parentPiece F j (paths j)) ∧
      a.val = rightPort F 0 ∧ c.IsHamiltonianCycle ∧
      c.support.tail = ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse ∧
      c.edges = s(a, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
        (chainEdges (pieces ⟨0, by omega⟩)
          (List.ofFn fun i : Fin (F.base.length - 1) =>
            pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse := by
  classical
  have hordinary (j : Fin F.base.length) (hj : 0 < j.val) :
      ∃ p : ActualChildPath F j, ∀ e, e ∈ p.piece.walk.edges ↔
        e ∈ (children j hj).walk.edges ∧
          e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) :=
    ordinary_child_open hm F hB j hj (children j hj).walk
      (children j hj).hamiltonian (children j hj).cut
  let zero : Fin F.base.length := ⟨0, by omega⟩
  let paths (j : Fin F.base.length) : ActualChildPath F j :=
    if hj : j = zero then hj.symm ▸ special_child_path hm F hB q hq
    else Classical.choose (hordinary j (by
      have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
      omega))
  refine ⟨paths, ?_, ?_, native_parent_cycle_of_child_paths hm F hB paths⟩
  · simp only [paths, dif_pos rfl]
    rfl
  · intro j hj
    have hne : j ≠ zero := fun he => by
      have hval := congrArg Fin.val he
      dsimp only [zero] at hval
      omega
    have hpaths : paths j = Classical.choose (hordinary j hj) := by
      dsimp only [paths]
      split
      · rename_i he
        exact (hne he).elim
      · rfl
    rw [hpaths]
    exact Classical.choose_spec (hordinary j hj)

/-- Keep the actual chosen ordinary cycles and their complement inventories
attached to the actual parent pieces. This witness supports subsequent J
propagation on this very parent cycle rather than an unrelated existence. -/
theorem recursive_cycle_from_special_with_inventory {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1)))
    (hq : q.IsHamiltonian) (hothers : OtherChildCycles hm F hB) :
    ∃ paths : ∀ j : Fin F.base.length, ActualChildPath F j,
      (paths ⟨0, by omega⟩).piece = (special_child_path hm F hB q hq).piece ∧
      (∀ (j : Fin F.base.length) (hj : 0 < j.val),
        ∃ a : {x : Configuration m // ChildDomain (childGap F j) x},
          ∃ w : (domainGraph (ChildDomain (childGap F j))).Walk a a,
          w.IsHamiltonianCycle ∧
          s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) ∈ w.edgeSet ∧
          ∀ e, e ∈ (paths j).piece.walk.edges ↔ e ∈ w.edges ∧
            e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj)) ∧
      ∃ pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)),
      ∃ a : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk a a,
      (∀ j, pieces j = parentPiece F j (paths j)) ∧
      a.val = rightPort F 0 ∧ c.IsHamiltonianCycle ∧
      c.support.tail = ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse ∧
      c.edges = s(a, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
        (chainEdges (pieces ⟨0, by omega⟩)
          (List.ofFn fun i : Fin (F.base.length - 1) =>
            pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse := by
  classical
  have hordinary (j : Fin F.base.length) (hj : 0 < j.val) :
      ∃ p : ActualChildPath F j,
        ∃ a : {x : Configuration m // ChildDomain (childGap F j) x},
          ∃ w : (domainGraph (ChildDomain (childGap F j))).Walk a a,
          w.IsHamiltonianCycle ∧
          s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) ∈ w.edgeSet ∧
          ∀ e, e ∈ p.piece.walk.edges ↔ e ∈ w.edges ∧
            e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj) := by
    obtain ⟨a, w, hw, hcut⟩ := hothers j hj
    obtain ⟨p, hinv⟩ := ordinary_child_open hm F hB j hj w hw hcut
    exact ⟨p, a, w, hw, hcut, hinv⟩
  let zero : Fin F.base.length := ⟨0, by omega⟩
  let paths (j : Fin F.base.length) : ActualChildPath F j :=
    if hj : j = zero then hj.symm ▸ special_child_path hm F hB q hq
    else Classical.choose (hordinary j (by
      have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
      omega))
  refine ⟨paths, ?_, ?_, native_parent_cycle_of_child_paths hm F hB paths⟩
  · simp only [paths, dif_pos rfl]
    rfl
  · intro j hj
    have hne : j ≠ zero := fun he => by have hval := congrArg Fin.val he; dsimp [zero] at hval; omega
    have hpaths : paths j = Classical.choose (hordinary j hj) := by
      dsimp only [paths]
      split
      · rename_i he
        exact (hne he).elim
      · rfl
    rw [hpaths]
    exact Classical.choose_spec (hordinary j hj)

private theorem recursive_cycle_from_special {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1)))
    (hq : q.IsHamiltonian) (hothers : OtherChildCycles hm F hB) :
    ∃ a : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk a a,
      a.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  obtain ⟨_, _, _, _, a, c, _, ha, hc, _, _⟩ :=
    recursive_cycle_from_special_with_inventory hm F hB q hq hothers
  exact ⟨a, c, ha, hc⟩

theorem native_recursive_even_cycle_step {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 2)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (pieces : List (Piece (domainGraph (SpecialDomain F hB))))
    (hs : (pieces.flatMap fun z => z.walk.support).Perm w.support.tail)
    (he : (pieces.flatMap fun z => z.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ specialCuts hm F hB)))
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edges)
    (hpair : ∀ z ∈ pieces,
      ∃ p q : Port (2 * s + 2), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        evenBoundary (2 * s + 2) (code p) (code q))
    (hothers : OtherChildCycles hm F hB) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
      base.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  obtain ⟨_, q, hq, _, _, _, _⟩ := native_special_child_even_path hm s F hB w hw pieces hs he hcuts hpair
  exact recursive_cycle_from_special hm F hB q hq hothers

theorem native_recursive_odd_cycle_step {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 3)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (pieces : List (Piece (domainGraph (SpecialDomain F hB))))
    (hs : (pieces.flatMap fun z => z.walk.support).Perm w.support.tail)
    (he : (pieces.flatMap fun z => z.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ specialCuts hm F hB)))
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edges)
    (hpair : ∀ z ∈ pieces,
      ∃ p q : Port (2 * s + 3), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        oddBoundary (2 * s + 3) (code p) (code q))
    (hothers : OtherChildCycles hm F hB) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
      base.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  obtain ⟨_, q, hq, _, _, _, _⟩ := native_special_child_odd_path hm s F hB w hw pieces hs he hcuts hpair
  exact recursive_cycle_from_special hm F hB q hq hothers

#print axioms native_recursive_even_cycle_step
#print axioms native_recursive_odd_cycle_step
#print axioms recursive_cycle_from_special_with_inventory
#print axioms recursive_cycle_from_specified_children_with_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
