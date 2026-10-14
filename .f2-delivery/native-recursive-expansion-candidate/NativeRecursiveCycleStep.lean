/- UNCOMPILED actual recursive cycle step.
   Special coverage is earned by the real E/O slice assembly. Ordinary
   paths are real single-cut complements of previous child cycles. The
   full independent parent domain is earned by NativeOuterChildAssembly.
   This is not yet an all-n induction: the next J-state still needs its
   own b-cut membership and E/O endpoint propagation. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering
open private special_cuts_nonempty from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly

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

private def special_child_path {m k : ℕ} (hm : 3 ≤ m)
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

private theorem recursive_cycle_from_special {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1)))
    (hq : q.IsHamiltonian) (hothers : OtherChildCycles hm F hB) :
    ∃ a : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk a a,
      a.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  classical
  have hordinary (j : Fin F.base.length) (hj : 0 < j.val) : Nonempty (ActualChildPath F j) := by
    obtain ⟨a, w, hw, hcut⟩ := hothers j hj
    obtain ⟨p, _⟩ := ordinary_child_open hm F hB j hj w hw hcut
    exact ⟨p⟩
  let paths (j : Fin F.base.length) : ActualChildPath F j := by
    by_cases hj : j.val = 0
    · have he : j = ⟨0, by omega⟩ := Fin.ext hj
      subst j
      exact special_child_path hm F hB q hq
    · exact Classical.choice (hordinary j (by omega))
  obtain ⟨_, a, c, ha, hc, _, _⟩ := native_parent_cycle_of_child_paths hm F hB paths
  exact ⟨a, c, ha, hc⟩

theorem native_recursive_even_cycle_step {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 2)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edgeSet)
    (hpair : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
        (special_cuts_nonempty hm F hB) hcuts,
      ∃ p q : Port (2 * s + 2), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        evenBoundary (2 * s + 2) (code p) (code q))
    (hothers : OtherChildCycles hm F hB) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
      base.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  obtain ⟨_, q, hq, _, _, _⟩ := native_special_child_even_path hm s F hB w hw hcuts hpair
  exact recursive_cycle_from_special hm F hB q hq hothers

theorem native_recursive_odd_cycle_step {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 3)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edgeSet)
    (hpair : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
        (special_cuts_nonempty hm F hB) hcuts,
      ∃ p q : Port (2 * s + 3), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        oddBoundary (2 * s + 3) (code p) (code q))
    (hothers : OtherChildCycles hm F hB) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
      base.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  obtain ⟨_, q, hq, _, _, _⟩ := native_special_child_odd_path hm s F hB w hw hcuts hpair
  exact recursive_cycle_from_special hm F hB q hq hothers

#print axioms native_recursive_even_cycle_step
#print axioms native_recursive_odd_cycle_step

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
