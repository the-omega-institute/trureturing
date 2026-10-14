/- UNCOMPILED native E/O instances of the actual-piece assembler.
   The public RecursivePortBoundary whole-edge enumeration supplies
   reordering; its internally proved seam recipe is realized by the
   independently verified native c-generator coordinates. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering
open private special_cuts_nonempty from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly
open private code_injective even_route_seam_step odd_route_seam_step
  even_route_last1_eq odd_route_last3_eq from
  D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary

def evenPortRoute (s : ℕ) (j : Fin (2 * (2 * s + 3))) : Port (2 * s + 2) :=
  evenEnumerate s (Fin.cast (by omega) j)

def oddPortRoute (s : ℕ) (j : Fin (2 * (2 * s + 4))) : Port (2 * s + 3) :=
  oddEnumerate s (Fin.cast (by omega) j)

private theorem even_native_route_start (s : ℕ) :
    evenPortRoute s ⟨0, by omega⟩ = (0, 0) := by
  apply code_injective
  change evenRoute s 0 = (0, 0)
  simp only [evenRoute, Nat.zero_le, ↓reduceIte, Nat.zero_mod]

private theorem odd_native_route_start (s : ℕ) :
    oddPortRoute s ⟨0, by omega⟩ = (0, 0) := by
  apply code_injective
  change oddRoute s 0 = (0, 0)
  simp only [oddRoute, Nat.zero_le, ↓reduceIte, Nat.zero_mod]

private theorem even_native_route_finish (s : ℕ) :
    evenPortRoute s ⟨2 * (2 * s + 3) - 1, by omega⟩ = (Fin.last (2 * s + 2), 1) := by
  apply code_injective
  change evenRoute s (2 * (2 * s + 3) - 1) = (2 * s + 2, 1)
  rw [show 2 * (2 * s + 3) - 1 = 4 * s + 5 by omega]
  exact even_route_last1_eq s

private theorem odd_native_route_finish (s : ℕ) :
    oddPortRoute s ⟨2 * (2 * s + 4) - 1, by omega⟩ = (Fin.last (2 * s + 3), 1) := by
  apply code_injective
  change oddRoute s (2 * (2 * s + 4) - 1) = (2 * s + 3, 1)
  rw [show 2 * (2 * s + 4) - 1 = 4 * s + 7 by omega]
  exact odd_route_last3_eq s

theorem native_special_child_even_path {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 2)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edgeSet)
    (hpair : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
        (special_cuts_nonempty hm F hB) hcuts,
      ∃ p q : Port (2 * s + 2), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        evenBoundary (2 * s + 2) (code p) (code q)) :
    ∃ ordered : Fin (2 * s + 3) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (0, 0))
        (specialVertex hm F hB (Fin.last (2 * s + 2), 1)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = specialVertex hm F hB
          (evenPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish = specialVertex hm F hB
          (evenPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0)
        (List.ofFn fun i : Fin (2 * s + 2) => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB := by
  have honce (p q : Port (2 * s + 2))
      (hb : evenBoundary (2 * s + 2) (code p) (code q)) :
      ∃! i : Fin (2 * s + 3), s(p, q) = routeEdge (evenPortRoute s) i := by
    simpa only [routeEdge, evenPortRoute, evenBEdge] using even_boundary_edges_once s p q hb
  have hseams (i : ℕ) (hi : i + 1 < 2 * s + 3) :
      internalSeam (2 * s + 2)
        (code (evenPortRoute s ⟨2 * i + 1, by omega⟩))
        (code (evenPortRoute s ⟨2 * (i + 1), by omega⟩)) := by
    change internalSeam (2 * s + 2) (evenRoute s (2 * i + 1)) (evenRoute s (2 * (i + 1)))
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
      even_route_seam_step s (2 * i + 1) (by omega) (by omega)
  obtain ⟨ordered, q, hq, hend, hs, he, hinv⟩ :=
    native_special_child_assembled hm F hB w hw hcuts
      (evenBoundary (2 * s + 2)) (evenPortRoute s) honce hpair hseams
  let q' := q.copy (congrArg (specialVertex hm F hB) (even_native_route_start s))
    (congrArg (specialVertex hm F hB) (even_native_route_finish s))
  refine ⟨ordered, q', ?_, hend, ?_, ?_, hinv⟩
  · intro x
    simpa only [q', SimpleGraph.Walk.support_copy] using hq x
  · simpa only [q', SimpleGraph.Walk.support_copy] using hs
  · simpa only [q', SimpleGraph.Walk.edges_copy] using he

theorem native_special_child_odd_path {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 3)) (hB : 3 ≤ F.base.length)
    {a : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a) (hw : w.IsHamiltonianCycle)
    (hcuts : ∀ e ∈ specialCuts hm F hB, e ∈ w.edgeSet)
    (hpair : ∀ z ∈ cyclePieces (specialCuts hm F hB) w hw
        (special_cuts_nonempty hm F hB) hcuts,
      ∃ p q : Port (2 * s + 3), z.start.val = specialPort F p ∧
        z.finish.val = specialPort F q ∧
        oddBoundary (2 * s + 3) (code p) (code q)) :
    ∃ ordered : Fin (2 * s + 4) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (0, 0))
        (specialVertex hm F hB (Fin.last (2 * s + 3), 1)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = specialVertex hm F hB
          (oddPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish = specialVertex hm F hB
          (oddPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0)
        (List.ofFn fun i : Fin (2 * s + 3) => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB := by
  have honce (p q : Port (2 * s + 3))
      (hb : oddBoundary (2 * s + 3) (code p) (code q)) :
      ∃! i : Fin (2 * s + 4), s(p, q) = routeEdge (oddPortRoute s) i := by
    simpa only [routeEdge, oddPortRoute, oddBEdge] using odd_boundary_edges_once s p q hb
  have hseams (i : ℕ) (hi : i + 1 < 2 * s + 4) :
      internalSeam (2 * s + 3)
        (code (oddPortRoute s ⟨2 * i + 1, by omega⟩))
        (code (oddPortRoute s ⟨2 * (i + 1), by omega⟩)) := by
    change internalSeam (2 * s + 3) (oddRoute s (2 * i + 1)) (oddRoute s (2 * (i + 1)))
    simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
      odd_route_seam_step s (2 * i + 1) (by omega) (by omega)
  obtain ⟨ordered, q, hq, hend, hs, he, hinv⟩ :=
    native_special_child_assembled hm F hB w hw hcuts
      (oddBoundary (2 * s + 3)) (oddPortRoute s) honce hpair hseams
  let q' := q.copy (congrArg (specialVertex hm F hB) (odd_native_route_start s))
    (congrArg (specialVertex hm F hB) (odd_native_route_finish s))
  refine ⟨ordered, q', ?_, hend, ?_, ?_, hinv⟩
  · intro x
    simpa only [q', SimpleGraph.Walk.support_copy] using hq x
  · simpa only [q', SimpleGraph.Walk.support_copy] using hs
  · simpa only [q', SimpleGraph.Walk.edges_copy] using he

#print axioms native_special_child_even_path
#print axioms native_special_child_odd_path

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
