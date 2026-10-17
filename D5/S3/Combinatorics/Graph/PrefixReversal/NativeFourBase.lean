/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: The actual zero-star complement closes to a Hamilton cycle on all 24 permutations. -/

import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeFourBase

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

/-- The three actual reversals of lengths four, three and two have a Hamilton cycle.
The path is the existing literal zero-star complement; its 24 distinct vertices exhaust
the full permutation group, and the removed three-prefix edge closes the cycle. -/
theorem native_four_hamiltonian_cycle :
    ∃ base : Configuration 3,
      ∃ w : (SimpleGraph.mulCayley ({a 3, b 3, c 3} : Set (Configuration 3))).Walk
        base base, w.IsHamiltonianCycle := by
  classical
  let W := delete (0 : Fin 4) (configurationCycle (1 : Configuration 3))
  have hv : Star (0 : Fin 4) W (1 : Configuration 3) := Or.inl rfl
  obtain ⟨hvb, p, hp, hlen, _⟩ :=
    zeroStar_b_complement_hamiltonian (by omega : 3 ≤ 3) 0 W 1 hv (0 : Fin 3) rfl
  let G := SimpleGraph.mulCayley ({a 3, b 3, c 3} : Set (Configuration 3))
  let f : ((starFactor (0 : Fin 4) W).deleteEdges
      ({s((⟨1, hv⟩ : {x : Configuration 3 // Star 0 W x}),
        (⟨1 * b 3, hvb⟩ : {x : Configuration 3 // Star 0 W x}))} : Set _)) →g G :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        have hs := (SimpleGraph.deleteEdges_adj.mp hxy).1
        exact hs.1 }
  have hcard : Fintype.card {x : Configuration 3 // Star 0 W x} = 24 := by
    rw [← hp.length_support, SimpleGraph.Walk.length_support, hlen]
  have hf : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    refine ⟨Subtype.val_injective, ?_⟩
    rw [hcard]
    norm_num [Configuration, Fintype.card_perm, Nat.factorial]
  let q := p.map f
  have hq : q.IsHamiltonian := hp.map hf
  have hbn : b 3 ≠ (1 : Configuration 3) := by
    intro he
    have hx := congrArg (fun z : Configuration 3 => (z (0 : Fin 4)).val) he
    simp only [b_apply, Fin.val_zero, Equiv.Perm.one_apply] at hx
    norm_num at hx
  have hclose : G.Adj (1 * b 3) 1 := by
    change (SimpleGraph.mulCayley _).Adj _ _
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨by simpa using hbn, b 3, by simp, Or.inr (by simp)⟩
  refine ⟨1 * b 3, SimpleGraph.Walk.cons hclose q, ?_⟩
  apply SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
  constructor
  · apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa using hq.isPath
    · simp only [SimpleGraph.Walk.length_cons, q, SimpleGraph.Walk.length_map, hlen]
      norm_num
  · intro x
    simpa only [SimpleGraph.Walk.support_cons, List.tail_cons] using hq x

#print axioms native_four_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeFourBase
