/- GID: D5/S0/Certificates/SkeletonReturnSeedLowerBound
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonReturnSeedLowerBound
   mirror-E: none(waiver:reachable-return-cut-bound)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Disjoint reached regions with no incoming zero edge each require a distinct used return slot in the original skeleton. -/

import D5.S0.Certificates.SkeletonSlotCNF
import Mathlib.Data.Fintype.Card

/- The existing Skeleton, SlotWitness, blockStep and runTransition own all
   machine semantics. This module proves the return-seed condition used after
   smaller-capacity exclusion has forced full recurrent reachability. It does
   not assert that arbitrary padded candidates are reachable, and it introduces
   no new run function. The finite numerical searches are separate evidence.
   Logical review is complete; Lean elaboration has not been run here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonReturnSeedLowerBound

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Certificates.SkeletonSlotCNF

variable {r s : Nat} {K : Skeleton (Fin 4) (Fin r)}

private theorem run_outside_region (W : SlotWitness K s) (region : Set (Fin r))
    (zero_predecessors : ∀ q, W.zeroTarget q ∈ region → q ∈ region)
    (no_return : ∀ q, W.returnTarget (W.slotOf q) ∉ region)
    (word : List ReturnBlock) (p : Fin r) (outside : p ∉ region) (q : Fin r)
    (success : runTransition (fun u a => blockStep K a u) p word = some q) :
    q ∉ region := by
  induction word generalizing p with
  | nil =>
      have same : p = q := by
        simpa only [runTransition, Option.some.injEq] using success
      simpa only [same] using outside
  | cons a word ih =>
      cases a with
      | zero =>
          have tail : runTransition (fun u a => blockStep K a u)
              (W.zeroTarget p) word = some q := by
            simpa only [runTransition, blockStep, W.zero_eq] using success
          exact ih (W.zeroTarget p)
            (fun h => outside (zero_predecessors p h)) tail
      | oneZero =>
          have tail : runTransition (fun u a => blockStep K a u)
              (W.returnTarget (W.slotOf p)) word = some q := by
            simpa only [runTransition, blockStep, W.one_eq, Option.bind_some] using success
          exact ih (W.returnTarget (W.slotOf p)) (no_return p) tail

/-- If a region is reached from outside and no zero edge can enter it, some
actually selected return target enters it. Unused allocated slots do not supply
this witness. -/
theorem reached_region_has_used_return (W : SlotWitness K s)
    (region : Set (Fin r)) (start_outside : K.start ∉ region)
    (zero_predecessors : ∀ q, W.zeroTarget q ∈ region → q ∈ region)
    (q : Fin r) (member : q ∈ region) (word : List ReturnBlock)
    (success : runTransition (fun u a => blockStep K a u) K.start word = some q) :
    ∃ p : Fin r, W.returnTarget (W.slotOf p) ∈ region := by
  classical
  by_contra absent
  have no_return : ∀ p, W.returnTarget (W.slotOf p) ∉ region := by
    intro p h
    exact absent ⟨p, h⟩
  exact run_outside_region W region zero_predecessors no_return word
    K.start start_outside q success member

/-- A reached noninitial state with no zero predecessor must itself be a used
return target. This applies to every indegree-zero vertex of a fixed zero map. -/
theorem zero_leaf_is_used_return (W : SlotWitness K s) (q : Fin r)
    (noninitial : q ≠ K.start) (no_predecessor : ∀ p, W.zeroTarget p ≠ q)
    (word : List ReturnBlock)
    (success : runTransition (fun u a => blockStep K a u) K.start word = some q) :
    ∃ p : Fin r, W.returnTarget (W.slotOf p) = q := by
  have outside : K.start ∉ ({q} : Set (Fin r)) := by
    intro h
    exact noninitial (Set.mem_singleton_iff.mp h).symm
  have predecessors : ∀ p, W.zeroTarget p ∈ ({q} : Set (Fin r)) →
      p ∈ ({q} : Set (Fin r)) := by
    intro p h
    exact False.elim (no_predecessor p (Set.mem_singleton_iff.mp h))
  obtain ⟨p, hp⟩ := reached_region_has_used_return W {q} outside predecessors
    q (by simp) word success
  exact ⟨p, Set.mem_singleton_iff.mp hp⟩

/-- Pairwise disjoint reached regions closed under zero predecessors force
pairwise distinct selected slots. Each may be a zero leaf or an isolated zero
cycle. Reachability is an explicit premise, never a symmetry-breaking rule. -/
theorem disjoint_return_regions_bound_slots (W : SlotWitness K s) {k : Nat}
    (regions : Fin k → Set (Fin r))
    (separate : Pairwise (fun i j => Disjoint (regions i) (regions j)))
    (start_outside : ∀ i, K.start ∉ regions i)
    (zero_predecessors : ∀ i q, W.zeroTarget q ∈ regions i → q ∈ regions i)
    (reached : ∀ i, ∃ q : Fin r, q ∈ regions i ∧
      ∃ word : List ReturnBlock,
        runTransition (fun u a => blockStep K a u) K.start word = some q) :
    k ≤ s := by
  classical
  have entries : ∀ i, ∃ p : Fin r, W.returnTarget (W.slotOf p) ∈ regions i := by
    intro i
    obtain ⟨q, hq, word, success⟩ := reached i
    exact reached_region_has_used_return W (regions i) (start_outside i)
      (zero_predecessors i) q hq word success
  let source : Fin k → Fin r := fun i => Classical.choose (entries i)
  have member (i : Fin k) : W.returnTarget (W.slotOf (source i)) ∈ regions i :=
    Classical.choose_spec (entries i)
  let selected : Fin k → Fin s := fun i => W.slotOf (source i)
  have injective : Function.Injective selected := by
    intro i j same
    by_contra different
    have targets : W.returnTarget (selected i) = W.returnTarget (selected j) :=
      congrArg W.returnTarget same
    have both : W.returnTarget (selected i) ∈ regions j := by
      rw [targets]
      exact member j
    exact Set.disjoint_left.mp (separate different) (member i) both
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective selected injective

#print axioms reached_region_has_used_return
#print axioms zero_leaf_is_used_return
#print axioms disjoint_return_regions_bound_slots

end D5.S0.Certificates.SkeletonReturnSeedLowerBound
