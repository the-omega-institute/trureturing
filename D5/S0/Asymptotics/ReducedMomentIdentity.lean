/- GID: D5/S0/Asymptotics/ReducedMomentIdentity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/ReducedMomentIdentity
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Deleting one atom and weighting by its gap turns two power sums into one moment. -/

/- Library-search audit trail (2026-09-02). Commands reproduced literally as run, each with the
   count it returned. Paths are relative to the delivery worktree.

   grep -i -c 'Christoffel' /tmp/decl_names.txt                                              -> 2
   grep -i -c 'Christoffel' /tmp/mod_names.txt                                               -> 1
   git grep -in 'Christoffel' origin/dev -- '*.lean' | wc -l                                 -> 31
     Those thirty-one lines lie in exactly two modules, both opened by digest:
     `ChristoffelAtomFloor` (positive atoms give a positive floor for the Christoffel cost) and
     `ChristoffelSupportDecay` (unit-circle support gives exterior witnesses and exponential cost
     decay). Both are about the cost functional; neither states a moment identity.
   grep -i -c 'momentSequence' /tmp/decl_names.txt                                            -> 0
   grep -i -c 'reducedMeasure' /tmp/decl_names.txt                                            -> 0
   git grep -in 'momentSequence' origin/dev -- '*.lean' | wc -l                               -> 0
   git grep -in 'reducedMeasure' origin/dev -- '*.lean' | wc -l                               -> 0

   grep -ril "Christoffel"     .lake/packages/mathlib --include='*.lean' | wc -l              -> 0
   grep -ril "reduced moment"  .lake/packages/mathlib --include='*.lean' | wc -l              -> 0
   grep -ril "moment.*erase"   .lake/packages/mathlib --include='*.lean' | wc -l              -> 0
   grep -ril "sum_erase.*pow"  .lake/packages/mathlib --include='*.lean' | wc -l              -> 0
     The same four over batteries                                                 -> 0 each

   gh search prs --repo leanprover-community/mathlib4 --state open "Christoffel function"
     --limit 20                                                                              -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open "reduced moment sequence"
     --limit 20                                                                              -> 0
   gh search code --repo leanprover/cslib "Christoffel" --limit 5                             -> 0
   gh search code --repo TauCetiProject/TauCeti "Christoffel" --limit 5                       -> 5
     All five were opened. Every one is the differential-geometric Christoffel symbol of a
     connection — coordinate-change law, Christoffel form in a local frame, Levi-Civita geodesics,
     regularity, pullback along a curve. That is a different object from the Christoffel function
     of orthogonal-polynomial theory, and none states a moment identity.

   Zulip was not queried for this statement, so that domain is absent rather than a negative.

   The upstream results used rather than reproved are `Finset.sum_erase_add`, `Finset.mul_sum`,
   `Finset.sum_sub_distrib` and `pow_succ`.
-/

import Mathlib

/-!
# A deleted atom turns two power sums into one weighted moment

Fix a finite index set, a distinguished index inside it, and a family of ring elements. Delete the
distinguished atom, weight each surviving atom by its own value times its gap to the distinguished
one, and take the `n`-th moment. The result is the distinguished value times the `(n+1)`-st power
sum, minus the `(n+2)`-nd power sum.

The distinguished index carries a vanishing gap, so it contributes nothing and may be summed over
freely; that is the whole content. No positivity, ordering, or measure-theoretic hypothesis is used
or needed here, and none is claimed.
-/

namespace D5.S0.Asymptotics.ReducedMomentIdentity

variable {iota R : Type*} [DecidableEq iota] [CommRing R]

/-- The gap-weighted moment over the deleted index set equals the distinguished value times one
power sum minus the next power sum. -/
theorem reducedMoment_eq (S : Finset iota) (i : iota) (x : iota → R) (n : Nat) :
    (∑ j ∈ S.erase i, x j * (x i - x j) * x j ^ n) =
      x i * (∑ j ∈ S.erase i, x j ^ (n + 1)) -
        ∑ j ∈ S.erase i, x j ^ (n + 2) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- With the distinguished index present, the same moment is read off the full power sums. -/
theorem reducedMoment_eq_of_mem (S : Finset iota) (i : iota) (hi : i ∈ S) (x : iota → R)
    (n : Nat) :
    (∑ j ∈ S.erase i, x j * (x i - x j) * x j ^ n) =
      x i * (∑ j ∈ S, x j ^ (n + 1)) - ∑ j ∈ S, x j ^ (n + 2) := by
  rw [← Finset.sum_erase_add S _ hi, ← Finset.sum_erase_add S _ hi, reducedMoment_eq]
  ring

end D5.S0.Asymptotics.ReducedMomentIdentity
