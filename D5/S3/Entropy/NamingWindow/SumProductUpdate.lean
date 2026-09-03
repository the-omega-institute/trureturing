/- GID: D5/S3/Entropy/NamingWindow/SumProductUpdate
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/SumProductUpdate
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: One public home for the coordinate sum-product identity three frozen files re-prove. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none truncated. Declaration patterns are the wide form, and file names come from
   `git grep -l`.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '
   git grep -hoE "${P}sum_prod_update" origin/dev -- 'D5/**/*.lean' | wc -l                  -> 3
     All three opened and found to be the same statement, verbatim, differing in nothing:
       D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.lean:39
       D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.lean:34
       D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.lean:50
     Each is `private` and each fixes the codomain to `Real`. All three modules are frozen,
     with exactly one Freeze event each:
       git grep -l "NamingWindow/<module>.lean" origin/dev -- Golden/Frozen/accepted/ | wc -l
                                                                                       -> 1 each
     An earlier draft of this trail said one, one and two, from a substring search on the module
     name; the extra hit belonged to `GreenClassWindowEntropyEquality.lean`, a different module
     sharing the prefix. The selector-qualified command above is the one to trust.
     Being frozen, none of the three can be amended to import a shared lemma; this module cannot
     remove those copies, only stop a fourth from appearing.

   Relative to each private copy, the public statement below differs in exactly three ways: the
   `private` modifier is dropped, `{R : Type*} [CommSemiring R]` is added, and the three
   signature occurrences of `Real` become `R`. Hypotheses, conclusion and proof body are
   otherwise unchanged.

   Two of the three record the reason in their own headers, in the repository's words:
     "Those local facts are private and not reusable public theorems."
     "This file intentionally re-proves the same finite sum-product and coordinate-normalization"
   That is a documented demand for a public form, not an inference drawn here.

   No public form exists:
   git grep -hoE "${P}sum_prod_update" origin/dev -- 'D5/**/*.lean' | grep -vc private
                                                                                             -> 0

   The proof below is the frozen proof, generalised. It uses `Function.update`,
   `Finset.mul_prod_erase`, `Finset.prod_congr`, `Finset.sum_congr`, `mul_comm` and
   `Fintype.prod_sum` — none of which needs subtraction, division or an order — so the same
   argument works over any commutative semiring, which is the second thing this module adds.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this loop and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried. Live unmerged mathlib pull requests could not be searched: the
   local pin exposes no `refs/pull/` data and this environment has no network for that query.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi

/-!
# The coordinate sum-product identity, once and publicly

Summing over every assignment the product of all coordinates except one, times a factor at that
one coordinate, factors into the product of the other coordinates' sums times the sum of that
factor.

**This is API value, not new mathematics.** The identity is an immediate consequence of the
distributive law for finite products of sums; what it lacks in the repository is a public name.
Three frozen modules in this directory each carry a `private` copy of it, two of them recording
in their headers that they re-prove it because the earlier copies are private and not reusable.
Those three are frozen and cannot import this module; naming the fact here does not remove them,
it stops the next one.

The statement is also freed from `Real`: the argument needs no subtraction, division or order,
so it is given over an arbitrary commutative semiring.
-/

namespace D5.S3.Entropy.NamingWindow.SumProductUpdate

/-- Summing an assignment-indexed product with one coordinate replaced by `g` factors into the
product of the remaining coordinate sums times the sum of `g`. -/
theorem sum_prod_update {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    {R : Type*} [CommSemiring R] (p : ι → O → R) (i : ι) (g : O → R) :
    (∑ u : ι → O, (∏ j ∈ Finset.univ.erase i, p j (u j)) * g (u i)) =
      (∏ j ∈ Finset.univ.erase i, ∑ a, p j a) * ∑ a, g a := by
  classical
  have hupd : ∀ u : ι → O,
      (∏ j ∈ Finset.univ.erase i, p j (u j)) * g (u i) =
        ∏ j, (Function.update p i g) j (u j) := by
    intro u
    rw [← Finset.mul_prod_erase _ (fun j => (Function.update p i g) j (u j))
      (Finset.mem_univ i), Function.update_self]
    refine (mul_comm _ _).trans ?_
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Finset.sum_congr rfl fun u _ => hupd u,
    ← Fintype.prod_sum (fun j => (Function.update p i g) j),
    ← Finset.mul_prod_erase _ (fun j => ∑ a, (Function.update p i g) j a)
      (Finset.mem_univ i), Function.update_self]
  refine (mul_comm _ _).trans ?_
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

end D5.S3.Entropy.NamingWindow.SumProductUpdate
