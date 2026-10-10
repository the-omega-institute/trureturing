# The Valuation-Step Greedy Permutation

## Abstract

The valuation-step greedy sequence is a permutation of the positive integers.

OEIS A382357 starts with 1. The next term is the least unused positive integer whose 2-adic valuation differs by exactly one from the current valuation. The natural index starts at zero. An unused value at the next higher level always exists, so the rule never stalls and gives the lexicographically earliest allowed sequence.

**Definition 1.1 (The exact adjacency condition).**

$$\operatorname{Adjacent}\left(x, y\right) \iff \operatorname{add}\left(\operatorname{valuation}\left(2, x\right), 1\right) = \operatorname{valuation}\left(2, y\right) \lor \operatorname{add}\left(\operatorname{valuation}\left(2, y\right), 1\right) = \operatorname{valuation}\left(2, x\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Either valuation increases by one or it decreases by one. The condition does not impose a distance bound on the integers.

**Definition 1.2 (The least positive unused adjacent value).**

$$\operatorname{next}\left(l, c\right) = \operatorname{find}\left(\operatorname{positiveunusedadjacent}\left(l, c\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.next` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.find minimizes the positive integer itself. Its predicate requires positivity, absence from the full supplied history and the literal adjacency condition. A sufficiently large odd multiple of the next power of two proves nonemptiness.

**Definition 1.3 (The full reversed history).**

$$\operatorname{terms}\left(0\right) = \operatorname{singleton}\left(1\right) \land \operatorname{terms}\left(\operatorname{add}\left(n, 1\right)\right) = \operatorname{cons}\left(\operatorname{next}\left(\operatorname{terms}\left(n\right), \operatorname{headD}\left(\operatorname{terms}\left(n\right), 1\right)\right), \operatorname{terms}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.terms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The history starts at [1]. Each successor prepends the least unused adjacent positive integer. No term is discarded or repeated.

**Definition 1.4 (OEIS A382357).**

$$\operatorname{a}\left(n\right) = \operatorname{headD}\left(\operatorname{terms}\left(n\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence value is the head of its nonempty history. Thus a(0)=1 is the OEIS term a(1).

**Definition 1.5 (The permutation conjecture).**

$$\operatorname{injective}\left(\operatorname{a}\right) \land \forall m \in \mathbb{N}, 0 < m \implies \exists n \in \mathbb{N}, \operatorname{a}\left(n\right) = m$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact claim combines injectivity and occurrence of every positive integer.

**Theorem 1.6 (Every positive integer appears exactly once).**

$$\operatorname{injective}\left(\operatorname{a}\right) \land \forall m \in \mathbb{N}, 0 < m \implies \exists n \in \mathbb{N}, \operatorname{a}\left(n\right) = m$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a382357-valuation-step-permutation` (proved) by `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a382357-valuation-step-permutation","declaration_gid":"D5/S3/Combinatorics/Permutation/ValuationStepPermutation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Each level k is a queue of the values 2^k(2r+1), r starting at zero. Greedy minimality takes the least unused value of the chosen level. A recurrent level forces every value at each neighboring level to appear: an omitted value would bound infinitely many distinct successor terms. If level zero were not recurrent, no level would be recurrent and the height would eventually exceed each fixed bound. In a finite prefix ending above a prescribed height, let D_j count downward crossings from j to j-1. The visits to any lower level j number D_j+D_(j+1)+1. At its last exit, the upper candidate is at least 2^(j+1)(2D_(j+1)+1), while the unused lower candidate is at most 2^(j-1)(2(D_(j-1)+D_j+1)+1). Greedy comparison gives D_(j-1)+D_j >= 4D_(j+1)+1. The potential D_j+2D_(j+1) decreases by at least one at every level. Downward crossings to zero are bounded after the height stays above one, contradicting arbitrarily long potential descent. Level zero is therefore recurrent, and propagation covers every positive integer. The factor-four comparison is specific to 2-adic valuation; the analogous Omega and omega statements remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.Adjacent`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.a`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.next`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ValuationStepPermutation.terms`
