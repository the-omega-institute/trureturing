---
bibkey: fu2019two
authors: Shishuo Fu, Zhicong Lin, and Jiang Zeng
year: 2019
title: "On two unimodal descent polynomials"
doi: 10.48550/arXiv.1507.05184
url: https://arxiv.org/abs/1507.05184v2
claim: "Proposition 2.1 records the classical direct/skew decomposition of actual 2413/3142 avoiders; Theorem 2.3 relates descents to skew nodes; Conjecture 5.2 separately asks for real-rootedness of their descent polynomials."
strata_touched:
  - D5/S1/Words/Patterns/Separable/ProperCut
  - D5/S1/Words/Patterns/Separable/CutFactorization
license: citation-only
triage: anchor
---

# Classical separable permutations

## Locator

The source DOI is 10.48550/arXiv.1507.05184 and the URL is
https://arxiv.org/abs/1507.05184v2, version dated 2019-02-05.
The year above identifies that revision; the initial submission was
18 July 2015, and the journal reference is *Discrete Mathematics* 341
(2018), 2616–2626. Proposition 2.1 calls the characterization folkloric and cites
Sergey Kitaev, *Patterns in permutations and words* (2011), page 57.
The book page was not independently available and remains uninspected.
The arXiv paper's full
Proposition 2.1, Definition 2.2, and Theorem 2.3 were checked directly.

## Supporting result

The source class consists of actual classical 2413/3142 avoiders. The
supporting Lean theorem proves that every such permutation of length at
least two has a nonempty proper prefix whose values are all smaller than,
or all larger than, every value in the suffix. It uses the existing
order-embedding definition of classical pattern containment. The graph
proof is implemented internally; the cograph characterization is not an
assumption.

The fixed-cut support in `CutFactorization` makes both block sums actual
permutations, using `finSumFinEquiv` without reversing either factor.
`avoids_block_sum_iff` proves literal 2413/3142 avoidance if and only if
both factors avoid them, for every pair of natural lengths and both
orientations. For positive lengths, `fixed_cut_factorization` proves
that an oriented cut is equivalent to a unique pair of actual avoiding
factors with exact reconstruction. Its inverse uses the ranks obtained
from `Tuple.sort`. These are the fixed-cut ingredients of the classical
decomposition in Proposition 2.1 and the greatest-cut construction in the
proof of Theorem 2.3; the fixed-cut theorem does not select a greatest cut.

For arbitrary positive factor lengths, `descents_block_sum` proves that
ordinary adjacent descents add under direct sum and gain exactly one
under skew sum. This is the local descent correspondence used in
Theorem 2.3. A singleton factor has zero descents. The theorem allows
singletons in either factor; the later greatest-cut decomposition must
separately establish its right-factor convention.

This is a formal proof of a known classical bridge, not a newly solved
open problem. It is supporting draft work for repository issue #9208;
there is no standalone FirstFreeze or typed open-problem resolution claim.
Conjecture 5.2's full real-rootedness assertion remains unresolved here.

Theorem 2.3 chooses the greatest valid cut for its di-sk-tree construction.
The proper-cut existence theorem does not select that greatest cut.
The fixed-cut inverse and its local descent law do not yet supply the
greatest-cut uniqueness and right-child sign condition, the
actual-avoider/tree bijection, weighted enumeration, or the ensuing
generating-function and real-rootedness arguments. For the increasing
permutation 123, a least-cut
choice would not by itself enforce the right-child sign condition of
Definition 2.2.
