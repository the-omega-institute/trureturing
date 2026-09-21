---
bibkey: fu2019two
authors: Shishuo Fu, Zhicong Lin, and Jiang Zeng
year: 2019
title: "On two unimodal descent polynomials"
doi: 10.48550/arXiv.1507.05184
url: https://arxiv.org/abs/1507.05184v2
claim: "Proposition 2.1 records the classical direct/skew decomposition of actual 2413/3142 avoiders; Conjecture 5.2 separately asks for real-rootedness of their descent polynomials."
strata_touched:
  - D5/S1/Words/Patterns/Separable/ProperCut
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

This is a formal proof of a known classical bridge, not a newly solved
open problem. It is supporting draft work for repository issue #9208;
there is no standalone FirstFreeze or typed open-problem resolution claim.
Conjecture 5.2's full real-rootedness assertion remains unresolved here.

Theorem 2.3 chooses the greatest valid cut for its di-sk-tree construction.
The existence proof in this module does not select that greatest cut.
Standardization, the actual-avoider/tree bijection, descent preservation,
and the ensuing generating-function and real-rootedness arguments remain
separate obligations. For the increasing permutation 123, a least-cut
choice would not by itself enforce the right-child sign condition of
Definition 2.2.
