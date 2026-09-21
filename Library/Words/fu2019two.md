---
bibkey: fu2019two
authors: Shishuo Fu, Zhicong Lin, and Jiang Zeng
year: 2019
title: "On two unimodal descent polynomials"
doi: 10.48550/arXiv.1507.05184
url: https://arxiv.org/abs/1507.05184v2
claim: "Proposition 2.1 gives proper cuts of actual 2413/3142 avoiders; Theorem 2.3 selects the greatest cut and preserves descents; Corollary 2.4 gives signed enumeration recurrences; Conjecture 5.2 asks for real-rootedness."
strata_touched:
  - D5/S1/Words/Patterns/Separable/ProperCut
  - D5/S1/Words/Patterns/Separable/CutFactorization
  - D5/S1/Words/Patterns/Separable/GreatestCutEnumeration
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
Proposition 2.1, Definition 2.2, Theorem 2.3, and Corollary 2.4 with its proof
were checked directly in this revision.

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
singletons in either factor. The greatest-cut decomposition below establishes
its right-factor convention separately.

This is a formal proof of a known classical bridge, not a newly solved
open problem. It is supporting draft work for repository issue #9208;
there is no standalone FirstFreeze or typed open-problem resolution claim.
Conjecture 5.2's full real-rootedness assertion remains unresolved here.

`GreatestCutEnumeration.result` gives an equivalence between actual avoiders
with a proper oriented cut and triples of a positive split, an actual left
avoider, and an actual right avoider that is a singleton or has the opposite
orientation. Reconstruction is the literal `blockSum`, transported only
along the equality of lengths. The theorem certifies that the split is the
greatest proper cut of that orientation and preserves the descent count,
with one extra descent exactly for skew sum. Opposite proper cuts cannot
coexist, so greatestness agrees with the source's greatest valid cut.

The same result gives the exact finite polynomial and scalar coefficient
recurrences. Write D for the proper direct class and K for the proper skew
class in this paragraph, and let delta(n) be one at n=1 and zero otherwise.
For every natural length n,

$$S_n=\delta(n)+D_n+K_n,$$
$$D_n=\sum_{m+k=n;\,m,k>0}S_m(\delta(k)+K_k),\qquad
K_n=t\sum_{m+k=n;\,m,k>0}S_m(\delta(k)+D_k).$$

Here S0=0, S1=1, and D0=K0=D1=K1=0. The empty permutation remains an
avoider; S0=0 is the polynomial convention. In the proof of Corollary 2.4,
the source instead pads both signed sequences at length one, so its
S^(1) and S^(2) are delta+D and delta+K. The source's derangement polynomial
D is unrelated to the direct-class abbreviation used in this paragraph.
The scalar identities use ordinary finite convolution over a+b=r;
the skew constant coefficient is zero and the shifted identity is stated
at r+1. All statements hold for every length and every coefficient index.

This finite factor equivalence does not construct the entire
actual-avoider/di-sk-tree bijection. The generating-function cubic, gamma
identities, and the analytic real-rootedness argument remain separate.
For the increasing permutation 123, a least-cut choice would not by itself
enforce the right-child sign condition of Definition 2.2.
