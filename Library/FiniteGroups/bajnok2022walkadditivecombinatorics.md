---
bibkey: bajnok2022walkadditivecombinatorics
authors: Bela Bajnok
year: 2022
title: A Walk Through Some Newer Parts of Additive Combinatorics
doi: 10.48550/arXiv.2211.01893
url: https://arxiv.org/abs/2211.01893v1
claim: Conjecture 22 proposes a classification of finite abelian groups with perfect restricted bases; the binary Golay quotient lies outside its families.
strata_touched:
  - D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation
license: citation-only
triage: anchor
---

# The perfect restricted basis classification

Bela Bajnok, *A Walk Through Some Newer Parts of Additive Combinatorics*,
[arXiv:2211.01893v1](https://arxiv.org/abs/2211.01893v1), Section 3,
Conjecture 22, PDF page 10.

The original TeX states:

> For integers $m \geq 2$ and $s \geq 2$, perfect restricted $s$-bases of size
> $m$ exist if, and only if, $G$ has order $2^m$ or is isomorphic to
> $\mathbb{Z}_{2^{s+1}-1}$, $\mathbb{Z}_2^{2s}$, or to
> $\mathbb{Z}^{2s-2} \times \mathbb{Z}_4$.

The last family is printed without the subscript 2. The companion paper's
intended finite family is $\mathbb Z_2^{2s-2}\times\mathbb Z_4$.
The Golay quotient excludes both readings at $s=3,m=23$.

The definition and companion Question 11 are in B. Bajnok, C. Berson and
H. A. Just, *On Perfect Bases in Finite Abelian Groups*, Involve 15 (2022),
525–536, DOI [10.2140/involve.2022.15.525](https://doi.org/10.2140/involve.2022.15.525),
[arXiv:2211.13675v1](https://arxiv.org/abs/2211.13675v1), Section 4:

> Are there any groups that have a perfect restricted $s$-basis of size $m$
> with $m \geq 2s + 2$?

Here every group element must have a unique representing subset of size at
most $s$, including the empty subset. The formal construction uses the
existing literal `IsPerfectRestrictedBasis` predicate.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2211.01893.
The checked version is https://arxiv.org/abs/2211.01893v1,
Section 3, Conjecture 22, PDF page 10; its statement is quoted above.
