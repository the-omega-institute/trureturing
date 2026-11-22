---
bibkey: benfieldlippard2025positivepowers
authors: Brennan Benfield, Oliver Lippard
year: 2025
title: "Integers that are not the sum of positive powers"
doi: null
url: https://arxiv.org/abs/2404.08193v2
claim: 'Conjecture 10.5. The sequence $|B_k|$ for $k=2,3,\ldots$ never becomes monotone.'
strata_touched:
  - D5/S3/Arith/Additive/BenfieldLippard/Result
license: citation-only
triage: anchor
---

# Integers that are not the sum of positive powers

Conjecture 10.5 is in §10.1 of arXiv:2404.08193v2. Section 1 takes the
positive offsets s = n − j from integers n > j that have no representation
by exactly j positive kth powers. The bases may repeat. The cardinalities
of the eventual finite offset sets give the sequence in the conjecture.

Theorem 1.1 credits A. A. Zenkin [65] with eventual fixed-length
cofiniteness. For every k ≥ 2, at each fixed j ≥ G(1,k), all but finitely
many positive integers are sums of exactly j positive kth powers.
Reference [65] is *Waring's problem from the standpoint of the cognitive
interactive computer graphics*. [Theorem 1.1](https://arxiv.org/html/2404.08193v2#S1.Thmtheorem1) · [Ref. 65](https://arxiv.org/html/2404.08193v2#bib.bib65) · <https://doi.org/10.1016/0895-7177(90)90060-z>

Conjecture 1.2 gives the stable finite offset formulation.
`BenfieldLippard.stabilization` derives equality with the positive gaps
of the shifted-power monoid from the formal fixed-length Waring bridge.
Starting at a length j₀ with finitely many exceptions, it takes the
maximum of j₀ and the supremum of the witness lengths for exceptions
that eventually acquire a representation. The j₀ bound allows
padding of representations already available at j₀.
[Conjecture 1.2](https://arxiv.org/html/2404.08193v2#S1.Thmtheorem2)

The mathematical input is Hilbert's qualitative Waring theorem. The
Waring formalization authors proved the Lean theorem using Linnik's
method as presented in Tim Jameson's notes.
[Hilbert](https://doi.org/10.1007/BF01450405) · [Tim Jameson, p. 1](https://www.maths.lancs.ac.uk/jameson/warlin.pdf#page=1)

The bounded literature check covered the two arXiv versions, arXiv
title and topic searches, DataCite, Crossref and the OpenAlex record
W4394838815. It found the same conjecture in both versions and identified
no prior complete resolution. Semantic Scholar returned HTTP 429, and
priority beyond this search remains unverified.

## Verified locator

Versioned source: https://arxiv.org/abs/2404.08193v2

Conjecture 10.5 is in Section 10.1, page 10, at
https://arxiv.org/html/2404.08193v2#S10.Thmtheorem5.
Theorem 1.1 and the exception-set definitions are in Section 1.
The lower-bound comparison uses Theorem 10.7 in Section 10.1.
