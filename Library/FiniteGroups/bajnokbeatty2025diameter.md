---
bibkey: bajnokbeatty2025diameter
authors: Bela Bajnok and W. Kyle Beatty
year: 2025
title: On the diameter of undirected Cayley graphs of finite abelian groups
doi: 10.2140/cnt.2025.14.1
url: https://arxiv.org/abs/2406.04045v1
claim: Conjecture 4.1 concerns signed two-generator diameter in Z/2 times Z/(2k); the formal result proves one uniform sufficient family and leaves the converse open.
strata_touched:
  - D5/S3/FiniteGroups/BajnokBeattyCayleySufficiency
license: citation-only
triage: anchor
---

# On the diameter of undirected Cayley graphs of finite abelian groups

Bela Bajnok and W. Kyle Beatty, *Combinatorics and Number Theory* **14** (2025),
no. 1, 1–12. The accessible full text checked here is arXiv:2406.04045v1,
submitted 6 June 2024. The publisher records a revision on 26 October 2024;
the published full text was not accessed because the download returned
subscription-access-denied HTML. Conclusions about the paper's precise
theorem scope refer to arXiv v1, and do not certify literature novelty.

In Section 4, an s-spanning pair represents every group element with integer
coefficients whose absolute values sum to at most s. Conjecture 4.1 gives a
classification for Z/2 × Z/(2k). Theorem 4.2 proves a necessary order bound;
Theorem 4.3 treats odd s; Theorem 4.4 gives sufficiency for even s only when
k ≤ (s²−s)/2. Theorem 1.9 asserts the maximal order 2s² at even radius
for groups of this form; it therefore already attests the j=0 endpoint.
That endpoint is not claimed as a new positive case here.

The earlier positive constructions do not directly supply the whole retained
family. Proposition 2.2 is cyclic. Proposition 2.3 concerns Z/s × Z/(2s).
Theorem 2.4 requires s mod c ≥ (c−1)/2, which for c=2 allows only odd s.
Corollary 2.5 has odd first invariant factor.

The repository construction proves: for t ≥ 1 and 0 ≤ j < t with t even or
j even, k=2(t²−j) admits a distinct signed spanning pair of radius at most 2t.
It therefore includes the allowed top strip 0 ≤ 2j < t. A simultaneous
integer remainder descent supplies the covering, and explicit surjective
maps supply the exact group Z/2 × Z/(2k). This is a repo-derived sufficient
construction. It proves neither exclusion of other pairs nor the conjecture's
general necessity direction. The nonprimitive excluded displayed lattice
does not exclude alternative primitive lattices.

## Verified locator

DOI: https://doi.org/10.2140/cnt.2025.14.1

Source: https://arxiv.org/abs/2406.04045v1

## Necessary congruences in the even-radius top strip

The repository's necessity result applies to every pair in Z/2 × Z/(2k).
For integers t ≥ 1 and 0 ≤ r < t with k=2t²−r, a signed coefficient
cover of radius 2t forces 2 | r and, when t is odd, 4 | r. It imposes no
chosen lattice form or distinctness hypothesis on the pair.

The mechanism uses the actual relation quotient. For n ≥ 2 and
0 ≤ δ < n, a square [0,n)² covering Z²/L with quotient order n²−δ
forces L to have basis (n,−εb), (−a,εn), where ε=±1,
0 ≤ a,b < n and ab=δ. Least adjacent-column displacements and
determinant divisibility force this basis; the determinant-index identity
is supplied by pinned Mathlib, not claimed as new mathematics.

For an arbitrary covering pair, the affine odd coefficient class becomes
a square torsor under the sum-and-difference map. Its relation quotient
has order 2k, so the rigidity result applies with n=2t and δ=2r.
Parity forces both displacement parameters to be even. When t is odd,
failure of 4 | r would force the entire original relation kernel into
4Z², contradicting the first Z/2 factor. Thus the argument excludes
alternative pairs, beyond checking the displayed sufficient construction.

This is a repo-derived necessary direction in the stated top strip,
alongside the sufficient family above. The source comparison remains
arXiv:2406.04045v1, Conjecture 4.1 and Theorems 4.2–4.4. The revised
paper has not been read; neither the full conjecture nor literature
novelty is asserted by this increment.
