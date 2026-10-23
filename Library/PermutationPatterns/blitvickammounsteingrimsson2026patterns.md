---
bibkey: blitvickammounsteingrimsson2026patterns
authors: Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson
year: 2026
title: "Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets"
doi: 10.48550/arXiv.2610.29846
url: https://arxiv.org/abs/2610.29846v1
claim: "Conjecture 7.1: prescribed interleaved minimal prefix and suffix attain the maximum packing count for m≤K/2."
strata_touched:
  - D5/S3/Combinatorics/Permutation/PackingMaximumRefutation
license: citation-only
triage: anchor
---

# Prescribed permutation packing

The primary source is arXiv:2610.29846v1, submitted 21 October 2026.
Definition 2.2 defines order isomorphism by agreement of every strict
comparison. Definition 2.6 and equation (2.1) define a permutation of length
$n=K+(j-1)(K-m)$ that has a copy of the $K$-pattern at each start
$1+t(K-m)$, for $0\le t<j$. Remark 2.7 explicitly permits additional
occurrences. This is a prescribed packing count, rather than avoidance
or a count with exactly $j$ total occurrences.

Definition 3.3 and its following paragraph require order-compatible
$m$-prefix and $m$-suffix. The important convention in Section 3 uses
increasing prefix and suffix, with the first prefix value smaller, after
count-preserving symmetries. The Lean comparison domain includes every
compatible pattern directly. No normalization theorem is needed to admit
the counterexample, which already satisfies the convention.

Section 7 item 4 introduces the maximum count as a function of $(K,m,j)$.
Conjecture 7.1 states:

> For overlap $m\le K/2$, the maximum is obtained when prefix and suffix
> are interleaved and minimal, that is, for patterns with prefix
> $135\ldots(2m-1)$ and suffix $246\ldots(2m)$.

This asserts attainment by a member of the prescribed family. It does not
assert uniqueness or fix the order of the remaining middle values.
The equality case $K=2m$ has an empty middle.

The repository calculation gives
$C(13472568,4,2)=9>8=C(13572468,4,2)$. At this equality boundary,
the prefix and suffix determine every prescribed pattern, so the comparison
refutes the entire maximum-attainment assertion. The exact counts and
source-permutation correspondence are the repository result; the general
packing definitions and the packing/linear-extension interpretation
(Lemma 5.1 and Theorem 5.3) are the source authors' results.

The finite mechanism is two independent three-way choices for the
competitor, compared with three independent binary choices for the
prescribed pattern. The actual maximum, the strict-overlap range
$2m<K$, and Section 7 item 8's separate cutoff question are not settled.

The bounded prior check covered the primary version, selected symmetry
and enumeration results, the FPSAC precursor, Elizalde
arXiv:1203.1636v1 (overlap-one results), and Iriarte
arXiv:1405.4880v2 (orientations of a fixed graph). None supplied a located
whole answer in that checked scope. The graph-orientation theorem does
not directly compare these changing pattern posets. Ineffective general
web queries establish no absence. Worldwide priority, exhaustive
literature absence, and provider memory are unverified; no such claim
is made. Ordinary counting ingredients receive no separate novelty claim.

## Locator

- DOI: `10.48550/arXiv.2610.29846`.
- https://arxiv.org/abs/2610.29846v1
- https://arxiv.org/html/2610.29846v1#S7.Thmtheorem1
- Definitions 2.1–2.2, 2.5–2.6; equation (2.1); Remark 2.7.
- Definition 3.3 and the important convention in Section 3.
- Lemma 5.1 and Theorem 5.3 for the original chain interpretation.

The retained primary HTML has SHA-256
`ccfe47a85e19f9deb414583e52f1e627c4291eb4aaef1d8af3da683132202b97`.
