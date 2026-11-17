---
bibkey: nathanson2026latticesumsets
authors: Melvyn B. Nathanson
year: 2026
title: "A problem on sumset sizes of sets of lattice points"
doi: 10.48550/arXiv.2607.20571
url: https://arxiv.org/abs/2607.20571v1
claim: Problem 3 asks whether the least positive full-range lattice-cube diameter is at most the exact nth root of the corresponding interval diameter.
strata_touched:
  - D5/S3/Arith/Additive/NathansonLatticeRootRefutation
license: citation-only
triage: anchor
---

# Full-range lattice diameters

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2607.20571

Pinned version: https://arxiv.org/abs/2607.20571v1.
HTML: https://arxiv.org/html/2607.20571v1, final numbered Problem 3 before
the references. The source TeX is available at
https://arxiv.org/src/2607.20571v1 in
`Sumset_sizes_of_sets_of_lattice_points.tex`.

## Original question

The original TeX uses `\mcr` for `\mathcal R` and `\Z` for `\mathbf Z`.

```tex
Let $N(h,k)$ be the smallest positive integer such that
\[
\mcr_{\Z} (h,k)  = \left\{ \left| hA \right|: A \subseteq [0,N(h,k)] \text{ and }  |A| = k \right\}.
\]
and let $N_n(h,k)$ be the smallest positive integer such that
\[
\mcr_{\Z} (h,k)  = \left\{ \left| hA \right|: A \subseteq [0,N_n(h,k)]^n \text{ and }  |A| = k \right\}.
\]
Prove or disprove the following inequality:
\[
N_n(h,k)\leq N(h,k)^{1/n}.
\]
```

The paper defines the h-fold sumset to allow h not necessarily distinct
elements. Its range R_Z(h,k) uses every k-element integer set. The lattice
interpretation of the displayed cube is fixed by the surrounding theorem
equating the ordinary ranges for Z and Z^n and the integer-coordinate
construction. Endpoints are inclusive; the diameter is a positive integer;
the root is an exact real root. Restricted sums and real-point cubes are
different objects.

## Mathematical scope

For h=2 and k=3 the complete integer range is {5,6}. If a<b<c, the only
possible equality among the six unordered pair sums is a+c=2b.
The interval models {0,1,2} and {0,1,3} give both values at D=3, whereas
every three-point subset of [0,2] is {0,1,2} and misses 6. The least
positive interval diameter is therefore 3.

Every triple in the integer unit square has six distinct pair sums. A
midpoint equality in a binary coordinate forces both endpoints to equal
that midpoint. At D=2 the line {(0,0),(1,0),(2,0)} gives 5 and the triangle
{(0,0),(1,0),(0,1)} gives 6; all triples in that square have a cardinality
in the complete integer range. The least positive square diameter is 2.
Thus the exact bound would require 2<=sqrt(3).

The Lean minima are defined by Nat.find on explicit proofs that a positive
covering diameter exists. The universal proposition includes those
existence obligations, and the counterexample constructs both of them.
No default value or unproved global inhabitedness supplies a diameter.
The negative result concerns the universal inequality, not a claim about
all possible corrected bounds or other parameter values.
