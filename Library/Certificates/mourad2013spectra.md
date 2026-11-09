---
bibkey: mourad2013spectra
authors: Bassam Mourad; Hassan Abbas
year: 2013
title: On the symmetric doubly stochastic matrices that are determined by their spectra
doi: 10.48550/arXiv.1310.1273
url: https://arxiv.org/abs/1310.1273v1
claim: Conjecture 5.1 places every spectrally determined symmetric doubly stochastic matrix of positive trace on specified closed segments of the full symmetric polytope.
strata_touched:
  - D5/S0/Certificates/MouradAbbasC51Refutation
license: citation-only
triage: anchor
---

# Symmetric doubly stochastic matrices determined by their spectra

## Verified locator

DOI: 10.48550/arXiv.1310.1273

Source: https://arxiv.org/abs/1310.1273v1

The source is arXiv v1. Printed pages 1–2 define the objects; printed page 10
states Conjecture 5.1. The journal article has the expanded title *On the
symmetric doubly stochastic matrices that are determined by their spectra and
their connection with spectral graph theory*, DOI 10.1080/03081087.2014.903590.
That version has not been read.

## Source statements

Printed page 1:

> An $n\times n$ real matrix $A$ having each row and column sum equal to 1 is called doubly quasi-stochastic. If, in addition, $A$ is nonnegative then $A$ is said to be doubly stochastic. The set of all $n\times n$ doubly-stochastic matrices is denoted by $\Delta_n$ and the set of all the symmetric elements in $\Delta_n$ will be denoted by $\Delta^s_n.$ For $0\leq a\leq n,$ denote by $\Delta^s_n(a)$ to be the set of all elements of $\Delta^s_n$ with trace $a.$

> The third is $C_n$ which denotes the $n\times n$ matrix whose diagonal entries are all zeroes and whose off-diagonal entries are equal to $\frac{1}{n-1}$ (here for $n\geq 2$).

Printed page 2:

> Two matrices $A$ and $B$ are said to be permutationally similar if $B=P^TAP$ for some permutation matrix $P.$

> If in addition $A$ is symmetric then $A$ is said to be DS in $\Delta_n^s$ if $B\in\Delta_n^s$ is similar to $A$ implies that $B$ is permutationally similar to $A.$

Printed page 10, Conjecture 5.1:

> For $0< a \leq n,$ the only elements of $\Delta_n^s(a)$ that are DS in $\Delta_n^s$ are points on the line segments $[I_n,C_n],$ $[I_n,P]$ and $[C_n,P]$ where $P$ is a vertex of $\Delta_n^s.$

## Mathematical reading

The carrier is `Matrix (Fin n) (Fin n) ℝ`. Mathlib's `doublyStochastic`
supplies entrywise nonnegativity and row and column sums equal to one.
`Matrix.IsSymm` expresses symmetry, and `Matrix.trace` defines the trace slice.
Permutation similarity is the displayed equation with an `Equiv.Perm (Fin n)`.
`IsConj` expresses ordinary real matrix similarity by a unit, with no
orthogonality restriction. Vertices are extreme points of the full symmetric
polytope, and `segment ℝ` includes both endpoints. The order range is `2 ≤ n`,
as required for the source's `C_n`. The word “only” asserts a necessary
condition; no converse or irreducibility assumption is included.

The family used to refute this condition has `r` equal blocks of size `k`,
`k ≥ 4`, `r ≥ 2`, diagonal `t`, and within-block off-diagonal
`(1-t)/(k-1)`, with `0 < t < 1/k²`. The concrete choice is `k=4`, `r=2`,
`t=1/40`, giving trace `1/5`. The source's order-three classification and its
two final-section questions remain outside this refutation.

## Literature status

The bounded screen in issue #21726 found no settlement in the material it
queried and read. It includes the source, nine related arXiv texts and Flor's
classical classification of nonnegative idempotents. Some citation APIs were
rate limited, only the first page of two broad full-text searches was read,
and the journal version and three other publisher texts were inaccessible.
Completeness and settlement priority are `ASSUMED-UNVERIFIED`.

## Exact experiment

Repository: https://github.com/the-omega-institute/trureturing-experiments

Commit: `10e7685b6ec8d6cb777ff4900b831634de180820`.

Command: `python3 docs/reports/mourad-abbas-c51/check.py`.

Program SHA256: `63271ba871f6df28a09775beea24e0527fde677a5025e6c8041fa234bd3a828a`.
The command exits 0 with final line `ALL_CHECKS_OK`. This exact computation
is distinct from kernel verification. Its boundary examples
at `t=1/k²` for `k=4,5,6` and its characteristic polynomial
`(x-1)²(x+3/10)⁶` for the order-eight matrix are finite computed results.
