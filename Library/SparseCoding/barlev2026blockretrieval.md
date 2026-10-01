---
bibkey: barlev2026blockretrieval
authors: Daniella Bar-Lev
year: 2026
title: "Coded Information Retrieval for Block-Structured DNA-Based Data Storage"
doi: 10.48550/arXiv.2603.17154
url: https://arxiv.org/html/2603.17154v2
claim: "Conjecture 1 asserts the universal hyperbolic tradeoff s1/E1+s2/E2<=1; Conjecture 2 asserts weak Pareto improvement from length n to n+1. Both use actual minimum iid uniform whole-file retrieval and positive partitions with maximum size at least two."
strata_touched:
  - D5/S3/Resource/MinimumRetrievalTime
  - D5/S3/Resource/VandermondeHyperbolicRefutation
license: citation-only
triage: anchor
---

# Block-structured coded retrieval

## Verified locator

DOI: `10.48550/arXiv.2603.17154`.
URL: https://arxiv.org/html/2603.17154v2
Scope: arXiv v2, Section II-A, Section V-B Conjecture 1, and Section VII-A Conjecture 2.

## Source contract

The source is arXiv:2603.17154v2, Section II-A, Definitions 1 and 2,
equation (5), and Section VII-A, Conjecture 2. Its field is the finite field
`F_q`, with `q` a prime power. A generator has rank `k`, and its physical
column indices are sampled independently, uniformly, and with replacement.
Recovering a file means that the sampled-column span contains every
standard basis vector belonging to that file. The two files have positive
dimensions `s1+s2=k`.

For `n>=k` and `max(s1,s2)>=2`, Conjecture 2 asks for a rank-`k`
length-`n+1` generator whose two expected minimum retrieval times are each
at most those of any given length-`n` generator. The successor is arbitrary:
it need not append the old generator, be systematic, or be file-dedicated.
Repeated columns remain distinct sampling indices, and the stated rank
condition does not exclude zero columns. Exact equality of expected pairs
is not the target. Remark 10 excludes the partition `(1,1)`; it does not
exclude `(1,2)`.

## Formal interface

`MinimumRetrievalTime.claim` quantifies over finite field structures and
all positive two-file sizes, legal lengths, and full-rank matrices, encoded
by their indexed columns. `Matrix.rank_eq_finrank_span_cols` and
`Submodule.eq_top_of_finrank_eq` connect matrix rank with full column span.
The coordinate-file definitions use the standard coordinate basis and
the exact index cuts `<s1` and `>=s1`.

The expectation in the formal statement is the Bochner integral of the
minimum stopping time under the infinite product of uniform finite-index
measures. The probability bridge proves measurability, the exact tail
identity, finite expectation, integrability, and equality with the
nonnegative integral; no subset-count formula is taken as a definition or
axiom.

`VandermondeHyperbolicRefutation.claim` uses the same finite-field model,
coordinate files and actual stopping-time expectations for Conjecture 1.
Its scope is every full-rank generator, not just systematic or
file-dedicated generators. A source-faithful refutation therefore needs
one admitted code and its actual file expectations, rather than a
universal inequality for a restricted class.

## Literature boundary

The source v2 retains Conjecture 2. The nearby Vlachos--Bar-Lev preprint
arXiv:2609.36067v1 concerns hyperbolic bounds (Conjecture 1), not the
length-monotonicity assertion. Exact-id and title/topic searches found no
earlier Conjecture 2 resolution in the searched scope. This is bounded
negative evidence, not an exhaustive priority claim.
