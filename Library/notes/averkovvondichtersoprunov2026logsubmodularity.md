---
bibkey: averkovvondichtersoprunov2026logsubmodularity
authors: Gennadiy Averkov; Katherina von Dichter; Ivan Soprunov
year: 2026
title: "On the Log-submodularity for zonoids: from Mixed Volume inequalities to the Hypercube"
doi: null
url: https://arxiv.org/html/2608.14909v1#S4.E16
claim: "Equation (16) is the Hypercube Inequality for nonnegative weights on the vertices of the d-dimensional cube; Section 7.5 states that it remains open for d >= 4."
strata_touched:
  - D5/S0/FiniteGeometry/HypercubeInequality
license: CC BY 4.0
triage: anchor
---

# The Hypercube Inequality

Averkov, von Dichter and Soprunov reduce their proposed
log-submodularity inequality for zonoids to the Hypercube Inequality.
Section 4.4, Equation (16), states that for nonnegative weights indexed by
the vertices of the d-dimensional cube,

> (sum over (d+1)-vertex subsets S of Vol(S) times the product of the
> weights on S) times (the sum of all weights)^(d-1) is at most the
> product, over all cube facets F, of the sum of the weights on F.

Here Vol(S) is normalized simplex volume. With the columns `(v,1)`, this
is the absolute value of the corresponding integer determinant. Each
unordered subset occurs once and there is no factorial factor. Pairing
the two facets perpendicular to each coordinate gives exactly the two
facet sums in the formal result.

The paper proves the inequality for `d=3`, with lower dimensions included
in its discussion. Section 7.5 explicitly says that for `d>=4` the
Hypercube Inequality remains open. The repository theorem addresses the
determinant-defined Equation (16) uniformly for every `d>=1`; it does not
formalize the paper's geometric reduction or assert a theorem about
zonoid volume.

## Verified locator

- Primary version: https://arxiv.org/html/2608.14909v1
- Exact cited URL: https://arxiv.org/html/2608.14909v1#S4.E16
- arXiv identifier and submission date: 2608.14909v1, 14 August 2026.
- Manuscript date printed in the source: August 24, 2026.
- Exact target: Section 4.4, Equation (16), HTML anchor `S4.E16`.
- Open-status statement: Section 7.5, "Limitations for higher dimensions".
- Source file read locally with SHA-256
  `b439f4eab795c6e2091720f5a2025616231035b9eaffa0c9d5158b8228fd8d4f`.

No DOI is displayed in the primary source. The source status and the
bounded literature checks attest eligibility; they do not establish a
worldwide novelty or priority claim.
