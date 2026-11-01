---
bibkey: mishraraundal2021weaving
authors: Rama Mishra; Hitesh Raundal
year: 2021
title: Hecke algebra trace algorithm and some conjectures on weaving knots
doi: null
url: https://arxiv.org/abs/1908.04152v3
claim: "Conjecture 5.2 asks for the fixed-width large-m twist-number asymptotic for W(n+1,m); the present formalization begins with a generic signed rank-state coefficient estimate used by the eventual graph/Jones bridge."
strata_touched:
  - D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
license: citation-only
triage: anchor
---

# Weaving-knot twist-number conjecture

The primary source is arXiv:1908.04152v3. Definition 5.1 (printed p. 21)
defines the higher twist numbers from the Jones coefficients, and Conjecture 5.2
(printed p. 23) states the fixed-width large- $m$ asymptotic involving

$$
d=n\bmod 2,\qquad r=(n-d)/2,
$$

with links included and no coprimality condition on $m$. The literal $n=1$
boundary is not silently included in the formalization target; the full
geometric/Jones route must preserve the source's width and link conventions.

The first formal layer in
`D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate` defines the actual
finite signed rank-state polynomial, proves its exact coefficient extraction and
forest/cyclic split, and consumes those results in a uniform cyclic-error
estimate. It is a generic graph-polynomial layer, not a Jones identification.
The bounded-degeneracy cyclic embedding count, the explicit weaving state-graph
incidences, the signed Jones--Tutte convention, and the all-width asymptotic
remain separate proof obligations.

The inspected source audit also records later width-three coefficient results and
a 2026 JIMS paper whose full body was unavailable in the public access route.
Consequently this note records the source and formalization boundary only; it
makes no priority, uniqueness, or open-problem claim.

## Verified locator

- Primary source: https://arxiv.org/abs/1908.04152v3
- TeX/PDF locator: Definition 5.1, equation (5.5), and Conjecture 5.2.
- Related Jones--Tutte source used for the eventual classical bridge: Dasbach and
  Lin, *A volumish theorem for the Jones polynomial of alternating knots*,
  Pacific Journal of Mathematics 231 (2007), 279–291.
