---
bibkey: tenenbaum2013unconventional
authors: Gérald Tenenbaum
year: 2013
title: "Some of Erdős' Unconventional Problems in Number Theory, Thirty-four Years Later"
doi: 10.1007/978-3-642-39286-3_23
claim: "Erdős (1979), restated as open by Tenenbaum (2013): Perhaps ε₁(n,m) is unimodular for m > n+1, but I know nothing about this."
strata_touched:
  - D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
license: citation-only
triage: anchor
---

# Unimodality of the one-divisor interval density

Tenenbaum revisits Erdős's questions about the set of multiples of an interval.
He reproduces the 1979 suggestion and later states that the unimodality question
remained open to his knowledge.

## Verified locator

- DOI: https://doi.org/10.1007/978-3-642-39286-3_23
- Archived chapter PDF:
  https://web.archive.org/web/20220710081934id_/https://tenenb.perso.math.cnrs.fr/PPP/Erdos-100.pdf
- The sentence occurs on the chapter's printed page 18 (volume page 668), in
  the discussion of the set of multiples of an interval begun on printed page
  17. It reads verbatim:

  > To my knowledge, the question of unimodality of ε₁(y,z) as a function of z is still open.

- The original is P. Erdős, *Some unconventional problems in number theory*,
  Astérisque 61 (1979), printed page 78:
  https://users.renyi.hu/~p_erdos/1979-21.pdf

  > Perhaps ε₁(n,m) is unimodular for m > n+1, but I know nothing about this.

The chapter uses the interval convention `y < d <= z`, while the quoted 1979
sentence uses `n < d < m`. The Lean statement follows the original strict
upper endpoint and addresses only the unqualified printed suggestion.
