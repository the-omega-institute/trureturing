---
bibkey: cassels1959rankin
authors: J. W. S. Cassels
year: 1959
title: On a problem of Rankin about the Epstein zeta-function
doi: 10.1017/S2040618500033906
url: https://doi.org/10.1017/S2040618500033906
claim: For positive definite binary quadratic forms of determinant one, the Epstein zeta function is minimized by the hexagonal form for every s greater than one, with equality only for forms equivalent to it, answering Rankin's question.
strata_touched:
  - D5/S3/Fourier/EpsteinMellinMinimum
license: citation-only
triage: anchor
---

# On a problem of Rankin about the Epstein zeta-function

The article is J. W. S. Cassels, Proceedings of the Glasgow Mathematical
Association 4 (1959), 73–80, available through the
[DOI](https://doi.org/10.1017/S2040618500033906). Its publisher abstract sets
$Z_h(s)=\sum{}'h(m,n)^{-s}$ for a positive definite binary form $h$ of
determinant one, with convergence for $s>1$, and recalls Rankin's statement
$Z_h(s)\ge Z_Q(s)$ for $s\ge1.035$, equality only when $h$ is equivalent to
the hexagonal form $Q$.

Diananda's later note, Proceedings of the Glasgow Mathematical Association 6
(1964), 202–204 ([DOI](https://doi.org/10.1017/S2040618500035036)), records
in its publisher abstract that Cassels answered Rankin's question for all
$s>1$ in the affirmative and proved further that the theorem holds for all
$s>0$; the 1964 notes of Ennola and Diananda concern lemmas used in this
argument. Montgomery's 1988 abstract attributes the full statement to
Rankin, Cassels, Ennola and Diananda between them.

The Lean statement uses the same normalization: $Q_{x,y}$ has determinant
one, the sum runs over nonzero integer pairs (the zero pair contributes
zero for $s>1$ in the Lean definition), and equality is characterized by
the lattice being an orthogonal image of the hexagonal lattice.

## Verified locator

- URL: https://doi.org/10.1017/S2040618500033906
- DOI: 10.1017/S2040618500033906
