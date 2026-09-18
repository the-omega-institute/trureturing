---
bibkey: erdossarkozysos1994additive
authors: Paul Erdős; András Sárközy; Vera T. Sós
year: 1994
title: On additive properties of general sequences
doi: 10.1016/0012-365X(94)00108-U
url: https://doi.org/10.1016/0012-365X(94)00108-U
claim: The paper asks for the least possible size of a maximal Sidon set in the integers from one to N; the saturation lower bound of order N to the one third is recorded as elementary.
strata_touched:
  - D5/S3/Arith/Additive/MaximalSidon
license: citation-only
triage: anchor
---

# Maximal Sidon sets in an initial interval

## Verified locator

Discrete Mathematics 136 (1994), 75-99, DOI 10.1016/0012-365X(94)00108-U.

The question of how small a maximal Sidon set inside the integers from one to N
can be is due to Erdős, Sárközy and Sós. It is catalogued as Erdős Problem 156
at https://www.erdosproblems.com/156, which asks whether a maximal Sidon set of
size O(N^(1/3)) exists and records that the greedy construction of a maximal
Sidon set has size at least of order N^(1/3). Ruzsa, Acta Arithmetica 85 (1998),
constructed a maximal Sidon set of size at most of order (N log N)^(1/3).

## Proof scope

The Lean module states the saturation direction with an explicit polynomial:
for a Sidon set A that is maximal in the integers from one to N, the inequality
N <= A.card^3 + A.card^2 + A.card holds. The argument classifies every failed
insertion into a three-parameter sum witness or a two-parameter midpoint
witness, covers the interval by A together with the two witness images, and
applies the cardinality bounds for images and unions. Mathlib supplies the
interval cardinality and the image and union inequalities.

The exponent in the displayed inequality is the elementary one recorded on the
problem page; the polynomial form, with its explicit lower-order terms, is the
repository's own statement of it. The module does not exhibit a maximal Sidon
set of order N^(1/3), so the existence question stated above stays open, and no
bound in the opposite direction is claimed.
