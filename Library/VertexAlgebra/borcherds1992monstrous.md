---
bibkey: borcherds1992monstrous
authors: Richard E. Borcherds
year: 1992
title: Monstrous moonshine and monstrous Lie superalgebras
doi: 10.1007/BF01232032
claim: Monster Lie algebra, twisted denominator formulas, and replication relations for McKay-Thompson series.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/borcherds1992monstrous -->

# Monstrous moonshine and denominators

Borcherds constructs a Monster-equivariant rank-two generalized Kac-Moody
algebra and uses twisted denominator formulas to establish the replication
relations and genus-zero properties of the Monster Thompson series.
Equation (7.1) is the untwined product. Equations (8.2)-(8.3) give the
equivariant exterior-power identity and its Adams-operation trace expansion;
the $n=-1$ contribution supplies the Weyl factor. Formal logarithms and
trace/determinant expansions are prior mathematics. The cited equations do
not by themselves verify an equality in this repository's Lean carrier, nor
do they classify the partial-observation power-closure criterion.

The existing `MonsterPrimitiveMobiusRecovery.lean` theorem
`monster_primitive_mobius_recovery` explicitly takes
`logExpansion : negativeFormalLog D = logarithmicHistory (primitiveHeatSeries c)`
as a hypothesis. It proves recovery conditional on that equality; it does
not establish the actual Monster root-space determinant interface or its
identification with the denominator. The determinant/log trace calculation
in [appendix 2143](../../docs/develop/theory/OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md)
is an attributed intermediate use of Section 8, not a new standalone result.

## Verified locator

- Published article: https://doi.org/10.1007/BF01232032
- Author's paper, introduction and equations (7.1), (8.2), (8.3):
  https://math.berkeley.edu/~reb/papers/monster/monster.tex
