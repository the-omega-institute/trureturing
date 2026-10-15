---
bibkey: zhang2025stochastic
authors: Shangtong Zhang
year: 2025
title: Stochastic matrices and geometric mixing in rl-theory-in-lean
doi: null
url: https://github.com/ShangtongZhang/rl-theory-in-lean/blob/fec0b5d1a03e90479945286532f89e4f22cfcd1e/RLTheory/Data/Matrix/Stochastic.lean
claim: Finite irreducible aperiodic real stochastic matrices admit a unique stationary probability row and geometric convergence in l1.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing
license: MIT
triage: anchor
---

## Verified locator

https://github.com/ShangtongZhang/rl-theory-in-lean/blob/fec0b5d1a03e90479945286532f89e4f22cfcd1e/RLTheory/Data/Matrix/Stochastic.lean

## Scope

The retained port preserves the source minorization, contraction, stationary uniqueness and geometric estimate. The repository's generic Cesaro cluster supplies stationary existence. Pinned Mathlib supplies eventual membership in the additive closure of return lengths with gcd one. The primitive bridge proves the actual positive-return predicate from a positive matrix power and row stochasticity. This supports primitive block convergence; it does not supply the closed-class or cyclic decomposition of an arbitrary reducible chain.

The upstream MIT license and retained-source notice are in docs/reports/stochastic-mixing-suppliers/.
