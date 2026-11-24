---
slug: su-hu-2026-minimum-rectangular-size
bibkey: suhu2026fullnegative
doi: null
url: https://arxiv.org/abs/2609.23313v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Probability/FiniteNegativeRegression.na_of_fullNRD_of_marginalProduct_lt_81
  - D5/S3/Analytic/Probability/SuHuTable41.table_attainment
---

# The minimum rectangular size for full negative regression without negative association

## Problem

Yuting Su and Taizhong Hu ask in Remark 4.7 whether “81 is the minimal total rectangular size for counterexamples with an arbitrary number of coordinates.” Among strictly positive probability laws on products of an arbitrary finite family of nonempty finite chains, the least product of the chain sizes for a full negatively regression dependent law failing negative association is **81**. The same minimum holds for the product of actual marginal support sizes when joint masses may vanish. [Remark 4.7, arXiv:2609.23313v1, p. 12](https://arxiv.org/pdf/2609.23313v1#page=12)

| Source clause | Lean counterpart |
| --- | --- |
| Arbitrary finite coordinate set and finite chains | A probability mass function on the dependent product of finite linearly ordered types indexed by a finite type. The PMF supplies a point in the product and hence in every factor. |
| Full negative regression dependence | `FullNRD` quantifies over all disjoint response and conditioning blocks, all increasing real response tests, and all coordinatewise comparable conditioning endpoints of strictly positive fiber mass. The comparison still applies if some intermediate fiber has zero mass. |
| Failure of negative association | `¬ NA p`, where `NA` requires nonpositive covariance for every pair of increasing real tests on disjoint blocks. Covariance is the expectation of the product minus the product of expectations. |
| Rectangular size | `marginalProduct` multiplies the cardinalities of the supports of the one-coordinate pushforward PMFs. For a strictly positive law the supports are the entire factors. |
| Least possible size 81 | The lower-bound theorem forces `NA` below 81. The attainment theorem supplies the published law with 81, strict positivity, full negative regression and failure of negative association. |

## Motivation

Coordinatewise minimality at four coordinates does not determine the least product across all numbers of coordinates. The least product gives a uniform cutoff for when full negative regression suffices for negative association. [Preregistration #33741](https://github.com/the-omega-institute/trureturing/issues/33741)

## Gap

Propositions 4.4 and 4.6 cover the low-dimensional and strictly positive four-coordinate cases. Table 4.1 and Propositions 4.1–4.2 supply attainment in four ternary coordinates. The remaining lower bound concerns arbitrary finite products, including products with more than four active coordinates. The preregistration's searches of arXiv, Crossref, indexed citations and the pinned Lean libraries found no proof of this lower bound in their searched scope. [Su–Hu, §§4.1–4.3](https://arxiv.org/pdf/2609.23313v1#page=8) · [Search scope](https://github.com/the-omega-institute/trureturing/issues/33741)

## Route

1. Push the law to the actual marginal supports and transfer both properties along the coordinate maps. For two disjoint test blocks, their size product is below 81, so one block has size at most eight. Removing singleton coordinates leaves a constant block, a chain, a binary factor times a chain, or the three-bit cube.
2. Use the finite tower identity to transport comparisons of positive conditional fiber means to each subblock of the smaller block. The chain proof gives the upper-tail sign. The binary-by-chain proof combines the upper row and marginal tails with the sign of a lower-row interval. On the cube, upper coordinate faces and the opposite-sign obstruction give the signs of upper events contained in or containing an upper face. For the remaining majority event the proof exchanges a singleton and a doubleton in an upper face. Finite upper-level decomposition gives the covariance sign for real monotone tests.
3. On the published rectangle use the Table 4.1 entries in lexicographic row and column order and divide by 99,999. Compare integer weights of upper events by cross multiplication. Upper events on any disjoint response block pull back to upper events on the full complementary block. Finite Strassen couples the response marginal at the larger positive conditioning endpoint to the response marginal at the smaller one. The ordered pairs and the two coupling marginals give the full negative regression inequality for every increasing real test. The disjoint events that both coordinates of their respective pairs are at least one have weights 39,649 each and intersection weight 15,732. Their indicator covariance is $1141067/9999800001>0$. Positivity of every cell gives four marginal supports of size three.

## Falsifier

A full-NRD law on finite chains with actual marginal-support product at most 80 and a strictly positive covariance between increasing real tests on disjoint blocks would falsify the lower bound. A discrepancy in the published table, a failed positive-endpoint comparison, or a nonpositive covariance for the two displayed indicators would invalidate the claimed attainment.

## Evidence

- Lower bound and upper-event lifting are given by `D5/S3/Analytic/Probability/FiniteNegativeRegression.na_of_fullNRD_of_marginalProduct_lt_81` and `D5/S3/Analytic/Probability/FiniteNegativeRegression.fullNRD_of_upper`. [Lean source](../D5/S3/Analytic/Probability/FiniteNegativeRegression.lean)
- The cube branch uses `D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans.centered_sum_nonpos_of_antitone_fiber_means`. [Lean source](../D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans.lean)
- The published witness is certified by `D5/S3/Analytic/Probability/SuHuTable41.table_attainment` and `D5/S3/Analytic/Probability/SuHuTable41.table_positive_covariance`. Su and Hu supply the table, the two events, and the published witness argument. [Lean source](../D5/S3/Analytic/Probability/SuHuTable41.lean) · [Library note](../Library/Estimation/suhu2026fullnegative.md)

## Triage

### What the settlement shows

- **Proved.** `FiniteNegativeRegression.na_of_fullNRD_of_marginalProduct_lt_81` gives the uniform cutoff from a block of size at most eight and applies to zero-mass joint cells and conditioning comparisons across zero-mass fibers.
- **Proved.** `SuHuTable41.table_attainment` makes the cutoff sharp using the authors’ strictly positive law. Together the two theorems answer the first residual in Remark 4.7 for any finite number of coordinates and give the exact minimum with the actual marginal-support convention.
- **Open here.** The minimum number of positive joint atoms for counterexamples with zero masses is the separate residual in Remark 4.7. [Remark 4.7](https://arxiv.org/pdf/2609.23313v1#page=12)

## ASSUMED-UNVERIFIED

Publication priority beyond the bounded literature search in the preregistration is unverified. [Search scope](https://github.com/the-omega-institute/trureturing/issues/33741)
