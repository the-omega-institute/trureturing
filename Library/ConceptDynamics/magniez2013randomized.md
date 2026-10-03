---
bibkey: magniez2013randomized
authors: Frederic Magniez, Ashwin Nayak, Miklos Santha, Jonah Sherman, Gabor Tardos, and David Xiao
year: 2013
title: Improved bounds for the randomized decision tree complexity of recursive majority
doi: null
url: https://arxiv.org/abs/1309.7565v1
claim: Page 2 defines randomized query cost at a fixed input as the expected number of queries, and complexity as the worst input cost.
strata_touched:
  - D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/magniez2013randomized -->

# Expected query cost at a fixed input

On page 2, a randomized decision tree is a distribution over deterministic
query trees on finite Boolean words. Its cost at an input is the expected
number of queried input bits. The optimization then takes the worst input
cost and minimizes over admissible algorithms.

This convention supplies the order of expectation and worst-input
optimization for exact real probes. The paper's finite-word domain does
not supply a contract on an uncountable real source domain. In particular,
pointwise almost sure correctness and correctness at every declared seed
are separate contracts for exact real probes. The certificate cost two and
the deterministic, weak random, and strong random sharp costs three, one,
and two are repository deductions for that probe interface.
