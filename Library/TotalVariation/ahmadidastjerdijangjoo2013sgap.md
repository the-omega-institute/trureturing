---
bibkey: ahmadidastjerdijangjoo2013sgap
authors: Dawoud Ahmadi Dastjerdi and Somaye Jangjoo
year: 2013
title: Computations on Sofic S-gap Shifts
doi: 10.1007/s12346-013-0096-2
url: https://arxiv.org/abs/1108.3414
claim: The topological entropy of an S-gap shift is the base-two logarithm of the positive root of its entropy function.
strata_touched:
  - D5/S3/TotalVariation/ParryTopologicalEntropy
license: citation-only
triage: anchor
---

# Computations on Sofic S-gap Shifts

## Verified locator

- Journal article DOI — https://doi.org/10.1007/s12346-013-0096-2.
- Author preprint — https://arxiv.org/abs/1108.3414. See the abstract on page 1
  and §2.2 of [version 5](https://arxiv.org/pdf/1108.3414v5).

The entropy function is specified there. For an S-gap shift,
the root \(x\) satisfies \(\sum_{s\in S}x^{-(s+1)}=1\) and the entropy
is \(\log_2 x\).

Complementing bits identifies the bilateral forbidden-\(1^k\) shift
with the finite \(S\)-gap shift for \(S=\{0,\ldots,k-1\}\). The equation
then selects the order-\(k\) d-bonacci Perron root. Natural logarithms
express the resulting entropy in nats per step.

The Lean proof works on the native Boolean carrier. It bounds the count
of admissible prefixes and uses the forward-tail maps to transport the
one-sided cover entropy to the product uniformity on bilateral paths.
