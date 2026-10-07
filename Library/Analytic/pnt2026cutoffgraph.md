---
bibkey: pnt2026cutoffgraph
authors: PrimeNumberTheoremAnd contributors; Anthropic PBC
year: 2026
title: Scaled cutoff and derivative approximation argument
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/43cdec3b5cfa62c75aac586f4edc2066e2cac4ca/D5/S3/Weil/ZetaPntBase/Sobolev.lean
claim: Compact scaled cutoffs approximate a function and its second derivative in the source W21 norm.
strata_touched:
  - D5/S3/Quantum/Analysis/SchwartzCutoffGraph
license: Apache-2.0
triage: anchor
---

# Scaled cutoff method

## Verified locator

https://github.com/the-omega-institute/trureturing/blob/43cdec3b5cfa62c75aac586f4edc2066e2cac4ca/D5/S3/Weil/ZetaPntBase/Sobolev.lean

The original theorem is `W21_approximation`. Its norm is one-dimensional
and uses L1 integrals. The receiving theorem derives simultaneous convergence
in actual complex Lebesgue L2 on every finite-dimensional Euclidean space,
for the sum of coordinate second derivatives and quadratic potentials.
It preserves the scaled-cutoff, second-product-rule and dominated-convergence
method; the receiving argument squares the norm and treats all coordinates.

The source chain is anthropics/zeta-23-lean at
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, from
AlexKontorovich/PrimeNumberTheoremAnd at
`6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`,
`PrimeNumberTheoremAnd/Sobolev.lean`.
Full grants and the applicable NOTICE are in
`docs/reports/oscillator-suppliers/sobolev-zeta-LICENSE.txt`,
`docs/reports/oscillator-suppliers/sobolev-pnt-LICENSE.txt`, and
`docs/reports/oscillator-suppliers/sobolev-zeta-NOTICE.txt`.
No originality is claimed for the attributed cutoff method.
