---
bibkey: wunderlich2026finitejensen
authors: Henning Wunderlich
year: 2026
title: Finite-radius Jensen and relative-entropy formulations of the Balazard--Saias--Yor criterion
doi: null
url: https://arxiv.org/abs/2610.10584v1
claim: The preprint gives finite-radius Jensen and relative-entropy reformulations of an established Balazard--Saias--Yor criterion; the new finite bookkeeping does not prove RH or supply a Robin estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite-radius Jensen and entropy reformulations

The inspected source is [arXiv:2610.10584v1](https://arxiv.org/abs/2610.10584v1),
submitted 6 October 2026. The paper explicitly presents the underlying
Jensen--Hardy boundary identity as known. This card records the finite-radius
and information-theoretic reformulations, not an independent proof audit or a
new RH criterion.

## Finite-radius defect

After mapping the left half-plane to the disk, the source separates the
contribution of the trivial zeros from the circular Jensen mean. For its
normalization, the mapped trivial-zero product telescopes. The remaining
finite-radius defect is an integral of the number of mapped nontrivial zeros
outside the critical line. The defect is nonnegative and vanishes exactly
when RH holds. A parameterized version replaces the telescoping product by a
gamma quotient.

The construction is a finite-radius presentation of the established
Balazard--Saias--Yor/Jensen--Hardy mechanism. It does not turn finite-radius
vanishing into an unconditional estimate at all radii.

## Relative entropy form

Combining two boundary identities gives an absolutely convergent logarithmic
integral involving the completed $\Xi$-function. With

$$
 Z=\left|\frac{\Xi(T)}{\Xi(0)}\right|^2,
$$

the source compares the law of $Z$ with its size-biased law. The
data-processing step is lossless for this statistic, and RH is equivalent to
saturation of the resulting explicit upper bound for relative entropy. The
gap is a positive sum over off-line zeros. The variational and moment forms
are reformulations of the same identity; an independent lower bound reaching
the saturation value is left open.

## Relation to the FIB geometry

The FIB boundary--bulk language can use this source as a precise example of a
positive defect split: the finite boundary contribution is explicit, while
the hidden off-line contribution is nonnegative. A FIB five-state or four-phase
encoding has not been identified with the Jensen zero count, the $\Xi$ law,
or the relative-entropy statistic. Such an identification would require an
actual transport theorem and would still need a uniform bound that closes the
Robin signed residual.
