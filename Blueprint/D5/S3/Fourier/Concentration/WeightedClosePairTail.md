# Weighted close pairs above a height cutoff

## Abstract

A count by the larger ordinate bounds the total reciprocal-product weight.

**Theorem 1.1 (A cumulative count bounds the weighted tail).**

$$A \leq 4 C \frac{log(X) + 1}{X}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/WeightedClosePairTail.weighted_close_pairs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite set of ordered pairs whose two ordinates lie in [X,T], where 2≤X≤T. Assume each pair has gap at most η and η≤X/2. Each index has nonnegative multiplicity m and nonnegative weight w bounded by m divided by its ordinate. Let B(y) be the sum of m(i)m(j) over the supplied pairs whose larger ordinate is at most y. Assume B(y)≤Cy log y for X≤y≤T with C≥0. Let A denote the sum of w(i)w(j) over the supplied pairs.

The larger ordinate h of a close pair is at least X. Its smaller ordinate is at least h/2, so the weight of that pair is at most 2m(i)m(j)/h². Express 1/h² as 1/T² plus the integral of 2/y³ from h to T. Interchanging the finite sum and the integral replaces the sum of indicators by B(y). Apply the cumulative bound at T and inside the integral. Integrating log y/y² gives the asserted bound.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/WeightedClosePairTail.weighted_close_pairs_le`
