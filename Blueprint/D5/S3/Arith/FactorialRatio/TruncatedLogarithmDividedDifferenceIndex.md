# Divided-difference LCM indices

## Abstract

Counting the prefix least common multiple factors gives an exact positive integer for the factor-four prime tent.

**Definition 1.1 (Product of prefix least common multiples).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.differenceIndex`

*Formalization.* `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.differenceIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and r, I(n,r) is the product of lcmUpto(floor(d/r)) over 0 <= d < n. Division uses Lean's natural division, which is zero when r=0. The product is one when n=0.

**Theorem 1.2 (Exact logarithm of the index).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_differenceIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_differenceIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n and positive natural r, log(I(n,r)) is the sum over 0 <= q < n of max(n-rq,0) times the von Mangoldt value at q. The logarithm of each prefix LCM is a Chebyshev psi sum. Exchanging the two finite sums counts the d with rq <= d < n.

**Theorem 1.3 (Exact prime valuation of the index).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_differenceIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_differenceIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n, positive natural r and prime p, the p-valuation of I(n,r) is the sum over 0 <= a < n of max(n-r*p^(a+1),0). The valuation of a prefix LCM counts the powers p^(a+1) up to its cutoff. For each such power the number of eligible d is the length of the interval from r*p^(a+1) up to, but excluding, n.

**Definition 1.4 (Factor-four tent weight).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.tentWeight`

*Formalization.* `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.tentWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural x and q, the weight is zero for q <= x, is 2*(q-x) for x < q <= 2*x, and is max(4*x-q,0) for q > 2*x.

**Definition 1.5 (Relative divided-difference index).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex`

*Formalization.* `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each natural x, the relative index is the natural quotient of I(4*x,1)^2 * I(4*x,4) by I(4*x,2)^3.

**Theorem 1.6 (Positive exact quotient).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural x the denominator I(4*x,2)^3 divides the numerator I(4*x,1)^2 * I(4*x,4). Multiplying the relative index by the denominator gives the numerator, and the relative index is strictly positive. At every prime power, the numerator's exponent contribution exceeds or equals the denominator's contribution by twice the tent weight.

**Theorem 1.7 (Prime-power tent valuation).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_relativeIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_relativeIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural x and every prime p, the p-valuation of the relative index is the sum over 0 <= a < 4*x of twice the tent weight at p^(a+1). Each term of the numerator valuation is the corresponding denominator term plus twice this weight, so the denominator cancels.

**Theorem 1.8 (Exact tent logarithm).**

Lean statement: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_relativeIndex`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_relativeIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural x, the logarithm of the relative index is twice the sum over 0 <= q < 4*x of the tent weight at q times the von Mangoldt value at q. The three index logarithms have the same finite cutoff. Applying the tent identity to each summand and cancelling the denominator logarithm gives the formula. The formulas include all primes and their powers, with empty sums and relative index one at x=0.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.differenceIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_differenceIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.factorization_relativeIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_differenceIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.log_relativeIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.relativeIndex_spec`
- Truth anchor: `D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex.tentWeight`
