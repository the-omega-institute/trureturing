# Alternating Factorial Sum

## Abstract

The alternating factorial convolution for every pair of natural parameters.

The source is restored byte-for-byte from the archived matching-SOS report. It supplies equation (5) for the monomial-fiber route; no matching-polynomial coefficient formula follows without the separate combinatorial fiber proof.

**Theorem 1.1 (Opposite Series Product).**

Lean statement: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every commutative ring, the two opposite negative-binomial series multiply to the series obtained by substituting the squared variable.

**Theorem 1.2 (Alternating Choose Convolution).**

Lean statement: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_choose_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_choose_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient extraction gives the alternating binomial convolution for arbitrary natural d and h over the rationals.

**Theorem 1.3 (Alternating Factorial Identity).**

Lean statement: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_factorial_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_factorial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum over ell from zero to 2h of (-1)^ell choose(2h,ell) (d+ell)! (d+2h-ell)! equals (2h)! d! (d+h)! / h!. Both natural parameters remain universally quantified.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_choose_convolution`
- Truth anchor: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.alternating_factorial_sum`
- Truth anchor: `D5/S3/Zeros/Convolution/AlternatingFactorialSum.opposite_inv_series_mul`
