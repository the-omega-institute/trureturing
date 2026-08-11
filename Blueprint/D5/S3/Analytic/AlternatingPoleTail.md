# Alternating Pole Tails

## Abstract

A pole at minus one has an exact alternating binomial coefficient tail.

**Theorem 1.1 (A pole at minus one generates an alternating binomial tail).**

$$\operatorname{coeff}(n, \operatorname{rescale}(-1, (1-X)^{-(k+1)}))=(-1)^n \operatorname{choose}(k+n,k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlternatingPoleTail.alternating_pole_tail_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative k and n, rescaling the inverse power series of one minus X by minus one gives coefficient n equal to minus one to the n times choose k plus n over k. Thus a pole of order k plus one at minus one has an exact alternating tail whose magnitudes are polynomial in n.

The proof is a thin honest wrapper over pinned Mathlib's negative-binomial power series and coefficient-rescaling declarations. Mathlib has no named theorem for the source atom's full row-family specialization. This declaration proves the exact algebraic pole-tail mechanism; it does not assert that every row function in the source atom has already been identified with this model.

## References

- Truth anchor: `D5/S3/Analytic/AlternatingPoleTail.alternating_pole_tail_coeff`
