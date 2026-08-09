# Image of Golden Coordinates

## Abstract

Doubled golden coordinates are exactly the Zsqrtd pairs with equal parity.

**Theorem 1.1 (Exact image criterion).**

$$\forall z\in\operatorname{Zsqrtd}(5),\ z\in\operatorname{range}(\operatorname{toZsqrtd}) \Leftrightarrow \exists k\in\mathbb{Z},\ z.re - z.im = 2 \times k$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/ZsqrtdImage.mem_range_toZsqrtd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic integer lies in the image precisely when the difference of its two integer coordinates is even. The forward direction reads the golden real coordinate from that half-difference; the reverse direction reconstructs the unique preimage from the half-difference and the square-root coordinate.

## References

- Truth anchor: `D5/S0/Carrier/ZsqrtdImage.mem_range_toZsqrtd_iff`
- Dependency: [D5/S0/Carrier/Ring](Ring.md)
