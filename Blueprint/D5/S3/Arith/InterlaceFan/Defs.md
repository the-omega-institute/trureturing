# Interlace fan definitions

## Abstract

Interlace functionals and rational faces of their fan.

For darga n, a real coordinate vector has entries indexed from one through floor(n/2). Certificate indices run from zero through floor(n/2). Rational points have rational coordinates. The order class for a divisor d consists of the indices j with n/gcd(n,j)=d.

**Definition 1.1 (Interlace functionals).**

Lean statement: `D5/S3/Arith/InterlaceFan/Defs.I`

*Formalization.* `D5/S3/Arith/InterlaceFan/Defs.I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mandel; S. Robins (2019). *Dragging the roots of a polynomial to the unit circle*. URL: <https://arxiv.org/abs/1908.03208>.

*Commentary.*

The j-th interlace functional is minus the sum of the sigma coordinates multiplied by cos(2 pi j k/n), with coordinate k ranging from one through floor(n/2). This is equation (12) in section 5.2 of the cited article.

**Definition 1.2 (The interlace number).**

Lean statement: `D5/S3/Arith/InterlaceFan/Defs.interlaceNumber`

*Formalization.* `D5/S3/Arith/InterlaceFan/Defs.interlaceNumber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mandel; S. Robins (2019). *Dragging the roots of a polynomial to the unit circle*. URL: <https://arxiv.org/abs/1908.03208>.

*Commentary.*

The interlace number is the maximum of the functionals over indices zero through floor(n/2), as in the Interlace Formula, Theorem 4.2 of the cited article.

**Definition 1.3 (Closed certificate faces).**

Lean statement: `D5/S3/Arith/InterlaceFan/Defs.face`

*Formalization.* `D5/S3/Arith/InterlaceFan/Defs.face` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mandel; S. Robins (2019). *Dragging the roots of a polynomial to the unit circle*. URL: <https://arxiv.org/abs/1908.03208>.

*Commentary.*

The closed face associated with S consists of all vectors for which every index in S attains the maximum. This is the face convention of section 5.2, Proposition 5.5 and equation (15), in the cited article.

**Definition 1.4 (The rational-face classification proposition).**

Lean statement: `D5/S3/Arith/InterlaceFan/Defs.claim`

*Formalization.* `D5/S3/Arith/InterlaceFan/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mandel; S. Robins (2019). *Dragging the roots of a polynomial to the unit circle*. URL: <https://arxiv.org/abs/1908.03208>.

*Commentary.*

For darga at least two, a nonempty certificate set admits a nonzero rational point precisely when it misses an order class; the maximal such certificate sets are the complements of individual order classes. At a nonzero rational point of the corresponding face, every omitted index has strictly smaller functional value and the interlace number is rational. This is the classification proposition answering section 10, Problem 3 of the cited article.

## References

- Truth anchor: `D5/S3/Arith/InterlaceFan/Defs.I`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Defs.claim`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Defs.face`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Defs.interlaceNumber`
