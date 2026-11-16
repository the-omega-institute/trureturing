# Primitive Duplication over the Square-Root-Two Order

## Abstract

Local cancellation of primitive homogeneous duplication forms over Z[sqrt(2)].

**Theorem 1.1 (Two exceptional prime ideals and their cancellation bounds).**

$$\forall a, b: \operatorname{Zsqrtd}\left(2\right), \operatorname{IdealSpanPair}\left(a, b\right) = \operatorname{UnitIdeal}\left(\operatorname{Zsqrtd}\left(2\right)\right) \implies \neg (\operatorname{commonIdeal}\left(a, b\right) \le \operatorname{IdealSpan}\left(root\right)^{7}) \land\\{}\neg (\operatorname{commonIdeal}\left(a, b\right) \le \operatorname{IdealSpan}\left(delta\right)^{5}) \land\\{}\forall q: \operatorname{Ideal}\left(\operatorname{Zsqrtd}\left(2\right)\right), \operatorname{IsPrime}\left(q\right) \implies \operatorname{commonIdeal}\left(a, b\right) \le q \implies (q = \operatorname{IdealSpan}\left(root\right) \lor q = \operatorname{IdealSpan}\left(delta\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation.primitive_duplication_local` (`✓ std3`). ∎

*Citation.* Unattributed manuscript in the elliotglazer repository (2026). *Z is Diophantine in Q, Version 13*. URL: <https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex>.

*Commentary.*

Let O be the explicit quadratic order Z[sqrt(2)], s = sqrt(2), and delta = 3 - s. For a and b in O define F = (a^2 + delta^2 b^2)^2, G = 4ab(a^2 - delta^2 b^2), and I = (F,G). The hypothesis (a,b) = O is ideal-theoretic primitivity. No nonvanishing hypothesis is imposed on either coordinate or either duplication form.

The numerator alone is not divisible by s^7 or delta^5. For the dyadic bound, divisibility by s^7 would make the real coordinate of F divisible by sixteen. Twice applying the parity obstruction for X^2 + 2Y^2 modulo four makes both coordinates of a^2 + (delta b)^2 divisible by four. The real and imaginary coordinate congruences then force both a and b to be divisible by s, contrary to primitivity.

Evaluation at s = 3 modulo seven has kernel (delta). If delta^5 divides F, then delta divides a. Writing a = delta c and cancelling delta^4 forces delta to divide c^2 + b^2. The sum of two squares over F_7 vanishes only when both vanish, so delta divides b as well, again contradicting primitivity.

A prime ideal containing F and G, but containing neither two nor delta, cannot contain either a or b. It must therefore contain a^2 - delta^2 b^2. Adding this expression to a^2 + delta^2 b^2 forces a into the prime ideal, a contradiction. The kernels of evaluation at s = 0 modulo two and s = 3 modulo seven are maximal; hence every prime ideal containing I is exactly (s) or (delta).

These local calculations are the arithmetic step in the duplication-height argument of Version 13, Proposition generator. The present result is stated in the explicit order. An identification with the full ring of integers, existence of primitive representatives for all projective points, the ideal norm estimate N(I) <= 2^6 7^4 = 392^2, and the all-point height inequalities remain additional obligations. The intended absolute height is the unnormalized number-field projective logarithmic height divided by the field degree two, with the point at infinity assigned height zero. In that normalization the intended inequalities are 4 h_x(T) - log(392) <= h_x(2T) <= 4 h_x(T) + log(676). The real inequalities at the two embeddings are supplied separately by the source's ModelDuplication bounds; no numerical height estimate is asserted by this theorem.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation.primitive_duplication_local`
