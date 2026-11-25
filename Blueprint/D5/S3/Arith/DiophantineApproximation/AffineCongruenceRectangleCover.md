# Affine congruence obstruction for a missed rectangle

## Abstract

A missed affine rectangle forces a unique primitive label and a phase obstruction.

**Theorem 1.1 (The unique short label and its weighted phase obstruction).**

$$\forall N, M: \mathbb{N}, \forall \theta, \phi, t, w: \mathbb{R}, (0 < w \land w < 1) \to 4 \le (N : \mathbb{R}) \cdot w \to 4 \le (M : \mathbb{R}) \cdot w \to \neg (\exists a: \mathbb{Z}, \exists b, d: \mathbb{N}, N \le b \land b \le 2 \cdot N \land M \le d \land d \le 2 \cdot M \land t < (b : \mathbb{R}) \cdot \theta + (d : \mathbb{R}) \cdot \phi - (a : \mathbb{R}) \land (b : \mathbb{R}) \cdot \theta + (d : \mathbb{R}) \cdot \phi - (a : \mathbb{R}) < t + w) \to \exists L: \operatorname{ShortLabel}\left(N, M, \theta, \phi, w\right), (\forall L': \operatorname{ShortLabel}\left(N, M, \theta, \phi, w\right), L' = L) \land (\forall n: \mathbb{Z}, R_{L} - (L.h : \mathbb{R}) \cdot E_{L} \le \left|(n : \mathbb{R}) - \xi_{L}\right|) \land ((L.h : \mathbb{R}) \cdot w + \left((N : \mathbb{R}) - 2 \cdot (L.h : \mathbb{R})\right) \cdot \left|x_{L}\right| + \left((M : \mathbb{R}) - 2 \cdot (L.h : \mathbb{R})\right) \cdot \left|z_{L}\right| \le 1) \land ((L.h : \mathbb{R}) \le \frac{1}{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover.short_label_miss_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$\operatorname{ShortLabel}\left(N, M, \theta, \phi, w\right)$ contains a natural denominator $L.h$ and signed integer numerators $L.p_{3}$ and $L.p_{5}$ with $1 \le L.h$, joint primitiveness $\gcd\left((L.h : \mathbb{Z}), (\gcd\left(L.p_{3}, L.p_{5}\right) : \mathbb{Z})\right) = 1$, and the joint square bound $\left((N : \mathbb{R}) \cdot x_{L}\right)^{2} + \left((M : \mathbb{R}) \cdot z_{L}\right)^{2} + \left(w \cdot (L.h : \mathbb{R})\right)^{2} \le \frac{11}{3}$.

The signed errors are $x_{L} = (L.h : \mathbb{R}) \cdot \theta - (L.p_{3} : \mathbb{R})$ and $z_{L} = (L.h : \mathbb{R}) \cdot \phi - (L.p_{5} : \mathbb{R})$. The phase is $\xi_{L} = (L.h : \mathbb{R}) \cdot \left(t + \frac{w}{2}\right) - \frac{3 \cdot (N : \mathbb{R})}{2} \cdot x_{L} - \frac{3 \cdot (M : \mathbb{R})}{2} \cdot z_{L}$, the radius is $R_{L} = \frac{(L.h : \mathbb{R}) \cdot w + (N : \mathbb{R}) \cdot \left|x_{L}\right| + (M : \mathbb{R}) \cdot \left|z_{L}\right|}{2}$, and the absolute error sum is $E_{L} = \left|x_{L}\right| + \left|z_{L}\right|$.

The rectangle includes its integer endpoints and the phase window has strict endpoints. The side-width lower bounds keep both rounding margins positive and force the integer cross minors between any two short labels to vanish.

Divide the joint inverse label by its joint gcd to obtain a positive primitive label. Bézout supplies a residue pair for any integer in the inner phase band. A continuous box image and nearest-residue rounding would realize that integer in the target window. Since the window is missed, the phase inequality holds for every integer. Applying it at an integer nearest the phase gives the weighted width bound, whose nonnegative error terms then give the denominator bound. `D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover.finite_rectangle_inverse`

## References

- Truth anchor: `D5/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover.short_label_miss_obstruction`
- Truth anchor: `D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover.finite_rectangle_inverse`
- Dependency: [D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover](FiniteRectangleCircleCover.md)
