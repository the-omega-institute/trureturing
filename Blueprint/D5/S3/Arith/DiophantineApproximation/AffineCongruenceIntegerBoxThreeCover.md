# Affine congruence obstruction for a missed three-axis integer box

## Abstract

A missed strict phase window on a closed three-axis integer box forces a unique positive primitive label.

**Theorem 1.1 (The unique padded short label and its phase obstruction).**

$$\forall N: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, \forall \theta: \operatorname{Fin}\left(3\right) \to \mathbb{R}, \forall t, w: \mathbb{R}, 0 < w \to (\forall i: \operatorname{Fin}\left(3\right), \frac{43}{9} < (N_{i} : \mathbb{R}) \cdot w) \to \neg (\exists b: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, \exists a: \mathbb{Z}, (\forall i: \operatorname{Fin}\left(3\right), N_{i} \le b_{i} \land b_{i} \le 2 \cdot N_{i}) \land t < \sum_{i \in \operatorname{Fin}\left(3\right)} ((b_{i} : \mathbb{R}) \cdot \theta_{i}) - (a : \mathbb{R}) \land \sum_{i \in \operatorname{Fin}\left(3\right)} ((b_{i} : \mathbb{R}) \cdot \theta_{i}) - (a : \mathbb{R}) < t + w) \to \exists L: \operatorname{ShortLabel}\left(N, \theta, w\right), (\forall L': \operatorname{ShortLabel}\left(N, \theta, w\right), L' = L) \land (\forall n: \mathbb{Z}, R_{L} - (L.h : \mathbb{R}) \cdot E_{L} \le \left|(n : \mathbb{R}) - \xi_{L}\right|) \land ((L.h : \mathbb{R}) \cdot w + \sum_{i \in \operatorname{Fin}\left(3\right)} (\left((N_{i} : \mathbb{R}) - 2 \cdot (L.h : \mathbb{R})\right) \cdot \left|x_{L, i}\right|) \le 1) \land ((L.h : \mathbb{R}) \le \frac{1}{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover.short_label_miss_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$\operatorname{ShortLabel}\left(N, \theta, w\right)$ consists of an integer denominator $L.h \in \mathbb{Z}$ with $1 \le L.h$ and an integer numerator function $L.p: \operatorname{Fin}\left(3\right) \to \mathbb{Z}$. Joint primitiveness means $\exists u: \mathbb{Z}, \exists v: \operatorname{Fin}\left(3\right) \to \mathbb{Z}, L.h \cdot u + \sum_{i \in \operatorname{Fin}\left(3\right)} (L.p_{i} \cdot v_{i}) = 1$. The padded joint square bound is $\sum_{i \in \operatorname{Fin}\left(3\right)} (\left(\left((N_{i} : \mathbb{R}) + 2\right) \cdot x_{L, i}\right)^{2}) + \left(w \cdot (L.h : \mathbb{R})\right)^{2} \le \frac{43}{9}$.

For each axis the signed error is $x_{L, i} = (L.h : \mathbb{R}) \cdot \theta_{i} - (L.p_{i} : \mathbb{R})$. The phase and radius use the original side lengths $N_{i}$. The phase is $\xi_{L} = (L.h : \mathbb{R}) \cdot \left(t + \frac{w}{2}\right) - \sum_{i \in \operatorname{Fin}\left(3\right)} (\frac{3 \cdot (N_{i} : \mathbb{R})}{2} \cdot x_{L, i})$, the radius is $R_{L} = \frac{(L.h : \mathbb{R}) \cdot w + \sum_{i \in \operatorname{Fin}\left(3\right)} ((N_{i} : \mathbb{R}) \cdot \left|x_{L, i}\right|)}{2}$, and the error sum is $E_{L} = \sum_{i \in \operatorname{Fin}\left(3\right)} (\left|x_{L, i}\right|)$.

The finite-box inverse supplies a positive joint resonance. Divide all four integer coordinates by their joint gcd. The joint squared length can only decrease, and the gcd identity gives Bézout's identity for the reduced label. `D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three`

For uniqueness, project two labels to the two coordinates Nᵢδᵢ and wh on each axis i. Each row has squared length at most 43/9, since the padded bound also bounds the unpadded rows. The area of the two rows is at most the product of their lengths, hence at most 43/9. That area is Nᵢw times the absolute value of the integer cross minor h p′ᵢ − h′ pᵢ. The strict side-width hypothesis forces each minor to vanish. The two Bézout identities then give mutual divisibility of the positive denominators and equality of the numerators.

The unpadded square estimate and the side-width hypotheses give 2h < Nᵢ on every axis and E < w. If an integer n lay strictly inside the phase band of radius R − hE, the continuous linear image of the inset box [Nᵢ + h/2, 2Nᵢ − h/2] would meet the phase interval after reserving hE/2 for rounding. For Bézout coefficients u and vᵢ, round each inset coordinate to the nearest integer bᵢ in the class n vᵢ modulo h. This preserves the original closed box and realizes ∑ᵢ bᵢpᵢ − ha = n for an integer a. Each coordinate moves by at most h/2, so the change in the linear image is at most hE/2 and the resulting phase hit is strict.

Apply the exclusion inequality to an integer nearest the phase. Its distance is at most 1/2, giving 2(R − hE) ≤ 1, the weighted width bound. The weights Nᵢ − 2h are positive, so dropping the error sum and dividing by w gives the reciprocal denominator bound.

## References

- Truth anchor: `D5/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover.short_label_miss_obstruction`
- Truth anchor: `D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three`
- Dependency: [D5/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover](AffineCongruenceRectangleCover.md)
- Dependency: [D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover](FiniteIntegerBoxThreeCircleCover.md)
