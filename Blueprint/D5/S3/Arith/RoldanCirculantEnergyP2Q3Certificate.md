# The polynomial coefficient certificate for integral circulant energy

## Abstract

An exact integer coefficient comparison gives a uniform energy deficit for every mask below 2048 other than 1445 on the nonnegative quadrant.

**Definition 1.1 (A: prime-power coefficient data).**

$$(\operatorname{A} : \operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \mathbb{Z}\right)\right)) = ![![![0, 0, 0], ![-1, 0, 0], ![1, 0, 0]], ![![-3, -1, 0], ![2, 1, 0], ![1, 0, 0]], ![![6, 5, 1], ![2, 1, 0], ![1, 0, 0]]]$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent and columns index the divisor exponent.

**Definition 1.2 (B: prime-power coefficient data).**

$$(\operatorname{B} : \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \mathbb{Z}\right)\right)) = ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![-3, -1, 0, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]], ![![-9, -6, -1, 0], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]], ![![18, 21, 8, 1], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]]]$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent and columns index the divisor exponent.

**Definition 1.3 (wA: prime-power coefficient data).**

$$(\operatorname{wA} : \operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \mathbb{Z}\right)) = ![![6, 5, 1], ![2, 1, 0], ![1, 0, 0]]$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.wA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent; columns give coefficients in increasing exponent order.

**Definition 1.4 (wB: prime-power coefficient data).**

$$(\operatorname{wB} : \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \mathbb{Z}\right)) = ![![18, 21, 8, 1], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]]$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.wB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent; columns give coefficients in increasing exponent order.

**Definition 1.5 (The divisor-mask bit).**

$$\forall mask \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(3\right),\; \forall f \in \operatorname{Fin}\left(4\right),\; \operatorname{switch}\left(mask, c, f\right) = \operatorname{if} ((\operatorname{val}\left(c\right) = 2) \land (\operatorname{val}\left(f\right) = 3)) \operatorname{then} 0 \operatorname{else} \operatorname{if} \operatorname{Nat}.\operatorname{testBit}\left(mask, ((4) \cdot (\operatorname{val}\left(c\right))) + (\operatorname{val}\left(f\right))\right) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.switch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The (2,3) entry is zero. Every other entry is the bit of mask at position 4c + f, interpreted as an integer.

**Definition 1.6 (Spectral polynomial coefficients).**

$$\forall mask \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(3\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{lcoeff}\left(mask, a, b, i, j\right) = \sum_{c : \operatorname{Fin}\left(3\right)} (\sum_{f : \operatorname{Fin}\left(4\right)} (((\operatorname{A}\left(a, c, i\right)) \cdot (\operatorname{B}\left(b, f, j\right))) \cdot (\operatorname{switch}\left(mask, c, f\right))))$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.lcoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral coefficient is the sum over the two divisor exponents of the product of the two prime-power table entries and the selected bit.

**Definition 1.7 (The maximizing mask).**

$$\operatorname{star} = 1445$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.star` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eleven low bits encode the six divisors of Dstar.

**Definition 1.8 (Evaluation of a rectangular integer coefficient array).**

$$\forall r \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall C \in \operatorname{Fin}\left(r\right) \to \left(\operatorname{Fin}\left(s\right) \to \mathbb{Z}\right),\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{eval}\left(C, u, v\right) = \sum_{i : \operatorname{Fin}\left(r\right)} (\sum_{j : \operatorname{Fin}\left(s\right)} ((((C\left(i, j\right) : \mathbb{R})) \cdot ((u)^{\operatorname{val}\left(i\right)})) \cdot ((v)^{\operatorname{val}\left(j\right)})))$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.eval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An array is evaluated by the finite double sum of its integer coefficients cast to the reals, multiplied by the corresponding powers of u and v.

**Definition 1.9 (Evaluation of a weight polynomial).**

$$\forall R \in \operatorname{Type},\; [\operatorname{Ring}\left(R\right)] \forall r \in \mathbb{N},\; \forall C \in \operatorname{Fin}\left(r\right) \to \mathbb{Z},\; \forall x \in R,\; \operatorname{evalW}\left(C, x\right) = \operatorname{Polynomial}.\operatorname{eval}\left(x, \operatorname{Polynomial}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(R\right), \operatorname{Polynomial}.\operatorname{ofFn}\left(r, C\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.evalW` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight polynomial is the finite sum of its integer coefficients cast into a ring, times successive powers of x.

**Definition 1.10 (The weighted absolute spectral sum).**

$$\forall mask \in \mathbb{N},\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{modelEnergy}\left(mask, u, v\right) = \sum_{a : \operatorname{Fin}\left(3\right)} (\sum_{b : \operatorname{Fin}\left(4\right)} (((\operatorname{evalW}\left(\operatorname{wA}\left(a\right), u\right)) \cdot (\operatorname{evalW}\left(\operatorname{wB}\left(b\right), v\right))) \cdot (\left|\operatorname{eval}\left(\operatorname{lcoeff}\left(mask, a, b\right), u, v\right)\right|)))$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.modelEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are three exponents for p and four for q. Each spectral polynomial contributes its absolute value with the product of the two totient weight polynomials.

**Theorem 1.11 (A uniform gap of at least 96).**

$$\forall mask \in \operatorname{Fin}\left(2048\right),\; (\neg (\operatorname{val}\left(mask\right) = \operatorname{star})) \Rightarrow (\forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; (0 \le u) \Rightarrow ((0 \le v) \Rightarrow (96 \le (\operatorname{modelEnergy}\left(\operatorname{star}, u, v\right)) - (\operatorname{modelEnergy}\left(\operatorname{val}\left(mask\right), u, v\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.model_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every mask below 2048 other than 1445 and all nonnegative u and v, the maximizing mask exceeds that mask's weighted absolute spectral sum by at least 96. The proof compares integer coefficient arrays exactly and uses the triangle inequality for polynomial evaluation. At the maximizing mask every spectral polynomial has coefficients of one sign, so the majorant is attained.

## References

- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.A`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.B`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.eval`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.evalW`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.lcoeff`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.modelEnergy`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.model_gap`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.star`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.switch`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.wA`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.wB`
