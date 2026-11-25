# Dyadic Pochhammer coefficients

## Abstract

The ascending Pochhammer coefficients of the dyadic row polynomials.

**Definition 1.1 (Ascending Pochhammer basis).**

$$\forall j \in \mathbb{N}, \operatorname{pochhammerBasis}\left(j\right) = \operatorname{ascPochhammer}\left(\mathbb{Q}, j\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.pochhammerBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The monic ascending Pochhammer polynomials indexed by their natural degree form the basis of the rational polynomial module.

**Lemma 1.2 (Coordinates of a basis polynomial).**

$$\forall i, j \in \mathbb{N}, \operatorname{coord}\left(i, \operatorname{ascPochhammer}\left(\mathbb{Q}, j\right)\right) = \operatorname{ite}\left(j = i, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.coord_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The coordinate at i of the ascending Pochhammer polynomial of degree j is one for j=i and zero otherwise.

**Definition 1.3 (Rational row polynomial).**

$$\forall n \in \mathbb{N}, \operatorname{rationalRow}\left(n\right) = \operatorname{map}\left(\operatorname{R}\left(n\right), \mathbb{Q}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

Map every coefficient of the integer row R(n) to the rationals.

**Definition 1.4 (Row polynomial multiplied by the variable).**

$$\forall n \in \mathbb{N}, \operatorname{rowPolynomial}\left(n\right) = X \cdot \operatorname{rationalRow}\left(n\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rowPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

Multiply the rational row by X.

**Definition 1.5 (The dyadic difference operator).**

$$\forall P \in \mathbb{Q}[X], \operatorname{difference}\left(P\right) = X \cdot (\operatorname{comp}\left(P, X+1\right)-P)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.difference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

Send P(X) to X times the difference P(X+1)−P(X), as a rational linear map.

**Lemma 1.6 (Odd row recurrence).**

$$\forall n \in \mathbb{N}, \operatorname{rationalRow}\left(2 \cdot n+1\right) = X \cdot \operatorname{rationalRow}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

At every index 2n+1, multiply the rational row at n by X.

**Lemma 1.7 (Positive even row recurrence).**

$$\forall n \in \mathbb{N}, 0 < n \implies \operatorname{rationalRow}\left(2 \cdot n\right) = \operatorname{difference}\left(\operatorname{rationalRow}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

At index 2n with n positive, apply the dyadic difference operator to the row at n.

**Lemma 1.8 (Eigenvalue of a basis polynomial).**

$$\forall j \in \mathbb{N}, \operatorname{difference}\left(\operatorname{ascPochhammer}\left(\mathbb{Q}, j\right)\right) = (j: \mathbb{Q}) \cdot \operatorname{ascPochhammer}\left(\mathbb{Q}, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.difference_pochhammer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

The degree j basis polynomial is an eigenvector of the difference operator with eigenvalue j.

**Definition 1.9 (Signed coordinate).**

$$\forall n, i \in \mathbb{N}, \operatorname{signedCoefficient}\left(n, i\right) = (-1)^{\operatorname{wt}\left(n\right)+i} \cdot \operatorname{coord}\left(i, \operatorname{rowPolynomial}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.signedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

Multiply the coordinate in column i of the row polynomial by minus one to the power wt(n)+i, where wt is binary popcount.

**Lemma 1.10 (Literal A358612 correspondence).**

$$\forall n, j \in \mathbb{N}, \operatorname{coord}\left(j, \operatorname{rowPolynomial}\left(n\right)\right) = (-1)^{\operatorname{wt}\left(n\right)+2-j} \cdot \operatorname{T}\left(n, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.source_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

For every row and column, the coordinate is the literal rational A358612 entry times the sign with natural exponent wt(n)+2−j. Beyond the row edge the literal array is zero. Column zero has the same zero extension.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.coord_basis`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.difference`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.difference_pochhammer`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.pochhammerBasis`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow_even`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rationalRow_odd`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.rowPolynomial`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.signedCoefficient`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient.source_coordinate`
- Dependency: [D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge](DyadicExtendedStirlingEdge.md)
