# Odd repeated blocks and zero-energy Green mass

## Abstract

A repeated odd hopping block forces quadratic mass in its inverse bidiagonal block.

**Definition 1.1 (Forward-substitution entries).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall l \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{E}\left(t, l, 0\right) = \frac{1}{t\left(2 \cdot l\right)} \land \operatorname{E}\left(t, l, d + 1\right) = \frac{\operatorname{E}\left(t, l, d\right) \cdot t\left(2 \cdot \left(l + d\right) + 1\right)}{t\left(2 \cdot \left(l + d + 1\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/OddSquareGreenMass.greenEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an even open path, split the sites into even and odd sublattices. After alternating diagonal sign changes, its off-diagonal block has positive diagonal t(2i) and negative subdiagonal −t(2i+1). The recurrence E is its positive inverse-entry formula, with starting column l and row displacement d. Positive hoppings make every E positive.

**Definition 1.2 (The finite bidiagonal block).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{L}\left(t, n\right)\left(i, j\right) = \operatorname{ite}\left(i = j, t\left(2 \cdot \operatorname{val}\left(i\right)\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right), -t\left(2 \cdot \operatorname{val}\left(j\right) + 1\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OddSquareGreenMass.lowerBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(t,n) is a real matrix on Fin n. Its diagonal is t(2i), its subdiagonal is −t(2j+1), and all other entries vanish. The proof verifies its inverse by multiplication; no invertibility premise is supplied by the caller.

**Theorem 1.3 (Quadratic inverse mass in an odd square).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall q \in \mathbb{N},\; \left(\forall i \in \mathbb{N},\; 0 < t\left(i\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; t\left(i\right) \le 1\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < 2 \cdot q \Rightarrow t\left(i + 2 \cdot q + 1\right) = t\left(i\right)\right) \Rightarrow q \cdot \left(q + 1\right) \le \sum_{l < q} {\sum_{d < q - l} {\left(\operatorname{L}\left(t, 2 \cdot q + 1\right)^{-1}\right)\left(\langle l + d + 1 \rangle, \langle l \rangle\right) + \left(\operatorname{L}\left(t, 2 \cdot q + 1\right)^{-1}\right)\left(\langle q + l + d + 1 \rangle, \langle q + l + 1 \rangle\right)}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OddSquareGreenMass.odd_square_inverse_paired_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All indices are zero based. In the sums, l ranges over Fin q and d over Fin(q−l). Each displayed matrix index denotes the Fin(2q+1) element with that natural value. The bounds on l and d prove that every index exists, including the endpoints. Only the repeated bonds with i<2q are required; this is a finite repetition assumption. Forward substitution gives E(t,l,d+1)E(t,q+l+1,d) =1/(t(2l)t(2(l+d+1))). The repeated odd block exchanges numerator and denominator factors in the shifted interval. Since both endpoint hoppings are at most one, each pair has product at least one and sum at least two. There are q(q+1)/2 pairs. The conclusion concerns the actual finite inverse, rather than an assumed Green function. It does not assert the Tribonacci all-prefix spectral-gap statement: that application also needs the exact occurrence and parity bounds, the embedding into each chosen prefix, and the operator-norm and finite spectral bridges. No infinite-volume spectrum, localization, quasimode or filling hypothesis enters this theorem.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.greenEntry`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.lowerBlock`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.odd_square_inverse_paired_mass`
