# The integer central-binomial transform

## Abstract

An integer binomial-square transform and its first moment determine two coefficient residue laws.

**Definition 1.1 (The finite binomial-square polynomial).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall a:R, \forall n:\mathbb{N}, \operatorname{Q}\left(a, n\right) = \sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):R))^{2} \cdot (a)^{k}\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k}$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This polynomial has coefficient choose(n,k) squared times a to the k.

**Definition 1.2 (A parameterized summand).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall c:R, \forall a:R, \forall b:R, \forall n:\mathbb{N}, \operatorname{summand}\left(c, a, b, n\right) = (\operatorname{PowerSeries}.\operatorname{X})^{n} \cdot \operatorname{PowerSeries}.\operatorname{invOfUnit}\left((1-\operatorname{PowerSeries}.\operatorname{C}\left(c\right) \cdot \operatorname{PowerSeries}.\operatorname{X})^{2 \cdot n+1}, 1\right) \cdot \operatorname{Q}\left(a, n\right) \cdot \operatorname{Q}\left(b, n\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.summand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial power of X makes the n-th summand vanish below degree n.

**Definition 1.3 (The coefficientwise weighted series).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall w:\mathbb{N} \to R, \forall c:R, \forall a:R, \forall b:R, \operatorname{weighted}\left(w, c, a, b\right) = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (m:\mathbb{N}) \mapsto \operatorname{PowerSeries}.\operatorname{coeff}\left(m, \sum_{n\in \operatorname{Finset}.\operatorname{range}\left(m+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(w\left(n\right)\right) \cdot \operatorname{summand}\left(c, a, b, n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.weighted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coefficient is a finite sum, weighted by the value w(n).

**Theorem 1.4 (Every polynomial coefficient).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall a:R, \forall n:\mathbb{N}, \forall k:\mathbb{N}, \operatorname{PowerSeries}.\operatorname{coeff}\left(k, \operatorname{Q}\left(a, n\right)\right) = ((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):R))^{2} \cdot (a)^{k}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula also covers k greater than n, where the binomial coefficient is zero.

**Theorem 1.5 (The zero parameter).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall n:\mathbb{N}, \operatorname{Q}\left((0:R), n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter zero the binomial-square polynomial is one.

**Theorem 1.6 (The lower coefficients vanish).**

$$\forall R:Type, [\operatorname{CommRing}\left(R\right)] \forall c:R, \forall a:R, \forall b:R, \forall n:\mathbb{N}, \forall k:\mathbb{N}, (k<n) \Rightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left(k, \operatorname{summand}\left(c, a, b, n\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.term_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only indices up to the desired coefficient can contribute.

**Theorem 1.7 (Changing the coefficient ring).**

$$\forall R:Type, \forall S:Type, [\operatorname{CommRing}\left(R\right)] [\operatorname{CommRing}\left(S\right)] \forall hom:R \to^{+*} S, \forall c:R, \forall a:R, \forall b:R, \operatorname{PowerSeries}.\operatorname{map}\left(hom, \operatorname{weighted}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, 1\right), c, a, b\right)\right) = \operatorname{weighted}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, 1\right), hom\left(c\right), hom\left(a\right), hom\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.map_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here hom is a ring homomorphism R to S. Mapping the finite polynomials and the constant-one inverse commutes with every coefficient sum.

**Theorem 1.8 (Changing a weighted coefficient ring).**

$$\forall R:Type, \forall S:Type, [\operatorname{CommRing}\left(R\right)] [\operatorname{CommRing}\left(S\right)] \forall hom:R \to^{+*} S, \forall w:\mathbb{N} \to R, \forall c:R, \forall a:R, \forall b:R, \operatorname{PowerSeries}.\operatorname{map}\left(hom, \operatorname{weighted}\left(w, c, a, b\right)\right) = \operatorname{weighted}\left(\operatorname{fun} (n:\mathbb{N}) \mapsto hom\left(w\left(n\right)\right), hom\left(c\right), hom\left(a\right), hom\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.map_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here hom is a ring homomorphism R to S. The weights are mapped along with the series coefficients.

**Theorem 1.9 (The rational inverse).**

$$\forall c:\mathbb{Q}, \forall n:\mathbb{N}, \operatorname{PowerSeries}.\operatorname{invOfUnit}\left((1-\operatorname{PowerSeries}.\operatorname{C}\left(c\right) \cdot \operatorname{PowerSeries}.\operatorname{X})^{2 \cdot n+1}, 1\right) = (((1-\operatorname{PowerSeries}.\operatorname{C}\left(c\right) \cdot \operatorname{PowerSeries}.\operatorname{X})^{2 \cdot n+1}:\operatorname{PowerSeries}\left(\mathbb{Q}\right)))^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.rational_den` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the rationals the constant-one unit inverse equals the ordinary power-series inverse.

**Theorem 1.10 (The binomial-square transform).**

$$\forall n:\mathbb{N}, \forall t:\mathbb{N}, \sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):\mathbb{Z}))^{2} \cdot (\operatorname{Nat}.\operatorname{choose}\left(2 \cdot n+t-k, 2 \cdot n\right):\mathbb{Z}) = ((\operatorname{Nat}.\operatorname{choose}\left(n+t, n\right):\mathbb{Z}))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.square_binomial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A denominator-free telescoping certificate gives a recurrence in t. The initial finite sum is one; induction and the choose recurrence give the squared binomial coefficient. Natural subtraction truncates at zero.

**Theorem 1.11 (The exact alternating transform).**

$$\forall N:\mathbb{N}, \operatorname{PowerSeries}.\operatorname{coeff}\left(N, \operatorname{weighted}\left(\operatorname{Function}.\operatorname{const}\left(\mathbb{N}, 1\right), (-1:\mathbb{Z}), -1, 0\right)\right) = \operatorname{if} (2\mid N) \operatorname{then} (-1)^{\operatorname{Nat}.\operatorname{div}\left(N, 2\right)} \cdot (\operatorname{Nat}.\operatorname{choose}\left(N, \operatorname{Nat}.\operatorname{div}\left(N, 2\right)\right):\mathbb{Z}) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.R_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Even coefficients are signed central binomial coefficients and odd coefficients vanish. Nat.div denotes natural integer division.

**Theorem 1.12 (The first moment modulo two).**

$$\operatorname{PowerSeries}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{weighted}\left(\operatorname{fun} (n:\mathbb{N}) \mapsto (n:\mathbb{Z}), -1, -1, 0\right)\right) = (\operatorname{PowerSeries}.\operatorname{X}:\operatorname{PowerSeries}\left(\operatorname{ZMod}\left(2\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.T_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the alternating convolution computes the first moment. Its reduction modulo two is exactly X.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q_coeff`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.Q_zero`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.R_coeff`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.T_mod_two`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.map_series`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.map_weighted`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.rational_den`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.square_binomial_sum`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.summand`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.term_low`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.weighted`
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
