# Moments

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

**Definition 1.1 (rieszProduct).**

$$\forall (K : \mathbb{N}) , \operatorname{rieszProduct} K = \prod k \in \operatorname{Finset.range} K , (1 + (1 / 2) \cdot \operatorname{LaurentPolynomial.T} (4^{(k + 1)}) + (1 / 2) \cdot \operatorname{LaurentPolynomial.T} (- 4^{(k + 1)}))$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.rieszProduct` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 3: “The Riesz measure on the unit circle ∂D in ℂ is defined by” the infinite product of 1+(z^(4^k)+z^(-4^k))/2 over k≥1. This polynomial is its finite product through k=K.

**Definition 1.2 (coeffRec).**

$$\begin{aligned}\forall (x : \mathbb{Z}) , \operatorname{coeffRec} 0 x = \operatorname{if} x = 0 \operatorname{then} 1 \operatorname{else} 0\\\forall (x : \mathbb{Z}) (K : \mathbb{N}) , \operatorname{coeffRec} (K + 1) x = \operatorname{coeffRec} K x + (\operatorname{coeffRec} K (x - 4^{(K + 1)}) + \operatorname{coeffRec} K (x + 4^{(K + 1)})) / 2\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.coeffRec` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

At depth zero, coeffRec is one at exponent zero and zero elsewhere. Each successor adds to the preceding coefficient half the sum of the coefficients at the two exponents shifted by the next power of four.

**Definition 1.3 (rieszMoment).**

$$\forall (j : \mathbb{Z}) , \operatorname{rieszMoment} j = (\operatorname{rieszProduct} (\operatorname{Nat.log} 4 (\operatorname{Int.natAbs} j) + 1)) . coeff j$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.rieszMoment` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 3: “The Riesz measure on the unit circle ∂D in ℂ is defined by” the product below. The moments stabilize in the finite products. Nat.log is the integer logarithm and j.natAbs is the absolute value as a natural number.

**Theorem 1.4 (product independent).**

$$\forall (j : \mathbb{Z}) (K L : \mathbb{N}) , \operatorname{Int.natAbs} j < 4^{K} \to \operatorname{Int.natAbs} j < 4^{L} \to (\operatorname{rieszProduct} K) . coeff j = (\operatorname{rieszProduct} L) . coeff j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.product_independent` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For an integer j and natural K and L, if the absolute value of j is less than both four to the Kth power and four to the Lth power, the two finite Riesz products have the same coefficient at j.

**Theorem 1.5 (moment at).**

$$\forall (j : \mathbb{Z}) (K : \mathbb{N}) , \operatorname{Int.natAbs} j < 4^{K} \to \operatorname{rieszMoment} j = \operatorname{coeffRec} K j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.moment_at` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For an integer j and natural K with the absolute value of j less than four to the Kth power, rieszMoment j equals coeffRec K j.

**Theorem 1.6 (moment neg).**

$$\forall (j : \mathbb{Z}) , \operatorname{rieszMoment} (- j) = \operatorname{rieszMoment} j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.moment_neg` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For every integer j, the Riesz moments at j and at its negative are equal.

**Definition 1.7 (SignedRep).**

$$\begin{aligned}\operatorname{SignedRep} : \mathbb{N} \to \mathbb{Z} \to \mathbb{N} \to Prop\\\forall \{K : \mathbb{N}\} \{j : \mathbb{Z}\} \{p : \mathbb{N}\} , \operatorname{SignedRep} K j p \to \operatorname{SignedRep} (K + 1) (j + 4^{(K + 1)}) (p + 1)\\\forall \{K : \mathbb{N}\} \{j : \mathbb{Z}\} \{p : \mathbb{N}\} , \operatorname{SignedRep} K j p \to \operatorname{SignedRep} (K + 1) j p\\\forall \{K : \mathbb{N}\} \{j : \mathbb{Z}\} \{p : \mathbb{N}\} , \operatorname{SignedRep} K j p \to \operatorname{SignedRep} (K + 1) (j - 4^{(K + 1)}) (p + 1)\\\operatorname{SignedRep} 0 0 0\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.SignedRep` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

SignedRep is the least family of propositions on natural K, integer j and natural p generated by exactly the displayed base, skip, plus and minus rules. The final index counts nonzero signs.

**Theorem 1.8 (moment closed form).**

$$\forall \{K : \mathbb{N}\} \{j : \mathbb{Z}\} \{p : \mathbb{N}\} , \operatorname{SignedRep} K j p \to \operatorname{rieszMoment} j = (1 / 2)^{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.moment_closed_form` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

If SignedRep K j p holds, the Riesz moment at j is one half raised to the power p.

**Definition 1.9 (momentForm).**

$$\forall (m : \mathbb{Z} \to \mathbb{R}) , \operatorname{momentForm} m = (\operatorname{Finsupp.linearCombination} \mathbb{R} \operatorname{fun} (i : \mathbb{Z}) \mapsto (\operatorname{Finsupp.linearCombination} \mathbb{R} \operatorname{fun} (j : \mathbb{Z}) \mapsto m (j - i)) \circ_{l} \operatorname{LinearEquiv.toLinearMap}\left((\operatorname{AddMonoidAlgebra.coeffLinearEquiv} \mathbb{R})\right)) \circ_{l} \operatorname{LinearEquiv.toLinearMap}\left((\operatorname{AddMonoidAlgebra.coeffLinearEquiv} \mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.momentForm` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For any real moment sequence on the integers, momentForm is the real bilinear form on Laurent polynomials obtained by summing the product of their coefficients at i and j times the moment at j minus i.

**Theorem 1.10 (momentForm T T).**

$$\forall (m : \mathbb{Z} \to \mathbb{R}) (i j : \mathbb{Z}) , ((\operatorname{momentForm} m) (\operatorname{LaurentPolynomial.T} i)) (\operatorname{LaurentPolynomial.T} j) = m (j - i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.momentForm_T_T` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For any real moment sequence m and integer exponents i and j, its moment form on the two Laurent monomials is m evaluated at j minus i.

**Definition 1.11 (sigma).**

$$\operatorname{sigma} = \operatorname{momentForm} \operatorname{fun} (j : \mathbb{Z}) \mapsto \operatorname{Rat.cast}\left((\operatorname{rieszMoment} j)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.sigma` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

The real bilinear form sigma uses the Riesz moments, cast from rational numbers to real numbers, as its moment sequence.

**Definition 1.12 (tau).**

$$\operatorname{tau} = \operatorname{momentForm} \operatorname{fun} (j : \mathbb{Z}) \mapsto \operatorname{Rat.cast}\left((\operatorname{rieszMoment} (4 \cdot j))\right)$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.tau` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

The real bilinear form tau uses the Riesz moments at four times each integer exponent, cast to real numbers, as its moment sequence.

**Definition 1.13 (J).**

$$\operatorname{J} = \operatorname{AddMonoidAlgebra.mapDomainLinearMap} \mathbb{R} \mathbb{R} \operatorname{fun} (e : \mathbb{Z}) \mapsto 4 \cdot e$$

*Formalization.* `D5/S3/Quantum/Walks/Riesz/Moments.J` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

The real linear map J multiplies every Laurent exponent by four, leaving its coefficient unchanged.

**Theorem 1.14 (J T).**

$$\forall (i : \mathbb{Z}) , \operatorname{J} (\operatorname{LaurentPolynomial.T} i) = \operatorname{LaurentPolynomial.T} (4 \cdot i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.J_T` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

For every integer i, J sends the Laurent monomial with exponent i to the monomial with exponent four times i.

**Theorem 1.15 (riesz residue orthogonality).**

$$\forall (i j : \mathbb{Z}) , i \operatorname{mod} 4 \neq j \operatorname{mod} 4 \to (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} i)) (\operatorname{LaurentPolynomial.T} j) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.riesz_residue_orthogonality` (`✓ std3`). ∎

*Citation.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

Laurent monomials with integer exponents having different remainders modulo four are orthogonal for sigma. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Theorem 1.16 (riesz parity orthogonality).**

$$\forall (i j : \mathbb{Z}) , i \operatorname{mod} 2 \neq j \operatorname{mod} 2 \to (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} i)) (\operatorname{LaurentPolynomial.T} j) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.riesz_parity_orthogonality` (`✓ std3`). ∎

*Citation.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

Laurent monomials with integer exponents having different remainders modulo two are orthogonal for sigma. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Theorem 1.17 (tau density).**

$$\forall (i : \mathbb{Z}) (q : LaurentPolynomial \mathbb{R}) , (\operatorname{tau} (\operatorname{LaurentPolynomial.T} i)) q = (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} i)) q + ((\operatorname{sigma} (\operatorname{LaurentPolynomial.T} (i - 1))) q + (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} (i + 1))) q) / 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.tau_density` (`✓ std3`). ∎

*Citation.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

For every integer i and real Laurent polynomial q, tau on the monomial at i and q equals sigma on that pair plus half the sum of the sigma pairings with the monomials at i minus one and i plus one.

**Theorem 1.18 (decimation isometry).**

$$\forall (p q : LaurentPolynomial \mathbb{R}) , (\operatorname{sigma} (\operatorname{J} p)) (\operatorname{J} q) = (\operatorname{tau} p) q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.decimation_isometry` (`✓ std3`). ∎

*Citation.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

For any two real Laurent polynomials p and q, their sigma pairing after applying J to both equals their tau pairing before applying J.

**Theorem 1.19 (riesz positive definite).**

$$\forall (q : LaurentPolynomial \mathbb{R}) , q \neq 0 \to 0 < (\operatorname{sigma} q) q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Moments.riesz_positive_definite` (`✓ std3`). ∎

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Every nonzero real Laurent polynomial has strictly positive pairing with itself under sigma.

## References

- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.J`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.J_T`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.SignedRep`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.coeffRec`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.decimation_isometry`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.momentForm`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.momentForm_T_T`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.moment_at`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.moment_closed_form`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.moment_neg`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.product_independent`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.rieszMoment`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.rieszProduct`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.riesz_parity_orthogonality`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.riesz_positive_definite`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.riesz_residue_orthogonality`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.sigma`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.tau`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Moments.tau_density`
