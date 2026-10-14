# Decimation

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

**Theorem 1.1 (parity weighted projection).**

$$\forall (B C : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (x t : \mathbb{N}) , (\forall (i j : \mathbb{Z}) , i \operatorname{mod} 2 \neq j \operatorname{mod} 2 \to (B (\operatorname{LaurentPolynomial.T} i)) (\operatorname{LaurentPolynomial.T} j) = 0) \to (\forall (e : \mathbb{Z}) (q : LaurentPolynomial \mathbb{R}) , (C (\operatorname{LaurentPolynomial.T} e)) q = (B (\operatorname{LaurentPolynomial.T} e)) q + ((B (\operatorname{LaurentPolynomial.T} (e - 1))) q + (B (\operatorname{LaurentPolynomial.T} (e + 1))) q) / 2) \to \forall (h : LaurentPolynomial \mathbb{R}) , \operatorname{IsProjection} B (\operatorname{E} x) (\operatorname{LaurentPolynomial.T} (- (2 \cdot \operatorname{Nat.cast}\left(t\right)))) h \to \operatorname{IsProjection} C (\operatorname{W} x) (\operatorname{LaurentPolynomial.T} (- (2 \cdot \operatorname{Nat.cast}\left(t\right)))) h \land (C h) h = (B h) h$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Decimation.parity_weighted_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

If a real bilinear form B pairs monomials of different parity to zero and C is obtained from B by adding half the pairings with the two neighbouring exponents, then for natural x and t a B projection of the monomial at negative twice t onto E x is also a C projection onto W x, with the same self-pairing. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Theorem 1.2 (projection norm scale four).**

$$\forall (x t : \mathbb{N}) \{h k : LaurentPolynomial \mathbb{R}\} , \operatorname{IsProjection} \operatorname{sigma} (\operatorname{V} (2 \cdot x)) (\operatorname{LaurentPolynomial.T} (- (2 \cdot \operatorname{Nat.cast}\left(t\right)))) h \to \operatorname{IsProjection} \operatorname{sigma} (\operatorname{V} (8 \cdot x)) (\operatorname{LaurentPolynomial.T} (- (8 \cdot \operatorname{Nat.cast}\left(t\right)))) k \to (\operatorname{sigma} h) h = (\operatorname{sigma} k) k$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/Riesz/Decimation.projection_norm_scale_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Alberto Grunbaum, Luis Velazquez (2012). *The quantum walk of F. Riesz*. URL: <https://arxiv.org/abs/1111.6630>.

*Commentary.*

For natural x and t, a sigma projection of the monomial at negative twice t onto V at twice x and a sigma projection of the monomial at negative eight times t onto V at eight times x have equal sigma pairings with themselves.

## References

- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Decimation.parity_weighted_projection`
- Truth anchor: `D5/S3/Quantum/Walks/Riesz/Decimation.projection_norm_scale_four`
- Dependency: [D5/S3/Quantum/Walks/CMV/SzegoRecurrence](../CMV/SzegoRecurrence.md)
