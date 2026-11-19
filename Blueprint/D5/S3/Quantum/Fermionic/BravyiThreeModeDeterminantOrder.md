# Shifted determinants of the three-mode Bravyi blocks

## Abstract

Shifted determinant order for the real isotropic three-mode Bravyi blocks.

Bravyi studies the isotropic three-mode channel in Classical capacity of fermionic product channels (arXiv:quant-ph/0507282, Section V.B). The chiral and complementary real blocks have sizes four and two. Each comparator takes the first and third amplitudes to be the positive square root of one half and the second to be zero.

**Theorem 1.1 (The three chiral coefficient differences).**

$$\forall lam \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; c^{2} + p^{2} + q^{2} = 1 \Rightarrow \operatorname{shiftedDetPolynomial}\left(\operatorname{chiral}\left(\mathit{lam}, c, p, q\right)\right) - \operatorname{shiftedDetPolynomial}\left(\operatorname{chiralComparator}\left(\mathit{lam}\right)\right) = \operatorname{\mathit{Polynomial}.C}\left(\operatorname{delta2}\left(\mathit{lam}^{2}, \operatorname{invariantX}\left(c\right), \operatorname{invariantZ}\left(c, p\right)\right)\right) \cdot \operatorname{\mathit{Polynomial}.X}^{2} + \operatorname{\mathit{Polynomial}.C}\left(\operatorname{delta3}\left(\mathit{lam}^{2}, \operatorname{invariantX}\left(c\right), \operatorname{invariantZ}\left(c, p\right)\right)\right) \cdot \operatorname{\mathit{Polynomial}.X} + \operatorname{\mathit{Polynomial}.C}\left(\operatorname{delta4}\left(\mathit{lam}^{2}, \operatorname{invariantX}\left(c\right), \operatorname{invariantZ}\left(c, p\right), \operatorname{invariantR}\left(c, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.chiral_det_polynomial_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Laplace expansion depends on the squares of the amplitudes. Eliminating the third square by normalization gives the quadratic, linear and constant coefficients. Homogenizing the constant term using invariantX + invariantZ + invariantR = 1 expresses it as a sum of nonnegative terms at every channel parameter from zero through one.

**Theorem 1.2 (The complementary constant difference).**

$$\forall lam \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; c^{2} + p^{2} + q^{2} = 1 \Rightarrow \operatorname{shiftedDetPolynomial}\left(\operatorname{complement}\left(\mathit{lam}, c, q\right)\right) - \operatorname{shiftedDetPolynomial}\left(\operatorname{complementComparator}\left(\mathit{lam}\right)\right) = \operatorname{\mathit{Polynomial}.C}\left(\operatorname{complementDelta}\left(\mathit{lam}^{2}, \operatorname{invariantX}\left(c\right), \operatorname{invariantZ}\left(c, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.complement_det_polynomial_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary trace is independent of the amplitudes, so the difference comes entirely from the unshifted determinant.

**Theorem 1.3 (Both comparator determinants are lower bounds).**

$$\forall s \in \mathbb{R},\; \forall lam \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 0 \le s \Rightarrow \left(0 \le \mathit{lam} \Rightarrow \left(\mathit{lam} \le 1 \Rightarrow \left(c^{2} + p^{2} + q^{2} = 1 \Rightarrow \left(\operatorname{\mathit{Matrix}.\mathit{det}}\left(s \cdot (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right)) + \operatorname{chiralComparator}\left(\mathit{lam}\right)\right) \le \operatorname{\mathit{Matrix}.\mathit{det}}\left(s \cdot (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right)) + \operatorname{chiral}\left(\mathit{lam}, c, p, q\right)\right) \land \operatorname{\mathit{Matrix}.\mathit{det}}\left(s \cdot (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)) + \operatorname{complementComparator}\left(\mathit{lam}\right)\right) \le \operatorname{\mathit{Matrix}.\mathit{det}}\left(s \cdot (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)) + \operatorname{complement}\left(\mathit{lam}, c, q\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.det_shift_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate both difference polynomials at the nonnegative shift. The chiral difference has three nonnegative terms, and the complementary constant is nonnegative. The argument uses the closed parameter interval, including zero and one.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.chiral_det_polynomial_difference`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.complement_det_polynomial_difference`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder.det_shift_order`
