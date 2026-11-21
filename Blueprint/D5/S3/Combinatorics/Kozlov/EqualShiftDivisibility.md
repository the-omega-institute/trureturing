# The equal-shift Kozlov deficiency factor

## Abstract

For every positive ground-set size, the proper-sum and real-dilate lattice counts each extend to a rational polynomial. Their difference vanishes at zero and minus one.

**Definition 1.1 (Agreement with a literal count at positive ranks).**

$$\operatorname{AgreesOnPositiveRanks}\left(P, c\right) \Leftrightarrow \left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \operatorname{P}\left(r\right) = \operatorname{rat}\left(\operatorname{c}\left(r\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.AgreesOnPositiveRanks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For every positive natural rank, the rational evaluation equals the natural count cast to the rationals.

**Theorem 1.2 (Both literal counts have rational interpolants).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\exists A \in \mathbb{Q}[X],\; \exists L \in \mathbb{Q}[X],\; \left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \operatorname{A}\left(r\right) = \operatorname{rat}\left(\operatorname{properCount}\left(n, r\right)\right)\right) \land \left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \operatorname{L}\left(r\right) = \operatorname{rat}\left(\operatorname{latticeCount}\left(n, r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_count_polynomials_exist` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Part III, Corollary 34, states polynomiality of both counts and credits Part II, Theorems 36 and 41, for the proper count and its transfer formula. Here the rational witnesses come from the two falling-binomial matrix polynomials composed with X+1. The unconditional proper and lattice transfer laws identify each entry of power r+1 with its literal count at every positive rank r.

**Theorem 1.3 (Divisibility by X times X plus one).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall A \in \mathbb{Q}[X],\; \forall L \in \mathbb{Q}[X],\; \left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \operatorname{A}\left(r\right) = \operatorname{rat}\left(\operatorname{properCount}\left(n, r\right)\right)\right) \Rightarrow \left(\left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \operatorname{L}\left(r\right) = \operatorname{rat}\left(\operatorname{latticeCount}\left(n, r\right)\right)\right) \Rightarrow X \cdot (X + 1) \mid L - A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_kozlov_deficiency_divisible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Infinitely many positive natural ranks identify each interpolant with its matrix polynomial. At argument zero the relevant power is one and the first-to-last entry is one in each matrix. At argument minus one the relevant power is zero, so the identity entry is one when n=1 and zero otherwise. Thus the difference has both roots, giving the product of the two factors. This proves the divisibility question in Part III, Section 10 item 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.AgreesOnPositiveRanks`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_count_polynomials_exist`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.equal_shift_kozlov_deficiency_divisible`
- Dependency: [D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial](MatrixPowerPolynomial.md)
- Dependency: [D5/S3/Combinatorics/Kozlov/TransferEndpoints](TransferEndpoints.md)
