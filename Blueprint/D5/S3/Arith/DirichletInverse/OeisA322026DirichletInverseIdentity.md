# The OEIS A322026 Dirichlet-inverse identity

## Abstract

Sequence Machine's OEIS A322026 identity with the Dirichlet inverse correction.

**Definition 1.1 (The A322026 rank formula).**

$$\begin{aligned}\operatorname{a}\left(0\right) = 0\\\forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{latticeCount}\left(2^{\operatorname{factorization}\left(n, 2\right)} \cdot 3^{\operatorname{factorization}\left(n, 3\right)}\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.a` (`✓ std3`).

*Citation.* Sequence Machine; Antti Karttunen (2024). *OEIS A322026, whole Dirichlet-inverse identity*. URL: <https://oeis.org/A322026>.

*Commentary.*

The formal function sets a(0)=0. For positive n, the source formula is A071521(A065331(n)): count nonnegative exponent pairs whose 2,3-number is at most the product of the 2- and 3-adic valuation powers.

**Definition 1.2 (The A322026 Dirichlet inverse).**

$$b = \operatorname{dirichletInverse}\left(a\right)$$

*Formalization.* `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.b` (`✓ std3`).

*Citation.* Sequence Machine; Antti Karttunen (2024). *OEIS A322026, whole Dirichlet-inverse identity*. URL: <https://oeis.org/A322026>.

*Commentary.*

b is the integer-valued Dirichlet inverse of a under positive-index Dirichlet convolution; the zero index is carried by the arithmetic-function convention.

**Theorem 1.3 (The whole A322026 identity).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{a}\left(25 \cdot n\right) + \operatorname{b}\left(25 \cdot n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a322026-sequence-machine-dirichlet-inverse-identity` (proved) by `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a322026-sequence-machine-dirichlet-inverse-identity","declaration_gid":"D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sequence Machine; Antti Karttunen (2024). *OEIS A322026, whole Dirichlet-inverse identity*. URL: <https://oeis.org/A322026>.

*Commentary.*

The proof uses a(5n)=a(n). A general convolution argument shows that the inverse of any unit-headed arithmetic function with this 5-insensitivity vanishes at every 25n. Therefore a(25n)=a(n) and the inverse correction b(25n) is zero.

## References

- Truth anchor: `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.a`
- Truth anchor: `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.b`
- Truth anchor: `D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.result`
