# The binary Hankel determinants

## Abstract

Even and odd index splitting proves both determinant families equal one over F2.

Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.

**Definition 1.1 (The positive power-of-two indicator).**

$$\forall n \in Nat,\; epsilon\left(n\right) = ite\left(\exists k \in Nat,\; n = 2^{k}, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Binary.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Values lie in ZMod 2; epsilon(0)=0.

**Definition 1.2 (The first binary family).**

$$\forall k \in Nat,\; S\left(k\right) = det\left((\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: Fin\left(k\right)) \mapsto (\lambda (j: Fin\left(k\right)) \mapsto (epsilon\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + \operatorname{Fin}.\operatorname{val}\left(j\right) + 1\right)))\right): Matrix\left(Fin\left(k\right), Fin\left(k\right), ZMod\left(2\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Binary.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

This is the ordinary Rueppel determinant modulo two.

**Definition 1.3 (The shifted binary family).**

$$\forall k \in Nat,\; T\left(k\right) = det\left((\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: Fin\left(k\right)) \mapsto (\lambda (j: Fin\left(k\right)) \mapsto (epsilon\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + \operatorname{Fin}.\operatorname{val}\left(j\right) + 2\right)))\right): Matrix\left(Fin\left(k\right), Fin\left(k\right), ZMod\left(2\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Binary.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

This is the once-shifted Rueppel determinant modulo two.

**Theorem 1.4 (Both determinants at every size).**

$$\forall n \in Nat,\; S\left(n\right) = 1 \land T\left(n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Binary.rueppel_determinants` (`✓ std3`). ∎

*Citation.* Johann Cigler (2018). *A curious class of Hankel determinants*. DOI: [10.48550/arXiv.1803.05164](https://doi.org/10.48550/arXiv.1803.05164). URL: <https://arxiv.org/abs/1803.05164v2>.

*Commentary.*

Over ZMod 2, parity splitting gives S(2k)=S(k)^2, S(2k+1)=T(k)^2, T(2k)=S(k)T(k), and T(2k+1)=S(k+1)T(k). The exceptional first corner in the odd S case is separated before taking block determinants. Strong induction includes the empty and one-square cases. The cited note attests the ordinary and shifted integer evaluations and their reduction modulo two.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Binary.S`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Binary.T`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Binary.epsilon`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Binary.rueppel_determinants`
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077Blocks](SunA006077Blocks.md)
