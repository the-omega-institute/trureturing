# The three residue classes

## Abstract

Residue classes modulo three give exact block determinant formulas.

Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.

**Definition 1.1 (Unshifted multinomial determinants).**

$$\forall k \in Nat,\; D\left(k\right) = det\left((\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: Fin\left(k\right)) \mapsto (\lambda (j: Fin\left(k\right)) \mapsto (c\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + \operatorname{Fin}.\operatorname{val}\left(j\right)\right)))\right): Matrix\left(Fin\left(k\right), Fin\left(k\right), \mathbb{Z}\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Blocks.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

D(0)=1.

**Definition 1.2 (Shifted multinomial determinants).**

$$\forall k \in Nat,\; E\left(k\right) = det\left((\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: Fin\left(k\right)) \mapsto (\lambda (j: Fin\left(k\right)) \mapsto (c\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + \operatorname{Fin}.\operatorname{val}\left(j\right) + 1\right)))\right): Matrix\left(Fin\left(k\right), Fin\left(k\right), \mathbb{Z}\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Blocks.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

E(0)=1.

**Theorem 1.3 (A zero lower diagonal block).**

$$\forall R \in Type,\; CommRing\left(R\right) \Rightarrow \left(\forall k \in Nat,\; \forall A \in Matrix\left(Fin\left(k\right), Fin\left(k\right), R\right),\; \forall B \in Matrix\left(Fin\left(k\right), Fin\left(k\right), R\right),\; \forall C \in Matrix\left(Fin\left(k\right), Fin\left(k\right), R\right),\; det\left(fromBlocks\left(A, B, C, 0\right)\right) = \left(-1\right)^{k} \cdot det\left(B\right) \cdot det\left(C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Blocks.cross_block_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

For any commutative ring and three k-square matrices A,B,C, the block matrix with rows (A,B) and (C,0) has determinant (-1)^k det(B) det(C). Exchanging its column blocks gives a block triangular matrix; the top left block A is unrestricted.

**Theorem 1.4 (The zero residue formula).**

$$\forall m \in Nat,\; W\left(3 \cdot m\right) = \left(-1\right)^{m} \cdot D\left(m + 1\right) \cdot E\left(m\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Blocks.block_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Group indices by their residues modulo three and apply the same signs to the corresponding rows and columns. The blocks are D of size m+1 and two opposite shifted blocks of size m.

**Theorem 1.5 (The second residue formula).**

$$\forall m \in Nat,\; W\left(3 \cdot m + 2\right) = \left(-1\right)^{m + 1} \cdot D\left(m + 1\right) \cdot E\left(m + 1\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Blocks.block_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

The two shifted blocks now both have size m+1. Simultaneous row and column operations contribute determinant multiplier one.

**Theorem 1.6 (The vanishing residue class).**

$$\forall m \in Nat,\; W\left(3 \cdot m + 1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Blocks.zero_branch` (`✓ std3`). ∎

*Citation.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

The two off-diagonal residue blocks have unequal dimensions, so every permutation term vanishes. Sun v6, Remark 3.16 credits this entire branch to C. Krattenthaler; no originality is claimed for it.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.D`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.E`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.block_two`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.block_zero`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.cross_block_det`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Blocks.zero_branch`
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077](SunA006077.md)
