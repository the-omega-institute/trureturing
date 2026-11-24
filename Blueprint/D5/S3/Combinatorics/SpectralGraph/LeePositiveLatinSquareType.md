# Lee’s symmetric rank-threshold fusion

## Abstract

The binary symmetric rank-threshold graph in dimension seven fails the positive Latin-square-type valency.

**Definition 1.1 (The positive Latin-square-type claim).**

$$\operatorname{claim} \Leftrightarrow \left(\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Finite}\left(K\right)] \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; 0 < m \Rightarrow \left(\left(\left(m \equiv 3 \pmod{4} \land d = \frac{m + 3}{2}\right) \lor \left(m \equiv 0 \pmod{4} \land d = \frac{m + 2}{2}\right)\right) \Rightarrow \operatorname{let} V := \operatorname{SymmetricMatrix}\left(K, m\right) \operatorname{in} \operatorname{let} G := \operatorname{rankGraph}\left(K, m, d\right) \operatorname{in} \exists n \in \mathbb{N},\; \exists t \in \mathbb{N},\; 0 < n \land \left(0 < t \land \left(\operatorname{card}\left(V\right) = n^{2} \land \left(\left(\forall A \in V,\; \operatorname{degree}\left(G, A\right) = t \cdot (n - 1)\right) \land \left(\forall lambda \in \mathbb{R},\; \left(lambda = (n: \mathbb{R}) - (t: \mathbb{R}) \lor lambda = -(t: \mathbb{R})\right) \Leftrightarrow \left(\exists f \in V \to \mathbb{R},\; f \ne 0 \land \left(\sum_{A \in V} f\left(A\right) = 0 \land \left(\forall A \in V,\; \sum_{B \in \operatorname{neighborFinset}\left(G, A\right)} f\left(B\right) = lambda \cdot f\left(A\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.claim` (`✓ std3`).

*Citation.* Jon Lee (2026). *The dimension of multi-index assignment polytopes and Latin-square transversal polytopes, via association schemes*. DOI: [10.48550/arXiv.2611.12780](https://doi.org/10.48550/arXiv.2611.12780). URL: <https://arxiv.org/abs/2611.12780v1>.

*Commentary.*

Lee’s §6.3 ends with “whether the relation ‘rank at least d’ is of Latin-square type for all such m we leave open.” The field K ranges over all finite fields, including both characteristics and nonprime prime powers. The vertex type V consists of all symmetric m by m matrices over K. In the rank graph G, distinct A and B are adjacent exactly when the rank over K of A − B is at least d. This fuses every rank/type class above or at the threshold. The neighbor set is taken in this full graph. The real sum of f over V vanishes exactly when f is orthogonal to the all-ones vector. The biconditional gives the exact set of restricted eigenvalues from §2.3. Both n − t and −t are evaluated over the reals.

**Theorem 1.2 (Refutation at q = 2, m = 7, d = 5).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Lee (2026). *The dimension of multi-index assignment polytopes and Latin-square transversal polytopes, via association schemes*. DOI: [10.48550/arXiv.2611.12780](https://doi.org/10.48550/arXiv.2611.12780). URL: <https://arxiv.org/abs/2611.12780v1>.

*Commentary.*

The 28 upper-triangular entries give 2²⁸ vertices, so n must be 16,384. Simultaneous reindexing by (0 1 2)(3 4 5) acts on the actual zero-neighbor set with order three. The ten classes of ordered index pairs under reindexing and transpose give exactly 1,024 fixed symmetric matrices. Decoding all 128 binary vectors identifies the parity test with actual kernel membership. Rank-nullity identifies rank at least five with kernel cardinality at most four. The kernel checks 32 chunks of 32 masks, and the equivalence with accepted masks gives 770 fixed zero-neighbors. The nonfixed orbits have size three, so the degree at zero is congruent to 770, or 2 modulo 3. With n = 4⁷, the frozen base-four residue theorem gives n ≡ 1 modulo 3, which makes the required valency t(n − 1) divisible by 3.

Independently, summing Schmidt’s published rank/type valencies gives the exact degree 262,802,624. The Lean proof establishes the obstruction by the orbit congruence.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.result`
- Dependency: [D5/S1/Digit/GoldenBase4ResidueBridge](../../../S1/Digit/GoldenBase4ResidueBridge.md)
