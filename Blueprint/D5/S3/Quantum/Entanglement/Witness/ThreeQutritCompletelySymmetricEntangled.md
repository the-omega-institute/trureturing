# An entangled completely symmetric three-qutrit density matrix

## Abstract

A completely symmetric density matrix on three qutrits has no fully separable decomposition.

**Definition 1.1 (Complete symmetry of all index positions).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.IsCompletelySymmetric}\left(\rho\right)\right) \Leftrightarrow \left(\forall \left(\pi: \operatorname{Equiv.Perm}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)\right)\right), \left(\forall \left(i: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right)\right), \left(\forall \left(j: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right)\right), \left(\rho\left(\lambda \left(k: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{Sum.elim}\left(i, j, \operatorname{Equiv.toFun}\left(\pi, \operatorname{Sum.inl}\left(k\right)\right)\right)\right), \lambda \left(k: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{Sum.elim}\left(i, j, \operatorname{Equiv.toFun}\left(\pi, \operatorname{Sum.inr}\left(k\right)\right)\right)\right)\right) = \rho\left(i, j\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.IsCompletelySymmetric` (`✓ std3`).

*Citation.* Lin Chen; Delin Chu; Lilong Qian; Yi Shen (2019). *Separability of completely symmetric states in a multipartite system*. DOI: [10.1103/PhysRevA.99.032312](https://doi.org/10.1103/PhysRevA.99.032312). URL: <https://arxiv.org/abs/1812.04182v4>.

*Commentary.*

A word is a function from Fin d to Fin 3. The two copies of Fin d label the ket and bra positions. Every permutation of their disjoint union rearranges all twice d positions, including permutations that mix the ket and bra. The matrix entry must remain unchanged. This is Definition 1 of the source, arXiv:1812.04182v4, CSv2.tex lines 360–391, with local dimension three. The predicate is defined for every complex matrix and every natural d; positivity and trace one are separate conditions.

**Definition 1.2 (Finite mixtures of unit product projectors).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.IsFullySeparable}\left(\rho\right)\right) \Leftrightarrow \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(wt: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{R}\right)\right), \left(\exists \left(v: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(d\right)\right) \to \left(\left(\operatorname{Fin}\left(3\right)\right) \to \left(\mathbb{C}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(0 < wt\left(i\right)\right)\right) \land \left(\left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(wt\left(i\right)\right)\right) = 1\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(k: \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right)\right), \lambda \left(j: \operatorname{Fin}\left(3\right)\right) \mapsto \left(\operatorname{Complex.normSq}\left(v\left(i, k, j\right)\right)\right)\right) = 1\right)\right)\right) \land \left(\rho = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(wt\left(i\right)\right), \operatorname{Matrix.vecMulVec}\left(\operatorname{DFunLike.coe}\left(\operatorname{MultilinearMap.piFamily}\left(\operatorname{Function.const}\left(\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \operatorname{MultilinearMap.mkPiAlgebra}\left(\mathbb{C}, \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), v\left(i\right)\right), \operatorname{Star.star}\left(\operatorname{DFunLike.coe}\left(\operatorname{MultilinearMap.piFamily}\left(\operatorname{Function.const}\left(\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \operatorname{MultilinearMap.mkPiAlgebra}\left(\mathbb{C}, \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), v\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.IsFullySeparable` (`✓ std3`).

*Citation.* Lin Chen; Delin Chu; Lilong Qian; Yi Shen (2019). *Separability of completely symmetric states in a multipartite system*. DOI: [10.1103/PhysRevA.99.032312](https://doi.org/10.1103/PhysRevA.99.032312). URL: <https://arxiv.org/abs/1812.04182v4>.

*Commentary.*

Choose a finite number n of summands, strictly positive real weights wt summing to one, and a unit complex vector v i k for each summand i and subsystem k. The sum of squared complex norms of each local vector is one. The multilinear product map forms the product vector, and its outer product with its pointwise conjugate forms its rank-one projector. The real weight is included in the complex scalars before scalar multiplication of that projector. The constant family of multiplication maps is indexed by the word type. This specializes the source's convex-mixture definition at CSv2.tex lines 244–252 and its multipartite definition of full separability at lines 444–452.

**Definition 1.3 (The universal multi-qutrit separability assertion).**

$$\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\left(3 \le d\right) \to \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.IsCompletelySymmetric}\left(\rho\right)\right) \to \left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.IsFullySeparable}\left(\rho\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Chen; Delin Chu; Lilong Qian; Yi Shen (2019). *Separability of completely symmetric states in a multipartite system*. DOI: [10.1103/PhysRevA.99.032312](https://doi.org/10.1103/PhysRevA.99.032312). URL: <https://arxiv.org/abs/1812.04182v4>.

*Commentary.*

For every natural d at least three, every positive semidefinite complex matrix of trace one on d qutrits is fully separable whenever it is completely symmetric. This is the universal assertion associated with the source's question, ‘Are multi-qutrit CS states separable?’, at CSv2.tex line 1857. The quantifier starts at three subsystems; it makes no assertion about two qutrits.

**Theorem 1.4 (A three-qutrit counterexample).**

$$\neg \left(\operatorname{D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-chu-qian-shen-2019-multi-qutrit-completely-symmetric-separability` (refuted) by `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-chu-qian-shen-2019-multi-qutrit-completely-symmetric-separability","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Chen; Delin Chu; Lilong Qian; Yi Shen (2019). *Separability of completely symmetric states in a multipartite system*. DOI: [10.1103/PhysRevA.99.032312](https://doi.org/10.1103/PhysRevA.99.032312). URL: <https://arxiv.org/abs/1812.04182v4>.

*Commentary.*

For a three-letter word, its occupation tuple records the numbers of zeros, ones and twos. Each coordinate is the sum of its three equality indicators, and summing over words is summing independently over their three letters. The ten possible occupation tuples are (3,0,0), (1,2,0), (1,0,2), (0,3,0), (2,1,0), (0,1,2), (0,0,3), (2,0,1), (0,2,1) and (1,1,1). Define a real function y of the combined occupation tuple by the nonzero values y(6,0,0) = y(0,6,0) = 132; y(0,0,6) = 3; y(4,2,0) = y(2,4,0) = y(2,2,2) = 4; y(4,0,2) = y(0,4,2) = 20; and y(2,0,4) = y(0,2,4) = 6, with zero elsewhere. Let ρ have entry y(q)/471, included from the reals into the complex numbers, when q is the sum of the two word occupation tuples. A permutation of the six positions preserves each combined letter count: the two indicator sums are one sum over the disjoint union, invariant under reindexing by the permutation. Thus ρ is completely symmetric.

For each occupation tuple q, let e_q be the complex-valued indicator of its word class. Use the seven vectors e_(3,0,0) + e_(1,2,0) + e_(1,0,2), 8e_(3,0,0) + e_(1,0,2), e_(0,3,0) + e_(2,1,0) + e_(0,1,2), 8e_(0,3,0) + e_(0,1,2), e_(0,0,3) + 2e_(2,0,1) + 2e_(0,2,1), e_(2,0,1) − e_(0,2,1), and e_(1,1,1). The matrix ρ is the sum of their rank-one projectors with respective weights 4, 2, 4, 2, 3, 8 and 4, all divided by 471. This identity follows by evaluating the hundred pairs of occupation classes. Each projector and each weighted term is positive semidefinite, hence so is their sum. The real trace numerator is 2·132 + 3 + 6·4 + 6·20 + 6·6 + 6·4 = 471; every diagonal entry has zero imaginary part. Therefore ρ has trace one.

Consider any decomposition of ρ into rank-one projectors with strictly positive real weights wt j and vectors ψ j. If words a and b have the same occupation tuple, the four entries give ρ(a,a) + ρ(b,b) − ρ(a,b) − ρ(b,a) = 0. Expanding those entries and taking real parts gives the sum of wt j times the squared norm of ψ j a − ψ j b equal to zero. Every summand is nonnegative, and every weight is strictly positive, so each difference vanishes. Thus every vector in such a decomposition is constant on each occupation class.

A product vector with this constancy is a scalar multiple of a third tensor power. For the zero vector choose scalar zero and the zero local vector. Otherwise choose a word w where its product amplitude is nonzero, so all three local factors there are nonzero. Swapping the first two letters and then the first and third letters preserves occupation tuples. Canceling the corresponding nonzero factors in these two identities shows that the second local vector is the first multiplied by v 1 (w 0) / v 0 (w 0), and the third is the first multiplied by v 2 (w 0) / v 0 (w 0). Consequently the product amplitude at any word is c times the product of the coordinates of x, where x is v 0 and c is the product of those two ratios.

For nonnegative real a, b and c, the three-term arithmetic–geometric mean inequality with equal weights one third, applied to a²b, ab² and c³, gives a²b + ab² + c³ − 3abc ≥ 0, since their product is (abc)³. Define a diagonal real functional W on words by assigning one third to occupation tuples (2,1,0) and (1,2,0), one to (0,0,3), minus one half to (1,1,1), and zero elsewhere. For a scalar multiple of a third tensor power its value is the squared norm of the scalar times a²b + ab² + c³ − 3abc, where a, b and c are the squared norms of the three coordinates of the local vector. Expanding over the 27 words proves this identity. The preceding inequality makes the value nonnegative, so it is nonnegative for every product vector constant on occupation classes.

Direct evaluation on ρ gives the W-weighted diagonal sum (4 + 4 + 3 − 12)/471 = −1/471. If ρ were fully separable, its product vectors would be constant on occupation classes by the positive-weight argument. Its real diagonal entries would be sums of the positive weights times the squared norms of those product amplitudes. Interchanging the two finite sums would express the W-weighted diagonal sum as a sum of nonnegative terms. This contradicts its strictly negative value, proving that ρ is entangled. Finally, applying the universal assertion at d = 3 to the positive semidefinite, trace-one, completely symmetric matrix ρ would make it fully separable, yielding the contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.IsCompletelySymmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.IsFullySeparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum](../../../Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.md)
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../../Information/SLDSpectralEnergy.md)
