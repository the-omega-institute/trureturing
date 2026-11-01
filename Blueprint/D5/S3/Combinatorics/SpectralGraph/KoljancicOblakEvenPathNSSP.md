# Even looped paths allow the non-symmetric Strong Spectral Property

## Abstract

Exact-support witnesses for every positive even double path and every nonempty loop set.

The target is the unchanged existential event in Koljančić–Oblak Question 5.11. Both orientations of every consecutive path edge occur, and the only additional arcs are exactly the loops at the nonempty vertex set L. The source vertex i corresponds to Fin n value i minus one. Every real test matrix X is permitted. In particular, no symmetry or diagonal condition is imposed on X.

**Theorem 1.1 (The complete all-orders and all-loop-sets event).**

$$\forall n \in \operatorname{Nat},\; 0 < n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \left(\forall L \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Nonempty}\left(L\right) \Rightarrow \left(\exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \ne 0 \Leftrightarrow \left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right) \lor \left(i = j \land i \in L\right)\right)\right)\right) \land \left(\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \cdot X\left(i, j\right) = 0\right) \Rightarrow \left(A \cdot \operatorname{transpose}\left(X\right) - \operatorname{transpose}\left(X\right) \cdot A = 0 \Rightarrow X = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result` (`✓ std3`). ∎

*Resolves.* `Problems/koljancic-oblak-2026-question-5-11-even-loop-path` (proved) by `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"koljancic-oblak-2026-question-5-11-even-loop-path","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

For every positive even order and every nonempty loop set, an exact-support real matrix exists for which entrywise annihilation and the transpose commutator force every real test matrix to vanish. The constructed witnesses are symmetric, but symmetry is a choice in the existential proof and is not an extra condition on the event. Order two, endpoint loops and empty branches are included.

Fix a loop vertex r and let s be the number of vertices on its other side. Then r+s is odd. The existing coprime_positive_branches relation supplies strictly positive squared edge parameters on both branches with coprime continuants. Taking their real square roots gives nonzero real edge weights, and the central loop weight is one. The literal joinedPath matrix has exactly the singleton-loop pattern.

The matrix is a real symmetric Jacobi matrix with all adjacent coefficients nonzero. The original GibbsStochasticSimpleSpectrum.jacobi_simple supplier gives a characteristic polynomial with simple complex roots; the Hermitian spectral theorem supplies a real orthogonal eigenbasis. The roots/eigenvalues correspondence makes its diagonal eigenvalue function injective. This application uses the original Jacobi proof, with its telescope unchanged.

The support tangent has r+s+1 coordinates. Its readout is the diagonal after orthogonal conjugation. If the readout vanishes, the evaluated characteristic derivative vanishes: at a diagonal matrix each determinant row-replacement summand has a zero column. Applying joined_path_charpoly_derivative, polynomial extensionality and joined_variation_injective recovers every tangent coordinate. Equal finite dimensions make the readout surjective.

For an unrestricted commuting X, orthogonal conjugation of its transpose gives a matrix commuting with a diagonal matrix with distinct entries, hence a diagonal matrix Y. Entrywise annihilation gives trace orthogonality against every support tangent. Choose a tangent whose spectral diagonal is diag(Y). The resulting trace equals the sum of squares of the diagonal entries of Y, so Y and X vanish. This proves the singleton-loop witness against the full real commutant.

For enlargement, send A to the linear map X mapped to the pair consisting of its entrywise product with A and the transpose commutator. HasNSSP is exactly injectivity of this map. In finite dimensions the family is continuous and the set of injective continuous linear maps is open. Add the same sufficiently small positive value at all remaining loops in L. The off-diagonal entries and chosen central loop retain their values, the newly required loops are nonzero, and all other diagonal entries are zero. Openness preserves nSSP. Similarity preservation from the published Superpattern Lemma is unnecessary for this existential event.

The source question and published definitions are literature inputs. The continuant construction and its synthesis with the original Jacobi supplier and openness of injectivity are repository derivations. Source and license boundaries are in Library/Eigenstructure/koljancic2026nssp.md. Bounded source qualification does not assert worldwide priority or exhaustive nonresolution.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath](KoljancicOblakEvenPath.md)
- Dependency: [D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum](../../Quantum/Matrix/GibbsStochasticSimpleSpectrum.md)
