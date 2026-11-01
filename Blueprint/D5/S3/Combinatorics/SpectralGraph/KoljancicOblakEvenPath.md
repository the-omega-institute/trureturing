# Even double paths with a nonempty loop set

## Abstract

Weighted branch continuants and their first variations for the even double-path nSSP question.

Koljančić and Oblak ask in Question 5.11 of arXiv:2604.21552v1 whether every even double path with at least one loop allows the non-symmetric Strong Spectral Property. Allows means existence of a real matrix with exactly the prescribed nonzero entries. The test matrix in the nSSP definition is an unrestricted real matrix, and the commutator uses its transpose.

The formal claim retains every positive even order and every nonempty loop set. It imposes no symmetry, sign, trace or spectral condition on the existential witness. The source convention on vertices numbered from one corresponds to Fin n by subtracting one.

**Definition 1.1 (Exact double-path pattern).**

$$\forall n \in \operatorname{Nat},\; \forall L \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{pathPattern}\left(L, i, j\right) \Leftrightarrow \left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right) \lor \left(i = j \land i \in L\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.pathPattern` (`✓ std3`).

*Citation.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Both orientations of each consecutive edge occur; the only additional arcs are the specified loops.

**Definition 1.2 (Non-symmetric Strong Spectral Property).**

$$\forall n \in \operatorname{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{HasNSSP}\left(A\right) \Leftrightarrow \left(\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \cdot X\left(i, j\right) = 0\right) \Rightarrow \left(A \cdot \operatorname{transpose}\left(X\right) - \operatorname{transpose}\left(X\right) \cdot A = 0 \Rightarrow X = 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.HasNSSP` (`✓ std3`).

*Citation.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Entrywise annihilation and the transpose commutator must force every real test matrix to vanish.

**Definition 1.3 (Complete Question 5.11 event).**

$$claim \Leftrightarrow \left(\forall n \in \operatorname{Nat},\; 0 < n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \left(\forall L \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Nonempty}\left(L\right) \Rightarrow \left(\exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \ne 0 \Leftrightarrow \operatorname{pathPattern}\left(L, i, j\right)\right) \land \operatorname{HasNSSP}\left(A\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.claim` (`✓ std3`).

*Citation.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

This proposition is the full source question. No theorem in this module currently proves it.

**Definition 1.4 (Zero-diagonal branch continuant).**

$$\forall q \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{continuant}\left(q, 0\right) = 1 \land \left(\operatorname{continuant}\left(q, 1\right) = X \land \left(\forall k \in \operatorname{Nat},\; \operatorname{continuant}\left(q, k + 2\right) = X \cdot \operatorname{continuant}\left(q, k + 1\right) - \operatorname{C}\left(q\left(k\right)\right) \cdot \operatorname{continuant}\left(q, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The empty branch has polynomial one and a one-vertex branch has polynomial X. Each successor step uses the squared weight of the newly attached edge.

**Definition 1.5 (Edge-parameter first variation).**

$$\forall q \in \operatorname{Nat} \to \operatorname{Real},\; \forall dq \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{variation}\left(q, dq, 0\right) = 0 \land \left(\operatorname{variation}\left(q, dq, 1\right) = 0 \land \left(\forall k \in \operatorname{Nat},\; \operatorname{variation}\left(q, dq, k + 2\right) = X \cdot \operatorname{variation}\left(q, dq, k + 1\right) - \operatorname{C}\left(dq\left(k\right)\right) \cdot \operatorname{continuant}\left(q, k\right) - \operatorname{C}\left(q\left(k\right)\right) \cdot \operatorname{variation}\left(q, dq, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.variation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The formal linearized recurrence includes the variation of the edge parameter and the variation of the preceding continuant. A connection to the actual characteristic-coefficient differential remains to be proved.

**Definition 1.6 (Simultaneous polynomial edge perturbation).**

$$\forall q \in \operatorname{Nat} \to \operatorname{Real},\; \forall dq \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{deformedContinuant}\left(q, dq, 0\right) = 1 \land \left(\operatorname{deformedContinuant}\left(q, dq, 1\right) = \operatorname{C}\left(X\right) \land \left(\forall k \in \operatorname{Nat},\; \operatorname{deformedContinuant}\left(q, dq, k + 2\right) = \operatorname{C}\left(X\right) \cdot \operatorname{deformedContinuant}\left(q, dq, k + 1\right) - \left(\operatorname{C}\left(\operatorname{C}\left(q\left(k\right)\right)\right) + \operatorname{C}\left(\operatorname{C}\left(dq\left(k\right)\right)\right) \cdot z\right) \cdot \operatorname{deformedContinuant}\left(q, dq, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.deformedContinuant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Each squared edge parameter is replaced by q plus z times dq. The outer polynomial variable is z; coefficients are polynomials in the spectral variable X. In its defining formula, z denotes the outer Polynomial.X and C embeds into the applicable polynomial ring.

**Theorem 1.7 (Exact constant and first-order terms).**

$$\forall q \in \operatorname{Nat} \to \operatorname{Real},\; \forall dq \in \operatorname{Nat} \to \operatorname{Real},\; \forall n \in \operatorname{Nat},\; \operatorname{coeff}\left(\operatorname{deformedContinuant}\left(q, dq, n\right), 0\right) = \operatorname{continuant}\left(q, n\right) \land \operatorname{coeff}\left(\operatorname{deformedContinuant}\left(q, dq, n\right), 1\right) = \operatorname{variation}\left(q, dq, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant_linearization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The constant term of the deformation is the continuant and its coefficient of z is exactly variation. The induction uses the complete coefficient-one product rule, with both cross terms. This is algebraic first-order evidence for all lengths and all real parameter and variation sequences; it is not a claim that the complete central-vertex coefficient map is already injective.

**Theorem 1.8 (Reverse recovery of every edge variation).**

$$\forall q \in \operatorname{Nat} \to \operatorname{Real},\; \forall dq \in \operatorname{Nat} \to \operatorname{Real},\; \forall n \in \operatorname{Nat},\; \left(\forall k \in \operatorname{Nat},\; k < n \Rightarrow q\left(k\right) \ne 0\right) \Rightarrow \left(\operatorname{variation}\left(q, dq, n\right) = 0 \Rightarrow \left(\operatorname{variation}\left(q, dq, n + 1\right) = 0 \Rightarrow \left(\forall k \in \operatorname{Nat},\; k < n \Rightarrow dq\left(k\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.branch_variation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

At a nonzero edge-parameter sequence, two consecutive zero polynomial variations force every earlier edge variation to vanish. The leading coefficient of each continuant is one, while its variation has strictly smaller degree. Taking that coefficient in the linearized recurrence first recovers the last edge variation; cancellation and induction recover the remaining edges. Length-zero and length-one branches are included without extra parameters.

**Definition 1.9 (Actual zero-diagonal weighted branch).**

$$\forall b \in \operatorname{Nat} \to \operatorname{Real},\; \forall n \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{weightedPath}\left(b, n\right)\left(i, j\right) = \operatorname{if} (\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right)) \operatorname{then} b\left(n - 2 - \operatorname{val}\left(i\right)\right) \operatorname{else} \operatorname{if} (\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right)) \operatorname{then} b\left(n - 2 - \operatorname{val}\left(j\right)\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weightedPath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The two orientations of each edge carry the same real weight. Vertex reversal aligns the first-row determinant expansion with the last edge in the recurrence. The constructor permits zero weights as well. Subtraction in its natural-number edge index is truncated subtraction.

**Theorem 1.10 (Weighted branch characteristic correspondence).**

$$\forall b \in \operatorname{Nat} \to \operatorname{Real},\; \forall n \in \operatorname{Nat},\; \operatorname{charpoly}\left(\operatorname{weightedPath}\left(b, n\right)\right) = \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto b\left(k\right)^{2}, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weighted_path_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The actual characteristic polynomial of the weighted branch equals the continuant with squared edge parameters, in every order including zero and one. First-row expansion uses the existing det_sparse_front supplier in ForbiddenNeighbourDeterminant; both remaining principal submatrices have the same reversed-edge convention.

The remaining whole-event bridges are the central-loop characteristic identity joining two weighted branches; a coprime choice for opposite-parity branches; separation of the complete central-vertex variation, retaining all product-rule cross terms; the coefficient/adjugate trace pairing and unrestricted real commutant argument; and exact support enlargement to every nonempty loop set. The source Superpattern Lemma also preserves similarity, which is stronger than the existential event requires.

Source attribution and license boundaries are recorded in Library/Eigenstructure/koljancic2026nssp.md. The continuant variation argument is a repository derivation; the source question and its published definitions are not claimed as new results.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.HasNSSP`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.branch_variation_injective`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant_linearization`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.deformedContinuant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.pathPattern`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.variation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weightedPath`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weighted_path_charpoly`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
