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

This proposition is the full source question. The companion KoljancicOblakEvenPathNSSP.result proves it with exactly these quantifiers.

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

The formal linearized recurrence includes the variation of the edge parameter and the variation of the preceding continuant. The actual evaluated characteristic differential is supplied by joined_path_charpoly_derivative.

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

**Definition 1.11 (Complete central-loop variation).**

$$\forall qL \in \operatorname{Nat} \to \operatorname{Real},\; \forall qR \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqL \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall da \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \operatorname{joinedVariation}\left(qL, qR, dqL, dqR, a, da, r, s\right) = 0 - \operatorname{C}\left(da\right) \cdot \operatorname{continuant}\left(qL, r\right) \cdot \operatorname{continuant}\left(qR, s\right) + \left(X - \operatorname{C}\left(a\right)\right) \cdot \left(\operatorname{variation}\left(qL, dqL, r\right) \cdot \operatorname{continuant}\left(qR, s\right) + \operatorname{continuant}\left(qL, r\right) \cdot \operatorname{variation}\left(qR, dqR, s\right)\right) - \left(X \cdot \operatorname{variation}\left(qL, dqL, r\right) - \operatorname{variation}\left(qL, dqL, r + 1\right)\right) \cdot \operatorname{continuant}\left(qR, s\right) - \left(X \cdot \operatorname{continuant}\left(qL, r\right) - \operatorname{continuant}\left(qL, r + 1\right)\right) \cdot \operatorname{variation}\left(qR, dqR, s\right) - \operatorname{variation}\left(qL, dqL, r\right) \cdot \left(X \cdot \operatorname{continuant}\left(qR, s\right) - \operatorname{continuant}\left(qR, s + 1\right)\right) - \operatorname{continuant}\left(qL, r\right) \cdot \left(X \cdot \operatorname{variation}\left(qR, dqR, s\right) - \operatorname{variation}\left(qR, dqR, s + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joinedVariation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Write U=P_left(r), V=P_right(s), F=XU-P_left(r+1), and G=XV-P_right(s+1). The displayed expression retains all six contributions to the variation of (X-a)UV-FV-UG. Each flux is zero when its branch is empty; for a positive branch length its flux is the attaching squared edge weight times the preceding continuant. The joined_path_charpoly theorem supplies the corresponding actual central-loop matrix characteristic expression; the matrix support-tangent bridge is separate.

**Definition 1.12 (Actual simultaneous algebraic perturbation).**

$$\forall qL \in \operatorname{Nat} \to \operatorname{Real},\; \forall qR \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqL \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall da \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \operatorname{deformedJoinedContinuant}\left(qL, qR, dqL, dqR, a, da, r, s\right) = \left(\operatorname{C}\left(X\right) - \left(\operatorname{C}\left(\operatorname{C}\left(a\right)\right) + \operatorname{C}\left(\operatorname{C}\left(da\right)\right) \cdot z\right)\right) \cdot \operatorname{deformedContinuant}\left(qL, dqL, r\right) \cdot \operatorname{deformedContinuant}\left(qR, dqR, s\right) - \left(\operatorname{C}\left(X\right) \cdot \operatorname{deformedContinuant}\left(qL, dqL, r\right) - \operatorname{deformedContinuant}\left(qL, dqL, r + 1\right)\right) \cdot \operatorname{deformedContinuant}\left(qR, dqR, s\right) - \operatorname{deformedContinuant}\left(qL, dqL, r\right) \cdot \left(\operatorname{C}\left(X\right) \cdot \operatorname{deformedContinuant}\left(qR, dqR, s\right) - \operatorname{deformedContinuant}\left(qR, dqR, s + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.deformedJoinedContinuant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Replace the central loop by a plus z times da and each branch squared edge parameter by q plus z times dq in the joined expression. The outer polynomial variable is z and the inner variable X is spectral. In the formula C embeds into the applicable coefficient ring. The complete coefficient-one product rule identifies this perturbation coefficient with joinedVariation; that identity is consumed in the recovery theorem.

**Theorem 1.13 (Separation of central and branch variations).**

$$\forall qL \in \operatorname{Nat} \to \operatorname{Real},\; \forall qR \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqL \in \operatorname{Nat} \to \operatorname{Real},\; \forall dqR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall da \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; a \ne 0 \Rightarrow \left(\operatorname{Odd}\left(r + s\right) \Rightarrow \left(\left(\forall k \in \operatorname{Nat},\; k < r \Rightarrow qL\left(k\right) \ne 0\right) \Rightarrow \left(\left(\forall k \in \operatorname{Nat},\; k < s \Rightarrow qR\left(k\right) \ne 0\right) \Rightarrow \left(\operatorname{IsCoprime}\left(\operatorname{continuant}\left(qL, r\right), \operatorname{continuant}\left(qR, s\right)\right) \Rightarrow \left(\operatorname{coeff}\left(\operatorname{deformedJoinedContinuant}\left(qL, qR, dqL, dqR, a, da, r, s\right), 1\right) = 0 \Rightarrow \left(da = 0 \land \left(\left(\forall k \in \operatorname{Nat},\; k < r \Rightarrow dqL\left(k\right) = 0\right) \land \left(\forall k \in \operatorname{Nat},\; k < s \Rightarrow dqR\left(k\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_variation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

For every pair of branch lengths with odd sum, nonzero central loop and nonzero branch edge parameters, coprime branch continuants make the coefficient of z in the actual algebraic joined perturbation injective. The recovered edge indices below each branch length include its attaching edge. No lower bound on either individual branch length is imposed. The complete product rule first identifies that coefficient with joinedVariation. Reflection X to -X then separates the odd part C(a) times the product variation plus C(da)UV. Its leading coefficient recovers da, after which coprimality and strict degree bounds separate both branch variations. Applying the same separation to the remaining adjacent continuants and using branch_variation_injective recovers all edge parameters. This theorem assumes coprimality; it does not construct the required branches or prove the complete nSSP claim.

**Theorem 1.14 (Uniform positive coprime branch construction).**

$$\forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \operatorname{Odd}\left(r + s\right) \Rightarrow \left(\exists qL \in \operatorname{Nat} \to \operatorname{Real},\; \exists qR \in \operatorname{Nat} \to \operatorname{Real},\; \left(\forall k \in \operatorname{Nat},\; 0 < qL\left(k\right)\right) \land \left(\left(\forall k \in \operatorname{Nat},\; 0 < qR\left(k\right)\right) \land \operatorname{IsCoprime}\left(\operatorname{continuant}\left(qL, r\right), \operatorname{continuant}\left(qR, s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.coprime_positive_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Every pair of lengths with odd sum admits two strictly positive squared-edge parameter sequences whose continuants are coprime. Put unit parameters on an even-length branch and a common positive parameter t on the other branch. The first branch has nonzero constant coefficient. The spectral resultant is a polynomial in t; at t=0 the other branch becomes X to its length, so the resultant is nonzero. A positive t outside its finite root set gives the required pair. Swapping the branches covers the other parity orientation. Zero and one lengths need no exceptions, and the final selected t is strictly positive; zero is used only to prove that the parameter polynomial is not identically zero.

**Definition 1.15 (Actual path with one central loop).**

$$\forall bL \in \operatorname{Nat} \to \operatorname{Real},\; \forall bR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(s + 1 + r\right),\; \forall j \in \operatorname{Fin}\left(s + 1 + r\right),\; \operatorname{joinedPath}\left(bL, bR, a, r, s\right)\left(i, j\right) = \operatorname{if} (i = j) \operatorname{then} \operatorname{if} (\operatorname{val}\left(i\right) = r) \operatorname{then} a \operatorname{else} 0 \operatorname{else} \operatorname{if} (\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right)) \operatorname{then} \operatorname{if} (\operatorname{val}\left(i\right) < r) \operatorname{then} bL\left(\operatorname{val}\left(i\right)\right) \operatorname{else} bR\left(s + r - 1 - \operatorname{val}\left(i\right)\right) \operatorname{else} \operatorname{if} (\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right)) \operatorname{then} \operatorname{if} (\operatorname{val}\left(j\right) < r) \operatorname{then} bL\left(\operatorname{val}\left(j\right)\right) \operatorname{else} bR\left(s + r - 1 - \operatorname{val}\left(j\right)\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joinedPath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The vertex set is Fin(s+1+r), with the loop at vertex r. The left branch edges have weights bL(0) through bL(r-1) from its far endpoint towards the loop; the right branch edges have weights bR(s-1) down to bR(0) from the loop towards its far endpoint. All diagonal entries except the central loop are zero. Natural-number subtraction in the displayed edge indices is truncated subtraction. Empty branches, either endpoint and the single-vertex carrier are included.

**Theorem 1.16 (Actual central-loop characteristic identity).**

$$\forall bL \in \operatorname{Nat} \to \operatorname{Real},\; \forall bR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \operatorname{charpoly}\left(\operatorname{joinedPath}\left(bL, bR, a, r, s\right)\right) = \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right)^{2}, r + 1\right) \cdot \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bR\left(k\right)^{2}, s\right) + \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right)^{2}, r\right) \cdot \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bR\left(k\right)^{2}, s + 1\right) - \left(X + \operatorname{C}\left(a\right)\right) \cdot \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right)^{2}, r\right) \cdot \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bR\left(k\right)^{2}, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_path_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

For every pair of real edge sequences, every real loop weight and every pair of natural branch lengths, the characteristic polynomial of joinedPath equals the displayed branch-continuant expression. This is also (X-C(a))UV-FV-UG with U=P_left(r), V=P_right(s), F=XU-P_left(r+1) and G=XV-P_right(s+1). The proof uses the actual matrix determinant, the frozen sparse determinant expansion, the existing weighted_path_charpoly, and induction from either empty or one-vertex left branches. The front recurrence for continuants aligns the far-end deletion with the squared edge indexing. The formula assumes neither nonzero weights nor parity, and includes every endpoint and empty branch. It does not establish the support-tangent or unrestricted commutant bridges.

**Theorem 1.17 (Actual characteristic variation along edge and loop perturbations).**

$$\forall bL \in \operatorname{Nat} \to \operatorname{Real},\; \forall bR \in \operatorname{Nat} \to \operatorname{Real},\; \forall dbL \in \operatorname{Nat} \to \operatorname{Real},\; \forall dbR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall da \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; \forall x \in \operatorname{Real},\; \operatorname{HasDerivAt}\left(\lambda t: \operatorname{Real} \mapsto \operatorname{eval}\left(x, \operatorname{charpoly}\left(\operatorname{joinedPath}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right) + t \cdot dbL\left(k\right), \lambda k: \operatorname{Nat} \mapsto bR\left(k\right) + t \cdot dbR\left(k\right), a + t \cdot da, r, s\right)\right)\right), \operatorname{eval}\left(x, \operatorname{joinedVariation}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right)^{2}, \lambda k: \operatorname{Nat} \mapsto bR\left(k\right)^{2}, \lambda k: \operatorname{Nat} \mapsto 2 \cdot bL\left(k\right) \cdot dbL\left(k\right), \lambda k: \operatorname{Nat} \mapsto 2 \cdot bR\left(k\right) \cdot dbR\left(k\right), a, da, r, s\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_path_charpoly_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić and Polona Oblak (2026). *Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs*. DOI: [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

For every real edge and variation sequence, every loop weight and variation, every pair of natural branch lengths and every real spectral value x, the actual characteristic polynomial evaluated at x has the displayed derivative at perturbation parameter zero. Each edge is perturbed by b+t*db and the central loop by a+t*da. The squared-edge first variations are 2*b*db, with the complete joined product rule retained. The proof differentiates the continuant recurrence and applies joined_path_charpoly to the actual perturbed matrix. Zero edge weights, empty branches and endpoints remain included. The conditional application below uses these evaluated derivatives directly, together with an orthogonal diagonalization having distinct eigenvalues. It does not require a separate characteristic-coefficient or adjugate interface. The companion KoljancicOblakEvenPathNSSP.result supplies that diagonalization for the selected branch weights and constructs the final exact-support witnesses.

Conditional unrestricted commutant application. Let the two branch lengths have odd sum, let the loop and all r+s used edge weights be nonzero, and let the two squared-weight continuants be coprime. Suppose U is real orthogonal and U-transpose A U is diagonal with pairwise distinct diagonal entries, where A is the actual joinedPath. Under these explicit hypotheses the existing matrix derivative and recovery relations imply HasNSSP A. This conditional application supplies no existence assertion for U, the branch weights or the final exact-support witness.

$$
\forall bL \in \operatorname{Nat} \to \operatorname{Real},\; \forall bR \in \operatorname{Nat} \to \operatorname{Real},\; \forall a \in \operatorname{Real},\; \forall r \in \operatorname{Nat},\; \forall s \in \operatorname{Nat},\; a \ne 0 \Rightarrow \left(\operatorname{Odd}\left(r + s\right) \Rightarrow \left(\left(\forall k \in \operatorname{Nat},\; k < r \Rightarrow bL\left(k\right) \ne 0\right) \Rightarrow \left(\left(\forall k \in \operatorname{Nat},\; k < s \Rightarrow bR\left(k\right) \ne 0\right) \Rightarrow \left(\operatorname{IsCoprime}\left(\operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bL\left(k\right)^{2}, r\right), \operatorname{continuant}\left(\lambda k: \operatorname{Nat} \mapsto bR\left(k\right)^{2}, s\right)\right) \Rightarrow \left(\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(s + 1 + r\right), \operatorname{Fin}\left(s + 1 + r\right), \operatorname{Real}\right),\; \forall lam \in \operatorname{Fin}\left(s + 1 + r\right) \to \operatorname{Real},\; \operatorname{transpose}\left(U\right) \cdot U = 1 \Rightarrow \left(U \cdot \operatorname{transpose}\left(U\right) = 1 \Rightarrow \left(\operatorname{transpose}\left(U\right) \cdot \operatorname{joinedPath}\left(bL, bR, a, r, s\right) \cdot U = \operatorname{diagonal}\left(lam\right) \Rightarrow \left(\operatorname{Injective}\left(lam\right) \Rightarrow \operatorname{HasNSSP}\left(\operatorname{joinedPath}\left(bL, bR, a, r, s\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)
$$

Put n=r+s+1. Parameterize a symmetric support tangent T(v) by its r left edges, one central loop and s right edges, so v lies in Real to the n. Its spectral diagonal readout is v mapped to diag(U-transpose T(v) U). If this readout vanishes, the derivative of every evaluated characteristic polynomial vanishes: the determinant differential at a diagonal matrix is a sum of determinants with one row replaced, and the zero diagonal of the direction leaves a zero column in each summand. Orthogonal conjugation preserves the characteristic polynomial. Applying joined_path_charpoly_derivative and polynomial extensionality therefore gives zero joinedVariation. The complete joined recovery theorem, with squared-edge variations 2*b*db, recovers every edge and loop direction. The readout is injective and hence surjective between two real spaces of dimension n.

Now take an arbitrary real X satisfying entrywise A times X equal to zero and A X-transpose equal to X-transpose A. The matrix Y=U-transpose X-transpose U commutes with the diagonal spectral matrix. Distinct spectral entries force every off-diagonal entry of Y to vanish; symmetry of X is a consequence here and is never assumed. Entrywise annihilation gives trace(X-transpose T(v))=0 for every support tangent. Choose v whose spectral diagonal readout equals diag(Y). Invariance of trace under the orthogonal change of basis identifies that trace with the sum of the squares of the diagonal entries of Y. Thus Y=0 and X=0. This argument tests the full unrestricted real commutant.

The companion KoljancicOblakEvenPathNSSP.result consumes these relations in a proof of the full claim. It applies the original Jacobi simple-spectrum supplier, takes square roots of the positive branch parameters, proves singleton-loop exact support and enlarges to every nonempty loop set using openness of the injective nSSP test map. Empty branches, endpoints and order two are included. The source Superpattern Lemma also preserves similarity, which is stronger than this existential event requires.

Source attribution and license boundaries are recorded in Library/Eigenstructure/koljancic2026nssp.md. The continuant variation argument is a repository derivation; the source question and its published definitions are not claimed as new results.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.HasNSSP`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.branch_variation_injective`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.continuant_linearization`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.coprime_positive_branches`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.deformedContinuant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.deformedJoinedContinuant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joinedPath`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joinedVariation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_path_charpoly`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_path_charpoly_derivative`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.joined_variation_injective`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.pathPattern`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.variation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weightedPath`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.weighted_path_charpoly`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
