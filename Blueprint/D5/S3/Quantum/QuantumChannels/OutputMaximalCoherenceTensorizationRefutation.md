# Entangled inputs violate output maximal coherence tensorization

## Abstract

A qubit Pauli channel has output maximal coherence 3/4, while two copies on a Bell input give maximal coherence 225/272, contradicting Conjecture 1 of Lee, Baek, Park, Kim and Nha.

All matrices use a fixed basis; tensor products use the corresponding product basis. Matrix(b,a,C) denotes complex matrices with rows indexed by b and columns indexed by a. The superscript H denotes conjugate transpose, re denotes real part, and the norm of a complex entry is its modulus. Anonymous bracketed assumptions supply finite enumerations and decidable equality on the indicated index types.

**Definition 1.1 (Maximal coherence in a fixed basis).**

$$\forall (n : Type), ([\operatorname{Fintype}\left(n\right)] \forall (R : \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), (\operatorname{maxCoherence}\left(R\right) = \operatorname{sSup}\left(\operatorname{insert}\left(0, \operatorname{range}\left(\lambda (p : n \times n) \mapsto (\operatorname{if} ((p.1 \ne p.2) \land (0 < (\operatorname{re}\left(R\left(p.1, p.1\right)\right)) \cdot (\operatorname{re}\left(R\left(p.2, p.2\right)\right)))) \operatorname{then} (\frac{\left\lVert R\left(p.1, p.2\right) \right\rVert}{\sqrt{(\operatorname{re}\left(R\left(p.1, p.1\right)\right)) \cdot (\operatorname{re}\left(R\left(p.2, p.2\right)\right))}}) \operatorname{else} (0))\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.maxCoherence` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

Equation (15) compares each off-diagonal modulus with the geometric mean of its diagonal populations. The displayed supremum includes zero and every ordered pair of indices. A pair contributes zero when its indices agree or its diagonal product is not positive. Thus a matrix with no supported off-diagonal pair has value zero, including the one-dimensional case. On a density matrix this is the maximal coherence of Eq. (15), with the zero convention made explicit.

**Definition 1.2 (The action of a finite Kraus family).**

$$\forall (a : Type), (\forall (b : Type), (\forall (k : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(k\right)] \forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), (\forall (R : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (\operatorname{krausApply}\left(K, R\right) = \sum_{(r : k)} (((K\left(r\right)) \cdot (R)) \cdot ((K\left(r\right))^{H})))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.krausApply` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

A finite family K of matrices from a to b acts by the sum of K(r) R K(r)^H. This is MatrixMap.of_kraus K K applied to R, the Kraus representation of the completely positive maps considered in Section IV. No normalization is imposed by the action itself.

**Theorem 1.3 (Kraus actions preserve positivity).**

$$\forall (a : Type), (\forall (b : Type), (\forall (k : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Finite}\left(b\right)] [\operatorname{Fintype}\left(k\right)] \forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), (\forall (R : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), ((\operatorname{PosSemidef}\left(R\right)) \Rightarrow (\operatorname{PosSemidef}\left(\operatorname{krausApply}\left(K, R\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.kraus_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Kraus family sends positive semidefinite input matrices to positive semidefinite output matrices.

**Definition 1.4 (Kraus normalization).**

$$\forall (a : Type), (\forall (b : Type), (\forall (k : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{Fintype}\left(k\right)] \forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), ((\operatorname{IsKrausChannel}\left(K\right)) \Leftrightarrow (\sum_{(r : k)} (((K\left(r\right))^{H}) \cdot (K\left(r\right))) = 1)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.IsKrausChannel` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

The finite Kraus family represents a trace-preserving channel precisely when the sum of K(r)^H K(r) is the identity on a. Together with the Kraus action, this is the finite-dimensional completely positive trace-preserving channel setting of Section IV.

**Definition 1.5 (Output maximal coherence).**

$$\forall (a : Type), (\forall (b : Type), (\forall (k : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{Fintype}\left(k\right)] \forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), (\operatorname{outputMaxCoherence}\left(K\right) = \operatorname{sSup}\left(\{(x : \mathbb{R}) \mid \exists (R : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (((\operatorname{PosSemidef}\left(R\right)) \land (\operatorname{trace}\left(R\right) = 1)) \land (x = \operatorname{maxCoherence}\left(\operatorname{krausApply}\left(K, R\right)\right)))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.outputMaxCoherence` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

Equation (28), specializing the output resource of Eq. (19), optimizes maximal coherence over all density inputs. The maximum is expressed as a real supremum. The density inputs are exactly the positive semidefinite complex matrices of trace one; the displayed set expands this condition. There is no restriction to product inputs when a is itself a product type, so entangled inputs are included. The definition is meaningful for any finite Kraus family, before imposing channel normalization.

**Definition 1.6 (Kraus operators of the product channel).**

$$\forall (a : Type), (\forall (b : Type), (\forall (c : Type), (\forall (d : Type), (\forall (k : Type), (\forall (l : Type), (\forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), (\forall (L : l \to \operatorname{Matrix}\left(d, c, \mathbb{C}\right)), (\operatorname{krausTensor}\left(K, L\right) = (\lambda (p : k \times l) \mapsto \operatorname{kronecker}\left(K\left(p.1\right), L\left(p.2\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.krausTensor` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

A pair of Kraus families gives the family K(r) tensor L(s), indexed by the Cartesian product of their index types. The rows are indexed by b times d and the columns by a times c. These are the Kraus operators of the tensor product channel in Eq. (29). The family itself does not require finiteness or decidable equality assumptions.

**Definition 1.7 (The proposed tensorization equality).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (a : Type), (\forall (b : Type), (\forall (c : Type), (\forall (d : Type), (\forall (k : Type), (\forall (l : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] [\operatorname{Fintype}\left(c\right)] [\operatorname{DecidableEq}\left(c\right)] [\operatorname{Fintype}\left(d\right)] [\operatorname{DecidableEq}\left(d\right)] [\operatorname{Fintype}\left(k\right)] [\operatorname{Fintype}\left(l\right)] \forall (K : k \to \operatorname{Matrix}\left(b, a, \mathbb{C}\right)), (\forall (L : l \to \operatorname{Matrix}\left(d, c, \mathbb{C}\right)), ((\operatorname{IsKrausChannel}\left(K\right)) \Rightarrow ((\operatorname{IsKrausChannel}\left(L\right)) \Rightarrow (\operatorname{outputMaxCoherence}\left(\operatorname{krausTensor}\left(K, L\right)\right) = \operatorname{max}\left(\operatorname{outputMaxCoherence}\left(K\right), \operatorname{outputMaxCoherence}\left(L\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim` (`✓ std3`).

*Citation.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

Conjecture 1, Eq. (29), asserts that for every pair of finite-dimensional Kraus channels the output maximal coherence of their tensor product equals the larger of the two individual values. Input and output dimensions may differ. Every finite index type and every normalized Kraus family is quantified, and the product-channel supremum ranges over all density matrices in the product input space.

**Theorem 1.8 (A Pauli channel and a Bell input contradict the equality).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-baek-park-kim-nha-2022-output-coherence-tensorization-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-baek-park-kim-nha-2022-output-coherence-tensorization-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaehak Lee; Kyunghyun Baek; Jiyong Park; Jaewan Kim; Hyunchul Nha (2022). *Fundamental limits on concentrating and preserving tensorized quantum resources*. DOI: [10.1103/PhysRevResearch.4.043070](https://doi.org/10.1103/PhysRevResearch.4.043070). URL: <https://arxiv.org/abs/2104.12307v2>.

*Commentary.*

Let I = [[1,0],[0,1]], X = [[0,1],[1,0]], Y = [[0,-i],[i,0]] and Z = [[1,0],[0,-1]], where i is the imaginary unit. Take the Pauli channel Phi(A) = (31/40) I A I + (1/10) X A X + (1/10) Y A Y + (1/40) Z A Z. Its Kraus operators are sqrt(31/40) I, sqrt(1/10) X, sqrt(1/10) Y and sqrt(1/40) Z. The four probabilities are nonnegative and sum to one, and each Pauli matrix is a self-adjoint involution, so the Kraus normalization holds.

For a density matrix R = [[a,z],[conj(z),1-a]], the output is [[1/5 + 3a/5,3z/4],[3conj(z)/4,4/5 - 3a/5]]. Its diagonal product is 4/25 + (9/25)a(1-a), exceeding a(1-a) by (4/25)(2a-1)^2. Positivity gives |z|^2 <= a(1-a), hence every such output has maximal coherence at most 3/4. At R = (1/2)[[1,1],[1,1]], the output is [[1/2,3/8],[3/8,1/2]], with maximal coherence 3/4, so the single-channel output supremum equals 3/4. The upper bound suffices for the contradiction.

Use the Bell input (1/2)[[1,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,1]], the density matrix of (|00> + |11>)/sqrt(2). In the ordered product basis (00,01,10,11), applying Phi tensor Phi gives [[17/50,0,0,9/32],[0,4/25,0,0],[0,0,4/25,0],[9/32,0,0,17/50]]. Its only nonzero off-diagonal entries are the two corners, each with normalized modulus (9/32)/(17/50) = 225/272. Thus the product-channel output supremum is at least 225/272, exceeding 3/4 by 21/272. This contradicts Eq. (29) for two copies of the same qubit channel.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.IsKrausChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.krausApply`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.krausTensor`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.kraus_psd`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.maxCoherence`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.outputMaxCoherence`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](../../QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.md)
