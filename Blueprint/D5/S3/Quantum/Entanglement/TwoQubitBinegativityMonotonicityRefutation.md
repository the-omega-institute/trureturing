# Binegativity is not monotone under one-way LOCC

## Abstract

Binegativity increases under a finite one-way LOCC channel on two qubits. Alice applies a local filter and sends its outcome to Bob, who resets to |1> on failure. Forgetting the outcomes gives a deterministic counterexample to the monotonicity conjecture of Girard and Gour.

**Definition 1.1 (Finite one-way LOCC channels).**

$$\forall E : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsOneWayLOCC}\left(E\right)) \Leftrightarrow (\exists n : \mathbb{N}, \exists m : \operatorname{Fin}\left(n\right) \to \mathbb{N}, \exists A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \exists B : (i: \operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(m\left(i\right)\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\sum_{i : \operatorname{Fin}\left(n\right)} \operatorname{conjTranspose}\left(A\left(i\right)\right) \cdot A\left(i\right) = 1) \land ((\forall i : \operatorname{Fin}\left(n\right), \sum_{j : \operatorname{Fin}\left(m\left(i\right)\right)} \operatorname{conjTranspose}\left(B\left(i, j\right)\right) \cdot B\left(i, j\right) = 1) \land (\forall sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), E\left(sigma\right) = \sum_{i : \operatorname{Fin}\left(n\right)} \sum_{j : \operatorname{Fin}\left(m\left(i\right)\right)} \operatorname{kronecker}\left(A\left(i\right), B\left(i, j\right)\right) \cdot sigma \cdot \operatorname{conjTranspose}\left(\operatorname{kronecker}\left(A\left(i\right), B\left(i, j\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.IsOneWayLOCC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alice has n outcomes with Kraus matrices A(i). On receiving outcome i, Bob applies the channel with m(i) Kraus matrices B(i,j). Both completeness equalities are required. The outcomes are forgotten, so E is the double Kraus sum. The tensor product is Matrix.kronecker, and adjoint is conjugate transpose. The finite Kraus representation permits zero Kraus matrices and includes channels with different numbers of Kraus matrices for different Alice outcomes.

**Definition 1.2 (The monotonicity conjecture).**

$$(claim) \Leftrightarrow (\forall sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(sigma\right)) \Rightarrow (\forall E : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsOneWayLOCC}\left(E\right)) \Rightarrow (\operatorname{binegativity}\left(E\left(sigma\right)\right) \le \operatorname{binegativity}\left(sigma\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.claim` (`✓ std3`).

*Citation.* Sk Sazim; Natasha Awasthi (2018). *Binegativity of two qubits under noise*. DOI: [10.1016/j.physleta.2018.04.056](https://doi.org/10.1016/j.physleta.2018.04.056). URL: <https://arxiv.org/abs/1711.03717v2>.

*Commentary.*

Girard and Gour, arXiv:1701.02724v3, p. 1, introduction: "That is, we conjecture that for any two-qubit state σ it holds that N₂(ℰ(σ)) ≤ N₂(σ) for any LOCC (or PPT) channel ℰ that outputs states of two qubits." Sazim and Awasthi, arXiv:1711.03717v2, p. 1, introduction: "On the basis of numerical evidence, it is conjectured that the binegativity behaves monotonically under both LOCC and PPT channels [15]." Their abstract, p. 1, also says: "Our study supports the conjecture that the binegativity is a monotone." The encoding quantifies over matrices on Fin 2 times Fin 2, with IsDensity meaning positive semidefinite and trace one, and over every E satisfying IsOneWayLOCC. This restricted universal assertion is implied by the quoted LOCC assertion. Binegativity is the existing N_2(sigma) = ReTr[(sigma^Gamma)_-] + 2 ReTr[(((sigma^Gamma)_-)^Gamma)_-], with partial transposition on Bob's qubit and Mathlib's negative part. ReTr agrees with trace on these self-adjoint matrices. The output again has two qubits.

**Example 1.3 (The independent restatement).**

$$
claim
$$

*Citation.* Sk Sazim; Natasha Awasthi (2018). *Binegativity of two qubits under noise*. DOI: [10.1016/j.physleta.2018.04.056](https://doi.org/10.1016/j.physleta.2018.04.056). URL: <https://arxiv.org/abs/1711.03717v2>.

*Commentary.*

Sazim and Awasthi, arXiv:1711.03717v2, p. 1: "On the basis of numerical evidence, it is conjectured that the binegativity behaves monotonically under both LOCC and PPT channels [15]." The statement above uses finite one-way LOCC channels, a subclass of LOCC.

**Theorem 1.4 (The conjecture fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

The input in the basis 00,01,10,11 is rho = (3/4)|00><00| + (1/8)(|01>+|10>)(<01|+<10|). Alice uses diag(1/2,1) and (sqrt(3)/2)|0><0|. Bob does nothing on outcome 0 and resets to |1> on outcome 1. The output matrix has entries rho'(00,00)=3/16, rho'(01,01)=11/16, rho'(10,10)=1/8 and rho'(01,10)=rho'(10,01)=1/16, with every other entry zero. Positive semidefinite rank-one decompositions with zero positive-negative product identify both successive negative parts. Their traces give N_2(rho) = -1/4 + 7 sqrt(10)/80 and N_2(rho') = -1/32 + 7 sqrt(13)/416. The rational certificates sqrt(10) < 31623/10000 and sqrt(13) > 36055/10000 show a strict increase. The input is a density matrix and each conditional local Kraus family is complete, so this is a deterministic one-way LOCC counterexample.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.IsOneWayLOCC`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation](TwoQubitBinegativityUpperBoundRefutation.md)
