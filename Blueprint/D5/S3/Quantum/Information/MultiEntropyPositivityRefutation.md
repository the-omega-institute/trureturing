# Multi-entropy positivity fails on three qutrits

## Abstract

The fourth replica invariant of the antisymmetric three-qutrit state is -35/58773123072, so the replica invariant need not be positive on normalized pure states.

**Definition 1.1 (Replica invariant).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)], \forall L \in \operatorname{Fin}\left(q\right) \to Type,\; [\forall a \in \operatorname{Fin}\left(q\right),\; \operatorname{Fintype}\left(L\left(a\right)\right)], \forall psi \in ((a: \operatorname{Fin}\left(q\right)) \to L\left(a\right)) \to \mathbb{C},\; \operatorname{E}\left(n, q, psi\right) = \sum_{x: (\operatorname{Fin}\left(q - 1\right) \to \operatorname{ZMod}\left(n\right)) \to ((a: \operatorname{Fin}\left(q\right)) \to L\left(a\right))} \prod_{r: \operatorname{Fin}\left(q - 1\right) \to \operatorname{ZMod}\left(n\right)} \operatorname{star}\left(psi\left(x\left(r\right)\right)\right) \cdot psi\left((fun (a: \operatorname{Fin}\left(q\right)) \mapsto x\left(\operatorname{shift}\left(n, q, a, r\right), a\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.E` (`✓ std3`).

*Citation.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

Section 1.2, printed pp. 6–7, equations (1.10)–(1.11): "Consider m = n^{q−1} replicas, arranged as a q−1 dimensional regular hyper-cubical lattice." and "The permutation σ_q is taken to be identity and the rest of the permutations are taken to be the generators of independent Z_n symmetries i.e. σ_a = g_a for a = 1, …, q − 1.". The local basis at party a is L(a). Replicas are functions Fin(q - 1) to ZMod(n); shift is StabilizerMultiEntropyCollapse.shift. With zero-based party labels, shift translates coordinate a when a < q - 1 and leaves the last party fixed. star is complex conjugation. The finite sums and products include every basis assignment and every replica exactly once. Type universes are implicit.

**Definition 1.2 (Normalized pure state).**

$$\forall q \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(q\right) \to Type,\; [\forall a \in \operatorname{Fin}\left(q\right),\; \operatorname{Fintype}\left(L\left(a\right)\right)], \forall psi \in ((a: \operatorname{Fin}\left(q\right)) \to L\left(a\right)) \to \mathbb{C},\; \operatorname{IsUnitState}\left(psi\right) = (\sum_{x: (a: \operatorname{Fin}\left(q\right)) \to L\left(a\right)} \operatorname{Complex.normSq}\left(psi\left(x\right)\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.IsUnitState` (`✓ std3`).

*Citation.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

A normalized pure-state amplitude has sum of squared absolute values one over all joint basis indices. Complex.normSq is the squared absolute value. The local basis at party a is L(a), and each L(a) is finite. Type universes are implicit.

**Definition 1.3 (Positivity question).**

$$claim = (\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)], (2 \le n) \Rightarrow \left((2 \le q) \Rightarrow \left(\forall L \in \operatorname{Fin}\left(q\right) \to Type,\; [\forall a \in \operatorname{Fin}\left(q\right),\; \operatorname{Fintype}\left(L\left(a\right)\right)], \forall psi \in ((a: \operatorname{Fin}\left(q\right)) \to L\left(a\right)) \to \mathbb{C},\; (\operatorname{IsUnitState}\left(psi\right)) \Rightarrow \left((0 < \operatorname{Complex.re}\left(\operatorname{E}\left(n, q, psi\right)\right)) \land (\operatorname{Complex.im}\left(\operatorname{E}\left(n, q, psi\right)\right) = 0)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.claim` (`✓ std3`).

*Citation.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

Section 7, printed p. 32: "The definition (1.11) of S_n requires that the quantity E_n be positive definite. In this paper, we did not prove or even discuss this and phrased the monotonicity conjecture in terms of E_n instead. Although we found that E_n is positive in the examples we studied, it would be nice to prove this in general and to see if there is any relation between the positivity of E_n and the coarse-graining monotonicity." Footnote 2 states: "Note that in defining the Renyi multi-entropy S_n in equation (1.11), we have tacitly assumed that the quantity E_n^(q) is positive." The formula quantifies over n and q at least two, every finite local basis and every complex pure-state amplitude with sum of squared absolute values one. Positive means positive real part and zero imaginary part. The NeZero argument and the family of Fintype arguments are anonymous instance parameters.

**Theorem 1.4 (A negative fourth replica invariant).**

$$\neg (\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)], (2 \le n) \Rightarrow \left((2 \le q) \Rightarrow \left(\forall L \in \operatorname{Fin}\left(q\right) \to Type,\; [\forall a \in \operatorname{Fin}\left(q\right),\; \operatorname{Fintype}\left(L\left(a\right)\right)], \forall psi \in ((a: \operatorname{Fin}\left(q\right)) \to L\left(a\right)) \to \mathbb{C},\; (\operatorname{IsUnitState}\left(psi\right)) \Rightarrow \left((0 < \operatorname{Complex.re}\left(\operatorname{E}\left(n, q, psi\right)\right)) \land (\operatorname{Complex.im}\left(\operatorname{E}\left(n, q, psi\right)\right) = 0)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gadde-jain-krishna-kulkarni-sharma-2023-multi-entropy-positivity` (refuted) by `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gadde-jain-krishna-kulkarni-sharma-2023-multi-entropy-positivity","declaration_gid":"D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

At n = 4 and q = 3 take L(a) = Fin 3 and the totally antisymmetric state with coefficients epsilon(i,j,k)/sqrt(6). The determinant of the matrix whose rows select i, j and k gives epsilon. Its six nonzero coefficients have squared modulus 1/6. Summing the unshifted third party gives the two-party kernel (I - F)/6, where F exchanges the two qutrits. Reindexing the replica lattice turns the contraction into the trace of the fourth power of its row transfer, divided by 6^16. The integer trace is -1680, giving E(4,3,psi) = -35/58773123072. This contradicts the positive-real-part conclusion. The coarse-graining inequalities formulated directly for E retain their separate statements.

## References

- Truth anchor: `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.E`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.IsUnitState`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection](../../Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../Entanglement/AbsoluteSeparability/LowRankRays.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse](../Entanglement/StabilizerMultiEntropyCollapse.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](SeparableStateLocalUnitaryStabilizerObstruction.md)
