# The operational error-state erasure conjecture is false

## Abstract

A rational qubit ensemble prevents exact error erasure while preserving both correct states.

The classical fair public bit is part of both the input and output of a single completely positive trace-preserving channel. The channel may act coherently on the entire joint system. DensityState and QuantumChannel refer to FiniteStateChannel.

**Definition 1.1 (The conditional state with its public bit).**

$$\forall d \in \mathbb{N}, sigma \in Bool \to \left(Bool \to \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right)\right),\; \forall a \in Bool, b \in Bool, i \in \operatorname{Fin}\left(d\right) \times Bool, j \in \operatorname{Fin}\left(d\right) \times Bool,\; \operatorname{rhoET}\left(sigma, a, b\right)\left(i, j\right) = \text{if} (i.2 = j.2) \text{then} ((\frac{1}{2}:\mathbb{C}) \cdot (\text{if} (i.2) \text{then} (\operatorname{val}\left(sigma\left(\operatorname{Bool.not}\left(a\right), \operatorname{Bool.not}\left(b\right)\right)\right)\left(i.1, j.1\right)) \text{else} (\operatorname{val}\left(sigma\left(a, b\right)\right)\left(i.1, j.1\right)))) \text{else} (0)$$

*Formalization.* `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.rhoET` (`✓ std3`).

*Citation.* Mikka Stasiuk, Norbert Lütkenhaus and Ernest Y.-Z. Tan (2025). *Quantum Chernoff divergence in advantage distillation for quantum key distribution and device-independent quantum key distribution*. DOI: [10.1103/PhysRevA.111.022631](https://doi.org/10.1103/PhysRevA.111.022631). URL: <https://arxiv.org/abs/2212.06975v3>.

*Commentary.*

Equation (6), p. 2, defines the conditional ET state by the sum of the two orthogonal flag blocks with equal weights.

The Bool values false and true represent 0 and 1; Bool.not complements a bit. Row i and column j have Eve coordinate in their first component and public-bit coordinate in their second. Each flag block has weight one half; the second block complements both outcome bits. The displayed equality specifies every matrix entry.

**Definition 1.2 (One channel with three simultaneous requirements).**

$$\forall d \in \mathbb{N}, sigma \in Bool \to \left(Bool \to \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right)\right),\; \forall channel \in \operatorname{QuantumChannel}\left((\operatorname{Fin}\left(d\right) \times Bool), (\operatorname{Fin}\left(d\right) \times Bool)\right),\; \operatorname{ErasesErrorsPreservingCorrect}\left(sigma, channel\right) \Leftrightarrow \left(\operatorname{toCompletelyPositiveMap}\left(channel\right)\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, false, false\right)\right)\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, false, false\right)\right) \land \left(\operatorname{toCompletelyPositiveMap}\left(channel\right)\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, true, true\right)\right)\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, true, true\right)\right) \land \operatorname{toCompletelyPositiveMap}\left(channel\right)\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, false, true\right)\right)\right) = \operatorname{toCompletelyPositiveMap}\left(channel\right)\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{rhoET}\left(sigma, true, false\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.ErasesErrorsPreservingCorrect` (`✓ std3`).

*Citation.* Mikka Stasiuk, Norbert Lütkenhaus and Ernest Y.-Z. Tan (2025). *Quantum Chernoff divergence in advantage distillation for quantum key distribution and device-independent quantum key distribution*. DOI: [10.1103/PhysRevA.111.022631](https://doi.org/10.1103/PhysRevA.111.022631). URL: <https://arxiv.org/abs/2212.06975v3>.

*Commentary.*

We remark that it does seem plausible to conjecture that Eve can indeed always perform an operation on her side-information such that this condition is fulfilled (while keeping the states $\rho_{ET\Vert00},\rho_{ET\Vert11}$ unchanged), because it essentially corresponds to having Eve “erase” her side-information whenever Alice and Bob did not get the same output value. (Section III A, p. 5, immediately after Theorem 2.)

This predicate requires the channel to preserve the 00 and 11 matrices separately and to send the 01 and 10 matrices to the same output. It imposes all three equalities on one channel.

**Definition 1.3 (The universal operational assertion).**

$$claim \Leftrightarrow \left(\forall d \in \mathbb{N}, sigma \in Bool \to \left(Bool \to \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right)\right),\; \exists channel \in \operatorname{QuantumChannel}\left((\operatorname{Fin}\left(d\right) \times Bool), (\operatorname{Fin}\left(d\right) \times Bool)\right),\; \operatorname{ErasesErrorsPreservingCorrect}\left(sigma, channel\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.claim` (`✓ std3`).

*Citation.* Mikka Stasiuk, Norbert Lütkenhaus and Ernest Y.-Z. Tan (2025). *Quantum Chernoff divergence in advantage distillation for quantum key distribution and device-independent quantum key distribution*. DOI: [10.1103/PhysRevA.111.022631](https://doi.org/10.1103/PhysRevA.111.022631). URL: <https://arxiv.org/abs/2212.06975v3>.

*Commentary.*

We remark that it does seem plausible to conjecture that Eve can indeed always perform an operation on her side-information such that this condition is fulfilled (while keeping the states $\rho_{ET\Vert00},\rho_{ET\Vert11}$ unchanged), because it essentially corresponds to having Eve “erase” her side-information whenever Alice and Bob did not get the same output value. (Section III A, p. 5, immediately after Theorem 2.)

The dimension d ranges over all natural numbers, and sigma ranges over four normalized conditional density states. The same output dimension and the full public Bool register are retained. The assertion concerns a local operation on the given side-information; replacing the underlying attack is a separate question.

**Theorem 1.4 (A two-dimensional counterexample).**

$$\neg (\forall d \in \mathbb{N}, sigma \in Bool \to \left(Bool \to \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right)\right),\; \exists channel \in \operatorname{QuantumChannel}\left((\operatorname{Fin}\left(d\right) \times Bool), (\operatorname{Fin}\left(d\right) \times Bool)\right),\; \operatorname{ErasesErrorsPreservingCorrect}\left(sigma, channel\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikka Stasiuk, Norbert Lütkenhaus and Ernest Y.-Z. Tan (2025). *Quantum Chernoff divergence in advantage distillation for quantum key distribution and device-independent quantum key distribution*. DOI: [10.1103/PhysRevA.111.022631](https://doi.org/10.1103/PhysRevA.111.022631). URL: <https://arxiv.org/abs/2212.06975v3>.

*Commentary.*

Use rank-one projectors of (1,0), (9999/10001,200/10001), (29197/50005,40596/50005), and (3/5,4/5), in 00,01,10,11 order. Their public-bit extensions are positive matrices of trace one. The correct-state trace distance is 4/5, and each same-Alice-bit correct-to-error distance is 200/10001.

For every joint channel, trace-distance contraction on the two short legs and the triangle inequality force the sum of the two correct-state disturbances and the residual error-output distance to be at least 38004/50005. Exact preservation and exact erasure would make all three terms zero.

If the error outputs coincide, the two correct-state disturbances must sum to at least 38004/50005. Theorem 2, which assumes equal error states, is not refuted. A weaker replacement-attack assertion and positive asymptotic key rates remain separate questions.

The physical preparation has balanced positive key-event probabilities, distinct flagged states, CHSH violation and Q=9/25<9/16. These physical and Chernoff calculations are additional to the matrix-state refutation.

Bhavsar, Moon and Bae, arXiv:2602.05870v2, address neighbouring asymptotic key-rate conditions. Finite-blocklength security, the replacement-realization question, optimality of the disturbance constant and positive erasure with an orthogonal correct/error record remain open here.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.ErasesErrorsPreservingCorrect`
- Truth anchor: `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.result`
- Truth anchor: `D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.rhoET`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](FiniteTraceDistance.md)
