# Rank-One Born Pairing Weight

## Abstract

A rank-one Born weight is a trace pairing, and unread measurement is its conditional ensemble.

**Theorem 1.1 (Rank-one Born weight, trace pairing, and unread ensemble).**

$$\forall n, K, \operatorname{Fintype}\left(n\right), \operatorname{Fintype}\left(K\right),\\{}\forall P: K \to M_{n}(\mathbb{C}), rho\in M_{n}(\mathbb{C}), k\in K, phi, psi\in \mathbb{C}^{n},\\{}\operatorname{Record}\left(P\right) \land \operatorname{PosSemidef}\left(rho\right) \land \operatorname{tr}\left(rho\right) = 1 \land\\P_{k} = phi phi^{*} \land rho = psi psi^{*} \Rightarrow\\(\operatorname{recordWeight}\left(P, rho, k\right) = \lvert\langle phi, psi \rangle\rvert^{2} \land \operatorname{recordWeight}\left(P, rho, k\right) = \operatorname{tr}\left(rho P_{k}\right) \land\\\operatorname{unreadState}\left(P, rho\right) = \sum_{j \in K}\operatorname{recordWeight}\left(P, rho, j\right)\cdot \operatorname{conditionalState}\left(P, rho, j\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/RankOneBornPairingWeight.rank_one_born_pairing_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite complete family of pairwise orthogonal, self-adjoint idempotent complex projections, and let rho be a positive trace-one matrix. Fix a branch k and rank-one representations P_k = phi phi* and rho = psi psi*.

Write p_k for the canonical recordWeight. The three conclusions are p_k = |<phi, psi>|^2, p_k = trace(rho P_k), and unreadState P rho = sum_j p_j conditionalState(P, rho, j). The second equality carries the source's object-role assertion: p_k has scalar trace-pairing type, not projection-matrix or quotient-object type.

The first and third leaves directly apply the frozen rank-one reduction and unread weighted-ensemble theorems. The middle leaf unfolds only the canonical recordWeight and bornProbability definitions.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/RankOneBornPairingWeight.rank_one_born_pairing_weight`
- Dependency: [D5/S3/Observer/BornReduction](../BornReduction.md)
