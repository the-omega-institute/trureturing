# Rank-One Born Pairing Weight

## Abstract

A rank-one branch weight is a nonnegative state-projection pairing equal to a squared transition modulus.

**Theorem 1.1 (Rank-one Born weight is a nonnegative pairing scalar).**

$$\forall n, K, \operatorname{Fintype}\left(n\right), \operatorname{Fintype}\left(K\right),\\{}\forall P: K \to M_{n}(\mathbb{C}), rho\in M_{n}(\mathbb{C}), k\in K, phi, psi\in \mathbb{C}^{n},\\{}\operatorname{Record}\left(P\right) \land \operatorname{PosSemidef}\left(rho\right) \land \operatorname{tr}\left(rho\right) = 1 \land\\P_{k} = phi phi^{*} \land rho = psi psi^{*} \Rightarrow\\(\operatorname{tr}\left(rho P_{k}\right) = \lvert\langle phi, psi \rangle\rvert^{2} \land 0 \leq \operatorname{tr}\left(rho P_{k}\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/RankOneBornPairingWeight.rank_one_born_pairing_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite complete family of pairwise orthogonal, self-adjoint idempotent complex projections, and let rho be a positive trace-one matrix. Fix a branch k and rank-one representations P_k = phi phi* and rho = psi psi*.

Write p_k for the canonical recordWeight, definitionally the complex scalar trace(rho P_k). The first conclusion is exactly p_k = |<phi, psi>|^2. The second conclusion is 0 <= p_k, so the formal carrier is a nonnegative state-projection pairing scalar, not a projection matrix or a quotient object.

The equality directly applies the frozen rank-one reduction. Nonnegativity directly applies the canonical Born probability skeleton to the positive trace-one state and the selected record projection.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/RankOneBornPairingWeight.rank_one_born_pairing_weight`
- Dependency: [D5/S3/Observer/BornReduction](../BornReduction.md)
