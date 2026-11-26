# Conditional trace-distance expansion and the reverse Doeblin coefficient

## Abstract

Qubit half-depolarization violates the proposed conditional expansion bound.

**Definition 1.1 (The proposed conditional expansion bound).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.claim`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.claim` (`✓ std3`).

*Citation.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Equation (2.42) takes the infimum, over finite references and density pairs with positive denominator, of the joint output trace distance minus the reference distance divided by the joint input trace distance minus the reference distance. The paragraph after Proposition 9 asks whether the reverse Doeblin bound applies to that infimum. By Equations (6.54) and (6.55) and Proposition 33 of George et al., the pointwise bound would require every such ratio to be at least one minus p whenever a channel postprocesses N to Z ↦ (1 − p)Z + p Tr(Z)X, with X Hermitian and p in the unit interval.

**Theorem 1.2 (A vanishing conditional ratio for qubit half-depolarization).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Acknowledgement.* Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde (2026). *Quantum Doeblin Coefficients: Interpretations and Applications*. DOI: [10.22331/q-2026-05-22-2115](https://doi.org/10.22331/q-2026-05-22-2115). URL: <https://arxiv.org/html/2503.22823v3>.

*Commentary.*

Take N to be the qubit half-depolarizing channel and postprocess by the identity, so p = 1/2 and X = I/2. In reference-first coordinates take the input diagonals (1, 0, 0, 0) and (0, 1/4, 3/4, 0). The joint input difference has trace distance one and the reference distance is 3/4. The output difference has diagonal (11/16, 1/16, −9/16, −3/16), giving trace distance 3/4. The conditional ratio is therefore zero, below the proposed lower bound of 1/2. Proposition 10 of the conditional contraction paper, Equations (5.38) and (5.39), also supplies a witness after evaluating its classical pair at trace distance. Hirche's 2024 vanishing hockey-stick expansion result (arXiv:2405.00105, Appendix B-B, Equations (B.10)–(B.16)) implies the conditional failure by adjoining a binary reference flag.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.result`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](../CompleteHockeyStickRefutation.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension](../UmegakiChannelSupportedExtension.md)
