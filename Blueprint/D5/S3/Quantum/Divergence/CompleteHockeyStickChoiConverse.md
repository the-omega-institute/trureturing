# Strict complete hockey-stick contraction and Choi support

## Abstract

A full reference factor in the normalized Choi support characterizes strict complete hockey-stick contraction at each fixed parameter greater than one.

**Theorem 1.1 (Pure replacement from full Choi support slices).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Let a finite CPTP channel have nonempty input. Suppose that for one nonzero output vector every reference basis slice of that vector lies in the range of the normalized Choi matrix. There exist a weight p strictly between zero and one, a pure output state, and a finite CPTP residual channel. On every input matrix, the channel is the sum of the residual with weight one minus p and trace times the pure state with weight p.

Normalize the output vector and assemble preimages of its slices under the positive Choi square root. A bound on their Gram matrix provides a strictly positive weight that can be subtracted while preserving Choi positivity. After dividing by one minus p, the remaining map is trace preserving. A finite Kraus representation gives the residual channel.

**Theorem 1.2 (Strict contraction from full Choi support slices).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For every parameter at least one, a full reference factor over a nonzero output vector implies that the complete coefficient for equal-reference-marginal inputs is strictly below one. The constructed replacement weight p gives the upper bound one minus p by the exhibited-weight bound from Proposition 31 of George, Hirche, Nuradha and Wilde.

**Theorem 1.3 (Choi support criterion for strict contraction).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For any finite CPTP channel with nonempty input and each fixed parameter greater than one, the complete coefficient for equal-reference-marginal inputs is strictly below one if and only if the normalized Choi support contains a full reference factor over a nonzero output vector. In its absence the saturation proof applies the classical-input support mechanism of Eriksson v3, Section 6, through finite Bell preparations. In its presence the finite Choi residual construction gives strict contraction. Both branches concern the static channel and its Choi support.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_iff`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport](CompleteHockeyStickChoiSupport.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
