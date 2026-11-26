# Complete hockey-stick contraction and the Hermitian Doeblin coefficient

## Abstract

A binary channel violates the proposed complete hockey-stick bound using Hermitian alpha.

**Definition 1.1 (The proposed bound at gamma two).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.claim`

*Formalization.* `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.claim` (`✓ std3`).

*Citation.* Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde (2026). *Quantum Doeblin Coefficients: Interpretations and Applications*. DOI: [10.22331/q-2026-05-22-2115](https://doi.org/10.22331/q-2026-05-22-2115). URL: <https://arxiv.org/html/2503.22823v3>.

*Commentary.*

For the binary measure-and-prepare channel, the proposed inequality in Section 9.2(1) would imply that at gamma two the complete coefficient is at most one minus the trace of every Hermitian H with I tensor H below the unnormalized Choi operator. Definition 4 takes the supremum over these traces.

**Theorem 1.2 (A Hermitian minorant of trace two fifths).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde (2026). *Quantum Doeblin Coefficients: Interpretations and Applications*. DOI: [10.22331/q-2026-05-22-2115](https://doi.org/10.22331/q-2026-05-22-2115). URL: <https://arxiv.org/html/2503.22823v3>.

*Commentary.*

The channel measures in the computational basis and prepares the rays of (1,0) and (4/5,3/5). Its unnormalized Choi operator has those two density matrices P and Q as diagonal blocks in input-first order. The matrix H = [[13,6],[6,-3]]/25 is Hermitian. The differences P − H and Q − H are 3/25 times the outer products of (2,-1) and (1,2), respectively, so I tensor H lies below the Choi operator.

The trace of H is 2/5 and the complete coefficient at gamma two is at least 9/10, which exceeds 3/5. Hence the coefficient also exceeds one minus the supremum in Definition 4. Proposition 31 applies to alpha plus, whose feasible matrices must be positive semidefinite.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.result`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](CompleteHockeyStickRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
