# Exact reduction of weighted overlap optimization to its common corner

## Abstract

Exact reduction of weighted overlap optimization to its common corner

The trace weight W is arbitrary in this reduction. Strict positivity is imposed only later on its compression. The reduction preserves the full feasible optimization, rather than only the canonical candidate.

**Theorem 1.1 (diagonal feasible).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For d_i in [0,1] and t>=0, diag(min(d_i,t(1-d_i))) is PSD and below both diag(d) and t(1-diag(d)). This supplies the canonical feasible point used in the reduction.

**Theorem 1.2 (diagonal optimization reduction).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_optimization_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_optimization_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For d_i in [0,1], arbitrary W and t>=0, weighted optimality of the diagonal canonical overlap over all ambient PSD common lower bounds is equivalent to weighted optimality on the subtype 0<d_i<1, with both W and the candidate compressed. Support, order-preserving extension and cyclic trace transport prove both directions. CornerCriterion consumes this iff.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_feasible`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.diagonal_optimization_reduction`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickCorner](MaximalHockeyStickCorner.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight](MaximalHockeyStickCornerWeight.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold](MaximalHockeyStickThreshold.md)
