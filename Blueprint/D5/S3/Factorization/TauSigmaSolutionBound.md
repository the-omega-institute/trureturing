# A336687 Solution Bound

## Abstract

A bound on positive tau-sigma fixed points, with finite classification still open.

This module does not prove the A336687 conjecture. It proves only that every positive solution is below 3^13. The finite exhaustive classification needed to obtain the three-solution theorem remains an explicit unproved hypothesis.

**Theorem 1.1 (Every positive solution is below 3^13).**

$$\forall m \in \mathbb{N}, 1 \le m \implies \operatorname{tau}(\operatorname{sigma}(m)) \cdot \operatorname{sigma}(\operatorname{tau}(m)) = m \implies m < 3^{13}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TauSigmaSolutionBound.tau_sigma_solution_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev; Bernard Schott (2020). *OEIS A336687, divisor compositions and a three-solution equality conjecture*. URL: <https://oeis.org/A336687>.

*Commentary.*

Apply each uniform fourth-power estimate twice. Multiplying the resulting sixteenth-power inequalities gives m^16 <= 3^77*m^10. Positivity permits cancellation, so m^6 <= 3^77 < (3^13)^6, yielding m < 1594323.

**Theorem 1.2 (Conditional three-solution classification).**

$$(\forall n \in \mathbb{N}, 1 \le n \implies n < 3^{13} \implies \operatorname{tau}(\operatorname{sigma}(n)) \cdot \operatorname{sigma}(\operatorname{tau}(n)) = n \Leftrightarrow \left(n = 1 \lor \left(n = 468 \lor n = 3240\right)\right)) \implies \forall m \in \mathbb{N}, 1 \le m \implies \operatorname{tau}(\operatorname{sigma}(m)) \cdot \operatorname{sigma}(\operatorname{tau}(m)) = m \Leftrightarrow \left(m = 1 \lor \left(m = 468 \lor m = 3240\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TauSigmaSolutionBound.tau_sigma_product_eq_self_iff_of_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev; Bernard Schott (2020). *OEIS A336687, divisor compositions and a three-solution equality conjecture*. URL: <https://oeis.org/A336687>.

*Commentary.*

The hypothesis hfinite asserts the complete equivalence on 1 <= n < 3^13. It is not established by this module. Under that hypothesis the proved bound extends the equivalence to all positive m. No unconditional resolution claim is made.

## References

- Truth anchor: `D5/S3/Factorization/TauSigmaSolutionBound.tau_sigma_product_eq_self_iff_of_finite`
- Truth anchor: `D5/S3/Factorization/TauSigmaSolutionBound.tau_sigma_solution_lt`
- Dependency: [D5/S3/Factorization/TauSigmaPowerBounds](TauSigmaPowerBounds.md)
