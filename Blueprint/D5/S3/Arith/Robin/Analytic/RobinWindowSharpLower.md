# Actual zero strips and weighted negative mass

## Abstract

Sharp lower power bounds for Robin window mass

Write M_b(Y) for the actual weighted negative mass from Y to Y^b of the Chebyshev kernel (ψ(t)−t)/t². A strip of width α>0 means that every nontrivial zeta zero has real part at most 1−α.

**Theorem 1.1 (A fixed zero on an inner power window).**

Lean statement: `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.off_line_zero_forces_weighted_negative_mass_of_actual_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.off_line_zero_forces_weighted_negative_mass_of_actual_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 1<d<b and a nontrivial zero with real part β>1/2. If max(r,d/2−bα,0)<d(β−1/2), then Y^r≤M_b(Y) for every sufficiently large real Y. Choose an intermediate power s between these bounds. The inner prime mass is at least Y^s. Its comparison with the full mass has a bounded coefficient on M_b(Y), an endpoint term of power d/2−bα, and a logarithmic prime-power correction. The last two terms are absorbed by Y^s, which also dominates the target power.

**Theorem 1.2 (The zero abscissa and cofinal power bounds).**

Lean statement: `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.weighted_negative_mass_power_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.weighted_negative_mass_power_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let β* be the supremum of the real parts of the nontrivial zeros. Under a positive strip and for fixed b>1, each real 0<r<b(β*−1/2) satisfies Y^r≤M_b(Y) eventually. Use the positive strip width 1−β*, choose d<b with r<d(β*−1/2), and take an actual zero sufficiently near β*. The gap at the supremum between the inner pole power and the endpoint power is (b−d)(1−β*)>0. For a fixed p≥0 and constant C, a cofinal bound M_b(Y)≤CY^p then forces β*≤1/2+p/b.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.off_line_zero_forces_weighted_negative_mass_of_actual_strip`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.weighted_negative_mass_power_criterion`
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass](../../../Weil/Mertens/IntegratedExplicit/RobinWindowMass.md)
