# TracePerspectiveConvexity

## Abstract

Ando trace perspective convexity from the actual uniform Jensen input.

**Theorem 1.1 (Joint trace perspective convexity).**

$$\forall u: \operatorname{Level}(), H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)],\ [\operatorname{FiniteDimensional}(\mathbb{C}, H)], [\operatorname{Nontrivial}(H)],\ a: \mathbb{R}, K: \operatorname{L}(H),\ 1\le a\le 2\implies\ \operatorname{JointlyConvexOn}(\operatorname{pdSet}(H), \operatorname{pdSet}(H), \operatorname{liebTraceMap}(a, K))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/TracePerspectiveConvexity.trace_perspective_jointly_convex` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb joint trace concavity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

For 1 <= a <= 2 and arbitrary bounded K on any complete nontrivial finite dimensional complex Hilbert space, Re Tr(A to exponent a K* B to exponent 1-a K) is jointly convex for positive definite A and B. K need not be invertible or selfadjoint. This consumed supplier transports to square matrices and feeds explicit Carlen-Lieb optimizer interpolation.

Apply the public generalized perspective theorem to the actual all-Hilbert CondIciAll for x to exponent a and the affine second function x to exponent one. Transfer affine mixtures through the Hilbert-Schmidt left and right multipliers, then apply the positive quadratic functional phiK. The existing public phiK_operatorPowerMean_eq_liebTraceMap supports unrestricted real exponents and supplies the exact trace identity. No joint eigenbasis proof or private CondV core is reproved.

Right multiplication is an antihomomorphism and its star algebra homomorphism has opposite domain. The second perspective input remains the base. For a quadratic vector Z the trace transport uses K=star Z. Physlib source reuse is Apache-2.0 and the mathematics is classical. Native audit remains unfinished under #5214: the full dependent Hilbert telescope lacks a supplied lawful template with rigid universe reconstruction and variation/sensitivity evidence. No declared_validated status or full Hiai resolution is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/TracePerspectiveConvexity.trace_perspective_jointly_convex`
- Dependency: [D5/S3/Quantum/Lieb/LiebConcavity](LiebConcavity.md)
- Dependency: [D5/S3/Quantum/Lieb/PowerConvexity](PowerConvexity.md)
