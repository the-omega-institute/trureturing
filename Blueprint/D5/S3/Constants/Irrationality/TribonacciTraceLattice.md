# Tribonacci Deficit Integrality Contrast

## Abstract

The Tribonacci deficit is nonintegral somewhere, and integrality distinguishes the Fibonacci encoding.

There exist natural inputs v1 and v2 for which the Binet-main-term Tribonacci deficit has no integer representative. This is an unrestricted existential statement: the finite scan used to find the witness is not a hypothesis in the Lean declaration.

For the concrete two-element comparison carrier, the Fibonacci and Tribonacci HasIntegralDeficit propositions are unequal. Moreover, the Tribonacci proposition is false, so the Fibonacci encoding cannot be replaced by the Tribonacci encoding.

What this does not claim: it does not identify an input domain behind the reported output bound or 44.4 percent; it does not identify a nonintegral topological spectrum with an additive trace lattice; and it does not claim a quadratic embedding-exhaustion theorem, a cubic one-real/two-complex signature, or an Algebra.trace obstruction. Those clauses lack the required source-specific carriers.

The previous thirteen-leaf finite-window result remains available as tribonacci_trace_lattice_window_certificate. It preserves the exact bound, count, rounding, code image, congruence, and supporting root facts without presenting them as source clauses of this theorem.

**Theorem 1.1 (PZG Remark 6.27: nonintegrality and two-faced privilege).**

$$\left(\exists v1 \in N, v2 \in N,\; \neg \left(\exists z \in Z,\; \operatorname{tribonacciDeficit}\left(\mathit{v1}, \mathit{v2}\right) = z\right)\right) \land \left(\operatorname{HasIntegralDeficit}\left(\mathit{fibonacci}\right) \ne \operatorname{HasIntegralDeficit}\left(\mathit{tribonacci}\right) \land \left(\neg \operatorname{HasIntegralDeficit}\left(\mathit{tribonacci}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciTraceLattice.pzg_remark_6_27_tribonacci_trace_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public type has two conjunction nodes and three independently projectable leaves: the existential CAS-A2 witness, the CAS-A10 privilege relation, and the CAS-A11 nonreplaceability negation.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciTraceLattice.pzg_remark_6_27_tribonacci_trace_lattice`
- Dependency: [D5/S3/Constants/Irrationality/CubicConjugateTrace](CubicConjugateTrace.md)
- Dependency: [D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate](TribonacciDeficitScanCertificate.md)
- Dependency: [D5/S3/Constants/Irrationality/TwoFacedPrivilege](TwoFacedPrivilege.md)
