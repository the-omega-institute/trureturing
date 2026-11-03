# A quantitative fixed Petz recovery estimate

## Abstract

Actual entropy loss bounds trace distance from fixed Petz recovery.

**Theorem 1.1 (One fixed recovery channel, then all supported input states).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalPetzStability.supported_entropy_defect_fixed_petz_trace_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalPetzStability.supported_entropy_defect_fixed_petz_trace_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Fix an arbitrary channel Phi between finite nonempty quantum systems and a reference density sigma. There is one completed Petz recovery channel, chosen before rho, with the stated full-matrix Kraus action and complement reset to sigma. It recovers sigma exactly. For every density rho supported in sigma, construct the actual supported relative-modular model M. Let m > 0 satisfy mI <= A and mI <= B on its supported carriers, and let L >= 0 bound every actual spectral ratio sj/ri. If Delta is the finite trace-log relative entropy loss under Phi, the trace norm of recovery(Phi(rho)) minus rho is at most (16/pi) sqrt(L/m) Delta^(1/4). The constant retains the stated spectral dependence; the physical density matrices may be singular.

The proof consumes the full-axis entropy-resolvent budget and its genuine Euclidean L2 inverse-square-root estimate. The physical amplitude keeps the input support projection. Its squared Hilbert-Schmidt error is the exact coordinate sum weighted by sj/ri, and is therefore bounded by L times the squared modular-coordinate error. A shared Schwarz and equal-trace supplier and the Hilbert-Schmidt-to-trace estimate convert this to the Petz core trace error. Support containment makes the complement reset vanish on Phi(rho), so this core is exactly the output of the same fixed channel. No supremum norm is identified with L2, and no unweighted modular norm is identified with the physical Hilbert-Schmidt norm.

This is a quantitative library derivation using existing Petz construction, resolvent and matrix analysis, with no claim of literature novelty or optimality of the constant. Related quantitative Petz estimates are treated by Carlen and Vershynina, Recovery map stability for the Data Processing Inequality, arXiv:1710.02409v3, and Recovery and the Data Processing Inequality for quasi-entropies, arXiv:1710.08080v3. Those references are context for the stability method, not an assertion that their parameterization or constants coincide with this statement. The unsupported infinite-entropy branch and spectral bounds not satisfying the displayed hypotheses are outside the estimate.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalPetzStability.supported_entropy_defect_fixed_petz_trace_stability`
- Dependency: [D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability](../Divergence/EntropyDefectInverseSqrtStability.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalPetzEquality](CanonicalPetzEquality.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzCoreTraceStability](PetzCoreTraceStability.md)
