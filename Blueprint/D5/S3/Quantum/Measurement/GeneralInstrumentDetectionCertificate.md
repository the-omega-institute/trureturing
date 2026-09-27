# Uniform Detection Certificate for General Instruments

## Abstract

When a general no-click instrument has no definite dark direction, the survival effects decay geometrically in blocks of d rounds, and the survival probabilities of every initial state have sum at most d / g.

**Theorem 1.1 (Block decay of the survival effects).**

$$\sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \Rightarrow\\{}(D_{d} = 0 \Rightarrow \exists g > 0, g I \leq I-S_{d}) \land\\{}\forall g > 0, g I \leq I-S_{d} \Rightarrow (\forall m, S_{m d} \leq (1-g)^{m} I) \land\\{}\forall \rho \geq 0 \text{ with }\operatorname{Tr} \rho = 1, (N \mapsto \operatorname{Re} \operatorname{Tr}(\rho S_{N})) \text{ summable }\land \sum_{N} \operatorname{Re} \operatorname{Tr}(\rho S_{N}) \leq \frac{d}{g}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentDetectionCertificate.detection_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the d-dimensional space with the completeness relation, let S_N be the survival effects and D_d the stable dark layer; the order is the Loewner order.

If D_d is zero, then I - S_d is positive definite, so its spectrum is positive and compact, and some g > 0 satisfies g I <= I - S_d. For any such g, S_d <= (1 - g) I; the dual no-click map is positive, monotone and homogeneous, so S_{(m+1)d} = A^d(S_{md}) <= (1 - g)^m A^d(I) = (1 - g)^m S_d <= (1 - g)^{m+1} I.

For a density matrix rho, the real parts of the traces Tr(rho S_N) are nonnegative and decrease in N; the block of d consecutive terms starting at md is at most d (1 - g)^m, and the geometric sum of these block bounds is at most d / g.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentDetectionCertificate.detection_certificate`
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection](GeneralInstrumentNoDarkDirection.md)
