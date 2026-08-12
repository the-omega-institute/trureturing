# Exact Additive Pricing and Higher-Degree Pruning

## Abstract

Finite complete contexts preserve additive Born totals exactly, while one explicit qutrit state and two complete contexts separate the corresponding quartic and sextic totals.

**Theorem 1.1 (Additive totals are context-invariant).**

$$\operatorname{trace}(\rho) = 1 \land \operatorname{Complete}(C) \Rightarrow T_{2}(\rho, C) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/AdditivePricingPruning.additive_total_context_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite matrix dimension and finite context, if the context resolves the identity and the priced matrix has trace one, then its additive Born total is one.

**Theorem 1.2 (Exact finite harmonic pruning certificate).**

$$(T_{2}(\rho, C_{\mathrm{std}}) = 1 \land T_{2}(\rho, C_{\mathrm{aligned}}) = 1) \land (T_{4}(\rho, C_{\mathrm{std}}) = \frac{1}{3} \land T_{4}(\rho, C_{\mathrm{aligned}}) = 1) \land (T_{6}(\rho, C_{\mathrm{std}}) = \frac{1}{9} \land T_{6}(\rho, C_{\mathrm{aligned}}) = 1) \land T_{4}(\rho, C_{\mathrm{std}}) < T_{4}(\rho, C_{\mathrm{aligned}}) \land T_{6}(\rho, C_{\mathrm{std}}) < T_{6}(\rho, C_{\mathrm{aligned}})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/AdditivePricingPruning.harmonic_spectral_pruning_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the equal-amplitude qutrit state, the additive totals in the standard and aligned contexts are both one. Their quartic totals are respectively one third and one, and their sextic totals are respectively one ninth and one. Both higher-degree comparisons are strict.

**Theorem 1.3 (Exact Born controls satisfy the numerical tolerance).**

$$\Vert\Re(T_{2}(\rho, C_{\mathrm{std}}))-1\Vert = 0 \land \Vert\Re(T_{2}(\rho, C_{\mathrm{aligned}}))-1\Vert = 0 \land \frac{1}{10^{16}} < \Vert T_{4}(\rho, C_{\mathrm{std}})- T_{4}(\rho, C_{\mathrm{aligned}})\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/AdditivePricingPruning.born_control_numerical_tolerance_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute additive-total defects in both contexts equal zero, and the quartic gap is strictly larger than 10^-16. In particular, both controls lie strictly within the stated tolerance.

**Theorem 1.4 (The certificate is inhabited and discriminating).**

$$\exists \rho, \operatorname{Positive}(\rho) \land \operatorname{trace}(\rho) = 1 \land \operatorname{Complete}(C_{\mathrm{std}}) \land \operatorname{Complete}(C_{\mathrm{aligned}}) \land 0 < \Re(T_{2}(\rho, C_{\mathrm{std}})) \land T_{4}(\rho, C_{\mathrm{std}}) < T_{4}(\rho, C_{\mathrm{aligned}})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/AdditivePricingPruning.additive_pricing_anti_vacuity_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported equal-amplitude density matrix supplies positivity and trace one, while both displayed contexts supply exact identity resolutions.

Its standard additive total is positive and its quartic standard total is strictly smaller than its quartic aligned total, so the certificate is inhabited and discriminating.

The exact finite result asserts no random-basis sample variance, distribution over contexts, or general extremal classification.

## References

- Truth anchor: `D5/S3/QuantumContext/AdditivePricingPruning.additive_pricing_anti_vacuity_witness`
- Truth anchor: `D5/S3/QuantumContext/AdditivePricingPruning.additive_total_context_invariant`
- Truth anchor: `D5/S3/QuantumContext/AdditivePricingPruning.born_control_numerical_tolerance_certificate`
- Truth anchor: `D5/S3/QuantumContext/AdditivePricingPruning.harmonic_spectral_pruning_certificate`
- Dependency: [D5/S3/QuantumContext/QuarticContextWitness](QuarticContextWitness.md)
