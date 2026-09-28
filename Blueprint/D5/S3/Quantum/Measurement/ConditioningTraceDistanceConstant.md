# Conditioning Trace-Distance Constant

## Abstract

Positive conditioning filters have sharp trace-distance constant equal to the spectral condition number.

**Definition 1.1 (The maximum eigenvalue).**

$$\operatorname{rMax}(h_{d}, R, h_{R}) := \operatorname{eigenvalues}_{0}(h_{R})(0).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum eigenvalue is the first entry of the ordered eigenvalue list.

**Definition 1.2 (The minimum eigenvalue).**

$$\operatorname{rMin}(h_{d}, R, h_{R}) := \operatorname{eigenvalues}_{0}(h_{R})(\operatorname{card}(\operatorname{Fin}(d)) - 1).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minimum eigenvalue is the last entry of the ordered eigenvalue list.

**Definition 1.3 (The spectral condition number).**

$$\operatorname{conditionNumber}(h_{d}, R, h_{R}) := \frac{\operatorname{rMax}(h_{d}, R, h_{R})}{\operatorname{rMin}(h_{d}, R, h_{R})}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral condition number is the ratio of the maximum to the minimum eigenvalue.

**Definition 1.4 (The normalized conditioned state).**

$$\operatorname{conditionedState}(h_{d}, R, h_{R}, \rho): \operatorname{DensityState}(\operatorname{Fin}(d)) := \frac{((\operatorname{sqrt}(R) \cdot \operatorname{CStarMatrix.ofMatrix.symm}(\operatorname{val}(\rho))) \cdot \operatorname{sqrt}(R))}{(\operatorname{Re}(\operatorname{Tr}(R \cdot \operatorname{CStarMatrix.ofMatrix.symm}(\operatorname{val}(\rho)))))}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bundled definition applies the positive filter on both sides, normalizes by its real trace, and returns a DensityState.

**Theorem 1.5 (Conditioning has sharp constant equal to the condition number).**

$$\forall d: \mathbb{N}, h_{d}: 2 \le d, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), h_{R}: \operatorname{PosDef}(R), \operatorname{let}(h_{0}: 0 < d)\;(\forall \rho: \operatorname{DensityState}(\operatorname{Fin}(d)), (\forall \sigma: \operatorname{DensityState}(\operatorname{Fin}(d)), (((\operatorname{inv}(\operatorname{conditionNumber}(h_{0}, R, \operatorname{isHermitian}(h_{R}))) \cdot \operatorname{traceDistance}(\rho, \sigma)) \le \operatorname{traceDistance}(\operatorname{conditionedState}(h_{0}, R, h_{R}, \rho), \operatorname{conditionedState}(h_{0}, R, h_{R}, \sigma)) \land \operatorname{traceDistance}(\operatorname{conditionedState}(h_{0}, R, h_{R}, \rho), \operatorname{conditionedState}(h_{0}, R, h_{R}, \sigma)) \le (\operatorname{conditionNumber}(h_{0}, R, \operatorname{isHermitian}(h_{R})) \cdot \operatorname{traceDistance}(\rho, \sigma))))) \land (\forall \rho: \operatorname{DensityState}(\operatorname{Fin}(d)), ((\operatorname{rMin}(h_{0}, R, \operatorname{isHermitian}(h_{R})) = \operatorname{rMax}(h_{0}, R, \operatorname{isHermitian}(h_{R})) \Rightarrow \operatorname{conditionedState}(h_{0}, R, h_{R}, \rho) = \rho)) \land \operatorname{IsLUB}(\{x \mid \exists \rho: \operatorname{DensityState}(\operatorname{Fin}(d)), (\exists \sigma: \operatorname{DensityState}(\operatorname{Fin}(d)), ((\rho \neq \sigma \land x = (\frac{\operatorname{traceDistance}(\operatorname{conditionedState}(h_{0}, R, h_{R}, \rho), \operatorname{conditionedState}(h_{0}, R, h_{R}, \sigma))}{\operatorname{traceDistance}(\rho, \sigma)}))))\}, \operatorname{conditionNumber}(h_{0}, R, \operatorname{isHermitian}(h_{R}))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite filter in dimension at least two, canonical density states obey the two-sided trace-distance bound.

Equal extreme eigenvalues make the bundled conditioned state equal to the input, and the condition number is the least upper bound of all nontrivial conditioned-to-unconditioned ratios.

The scoped hypothesis h_0 : 0 < d is derived from h_d : 2 <= d and supplies every positivity proof argument in the displayed statement.

Here Fin d models the source support space H_P; the construction of H_P and R from a general instrument (Convention 26.1), and the exact values along the sharpness family, are not part of the statement.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin`
- Dependency: [D5/S3/Quantum/Measurement/BranchConditionedTraceDistance](BranchConditionedTraceDistance.md)
