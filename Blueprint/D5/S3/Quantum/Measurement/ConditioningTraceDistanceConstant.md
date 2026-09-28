# Conditioning Trace-Distance Constant

## Abstract

Positive conditioning filters have sharp trace-distance constant equal to the spectral condition number.

**Definition 1.1 (The maximum eigenvalue).**

$$\operatorname{rMax}(d, hd, R, hR) := \operatorname{eigenvalueFirst}(R, hR).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum eigenvalue is the first entry of the ordered eigenvalue list.

**Definition 1.2 (The minimum eigenvalue).**

$$\operatorname{rMin}(d, hd, R, hR) := \operatorname{eigenvalueLast}(R, hR).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minimum eigenvalue is the last entry of the ordered eigenvalue list.

**Definition 1.3 (The spectral condition number).**

$$\operatorname{conditionNumber}(d, hd, R, hR) := \frac{\operatorname{rMax}(d, hd, R, hR)}{\operatorname{rMin}(d, hd, R, hR)}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral condition number is the ratio of the maximum to the minimum eigenvalue.

**Definition 1.4 (The normalized conditioned state).**

$$\operatorname{conditionedState}(d, hd, R, hR, rho) := \frac{\operatorname{sqrt}(R) \cdot \operatorname{ofMatrixSymm}(\operatorname{val}(rho)) \cdot \operatorname{sqrt}(R)}{\operatorname{Re}(\operatorname{Tr}(R \cdot \operatorname{ofMatrixSymm}(\operatorname{val}(rho))))}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bundled definition applies the positive filter on both sides, normalizes by its real trace, and returns a DensityState.

**Theorem 1.5 (Conditioning has sharp constant equal to the condition number).**

$$\forall d: \mathbb{N}, hd: 2 \le d, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), hR: \operatorname{PosDef}(R), (\forall rho: \operatorname{DensityState}(\operatorname{Fin}(d)), (\forall sigma: \operatorname{DensityState}(\operatorname{Fin}(d)), ((\operatorname{inv}(\operatorname{conditionNumber}(d, \operatorname{proofOfPositivity}(d), R, \operatorname{isHermitian}(hR))) \cdot \operatorname{traceDistance}(rho, sigma) \le \operatorname{traceDistance}(\operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, rho), \operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, sigma)) \land \operatorname{traceDistance}(\operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, rho), \operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, sigma)) \le \operatorname{conditionNumber}(d, \operatorname{proofOfPositivity}(d), R, \operatorname{isHermitian}(hR)) \cdot \operatorname{traceDistance}(rho, sigma)))) \land (\forall rho: \operatorname{DensityState}(\operatorname{Fin}(d)), ((\operatorname{rMin}(d, \operatorname{proofOfPositivity}(d), R, \operatorname{isHermitian}(hR)) = \operatorname{rMax}(d, \operatorname{proofOfPositivity}(d), R, \operatorname{isHermitian}(hR)) \Rightarrow \operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, rho) = rho)) \land \operatorname{IsLUB}(\{x \mid \exists rho: \operatorname{DensityState}(\operatorname{Fin}(d)), (\exists sigma: \operatorname{DensityState}(\operatorname{Fin}(d)), ((rho \neq sigma \land x = \frac{\operatorname{traceDistance}(\operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, rho), \operatorname{conditionedState}(d, \operatorname{proofOfPositivity}(d), R, hR, sigma))}{\operatorname{traceDistance}(rho, sigma)})))\}, \operatorname{conditionNumber}(d, \operatorname{proofOfPositivity}(d), R, \operatorname{isHermitian}(hR))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite filter in dimension at least two, canonical density states obey the two-sided trace-distance bound.

Equal extreme eigenvalues make the bundled conditioned state equal to the input, and the condition number is the least upper bound of all nontrivial conditioned-to-unconditioned ratios.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin`
- Dependency: [D5/S3/Quantum/Measurement/BranchConditionedTraceDistance](BranchConditionedTraceDistance.md)
