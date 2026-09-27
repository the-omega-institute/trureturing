# Conditioning Trace-Distance Constant

## Abstract

Positive conditioning filters have sharp trace-distance constant equal to the spectral condition number.

**Definition 1.1 (Density matrices are positive semidefinite and trace one).**

$$\forall d: \mathbb{N}, rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \operatorname{PosSemidef}(rho) \land \operatorname{Tr}(rho) = 1.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.IsDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A density matrix is a positive semidefinite matrix whose trace is one.

**Definition 1.2 (Trace distance is half the trace norm).**

$$\forall d: \mathbb{N}, X: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), Y: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \frac{\operatorname{traceNorm}(X - Y)}{2}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.traceDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace distance is one half of the trace norm of the difference.

**Definition 1.3 (The maximum eigenvalue).**

$$\forall d: \mathbb{N}, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), hR: \operatorname{IsHermitian}(R) \operatorname{rMax}(d, R, hR) = \operatorname{eigenvalueFirst}(R).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum eigenvalue is the first entry of the ordered eigenvalue list.

**Definition 1.4 (The minimum eigenvalue).**

$$\forall d: \mathbb{N}, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), hR: \operatorname{IsHermitian}(R) \operatorname{rMin}(d, R, hR) = \operatorname{eigenvalueLast}(R).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minimum eigenvalue is the last entry of the ordered eigenvalue list.

**Definition 1.5 (The spectral condition number).**

$$\forall d: \mathbb{N}, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), hR: \operatorname{IsHermitian}(R) \operatorname{conditionNumber}(d, R, hR) = \frac{\operatorname{rMax}(d, R, hR)}{\operatorname{rMin}(d, R, hR)}.$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral condition number is the ratio of the maximum to the minimum eigenvalue.

**Definition 1.6 (The normalized conditioned state).**

$$\forall d: \mathbb{N}, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \frac{1}{\operatorname{Re}(\operatorname{Tr}(R \cdot rho))} \cdot \operatorname{sqrt}(R) \cdot rho \cdot \operatorname{sqrt}(R).$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive filter is applied on both sides and normalized by its real trace.

**Theorem 1.7 (Conditioning has sharp constant equal to the condition number).**

$$\forall d: \mathbb{N}, R: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), 1 < d \land \operatorname{PosDef}(R) \Rightarrow \forall rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), sigma: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{IsDensity}(rho) \Rightarrow \operatorname{IsDensity}(sigma) \Rightarrow \operatorname{inv}(\operatorname{conditionNumber}(d, R, \operatorname{hR}(R))) \cdot \operatorname{traceDistance}(rho, sigma) \le \operatorname{traceDistance}(\operatorname{conditionedState}(R, rho), \operatorname{conditionedState}(R, sigma)) \land \operatorname{traceDistance}(\operatorname{conditionedState}(R, rho), \operatorname{conditionedState}(R, sigma)) \le \operatorname{conditionNumber}(d, R, \operatorname{hR}(R)) \cdot \operatorname{traceDistance}(rho, sigma) \land \operatorname{IsLUB}(\{x \mid \operatorname{exists}(rho,  , sigma,  , \operatorname{IsDensity}(rho),  , \operatorname{IsDensity}(sigma) \land \left(rho \neq sigma \land x = \frac{\operatorname{traceDistance}(\operatorname{conditionedState}(R, rho), \operatorname{conditionedState}(R, sigma))}{\operatorname{traceDistance}(rho, sigma)}\right))\}, \operatorname{conditionNumber}(d, R, \operatorname{hR}(R))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite filter in dimension at least two, conditioning preserves density matrices and changes trace distance by at most the spectral condition number and at least its reciprocal.

The condition number is sharp: it is the least upper bound of all nontrivial ratios of conditioned to unconditioned trace distance.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.IsDensity`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.traceDistance`
- Dependency: [D5/S3/Quantum/Measurement/BranchConditionedTraceDistance](BranchConditionedTraceDistance.md)
