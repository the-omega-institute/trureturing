# OrbitIncidenceChecker

## Abstract

Exact tree evaluation and finite Fourier identities support the exclusion of uniform mixing on the cycle with twenty-one vertices.

**Theorem 1.1 (checked_inc).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{F} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp} \to \operatorname{K}) (\operatorname{src} : \operatorname{Nat} \to (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp} \times \operatorname{Int})) (\operatorname{rep} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp}) (\operatorname{t} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) , (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.checkInc} \operatorname{src} \operatorname{rep} \operatorname{t} = \operatorname{true}) \to (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalInc} \operatorname{F} \operatorname{src} \operatorname{t} = (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.coefficientSum} \operatorname{src} \operatorname{t} : \operatorname{K}) \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm} \operatorname{F} \operatorname{rep})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.checked_inc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every accepted incidence tree evaluates to its total coefficient times the orbit sum of its representative. Node composition preserves this equality.

**Definition 1.2 (certificateScalar).**

$$\operatorname{certificateScalar} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.certificateScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed natural scalar in the integer Laurent certificate has the displayed type. Its value is specified by the Lean definition.

**Theorem 1.3 (identity).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{F} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp} \to \operatorname{K}) , ((\operatorname{List.range} 149736) . \operatorname{map} (\operatorname{fun} \operatorname{i} \mapsto ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{i}) . 2 : \operatorname{K}) \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm} \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{i}) . 1)) . \operatorname{sum} = (\operatorname{certificateScalar} : \operatorname{K}) \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm} \operatorname{F} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.zeroExp}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.certificateScalar`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.checked_inc`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIncidenceChecker.identity`
- Dependency: [D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker](SupportMaskChecker.md)
