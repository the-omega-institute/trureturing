# Completion Point Covariance

## Abstract

Completion-point carriers are covariant under parameter equivalences that preserve normalization and zero defect.

**Theorem 1.1 (Preserving the defining predicates transports completion points).**

$$\forall A: Type, APrime: Type, D: Type, DPrime: Type, N: \operatorname{Set}(A), NPrime: \operatorname{Set}(APrime),\\\Delta: A \to D, DeltaPrime: APrime \to DPrime, zeroD: D, zeroDPrime: DPrime, \alpha: \operatorname{Equiv}(A, APrime),\\(\forall a: A, a\in N \iff \alpha(a)\in NPrime) \land (\forall a: A, \Delta(a) = zeroD \iff DeltaPrime(\alpha(a)) = zeroDPrime) \Rightarrow\\\operatorname{Bijective}(\alpha: \{a: A \mid a\in N \land \Delta(a) = zeroD\} \to \{aPrime: APrime \mid aPrime\in NPrime \land DeltaPrime(aPrime) = zeroDPrime\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/CompletionPointCovariance.completion_point_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completion carrier is the repository's canonical constrained zero-defect subtype. A parameter equivalence preserving each of its two predicates therefore restricts to the displayed equivalence.

The Lean term is Mathlib's exact subtype equivalence construction. Its forward map sends a completion point with parameter a to the point whose parameter is alpha(a), and the inverse is inherited from alpha.

## References

- Truth anchor: `D5/S3/Observer/Completion/CompletionPointCovariance.completion_point_covariance`
- Dependency: [D5/S3/Observer/Completion/StructuralCompletionSignature](StructuralCompletionSignature.md)
