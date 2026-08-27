# Frobenius Quantum Postprocessing Kernel

## Abstract

Frobenius-observer fibers survive quantum encoding and deterministic observation.

**Theorem 1.1 (Postprocessing preserves every Frobenius-observer fiber).**

$$\begin{gathered}\forall G: \operatorname{Type}, Q: \operatorname{Type}, O: \operatorname{Type},\\{}[\operatorname{Monoid}\left(G\right)], U: Primes \to \operatorname{Prop},\\{}Frob: \forall p: Primes, U\left(p\right) \to G,\\{}eta: \operatorname{Option}\left(\operatorname{ConjClasses}\left(G\right)\right) \to Q, Sigma: Q \to O,\\{}\operatorname{ker}\left(\operatorname{galoisPrimeObserver}\left(U, Frob\right)\right) \subseteq \operatorname{ker}\left(Sigma \circ eta \circ \operatorname{galoisPrimeObserver}\left(U, Frob\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FrobeniusQuantumPostprocessingKernel.frobenius_quantum_postprocessing_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public source object is the canonical tagged Frobenius observer on rational primes. Its unramified predicate and Frobenius representatives remain explicit parameters.

An arbitrary encoding maps the complete tagged output to a quantum state, and an arbitrary deterministic observation maps that state to its final signature. Equality in the source kernel is preserved by both compositions.

The proof directly applies Mathlib's factor-through composition law; no parallel observer or postprocessing primitive is introduced.

## References

- Truth anchor: `D5/S3/Factorization/Galois/FrobeniusQuantumPostprocessingKernel.frobenius_quantum_postprocessing_kernel`
- Dependency: [D5/S3/Factorization/Galois/GaloisPrimeObserver](GaloisPrimeObserver.md)
