# Two-point functional calculus

## Abstract

Shared existing functional calculus for self-adjoint matrix involutions.

**Theorem 1.1 (Spectrum of a self-adjoint involution).**

Lean statement: `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.involution_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.involution_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type n with Fintype and DecidableEq instances, a self-adjoint complex matrix H with H H = I has real spectrum contained in {1,-1}. This is the existing proof extracted from the cumulant-Renyi refutation, consumed there and by the Hiai TILDE classification.

**Theorem 1.2 (Exact affine involution calculus).**

Lean statement: `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.two_point_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.two_point_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type n with Fintype and DecidableEq instances, any self-adjoint complex matrix H with H H = I, every real function f, and all real a and b, the actual matrix CFC of a I + b H equals ((f(a+b)+f(a-b))/2) I + ((f(a+b)-f(a-b))/2) H. The finite spectrum requires no global continuity assumption on f. Both existing consumers reuse the one extracted proof. This refactor claims no independent mathematical gain.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.involution_spectrum`
- Truth anchor: `D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.two_point_cfc`
