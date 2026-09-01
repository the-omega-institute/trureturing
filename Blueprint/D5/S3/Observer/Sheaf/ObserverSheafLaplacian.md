# Finite Observer Sheaf Laplacian

## Abstract

A finite observer coboundary yields a Hermitian Laplacian and zero Dirichlet energy exactly characterizes compatibility.

**Definition 1.1 (Matrix compatibility).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.MatrixCompatible`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.MatrixCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coordinate observer family is compatible when the coboundary matrix annihilates it.

**Definition 1.2 (Observer sheaf Laplacian).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-zero finite Laplacian is the adjoint coboundary multiplied by the coboundary.

**Definition 1.3 (Observer Dirichlet energy).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compatibility defect is measured by the sum of squared edge-defect norms.

**Definition 1.4 (Observer harmonicity).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.IsObserverHarmonic`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.IsObserverHarmonic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local observer family is harmonic when the degree-zero Laplacian annihilates it.

**Theorem 1.5 (The Laplacian is Hermitian).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_isHermitian`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every adjoint-times-original finite coboundary matrix is Hermitian.

**Theorem 1.6 (Dirichlet energy is nonnegative).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_nonneg`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge contributes a squared norm and the finite sum is nonnegative.

**Theorem 1.7 (Zero energy is compatibility).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_eq_zero_iff`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total edge-defect energy vanishes exactly when the coboundary annihilates the section.

**Theorem 1.8 (Laplacian action factors through defects).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_mulVec`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the Laplacian means first taking the coboundary and then applying its conjugate transpose.

**Theorem 1.9 (Compatible sections are harmonic).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.matrixCompatible_implies_harmonic`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.matrixCompatible_implies_harmonic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every zero-defect observer family lies in the kernel of the finite sheaf Laplacian.

**Theorem 1.10 (Injective adjoint gives the converse).**

Lean statement: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.harmonic_implies_matrixCompatible_of_adjoint_injective`

*Formalization.* `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.harmonic_implies_matrixCompatible_of_adjoint_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the adjoint coboundary is injective, harmonicity forces the original edge defects to vanish.

## References

- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.MatrixCompatible`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.IsObserverHarmonic`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_isHermitian`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_nonneg`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerDirichletEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.observerSheafLaplacian_mulVec`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.matrixCompatible_implies_harmonic`
- Truth anchor: `D5/S3/Observer/Sheaf/ObserverSheafLaplacian.harmonic_implies_matrixCompatible_of_adjoint_injective`
- Dependency: [D5/S3/Observer/Sheaf/FiniteObserverSheaf](FiniteObserverSheaf.md)
