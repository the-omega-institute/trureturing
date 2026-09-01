# Finite Vandermonde Tomography

## Abstract

Distinct finite phase nodes make a matching finite moment window faithful.

**Theorem 1.1 (Distinct nodes give faithful finite moments).**

$$\forall v, \operatorname{Injective}(v) \Rightarrow \operatorname{Injective}(\operatorname{finiteMomentReadout}(v)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.finite_moment_readout_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of pairwise distinct nodes over a field, the first matching number of power moments uniquely determines the hidden amplitude vector.

The proof reuses Mathlib's Vandermonde determinant and determinant-kernel machinery. It asserts exact finite injectivity and leaves conditioning and infinite reconstruction outside its scope.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.finite_moment_readout_injective`
