# Integer oriented support checker

## Abstract

Integer oriented support checker.

**Definition 1.1 (Integer oriented support checker).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/CofactorCatalog.CaseValid`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/CofactorCatalog.CaseValid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer matrix aZ contains the three boundary rows. Appending minus the three by three identity gives bZ with nineteen columns; its real cast is the slack kernel matrix. Each original gap vector is aligned with its ray label and its three exact slacks. For an increasing four-column support, CaseValid checks one of three alternatives: opposite cofactor signs, all cofactors zero, or an explicitly oriented zero extension equal to a strictly positive integer multiple of one original catalog vector. The witness is supplied, rather than searched over the catalog.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/CofactorCatalog.CaseValid`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCofactor](../NonnegativeKernelCofactor.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments](RayMoments.md)
