# Concrete operator-algebra adapter

## Abstract

A concrete von Neumann algebra is an actual norm-closed C-star subalgebra with the inherited operator order, to which the order-normal whole-L1 realization applies.

**Theorem 1.1 (Closed carrier of the actual double commutant).**

Lean statement: `D5/S3/Quantum/Analysis/VonNeumannNormalL1.closedCarrier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/VonNeumannNormalL1.closedCarrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex Hilbert space H, with no separability or dimension restriction, and any actual M : VonNeumannAlgebra H, closedCarrier proves that M.toStarSubalgebra is norm closed. Its carrier is its double centralizer, and Set.isClosed_centralizer proves the required closedness. Mathlib's StarSubalgebra.cstarAlgebra supplies CStarAlgebra M.toStarSubalgebra. The subtype order is the inherited Loewner order on bounded operators. Mathlib's Subtype.starOrderedRing from ContinuousFunctionalCalculus.Range proves compatibility with this inherited order using square roots inside the closed subalgebra. No new order is selected.

With A:=M.toStarSubalgebra, NormalFunctionals.normalDual is therefore an actual complex Banach space of all-directed order-normal continuous functionals, and NormalL1Realization.exists_normal_L1_extension applies to actual positive complex-linear J with this dual codomain. The retained substantive consumer NormalMomentFamily.compact_normal_posterior_family uses this exact inherited C-star and ordered carrier to construct the compact full continuous-moment family, scalar Riesz measures and their entire complex L1 normal posterior realizations. The order-normality quantifies over suprema in M itself. This adapter makes no identification with WStarAlgebra.exists_predual and proves no ultraweak equivalence, vector representation or full attainment theorem.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/VonNeumannNormalL1.closedCarrier`
- Dependency: [D5/S3/Quantum/Analysis/NormalL1Realization](NormalL1Realization.md)
