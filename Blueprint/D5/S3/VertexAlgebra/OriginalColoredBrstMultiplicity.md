# Original BRST Colored Partition Multiplicities

## Abstract

The actual original nonzero-charge on-shell Lorentzian BRST ghost-one and ghost-two multiplicities are the independent twenty-four-color partition coefficient.

coloredMultiplicity(c, level) is zero for negative integer level, and otherwise coefficient level.toNat of Nat.Partition.genFun(one) to the c-th power. p24 is coloredMultiplicity with c equal to twenty-four, never a definition by the actual native index cardinal. The actual TransverseDownIndex has nativeLevel(powers, empty) equal to level. polarizedLevel(empty) is zero; there is no ghost offset hidden in the conversion.

**Theorem 1.1 (Actual Transverse Index Count).**

Lean statement: `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.downIndex_card`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.downIndex_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice D, two distinct native axes x and y and every integer level, the cardinal of the actual TransverseDownIndex is coloredMultiplicity(rank minus two, level). TransverseColors is the actual finite complement of these axes, whose cardinal is rank minus two. downOccupationEquiv restricts occupations along its explicit frequency-preserving embedding and extends them back with zero axes; down_support proves the needed support condition and both inverse laws are exact. lift_nativeLevel proves preservation of the original integer energy. Negative indices are empty by the supplied original nativeLevel_nonnegative. No displayed frame is an input to the physical theorem.

**Theorem 1.2 (Actual Original Absolute Cohomology Dimensions).**

Lean statement: `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.original_brst_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.original_brst_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original D and complex H, assume H times gramComplex equals one and gramComplex times H equals one, rank equals twenty-six, beta is nonzero, actual signature of the real Gram quadratic form equals rank minus two, and chosenH(D,beta) plus integer level minus one equals zero in the complex numbers. For every such integer level, the actual original ghostCohomology in degree one and degree two each has complex finrank p24(level); the full original energy-sector cohomology has finrank twice p24(level). The native frame is obtained internally by OriginalAbsoluteGradedSector.choice from the original constructedFrame, and its supplied distinct-axes proof yields exactly twenty-four colors. The proof consumes the actual downEquiv, upEquiv and ungradedEquiv, with the original ambient-boundary quotient already present in their source chain. It does not assume a surrogate complex or a physical-space equivalence.

For every other integer ghost degree, the existing RelativePairing.AbsolutePhysicalNoGhost.original_other_ghost_cohomology_zero proves that every class in the same literal original quotient equals zero. This is the already supplied vanishing result used by OriginalAbsoluteGradedSector.twoDegreesEquiv, not a new duplicate dimension theorem. The negative-level conclusion is actual vanishing of the finite original quotient dimensions, not positivity at every level. Level zero has only the vacuum occupation. The conclusion is restricted to the stated nonzero-charge on-shell sectors; it asserts no fixed-beta off-shell character, no all-charge positivity and no neutral beta-zero result. These are classical BRST oscillator multiplicities, not a Monster Lie algebra, denominator, anomaly, fusion or complete string or AdS/CFT formalization. The larger original goal remains open, as do source admission and remote CI, merge, dev synchronization and cleanup.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.downIndex_card`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity.original_brst_multiplicities`
- Dependency: [D5/S3/VertexAlgebra/ColoredFockCharacter](ColoredFockCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalAbsoluteGradedSector](OriginalAbsoluteGradedSector.md)
