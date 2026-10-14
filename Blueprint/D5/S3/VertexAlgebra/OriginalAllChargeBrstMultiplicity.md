# Original All-Charge BRST Multiplicities

## Abstract

The literal original critical BRST energy-sector quotients have an all-charge, all-integer-level and all-integer-ghost-degree multiplicity classification.

Fix the original lattice data and both inverse-Gram equations at critical rank twenty-six. Levels and ghost degrees range over all integers. For nonzero charge the actual real quadratic signature is rank minus two. This signature condition supplies the previously constructed frame; no independently supplied frame replaces its construction. The zero-charge branch does not require a positivity hypothesis.

**Theorem 1.1 (Off-Shell Original Quotient Vanishes).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_off_shell_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_off_shell_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

originalSectorEquiv compares the kernel and range quotient of the actual restricted energyOriginalQ with the literal OriginalBrstReassembly.Cohomology. The established original_off_shell_cycle_boundary uses the actual original Ward identity and the charge-energy projection of the inverse-energy-scaled antighost contraction. Transporting that precise boundary, rather than an ambient-image dimension, kills every off-shell class. The split inclusion of each integral ghost-degree quotient into the full quotient is injective, so full off-shell vanishing also kills every off-shell graded quotient.

**Theorem 1.2 (Complete Integral Multiplicity Formula).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_all_charge_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_all_charge_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On shell, nonzero charge has multiplicity p24(level) in ghost degrees one and two, zero in every other degree, and total dimension twice p24(level). This is the existing OriginalColoredBrstMultiplicity result together with the original constructed-frame vanishing theorem. Zero charge is on shell exactly at level one; its dimensions are one, twenty-six, twenty-six and one in degrees zero through three, and total fifty-four. Off shell every degree and the full quotient vanish. The new zero-charge quotient identification supplies the exceptional branch; none of the previous native dimensions or p24 suppliers is reproved.

**Theorem 1.3 (Negative Levels Are Included).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_negative_level_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_negative_level_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every negative integer level both the full and all graded multiplicities vanish. The colored partition supplier defines p24 to be zero at negative level. A zero-charge negative-level sector is off shell, since its mass-shell equation would force level one.

literalOriginalSummandEquiv identifies the exact sector quotient with the corresponding projection range in the literal ambient OriginalCohomology. original_ambient_representative verifies that this inclusion is the class of the unchanged original representative. The mass-shell equation is checked separately for each charge and integer level; the statement does not put all levels of a fixed charge on shell simultaneously. Finite multiplicities under the stated nonzero-charge signature hypothesis do not establish arbitrary-signature energy-fiber finiteness. No descent of an arbitrary nonrelative C0 form, all-charge positivity, denominator identity, Monster construction, complete string theory or AdS/CFT conclusion follows from these multiplicities.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_all_charge_multiplicities`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_negative_level_multiplicities`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity.original_off_shell_zero`
- Dependency: [D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity](OriginalColoredBrstMultiplicity.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalQAmbientMassShellCohomologyTransient](OriginalQAmbientMassShellCohomologyTransient.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge](OriginalZeroChargeGradedSectorBridge.md)
