# Base-Four Residue Bridge

## Abstract

The residues of four-to-the-n modulo five and seven recover n modulo six, while prime-axis factorization sees only the exponent 2n on prime two.

**Definition 1.1 (Power residue code).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode`

*Formalization.* `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite pair of mod-five and mod-seven power residues indexed by a residue class modulo six.

**Theorem 1.2 (Six residue pairs are distinct).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact finite arithmetic separates all six exponent classes.

**Theorem 1.3 (Mod-five period divides six).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_add_six`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_add_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding six to the exponent leaves the mod-five residue unchanged.

**Theorem 1.4 (Mod-seven period divides six).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_add_six`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_add_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding six to the exponent leaves the mod-seven residue unchanged.

**Theorem 1.5 (Reduce mod-five powers by exponent class).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_reduce_six`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_reduce_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mod-five power equals the power at the exponent remainder modulo six.

**Theorem 1.6 (Reduce mod-seven powers by exponent class).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_reduce_six`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_reduce_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mod-seven power equals the power at the exponent remainder modulo six.

**Theorem 1.7 (Actual residues equal the finite code).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.power_residues_eq_code`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.power_residues_eq_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair of actual power residues factors exactly through n modulo six.

**Theorem 1.8 (Recover the exponent class).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.mod_six_of_equal_power_residues`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.mod_six_of_equal_power_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal mod-five and mod-seven residues imply equal exponent remainders modulo six.

**Theorem 1.9 (Modulo three is constant).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_three`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every base-four power is congruent to one modulo three, so this prime contributes no exponent-class distinction.

**Theorem 1.10 (Prime-two axis exponent).**

Lean statement: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_eq_two_pow_even`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_eq_two_pow_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization-side description is two to the exponent 2n. This is kept distinct from the Zeckendorf word of the integer four-to-the-n read by the DFAO.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_eq_two_pow_even`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_add_six`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_five_reduce_six`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_add_six`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_seven_reduce_six`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.four_pow_mod_three`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.mod_six_of_equal_power_residues`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.powerResidueCode_injective`
- Truth anchor: `D5/S1/Digit/GoldenBase4ResidueBridge.power_residues_eq_code`
