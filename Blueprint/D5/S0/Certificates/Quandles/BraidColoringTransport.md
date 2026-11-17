# Braid Coloring Transport

## Abstract

Rack crossings give invertible coloring transport and satisfy the Yang--Baxter relation.

**Definition 1.1 (Rack crossing).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing`

*Formalization.* `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local crossing sends a pair of rack colors to the acted color and the over-crossing color.

**Definition 1.2 (Inverse rack crossing).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv`

*Formalization.* `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse transport uses the rack inverse action and recovers the two boundary colors.

**Definition 1.3 (Crossing equivalence).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv`

*Formalization.* `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The crossing and its inverse form an equivalence of the two-color boundary space.

**Theorem 1.4 (Crossing equivalence evaluation).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the bundled equivalence is the rack crossing map.

**Theorem 1.5 (Inverse after crossing).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv_crossing`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying inverse transport after a crossing returns the original pair.

**Theorem 1.6 (Crossing after inverse).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_crossingInv`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_crossingInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the crossing after inverse transport returns the original pair.

**Theorem 1.7 (Yang--Baxter transport).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_yang_baxter`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_yang_baxter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three successive rack crossings obey the Yang--Baxter relation, by self-distributivity.

**Theorem 1.8 (Crossing preserves finite cardinality).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_card_bijective`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_card_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite rack, the crossing is a bijection of the finite pair space and therefore preserves its cardinality.

**Theorem 1.9 (Inverse equivalence evaluation).**

Lean statement: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_symm_apply`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_symm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the inverse of the bundled equivalence is the inverse rack crossing map.

## References

- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_apply`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingEquiv_symm_apply`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossingInv_crossing`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_card_bijective`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_crossingInv`
- Truth anchor: `D5/S0/Certificates/Quandles/BraidColoringTransport.crossing_yang_baxter`
