# Residue Balance at Zero, One, and Infinity

## Abstract

Residue Balance at Zero, One, and Infinity.

**Theorem 1.1 (Residue balance).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the finite principal parts at zero and one and extend over both punctures. The inverse-coordinate bound at infinity gives a bounded entire remainder. Liouville and the first inverse coefficient then give the residue balance.

**Theorem 1.2 (Residue in the iterate coordinate).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The substitution u ↦ −u/(1+u) includes its derivative. Each pole of order at least two contributes only higher poles. A simple pole contributes its original coefficient.

**Theorem 1.3 (Residue balance for three local differentials).**

Lean statement: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The expansions at zero and one use local translated coordinates. The expansion at infinity is for the differential pulled back by inversion, including the derivative of inversion. The three coefficients of the simple poles sum to zero.

## References

- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`
