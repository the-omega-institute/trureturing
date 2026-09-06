# Support-local affine moment reconstruction

## Abstract

Pointwise affine reconstruction on the original support justifies retaining fewer coordinates. The existing replay preserves this support, so the omitted original coordinates are recovered exactly.

**Definition 1.1 (Affine feature readout).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.affineCoefficient`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.affineCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An offset and rational coefficient vector define a query on the actual original features.

**Theorem 1.2 (Reconstruct an affine expectation).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_affineCoefficient`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_affineCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization transports the offset, while finite sum interchange transports the feature combination.

**Theorem 1.3 (Ignore zero-mass discrepancies).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_congr_on_active`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_congr_on_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise equality is required only at nonzero atoms of the evaluated vector.

**Theorem 1.4 (Recover the checked input conditions).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkCompression_input_probability`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.checkCompression_input_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successful compression necessarily passed the existing initial nonnegativity and normalization checks.

**Definition 1.5 (Data-only coordinate presentation).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.AffinePresentation`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.AffinePresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Records selected original coordinates, offsets and reconstruction coefficients. Selection need not be independent, so its size certifies only an upper dimension bound.

**Definition 1.6 (Use original feature coordinates).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.selectedFeature`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.selectedFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced coordinates are selected from the original coefficient array without changing their values.

**Definition 1.7 (Pointwise reconstruction contract).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.ValidPresentation`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.ValidPresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every original coefficient must be reconstructed on every active input atom.

**Definition 1.8 (Exact presentation checker).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite rational equality checks validate the proposed reconstruction. A small averaged residual is insufficient.

**Theorem 1.9 (Reflect presentation acceptance).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation_eq_true_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acceptance is equivalent to the support-local coefficient equalities used by the proof.

**Definition 1.10 (Replay with the reduced support budget).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression`

*Formalization.* `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After validating reconstruction, the unchanged replay checks only selected moments and requires support at most the selected count plus one.

**Theorem 1.11 (Preserve all original moments).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The returned normalized nonnegative law has contained support, obeys the reduced support bound and preserves every original feature expectation.

**Theorem 1.12 (One compression for all affine queries).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_preserves_affine_family`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_preserves_affine_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accepted compression is fixed before arbitrary affine query coefficients are chosen. No new compression is selected per query.

**Theorem 1.13 (Three coordinates, two output atoms).**

Lean statement: `D5/S0/Certificates/RationalAffineMomentCompression.affine_reconstruction_replay_example`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalAffineMomentCompression.affine_reconstruction_replay_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A closed rational example retains a mean and two affine transforms of that mean through a one-coordinate replay.

## References

- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.AffinePresentation`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.ValidPresentation`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.affineCoefficient`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.affine_reconstruction_replay_example`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_preserves_affine_family`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkAffineCompression_sound`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkCompression_input_probability`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.checkPresentation_eq_true_iff`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_affineCoefficient`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.linearObjective_congr_on_active`
- Truth anchor: `D5/S0/Certificates/RationalAffineMomentCompression.selectedFeature`
- Dependency: [D5/S0/Certificates/RationalMomentReplay](RationalMomentReplay.md)
