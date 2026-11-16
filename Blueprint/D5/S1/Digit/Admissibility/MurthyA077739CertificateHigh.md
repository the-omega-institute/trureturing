# Murthy A077739 certificate rows 500 through 999

## Abstract

Consumed decimal-block certificate rows for Murthy A077739, indices 500 through 999.

**Definition 1.1 (Ordered multiplier-count data).**

Lean statement: `D5/S1/Digit/Admissibility/MurthyA077739CertificateHigh.entries`

*Formalization.* `D5/S1/Digit/Admissibility/MurthyA077739CertificateHigh.entries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry i is the list of multiplier-count pairs for n=500+i. A pair (j,c) prescribes c copies of the decimal block jn. The classification module concatenates the low and high arrays in index order to form its private certificateData. It checks the exact residual digit sum for every nonexceptional index below 1000 by kernel reduction, then uses the general certificate_sound and from_blocks proofs to obtain a witness. The literal rows alone prove neither admissibility nor nonexistence. These consumed data definitions supply no independent mathematical result or external problem resolution.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/MurthyA077739CertificateHigh.entries`
