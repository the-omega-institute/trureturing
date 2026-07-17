# The Spectral Hilbert Foundation

## Definition: The source pairing completes the coefficient space

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum` `✓ std3`

The coefficient space is the square-summable complex lp space indexed by the canonical prime-axis table. Its source pairing is linear in the first displayed coefficient and conjugate-linear in the second, so it is defined by reversing mathlib's inner-product arguments. The subtype coercion supplies the inclusion into the unrestricted coefficient product.

## Theorem: The labeled zeta norm is zeta on the convergence side

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq` `✓ std3`

When the real part of the parameter is greater than one half, the squared lp norm of the labeled zeta vector is the classical zeta function evaluated at twice that real part. The right side is independent of the imaginary part. No numerical window certificate is promoted into this exact identity.

## Theorem: Labeled zeta membership has the half-density boundary

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff` `✓ std3`

The raw labeled coefficient function is square-summable exactly when the spectral parameter has real part greater than one half. Thus the reverse implication includes every parameter on or to the left of the boundary; the statement does not replace that exact p-series criterion by a separate pole or Euler-product claim.

## Theorem: The coefficient pairing is the zeta kernel

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel` `✓ std3`

If the real part of s plus the conjugate of w is greater than one, the raw coefficient pairing sums to the classical zeta function at that parameter. This series theorem keeps only the joint convergence hypothesis and does not add individual square-summability assumptions.

## Theorem: The Hilbert pairing is the zeta kernel

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner` `✓ std3`

For two actual labeled vectors in the square-summable half-plane, the source-ordered Hilbert pairing is the same zeta kernel. The two individual half-plane hypotheses are typing conditions for the vectors; they imply the raw kernel's joint convergence condition.

## Theorem: The mirror is the unique resonance partner

Provenance: `repo-derived`

Statement: `D5/S3/Weil/SpectralHilbert.resonance_partner_spec` `✓ std3`

The equation s plus conjugate w equals one holds exactly for the mirror partner w = 1 - conjugate s. Self-resonance is exactly the critical line, and a parameter on the square-summable side has its mirror strictly outside that side. This is algebra of the kernel's pole-locus equation; it asserts neither meromorphic continuation nor any location of zeta zeros.

## Remark: Hardy-space identification

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner` `✓ std3`

The coefficient Hilbert space and its zeta reproducing kernel are the classical Hardy-space geometry of Dirichlet series. The repository supplies a typed translation and combined presentation of that known mathematics, not a novelty claim.
