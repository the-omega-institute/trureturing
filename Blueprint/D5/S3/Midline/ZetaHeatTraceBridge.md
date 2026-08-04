# The Labeled-Zeta Heat-Trace Bridge

## Abstract

The universal heat-abscissa theorem specializes to the existing labeled-zeta Hilbert criterion.

**Theorem 1.1 (Labeled zeta is the prime-axis specialization).**

$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2)\Leftrightarrow\frac12<\Re(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/ZetaHeatTraceBridge.labeled_zeta_mem_iff_via_universal_heat_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SpectralHilbert proves the established criterion by instantiating the general theorem on PrimeAxisTable with logarithmic length and abscissa one. This declaration exposes that single-source relation without adding a second analytic proof.
