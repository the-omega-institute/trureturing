# The Spectral Hilbert Foundation

## Abstract

The square-summable zeta coefficient geometry supplies a spectral foundation for Weil positivity.

**Definition 1.1 (The source pairing completes the coefficient space).**

Lean statement: `D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum`

*Formalization.* `D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum` (`✓ std3`).

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

The coefficient space is the square-summable complex lp space indexed by the canonical prime-axis table. Its source pairing is linear in the first displayed coefficient and conjugate-linear in the second, so it is defined by reversing mathlib's inner-product arguments. The subtype coercion supplies the inclusion into the unrestricted coefficient product.

**Theorem 1.2 (The labeled zeta norm is zeta on the convergence side).**

$\forall s\in\mathbb{C},\ \frac{1}{2}<\Re(s) \Rightarrow \operatorname{ofReal}(\Vert\operatorname{labeledZetaVector}(s)\Vert^{2})=\operatorname{classicalZeta}(2\Re(s))$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

When the real part of the parameter is greater than one half, the squared lp norm of the labeled zeta vector is the classical zeta function evaluated at twice that real part. The right side is independent of the imaginary part. No numerical window certificate is promoted into this exact identity.

**Theorem 1.3 (Labeled zeta membership has the half-density boundary).**

$\forall s\in\mathbb{C},\ \operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2) \Leftrightarrow \frac{1}{2}<\Re(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

The raw labeled coefficient function is square-summable exactly when the spectral parameter has real part greater than one half. Thus the reverse implication includes every parameter on or to the left of the boundary; the statement does not replace that exact p-series criterion by a separate pole or Euler-product claim.

**Theorem 1.4 (The coefficient pairing is the zeta kernel).**

$$\forall s,w\in\mathbb{C},\ 1<\Re(s+\overline{w}) \Rightarrow \sum_{a\in\operatorname{PrimeAxisTable}}\operatorname{labeledZetaCoefficient}(s,a)\overline{\operatorname{labeledZetaCoefficient}(w,a)}=\operatorname{classicalZeta}(s+\overline{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

If the real part of s plus the conjugate of w is greater than one, the raw coefficient pairing sums to the classical zeta function at that parameter. This series theorem keeps only the joint convergence hypothesis and does not add individual square-summability assumptions.

**Theorem 1.5 (The Hilbert pairing is the zeta kernel).**

$$\forall s,w\in\mathbb{C},\ \frac{1}{2}<\Re(s) \land \frac{1}{2}<\Re(w) \Rightarrow \operatorname{sourcePairing}(\operatorname{labeledZetaVector}(s),\operatorname{labeledZetaVector}(w))=\operatorname{classicalZeta}(s+\overline{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

For two actual labeled vectors in the square-summable half-plane, the source-ordered Hilbert pairing is the same zeta kernel. The two individual half-plane hypotheses are typing conditions for the vectors; they imply the raw kernel's joint convergence condition.

**Theorem 1.6 (The mirror is the unique resonance partner).**

$$\forall s,w\in\mathbb{C},\ (s+\overline{w}=1 \Leftrightarrow w=1-\overline{s}) \land (s+\overline{s}=1 \Leftrightarrow \Re(s)=\frac{1}{2}) \land (\frac{1}{2}<\Re(s) \Rightarrow \Re(1-\overline{s})<\frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralHilbert.resonance_partner_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equation s plus conjugate w equals one holds exactly for the mirror partner w = 1 - conjugate s. Self-resonance is exactly the critical line, and a parameter on the square-summable side has its mirror strictly outside that side. This is algebra of the kernel's pole-locus equation; it asserts neither meromorphic continuation nor any location of zeta zeros.

**Remark 1.7 (Hardy-space identification).**

Lean statement: `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner`

*Formalization.* `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner` (`✓ std3`).

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

The coefficient Hilbert space and its zeta reproducing kernel are the classical Hardy-space geometry of Dirichlet series. The repository supplies a typed translation and combined presentation of that known mathematics, not a novelty claim.

## References

- Truth anchor: `D5/S3/Weil/SpectralHilbert.labeled_zeta_inner`
- Truth anchor: `D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel`
- Truth anchor: `D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff`
- Truth anchor: `D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq`
- Truth anchor: `D5/S3/Weil/SpectralHilbert.resonance_partner_spec`
- Truth anchor: `D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum`
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](../../S1/Digit/PrimeAxisEncoding.md)
