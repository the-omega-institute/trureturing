---
bibkey: thio2026tight
authors: Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur
year: 2026
title: Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems
doi: null
url: https://arxiv.org/abs/2611.04009v1
claim: Appendix A asks whether only coordinate supports D=delta*d can saturate the fixed-purity Shannon bound.
strata_touched:
  - D5/S3/Quantum/Magic/ThioSaturationRefutation
license: citation-only
triage: anchor
---

# Fixed-purity saturation and the noisy Strange qutrit

Thio et al., arXiv:2611.04009v1, Eq. (9), defines coordinates by
Q_lambda(rho)=Tr(rho S_lambda^dagger). Eq. (17) defines the KD frame as the
ordered product of the two basis projectors. For mutually unbiased bases,
every squared overlap is 1/d. Eqs. (19)–(20) define the odd-dimensional Gross
frame by phase-adjusted cyclic displacements, their normalized sum and
unitary conjugation. Tensor systems use the product of the local frames.
The middle inequality in Eq. (21), restated in Eq. (39), is
H(Q) >= -ln(Tr(rho^2)) + ln(d), with natural logarithms.

Appendix A, A1.p8.1, states:
“Whether these are the only possible D-values for which saturation occurs is not clear in general.”
The preceding values are D=delta*d, 1<=delta<=d. D counts nonzero coordinates.
Purity ranges over the closed interval [1/d,1]. This question concerns the
purity-dependent middle bound; it does not require equality in the pure-state
global bound H>=ln(d). Lemma 2 has a separate MUB-KD convex-hull hypothesis.

The phase-point and noisy Strange constructions are existing literature:

- D. Gross, *Hudson's Theorem for finite-dimensional quantum systems*,
  arXiv:quant-ph/0602001v3, supplies odd-dimensional parity, phase-point
  operators and the antisymmetric qutrit projector. The mixed-state example
  with six equal nonzero Wigner coefficients is distinct from support eight.
- Shiroman Prakash and Rishabh Singhal, *A Search for High-Threshold Qutrit
  Magic State Distillation Routines*, arXiv:2408.00436v2, Section II.B,
  Eqs. (II.14)–(II.19), supplies the depolarized Strange family. Its Eq. (II.15)
  contains differing signs in the distinguished cases entry and adjacent
  matrix; the source convention used here is Thio's explicit operator sum.
- Shiroman Prakash, *Magic State Distillation with the Ternary Golay Code*,
  arXiv:2003.02717v2, Section 3, Eqs. (14), (21)–(24), and Sections 5 and 7,
  supplies the Strange family and the Wigner-positivity boundary.
- Enrico Bozzetto and Jonte R. Hance, *Classical Limit: Dissipation of Spekkens'
  Generalised Contextuality under Decoherence*, arXiv:2605.09558v3,
  Section III.2, Eqs. (7)–(9), Table 2 and Section XI.4, discusses
  depolarization and the Strange-state Wigner-positivity point.

The application uses rho=(3I-P)/8, where P|j>=|-j> in dimension three.
This is a known depolarized antisymmetric qutrit state, rather than a new
state construction. Its eight-coordinate saturation addresses the particular
Thio support question. No priority or global novelty claim, or classification
of all attaining states at every purity, is made. The primary preprint is distributed under CC BY 4.0. The citations and brief
quotation are attribution; no third-party source code or document is copied.

## Verified locator

Source: https://arxiv.org/abs/2611.04009v1

Primary source version: arXiv:2611.04009v1. The locators for the preceding
whole-source reading are Eqs. (9), (17), (19)–(21) and (39), the stated tensor
extensions, Appendix A A1.p8.1 with its preceding support values and closed
purity interval, and the separately scoped Lemma 2. The Appendix A question
and quotation retain their full scope as stated above.

Supplier-source locators for the attributed ingredients above:

- Gross, arXiv:quant-ph/0602001v3: odd-dimensional parity, phase-point
  operators, the antisymmetric qutrit projector and the distinct six-support
  mixed-state example.
- Prakash–Singhal, arXiv:2408.00436v2: Section II.B, Eqs. (II.14)–(II.19),
  including the Eq. (II.15) sign discrepancy described above.
- Prakash, arXiv:2003.02717v2: Section 3, Eqs. (14), (21)–(24), and
  Sections 5 and 7.
- Bozzetto–Hance, arXiv:2605.09558v3: Section III.2, Eqs. (7)–(9),
  Table 2 and Section XI.4.
