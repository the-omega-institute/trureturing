---
bibkey: camargonishida2026page
authors: Hugo A. Camargo, Mitsuhiro Nishida
year: 2026
title: "Genuine Multi-Entropy of Fully Symmetric Gaussian States"
doi: null
url: https://arxiv.org/abs/2609.30754v2
claim: "Section 6 asks for analytic large-N formulas at the Page and Multi-entropy configurations."
strata_touched:
  - D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2609.30754v2

## Source question

Section 6, printed page 18 (PDF page 19), immediately after equations
(63)–(64):

“It would be very interesting to obtain similar analytic formulas for the
subsystem configurations corresponding to the Page and Multi-entropy times
in the large N regime. This would be particularly important to determine
the behavior of GM₃³ in other relevant subsystem
configurations.”

The source defines the fully symmetric Gaussian precision in equation (30):
diagonal entries are $a\ge1$, and the off-diagonal entry is

$$
e^- = \frac{(a^2-1)(N-2)-\sqrt{a^2-1}\sqrt{(a^2-1)N^2+4(N-1)}}{2a(N-1)}.
$$

The entropy uses the normalized replica contractions of equations (1)–(10).
The Lean owner `GaussianMultiEntropyAsymptotic.GM3` uses their real Gaussian
density kernels and Lebesgue integrals. Its determinant formula is a proved
bridge from those integrals.

Under $N_B=N_C$, the Page configuration of equation (60) is $(2k,k,k)$,
with $N=4k$; the Multi-entropy configuration of equation (61) is $(k,k,k)$,
with $N=3k$. The numbers 12 and 16 printed there refer to the illustrative
total $N=24$.

## Attribution boundary

The source asks for formulas without specifying their coefficients. The
repository answer at replica order three has constants $400/27$ and $27/2$
and, for each fixed $a>1$, errors bounded by $K/N$ with
$K=(2+30/(a^2-1))/12$. These coefficients and bounds are repository
derivations. Their literature novelty and completeness of the literature
screen in issue #22644 remain ASSUMED-UNVERIFIED.

The finite exact checker belongs to
`the-omega-institute/trureturing-experiments`, commit
`25a25360d7d48a4ea64a38b84e690178dba8db47`, at
`docs/reports/camargo-nishida-page-multientropy-large-n/check.py`.
Its SHA-256 is
`4f6007098b18042fc8e4231e28e55428cf6c67a4ab1a73b500ebc6c5d2d3fe88`;
issue #22644 records exit code 0 and `ALL_CHECKS_OK`. These finite checks
provide computational evidence, independently of the quantified Lean proof.
