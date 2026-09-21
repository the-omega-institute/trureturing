---
bibkey: byun2026unimodality
authors: Seok Hyun Byun and Svetlana Poznanović
year: 2026
title: Unimodality and log-concavity of generalized Glasby-Paseman sequences
doi: null
url: https://arxiv.org/abs/2604.14639v1
claim: Conjecture 1.1(d) specifies the exact asymptotic maximum of the powered-sum ratio (1.4) for every fixed positive real a and positive integer l; the paper proves the case l=2 and a=1.
strata_touched:
  - D5/S3/AnalyticClosure/BinomialMovingEndpoint
  - D5/S3/AnalyticClosure/BinomialMaximumLocalization
  - D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization
  - D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Analytic/byun2026unimodality -->
# Generalized Glasby–Paseman maximum

The source is the version-1 preprint dated 16 April 2026. Page 2, equation
(1.4), defines, for positive integers m,l and a positive real a,

\[
R_{m,l,a}(r)=
\frac{\sum_{i=0}^{r}(\binom mi a^i)^l}
     {\sum_{i=0}^{r}(\binom ri a^i)^l},\qquad 0\le r\le m.
\]

Conjecture 1.1(d) on the same page states that its maximum is asymptotic to

\[
\frac{\sqrt l}{\sqrt{2\pi m}}
\frac{\sqrt{1+2a}(1+a)a^{(l-2)/2}}{(1+a)^l-1}
\left(\frac{1+2a}{1+a}\right)^{(m+1/2)l}.
\]

Footnote 1 defines “asymptotically” as the ratio tending to one as m tends
to infinity. The subtraction in (l-2)/2 is real subtraction, so l=1 gives
the exponent -1/2. The maximum ranges over all integer indices including
0 and m; ties do not change its value.

The paragraph immediately after Conjecture 1.1 credits prior results for
l=a=1 and for l=1 with positive integer a. Theorem 1.2 proves the l=2,a=1
case in this paper, with the asymptotic in equation (1.6). These cases are
prior results, not separate new candidate resolutions.

The source also conjectures unimodality (a), eventual log-concavity (b),
and an exact three-position unique-peak restriction for integer a (c).
The repository maximum target concerns only (d), for the full real-a
parameter range. Its slope localization does not establish (c).

## Verified locator

- Versioned source: https://arxiv.org/abs/2604.14639v1
- Source body: https://arxiv.org/pdf/2604.14639v1, page 2, equation (1.4),
  Conjecture 1.1(d), footnote 1, and Theorem 1.2(c).
- Registration and bounded source audit:
  https://github.com/the-omega-institute/trureturing/issues/9357
- Candidate implementation:
  https://github.com/the-omega-institute/trureturing/pull/9399

The source audit supplied with #9357 reports that the arXiv abstract still
listed v1 on 2026-09-21 at 21:46 UTC. The versioned abstract and pages 1–3
were also consulted for this note on 2026-09-21 UTC. That identifies the
source and its stated conjecture; it does not establish worldwide priority
or rule out an uninspected settlement. This note is not a typed resolution
claim or evidence of canonical Freeze.
