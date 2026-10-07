---
bibkey: coffey2006baezduarteextensions
authors: "Mark W. Coffey"
year: 2006
title: "On the coefficients of the Baez-Duarte criterion for the Riemann hypothesis and their extensions"
doi: null
url: "https://arxiv.org/abs/math-ph/0608050v2"
claim: "Parametrized Baez-Duarte coefficients and their ordinary generating-function binomial transform are established prior tools; generalizing coefficient notation does not provide critical signed decay."
strata_touched: []
license: "Citation only; no source text is reproduced."
triage: anchor
---
<!-- GID: D5/L/Analytic/coffey2006baezduarteextensions -->
# Parametrized coefficients and binomial transforms

The retained primary version is arXiv:math-ph/0608050v2, updated
2006-09-07T19:52:20Z. Its 24-page PDF has SHA256
`031aae16827824dbf864c790e82bda6a5b7dd3f27081c8234d7da932712c7b85`.
The versioned arXiv metadata supplies no DOI or journal reference.
PDF page locators were checked against the source TeX; the PDF extraction
reports missing font-encoding support, so mathematical symbols are read from
the TeX source.

Equation (1) retains the original coefficients

$$
c_k=\sum_{j=0}^k(-1)^j\binom kj\frac1{\zeta(2j+2)}.
$$

Proposition 7, PDF page 17, equation (63), records the ordinary
generating-function transformation for the parametrized reciprocal-Hurwitz
coefficients $c_k(b,a)$, defined by equation (19). Its proof, equation (65),
reorders their finite binomial sums into a generating series. This is an
existing tool, not a new FIB result. The paper's stated generating-function
domain is retained as a source statement; this note does not independently
certify analytic continuation throughout that domain.

Proposition 4, PDF pages 11–12, equations (41)–(43), treats a general
Dirichlet series with a factor $(pj+p-1)$ in its coefficients and a factor
$1/(s-1)$ in the expansion. Those factors distinguish that representation
from the original reciprocal-zeta Newton coefficients. It cannot be applied
by dropping either factor. The general analytic-function proposal immediately
preceding Proposition 4 is explicitly labeled Conjecture 1.

For the project's actual $e=\mu*\beta$, the coefficient at index $k$ is
formed from the same signed kernel $n^{-2}(1-n^{-2})^k$. The passage from
$n=dm$ to a finite binomial average of the original $c_j$ is a source-scale
application of the classical binomial theorem. A bound for that average must
still be supplied with its index weights, and the complete $d$ tail must be
retained. Neither this paper's generalized notation nor its generating
transform supplies unconditional $k^{-3/4+\varepsilon}$ decay for the actual
FIB coefficients.

The original RH criterion is reused from
[Báez-Duarte 2003](baezduarte2003criterion.md). This source note makes no
claim of a new criterion, exhaustive literature coverage, or originality of
binomial transforms. It records primary-source scope rather than a Lean
verification of the source paper.
