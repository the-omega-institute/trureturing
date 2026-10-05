---
bibkey: pyvovarov2026baezduarteremarks
authors: "Alexandre Pyvovarov"
year: 2026
title: "A few remarks on the Baez-Duarte Criterion"
doi: null
url: "https://arxiv.org/abs/2607.12084v3"
claim: "The preprint's final section explicitly retains a global bilinear remainder estimate as unresolved; its truncated norm formulas do not supply an unconditional RH proof."
strata_touched: []
license: "Citation only; no source text is reproduced."
triage: anchor
---
<!-- GID: D5/L/Weil/pyvovarov2026baezduarteremarks -->
# Exponential approximants and the retained remainder

The retained primary version is arXiv:2607.12084v3, updated
2026-07-21T15:54:34Z. Its 66-page PDF has SHA256
`c85660d6c2bcbca5458e82cb048afd8c62311c216fd1fe88cbea8d6ffb4c48c7`.
The versioned arXiv metadata supplies no DOI or journal reference.
The source TeX and PDF page locators were inspected for the concluding
remainder statement. Mathematical symbols use the TeX source where PDF
extraction reports missing font-encoding support.

The preprint studies exponentially damped Möbius combinations of balanced
floor-function probes. These are Hilbert approximation vectors, distinct from
the original Newton coefficients $c_k$ even though both involve Báez-Duarte
criteria. Its notation $\rho_3$ denotes a deleted analytic remainder, not the
project's atomic Fibonacci substitution $\rho$.

Corollary 9.38, PDF page 63, lists four sufficient estimates in (9.39) and a
single combined boundedness condition in (9.40). Section 9.6, PDF pages
63–64, explicitly states that (9.40) remains unresolved and that boundedness
cannot be transported from the truncated quantity $\mathcal F_{[3]}$ to the
complete quantity $F$ before the total remainder $\mathcal E_{\rho_3}$ is
controlled. The source also distinguishes existing Möbius–cotangent
power-saving estimates with other summation regions and weights from this
required combined estimate.

This note records that explicit limitation as prior-art evidence. It does not
certify every theorem or intermediate algebraic formula in the preprint, and
none is imported as a Lean-verified result. A growing upper bound for a
truncated norm is not the boundedness estimate required for the full
approximation. Separately estimating the four components is sufficient but
can be stronger than the combined condition, because cancellation can occur
between them.

For the actual FIB transport, an available absolute bound can pay a source
tail only at the scale it explicitly reaches. It cannot be used to declare a
remaining signed principal sum bounded. The distinct natural-prefix
obstruction and its subsequence boundary remain those of
[Báez-Duarte 2000](baezduarte2000natural.md). Neither this preprint nor the
source-tail interface establishes full Robin, actual critical FIB growth,
or RH. This versioned check is a bounded literature comparison, not an
exhaustive account of all current research.
