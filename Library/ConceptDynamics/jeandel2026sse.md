---
bibkey: jeandel2026sse
authors: Emmanuel Jeandel
year: 2026
title: Combinatorial Search for Strong Shift Equivalence
doi: null
url: https://arxiv.org/abs/2609.03567v1
claim: The archived v1 TeX source asks whether the Baker polynomial pair is strong shift equivalent over the semiring of polynomials with nonnegative integer coefficients; the question is after the rendered document ends.
strata_touched: []
license: citation-only
triage: anchor
---

# Baker polynomial draft question

The archived source `SSE.tex`, lines 731-738, asks whether the matrices
with rows `(1,t+1),(t,1)` and `(1,t^2+t),(1,1)` are strong shift equivalent
over the semiring of polynomials with nonnegative integer coefficients.
The rendered document ends at line 628. This is an externally authored
archived draft question, not a rendered or numbered published problem.
The source SHA-256 is
`a8cdbd3f4181bd10402710aa28c2b71c2e4dd88978eaee0c0ad257f50572b4da`.

`BakerPolynomialObstruction.no_lag` excludes every natural lag for this
literal pair over `Polynomial Nat`. Its `no_exchange_chain` consequence
uses the existing rectangular chain-to-lag theorem and allows arbitrary
finite intermediate dimensions. The proof combines the irreducibility
of `1-X-X^2` over the rationals, determinant-degree parity, and
coefficientwise noncancellation. The irreducibility input is reused from
the repository's multinacci theorem at order two; the degree obstruction
is the substantive argument for this pair.

This attribution concerns the question's source. It makes no claim that
the argument is the author's, that no earlier proof exists in the full
literature, that this is a unique solution, or that it settles the general
integer-evaluated Baker problem. Real-coefficient polynomial rings are
outside the formal statement.

## Verified locator

Primary record: https://arxiv.org/abs/2609.03567v1.
Archived source: https://arxiv.org/src/2609.03567v1, member `SSE.tex`,
question lines 731-738; end of rendered document at line 628.
