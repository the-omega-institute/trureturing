---
bibkey: evertjurymccullough2026completely
authors: Eric Evert, Michael T. Jury and Scott McCullough
year: 2026
title: "Completely Positive Matrix Products"
doi: 10.48550/arXiv.2607.13251
url: https://arxiv.org/pdf/2607.13251v1#page=22
claim: "Section 5.3, Question 1 asks for the largest Choi-Kraus rank of a jointly completely positive product with a left unit and with a common two-sided unit."
strata_touched:
  - D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2607.13251

Source: https://arxiv.org/pdf/2607.13251v1#page=22

Section 5.3, printed page 22, groups these two clauses under Question 1.

> What is the maximum Choi-Kraus rank of a jcp product with a left unit?
>
> What is the maximum Choi-Kraus rank of a jcp product with a unit?

The Introduction and equation (2.1) specify complex bilinearity and positivity of the joint block amplification at every positive block size. Theorem 2.1 gives the Choi criterion and rectangular Kraus form. Remark 2.2 defines the rank by the minimum number of coefficients. Section 5.3 takes the left unit to be any matrix satisfying the left identity and takes a unit to be one matrix satisfying both identities. The explicit tensor sum of Theorem 2.1 fixes the input-input-output order of the Choi indices. [Definitions and representation](https://arxiv.org/pdf/2607.13251v1#page=4) · [Unit definitions](https://arxiv.org/pdf/2607.13251v1#page=18) · [Weighted Schur example](https://arxiv.org/pdf/2607.13251v1#page=19)

The arXiv record lists the arXiv perpetual, non-exclusive license. This note uses a short quotation to identify the question and cites the remaining paper. [Author record](https://arxiv.org/abs/2607.13251v1) · [License terms](https://arxiv.org/licenses/nonexclusive-distrib/1.0/)

## Attribution

Evert, Jury and McCullough posed Question 1 and supplied the weighted Schur product in Example 5.10. The full-rank perturbation preserving its common unit originated with the `codex-search-a-r420` search seat. The Codex CLI research seat checked that construction with repository prior exposure, and Claude Code orchestrated the research. [Preregistration and producer attribution](https://github.com/the-omega-institute/trureturing/issues/29866)

A separate Codex CLI source qualification matched the clauses, conventions and literature scope. The Codex CLI Lean producer formalized the block positivity, Kraus length and all-dimensional attainment arguments. The Lean matrix-map operations come from the repository's attributed Physlib port and pinned Mathlib. [Kraus representation implementation](../../D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean)
