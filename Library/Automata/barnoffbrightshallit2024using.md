---
bibkey: barnoffbrightshallit2024using
authors: Aaron Barnoff and Curtis Bright and Jeffrey Shallit
year: 2024
title: Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals
doi: 10.48550/arXiv.2405.02727
claim: A deterministic finite automaton with output reads the Zeckendorf representation of a power of b and emits the corresponding base-b digit of a quadratic irrational.
strata_touched:
  - D5/S0/Conventions/WDigits
  - D5/S1/Words/ZeckendorfOrder
  - D5/S1/Depth/GoldenContinuedFraction
  - D5/S1/Scale/Fibonacci
license: citation-only
triage: anchor
---

# Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals

Barnoff, Bright, and Shallit construct DFAOs which, given the Zeckendorf
representation of `b^i`, output the `i`th base-`b` digit of the golden ratio and
of other quadratic irrationals. Their automata are minimal over all valid
inputs, but the paper leaves open whether smaller automata could be correct on
the sparse set of inputs of the form `b^i` alone, noting that the question is a
special case of the NP-hard problem of inferring a minimal DFAO from incomplete
data. For the golden ratio in base 4 the required 22-state bound was not
reached; the authors report a single UNSAT determination at 13 states taking
over 25 hours.

This note is the literature anchor for the problem candidate
`Problems/golden-ratio-base4-dfao-minimality.md`.

## Search log

- 2026-08-18: Queried the arXiv Atom API for `id_list=2405.02727`. HTTP 200 with
  `totalResults=1`; the entry resolved to `http://arxiv.org/abs/2405.02727v1`,
  authors Aaron Barnoff, Curtis Bright, and Jeffrey Shallit, published
  2024-05-04, primary category `cs.FL`. The API title renders the base as the
  LaTeX fragment `base-$b$`; this note records the same title with the plain
  letter `b`, and no other token was altered.
- 2026-08-18: The same API response carried `arxiv:doi`
  `10.1007/978-3-031-71112-1_3`, a published version of record. `HEAD
  https://doi.org/10.1007/978-3-031-71112-1_3` returned HTTP 302 redirecting to
  `https://link.springer.com/10.1007/978-3-031-71112-1_3`. The `doi` field above
  nevertheless carries the arXiv-assigned DOI, because the problem candidate
  quotes the arXiv version and the repository binds candidates to that address.
- 2026-08-18: Issued `HEAD https://doi.org/10.48550/arXiv.2405.02727`, which
  returned HTTP 302 redirecting to `https://arxiv.org/abs/2405.02727`.

No literature search for a later resolution of the minimality question was
performed; the open status recorded in the problem candidate is the status
stated in this arXiv version.

## Verified locator

- arXiv: https://arxiv.org/abs/2405.02727
- DOI: https://doi.org/10.48550/arXiv.2405.02727
- Version of record: https://doi.org/10.1007/978-3-031-71112-1_3
