---
bibkey: barnoffbrightshallit2024using
authors: Aaron Barnoff and Curtis Bright and Jeffrey Shallit
year: 2024
title: Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals
doi: 10.48550/arXiv.2405.02727
claim: A deterministic finite automaton with output reads the Zeckendorf representation of a power of b and emits the corresponding base-b digit of a quadratic irrational.
strata_touched:
  - D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality
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

The paper's SAT convention treats the dead state as implicit: an illegal input
is represented by an absent outgoing transition, and the virtual dead state is
not counted among the live states. The delivered module therefore uses a
21-live-state partial DFAO, rather than totalizing the seven transitions which
read a second consecutive `1`. Lean kernel-checks that every zero transition is
defined, no live state has a `1` self-loop, a defined `1` transition makes the
next `1` transition absent, and leading zeroes do not affect evaluation. Finite
table certificates plus structural induction prove agreement with the paper's
22-row table on every admissible Zeckendorf encoding, which is stronger than
agreement only on encodings of `4^i`. This admissible 21-live-state witness
refutes the concrete base-4 minimality claim. The broader general minimality and
uniqueness questions remain unresolved.

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
- 2026-08-23: Queried Crossref for the title and found the same authors' journal
  follow-up, *Computing the base-b representation of quadratic irrationals
  using automata*, Theoretical Computer Science 1071 (2026), article 115843,
  DOI `10.1016/j.tcs.2026.115843`. Crossref returned no abstract, and the
  available metadata does not establish whether that article records the
  specific base-4 reduction from 22 states to 21.

The 2024 source's open status is therefore superseded for this fixed base-4
instance by the repository's kernel-checked partial-machine witness. Literal
byte identity with the unretained raw Walnut outputs remains
`ASSUMED-UNVERIFIED`; the normalized tables are retained in the Evidence
receipt. Whether the 2026 journal article independently reports the same
reduction is also `ASSUMED-UNVERIFIED` because its full text was not available
in this search.

## Verified locator

- arXiv: https://arxiv.org/abs/2405.02727
- DOI: https://doi.org/10.48550/arXiv.2405.02727
- Version of record: https://doi.org/10.1007/978-3-031-71112-1_3
- 2026 journal follow-up: https://doi.org/10.1016/j.tcs.2026.115843
