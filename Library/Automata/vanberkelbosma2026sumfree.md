---
bibkey: vanberkelbosma2026sumfree
authors: Daan van Berkel, Wieb Bosma
year: 2026
title: On t-sumfree sequences
doi: 10.48550/arXiv.2609.16843
url: https://arxiv.org/html/2609.16843v1
claim: Section 6 Theorem 19 establishes the general three-seed difference pattern; Example 20 uses seeds 3,7,13.
strata_touched:
  - D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily
license: citation-only
triage: anchor
---

# On t-sumfree sequences

## Locator

DOI: 10.48550/arXiv.2609.16843

Versioned primary text: https://arxiv.org/html/2609.16843v1

Section 6, Theorem 19 and Example 20, arXiv:2609.16843v1, 15 September 2026.

Theorem 19 assumes natural parameters `1 <= f < g`, `d >= 2`, and
`f+g >= d+1`, excluding `(f,g,d)=(1,2,2)`. It states the eventual
difference pattern for the literal greedy strict three-sumfree sequence
with seeds `(f,g,g+d)`. Its modulus is `5g+2d+3(f-1)`, its entry/difference
preperiod has length `f+g+2`, and each repeated block has `f+g` entries.

The canonical set formulation uses `h=g+d`, `b=f+2g+d-1`, and
`M=3f+5g+2d-3`: the range is `{f,g}` together with `[h,b]` and every
`jM+[h-2,b-2]` for `j>=1`. The characteristic sequence on positive integer
positions has least eventual period `M` and earliest onset `b+1`. The latter
minimality statement is a direct deduction from the interval formula via
its unique cyclic zero-to-one transition and the obstruction at `b`.

This is a formal adaptation of an established theorem. No open-problem
resolution, global priority claim, or author agreement is asserted.
