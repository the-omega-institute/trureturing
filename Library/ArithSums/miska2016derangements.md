---
bibkey: miska2016derangements
authors: Piotr Miska
year: 2016
title: Arithmetic Properties of the Sequence of Derangements and its Generalizations
doi: 10.1016/j.jnt.2015.11.014
claim: The paper records the identity v_2(D_n) = v_2(n-1) for derangement numbers and studies perfect-power equations for the sequence.
strata_touched:
  - D5/S3/Arith/Derangements/DerangementTwoAdicValuation
license: citation-only
triage: anchor
---

# Arithmetic Properties of the Sequence of Derangements and its Generalizations

Piotr Miska studies arithmetic properties of the derangement sequence. The
paper explicitly records the identity `v_2(D_n) = v_2(n - 1)`. Its discussion
of perfect powers includes Proposition 31, which treats the equation
`D_n = p^k` with a fixed prime base.

The repository theorem is independently derived from Mathlib's recurrence and
parity facts. This note supplies mathematical context rather than attestation
for the Lean proof. In particular, the repository's natural-base statement
also allows composite and zero bases and is not attributed verbatim to the
paper.

## Search log

- 2026-09-10: Checked arXiv `1508.01987` for the displayed binary-valuation
  identity and the scope of Proposition 31.
- 2026-09-10: Verified the journal metadata and DOI as *Journal of Number
  Theory* 162 (2016), DOI `10.1016/j.jnt.2015.11.014`.

## Verified locator

- Preprint: https://arxiv.org/abs/1508.01987
- DOI: https://doi.org/10.1016/j.jnt.2015.11.014
