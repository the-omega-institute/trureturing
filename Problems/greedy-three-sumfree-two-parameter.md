---
slug: greedy-three-sumfree-two-parameter
bibkey: bosma2025using
doi: 10.48550/arXiv.2503.04122
triage: theorem
motivation_gids:
  - D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter
---

# Two-parameter greedy three-sumfree membership

## Problem

This dossier deliberately anchors Conjecture 17 of Bosma et al., *Journal of
Integer Sequences* 28 (2025), Article 25.3.8, printed page 18, which is
the earlier Conjecture 6 of arXiv:2503.04122v1 with its third-seed bound
corrected from `z > g+d` to `z >= g+d`. The caller-supplied reading, 2026-09-07,
quotes this single proposition:

> Let d >= 2. For every g >= d + 1 the greedy 3-sumfree sequence S_{1,g,g+d}
> is characterized as follows: z in S_{1,g,g+d} <=> z in {1, g, 2g+d-1, 2g+d}
> or z >= g+d and z mod 5g+2d in {g+d-2, g+d-1, ..., 2g+d-2}.

Here `d`, `g`, and sequence entries are integers, with positive seeds
`1 < g < g+d`. Every subsequent entry is the least larger positive integer
that is not a sum of three distinct earlier entries, as defined on printed
page 16. Conjecture 16 and the paper's other open items are deliberately out
of scope.

## Motivation

The frozen motivation module supplies a literal least-next-entry construction
of this greedy sequence and its two-parameter membership formula. Recording
the external proposition and its Library identity makes that existing formal
evidence discoverable in the problem pool.

## Gap

The paper presents this as a meta-conjecture supported by Magma computations.
The exact formal membership theorem is already frozen; this layer supplies
the missing literature dossier. It adds no claim binding. The human
identification of the paper's sequence with Lean's `S` remains outside the
machine-checked evidence.

## Route

Use the frozen `conjecture17` under `hd : 2 <= d` and `hg : d+1 <= g`.
Its `S` is membership in `greedyPrefix`, which starts at `[g+d, g, 1]` in
reverse order and prepends `Nat.find (next_exists s)`. `RestrictedThreeSum`
requires `x < y < w`, preserving the paper's distinctness condition.
The proof identifies the explicit periodic set through its restricted
three-sum complement and greedy uniqueness. The caller compared both the
definition and the final formula to the printed source; any subsequent
Scribe claim binding is a separate layer.

## Falsifier

An admissible triple `d >= 2`, `g >= d+1`, `z >= 1` for which the literal
greedy membership and the displayed residue criterion disagree would refute
the anchored proposition. Any alleged witness must use three distinct
previous entries and the least-next-entry rule. No new counterexample search
was run for this dossier.

## Evidence

- Frozen module: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.lean`.
- Public theorem: `conjecture17`; `s_eq_A` is its companion set equality,
  not a second problem anchor.
- Machine-checkable frozen-state receipt:
  `Golden/Frozen/state/D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.lean.json`.
  The worker's `test -f` exited 0 on 2026-09-07.
- Literature reading and locators: `Library/Words/bosma2025using.md`.
  The theory volume's candidate 6.225 is provenance context only.

## Triage

`theorem`. A frozen kernel-verified proof states the exact anchored formula
for the literal greedy sequence throughout the stated parameter range,
subject to the source-to-Lean reading limitation below. This triage is not
a machine-bound resolution claim.

## ASSUMED-UNVERIFIED

- No repository machine verifies that the Lean statement is equivalent to the
  paper's natural-language proposition. The caller-supplied statement and
  definition comparison, 2026-09-07, is a human reading, not a proof of that
  correspondence.
- The API, DOI redirect, printed PDF, and Conjecture 6/17 numbering readings
  are caller-supplied; this worker did not fetch them again. The frozen-state
  receipt was checked for existence; Lean was not rebuilt in this layer.
- No literature search for a later resolution of the conjecture was performed;
  the open status recorded in the problem candidate is the status stated in
  this arXiv version, not an assessment of the subsequent literature.
  The theory volume's 2026-09-06 Shtrezi comparison is an earlier reported
  search, not a search performed for this dossier.
