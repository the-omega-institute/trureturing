---
slug: cohen-consecutive-cube-cousin-prime-threshold-refutation
bibkey: cohen2025cyclic
doi: 10.48550/arXiv.2508.08335
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29
---

# Cohen Conjecture 29

## Problem

Cohen, Journal of Integer Sequences 28 (2025), Article 25.4.7, Section 2.5,
Conjecture 29, asserts that there are at least two cousin-prime pairs between
consecutive cubes for every natural `n > 1` and that the count eventually
exceeds every positive integer. Its printed threshold table further states
`N(8) = N(9) = N(10) = 12`: every natural `n >= 12` has at least eight,
nine, and ten such pairs, respectively.

The formal `claim29` retains both general assertions and all ten printed
threshold clauses. The theorem `result29` proves its negation.

## Motivation

The printed thresholds are part of the named conjecture, but the count
sequence printed immediately before them gives seven cousin-prime pairs for
`n = 12`. Checking that count settles the full conjunction while preserving
the paper's requirement that the two primes be consecutive.

## Gap

Issue #9016 records the source and scoped literature search. The published JIS
article and arXiv:2508.08335 state Conjecture 29 with all three thresholds at
12; the searched repository, open pull requests, and MathDB queries contained
no settlement of these thresholds. The search does not establish exhaustive
publication priority.

## Route

Define `cousinPairCount n` as the number of natural numbers `p` with
`n^3 < p`, `p + 4 < (n+1)^3`, prime endpoints, and no prime among `p + 1`,
`p + 2`, and `p + 3`. Kernel evaluation gives `cousinPairCount 12 = 7`.
Instantiating the printed `N(8) = 12` clause at `n = 12` would require
`8 <= 7`, a contradiction.

## Falsifier

The refutation would fail if cousin pairs did not require consecutive primes,
if the filtered count at `n = 12` were not seven, or if `claim29` omitted or
weakened the printed `N(8) = 12` clause. The formal definition, checked
examples, and theorem retain these three links.

## Evidence

- Lean theorem:
  `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29`.
- Freeze event:
  `sha256:252f3161cf9445d1de24352155da81e6de9872de419ef43dcc9deaa228547d6b`.
- Module statement identity:
  `sha256:d475fe3507eb9b1372aaea14defe909c30cd93c2ff7454a84ec4046863029fb1`.
- Result declaration identity:
  `sha256:db584f0741fdb5011858ba4dfb9af452e41ff850d66da49abad77cd9b6405557`.
- `proof_shape: bind-only`; `escape_witness: none`;
  `admission_basis: open-problem-resolution (issue #9016)`.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The certified count refutes Conjecture 29 as printed. It does not
assert corrected threshold values or settle the eventual-growth conjunct in
isolation.

## ASSUMED-UNVERIFIED

The scoped literature search does not establish exhaustive publication
priority. The JIS errata archive and Google Scholar were not exhaustively
checked.
