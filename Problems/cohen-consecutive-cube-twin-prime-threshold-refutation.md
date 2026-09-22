---
slug: cohen-consecutive-cube-twin-prime-threshold-refutation
bibkey: cohen2025cyclic
doi: 10.48550/arXiv.2508.08335
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28
---

# Cohen Conjecture 28

## Problem

Cohen, Journal of Integer Sequences 28 (2025), Article 25.4.7, Section 2.5,
Conjecture 28, asserts that there are at least two twin-prime pairs between
every pair of consecutive positive cubes and that the count eventually
exceeds every positive integer. Its printed threshold table further states
`N(10) = 11`: for every natural `n >= 11`, there are at least ten such pairs
strictly between `n^3` and `(n+1)^3`.

The formal `claim28` retains both general assertions and all seventeen printed
threshold clauses. The theorem `result28` proves its negation.

## Motivation

The printed threshold is part of the named conjecture, but the count sequence
printed immediately before it gives nine twin-prime pairs for `n = 11`.
Checking that count settles the full conjunction without changing its other
clauses.

## Gap

Issue #9016 records the source and scoped literature search. The published JIS
article and arXiv:2508.08335 state Conjecture 28 with `N(10) = 11`; the searched
repository, open pull requests, and MathDB queries contained no settlement of
this threshold. The search does not establish exhaustive publication priority.

## Route

Define `twinPairCount n` as the number of natural numbers `p` with
`n^3 < p`, `p + 2 < (n+1)^3`, and both `p` and `p + 2` prime. Kernel
evaluation gives `twinPairCount 11 = 9`. Instantiating the printed threshold
clause at `n = 11` would require `10 <= 9`, a contradiction.

## Falsifier

The refutation would fail if the open-interval interpretation disagreed with
the paper's examples, if the filtered count at `n = 11` were not nine, or if
`claim28` omitted or weakened the printed `N(10) = 11` clause. The formal
definition, checked examples, and theorem retain these three links.

## Evidence

- Lean theorem:
  `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28`.
- Freeze event:
  `sha256:252f3161cf9445d1de24352155da81e6de9872de419ef43dcc9deaa228547d6b`.
- Module statement identity:
  `sha256:d475fe3507eb9b1372aaea14defe909c30cd93c2ff7454a84ec4046863029fb1`.
- Result declaration identity:
  `sha256:6a1a9b0c9d12e06f7e1e4b66535d95cad610cc36f8db62234f09ecf5311330d2`.
- `proof_shape: bind-only`; `escape_witness: none`;
  `admission_basis: open-problem-resolution (issue #9016)`.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The certified count refutes Conjecture 28 as printed. It does not
assert a corrected value of `N(10)` or settle the eventual-growth conjunct in
isolation.

## ASSUMED-UNVERIFIED

The scoped literature search does not establish exhaustive publication
priority. The JIS errata archive and Google Scholar were not exhaustively
checked.
