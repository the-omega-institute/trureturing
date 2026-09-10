# A357512 implementation record

Source: user implementation brief; first-tier OEIS conjecture. Skill: `lean4`.
Producer: Codex implementation seat, single agent, no independent review claimed.
Base: `d6836dd2ae403f006f1f2d6ae5ddef3af56c5e46`; worktree branch: `lane/math/a357512`.

## Target and preregistration

Let `a(n) = sum(k=0..n, k^5 choose(n,k)^2 choose(n+k,k)^2)`.
A: every odd `n` with `3 ∤ n` satisfies `n^4 ∣ a(n-1)`.
B: every prime `p ≥ 5` satisfies `p^4 ∣ a(p-1)`.
A fixes the explicitly suggested `P(2)={3}`; it is stronger than the bare
existence of some finite exceptional prime set. This distinction is retained.
B is an authorized universal fallback, not a finite-instance delivery.

Proposed B escape witness, before numerical or Lean experiments: a binomial
product expansion modulo `p^4` reducing the weighted summand to a polynomial
term and a harmonic correction; cancellation of their complete sum.
For A the corresponding unit-denominator step must also handle indices
divisible by a prime factor of a composite `n`; no such extension is claimed.

Success requires a kernel proof of A or B, repository build and delivery gates,
and an opened PR. A counterexample requires a kernel witness. A blocked result
must identify actual Lean goals, not only unsuccessful library searches.
Numerical disagreements with the brief trigger its explicit stop condition.

## Repository search

`rg -n 'A357512|[Aa]p[eé]ry|Supercongruence|supercongruence' D5 --glob '*.lean'`
found `A375178Supercongruence.lean` and unrelated zeta-value prose.
The full A375178 module was read: 23 lines beginning `private ` (including
private definitions/abbreviations); the public surface is `a` and
`supercongruence`. Its sole public theorem concerns a different binomial cube
sum. Its private helper proofs inform technique but provide no public GID.
`D5/S3/ArithSums` contains 3 files at this base.

## Pending evidence and nonclaims

Mathlib and third-party searches, paper full texts, independent numeric rerun,
and Lean proof attempts are pending. No target is proved or refuted yet.
No novelty claim, search-complete claim, freeze, coverage, CI success, or
independent consensus is asserted. Unopened external sources remain
`ASSUMED-UNVERIFIED` until a receipt and reading account replace this status.
