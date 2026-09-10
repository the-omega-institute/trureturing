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

## Numerical probe

Independent Python `math.comb` / integer calculation reproduces all supplied
readings: in `3 ≤ n ≤ 139`, 46 odd nonmultiples of 3 pass modulo `n^4`;
all 23 odd multiples of 3 fail. All 28 primes in `5 ≤ p ≤ 113` pass modulo
`p^4`; 27 fail modulo `p^5` (the sole fifth-power pass is `p=7`). The six
specified composites all pass. The first 17 calculated terms start
`0,4,1188,126144,10040000,682492500`; fetched OEIS identity comparison is pending.
The exact probe output is `numeric-probe.json` in the runner attempt directory.
These finite checks are probes only, not mathematical progress on A or B.

Pinned Mathlib: `v4.33.0`, revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Text searches for Apéry/supercongruence and choose/ModEq found Lucas congruences
modulo a prime, plus generic factorial/binomial identities; no A357512 target.
Public helper candidates include `Nat.add_one_mul_choose_eq`,
`Nat.descFactorial_eq_factorial_mul_choose`, and `Nat.choose_mul_succ_eq`.
