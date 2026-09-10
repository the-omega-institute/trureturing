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

## Fetched source receipts

| URL | HTTP | Bytes | SHA-256 |
| --- | --- | --- | --- |
| https://oeis.org/search?q=id:A357512&fmt=json | 200 | 2499 | `6a642473a60423ea755db62d0b7a702f3024bcedaaa5345e94de4ab04dbbcbba` |
| https://oeis.org/A357512/b357512.txt | 200 | 354 | `024cfc8bafbce0b750834b74b2a404a40730fdefb62d96d2f7e3bd78a6157adc` |
| https://arxiv.org/pdf/2403.19503 | 200 | 117335 | `2ce5211f7b973c8eaced9963bc08c472244d86a359f8fee83e7935309540b8b2` |
| https://arxiv.org/pdf/1803.07146 | 200 | 236001 | `04aead65568fdb56bfb3c5a31b4ddd768fa47508eef7eabd622d3457065fc4c2` |
| https://arxiv.org/pdf/1401.0854 | 200 | 291946 | `902b4799157c7f5cae8be1122f3be10937a7f6d3533322da4b633d35154551af` |

OEIS DATA: all 17 terms match exactly. The FORMULA field additionally states
the explicit A target (`n ≡ 1 or 5 mod 6`) as a conjecture, removing any
ambiguity about its attribution to the entry. The comment retains its
existential-prime-set wording.

GitHub authenticated REST code search `A357512 language:Lean`: HTTP 200,
`total_count=0`, `incomplete_results=false`. This is a bounded negative search,
not an assertion about every third-party formalization.

`make lean-cache-ensure`: EXIT=0; `status=seeded`, `method=clonefile`,
`clonefile_attempts=1`, project and mathlib both `warm`, no missing mathlib oleans.
Donor `/Users/chronoai/trureturing`.
