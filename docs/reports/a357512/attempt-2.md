# A357512 attempt 2

Skill: `lean4`. Producer: Codex implementation seat, single agent; no independent
review or consensus claimed. Starting commit: `4b1a9ba824` on `lane/math/a357512`.
The user reopens only A: every odd natural `n` with `3 ∤ n` satisfies
`n^4 ∣ a(n-1)`. B remains excluded by the named A17.2 admission conditions in
the preceding report. No B reproof, upstream-code import, or upstream contact
is authorized or planned.

## Search and proposed witness

The complete existing A357512 module was read, including its private lemmas.
Its general `sum_factorization` is the starting point. The original 122 lines
are retained. Repository search with `rg` for `A357512`, `A357513`, Apéry,
binomial congruences, and squared binomial products finds no composite target.
The public surface of `A375178Supercongruence` was read: its only theorem is
a prime-index binomial-cube congruence, with no general summation helper.
The pinned Mathlib search finds `Data/Nat/Choose/Lucas.lean`, concerning
congruences modulo a prime, and no A357512 theorem. These are bounded search
results, not an exhaustive-search claim. Further third-party checks follow.

Proposed A witness before new probes: a denominator-cleared whole-sum identity
or congruence for the reduced sum, valid also at nonunit indices, yielding its
second factor `n^2` after cancelling only constants coprime to `n` (2 and 3).
The prime induction's cancellation of `k` cannot be extended to composites;
attempt 1 already records kernel counterexamples to that intermediate claim.
The stopping criteria are the user's A proof and delivery, a kernel witness
refuting A, or a concrete failed Lean goal and sharper remaining subclaim.

## Nonclaims

No proof of A, new finite-case progress, counterexample, freeze, coverage, PR,
CI success, or novelty is claimed at this checkpoint. No theory volume or atom
will be created. Unopened external pages are `ASSUMED-UNVERIFIED`.
