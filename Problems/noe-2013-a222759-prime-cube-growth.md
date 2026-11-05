---
slug: noe-2013-a222759-prime-cube-growth
bibkey: noe2013a222759
doi: null
url: https://oeis.org/A222759
triage: theorem
motivation_gids:
  - D5/S3/Arith/PrimeRemainders/OeisA222759Growth.result
---

# The complete first growth assertion of OEIS A222759

## Problem

T. D. Noe, OEIS A222759, revision 12, November 2, 2024.
The NAME is:

> Conjectured number of primes p for which binomial(n*p,p) (mod p^3) does not equal n.

The entire first COMMENT is:

> It appears that, for k > 2 and n >= prime(prime(k)^3), then a(n) >= k.

Let $P(j)$ be the one-based $j$-th prime for positive $j$, with $P(1)=2$.
For every integer $k\ge3$ and every integer $n\ge1$ with
$n\ge P(P(k)^3)$, the event is the existence of $k$ pairwise distinct
positive primes $q_1,\ldots,q_k$ such that
$\binom{nq_i}{q_i}\bmod q_i^3\ne n$ for every $i$.
The remainder is the least nonnegative integer remainder, compared with
$n$ itself. The threshold includes equality and cubes $P(k)$ inside the
outer prime index. The event asserts at least $k$ witnesses without
assuming finiteness of the entire set satisfying the predicate.

The formal domain is exactly the positive integer domain represented by
naturals with $3\le k$ and $1\le n$. An injection $q:\mathrm{Fin}(k)\to
\mathbb N$ supplies distinct witnesses, each explicitly positive and prime.
The total extension $P(0)=2$ is unused on the event's indices; the natural
remainder convention at modulus zero is unused on prime witnesses.
The source identity and operator correspondence are in
`Library/Factorization/noe2013a222759.md`.

## Motivation

The 2013 first-comment growth assertion is a Tier 1 published OEIS
conjectural assertion. Its full unbounded event is settled by the literal
remainder range and the sizes of the first $k$ primes. The frozen result
provides the exact source event rather than a finite sample or an
assumption about the global count.

## Gap

The original preregistration is
[comment 6618295321](https://github.com/the-omega-institute/trureturing/issues/26274#issuecomment-6618295321).
Its unchanged source event was registered at `2026-11-03T23:38:27Z`, before
execution at `2026-11-03T23:38:45Z`; its deadline is
`2026-11-11T00:00:00Z`. These are supplied preregistration readings.

The bounded source assessment identifies revision 12's first COMMENT as
still conjectural and finds no full-resolution citation in that entry.
At repository revision `6edb23f4fc2d44228fd765e0a6c2f57e85f7532b`, bounded
identifier and statement-shape searches of D5, Library, Problems and theory
found only this unit and its source note for the exact event. Pinned
Mathlib searches found the arithmetic suppliers, without a named supplier
of this entire OEIS assertion. The accepted source/history/literature
assessment is fallible supplied evidence. These readings do not certify
worldwide literature absence, originality or priority.

## Route

Set $m=P(k)^3>0$. The pinned prime-enumeration bound
`Nat.add_two_le_nth_prime` at $m-1$ gives $m+1\le P(m)$.
Consequently the source threshold implies $P(k)^3<n$.
For $i\in\mathrm{Fin}(k)$ choose $q(i)=\operatorname{nth}(\mathrm{Prime},i)$,
the first $k$ primes. Prime enumeration is injective and monotone, so these
are distinct positive primes and $q(i)\le P(k)$. Thus
$q(i)^3\le P(k)^3<n$.

`Nat.mod_lt` gives
$\binom{nq(i)}{q(i)}\bmod q(i)^3<q(i)^3<n$.
The literal remainder therefore differs from $n$. This is the ordinary
remainder-range mechanism; it uses no special binomial congruence.
Direct pinned suppliers include `Nat.nth`, `Nat.prime_nth_prime`,
`Nat.add_two_le_nth_prime`, `Nat.nth_injective`, `Nat.nth_monotone`,
`Nat.infinite_setOfPred_prime`, `Nat.Prime.pos`, `pow_pos`,
`pow_le_pow_left'`, `Nat.mod_lt`, `Fin.ext` and `ne_of_lt`.

## Falsifier

A counterexample to this exact event would be integers $k\ge3$ and
$n\ge P(P(k)^3)$ with fewer than $k$ positive prime witnesses to the
literal remainder inequality. Such a counterexample contradicts the
compiled result. A different placement of the cube, a congruence in place
of literal remainder equality, or an added whole-set finiteness premise
would break source fidelity. An earlier published resolution of this exact
assertion would invalidate the external-open-problem eligibility claim
without changing the verified arithmetic theorem.

## Evidence

The mathematical source is
`D5/S3/Arith/PrimeRemainders/OeisA222759Growth.lean`.
Its two definitions `P` and `cubicRemainder` are consumed by its sole public
theorem `result`. The full result has statement identity
`sha256:2a4b8f3d982aa14d26dbee8dfc3e8292ceaea402c369fa3c37126a82b8dbb72c`.
Its full telescope retains $k,n$, both lower bounds and the nested prime
threshold. There is no extra D5 companion declaration.

The per-theorem classification is `proof_shape: bind-only`,
`escape_witness: none`, `admission_basis: open-problem-resolution`.
The two earning definitions have no proof-shape claim. There are no direct
previously frozen project dependencies; the arithmetic suppliers are
pinned Mathlib and Lean. All three public declarations have axiom closure
contained in `propext`, `Classical.choice`, `Quot.sound`, without `sorry` or
an added axiom. The unbounded symbolic theorem has `utility: none`.

The canonical module membership record is
`Golden/Frozen/state/D5/S3/Arith/PrimeRemainders/OeisA222759Growth.lean.json`.
The matching Blueprint Scribe attaches one `OpenProblemResolutionClaim`
with `ResolutionKind.Proved` to this `result` and this dossier's slug.
The retained Reg mirror reconstructs the full original telescope through
an `Iff.rfl` source-equivalence bridge. It supplies the actual law,
whole-family rejection and sensitivity, and actual readout dependence.
Its unknown continuation records a residual only; it asserts neither
undecidability nor inexhaustibility.

## Triage

- Proved: the entire first COMMENT event for every $k\ge3$ and every
  positive $n\ge P(P(k)^3)$, including the threshold endpoint. The evidence
  is the full compiled `OeisA222759Growth.result`, with an injection of
  $k$ positive prime witnesses and the literal remainder predicate.
- Proved within that result: the first $k$ primes have cubes below $n$;
  the ordinary remainder bound forces the required inequalities. This
  identifies the decisive mechanism, without claiming a new general
  binomial theorem or a new proof technique.
- Open here: whether a smaller threshold is optimal and what exact
  counts hold. The result does not establish the finiteness of the entire
  prime set, any exact value of $a(n)$, or the sample table.
- Outside this settlement: the second COMMENT and A222760. No conclusion
  about either follows as a credited result in this dossier. No dependency
  of those assertions on the first COMMENT has been verified here.

## ASSUMED-UNVERIFIED

The supplied bounded prior and literature assessment is not a global
semantic search or an exhaustive exclusion of earlier full resolutions.
No independent priority, novelty, authorship-credit or external completion
certificate is asserted. The ordinary proof mechanism is known arithmetic.
The exact event above is distinguished from other comments, exact counts,
whole-set finiteness and A222760. Those excluded questions remain
unsettled by this delivery. Repository-wide required checks and final
independent review are separate from the scoped local evidence.
