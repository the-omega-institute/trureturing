---
slug: adamson-a156834
bibkey: elabdalaouidahmouneziadi2013automata
doi: 10.48550/arXiv.1301.3751
url: https://arxiv.org/abs/1301.3751v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.result
---

# Adamson's OEIS A156834 prime-equality conjecture

## Problem

Gary W. Adamson's [OEIS A156834](https://oeis.org/A156834/internal),
revision 20, COMMENTS, states verbatim:

> Conjecture: for n>1, a(n) = n iff n is prime. Companion to A156833.

The FORMULA entry, attributed to Seiichi Manyama, states verbatim:

> a(n) = Sum_{d|n} phi(d) * binomial(d+n/d-2, d-1).

Thus, for positive integer indices,

$$
a(n)=\sum_{d\mid n}\varphi(d)\binom{d+n/d-2}{d-1},
\qquad n>1\Longrightarrow\bigl(a(n)=n\iff n\text{ is prime}\bigr).
$$

The matrix ingredient is Proposition 6, §5.2, p. 11, of el Houcein el
Abdalaoui, Mohamed Dahmoune and Djelloul Ziadi, *On the transition reduction
problem for finite automata*, arXiv:1301.3751v1. Substituting column $k=d$
in its divisor-supported Eratosthenes-Pascal entry gives the binomial factor.
The weighted conjecture's author is Adamson; the matrix formula alone is not
the conjecture. Preregistration: [#23238](https://github.com/the-omega-institute/trureturing/issues/23238).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive-divisor sum in FORMULA | Public `a`, using `Nat.divisors`, `Nat.totient`, and `Nat.choose` | Literal source expression; division and subtraction are natural-number operations. |
| Every index greater than one | `claim` quantifies over `Nat` with antecedent $1<n$ | The exclusion of one is retained. |
| Equality iff primality | `claim` and `result` assert both directions with `Nat.Prime` | No additional hypothesis. |
| Sequence starts at one | `a` is total on `Nat` | The extension at zero is outside the assertion and imposes no source condition. |

## Motivation

The settling GID is
`D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.result`.
Its public conclusion proves the complete named assertion, rather than a
bounded prefix. The arithmetic lives in the registered S3 Arith domain;
there are no D5 imports. The module has `generality: I`, `utility: none`, and
`admission_basis: open-problem-resolution (#23238; Proved)`.

## Gap

The source labels the weighted equality characterization as a conjecture.
The bounded literature screen in #23238 found no settlement in the works it
inspected. The unweighted A157019 criterion is a different statement.
The scope of that search does not establish exhaustive absence or priority.
The source note is [elabdalaouidahmouneziadi2013automata](../Library/ArithUnits/elabdalaouidahmouneziadi2013automata.md).

## Route

Write $B(n,d)=\binom{d+n/d-2}{d-1}$ for a positive divisor $d$ of $n$.
Both $d$ and $n/d$ are positive. `Nat.choose_pos` and
`Nat.choose_eq_one_iff`, as used in the private `binomial_bounds`, give
$B(n,d)\ge1$ and

$$B(n,d)=1\iff d=1\ \lor\ d=n.$$

The private `excess_identity` uses `Nat.sum_totient` and integer finite-sum
normalization to give

$$a(n)-n=\sum_{d\mid n}\varphi(d)(B(n,d)-1).$$

Every term is nonnegative because $\varphi(d)\ge0$ and $B(n,d)-1\ge0$.
For prime $n$, every divisor is an endpoint, so the sum vanishes; this is
`prime_equality`. For nonprime $n>1$, `Nat.prime_def_lt'` supplies a proper
divisor $1<d<n$. At that divisor, $\varphi(d)>0$ by `Nat.totient_pos` and
$B(n,d)>1$. The sum is strictly positive, as proved by `composite_strict`
using `Finset.single_le_sum`. The public `result` combines these cases.
All four auxiliaries are private, consumed bind-only declarations; the
settling `result` is bind-only and has no qualifying escape witness.

## Falsifier

A positive integer $n>1$ at which equality and primality differ would refute
the exact claim. A bound on the tested indices cannot substitute for the
universal statement. The boundary $n=1$ is expressly excluded.

## Evidence

The kernel-checked public theorem is
`D5.S3.Arith.Divisors.AdamsonA156834PrimeEquality.result : claim`.
The compiled proof uses the private `prime_equality` and `composite_strict`;
both use `binomial_bounds` and `excess_identity`. The public definitions
are `a` and `claim`. No new axiom or numerical certificate is delivered.

The exact-arithmetic experiment is in
[the-omega-institute/trureturing-experiments, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/e7a413119183f7b479fd36fa0d95ee5cdc51199b/docs/reports/adamson-a156834),
commit `e7a413119183f7b479fd36fa0d95ee5cdc51199b`, file `check.py`.
Its SHA-256 is `1f6c051e0559f5831e53cb9dbe32831b7edf5cf9de2ec0d25dfa6f884a45ee8b`.
The exact pinned bytes, extracted into the ignored build scratch directory,
were run with `python3 .lake/scratch/stage-b-a156834/check.py`, exit 0.
The calculation reproduces 51 printed sequence terms and 11 triangle rows;
checks Pascal interleaving against Proposition 6 for $1\le k\le n\le256$;
and checks matrix-times-totient against the divisor sum through $n=256$.
The totient sieve agrees with trial factorization through 10000 and coprime
counting through 200. On $n=2,\ldots,10000$, there are 1229 prime equality
cases, 8770 composite strict-inequality cases and zero mismatches.
It computes $a(1)=1$ although 1 is not prime. These are finite results.

The four-slot escape audit is unfinished under
[#30277](https://github.com/the-omega-institute/trureturing/issues/30277).
The finite iff route lacks a `Fintype` instance on the complete domain
$\{n\in\mathbb N:1<n\}$. The enrolled dependent-family route still requires
a source reconstruction, exact bridge, whole-family variation, role
sensitivity and actual observational-dependence evidence. No Reg mirror is
retained and no registration is claimed `declared_validated`.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved in prose, Route | Subtracting $\sum_{d\mid n}\varphi(d)=n$ gives the integer excess sum; each factor is nonnegative. The identity also has the private Lean statement `excess_identity`. |
| Binomial equality criterion | Proved, kernel-checked `binomial_bounds` | For every $d\in n.\mathrm{divisors}$, $B(n,d)>0$ and $B(n,d)=1$ exactly at $d=1$ or $d=n$. |
| Prime indices | Proved, kernel-checked `prime_equality` | Every prime index satisfies $a(n)=n$ because all divisor contributions have zero excess. |
| Composite indices | Proved, kernel-checked `composite_strict` | Every nonprime $n>1$ satisfies $n<a(n)$; a proper divisor contributes strictly positively. |
| Excluded boundary | Computed, pinned `check.py` entry in Evidence, exit 0 | $a(1)=1$ and 1 is not prime, so the restriction $n>1$ is essential. |
| Finite independent check | Computed, same pinned experiment, exit 0 | Exactly $n=2,\ldots,10000$: 1229 prime equalities, 8770 composite strict inequalities, zero mismatches. No uniform extension is inferred from the experiment. |
| Surviving neighbour | Open | A156833 is not settled; its Mobius-transform construction does not provide this proof's nonnegative excess decomposition. |

The theorem settles the weighted conjecture for all indices in its source
range. It also proves the sharper strict inequality at composite indices,
through the private `composite_strict`. It imposes no extra hypothesis on the
source assertion. No claim is made that the automata results in the matrix
paper depend on Adamson's weighted conjecture, and no change to those results
is asserted. The companion A156833 remains a separate open target.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The bounded screen in #23238
does not exhaust citing works or later settlements. The 2014 journal version,
DOI `10.3233/FI-2014-1033`, was not read because publisher access challenged
the source-checking seat. No historical originality claim is made.
The linked escape audit lacks the stated registration evidence; the kernel
proof of the mathematical assertion does not complete that audit.
