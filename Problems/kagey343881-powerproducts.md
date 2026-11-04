---
slug: kagey343881-powerproducts
bibkey: kagey2021a343881
doi: null
url: https://oeis.org/A343881
triage: theorem
motivation_gids:
  - D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result
---

# Kagey's A343881 eventual equality conjecture

## Problem

P. Kagey's OEIS A343881 entry (revision 16) defines $T(n,k)$ as the least
$m>k$ for which $k^x m^y=c^n$ with positive natural $c,x,y$ and $x,y<n$, and
states:

> Conjecture: T(p,k) = A064549(k) for fixed k > 1 and sufficiently large p.

The entry defines $A064549(k)=k\prod_{q\mid k, q\ \mathrm{prime}}q$. Issue
[#18686](https://github.com/the-omega-institute/trureturing/issues/18686)
preregistered the literal prime-threshold claim. The settling declaration
is `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result : ¬ claim`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $k^x m^y=c^n$ with positive $c,x,y$ and $x,y<n$ | `Works` | The existential variables, positivity, strict bounds and equation are literal. |
| $T(n,k)$ is the least $m>k$ satisfying `Works`, with zero if none exists | the minimum expression in `claim` | The `Nat.find`/zero convention is inlined literally in the claim. |
| $A064549(k)=k\prod_{q\mid k}q$ | `A064549` | `Nat.primeFactors` gives the prime divisor product. |
| eventual equality for every fixed $k>1$ and all sufficiently large prime $p$ | `claim` | The threshold, prime hypothesis and equality are retained. |
| $T(p,12)=144$ for every prime $p\ge7$ | no delivered declaration | This stronger corrected statement remains open. |

## Motivation

At $k=12$, the source value is $A064549(12)=72$. The settling result shows
that 72 cannot satisfy the source power-product condition for any natural
exponent, while a valid larger factor exists at every prime exponent. Thus the
proposed eventual equality fails at the first unequal-exponent neighbour of
the source table.

## Gap

Issue #18686 records the source text, binding conventions, finite checker and
bounded literature screen. The repository and searched external sources
contained no settlement of this A343881 claim. Literature completeness is
`ASSUMED-UNVERIFIED`; this bounded reading makes no worldwide absence or
priority claim.

## Route

The proof compares prime-factorization coordinates of 12 and 72. If
$12^x72^y=c^n$, the coordinates at 2 and 3 imply
$n\mid 2x+3y$ and $n\mid x+2y$. Their determinant-one combination gives
$n\mid y$, contradicting $0<y<n$. For a prime $p$, $m=27$ works at $p=2$,
and $m=144$ works for $p\ge3$ with exponents $x=p-2$ and $y=1$. Infinitely
many primes beyond every threshold then contradict the claimed equality at
$k=12$.

## Falsifier

A natural $n$ and positive $x,y<n,c$ with $12^x72^y=c^n$ would invalidate
the coordinate obstruction. Failure of the prime witness at $p=2$ or $p\ge3$
would invalidate the existence step. A mismatch between the displayed claim
and the OEIS convention would invalidate source fidelity.

## Evidence

The kernel-checked public declarations are `Works`, `A064549`, `claim` and
`result`; private factorization and witness lemmas are consumed by `result`.
The result's axiom closure is contained in
{$\mathrm{propext}$, $\mathrm{Classical.choice}$, $\mathrm{Quot.sound}$}.
The Scribe result carries `OpenProblemResolutionClaim` with slug
`kagey343881-powerproducts` and `ResolutionKind.Refuted`.

### Experiment

The external checker is pinned to commit
[8975668582f8222ff2b9e04de8b8e573eca4ed96](https://github.com/the-omega-institute/trureturing-experiments/tree/8975668582f8222ff2b9e04de8b8e573eca4ed96/docs/reports/oeis-a343881-kagey-power-products/),
path `docs/reports/oeis-a343881-kagey-power-products/check.py`. Its SHA-256
is `c05425172c41c9f6f524c4c6a5454a5e73a46f91806e2b022f29e232f79ec5ab`.
The command is
`python3 ../trureturing-experiments/docs/reports/oeis-a343881-kagey-power-products/check.py 100 43`.
It checks the source table, the $k=12$ prime range, the absence of a working
72 through $n=60$, and the proposed correction on $2\le k\le100$ at
$p=31,37,41,43$. Its final output is `RESULT PASS` (exit code 0).

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Mechanism: exponent vectors $v(12)=(2,1)$ and $v(72)=(3,2)$ force $n\mid y$, contradicting $0<y<n$. | Proved; kernel-checked | `not_works_seventy_two`; the argument is uniform in natural $n$. |
| Extent: the obstruction holds for every natural $n$; a working $m$ exists at each prime exponent, so the large-prime conjecture is false. | Proved; kernel-checked | `not_works_seventy_two`, `defined_at_twelve` and `result`; the prime witness is 27 at $p=2$ and 144 for $p\ge3$. |
| Numerical neighbour: $T(p,12)=144$ for primes $7\le p<48$, with values 27, 18, 54 at $p=2,3,5$. | Computed; pinned experiment | The checker command above; scope is exactly the listed finite prime range. |
| Proposed correction on checked range: $T(p,k)=k^{1+1/g(k)}$ for $2\le k\le100$ and $p\in\{31,37,41,43\}$. | Computed; pinned experiment | The checker command above; this finite range does not establish a universal formula. |
| Full corrected formula, including $T(p,12)=144$ for every prime $p\ge7$. | Open | No delivered declaration proves the universal minimum or threshold formula. |
| Surviving neighbours: the equal-prime-exponent restriction and the distinct-integer prime-row assertion. | Open | Neither assertion is a premise or consequence of the delivered result. |

The exact finite computation scope is the checker invocation above; any
uniform extension beyond that scope remains open.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The OEIS source is
unpaginated and its revision is a source reading, not a proof of publication
priority. The finite checker supplies computed evidence only; the universal
refutation is the kernel-checked `result`.
