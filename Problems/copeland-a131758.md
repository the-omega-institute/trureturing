---
slug: copeland-a131758
bibkey: copeland2008a131758
doi: null
url: https://oeis.org/A131758
triage: theorem
motivation_gids:
  - D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result
---

# Copeland's A131758 polynomial-content conjecture

## Problem

Tom Copeland's unnumbered COMMENTS conjecture in OEIS A131758, revision 48,
states:

> Conjecture for the polynomial array:
> The greatest common divisor of the coefficients of each polynomial is given by A060872(n)/n or, equivalently, by A038548(n).

The FORMULA line states:

> a(n,m) = (-1)^n*n!*Sum_{k=0..m} (-1)^k*C(n+1,k)*Lag(n, m-k+1).

With the ordinary order-zero Laguerre normalization of DLMF 18.5.12,

$$L_n(x)=\sum_{j=0}^{n}(-1)^j\binom nj\frac{x^j}{j!},\qquad
a(n,m)=(-1)^nn!\sum_{k=0}^{m}(-1)^k\binom{n+1}{k}L_n(m-k+1).$$

The complete polynomial is $P_n(t)=\sum_{m=0}^{n}a(n,m)t^m$.
For an integer realization $r:\operatorname{Fin}(n+1)\to\mathbb Z$ of these
rational coefficients, put
$c_n=\gcd_{0\le m\le n}|r_m|$ and
$D(n)=\#\{d\in\mathbb N:d\mid n,\ 1\le d,\ d^2\le n\}$ for $n\ge1$.
The literal assertion is $c_n=D(n)$ at every positive index.

### Statement echo

| Source clause or explicit convention | Lean counterpart | Scope |
| --- | --- | --- |
| Finite source formula with ordinary Laguerre polynomial | `a` | Rational sums, factorials and binomial coefficients; the Laguerre expansion is inlined. |
| All coefficients of the polynomial | `P`, `IsSourceRow` | All $n+1$ coordinates, including degree $n$. |
| Greatest common divisor of coefficients | `rowContent` | Nonnegative gcd of all absolute integer coordinates of the same realization. |
| A038548(n) | `D` | Positive divisors satisfying $d^2\le n$; the content assertion excludes $n=0$. |
| Integer array starting at zero | First conjunct of `claim` | Integer realizations exist for every natural index; this is asserted, not assumed. |
| Each positive-index polynomial has the proposed content | Second conjunct of `claim` | Every realization at every $n\ge1$ satisfies the equation. |
| Refutation of the literal joint assertion | `result` | Closed proposition `¬ claim`; the shift $D(n+1)$ is not substituted. |

`IsSourceRow` and the existence conjunct are the explicit realization convention
of preregistration #23503. Natural subtraction is truncated; the outer summation
has $k\le m$, so this agrees with the source difference. The rational denominator
$j!$ is nonzero. No claim uses a rational numerator in place of a coefficient.

## Motivation

The external named conjecture is preregistered in
[#23503](https://github.com/the-omega-institute/trureturing/issues/23503).
The settling declaration is
`D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result`.
Its module has generality `I` and utility `certified-instance`, with
`basis=refutes` directed to its closed `claim`.

## Gap

`dominating_theorem_search: not-found-in-searched-scope`.
The source and related OEIS entries, the completed arXiv web/full-text screens,
Zenodo identifier screens and indexed settler records, public Lean repository
screens, MathDB, and the source-cited paper are described in #23503.
No settlement was found in those completed screens. OpenAlex, Semantic Scholar,
StackExchange and some arXiv API queries did not yield usable result lists;
the cited Beck–Robins book was not read. Wider literature completeness is
`ASSUMED-UNVERIFIED`.

Repository name, defining-expression and conclusion-shape searches include
private declarations. No existing A131758 settlement was found. The specialized
Laguerre and cyclic-difference content modules concern different inputs; they
are not on this module's dependency path. The module imports only pinned
Mathlib and reuses `Finset.gcd_dvd`, `Nat.eq_one_of_dvd_coprimes` and
`Nat.two_eq_digitChar` in the proof.

## Route

Assuming `claim`, its existence conjunct supplies a complete integer row at
$n=8$. The finite coefficient formula forces its first two coordinates to be
$6209$ and $-41417$. Their coprimality forces the gcd of the whole row to be
$1$, whereas $D(8)=2$. The content conjunct would identify these unequal
numbers. The kernel-checked `result` therefore refutes the joint assertion.

This proof does not independently establish global integer-row existence or a
replacement formula for content. It has `proof_shape: bind-only`,
`escape_witness: none`, and
`admission_basis: open-problem-resolution (#23503; Refuted)`.

## Falsifier

A different source normalization, an omitted coordinate, or a failure of the
coefficient evaluations or coprimality would invalidate the proposed route.
The formal result instead checks the exact preregistered formula and complete
row domain. A proof of the same closed `claim` would contradict `result` in
the accepted formal system.

## Evidence

The canonical Lean module is
`D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.lean`;
its Scribe and emitted Markdown share that stem under `Blueprint/D5/S0/Certificates/`.
The source note is `Library/Certificates/copeland2008a131758.md`.
The sole public theorem is `result`; its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

[Experiment directory at immutable revision 325704ce821388768ba82f405681a10eec9b2e67](https://github.com/the-omega-institute/trureturing-experiments/tree/325704ce821388768ba82f405681a10eec9b2e67/docs/reports/copeland-a131758).
Script: `docs/reports/copeland-a131758/check.py`;
SHA-256: `a86e8907ed61064fc93f2735e9cedcd50a406a2dda8e59a17a524f61b15e73ed`.
Command: `git -C /Users/auric/trureturing-experiments show 325704ce821388768ba82f405681a10eec9b2e67:docs/reports/copeland-a131758/check.py | python3`
(pipeline failure propagation enabled), exit 0.

The exact integer/fraction checks reproduce source rows $0$ through $7$,
the nine published b-file entries at indices $36$ through $44$, and agreement
of the finite Laguerre and inverse Eulerian representations through $n=20$.
The row at $8$ is

$$[6209,-41417,48645,376259,-1724861,3233925,-2977609,1078849,40320].$$

The exact certificate is
$-6417\cdot6209-962\cdot(-41417)=1$; both $D(8)$ and $D(9)$ equal $2$.
Constant-coefficient oddness is checked at every even $n=2,4,\ldots,256$.
For $n=2^{12s+7}$, divisor counts are checked at $s=0,1,2$:
$D(n)=4,10,16$ respectively and $D(n+1)=2$ in all three cases.
The modular conditions are checked at $s=0,\ldots,100$.
These are finite computations, not a kernel proof of an infinite family.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Literal content assertion at $n=8$ | **Proved:** kernel-checked `D5.S0.Certificates.CopelandA131758PolynomialContentRefutation.result` refutes the binding joint claim by the first-two-coordinate gcd argument on a complete nine-coordinate row. | The theorem assumes the claim to extract that row; it does not assert a separate integer-row existence theorem. |
| Shifted alternative $c_n=D(n+1)$ | **Computed:** the exact experiment above gives $c_8=1$ and $D(9)=2$, exit 0 with the stated script hash. | It is not the binding claim and is not a second Lean theorem. |
| Exact $n=1,\ldots,10$ screen | **Computed:** command `python3 -` re-evaluates using the immutable script's `source_row`, `content` and `small_divisors` functions gives the table below, exit 0 with the same script hash. | No minimality theorem or classification follows. |
| Parity and family sanity checks | **Computed:** the exact experiment above checks every even $n=2,\ldots,256$, divisor counts for $s=0,1,2$, and modular conditions for $s=0,\ldots,100$, exit 0 with the stated script hash. | The finite scope is exact; no uniform extension is kernel-checked here. |
| Universal parity, infinitely many literal/shifted failures, global integer-row existence and a full content formula | **Open:** outside the delivered Lean theorem. | The elementary argument in #23503 is not claimed as a kernel-verified family theorem. |
| Restriction to odd $D(n)$ | **Open:** no equality theorem under this restriction is established. | It avoids the cited parity obstruction alone and does not supply sufficiency. |

| $n$ | $c_n$ (computed) | $D(n)$ (computed) |
| --- | --- | --- |
| 1 | 1 | 1 |
| 2 | 1 | 1 |
| 3 | 2 | 1 |
| 4 | 1 | 2 |
| 5 | 2 | 1 |
| 6 | 1 | 2 |
| 7 | 2 | 1 |
| 8 | 1 | 2 |
| 9 | 2 | 2 |
| 10 | 1 | 2 |

Thus equality survives at $n=1,2,9$ in exactly this computed screen and fails
at $n=3,4,5,6,7,8,10$. The mechanism of the formal counterexample is that two
coprime coefficients force content $1$ while the proposed divisor count is $2$.
For the wider parity explanation, the constant coefficient at an even index
is odd in the checked range, whereas some predicted divisor counts are even.

The array definition, its displayed coefficients and the transform identities
are not contradicted by rejecting its gcd conjecture. No theorem conditional
on the gcd formula was identified in the inspected source material of #23503.
A replacement content formula and a characterization of equality indices
remain open; neither is inferred from the finite screen.

## ASSUMED-UNVERIFIED

Complete external literature clearance, publication priority and any uniform
extension of the finite computations are `ASSUMED-UNVERIFIED`. Source-to-Lean
fidelity, proof-shape classification and utility semantics require semantic
review in addition to kernel checking. The OEIS source has no arXiv identifier
or DOI; none is assigned to it.
