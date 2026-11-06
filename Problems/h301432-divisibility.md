---
slug: h301432-divisibility
bibkey: hanna2018geometricbinomial
doi: null
url: https://oeis.org/A301432/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/HannaA301432Divisibility
---

# Hanna's A301432 divisibility conjecture

## Problem

The source is Paul D. Hanna's OEIS A301432, COMMENTS and FORMULA:

```text
%I A301432 #7 Mar 21 2018 16:21:00
%A A301432 _Paul D. Hanna_, Mar 21 2018
%N A301432 G.f.: Sum_{n>=0} 3^n * (1+x)^(n^2) / 4^(n+1).
%F A301432 a(n) = Sum_{k>=0} 3^k * binomial(k^2, n) / 4^(k+1).
%C A301432 a(n) is divisible by 21 for n>0 (conjecture).
%O A301432 0,2
```

For $n\in\mathbb N$, set
$a(n)=\sum_{k\geq0} 3^k \binom{k^2}{n}/(4)^{k+1}$.
The settlement is **Proved**: for every $n\geq1$ there is $q\in\mathbb Z$ with $a(n)=21q$.
The preregistration is [#21834](https://github.com/the-omega-institute/trureturing/issues/21834).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed coefficient formula | `D5.S3.ArithSums.HannaA301432Divisibility.a` | Literal real infinite sum; ordinary natural binomial coefficients. |
| “for n>0” | `D5.S3.ArithSums.HannaA301432Divisibility.claim` | Natural index with $1\leq n$; no additional hypothesis. |
| “divisible by 21” | `D5.S3.ArithSums.HannaA301432Divisibility.result` | An existential integer quotient; integrality is included. |

The infinite sum is identified only after a `HasSum` proof. Natural subtraction in the A301311 upper index is truncated subtraction; its $n=0$ binomial coefficient is one. No analytic generating-function radius is presumed.

## Motivation

The settling GID is `D5/S3/ArithSums/HannaA301432Divisibility.result`.
The source is acknowledged in `Library/Factorization/hanna2018geometricbinomial.md`.
The companion settlements are A301310, A301311 and A301432, each with its own result, dossier and Proved resolution claim.

## Gap

The [source/provenance qualification](https://github.com/the-omega-institute/trureturing/issues/21832#issuecomment-6562357166) identifies the five public family theorems as this delivery's declarations under #21832, #21833 and #21834. The exact convergent real-series targets and integer quotients match their statement echoes; no independent prior owner is asserted.

The source calls the assertion a conjecture. The literature screen in #21834 found no settlement in the inspected OEIS records, repository, formal-conjecture collections or reachable papers. Boyadzhiev–Dil, DOI `10.1007/s10476-016-0302-y`, arXiv:1905.06171v1, supplies background geometric-polynomial identities; the target square-binomial divisibility assertion is absent from that screen. Citation and general-web coverage is incomplete. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For an even rational polynomial $P$ with $P(0)=0$ and integral values $f(k)$ at every natural argument, finite differences give an integral numerator
$N(z)=(1-z)^{d+1}\sum_{k\geq0}f(k)z^k$, with degree at most $d$, with the series identity interpreted for $|z|<1$.
The finite-difference recurrence and evenness give $N(-1)=0$, and $P(0)=0$ gives $N(0)=0$.
Monic division in $\mathbb Z[z]$ yields $N=z(z+1)Q$ with $\deg Q\leq d-2$.
Homogenizing at $(m,m+1)$ extracts $m(2m+1)$ while leaving an integer quotient.
The private `polynomial_divisibility` in `D5.S3.ArithSums.HannaA301310Divisibility` proves the resulting convergent-series statement. Its degree-bound parameter can always be chosen at least two.
The public `falling_hasSum` and `rising_hasSum` apply this to Mathlib's `preHilbertPoly` composed with $X^2$.
The named result uses `falling_hasSum` at $m=3$ and takes its sum value.
These statements are consumed bind-only applications of the pinned background machinery; no independent escape witness is claimed.

## Falsifier

A positive $n$ whose convergent source series is not an integer multiple of $21$ would falsify the claim.
A mismatch with the source formula, or an identification of `tsum` without the live summability proof, would invalidate the correspondence.

## Evidence

`D5/S3/ArithSums/HannaA301432Divisibility.lean` contains `D5.S3.ArithSums.HannaA301432Divisibility.result : D5.S3.ArithSums.HannaA301432Divisibility.claim`.
Its Scribe displays the expanded proposition and carries one `OpenProblemResolutionClaim` with `ResolutionKind.Proved`.
The admission basis is `open-problem-resolution (#21834; Proved)`; `generality: I`; `utility: none`.
The results are symbolic and unbounded, with no retained numerical certificate.

Four-slot escape audit is unfinished for the five public theorems of the three-module family, as listed in [#22143](https://github.com/the-omega-institute/trureturing/issues/22143). No completed registration is claimed.

### Independent finite computation

Experiment: [hanna-a301310-div10](https://github.com/the-omega-institute/trureturing-experiments/tree/c60d096843c6851282e0378a2875579990387574/docs/reports/hanna-a301310-div10), immutable revision `c60d096843c6851282e0378a2875579990387574`, script `docs/reports/hanna-a301310-div10/check.py`.
Command: `cd /tmp/op-h301310/experiment && python3 check.py`; the script and three b-files are extracted from that immutable revision.
Exit code: 0; final result `ALL_CHECKS_OK`.
Script SHA-256: `45a3b0cf70c3e974cafae22661fedce80ae0d80e35a661fc05480f90d4369c4b`.
For each of A301310, A301311 and A301432, the checker matches the b-file at every $0\leq n\leq100$, and checks exact divisibility, Newton/numerator equality, numerator tail vanishing, reciprocity and integral factorization for every $1\leq n\leq200$.
These finite checks are computed evidence and supply no universal proof.

## Triage

- **Proved, both binomial families:** kernel-checked `D5.S3.ArithSums.HannaA301310Divisibility.falling_hasSum` and `D5.S3.ArithSums.HannaA301310Divisibility.rising_hasSum` give $m(2m+1)$ times an integer for every $n\geq1$ and every natural $m$, including $m=0$, when the sum is zero.
- **Proved, polynomial extension:** the kernel-checked private `polynomial_divisibility` proves the same conclusion for every even rational polynomial vanishing at zero with integral natural values. Its live proof uses integral numerator factorization and homogenization; no cancellation of $n!$ modulo the divisor occurs.
- **Computed, checker scope:** the experiment entry above gives exit 0 with `ALL_CHECKS_OK`, b-file agreement at $n=0,\ldots,100$ and the exact checks at $n=1,\ldots,200$ for all three sequences, with pinned script and SHA-256.
- **Open, neighbouring assertions:** other OEIS neighbours, continued fractions, $q$-series and asymptotic identities have no settlement here.

### What the settlement shows

The decisive mechanism is the integral factor $z(z+1)$ followed by homogeneous evaluation. It covers both square-binomial families and every natural $m$, giving the source factors ten at $m=2$ and twenty-one at $m=3$. The zero boundary is included by the `HasSum` statements. The source's $n=0$ term is one and is excluded from the divisibility claims. The literature screen identifies no source theorem that assumes this conjecture; the other source formulas remain outside these settlements.

## ASSUMED-UNVERIFIED

Literature-search completeness and first-publication priority are `ASSUMED-UNVERIFIED`.
The source-to-definition correspondence is a source reading; Lean checks the stated mathematical propositions.
The four-slot audit remains unfinished under #22143. The finite experiment proves no assertion outside its stated range.
