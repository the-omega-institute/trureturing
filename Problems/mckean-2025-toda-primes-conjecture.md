---
slug: mckean-2025-toda-primes-conjecture
bibkey: mckean2025todaprimes
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/McKeanTodaPrimes/Result.result
url: https://arxiv.org/abs/2511.19744v1
---

# Refutation of both Toda-prime denominator assertions

## Problem

Stephen McKean, *Toda primes*, arXiv:2511.19744v1, §5.1,
Conjecture 5.6, printed p. 8:

> Conjecture 5.6. Let d be a Bernoulli denominator.
> (i) If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ.
> (ii) If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).

Definition 1.1, §1, printed p. 1:

> Definition 1.1. Let n be an integer. A Toda prime of n is an odd prime p such that
> p − 1 | 4n and gcd(p, 4n/(p−1)) = 1. Denote the set of Toda primes of n by T (n) (see Table 1),
> and let t(n) := |T (n)| (see Figure 1).

Notation 5.5, §5.1, printed p. 8:

> Notation 5.5. Given an even integer 2m, let P (2m) denote the set of primes such that
> p − 1 | 2m, so that D₂ₘ = ∏ₚ∈P(2m) p. Let F (d) = min{2m > 0 : D₂ₘ = d} [PW23].

### Formal reading

Lean names have prefix `D5.S3.Arith.McKeanTodaPrimes.Result`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $T(n)$ | `todaPrimes` | Odd primes with predecessor dividing $4n$ and coprime quotient. |
| $t(n)$ | `t` | Cardinality of the finite Toda-prime set. |
| $D_k$ | `bernDen` | Denominator of Mathlib's rational `bernoulli k`. |
| $P(k)$ | `denominatorPrimes` | Primes whose predecessor divides $k$. |
| Conjecture 5.6(i) | `clauseI` | Positive $a,m$, first even index $4a$, denominator unchanged. |
| Conjecture 5.6(ii) | `clauseII` | Positive $a,m$, denominator changed. |
| The full conjecture | `claim` | Conjunction of the two universal assertions. |
| Both negations | `refutedClauses` | Each component assertion is false. |
| Refutation | `result` | Exactly `¬ claim`. |

The condition $F(D_{4a})=4a$ is expressed equivalently as the absence of a
smaller positive even $k$ with $D_k=D_{4a}$. The equality at $4a$ is automatic.
For positive $n$, the range $p<4n+2$ is exhaustive because
$p-1\mid4n$ implies $p-1\le4n$. At $n=0$, the quotient is zero and
no prime is coprime to zero, so $T(0)$ is empty. All counterexamples have positive indices.
The natural-number restriction suffices to refute the integer conjecture.

## Motivation

The settling declaration is `D5/S3/Arith/McKeanTodaPrimes/Result.result`.
The source note is `D5/L/Factorization/mckean2025todaprimes`.
A Bernoulli denominator records predecessor divisibility, whereas Toda
primality additionally depends on a prime not dividing the input.
These two pieces of information behave differently under multiplication.

## Gap

Both clauses are false. For clause (i), take $a=23$, $m=47$:
$D_{92}=D_{4324}=1410$, with first positive even index $92$, but
$T(23)=\{3,5,47\}$ and $T(1081)=\{3,5\}$.
For clause (ii), take $a=11$, $m=5$:
$D_{44}=690\ne7590=D_{220}$, but
$T(11)=\{3,5,23\}$ and $T(55)=\{3,23\}$.

## Route

The von Staudt–Clausen identity gives

$$D_{2k}=\prod_{p\in P(2k)}p\qquad(k>0).$$

The denominator of the prime reciprocal sum divides this product. Each
prime in the product divides $D_{2k}$, and distinct primes are coprime,
which gives the opposite divisibility. Toda-prime membership reduces to

$$T(n)=\{p\in P(4n):p\text{ odd},\ p\nmid n\}\qquad(n>0).$$

For every prime $a\equiv23\pmod{30}$ such that $p=2a+1$ is prime,
the divisors of $4ap$ have twelve forms obtained from divisors of $4,a,p$.
The only prime successors are $2,3,5,p$; other successors are even or
are divisible by $3$ or $5$. Hence

$$D_{4a}=D_{4ap}=30p,\qquad T(a)=\{3,5,p\},\qquad T(ap)=\{3,5\}.$$

If $D_k=30p$ for a positive even $k$, the prime divisors $5$ and $p$
force $4\mid k$ and $2a\mid k$. Since $a$ is odd, $4a\mid k$.
Thus $F(30p)=4a$. This is a conditional family theorem; no infinitude of
prime pairs satisfying its hypotheses is asserted.

The second counterexample uses the denominator prime sets
$P(44)=\{2,3,5,23\}$ and $P(220)=\{2,3,5,11,23\}$.
It uses finite prime-set evaluation, without evaluating $B_{220}$ directly.

## Falsifier

An error in the Bernoulli-denominator formula, the exhaustiveness of the
prime ranges, the coprimality reduction or the first-index argument would
invalidate the corresponding counterexample. The separate negations in
`refutedClauses` establish failure of both clauses, rather than only failure
of their conjunction.

## Evidence

**PROVED.** `denominatorFormula` is the exact Bernoulli-denominator product;
`todaReduction` is the Toda-prime membership reduction. `family` states the
conditional family including minimality of the first index and both Toda
sets. `refutedClauses` refutes both universal assertions, and `result`
refutes their conjunction.

The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2afd8e16d4deb3d06d30494e5a12c1ae3f6ea8e3/experiments/mckean-toda-primes-conjecture)
contains `mckean-c56.py`, SHA-256
`162bd80015ea2c9615399d49ddc6868b15bd7665326e2ad92fec71b8d092ec4e`.
**COMPUTED.** `python3 mckean-c56.py`, exit 0: direct Bernoulli denominators
agree with the product formula at even indices through $400$; the two
counterexamples have the exact denominators and Toda sets above. The script
also computes $F(690)=44$ and $F(1410)=92$ by a finite first-index search.

The supplied literature search found no settlement in arXiv, Semantic
Scholar, web searches, Formal Conjectures or the repository scope recorded
with the source. The MathOverflow question concerns existence of Toda
primes, a different assertion. These are bounded supplied findings, not a
claim of exhaustive literature coverage or priority.

## Triage

### What the settlement shows

- **PROVED (Lean).** `family` exhibits the failure mechanism for clause (i):
  the Toda prime $p=2a+1$ divides the multiplier, disappears from the Toda
  set, and creates no new denominator prime. The minimal-first-index
  hypothesis does not prevent this loss.
- **PROVED (prose, using the reduction).** An old Toda prime of $a$ remains
  in $T(am)$ exactly when it does not divide $m$: predecessor divisibility
  persists, and $p\nmid am$ is equivalent to $p\nmid m$ for $p\in T(a)$.
  Thus coprimality of $m$ with every old Toda prime prevents a decrease in
  cardinality. If the denominator prime set is also unchanged, it ensures
  equality of the Toda sets. This describes a sufficient repair and is not
  a proof of the source's unqualified assertions.
- **PROVED (Lean).** The private `witnessII`, used in `refuteII` and
  `refutedClauses`, gives $D_{44}=690$, $D_{220}=7590$, $T(11)=\{3,5,23\}$
  and $T(55)=\{3,23\}$. It reverses the roles of $a$ and $m$ in the paper's
  own tightness example. The new denominator prime $11$ divides the input
  $55$, so it does not compensate for losing the old Toda prime $5$.
- **PROVED (prose).** Lemma 5.7's sufficient route fails on the family.
  For $p=2a+1$, the divisors of $2a$ are $1,2,a,2a$. Their corresponding
  successors $2p+1,4p+1,2pa+1,4pa+1$ are divisible respectively by
  $5,3,3,5$. Each is strictly larger than that divisor because $a\ge23$.
  Hence none is prime. This explanation is not an additional Lean theorem.
- **COMPUTED.** The cited script lists all prime $a<2000$ with
  $a\equiv23\pmod{30}$ and $2a+1$ prime:
  $23,53,83,113,173,233,293,443,593,653,683,743,953,1013,1103,1223,1583,1733,1973$.
  It checks the denominator, minimal-index and Toda-set identities separately
  for the first eight listed members. The general conditional identities
  are the statement of `family`; this finite computation asserts no
  infinitude.
- **OPEN.** Conjecture 1.3 and Question 1.2 about existence of Toda primes
  are untouched. Refuting Conjecture 5.6 removes its unrestricted proposed
  route to them; it refutes neither existence assertion nor the source's
  propositions under their original hypotheses. The restricted cases
  $a=3$ and $a=5$ mentioned in the paper are not settled here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. Google Scholar was not read in the supplied search.
No new network search is asserted. Infinitude of the prime pairs in the
conditional family is not established. The explanatory repair and the
Lemma 5.7 obstruction are proved in prose, not separate Lean declarations.
