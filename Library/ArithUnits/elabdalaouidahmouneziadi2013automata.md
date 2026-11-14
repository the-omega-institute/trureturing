---
bibkey: elabdalaouidahmouneziadi2013automata
authors: el Houcein el Abdalaoui; Mohamed Dahmoune; Djelloul Ziadi
year: 2013
title: "On the transition reduction problem for finite automata"
doi: 10.48550/arXiv.1301.3751
url: https://arxiv.org/abs/1301.3751v1
claim: "Proposition 6 gives the divisor-supported binomial matrix formula used in OEIS A156834; Adamson’s separate weighted prime-equality conjecture is quoted below."
strata_touched:
  - D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.1301.3751

Source: https://arxiv.org/abs/1301.3751v1

Primary assertion: https://oeis.org/A156834/internal, revision 20, COMMENTS
and FORMULA (unpaginated). Adamson authored the conjecture; Manyama supplied
the explicit formula. The arXiv paper is *On the transition reduction problem
for finite automata* (2013), §5.2, Proposition 6, p. 11; it supplies the matrix
entry formula, rather than the weighted conjecture.

## Source statements

OEIS A156834 COMMENTS:

> Conjecture: for n>1, a(n) = n iff n is prime. Companion to A156833.

OEIS A156834 FORMULA:

> a(n) = Sum_{d|n} phi(d) * binomial(d+n/d-2, d-1).

OEIS A000010 NAME (unpaginated):

> Euler totient function phi(n): count numbers <= n and prime to n.

The arXiv source, §5.2, p. 11, states:

> Let $n$ be a natural number. We denote by $D_n$ the set of divisors of $n$.

Proposition 6 gives

$$
T_n^k=\begin{cases}
\displaystyle\binom{\frac{n}{k}+k-2}{k-1}&\text{if }k\in D_n,\\
0&\text{otherwise.}
\end{cases}
$$

Setting $k=d$ supplies the binomial factor in the OEIS formula. In Lean,
`Nat.divisors`, `Nat.totient`, `Nat.choose` and `Nat.Prime` supply the existing
arithmetic objects. The public definition uses the displayed divisor sum,
natural integer division and natural subtraction. The conjecture is the
closed proposition `∀ n : ℕ, 1 < n → (a n = n ↔ Nat.Prime n)`.

The proof subtracts the classical totient divisor sum `Nat.sum_totient`.
Binomial positivity makes each integer excess term nonnegative. Equality of
the binomial to one occurs exactly at the two divisor endpoints; a proper
divisor makes the excess strictly positive. This settles the weighted
assertion without a finite bound on the index. It makes no assertion about
the companion A156833 conjecture or the paper's automata results.

## Experimental reference

The exact arithmetic experiment is in
[`the-omega-institute/trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/e7a413119183f7b479fd36fa0d95ee5cdc51199b/docs/reports/adamson-a156834),
commit `e7a413119183f7b479fd36fa0d95ee5cdc51199b`.
The `check.py` SHA256 is
`1f6c051e0559f5831e53cb9dbe32831b7edf5cf9de2ec0d25dfa6f884a45ee8b`.
The command `python3 check.py` exits 0 with `ALL_CHECKS_OK`: it reproduces
the 51 printed sequence terms and 11 triangle rows, checks the matrix formula
through 256, and finds equality at 1229 primes and strict inequality at 8770
composites in `2..10000`, with zero mismatches. It also finds `a(1)=1`, while
1 is not prime. These finite readings do not replace the universal proof.

## Literature boundary

The literature screen in [issue #23238](https://github.com/the-omega-institute/trureturing/issues/23238)
is partial. Its completeness, citing-work coverage and comparison with the
unread 2014 journal version, DOI `10.3233/FI-2014-1033`, remain
ASSUMED-UNVERIFIED. No historical priority claim follows from the proof.
