---
bibkey: caveney2012sacaga
authors: Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow
year: 2012
title: On SA, CA, and GA numbers
doi: null
url: https://arxiv.org/abs/1112.6010v2
claim: The paper proves infinitely many CA numbers are GA1 and infinitely many are not; its parameter conditions must be checked before applying either class to actual self-tangent packets.
strata_touched: []
license: citation-only
triage: anchor
---

# Existing CA subclasses and the actual tangent parameter

The inspected primary is [arXiv:1112.6010v2](https://arxiv.org/pdf/1112.6010v2),
whose first page identifies the version as 17 July 2012. It has 29 pages;
the retrieved PDF SHA-256 is
`7bf39ed12be2f708dc6c4dca747d7d9316470c11d8f09f071cdbc79e6f1148ae`.
Locators below use its printed pages. The relevant statements and their
proofs in §§5.1–5.2 were read; no independent audit of the whole paper,
journal-version correspondence, or Lean verification is claimed.

The source defines $G(n)=\sigma(n)/(n\log\log n)$ for $n>1$ and calls a
composite $N$ GA1 when $G(N)\ge G(N/q)$ for every prime divisor $q$.
The packet applications here use the positive-logarithm range $n>e$;
Lemma 7 itself ensures $N/q\ge6$.

## Directly reusable infinite subclasses

Lemma 7, §5.1, printed p.17, states that a CA number $N$ for parameter
$\epsilon>0$, with largest prime factor $p=P(N)\ge5$, is GA1 if

$$
\epsilon>\frac1{\log(N/p)\log\log(N/p)}.
$$

Its proof gives the strict deletion inequalities $G(N/q)<G(N)$ for all
prime factors $q$. Theorem 6, printed pp.17–18, already proves infinitely
many CA numbers are GA1 by choosing the largest CA integer at the layer
price $\epsilon=F(p,1)$ and using the existing positive Chebyshev
oscillation. This infinite subclass is not a new project target.

Lemma 8, §5.2, printed p.18, takes the largest CA integer $N$ for
$\epsilon=F(p,1)$, $p\ge3$, where

$$
F(p,1)=\frac{\log(1+1/p)}{\log p}.
$$

If $\epsilon<1/(\log N\log\log N)$, it gives $G(N/p)>G(N)$, so $N$ is
not GA1. Theorem 7, printed pp.18–19, already proves infinitely many CA
numbers are not GA1 using the negative Chebyshev oscillation. These are
actual CA integers, not measures chosen independently of the primes.
Neither theorem estimates a forward regular packet's moments.

## Keep the CA price and the tangent price distinct

For the [actual packet interface](../Analytic/mantovanelli2026primeworkload.md),
write $a=\log N$ and $q(t)=1/(t\log t)$ on $t>1$.
This $q$ is the project's price; it is not the auxiliary function called
$g$ in equations (20)–(21) of the present primary. A regular tangent state
uses the same integer $N=C_a$ at price $\epsilon=q(a)$.

At that price, Lemma 7's sufficient condition would be
$q(a)>q(a-\log p)$, whereas $q$ is strictly decreasing and
$a-\log p=\log(N/p)>1$. Thus that particular substitution cannot satisfy
the condition. This does not exclude a tangent state from GA1: the same
CA integer may have another admissible price that does satisfy Lemma 7.
To use the sufficient condition, retain the same integer and check its
admissible price interval, not an independently selected CA state.

Lemma 8 has a different obstruction. For its largest CA integer, the
first $p$-layer is selected at $F(p,1)=\epsilon<q(a)$. That layer is absent
at the tangent price $q(a)$. Hence that integer is not the actual prefix
$C_a$; the negative-oscillation construction in Theorem 7 does not supply
regular tangent states. This follows by applying the existing activation
rule and does not invalidate the theorem about CA numbers.

Theorem 6's GA1 conclusion alone likewise supplies neither an event-free
root $A(a)=a$ nor a later regular endpoint $b$, a short width $b-a=o(a)$,
or the required signed packet moment. Those are joint conditions on the
same actual source. They are not consequences of having two separately
infinite classes.

## A known finite example needs no new enumeration

The source's §5.2, printed p.18, explicitly states that CA integers with
$P(N)=13$ are not GA1. The
[project's existing §98.5](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already records $720720$ as a strict self-matching integer, with the
existing CA-prefix correspondence. Since
$720720=2^4\cdot3^2\cdot5\cdot7\cdot11\cdot13$, these existing results
already distinguish regular self-matching from GA1. No new counterexample
search, numerical verification, generic CA theorem, or Lean wrapper is
needed to make that distinction.

The unresolved packet task concerns actual joint selection: a suitable
unbounded tangent family and a forward signed surplus. For full Robin,
any proposed selection also has to cover the relevant potentially
nonpositive minima; an arbitrary infinite GA1 or safe-source family does
not supply that coverage.
