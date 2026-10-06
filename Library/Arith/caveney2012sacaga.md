---
bibkey: caveney2012sacaga
authors: Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow
year: 2012
title: On SA, CA, and GA numbers
doi: null
url: https://arxiv.org/abs/1112.6010v2
claim: The paper supplies a critical-source reduction and necessary prime-layer restrictions for proper GA1 integers, as well as infinite CA subclasses; these do not supply a signed forward packet bound.
strata_touched: []
license: citation-only
triage: anchor
---

# Published GA1 source constraints and the actual tangent parameter

The inspected primary is [arXiv:1112.6010v2](https://arxiv.org/pdf/1112.6010v2),
whose first page identifies the version as 17 July 2012. It has 29 pages;
the retrieved PDF SHA-256 is
`7bf39ed12be2f708dc6c4dca747d7d9316470c11d8f09f071cdbc79e6f1148ae`.
Locators below use its printed pages. The relevant statements and their
proofs in §§5.1–5.2 and §6, together with the recalled reduction and facts
on printed p.5, were read; no independent audit of the whole paper,
journal-version correspondence, or Lean verification is claimed.

The source defines $G(n)=\sigma(n)/(n\log\log n)$ for $n>1$ and calls a
composite $N$ GA1 when $G(N)\ge G(N/q)$ for every prime divisor $q$.
The packet applications here use the positive-logarithm range $n>e$;
Lemma 7 itself ensures $N/q\ge6$.

## Which potentially critical Robin source is covered

Theorem 4(ii), printed p.5, recalls the published same-source reduction:
if any counterexample to Robin's strict inequality exists above 5040,
then $\max_{n>5040}G(n)$ exists, and the least integer $N>5040$ attaining
it is extraordinary. Here extraordinary means composite and both GA1
and GA2; GA2 requires $G(N)\ge G(aN)$ for every positive integer $a$.
This selects a global extremal source under the counterexample hypothesis;
it does not say that every counterexample, regular return, or tangent
minimum is GA1. Theorem 4(i) already states the equivalent RH criterion
that 4 is the only extraordinary number. Both reductions are reused.

The source's definition following Fact 1 on the same page calls a GA1
integer **proper** exactly when $\Omega(N)\ge3$, counting prime factors
with multiplicity. Fact 1 classifies the improper GA1 integers as 4 and
$2p$ for primes $p\ge7$. Fact 2 gives $G(N)\ge e^\gamma$ for every GA2
integer. The selected source above 5040 is therefore proper: 4 is excluded
by size, while $\sigma(2p)/(2p)=\tfrac32(1+1/p)<2$ and
$\log\log(2p)>2$ when $2p>5040$, so $G(2p)<1<e^\gamma$ excludes GA2.
This is hypothesis bookkeeping for the existing reduction, not a new
critical-source theorem or a new enumeration.

## Directly reusable prime and stack envelopes

Keep the same proper GA1 integer $N$ and put $A=\log N$. The following
published restrictions are available without any CA or regular-return
hypothesis.

Theorem 9, §6.1, printed pp.20–21, gives, for every prime $p\mid N$ and
integer $1\le r\le v_p(N)$,

$$
p\le(rA)^{1/r}\le A.
$$

Its displayed equation (34) also gives $p^r\log p\le A\log A$.
Thus the same source's $r$th occupied prime layer has an explicit
size restriction; its prime support and its exponents are not separate
freely selectable data.

Theorem 10, §6.2, printed pp.21–22, proves that for each fixed integer
$k\ge3$ there are only finitely many GA1 integers with $\Omega(N)=k$.
Its proof already supplies the quantitative bound

$$
\Omega(N)\ge\frac{A}{\log A}.
$$

Theorem 11, §6.3, printed pp.22–23, defines $R=h(A)$ using the inverse
of $t\mapsto2^t/t$ on $[2,\infty)$, so $2^R/R=A$, and gives the
divisibility envelope

$$
N\mid M(N),\qquad
M(N)=\prod_{r=1}^{\lfloor R\rfloor}
       \prod_{\substack{p\ \mathrm{prime}\\p\le(rA)^{1/r}}}p.
$$

Lemma 9 on printed p.22 gives $2\le R\le3.08\log A$.
These are necessary restrictions and a finite divisor envelope at a
given size; dividing $M(N)$ does not certify GA1, a tangent realization,
or a favorable packet. The envelope is retained as a cited supplier,
not reconstructed as another candidate enumerator.

Theorem 12, §6.3, printed p.23, gives $v_{P(N)}(N)=1$, where $P(N)$
is the largest prime factor. Its proof's check of the 84 divisors of
43200 belongs to the published proof and is not rerun here.
Theorem 13, §6.4, printed p.24, gives

$$
P(N)\sim\log N
\quad\text{as }N\to\infty\text{ through proper GA1 integers}.
$$

It supplies neither an effective numerical threshold nor a forward
signed workload estimate. The above restrictions, including the growing
$\Omega(N)$ bound, are published results rather than project discoveries.

## Host structure and the FIB atom cutoff are different inputs

For the [actual packet interface](../Analytic/mantovanelli2026primeworkload.md),
these suppliers constrain the factorization of the Robin host $N$ at
$A=\log N$. They can be used together on the same proper GA1 source,
including the global maximizer selected by Theorem 4(ii).

The [project's §423](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
instead sorts the raw FIB correction by odd squarefree atom kernels with
a fixed number $k$ of distinct prime factors at an atom-index cutoff $X$.
Its $k$, $X$, and kernel are not $\Omega(N)$, $N$, and the host's prime
factorization. Theorem 10 does not by itself transfer to a growing-
kernel cancellation estimate, and Theorem 11 does not couple those
signed layers to a packet from that host.

A use of the host envelope in the packet problem still needs the same
integer's CA/tangent correspondence where that interface is required,
and an estimate of its actual joint-layer debt or an improving multiple.
Theorem 4's selected source is GA2, so an improving multiple of that
source would contradict its defining extremality. Constructing such an
improvement under the critical-source hypotheses is the remaining task;
neither the divisor envelope nor $P(N)\sim A$ establishes it. A uniformly
positive full Robin margin on all proper GA1 integers above 5040 would
also suffice by the recalled reduction, but is not supplied here.

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
