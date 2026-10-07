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

## The backward record classification is already published

Nazardonyavi and Yakubovich, *Superabundant numbers, their subsequences
and the Riemann hypothesis*,
[arXiv:1211.2147v3](https://arxiv.org/pdf/1211.2147v3), 26 February 2013,
already supply the relevant strict-record language. The inspected PDF
has 32 pages and SHA-256
`c184db590a50ea81daa88660e5885d3c64980b9324f6e545d27bbae4e1eba155`.
Definition 2.1, Theorems 2.3–2.4 and 4.32, and the numerical scope and
example in §5 were read against that primary. This is a citation and
applicability assessment, without a whole-paper proof audit, independent
reproduction of its numerical claims, or Lean verification.

Definition 2.1, printed p.4, calls $10080$ extremely abundant (XA), and
calls $n>10080$ XA exactly when

$$
G(m)<G(n)\qquad(10080\le m<n).
$$

Proposition 2.2 gives $\mathrm{XA}\subseteq\mathrm{SA}$. Theorem 2.3,
printed p.5, states that the least Robin counterexample is XA; its proof
reports the finite check on $5040<n\le10080$. That check is cited, not
rerun. Theorem 2.4, on the same page, already proves that RH is equivalent
to infinitely many XA numbers, and its proof discusses attainment of
the global supremum under failure of RH. Neither criterion nor the
record classifier needs to be reconstructed here.

Apply these existing results to the same least global maximizer $N$
selected above under the counterexample hypothesis. The cited finite
check places it above $10080$. Minimality among maximizers gives

$$
G(m)<G(N)\qquad(5040<m<N),
$$

so it is XA, while global maximality prevents any larger integer from
being XA. Thus it is the last XA under these hypotheses. This is direct
application of the published record definition and supremum argument,
not a new source-selection result. The least global maximizer need not
be the least counterexample. In particular, the available strict
backward comparisons include every divisor deletion with
$1<d\mid N$ and $N/d>5040$, and also nondivisor comparators in that
range; they do not authorize a comparison with $N/d\le5040$.

Theorem 4.32, printed p.24, supplies $P^+(n)<\log n$ on XA sources.
It supplies no effective signed prime-error estimate. Under the
counterexample hypothesis there are only finitely many XA by Theorem
2.4, so neither an unbounded XA critical family nor an infinite
continuation from this selected maximizer is available.

The recursive route must also retain exponent changes. Remark 5.5,
printed p.26, reports consecutive XA numbers

$$
n_1=(139\#)(13\#)(5\#)(3\#)^2\,2^4,
\qquad
n_3=(151\#)(13\#)(5\#)(3\#)^2\,2^3,
$$

where $p\#$ denotes the primorial. Their $2$-exponents decrease from
$9$ to $8$, so XA records do not form a divisibility chain. This cited
example is not a new numerical search and does not refute nesting in a
separately chosen CA parameter chain. Properties 5.1–5.4 are explicitly
finite observations from §5, not uniform theorems; in particular their
consecutive exponent-change and largest-prime assertions cannot be used
as unbounded recursion laws.

These suppliers pay backward record classification and its source
scope. They leave the same-source quantitative coupling of deletion
and insertion losses, a strict Robin sign and full finite-source
coverage unpaid. Reusing them does not yield a new Robin estimate.

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

## A proposed oscillation-geometry supplier loses its shrinking margin

Thomas Schwabhäuser, *Preventing Exceptions to Robins InEquality*,
[arXiv:1308.3678v3](https://arxiv.org/pdf/1308.3678v3), is a proposed
CA-multiplier argument using the Alaoglu–Erdős conjecture. The inspected
PDF has 23 pages and SHA-256
`050c4444d706c1d6dd89ed3d227f57a196fececaade4d3b0648c7e8de8e062db`.
The scope here is §4.3: equation (4.1), Fact 4.21, Lemma 4.22,
Proposition 4.25 and its use in Corollaries 4.27 and 4.31, printed
pp.13–16. This is a paper-level assessment of these statements, without
a complete proof audit or Lean verification. The elementary exponential
limit used below is reused, not claimed as new oscillation theory.

For fixed $b>0$ and $0<\delta<1$, retain the source's function

$$
g(\mu,\nu)=\frac{\mu}{\nu}
 \frac{1+\delta e^{-b\mu}}{1-\delta e^{-b\nu}},\qquad
\epsilon_{\mu,\nu}
 =\log\frac{1+\delta e^{-b\mu}}{1-\delta e^{-b\nu}}.
$$

For a fixed angle $0<\phi<\pi/2$, both coordinates of
$(\mu,\nu)=(r\cos\phi,r\sin\phi)$ tend to infinity. Thus

$$
\epsilon_{r\cos\phi,r\sin\phi}\longrightarrow0,
\qquad
 g(r\cos\phi,r\sin\phi)\longrightarrow\cot\phi.
$$

Fact 4.21 and Lemma 4.22 instead use the positive limiting constant
$\epsilon_\infty=\log((1+\delta)/(1-\delta))$ and the resulting
$e^{\epsilon_\infty}\cot\phi$. That constant is not the limit of the
printed function. In particular, there is no positive limiting angular
margin separating its contour from the diagonal.

### An increasing arithmetic progression tests the actual auxiliary claim

The source defines $\mathcal M=\{(\mu,\nu):\nu>\mu, g(\mu,\nu)>1\}$.
Its Proposition 4.25 claims that an increasing real sequence with
$\arctan(a_{n+1}/a_n)\to\pi/4$ has an adjacent pair in $\mathcal M$.
For $a>0$ and $h>0$, the denominator above is positive and its exact
crossing condition is

$$
g(a,a+h)>1
\iff
h<\delta\bigl(ae^{-ba}+(a+h)e^{-b(a+h)}\bigr).
$$

Choose $C\ge1/b$ large enough that $2\delta t e^{-bt}<1$ for every
$t\ge C$, and put $a_n=C+n$. Such a $C$ exists because
$t e^{-bt}\to0$. The function $t e^{-bt}$ is decreasing on $t\ge1/b$.
Consequently every adjacent pair has $h=1$ and

$$
\delta\bigl(a_ne^{-ba_n}+(a_n+1)e^{-b(a_n+1)}\bigr)
 \le 2\delta a_ne^{-ba_n}<1.
$$

Therefore $g(a_n,a_{n+1})<1$ for every $n$, while the sequence is
strictly increasing and $\arctan(a_{n+1}/a_n)\to\pi/4$.
This directly contradicts the stated Proposition 4.25. Relative spacing
converging to one does not by itself beat the exponentially shrinking
margin. The same crossing condition excludes distinct integer pairs
with $\mu\ge C$, since then $h\ge1$; hence Corollary 4.27's claimed
infinitely many consecutive-prime pairs in $\mathcal M$ also fails in
this parameter range.

This assessment does not exclude close pairs of actual CA logarithmic
clocks, whose additive gaps may tend to zero. It shows that Proposition
4.25 does not supply their required quantitative comparison. Corollary
4.31 uses that proposition in its proposed source-selection step; its
printed derivation cannot therefore be imported as the needed
same-source gain. The Alaoglu–Erdős conjecture, alternative proofs,
and the actual selected Robin source are not settled by this auxiliary
counterexample. The original full signed-tail target and RH remain
unproved; no new general criterion or certified theorem is claimed.
