---
bibkey: caveney2012sacaga
authors: Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow
year: 2012
title: On SA, CA, and GA numbers
doi: null
url: https://arxiv.org/abs/1112.6010v2
claim: The paper supplies a critical-source reduction, an unbounded GA2 family conditional on RH failure, and necessary prime-layer restrictions for proper GA1 integers; these do not supply a signed forward packet bound.
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
on printed p.5 and Theorem 5(iii) with its proof on pp.15–16, were read;
no independent audit of the whole paper,
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

## The published unbounded GA2 supplier under RH failure

Theorem 5(iii), printed p.13, states that if RH is false, infinitely many
GA2 integers exist. It also states that
$\mu=\max_{n>5040}G(n)>e^\gamma$ and that every integer attaining
this global maximum is both GA2 and CA. The infinitude and the CA
classification have different scopes.

Its proof on pp.15–16 uses Robin's published positive oscillation on CA
integers to obtain $\max_{n\ge t}G(n)>e^\gamma$ for every $t$.
Together with Gronwall's $\limsup G(n)=e^\gamma$, this permits a
sequence of tail maximizers $N_i$, with successive tails beginning after
the largest previous maximizer. Thus

$$
N_i\longrightarrow\infty,\qquad G(N_i)>e^\gamma,\qquad
n>N_i\ \Longrightarrow\ G(n)\le G(N_i).
$$

Every $N_i$ is therefore GA2. This is the source's construction, with
its integer $A_i$ renamed $N_i$ to distinguish it from the logarithmic
clock $A=\log N$. The proof classifies global maximizers as CA; it does
not classify all these later tail maximizers as GA1, CA, or maximizers
on the original domain $n>5040$.

The [all-GA2 core application](../Analytic/polak2026finiterobinca.md#application-to-arbitrary-ga2-sources-including-extra-prime-support)
uses this existing unbounded family without requiring those stronger
classifications. An eventual signed estimate covering every sufficiently
large GA2 clock can therefore be tested against these actual sources.
This supplier does not give that estimate. It is distinct from the fixed
least global maximizer and from the finite XA family under RH failure;
no new source-selection theorem, infinitude proof, originality claim,
or Lean verification is asserted.

## Ceiling replacements constrain the same right-tail source

The following applications use the all-integer comparisons of the
published tail sources, together with the classical Euler-layer
rearrangement. They retain one actual final integer for every comparison;
GA2 comparisons with multiples alone do not supply this argument.

Let $N>e$ satisfy $G(m)\le G(N)$ for every integer $m\ge N$, and put
$A=\log N$, $L=\log A$, $T=\sqrt A L$ and $W(n)=\log Z(n)$.
For any actual integer $1\le d\le N$, reuse the
[ceiling replacement](../ArithSums/nicolas2025comparison.md#all-integer-forward-comparisons-bound-the-envelope-deficit)
and retain its exact clock:

$$
c=\left\lceil\frac Nd\right\rceil,\qquad m=cd,\qquad
H=\log(N/d),\qquad s=\log(m/N),\qquad
C_A(s)=\log\frac{\log(A+s)}L.
$$

Thus $N\le m<N+d$ and $0\le s<\log(1+e^{-H})$. With
$b_p=v_p(d)$ and $r_p=v_p(c)$, the actual added Euler reward is

$$
B_d(c)=\log\frac{Z(cd)}{Z(d)}
=\sum_p\log\frac{1-p^{-(b_p+r_p+1)}}{1-p^{-(b_p+1)}}\ge0.
$$

Shared factors of $c$ and $d$ are included. The exact forward comparison
and the existing concavity tangent give

$$
\boxed{W(d)-W(N)+B_d(c)\le C_A(s)\le\frac{s}{AL}.}
\tag{R1}
$$

If the left side exceeds $C_A(s)$, the same actual $cd>N$ improves
$G(N)$. No comparison at an intermediate deletion integer is required.

### Rearrange all occupied layers in one integer

For the same $N$, let $S_k=\{p:v_p(N)\ge k\}$ and $r_k=|S_k|$,
and let $q_j$ be the $j$th ordinary prime. Set

$$
d_N=\prod_{k\ge1}\prod_{j\le r_k}q_j,\qquad
\beta_k(p)=\log\frac{Z(p^k)}{Z(p^{k-1})}
=\log\left(1+\frac1{p+\cdots+p^k}\right).
$$

The prefixes are nested because $r_{k+1}\le r_k$, so $d_N$ is one
realizable exponent inventory. Monotonicity of $\log p$ and $\beta_k(p)$
gives the simultaneous savings

$$
\begin{aligned}
H_N&=\sum_k\left(\sum_{p\in S_k}\log p
                 -\sum_{j\le r_k}\log q_j\right)
     =\log(N/d_N)\ge0,\\
\Gamma_N&=\sum_k\left(\sum_{j\le r_k}\beta_k(q_j)
                      -\sum_{p\in S_k}\beta_k(p)\right)
          =W(d_N)-W(N)\ge0.
\end{aligned}
$$

All sums are finite. Apply (R1) to this complete $d_N$, with
$c_N=\lceil N/d_N\rceil$ and $s_N=\log(c_Nd_N/N)$:

$$
\boxed{
\Gamma_N+B_{d_N}(c_N)\le C_A(s_N)
<\frac{e^{-H_N}}{AL},\qquad
0\le T\Gamma_N<\frac{e^{-H_N}}{\sqrt A}.}
\tag{R2}
$$

The inequality counts the total rearrangement and its actual padding,
not separately attainable optimum layers. It gives no positive lower
funding from a failure of prime-prefix order at the critical scale.
If $d_N=N$, then $c_N=1$ and both rewards are zero.

### A padding prime outside the replacement gives a strict improvement

Suppose additionally that $Z(d)\ge Z(N)$ and $AL\ge2$. Then

$$
\boxed{\operatorname{supp}(\lceil N/d\rceil)
       \subseteq\operatorname{supp}(d).}
\tag{R3}
$$

For $d=N$ the multiplier is one. Otherwise $d$ is not a divisor of $N$:
a proper divisor has strictly smaller $Z$. Thus
$c-1<N/d<c$, $c\ge2$, $cd>N$, and
$s<\log(c/(c-1))$. If a prime $p\mid c$ is absent from $d$, then
$B_d(c)\ge\log(1+1/p)\ge\log(1+1/c)$, so

$$
\log\frac{G(cd)}{G(N)}
>\log\frac{c+1}{c}-\frac1{AL}\log\frac c{c-1}>0.
$$

The last inequality uses
$\log(c/(c-1))<2\log((c+1)/c)$ for $c\ge2$, equivalently
$c^2-c-1>0$. This contradicts the actual forward comparison.
Even when (R3) holds, (R1) keeps all added layers in the same budget:
$B_d(c)<d/(NAL)$. Both restrictions apply to $d_N$ and to an actual
integer attaining $\Sigma(N)$.

The argument does not force a violation of (R1)–(R3), identify $N$ as
CA or GA1, or control the original signed $I_\psi(A)$. A FIB address
of either comparator must retain this actual prime inventory and clock;
the address alone supplies no strict improvement. These are applications
of existing source comparisons and Euler factors, without a priority
claim, new rearrangement theorem, or Lean verification.

## Inherited oscillation relaxes the eventual signed target

The displayed positive oscillation on printed p.15 of the same CNS v2
primary supplies more than the existence of arbitrarily large violations.
Under RH failure, set
$\Theta=\sup_{\zeta(\rho)=0}\Re\rho>1/2$ and fix
$1-\Theta<\eta<1/2$. The source applies Robin's oscillation result to
CA integers $C$ and obtains, for some fixed $c_\eta>0$, arbitrarily large
actual witnesses satisfying

$$
G(C)>e^\gamma\left(1+c_\eta(\log C)^{-\eta}\right).
\tag{O1}
$$

This is the oscillation used in the published infinitude proof, with an
explicit positive constant; its underlying Robin proof is cited through
that primary and is not independently reproved here.

Choose such a $C_j>\max\{e,N_{j-1}\}$ and let $N_j$ be the rightmost maximizer of
$G$ on the integers $n\ge C_j$. The maximum is attained with finitely
many ties: $G(C_j)>e^\gamma=\limsup G(n)$ places all sufficiently large
integers strictly below $G(C_j)$. This is the same tail-selection
mechanism as on printed p.16, with the tail starting at the chosen
oscillation witness. Thus

$$
N_j\ge C_j,\qquad N_j\longrightarrow\infty,\qquad
G(N_j)\ge G(C_j),\qquad
m>N_j\ \Longrightarrow\ G(m)\le G(N_j).
$$

This particular selection can also retain CA status by direct application
of the same primary's Lemma 2, printed p.10, and Lemma 6, p.13. If
$N_j=C_j$, it already has that status. If $N_j>C_j$, set
$\epsilon_j=1/(\log N_j\log\log N_j)$. Lemma 6 makes

$$
g_{\epsilon_j}(t)=\epsilon_j\log t-\log\log\log t
$$

minimal at $t=N_j$ on $t>e$. Hence, for every integer $n\ge C_j$,

$$
Z(n)n^{-\epsilon_j}
=G(n)e^{-g_{\epsilon_j}(n)}
\le G(N_j)e^{-g_{\epsilon_j}(N_j)}
=Z(N_j)N_j^{-\epsilon_j}.
$$

Lemma 2 applies with $N_0=C_j$ and $N=N_j$ and supplies global CA
optimization at $\epsilon_j$. Its comparison with a CA parameter for
$C_j$ is a conclusion of the lemma, not an additional assumption.
The equality branch $N_j=C_j$ does not identify its optimizing price
with $\epsilon_j$. This selection does not classify every member of
the original integer-tail family, or make these $N_j$ GA1 or global
maximizers on the original $n>5040$ domain.

At their actual clocks $A_j=\log N_j$, $L_j=\log A_j$,
$T_j=\sqrt{A_j}L_j$, and with
$\Delta(N)=\gamma-\log G(N)$, positivity of $\eta$ gives

$$
\Delta(N_j)<-\log(1+c_\eta A_j^{-\eta}).
\tag{O2}
$$

There is no bound needed on $N_j/C_j$: increasing the chosen integer
only decreases $A_j^{-\eta}$ from $(\log C_j)^{-\eta}$.
Reuse the exact same-source identity
$\Delta(N)=I_\psi(A)+K_N(A)$ and the
[actual-core allowance](../ArithSums/nicolas2025comparison.md#the-same-effective-allowance-on-actual-ga2-cores).
Its thresholds hold eventually along this family. Equations (O1)–(O2)
then give

$$
\begin{aligned}
T_j I_\psi(A_j)
&<-\mathcal E(L_j)-T_j\log(1+c_\eta A_j^{-\eta})\\
&\le-\mathcal E(L_j)
       -\frac{c_\eta}{2}A_j^{1/2-\eta}L_j
\longrightarrow-\infty.
\end{aligned}
\tag{O3}
$$

The second line uses $c_\eta A_j^{-\eta}\le1$ eventually. The complete
original improper integral $I_\psi$ and its clock remain unchanged;
no zero sum, upper endpoint, or elementary correction is discarded.
In particular, under RH failure, these actual CA right-tail sources
carry an unbounded negative normalized signed response. Their classical
prime-prefix support and ordered exponents give $d_{N_j}=N_j$, so the
sorting reward $\Gamma_{N_j}$ and its padding reward in (R2) are zero.
Their [existing strict SA property](alaoglu1944highly.md) also gives
$\Sigma(N_j)=Z(N_j)$ and $D_{N_j}=0$. Neither defect supplies a uniform
strictly positive funding term on this selectable critical family.
The source constraints do not establish a favorable-cutoff principle.

A weaker sufficient target for an eventual contradiction is therefore
an independently established finite lower bound: find fixed $M\ge0$
and $A_0$ such that every actual CA all-integer right-tail maximizer with
$A=\log N\ge A_0$ satisfies

$$
\boxed{\sqrt A\log A\,I_\psi(A)\ge-M.}
\tag{O4}
$$

Any such fixed $M$ would contradict (O3) under RH failure. This target
does not require $M$ to equal the effective core allowance. The lower
bound (O4) is not proved; the application only relaxes the outstanding
same-source signed obligation using the already published oscillation.
It is not a new source theorem, priority claim, Lean result, or proof
of RH.

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

## Relaxed forward records and the unfilled Robin step

Nazardonyavi and Yakubovich's later note,
*Delicacy of the Riemann hypothesis and certain subsequences of
superabundant numbers*,
[arXiv:1306.3434v2](https://arxiv.org/abs/1306.3434v2), is distinct from
the earlier `1211.2147v3` source used for XA above. Definition 1.3 and
Lemma 1.4, printed pp.2–3, use the same actual pair of integers $m<n$:

$$
\frac{Z(n)}{Z(m)}>
1+\frac{\log(n/m)}{\log n\,\log\log m},
\qquad Z(j)=\frac{\sigma(j)}j.
$$

Lemma 1.4 gives such a successor for a member $m$ of the source's $X'$;
Theorem 1.5 states that $X'$ is infinite without an RH premise. Definition
1.6, printed p.4, uses the stronger relaxed threshold

$$
\frac{Z(n)}{Z(m)}>
1+\frac{2\log(n/m)}{(\log n+\log m)\log\log m}
$$

to define $X''$. The displayed Theorem 1.5 concerns $X'$, not $X''$;
the latter's reported finite counts are not adopted as an infinitude
or a uniform jump estimate. The printed definitions say to find the
next integer and do not explicitly specify least successors. No
canonical-selection or arbitrary-branch SA assertion is used here.

The exact normalization shows what these rules guarantee. Put

$$
\ell=\log\log m>0,\qquad r=\frac{\log n}{\log m}>1,
\qquad G(j)=\frac{Z(j)}{\log\log j}.
$$

An actual Robin-ratio improvement needs
$Z(n)/Z(m)>1+\log r/\ell$. The two published relaxed rules instead use

$$
\phi_1(r)=1-r^{-1},\qquad
\phi_2(r)=\frac{2(r-1)}{r+1},
\qquad \phi_1(r)<\phi_2(r)<\log r.
$$

For either rule, on the same pair $m,n$, the exact readout is

$$
\frac{Z(n)}{Z(m)}>1+\frac{\phi_j(r)}\ell
\iff
\frac{G(n)}{G(m)}>
1-\frac{\log r-\phi_j(r)}{\ell+\log r}.
$$

The allowed loss is positive. With $h=\log r\downarrow0$, its two
numerators are respectively

$$
h-1+e^{-h}=\frac{h^2}{2}+O(h^3),\qquad
h-2\tanh(h/2)=\frac{h^3}{12}+O(h^5).
$$

These are normalizations of the published rules and standard elementary
expansions, not a new record theorem or analytic prime-error estimate.
They distinguish an available forward increase of $Z$ from an increase
of the normalized Robin quotient.

In particular, retain the same conditional least global maximizer $N$
from the earlier reduction. If an actual forward pair starts at $m=N$
and meets either rule, its lower bound for $G(n)/G(N)$ is below one and
is compatible with the known global upper bound $G(n)/G(N)\le1$.
This supplies no improving multiple or contradiction to GA2. No new
membership or successor-selection theorem at $N$ is asserted.

A usable recursive estimate still requires control of the actual
logarithmic jumps and their accumulated loss along one realized path,
or another jointly signed bound. The statements inspected here supply
no such uniform jump control and no bound for the complete original
$I_\psi(\log N)$. The earlier XA criterion and the later relaxed
infinitude statement are reused without reconstructing their proofs.
The same selected integer, actual zero real parts and multiplicities,
all heights, explicit-formula terms and strict Robin core remain
unchanged. RH remains unproved; this source application is not Lean
verified and claims no mathematical originality.

## Positive psi points supply a strict actual CA increase

The [Pintz source application](../Analytic/pintz1984remainder.md#positive-psi-error-points-in-power-windows)
locates positive $\psi$-error points in $[Y^r,Y]$ under its stated
fixed-exponent conditions. The following correspondence consumes that
input and the present primary's actual activation rules, equations
(7)–(12), pp.7–9. It does not repeat Theorem 6's infinite GA1 supplier.
Use the source's full layer price

$$
F(x,k)=\frac{\log(1+1/(x+\cdots+x^k))}{\log x},\qquad x>1.
$$

Let $t\to\infty$ satisfy $\psi(t)>t$, and let $p$ be the largest prime
at most $t$. The prime number theorem gives $p\sim t$, while the full
prime-power accounting gives

$$
\psi(t)-\vartheta(t)
=\vartheta(\sqrt t)
 +\sum_{k=3}^{\lfloor\log t/\log2\rfloor}\vartheta(t^{1/k})
=(1+o(1))\sqrt t.
$$

The remaining sum is $O(t^{1/3}\log t)$. Since
$\vartheta(p)=\vartheta(t)$, positivity implies
$\vartheta(p)-p>-(1+o(1))\sqrt p$.

At the actual price $\epsilon_p=F(p,1)$, let $x_k$ be the root of
$F(x_k,k)=\epsilon_p$, so $x_1=p$, and retain

$$
H=\prod_{k:x_k\ge2}\ \prod_{q\le x_k}q,
\qquad D=H/p.
$$

Here $q$ ranges over ordinary primes. The published activation rule
makes $H$ the largest CA integer at this price, including every tied
layer. The first $p$-layer is tied and no higher $p$-layer is occupied,
so $D$ is another actual CA integer at the same price.

For each fixed $c>0$,
$F(c\sqrt p,2)/F(p,1)\to2/c^2$; monotonicity therefore gives
$x_2\sim\sqrt{2p}$. Lemma 1, p.9, and equation (15), p.11, give
$x_3<(3p)^{1/3}$ and $O(\log p)$ occupied layers. Thus all layers yield

$$
\log H=\vartheta(p)+(\sqrt2+o(1))\sqrt p
 +O(p^{1/3}\log p),
\qquad \log D\sim\log H\sim t.
$$

In particular $\log D>p+(\sqrt2-1+o(1))\sqrt p-\log p>p+1$
eventually. The sign of the gain is then exact:

$$
\begin{aligned}
\log\frac{G(H)}{G(D)}
&=\epsilon_p\log p
 -\int_{\log D}^{\log H}\frac{du}{u\log u}>0,\\
\epsilon_p&>\frac1{(p+1)\log(p+1)}.
\end{aligned}
$$

Indeed $Z(H)/Z(D)=1+1/p$, $\log H-\log D=\log p$, and
$u\mapsto1/(u\log u)$ decreases throughout that interval. The positive
$\sqrt2-1$ term permits a positive $\psi$-point even if
$\vartheta(p)<p$. The full layer accounting is retained, and possible
activation ties remain allowed. This correspondence supplies no GA1
or event-free assertion.

## Quantitative selection into the self-clock-price class

Define the actual source class

$$
\mathscr S_*=
\left\{N>e:\ N\text{ is globally CA at }
\epsilon_N=\frac1{(\log N)\log\log N},\quad
G(m)\le G(N)\ \text{for every integer }m\ge N\right\}.
$$

Under RH failure, the preceding correspondence permits an unbounded
family entirely in this class while retaining a fixed power-sized
excess. This is a paper-level synthesis of the cited inputs, not a
priority claim, Lean certification, or bound for the signed tail.

Retain the zero abscissa $1/2<\Theta\le1$. Choose fixed parameters

$$
1-\Theta<\eta<\frac1{4\Theta},\qquad
2\eta<r<\frac1{2\sigma},
$$

where $\Theta<\sigma<\min\{1,1/(4\eta)\}$ if $\Theta<1$, and
$\sigma=1$ if $\Theta=1$. These choices exist because
$4\Theta(1-\Theta)<1$. They satisfy both $r\sigma<1/2$ for the Pintz
application and $0<\eta/r<1/2$ for the final excess. This selects an
allowed fixed exponent in (O1); it is not a construction for every
previously chosen $\eta<1/2$.

Take the published CA witnesses $C$ from (O1), with
$a=\log C\to\infty$, and put $Y=a/8$. Select a positive $\psi$-point
$t\in[Y^r,Y]$, then construct the actual $D,H$ above. Eventually

$$
\log D\ge\tfrac12(a/8)^r,\qquad
\log H\le2t\le a/4,
\qquad D<H<C,
\qquad G(H)>G(D).
\tag{S1}
$$

The selection of $t$ can be specified without a free continuum choice:
take the least member of the finite set
$\{Y^r\}\cup\{q^k:Y^r<q^k\le Y,\ q\text{ prime},\ k\ge1\}$
where $\psi(t)>t$. Such a member exists since $\psi(u)-u$ decreases
between its prime-power jumps.

Let $N$ be the rightmost maximizer of $G$ over the integers $n\ge D$.
The tail contains $C$ with $G(C)>e^\gamma=\limsup G(n)$, so this uses
the already recalled attained-tail-maximum mechanism and has finitely
many ties. The strict gain in (S1) gives $N>D$. Lemmas 6 and 2 therefore
apply with CA base $N_0=D$, selected maximum $N>D$, and price
$\epsilon_N$; they supply global CA optimization at that exact price.
Hence $N\in\mathscr S_*$, with all activation ties still allowed.

Put $A=\log N$, $L=\log A$, $T=\sqrt A L$ and
$k_0=1/(2\,8^r)$. On the same final integer, (S1) gives
$A\ge k_0a^r$, and consequently

$$
a^{-\eta}\ge k_0^{\eta/r}A^{-\eta/r},\qquad
G(N)\ge G(C)>e^\gamma(1+c_*A^{-\eta'}),
\quad \eta'=\eta/r\in(0,1/2),\quad c_*=c_\eta k_0^{\eta'}>0.
\tag{S2}
$$

Also $A\to\infty$. The possible positions $D<N<C$, $N=C$, and $N>C$
are all covered: the lifting comparison is $N>D$. The earlier procedure
whose tail starts at $C$ keeps its stated equality-branch price limitation.
Here the price identification follows from $N>D$ even if $N=C$.

Apply (O3) with the fixed $(\eta',c_*)$ supplied by (S2). Under RH
failure it yields $T I_\psi(A)\to-\infty$ on an unbounded family inside
$\mathscr S_*$. The same-source identity, complete original integral
and actual core $K_N(A)$ are evaluated at $A=\log N$, not at any
auxiliary clock $t,p,\log D$ or $\log C$.

Accordingly a sufficient remaining target can be restricted to

$$
\exists M\ge0,\ A_0\quad
\forall N\in\mathscr S_*,\ A=\log N\ge A_0:\quad
\sqrt A\log A
\int_A^\infty(\psi(u)-u)
 \frac{1+\log u}{u^2\log^2u}\,du\ge-M.
\tag{S3}
$$

No bound in (S3) is established. The increment is the quantified
source-selection interface justifying this narrower class, with the
original signed obligation preserved. It supplies neither GA1 nor
regular or event-free states, a favorable cutoff, eliminated ties,
positive sorting-defect funding, or RH. Those restrictions cannot be
added to (S3) without another same-source selection argument.

## The same power-excess family also supplies proper GA1 sources

Keep the actual $D,H,N$ and all parameters of (S1)–(S2). The following
application of equations (10)–(12) and Lemma 6, printed pp.8–9 and p.13,
provides the additional same-source selection required above. It does
not reconstruct the paper's known infinite CA–GA1 supplier or claim
priority for the application.

First the selected maximum satisfies $N\ge H$, not only $N>D$.
The two endpoints optimize at the common price $\epsilon_p$, with
$Q=Z(D)D^{-\epsilon_p}=Z(H)H^{-\epsilon_p}$. For $D<m<H$, global
CA optimization gives

$$
G(m)\le Qe^{g_{\epsilon_p}(m)},\qquad
g_\epsilon(t)=\epsilon\log t-\log\log\log t.
$$

Lemma 6's strict decrease followed by strict increase implies
$g_{\epsilon_p}(m)<\max\{g_{\epsilon_p}(D),g_{\epsilon_p}(H)\}$.
Since $G(D)<G(H)$, the larger endpoint is $H$. Together with the
separate strict comparison at $m=D$, every $D\le m<H$ has
$G(m)<G(H)$; tail maximality therefore forces $N\ge H$.

Put $q_0(u)=1/(u\log u)$. The same integer's own price now satisfies

$$
\epsilon_N=q_0(A)\le q_0(\log H)<q_0(p+1)<\epsilon_p.
$$

Every occupied $H$ layer has price at least $\epsilon_p$ and hence is
mandatory at $\epsilon_N$, by the cited activation rule. Thus $H\mid N$.
For any ordinary prime divisor $q$ of $N$, if $q\le p$ then
$N/q\ge H/q\ge H/p=D$. If $q>p$, the largest prime factor of $H$ is
$p$, so $H\mid N/q$ and again $N/q\ge H>D$. These comparisons cover
every multiplicity. The defining maximum over integers at least $D$
therefore supplies $G(N/q)\le G(N)$ for every such $q$.
Eventually $p\ge5$, so $\Omega(N)\ge\Omega(H)\ge3$; this is proper GA1
in the source's exact sense. The power excess (S2) holds on this same $N$.

### Apply the published prime-local regularity bridge

Define the narrower class

$$
\mathscr S_{\rm reg}=\mathscr S_*\cap\{N:N\text{ is proper GA1}\}.
$$

Every member meets the hypotheses of the
[published prime-local bridge](../Analytic/mantovanelli2026primeworkload.md#the-existing-prime-local-bridge):
properness gives $N/q\ge4>e$ for every prime divisor $q$, GA1 gives
the deletion comparisons, and right-tail maximality gives
$G(Nq)\le G(N)$ for every ordinary prime $q$. The cited theorem
therefore directly supplies the event-free identity
$N=C_A$ and $\Phi_{\rm CA}(A)=A$ at $A=\log N$.
No general regularity or activation-tie proof is repeated here. The
same manuscript's fixed-maximizer reduction in §11 does not supply
the unbounded family and fixed power excess in (S2).

### Restrict the unpaid signed estimate to this joint source class

The selected family lies in $\mathscr S_{\rm reg}$ and retains (S2).
Therefore (O3) still forces $T I_\psi(A)\to-\infty$ on that same
unbounded family if RH fails. It suffices to establish

$$
\exists M\ge0,\ A_0\quad
\forall N\in\mathscr S_{\rm reg},\ A=\log N\ge A_0:\quad
\sqrt A\log A\, I_\psi(A)\ge-M.
\tag{S4}
$$

This is the complete original signed integral, with every prime-power
layer and explicit-formula term retained. The
[existing regular-return endpoint application](../ArithSums/nicolas2025comparison.md#the-endpoint-condition-at-actual-self-tangent-sources)
now applies to this same family: it already gives
$A-\vartheta(A)=\sqrt{2A}(1+o(1))$ and a negligible squared endpoint
penalty at the actual primorial cutoff. Its proof and the archived
packet and cone results are reused rather than repeated.

No bound in (S4) follows from those endpoint identities. The added
interface is joint selection of proper GA1 regular sources with the
same quantified excess, not a proof that every member of
$\mathscr S_*$ is GA1. The full signed estimate and RH remain unproved;
this application is not Lean certified and claims no mathematical
originality.

The [existing Johnston weighted-sign theorem](../Analytic/johnston2022average.md#direct-transport-to-the-existing-robin-kernel)
also gives a negative primitive with this kernel, anchored at 2.
Writing that primitive as $J$ leaves the complete target
$I_\psi(A)=J_\infty-J(A)$. Its negative bias does not supply the
required comparison with $J_\infty$ at these same actual integers;
the uniform floor in (S4) on the already justified source class remains unpaid.

## Transport one selected source into an actual CA price interval

The Euler optimization and tangent minimum in equations (7)–(12) and
Lemma 6 of the inspected primary give the following application. It
quantifies the sampling requirement for a future arithmetic mean or
exceptional-set estimate; it is not a new optimization theorem, a
signed-tail bound, an originality claim, or Lean certification. The
[existing quadratic tail interpolation](../Analytic/guthmaynard2024largevalues.md#finite-interpolation-without-assuming-a-prime-error-bound)
already supplies the $A^{3/4}$ bounded-loss scale for a different
comparison. That interpolation and the tangent minimum are reused.
The tangent gap $R(A,b)$ below is also the existing $c_A(b)$ in
the [Nicolas pressure application](../ArithSums/nicolas2025comparison.md),
equation (PH1). Its global Robin maximum hypothesis is not imported
here: the comparison uses the original source's right-tail maximality
only at $C_b\ge N$ and retains actual Gronwall values, rather than
identifying them with pressure away from a self-clock point.

Fix the same $N\in\mathscr S_{\rm reg}$, put $A=\log N>1$,
$L=\log A$, $T=\sqrt A L$, and retain

$$
g(b)=\frac1{b\log b},\qquad
k(b)=-g'(b)=\frac{1+\log b}{b^2\log^2b}.
$$

For $b\ge A$, let $C_b$ be the largest full CA optimizer at price
$g(b)$, including all activation ties and repeated prime layers. Write
$B(b)=\log C_b$ and

$$
X_N=\log G(N)-\gamma,\qquad X(b)=\log G(C_b)-\gamma.
$$

The already cited prime-local bridge gives $N=C_A$. The full layer
rule gives $N\mid C_b$, hence $B(b)\ge A>1$. In general $B(b)\ne b$:
no self-clock identity, GA1 property, or tail maximality is imposed on
the later $C_b$.

Global optimization at $g(b)$ supplies
$\log Z(N)-g(b)A\le\log Z(C_b)-g(b)B(b)$, where $Z(n)=\sigma(n)/n$.
Lemma 6, in the logarithmic variable $t$, says that
$F_b(t)=g(b)t-\log\log t$ has its minimum at $t=b$.
Thus $X_N-X(b)\le F_b(A)-F_b(B(b))\le F_b(A)-F_b(b)$.
The original $N$'s all-integer right-tail maximality separately gives
$X(b)\le X_N$. Together these existing comparisons yield

$$
\begin{aligned}
0\le X_N-X(b)&\le R(A,b),\\
R(A,b)&=\log\frac{\log b}{\log A}-\frac{b-A}{b\log b}
       =\int_A^b(u-A)k(u)\,du\\
&\le\frac{k(A)}2(b-A)^2.
\end{aligned}
\tag{P1}
$$

The integral follows by differentiating the explicit tangent gap;
the last inequality uses the existing decreasing kernel. No ordinary
prime error has been assigned a favorable sign in this comparison.

For $h>0$, define the actual-price mean
$\mathcal M_A(h)=h^{-1}\int_A^{A+h}X(b)\,db$.
There are finitely many CA activation events on each such interval;
the mean is over the actual stepwise arithmetic values, with endpoint
ties of zero integration weight. Integrating (P1) gives

$$
0\le X_N-\mathcal M_A(h)
\le\frac1h\int_A^{A+h}(A+h-u)(u-A)k(u)\,du
\le\frac{k(A)h^2}{6}.
\tag{P2}
$$

At $h=A^{3/4}$ this is
$0\le T[X_N-\mathcal M_A(h)]\le(1+1/L)/6$.
It supplies a bounded transport cost, not an upper bound for
$T\mathcal M_A(h)$. In the existing identity
$I_\psi(A)+K_N(A)=-X_N$, a bound on that positive mean would still
need an independent arithmetic supplier before it could fund (S4).

### A power excess occupies a quantified price interval

Use the particular fixed $\eta'\in(0,1/2)$ and $c_*>0$ supplied
by (S2), rather than choosing a different exponent. Eventually
$X_N\ge cA^{-\eta'}$ for some fixed $c>0$ on that selected family.
Choose a fixed $\lambda>0$ with $\lambda^2\le c/2$, and set

$$
h_{\eta'}(A)=\lambda A^{1-\eta'/2}\sqrt{\log A}=o(A).
$$

For $L\ge1$, (P1) gives
$R(A,A+h_{\eta'}(A))\le\lambda^2A^{-\eta'}$.
Consequently every actual optimizer on this entire interval satisfies

$$
X(b)\ge\frac c2 A^{-\eta'}
\qquad(A\le b\le A+h_{\eta'}(A)).
\tag{P3}
$$

This provides a quantitative interface for the
[existing exceptional-center sampling obstruction](../Analytic/mantovanelli2026primeworkload.md#the-remaining-signed-supplier-and-its-sampling-conditions).
For example, put $\delta=c/(4\,2^{\eta'})$ and
$\mathcal E_X=\{b\in[X,3X]:X(b)>\delta X^{-\eta'}\}$.
For any selected source with $A\in[X,2X]$, (P3)'s interval lies in
$[X,3X]$ eventually and is contained in $\mathcal E_X$. Its length
is at least $\lambda X^{1-\eta'/2}\sqrt{\log X}$.
An unconditional estimate

$$
|\mathcal E_X|=o\!\left(X^{1-\eta'/2}\sqrt{\log X}\right)
\tag{P4}
$$

would therefore exclude such selected sources at all sufficiently large
scales, contradicting the existing RH-failure supplier. Here $|\cdot|$
is Lebesgue measure in the actual CA price variable $b$. No estimate
(P4), or uniform upper bound for the mean in (P2), is established.
Qualitative density $o(X)$ does not reach this required rate; an average
over integers, prime cutoffs, moduli, or characters cannot be substituted
without a proved transport of the averaging measure. The interval
comparison adds no new signed ordinary-prime control and leaves the
complete original Robin tail and RH unresolved.


## Use the existing short-interval PNT on the actual CA price path

The uniform short-interval theorem in
[Guth–Maynard, Corollary 1.3](../Analytic/guthmaynard2024largevalues.md#the-short-interval-input)
can be applied to the same actual path in (P1). The centered
prime-count conversion and wider interpolation scale are already in the
[FIB theory volume, §260, equations (260.5) and (260.9)](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
They are reused here. The additional application is the transport from
one selected $N\in\mathscr S_{\rm reg}$ to all the actual later $C_b$,
including their higher layers and activation ties. It is a paper-level
application of existing results, without an originality or Lean
certification claim.

Retain $A,L,T,g,k,B,X_N,X$ from (P1), in particular $B(A)=A$.
Put

$$
u=L^{1/4},\qquad \varepsilon_A=Le^{-u},\qquad t_0=A^{2/3}.
$$

For all sufficiently large $A$, uniformly for $t_0\le t\le A$,
the existing arithmetic inputs give

$$
|B(A+t)-B(A)-t|\le C_0\varepsilon_A t.
\tag{P5}
$$

The [existing uniform extension (GS4)](../ArithSums/nicolas2025comparison.md#the-local-prime-input-and-its-uniform-range)
gives the relative error
$\ll(\log Y)e^{-(\log Y)^{1/4}}+Y^{-1/10}+Y^{-1/6}$
on all intervals in $[Y/2,3Y/2]$ of length at least $Y^{2/3}$.
For $2^{2/3}A^{2/3}\le t\le A$, apply it with $Y=2A$ to
$[A,A+t]$. For $A^{2/3}\le t<2^{2/3}A^{2/3}$, use directly
the existing centered conversion (260.9), whose range contains
this whole segment for large $A$, and its accompanying ordinary
prime-power correction. Both give

$$
|\psi(A+t)-\psi(A)-t|\ll\varepsilon_A t
\qquad(t_0\le t\le A),
$$

including the already paid ordinary prime-power corrections.
The [existing full activation correction](../ArithSums/nicolas2025comparison.md#the-arithmetic-correction-vanishes-at-the-paid-heat-scale)
gives $|B(x)-\psi(x)|\ll\sqrt x\,[\log(2x)]^{5/2}$ for every
large real price coordinate $x$. Its two endpoint corrections are
$O(\sqrt A\,L^{5/2})=o(\varepsilon_A t_0)$, proving (P5).
No regularity or GA1 hypothesis is required of any future $C_b$.

Use the existing pressure from the
[Nicolas application](../ArithSums/nicolas2025comparison.md#the-same-source-price-minimum-gives-a-nonnegative-heat-cost),
with its almost-everywhere derivative:

$$
\begin{aligned}
P(x)&=\gamma+\log\log x-g(x)x
      -\max_{m\ge1}\{\log Z(m)-g(x)\log m\},\\
P'(x)&=k(x)[x-B(x)].
\end{aligned}
$$

The concavity tangent gap is

$$
H(b,B)=\log\log b+g(b)(B-b)-\log\log B\ge0.
$$

Since $B(A)=A$, the definitions give the exact identity
$X_N-X(b)=P(b)-P(A)-H(b,B(b))$.
The original $N$'s right-tail maximality supplies its nonnegative
left side. For $0\le t<t_0$, monotonicity gives
$A+t-B(A+t)\le t$; for $t\ge t_0$, (P5) and $B(A)=A$ give
$A+t-B(A+t)\le C_0\varepsilon_A t$.
Integrating the existing derivative against decreasing $k$ yields,
for one fixed $C_1>0$ and all $A\le b\le2A$,

$$
0\le X_N-X(b)
\le C_1 k(A)\left[A^{4/3}+\varepsilon_A(b-A)^2\right].
\tag{P6}
$$

The short initial segment is paid by $A^{4/3}$, rather than assigning
a favorable sign to any ordinary-prime error. The pressure comparison
retains $B(b)$ in the tangent gap; it does not identify $B(b)$ with $b$.

For example, at the already documented wider scale
$h=A^{3/4}e^{u/2}/L$, (P6) implies

$$
\sup_{A\le b\le A+h}T[X_N-X(b)]
\ll A^{-1/6}+\frac1L\longrightarrow0.
\tag{P7}
$$

This is the selected-source application of that existing scale,
not a new interpolation theorem or an upper bound for $X(b)$.
