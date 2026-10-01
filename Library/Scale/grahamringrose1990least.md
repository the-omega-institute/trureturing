---
bibkey: grahamringrose1990least
authors: S. W. Graham and C. J. Ringrose
year: 1990
title: Lower Bounds for Least Quadratic Non-Residues
doi: 10.1007/978-1-4612-3464-7_18
url: https://page-one.springer.com/pdf/preview/10.1007/978-1-4612-3464-7_18
claim: Theorem 1 gives infinitely many prime moduli whose least nonresidue exceeds a constant times log p times log log log p, ruling out a uniform positive negative-character prime weight at a fixed logarithmic cutoff for unrestricted quadratic characters.
strata_touched: []
license: citation-only
triage: anchor
---

# The generic logarithmic nonresidue route has a classical obstruction

The chapter appeared in *Analytic Number Theory*, Progress in Mathematics
85 (1990), 269–309,
[DOI:10.1007/978-1-4612-3464-7_18](https://doi.org/10.1007/978-1-4612-3464-7_18).
The inspected primary source is the publisher's
[two-page preview](https://page-one.springer.com/pdf/preview/10.1007/978-1-4612-3464-7_18).
Theorem 1 is on printed p.269. The full chapter was not obtained; this is
a check of the original statement and its parameter consequence, not an
independent audit of the full proof or a Lean verification.

## The actual lower-bound quantifiers

Let $n_p$ be the least positive integer that is a quadratic nonresidue
modulo the prime $p$. Theorem 1 unconditionally states

$$
n_p=\Omega(\log p\,\log\log\log p).
$$

The introduction explains this lower-bound convention as the existence of
an absolute $c>0$ and infinitely many primes satisfying
$n_p\ge c\log p\,\log\log\log p$. It is not a lower bound for every
prime and does not specify a congruence class modulo four.

For every fixed $A>0$, the same unbounded sequence eventually has
$n_p>A\log p$. There is then no prime, or integer, nonresidue up to
$A\log p$, and hence

$$
\sum_{\substack{\ell\le A\log p\\(\ell/p)=-1}}\frac1\ell=0
$$

for infinitely many prime conductors. Thus an assertion of uniformly
positive negative-character prime weight at $A\log q$ for all large
quadratic conductors is false. This does not conflict with the much larger
cutoffs of [Bourgain–Lindenstrauss](bourgainlindenstrauss2003entropy.md),
[Banks et al.](banksgaraevheathbrownshparlinski2008density.md), or
[Pollack](pollack2017nonresidues.md).

## What this does and does not exclude in FIB

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§182's $q_D<4N/g^2$ does not, on its own, exclude a conductor comparable
to $N$. At that scale a cutoff $\log N$ is comparable to $\log q_D$,
so a generic conductor-only nonresidue supply cannot fill the gap.

Applying this obstruction to actual FIB sources would additionally require
realizing these quadratic characters in actual FIB sources and retaining
the needed relation between $N$ and $q_D$. The construction below realizes
a related obstruction on canonical sources, with three retained as a ramified
prime. It does not realize the theorem's particular prime-conductor characters
or establish $q_D\asymp N$. Neither obstruction implies that the actual integer
has no missing small primes: missing primes may have positive character value.

The unresolved task is therefore to exploit a restriction of the **same
actual FIB source**, control its conductor relative to $N$, or supply a
different actual weighted deficit. This source refutes the unrestricted
logarithmic character assertion, not Robin, RH, or every family-specific
FIB route.

## A canonical source with vanishing logarithmic character weight

The local-residue mechanism is classical. Pomerance and Shparlinski,
*On Pseudosquares and Pseudopowers*, in *Combinatorial Number Theory*
(2009), 171–184,
[DOI:10.1515/9783110208504.171](https://doi.org/10.1515/9783110208504.171),
define an $x$-pseudosquare on p.2 of
[arXiv:0712.1081v2](https://arxiv.org/pdf/0712.1081v2), dated 17 December
2007: a positive nonsquare, congruent to one modulo eight, with Legendre
symbol one at every odd prime up to $x$. Their p.3 records a classical
pigeonhole construction and Theorem 1 on equidistribution. Those analytic
results are not reproved or used as a distribution theorem for the polynomial
below. Here three divides the fundamental discriminant, so the constructed
integers are **not standard pseudosquares**.

Closer polynomial and recent character interfaces are also already available:

* Lamzouri, *Extreme values of class numbers of real quadratic fields*,
  [arXiv:1501.01003v2](https://arxiv.org/pdf/1501.01003v2), dated
  6 February 2015, Corollary 2.2 on p.4: for
  $\sqrt{\log X}\le y\le(\log X)/8$, at least
  $X^{1/2}\exp(-y(1+o(1)))$ squarefree discriminants
  $d=4t^2+1\le X$ have $\chi_d(p)=1$ at every prime $p\le y$.
  Its preceding Lemma 2.1 is attributed to Montgomery–Weinberger,
  *Real quadratic fields with large class number*, Mathematische Annalen
  225 (1977), 173–176,
  [DOI:10.1007/BF01351721](https://doi.org/10.1007/BF01351721).
  This supplies a polynomial fundamental-discriminant family directly,
  but for $4t^2+1$, without the unit-one FIB identification or the
  prescribed ramification at three.
* Farashahi–Shparlinski, *On Pseudopoints of Algebraic Curves*,
  [arXiv:1005.4775v1](https://arxiv.org/pdf/1005.4775v1), submitted
  26 May 2010, Theorem 1 on p.2: for fixed absolutely irreducible
  $f(U,V)\in\mathbb Z[U,V]$ with $\deg_V f\ge2$, the least
  $x$-pseudopoint satisfies $N_f(x)\le M_f(x)^{1/2+o(1)}$.
  Here $M_f(x)$ multiplies the primes at most $x$ for which the curve
  has a modular point. A pseudopoint is an integer first coordinate
  having a modular second coordinate at all those primes, while having
  no integer second coordinate solving $f=0$. The published article is
  Archiv der Mathematik 95 (2010), 529–537,
  [DOI:10.1007/s00013-010-0200-7](https://doi.org/10.1007/s00013-010-0200-7).
  This is the relevant local-solubility framework for
  $f(U,V)=4U^2+5-V^2$. Raw modular zeros are permitted, so the theorem
  alone does not ensure their persistence after removal of a square part,
  nor supply the actual canonical FIB source.
* Lamzouri, *A note on large values of Dirichlet $L$-functions for
  characters of fixed order at $1/2<\sigma\le1$*,
  [arXiv:2606.09818v1](https://arxiv.org/pdf/2606.09818v1), submitted
  8 June 2026, §2 equations (2.2)–(2.3) and Lemma 2.2 on p.4:
  specialize to order two and take $X$ large,
  $2\le y\le(\log X)^2$, with
  $2^{\pi(y)+2}\le c_0\sqrt X/\log X$ for a suitably small
  absolute $c_0>0$. The family formed by pairs of distinct primes in
  $(\sqrt X/2,\sqrt X)$ with matching quadratic-character vectors at
  primes up to $y$ contains
  $\gg X/(2^{\pi(y)+2}(\log X)^2)$ primitive quadratic characters.
  Their conductors lie in $(X/4,X)$ and they equal one at every
  prime at most $y$. This is an existing direct character supplier,
  not a claim about discriminants of the form $4g^2+5$ or extremal
  Robin integers. Its almost-positivity conclusion averages over this
  character family; it is not pointwise positivity of one actual source.

The linked original PDFs and arXiv version histories supply these statements
and dates. Montgomery–Weinberger's full proof was not inspected here;
its recorded input is read through Lamzouri's exact attribution. The
applications below do not redo these constructions or transfer their
distribution bounds to a different polynomial. This is a bounded source
comparison, not a complete literature survey or a novelty certificate.

The necessary interface is a common realization of local character values,
canonical unit initialization and size at the actual cutoff. It uses
[the FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§182.1 and 205.1 directly. The following is a paper-level construction,
without a claim of originality or Lean verification.

For each real $z\ge5$, define

$$
P_z=\prod_{5\le p\le z}p,\qquad
k_z=\begin{cases}6,&P_z\equiv2\pmod3,\\
12,&P_z\equiv1\pmod3,\end{cases}
\qquad g_z=1+k_zP_z,
$$

where every product index is prime. Let $j_z$ be the least positive integer
congruent to one modulo six for which $F_{j_z}>2g_z$, with $F_0=0,F_1=1$.
Write $g=g_z,j=j_z$ and set

$$
x=(A,B)=gM^j\alpha,
\quad M(a,b)=(b,a+b),\quad\alpha=(1,0),
\quad h=1,\quad n=gF_{j+3}+1,
\quad D=4g^2+5.
$$

The same family has all of the following properties:

$$
\begin{gathered}
x\text{ is the actual canonical five-window composition of }n
\text{ with external unit bit }h=1,\\
2g^2<n\le210g^2+1,\qquad
D\text{ is positive and nonsquare},\qquad D\asymp n,\\
\log n=2\vartheta(z)+O(1)\sim2z,
\qquad\vartheta(z)=\sum_{p\le z}\log p.
\end{gathered}
$$

To identify the source, $j$ is odd and $F_j<\varphi^j$, so

$$
-\tfrac12<g\psi^j<0,\qquad
\varphi=(1+\sqrt5)/2,\quad\psi=-\varphi^{-1}.
$$

This is inside §205.1's sufficient unit-one window
$(-1,\varphi-1)$; that existing result supplies the actual canonical
composition, seam and unit initialization. Also
$Q(A,B)=A^2+AB-B^2=-g^2$, so the actual unit-one discriminant
$5-4Q(A,B)$ is exactly $D$. If $c=4A+7B$, the existing same-source
identity remains

$$
c^2-D=5n(n-2).
$$

The choice of $k_z$ gives $g$ odd and $g\equiv4\pmod9$.
Consequently $n$ is even, since $j+3\equiv1\pmod3$ and $F_{j+3}$
is odd. The inequalities
$(2g)^2<D<(2g+1)^2$ follow from $g>1$.
Minimality gives $F_{j-6}\le2g$; here $g\ge31$ and $j\ge13$,
so this index is valid. The usual Fibonacci recurrence yields

$$
F_j=13F_{j-6}+8F_{j-7}\le21F_{j-6},
\qquad F_{j+3}=3F_j+2F_{j-1}\le5F_j.
$$

Together with $F_{j+3}>F_j>2g$, these give the stated size bounds.
Since $\log P_z=\vartheta(z)-\log6$ and $k_z\in\{6,12\}$,
$\log g=\vartheta(z)+O(1)$. The asymptotic uses the ordinary prime
number theorem; no new prime-count estimate is supplied.

Write $D=\delta s^2$ with $s\ge1$ and $\delta>1$ positive squarefree.
Because $D\equiv1\pmod8$, $s$ is odd and $\delta\equiv1\pmod8$;
thus $\delta$ itself is the fundamental discriminant. The primitive real
nonprincipal character $\chi_\delta$ satisfies

$$
\chi_\delta(2)=1,\qquad
\chi_\delta(3)=0,\qquad
\chi_\delta(p)=1\quad(5\le p\le z).
$$

Indeed, $D\equiv6\pmod9$ gives $v_3(D)=1$, so three remains in
$\delta$. For every prime $5\le p\le z$, $g\equiv1\pmod p$ and
$D\equiv9\pmod p$; the latter is a nonzero square, so $p$ divides
neither $D$ nor $s$, and square removal preserves the positive symbol.
There is therefore no negative-character prime up to $z$, with zeros
retained rather than converted to positive values.

Let $Y=\log n$ and use the Robin ledger's prime weight:

$$
W_\delta^{\log}(Y)
=\sum_{\substack{p\le Y\\\chi_\delta(p)=-1}}
\log\frac p{p-1}.
$$

As $z\to\infty$, eventually $z<Y\le3z$. Hence

$$
0\le W_\delta^{\log}(Y)
\le\sum_{z<p\le Y}\log\frac p{p-1}
\le\frac{\pi(3z)}{z-1}
=O(1/\log z)\longrightarrow0.
$$

Only the usual Chebyshev prime-count upper bound is needed in this final
step. Thus actual canonicality together with $D\asymp n$ does not force
a fixed positive negative-character weight at $Y=\log n$.

This family is not established to be SA or CA, near the Robin boundary,
or a Robin counterexample. The conductor $q=\delta$ can be smaller than
$D$; $D\asymp n$ does not assert $q\asymp n$. Actual missing primes can
have positive or zero character, and a weight tending to zero can still pay
a budget tending to zero. The construction only excludes a fixed positive
character-supply estimate based on the two stated source conditions.
