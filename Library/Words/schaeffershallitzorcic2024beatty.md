---
bibkey: schaeffershallitzorcic2024beatty
authors: Luke Schaeffer; Jeffrey Shallit; Stefan Zorcic
year: 2024
title: "Beatty Sequences for a Quadratic Irrational: Decidability and Applications"
doi: 10.48550/arXiv.2402.08331
url: https://arxiv.org/abs/2402.08331v3
claim: "Theorem 9 and the first-order construction in Theorem 2 supply synchronized golden Beatty readouts and fixed-modulus FIB predicates; they do not supply moving-modulus estimates on actual CA sources."
strata_touched: []
license: citation-only
triage: anchor
---

# Reuse the quadratic Beatty automaton at the FIB arithmetic boundary

The inspected primary text is
[arXiv:2402.08331v3](https://arxiv.org/html/2402.08331v3), revised
2 April 2026. The initial submission is from 2024. The source statements
in §4, Theorem 2, and §5, Theorem 9 and Corollary 11, were checked.
The complete proof and Walnut implementation were not independently
verified. The applications below are paper-level parameter mappings,
without a new automaton construction, originality claim or Lean verification.

## The reusable source interface

Theorem 9 assumes a quadratic irrational $0<\gamma<1$ with a purely
periodic continued fraction after its initial zero. For
$\alpha,\beta\in\mathbb Q(\gamma)$ with $\alpha\ge0$ and
$\alpha+\beta\ge0$, the sequence

$$
(\lfloor n\alpha+\beta\rfloor)_{n\ge1}
$$

is $\gamma$-Ostrowski synchronized: a finite automaton recognizes the
padded paired representations of the input and its output. This is a
graph-recognition statement, not a fixed number of possible numerical outputs.

Theorem 2 supplies an algorithm for constructing synchronized automata
from first-order formulas using addition, subtraction, multiplication
by **constants**, automatic sequences and synchronized sequences.
Corollary 11 gives decidability of the first-order theory with addition
and the indicated quadratic Beatty function. This automata input is
already established and need not be reproved for each FIB predicate.

Use

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\gamma=\varphi-1=[0;\overline1],\qquad
\alpha=\varphi=1+\gamma,\quad\beta=0.
$$

The hypotheses hold, and the source supplies the synchronized graph of
$G(n)=\lfloor n\varphi\rfloor$ for $n\ge1$. Its value $G(0)=0$ can be
adjoined as a finite case. In the paper's convention, $q_i=F_{i+1}$ and
$e_0=0$; the unit bit is $e_1$. Thus the $\gamma$-Ostrowski representation
is the usual Fibonacci digit word followed by zero. For repository
windows $b_j=(b_{j,0},b_{j,1},b_{j,2})$ listed low to high, read the
windows in reverse order, reverse each block's bits, and append $h\,0$.
Apply leading-zero padding to paired automaton tracks while preserving
canonical End restrictions and every adjacency seam, including
$h\,b_{0,0}=0$. Handle zero separately. For example, $n=1$ is represented
by `10` in this convention. This fixed-length recoding transports graph
recognition; it does not identify the unit bit with occupancy of the
numerical term 2, or identify five letters with five machine states.

## The same canonical source and a fixed square-depth test

The existing
[canonical rotation interface](../ArithSums/guloglunevans2008beatty.md)
provides, for the actual integer $n>0$, the unit-bit window

$$
h(n)=1\iff a<\{n\varphi\}<2a,
\qquad a=2-\varphi,
$$

and, in that branch, the actual composition lift

$$
n=1+2A+3B,\qquad c=4A+7B=2G(n)-n-1.
$$

These are reused identities. Their finite-automaton application is
particularly direct. The unit branch is equivalently

$$
G(n+1)=G(n)+2,\qquad G(n+2)=G(n)+3.
$$

Indeed, with $r=\{n\varphi\}$, the two equalities say respectively
$r>a$ and $r<2a$; no positive integer hits the endpoints.
Writing $u=G(n)$, the lift graph uses only the integer-linear relation
$2u=n+c+1$.

For every **fixed** positive integer $d$, the same-source predicate

$$
n>2,\qquad h(n)=1,\qquad d\mid n,\quad d\mid c(n)
$$

is therefore obtained by the source's first-order construction: use
$u=G(n)$, the two neighboring-readout equalities, and quantified
$t,v\in\mathbb N$ with $n=dt$, $c=dv$, $2u=n+c+1$.
For each fixed prime $p$ and fixed $k\ge1$, choosing $d=p^k$ gives an
exact test of the required depth. An exact exponent $v_p(n)=2k$ can
also be selected using the fixed congruences
$p^{2k}\mid n$ and $p^{2k+1}\nmid n$.

This reuses existing synchronized readouts and formula closure. It
asserts existence of an appropriate machine for each fixed parameter;
no machine was generated here, no uniform state bound is claimed, and
these predicates do not select CA integers.

## Why this does not yet estimate the Robin exceptions

The actual
[prime-power mask](../Scale/pollack2017nonresidues.md), (P1)–(P4), uses
$c(n)$ from this same lift, a nonsquare
$D=5-4(A^2+AB-B^2)=\delta s^2$, and
$m_1=\operatorname{lcm}(|\delta|,R_1)$. Its exceptional primes and
square depths vary with the actual integer. For $r\ge1$, the moment
needed in (T17) is

$$
M_r(n)=
\sum_{\substack{p\le P,\ p\ne2,5\\v_p(n)>0\ \mathrm{even}\\
p^{v_p(n)/2}\mid c(n)}}
\frac{\log p}{p}\left(r-\frac{\log p}{\log P}\right),
\qquad P=P^+(n).
$$

The fixed-parameter machine family can evaluate specified local tests.
It does not bound this weighted sum at every actual CA maximizer,
including intermediate tied choices. If $d$ is another input instead
of a constant, the displayed witness relations use the products $dt$
and $dv$; these are outside the multiplication-by-constants syntax
used above. The source consequently does not establish that unrestricted
variable-divisibility relation by the same construction. This limitation
of the cited construction is not an impossibility theorem for the
restricted FIB or CA predicate.

Nor does exact recognition provide a signed prime-error bound.
The [same-integer Euler ledger](../Scale/bourgainlindenstrauss2003entropy.md)
and the [signed Robin comparison](../ArithSums/nicolas2025comparison.md)
require quantitative control at the actual candidate and cutoff.
Counting accepted ordinary integers, or replacing that population by a
sparse CA sequence without a transfer theorem, does not discharge those
conditions. The actual large-mask restriction (T22)–(T23) also prevents
silently restoring the old sufficient polynomial-mask cutoff.

The reusable result is the existing automaton for the golden readout
and its fixed-parameter arithmetic predicates. The missing relation is
an estimate uniform over the moving prime powers, their joint membership
in this actual lift, and the CA test set, strong enough to cross the
same-source signed Robin budget. No such estimate, general Robin
inequality or RH conclusion is supplied by this source application.


## A fixed finite-state selector cannot retain an infinite CA family

This is a structural application of ordinary regular-language pumping,
finite permutation periodicity and the classical CA support. It is not
a theorem attributed to Schaeffer–Shallit–Zorcic or a new analytic bound.
The existing [five-window word interface](../../docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md),
§§7.2, 14.1 and 17.2–17.3, supplies the canonical coding and affine
pumping scaffold; no new generic pumping theorem is needed.

Use the **unique** high-to-low canonical word with no leading
$\mathrm{null}$, the independent unit bit in exactly one terminal
symbol, and all existing End and adjacency restrictions. Arbitrary
high-end padding and freely positioned End symbols are outside this
contract. Every regular language contained entirely in positive CA
words under this coding is finite.

To see this, an infinite regular language would contain all words
$uv^kw$, $k\ge0$, for some nonempty pump block $v$. The terminal symbol
cannot occur in $v$, since deletion or duplication would violate the
one-terminal-symbol condition. Thus $v$ consists of windows. All the
pumped words remain canonical; with $H_k=H_0+k|v|$ windows their
positive values satisfy $n_k\ge F_{3H_k}$ and tend to infinity.

The Horner map of $v$ is

$$
F_v(x)=Ax+b,\qquad A=S^{|v|},\quad S=M^3,\quad\det S=-1.
$$

If $z=F_u(0)$ and $F_w(x)=Bx+d$ denotes only the window part of the
suffix, its unit bit $h$ is fixed and

$$
n_k=h+q\bigl(BF_v^k(z)+d\bigr),\qquad q=(2,3).
$$

For each fixed prime $p$, $F_v$ is a permutation of
$(\mathbb Z/p\mathbb Z)^2$. The orbit of $z$ is consequently purely
periodic from $k=0$, and so is $n_k\bmod p$.

The [classical CA support](../Arith/alaoglu1944highly.md) contains every
prime through the actual $P^+(n_k)$, including every tied choice.
The only additional fact needed is $P^+(n_k)\to\infty$ when
$n_k\to\infty$ within the CA set. This follows from the classical
optimizing objective: if support is bounded by $T$, the next omitted
prime forces a fixed positive lower bound on the optimizing price.
At that price each included prime exponent is bounded, since its last
local gain tends to one as the exponent grows. Only finitely many
profiles have that bounded support. This uses the existing
[CA price interface](../ArithSums/nicolas2025comparison.md), without
importing a branch-restricted discriminant assumption or a new
prime-distribution estimate.

It follows that $p\mid n_k$ for all sufficiently large $k$.
Periodicity then implies $p\mid n_0$. Since this holds for every prime,
it contradicts $n_0$ being a finite positive integer. This proves the
finite-language assertion. The classical CA family is infinite: as the
price tends to zero, every fixed prime's positive first local gain
forces its eventual inclusion. Hence its full canonical language is
not regular either.

The scope is exact finite-state selection of an infinite CA family.
A regular **superset** of candidates, a finite verification range,
and a recursive algorithm whose state or working memory grows are
not excluded. The five letters remain a valid unbounded address
alphabet, and the fixed-prime-power predicates above remain regular.
This application gives no Robin sign and excludes no actual CA
integer; it identifies why a fixed number of states cannot replace the
moving arithmetic information needed by the full candidate test set.
