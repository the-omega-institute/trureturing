---
bibkey: bourgainlindenstrauss2003entropy
authors: Jean Bourgain and Elon Lindenstrauss
year: 2003
title: Entropy of Quantum Limits
doi: 10.1007/s00220-002-0770-8
url: https://web.math.princeton.edu/~elonl/Publications/pos_entropy.pdf
claim: Theorem 5.1 gives reciprocal-prime mass greater than one half minus epsilon for positive nonsquare D at cutoff Y at least D to the power one quarter plus epsilon; its Robin application retains the actual discriminant, cutoff and multiplier exceptions.
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted nonresidue supply at the actual Robin cutoff

The article appeared in *Communications in Mathematical Physics* 233
(2003), 153–171, [DOI:10.1007/s00220-002-0770-8](https://doi.org/10.1007/s00220-002-0770-8).
The inspected full text is the 22-page
[author-hosted manuscript](https://web.math.princeton.edu/~elonl/Publications/pos_entropy.pdf),
linked from [Lindenstrauss's publication list](https://web.math.princeton.edu/~elonl/Publications/).
Theorem 5.1 is on printed p.15; its proof occupies pp.17–18.
The source statement, parameter dependence and the following application
were checked. The complete analytic proof was not independently verified,
and no Lean verification or new analytic theorem is claimed.

## The existing weighted theorem

For each fixed $\varepsilon>0$ there are $\alpha=\alpha(\varepsilon)>0$
and $D_0=D_0(\varepsilon)$ such that every **positive nonsquare integer**
$D\ge D_0$ and every real cutoff $Y\ge D^{1/4+\varepsilon}$ satisfy

$$
W_D(Y):=\sum_{\substack{Y^\alpha\le p\le Y\\(D/p)=-1}}\frac1p
>\frac12-\varepsilon.
$$

Here $p$ ranges over primes; the source's upper cutoff $N$ has been
renamed $Y$ to distinguish it from the target integer. Useful applications
take $0<\varepsilon<1/2$. Decreasing $\alpha$ preserves the lower bound,
so one may take $0<\alpha<1$. No numerical value of $\alpha$ or $D_0$
is certified by this note. The input is unconditional.

The statement uses the **original integer $D$**, without requiring it to
be squarefree. Its cutoff cannot be silently replaced by a power of the
squarefree kernel or the primitive conductor. For $D=dt^2$, primes
dividing $t$ have symbol zero in the original certificate, even if the
primitive character of $d$ is nonzero there. Negative $D$ and square $D$
are outside the statement used here.

[Pollack's prime nonresidue theorem](pollack2017nonresidues.md) gives a
smaller power-scale cutoff for prime counts. The present source instead
supplies the reciprocal weight needed in an Euler-product deficit. These
are established, distinct inputs; a new proof of either is unnecessary.

## The same-integer Euler budget

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already owns the norm certificates and Euler-product bookkeeping in
§§178,181,202,233. Their paper-level application to this source is recorded
here, without adding a theorem wrapper.

For the actual integer $n\ge8$, set

$$
Y=\log n,\qquad \Lambda=\log Y,\qquad
\mathcal P(Y)=\prod_{p\le Y}(1-p^{-1})^{-1},\qquad
M(Y)=\log\frac{\mathcal P(Y)}{e^\gamma\log Y}.
$$

Define quantities belonging to that same $n$:

$$
\begin{aligned}
J_{\rm miss}(n;Y)&=\sum_{\substack{p\le Y\\p\nmid n}}
\log\frac p{p-1},\\
J_{\rm large}(n;Y)&=\sum_{\substack{p\mid n\\p>Y}}
\log\frac p{p-1},\\
D_{\rm pow}(n)&=-\sum_{p\mid n}
\log(1-p^{-(v_p(n)+1)})\ge0.
\end{aligned}
$$

The finite Euler factors of $Z(n)=\sigma(n)/n$ give the exact ledger

$$
\log\frac{Z(n)}{e^\gamma\Lambda}
=M(Y)-J_{\rm miss}(n;Y)+J_{\rm large}(n;Y)-D_{\rm pow}(n).
$$

The large-prime count is at most $Y/\log Y$: their product divides $n$
and each logarithm exceeds $\log Y$. Since
$\log(p/(p-1))\le1/(p-1)$, the existing size bound is

$$
J_{\rm large}(n;Y)\le T(Y):=\frac{Y}{(Y-1)\log Y}
\le\frac2\Lambda.
$$

Thus a lower bound $J_{\rm miss}\ge r$ pays the budget when
$M(Y)+T(Y)-D_{\rm pow}(n)<r$. The sign of $M(Y)$ is not assumed.
The usual Mertens product theorem gives $M(Y)\to0$, and $T(Y)\to0$.
Along an actual source family with $n\to\infty$, if a **fixed** $r>0$
is eventually retained, this paper-level application gives
$\limsup Z(n)/(e^\gamma\log\log n)\le e^{-r}<1$.

## Primitive multiplicative sources retain their multiplier cost

Use §181's actual source $n=Cu$, with $C,u$ positive integers,
$u=2a+3b$, $\gcd(|a|,|b|)=1$, and
$D=-Q=-(a^2+ab-b^2)$ **positive and nonsquare**. Every odd prime
with $(D/p)=-1$ is excluded from $u$; it may still divide $C$.
Require $Y^\alpha>2$ before using this odd-prime certificate.

In the exact source window, write

$$
\mathcal S_D(Y)=\{p:Y^\alpha\le p\le Y,\ (D/p)=-1\},\qquad
E_C(Y)=\sum_{\substack{p\in\mathcal S_D(Y)\\p\mid C}}\frac1p.
$$

Every member of $\mathcal S_D(Y)$ not dividing $C$ misses $n$.
Using $\log(p/(p-1))\ge1/p$ therefore yields

$$
J_{\rm miss}(n;Y)\ge W_D(Y)-E_C(Y)
>\frac12-\varepsilon-E_C(Y).
$$

This cost uses the **same window and same negative-character set**.
A sufficient symbolic Robin budget is

$$
M(Y)+T(Y)-D_{\rm pow}(n)
<\frac12-\varepsilon-E_C(Y).
$$

The lower bound for $W_D$ requires the source's size and cutoff hypotheses.
For a finite certificate one can instead enumerate the actual $W_D$ and
$E_C$ and use certified bounds for the other terms. The unspecified
source thresholds alone do not supply such a certificate.
The actual-source examples in §§183,186 already show why a small
conductor cannot justify deleting the multiplier cost.

## The actual affine certificate avoids that subtraction

For §202's same actual integer

$$
n=h+gU,\qquad U=2a+3b,\qquad
Q=a^2+ab-b^2,\qquad D=5h^2-4g^2Q,
$$

assume $g\ge1$, $n\ge8$, and the **actual $D$ is positive and nonsquare**.
The existing identity with $c=4a+7b$ is

$$
(gc)^2-D=5n(n-2h).
$$

For every odd $p\mid n$, it gives $D\equiv(gc)^2\pmod p$.
Consequently an odd prime with $(D/p)=-1$ misses $n$ directly,
including when $p\mid g$ would otherwise have been an exception.
With $Y^\alpha>2$, this yields $J_{\rm miss}\ge W_D(Y)$ and the
sufficient budget

$$
M(Y)+T(Y)-D_{\rm pow}(n)<\frac12-\varepsilon.
$$

Primes dividing $D$, including its square part, have symbol zero and
never enter this negative set. No ramified prime has been declared
missing, and no multiplier or square-part cost has been discarded.
This uses the original affine $D$, not a substituted primitive conductor.

## A restricted growing-discriminant range, and the remaining gap

Fix $0<\delta<4$ and choose

$$
0<\varepsilon<\min\left\{\frac12,
\frac{\delta}{4(4-\delta)}\right\}.
$$

Along actual sources with $n\to\infty$, **positive nonsquare $D\to\infty$**
and $D\le(\log n)^{4-\delta}$, one has
$(4-\delta)(1/4+\varepsilon)<1$, so the cutoff $Y=\log n$ eventually
satisfies Theorem 5.1. It also eventually satisfies $Y^\alpha>2$.
For the affine certificate above, the known weighted theorem and existing
Euler budget therefore imply eventual strict Robin at paper level, with
$\limsup Z(n)/(e^\gamma\log\log n)\le e^{-(1/2-\varepsilon)}$.
The multiplicative route needs an additional eventual bound
$E_C(Y)\le1/2-\varepsilon-r$ for a fixed $r>0$.

This is an application of established literature, not a new analytic
estimate or a claim of originality. §201 already gives Robin for its
slow-norm families with its own multiplier conditions; their intersection
is not a new safe family. The growing **actual affine** discriminant range
above is not supplied by §202's elementary sufficient condition alone.
Fixed discriminants remain subject to the earlier source results rather
than an invented explicit threshold for Theorem 5.1.

For this weighted product route the cutoff is $Y=\log n$. Excluding a CA
integer by a single missing prime instead requires a prime at most the
actual support endpoint $P^+(n)$; no equality or comparison of these
cutoffs is assumed here.

General FIB sources can have negative, square, or much larger actual $D$,
and their multipliers can absorb the supplied negative primes. No uniform
all-candidate weighted deficit is supplied by this application. General
Robin and RH remain unresolved; this note identifies an existing usable
input and its exact remaining interface.

The [Graham–Ringrose lower bound](grahamringrose1990least.md) already rules
out an unrestricted logarithmic nonresidue supply based only on conductor.
[Banks et al.](banksgaraevheathbrownshparlinski2008density.md) supply a
smaller prime-conductor cutoff, but their guaranteed weight includes two
and needs the actual exception budget. The
[2026 smooth-modulus estimate](cochranegranvillezheng2026smooth.md) requires
its own modulus class and length conditions. These inputs guide the
remaining family-specific research; none supplies an all-source substitute
for those conditions.
