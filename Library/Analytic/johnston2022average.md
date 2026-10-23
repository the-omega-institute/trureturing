---
bibkey: johnston2022average
authors: Daniel R. Johnston
year: 2022
title: On the average value of π(t) - li(t)
doi: 10.4153/S0008439522000212
url: https://arxiv.org/abs/2201.06184v2
claim: The unconditional negative primitive anchored at 2 transfers to the Robin kernel, but does not provide a lower bound for a tail starting at the same actual self-clock integer.
strata_touched: []
license: citation-only
triage: anchor
---

# An existing signed primitive and its fixed lower endpoint

The inspected primary is [arXiv:2201.06184v2](https://arxiv.org/pdf/2201.06184v2),
revised 7 March 2022; the title page is dated 8 March 2022. It has
11 pages, 162,473 bytes and SHA-256
`75bc30df5b939e57e1cefef216e5e252f7fb29cdc9dfb5b5403f8c5f26ebcd74`.
The journal DOI above is bibliographic metadata confirmed through Crossref;
the journal edition was not inspected. All theorem and page locators below
refer to this manuscript. The note cites its results rather than reproducing
its proofs or finite computations; no Lean certification is supplied.

## The unconditional result includes the full Chebyshev function

Theorem 1.3, printed p.2, proves, unconditionally and for every real $x>2$,

$$
F_\psi(x):=\int_2^x\frac{\psi(t)-t}{t^2}\,dt<0,
\qquad \psi(t)=\sum_{p^j\le t}\log p.
\tag{J1}
$$

Its other three conclusions use $(\pi(t)-\operatorname{li}(t))/t^2$,
$(\vartheta(t)-t)/t^2$ and $(\Pi(t)-\operatorname{li}(t))/t^2$,
where $\Pi(t)=\sum_{p^j\le t}1/j$ and
$\vartheta(t)=\sum_{p\le t}\log p$.
The logarithmic integral has the ordinary principal-value-from-zero
normalization. These four functions and their weights are distinct;
the last conclusion in the theorem supplies (J1) directly, including
every prime-power layer.

The proof in §4, printed pp.7–8, uses explicit Mertens estimates, the
paper's prime/prime-power comparisons and a stated finite initial-range
calculation. Those existing arguments and computations are not rerun here.

## The nearby RH criteria have a different weight and function

Theorem 1.1, printed p.1, gives

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\int_2^x(\pi(t)-\operatorname{li}(t))\,dt<0
\quad\text{for every real }x>2.
$$

Theorem 1.2, printed p.2, gives the analogous equivalence with
$\int_2^x(\vartheta(t)-t)\,dt<0$.
The paragraph following Theorem 1.3 and Lemma 2.8 distinguish these
from the unweighted primitives using $\Pi$ or $\psi$, which change
sign infinitely often. Neither the unweighted RH criterion nor the
unconditional weighted criterion permits exchanging these functions.

Theorem 1.4, printed p.2, assumes
$\omega=\sup\{\Re s:\zeta(s)=0\}>1/2$ and $c<1+\omega$.
It gives positive values at arbitrarily large arguments for the four primitives
weighted by $t^{-c}$. The manuscript denotes this by $\Omega_+(1)$
and explicitly defines that notation here as arbitrarily large
arguments with positive value; this note asserts no additional uniform
positive magnitude. This zero-location obstruction is also about
primitives anchored at 2, not the endogenous CA tail.

## Direct transport to the existing Robin kernel

For $t\ge2$ put

$$
r(t)=\frac{1+\log t}{\log^2t},\qquad
k(t)=\frac{r(t)}{t^2},\qquad
r'(t)=-\frac{\log t+2}{t\log^3t}<0,
$$

and define $J(x)=\int_2^x(\psi(t)-t)k(t)\,dt$.
The finite integration-by-parts identity is

$$
J(x)=r(x)F_\psi(x)-\int_2^x r'(t)F_\psi(t)\,dt.
\tag{J2}
$$

Since $r>0$, $r'<0$ and (J1) gives $F_\psi(t)<0$ for $t>2$,
both terms in (J2) are negative for $x>2$. Thus the cited theorem
also supplies $J(x)<0$ with the exact Robin kernel. This is an
application by a positive decreasing weight and finite partial
integration, not a new theorem or a second proof of Theorem 1.3.

The [existing unconditional Chebyshev error supplier](../Weil/johnstonyang2022pnt.md)
already provides absolute convergence of these fixed-anchor weighted
integrals on the infinite tail. Write $J_\infty=\lim_{x\to\infty}J(x)$.
For an actual self-clock integer $N$ with $A=\log N>2$, the complete
quantity in the
[regular-source signed target](../Arith/caveney2012sacaga.md#restrict-the-unpaid-signed-estimate-to-this-joint-source-class)
is exactly

$$
I_\psi(A)=J_\infty-J(A).
\tag{J3}
$$

The assertion $J(A)<0$ does not compare $J(A)$ with $J_\infty$.
In particular, the requested eventual floor
$\sqrt A\log A\,I_\psi(A)\ge-M$ requires

$$
J(A)\le J_\infty+\frac{M}{\sqrt A\log A}
\tag{J4}
$$

on the same actual source class. Theorem 1.3 supplies no CA,
right-tail-maximality or proper GA1 hypothesis, and no estimate in
(J4). Its fixed-anchor negative bias cannot be substituted for that
centered comparison. No new absolute-envelope calculation, scalar
countermodel, finite source search or signed Robin margin is asserted.
