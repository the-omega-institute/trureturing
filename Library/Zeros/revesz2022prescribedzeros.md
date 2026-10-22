---
bibkey: revesz2022prescribedzeros
authors: Szilard Gy. Revesz
year: 2022
title: Oscillation of the remainder term in the prime number theorem of Beurling, caused by a given zeta-zero
doi: null
url: https://arxiv.org/abs/2202.01837v3
claim: Theorem 8 realizes prescribed zeros in a discrete Beurling system. Its application below tests the joint Robin-source constraints with full prime powers and reserve, without an ordinary-integer bound.
strata_touched: []
license: citation-only
triage: anchor
---

# Prescribed Beurling zeros and the joint Robin-source boundary

The inspected primary is [arXiv:2202.01837v3](https://arxiv.org/pdf/2202.01837v3),
whose arXiv version stamp is 15 September 2022. The PDF has 28 pages and
SHA-256 `513da18b5e8c9054f5cce499ae5c32340aff60640b759b1ddd3a66eaee772f89`.
Section 7, printed pp.16–22, especially equations (50)–(51), their
Chebyshev consequence on p.17, and Theorem 8 on pp.21–22, were read.
The complete source proof and a journal-version correspondence have not
been independently audited. No source text is vendored or Lean/kernel
verification claimed.

## Reuse the prescribed-zero construction

Theorem 8 takes $1/2\le r<1$ and a finite conjugation-symmetric multiset
$\mathcal S$ with $r<\Re\rho<1$. At $r=1/2$, choose once and for all

$$
\mathcal S=\{\rho,\bar\rho\},\qquad
\rho=\beta+i\tau,\qquad 1/2<\beta<1,\quad \tau>0.
$$

The frequency $\tau$ is fixed; it may exceed any specified finite height.
It supplies one discrete Beurling system, with prime generators of norms
$p>1$, for which, for every fixed $\varepsilon>0$,

$$
\mathcal N(x)=\kappa x+O_\varepsilon(x^{1/2+\varepsilon}),\qquad
\psi_{\mathcal P}(x)-x=-2\Re\frac{x^\rho}{\rho}+O(\sqrt x).
\tag{RJ1}
$$

Its construction also supplies
$\theta_{\mathcal P}(x)=f_0(x)+O(\log x)$, with $f_0'(x)=1+o(1)$.
This local information is read from (50)–(51) and the p.17 calculation;
it is stronger than the $O(\sqrt x)$ error alone. The source explicitly
uses the published [Broucke–Vindas realization](../Analytic/brouckevindas2024discretization.md).
Neither that construction nor the prescribed-zero theorem is re-proved.

A generalized integer here is a finite exponent vector in the free
commutative semigroup on those prime generators. Its norm is
$|\mathfrak n|=\prod p^{a_p}$. Distinct vectors remain distinct even
when their real norms coincide. All counts retain that multiplicity.
Define

$$
Z_{\mathcal P}(\mathfrak n)=\prod_p
\frac{1-p^{-a_p-1}}{1-p^{-1}},\qquad
G_{\mathcal P}(\mathfrak n)=
\frac{Z_{\mathcal P}(\mathfrak n)}{\log\log|\mathfrak n|}
\quad(|\mathfrak n|>e).
$$

The application below concerns these actual vectors, not independently
chosen support and exponent bounds. Its additional argument transports
the prescribed oscillation to their joint extremal sources. This is a
paper application, without a literature-priority or formal-certification
claim.

## Normalize once while preserving any finite ordinary prefix

Fix any $D\ge2$. Replace the finitely many prime generators of norm at
most $D$ by exactly one generator for each ordinary prime at most $D$.
The remaining prime harmonic sum still diverges. Delete finitely many
further generators of norm greater than $D$ so that the residue
$\kappa'$ lies in $(0,1)$. Choose an integer $m\ge1$ large enough that

$$
q=(1-(\kappa')^{1/m})^{-1}>D,
$$

and add $m$ distinct generators, each of norm $q$. The new residue is
exactly $\kappa'/(1-q^{-1})^m=1$. No generator of norm at most $D$
is changed by these last two steps.

A finite change of generators changes $\psi_{\mathcal P}(x)$ by
$O(\log x)$ and eventually changes $\theta_{\mathcal P}(x)$ by a
constant. Finite inclusion–exclusion handles deletion. For each insertion,
$\mathcal N_{\rm new}(x)=\sum_{q^k\le x}\mathcal N_{\rm old}(x/q^k)$
and its error is a convergent geometric sum. Iterating this finite
number of times gives

$$
\mathcal N(x)=x+O_\varepsilon(x^{1/2+\varepsilon}).
\tag{RJ2}
$$

Thus (RJ1) and the local $\theta$ property survive. All following
sources belong to this one fixed normalized system. Added generators
remain distinct labels when their norms coincide. Its prime prefix,
generalized integers, and divisor weights up to $D$ now agree exactly
with the ordinary ones; in particular $\mathcal N(x)=\lfloor x\rfloor$
for $1\le x\le D$.

The finite Euler factors have zeros and poles only on $\Re s=0$.
Thus the prescribed right-half-plane zeros are unchanged. Choosing
$\tau>H$ for any fixed $H$ also preserves absence of zeros in
$\Re s>1/2$, $|\Im s|\le H$. This does not prescribe the ordinary
critical-line zero table. All constants may depend on the fixed
$D,H,\beta,\tau$ and finite modifications; no uniformity as these grow
is asserted.

## Keep the actual CA pressure and its complete reserve

For $t>1$, put
$g(t)=1/(t\log t)$ and $w(t)=-g'(t)=(1+\log t)/(t^2\log^2t)$.
Define the actual pressure and an auxiliary pressure by

$$
\mathscr F(\epsilon)=\max_{\mathfrak n}
\{\log Z_{\mathcal P}(\mathfrak n)-\epsilon\log|\mathfrak n|\},\qquad
\mathscr F_0(\epsilon)=\sum_{p,k\ge1}
\left(\frac1{kp^k}-\epsilon\log p\right)_+.
$$

Both optimizations have finite support at every positive price. The
actual successive local gains are
$d_{p,k}=\log(1+1/(p+\cdots+p^k))$, strictly decreasing in $k$.
The auxiliary gain is selected at $\epsilon=g(t)$ exactly when
$p^k\le t$, with zero gain at equality. Hence, retaining inclusive
prime powers,

$$
\mathscr F_0(g(t))=J(t)-g(t)\psi_{\mathcal P}(t),\qquad
J(t)=\sum_{p^k\le t}\frac1{kp^k}.
$$

Set

$$
P(t)=\gamma+\log\log t-\frac1{\log t}-\mathscr F(g(t)),\qquad
R(t)=\mathscr F_0(g(t))-\mathscr F(g(t)).
\tag{RJ3}
$$

Here $R$ is the full difference of the actual optimized pressures.
For $0<z<1$ and integers $a\ge0$, the elementary comparison is

$$
D_a(z)=\sum_{k=1}^a\frac{z^k}{k}-\log(1+z+\cdots+z^a),\qquad
0\le D_a(z)\le-\log(1-z^{a+1}).
$$

Indeed,
$D_a'(z)=z^a((a+1)/(1-z^{a+1})-1/(1-z))\ge0$ and $D_a(0)=0$;
the upper bound follows by summing the missing logarithmic tail.
If $a_p$ is the actual optimal exponent and
$b_p=\lfloor\log t/\log p\rfloor$, evaluating each local objective
at the other's maximizer gives

$$
D_{a_p}(p^{-1})\le\mathscr F_{0,p}(g(t))-\mathscr F_p(g(t))
\le D_{b_p}(p^{-1}).
$$

For $p>t$, both exponents vanish. For $p\le\sqrt t$,
$p^{b_p+1}>t$; for $\sqrt t<p\le t$, $b_p=1$.
Using $\pi_{\mathcal P}(x)\ll x/\log x$ and
$\sum_{p>y}p^{-2}\ll1/(y\log y)$ therefore gives

$$
0\le R(t)\le\sum_{p\le t}-\log(1-p^{-b_p-1})
\ll\frac1{\sqrt t\log t}.
\tag{RJ4}
$$

The constant in the Mertens expression must also be kept. By (RJ1),
$J(t)-\log\log t\to C$. Abelian integration at $z\downarrow0$ yields

$$
\log\zeta_{\mathcal P}(1+z)
=z\int_0^\infty e^{-zv}J(e^v)\,dv
=-\log z+C-\gamma+o(1).
$$

The normalized residue is one, so $C=\gamma$. Stieltjes integration
by parts now gives the exact full-tail identities

$$
\begin{aligned}
I(t)&=\int_t^\infty(\psi_{\mathcal P}(u)-u)w(u)\,du,\\
J(t)&=\log\log t+\gamma+g(t)(\psi_{\mathcal P}(t)-t)-I(t),\\
P(t)&=I(t)+R(t).
\end{aligned}
\tag{RJ5}
$$

Let $B(t)$ be the logarithmic norm of the actual CA vector at price
$g(t)$, with any maximizing convention at ties. Away from its locally
finite events,

$$
P'(t)=(t-B(t))w(t),\qquad
R'(t)=(\psi_{\mathcal P}(t)-B(t))w(t).
$$

These pressures are continuous and locally absolutely continuous.
Since $R(\infty)=0$, (RJ4) gives the complete reserve, including its
future part,

$$
R(t)=\int_t^\infty(B(u)-\psi_{\mathcal P}(u))w(u)\,du.
\tag{RJ6}
$$

## The full real-clock inventory has the same normal form

The actual layer threshold $x_k(t)>1$ solves

$$
\frac{\log(1+1/(x+x^2+\cdots+x^k))}{\log x}=g(t).
$$

Expansion gives $x_1(t)=t+O(1)$ and $x_2(t)\sim\sqrt{2t}$.
For a selected $k$th layer, $g(t)\log p\le d_{p,k}\le p^{-k}$.
With $p_0>1$ the least prime norm, this implies
$p^k\le H(t):=t\log t/\log p_0$ and $k=O(\log t)$.
Consequently all layers $k\ge3$ together are
$O(t^{1/3}(\log t)^{4/3})=o(\sqrt t)$.

The local property $\theta=f_0+O(\log x)$ with $f_0'=1+o(1)$
controls bounded-length increments and individual jumps by $O(\log t)$.
It therefore controls the $O(1)$ first-layer threshold shift and its
ties. The second layer contributes $\sqrt{2t}+o(\sqrt t)$.
The inclusive prime-power identity similarly gives
$\psi_{\mathcal P}(t)=\theta_{\mathcal P}(t)+\sqrt t+o(\sqrt t)$.
Thus, on the entire real half-line and for every tie convention,

$$
B(t)=\psi_{\mathcal P}(t)+(\sqrt2-1)\sqrt t+o(\sqrt t).
\tag{RJ7}
$$

## Select one actual vector satisfying all joint source conditions

Integrating (RJ1) against the original kernel, without a finite cutoff,
gives

$$
I(t)=-2\Re\frac{t^{\rho-1}}{\rho(1-\rho)\log t}
+O_\rho\left(\frac{t^{\beta-1}}{\log^2t}
+\frac1{\sqrt t\log t}\right).
\tag{RJ8}
$$

For example, substitute $v=\log u$ in
$\int_t^\infty u^\rho w(u)\,du$ and integrate once by parts;
the remainder is bounded by
$\int_{\log t}^\infty e^{-(1-\beta)v}v^{-2}\,dv$.
Together with (RJ4)–(RJ5), this yields, with fixed $K>0$ and $\phi$,

$$
P(t)=-K\frac{t^{\beta-1}}{\log t}\cos(\tau\log t+\phi)
+o(t^{\beta-1}/\log t),\quad
K=\frac2{|\rho(1-\rho)|},\quad
\phi=\arg\frac1{\rho(1-\rho)}.
$$

Choose $x_j=\exp(((2j+1)\pi-\phi)/\tau)$,
$d=e^{\pi/(3\tau)}$ and $y_j=e^{\pi/\tau}x_j$.
Eventually $P>0$ on $[x_j,dx_j]$, whereas
$P(y_j)\le-(K/2)y_j^{\beta-1}/\log y_j<0$.
Since $P$ is continuous and tends to zero, it attains a negative minimum
on $[x_j,\infty)$ at some $A_j>dx_j$.
At an inventory event, $B$ jumps upward and $P'$ jumps strictly downward,
which rules out a local minimum there. Hence $A_j$ is event-free and
$B(A_j)=A_j$. Its actual unique CA vector $\mathfrak N_j$ satisfies

$$
\log|\mathfrak N_j|=A_j\to\infty,\qquad
P(A_j)=\gamma-\log G_{\mathcal P}(\mathfrak N_j)=-h_j.
\tag{RJ9}
$$

For every actual vector $\mathfrak m$ with $s=\log|\mathfrak m|>1$,
the same pressure majorant gives
$\log G_{\mathcal P}(\mathfrak m)\le\gamma-P(s)$.
The selected minimum consequently implies

$$
G_{\mathcal P}(\mathfrak m)\le G_{\mathcal P}(\mathfrak N_j)
\quad\text{whenever }\log|\mathfrak m|\ge x_j.
\tag{RJ10}
$$

This covers all future generalized integers, not only multiples.
Every occupied prime has $p<A_j$, since
$\log(1+p^{-1})/\log p<1/(p\log p)\le g(A_j)$ for $p\ge A_j$.
Thus $\log|\mathfrak N_j/p|\ge A_j-\log A_j>x_j$ eventually,
so (RJ10) also supplies every prime-deletion comparison. Moreover,
$\Omega(\mathfrak N_j)\ge A_j/\log A_j\to\infty$: these are proper
GA1 vectors in exactly the stated deletion sense.

If a prime generator $q\le A_j$ were absent, inserting it in the
future comparison would force

$$
1+q^{-1}\le\frac{\log(A_j+\log q)}{\log A_j}
<1+\frac{\log q}{A_j\log A_j}\le1+q^{-1},
$$

a contradiction. The support is therefore the entire prime prefix to
$A_j$. At the same source, all future real clocks satisfy

$$
\int_{A_j}^t(B(u)-u)w(u)\,du=P(A_j)-P(t)\le0\quad(t\ge A_j),
\qquad A_j-\theta_{\mathcal P}(A_j)\sim\sqrt{2A_j}.
\tag{RJ11}
$$

## The original root-scale signed floor fails on those same sources

Write $a(t)=t^{\beta-1}/\log t$, eventually decreasing.
The ratio $a(y_j)/a(dx_j)$ has a fixed positive lower bound, and
$a(A_j)\le a(dx_j)$. The selected minimum therefore gives a fixed
$c>0$ with $P(A_j)\le-c a(A_j)$. Nonnegativity of the complete
reserve in (RJ4), with no independent reoptimization, yields

$$
\sqrt{A_j}\log A_j\,I(A_j)
\le-c A_j^{\beta-1/2}\longrightarrow-\infty.
\tag{RJ12}
$$

Also $h_j\ge cA_j^{-(1-\beta)}/\log A_j$, which dominates
$c_\eta A_j^{-\eta}$ for every fixed $1-\beta<\eta<1/2$ after
adjusting a fixed positive constant. All prime powers, actual CA
exponents, the full improper tail and the complete reserve remain in
this same fixed system.

This tests the [joint regular GA1 source obligation](../Arith/caveney2012sacaga.md#retain-the-original-oscillation-exponent-on-the-regular-ga1-source)
in a broader arithmetic category. Euler products, prime deletion and
insertion, own-price CA selection, future-record comparisons and
(RJ7) can coexist there with failure of the proposed root-scale floor.
It is stronger source matching than an arbitrary pulse function or a
first-prime-mass model, while reusing the classical realization machinery.

The conclusion does not establish insufficiency for ordinary integers:
the finite-prefix matching and (RJ2) do not identify this system with
ordinary arithmetic. Neither the exact global count $\lfloor x\rfloor$
nor the ordinary zeta functional equation is supplied by the construction.
A proof for the original source must use an ordinary-integer or
ordinary-zeta constraint
that does not transport to this system. No such additional estimate,
ordinary Robin counterexample, RH proof, new zero construction or
Lean-certified theorem is supplied here.
