# Unbounded fractional inflection multiplicity with rational polynomial forcing

## 1. Riemann–Liouville equation and solution class

**Definition 1.1 (operators and weak solution).** For $\sigma>0$, let

$$
I_{0+}^{\sigma}v(x)=\frac1{\Gamma(\sigma)}
 \int_0^x(x-t)^{\sigma-1}v(t)\,dt,
\qquad
I_{1-}^{\sigma}v(x)=\frac1{\Gamma(\sigma)}
 \int_x^1(t-x)^{\sigma-1}v(t)\,dt.
$$

For $1<\alpha<2$, the left-sided Riemann–Liouville derivative is
$D_{0+}^{\alpha}=D^2I_{0+}^{2-\alpha}$. For $0<s<1$, the half-order
operators in the weak formulation are
$D_{0+}^{s}=DI_{0+}^{1-s}$ and $D_{1-}^{s}=-DI_{1-}^{1-s}$.
Write $H_0^s(0,1)$ for the closure of $C_c^\infty(0,1)$ in the norm
$\|\widetilde v\|_{W^{s,2}(\mathbb R)}$, where $\widetilde v$ is the zero
extension. The weak solution of

$$
D_{0+}^{\alpha}F=f\quad\hbox{in }(0,1),\qquad F(0)=F(1)=0
$$

means $F\in H_0^{\alpha/2}(0,1)$ with

$$
\int_0^1 D_{0+}^{\alpha/2}F(x)\,
               D_{1-}^{\alpha/2}\psi(x)\,dx
 =\int_0^1 f(x)\psi(x)\,dx
\quad\text{for every }\psi\in H_0^{\alpha/2}(0,1).
\tag{1.1}
$$

These are the operators and solution class of [LMS, Definition 1.1 and
§3, equation (6)]. Its equation (7), in both directions, supplies the
following representation for $f\in L^1(0,1)$ and $1<\alpha<2$:

$$
F_{\alpha,f}(x)=I_{0+}^{\alpha}f(x)
                  -I_{0+}^{\alpha}f(1)x^{\alpha-1},
\qquad F_{\alpha,f}(0)=0.
\tag{1.2}
$$

In particular, the converse in that source says that (1.2) belongs to
$H_0^{\alpha/2}(0,1)$ and is the unique weak solution of (1.1).
This converse, with its stated $L^1$ hypothesis, is the weak-solution
supplier used below.

**Definition 1.2 (admissible forcing and downward transition).** At an order
$1<\alpha<2$, the forcing assumptions are exactly

$$
f\in C([0,1])\cap C^1((0,1]),\quad f(1)=0,\quad
f\geq0,\quad f\not\equiv0,\quad
\lim_{x\downarrow0}x^{(3-\alpha)/(2-\alpha)}f'(x)=0.
\tag{1.3}
$$

These are [LMS, Theorem 5.2]. A downward strict transition of $F''$ in an
open interval $(l,r)$ is a point $\xi\in(l,r)$ for which some $\delta>0$
satisfies

$$
[\xi-\delta,\xi+\delta]\subset(l,r),\qquad F''(\xi)=0,
$$

$$
F''(x)>0\quad(\xi-\delta<x<\xi),\qquad
F''(x)<0\quad(\xi<x<\xi+\delta).
\tag{1.4}
$$

The fixed-order refutation [R] uses $\alpha=3/2$ and
$f(x)=(1-x)(1+5x^{12})$. The separated-pulse idea is inherited from
[R, Triage, “Unbounded inflection numbers”]. The assertion in §2 adds a
common rational polynomial and common rational transition intervals for
an arbitrary finite multiplicity and a whole compact band of orders.
The classical approximation statements in [VV, §2] and [HNP, Lemmas 17
and 19–22], and the weighted approximation results in [LW], supply
approximation inputs; the interaction and admissibility conclusions in
§2 concern the fractional equation (1.1).

## 2. Common compact-band construction and an analytic degree bound

**Theorem 2.1 (arbitrarily many downward transitions on a common band).**
For every integer $N\geq1$ and every pair of real numbers $1<a\leq b<2$,
there are $p\in\mathbb Q[x]$ and rational numbers

$$
0<l_1<r_1<\cdots<l_N<r_N<1
\tag{2.1}
$$

such that $p(0)=p(1)=0$ and $p(x)>0$ for $0<x<1$. The polynomial and
intervals are chosen before $\alpha$. For every $\alpha\in[a,b]$, the
function

$$
F_\alpha(x)=I_{0+}^{\alpha}p(x)-I_{0+}^{\alpha}p(1)x^{\alpha-1},
\qquad F_\alpha(0)=0,
\tag{2.2}
$$

is the unique weak solution (1.1). The forcing $p$ satisfies all
assumptions (1.3), and $F_\alpha$ has a downward strict transition in
each $(l_j,r_j)$. The transition
points and their signed neighborhoods may depend on $\alpha$.

An explicit sufficient degree bound is the following. Put

$$
\begin{aligned}
A&=a-1,&B&=b-1,&\eta&=\frac{1-B}{120},\\
C&=\frac1A+16(N+1)+16N^3,&H&=\frac1A+16,\\
K&=1+\left\lceil
 \max\left\{\log_2(8N),\frac{\log_2(4C/\eta)}{1-B}\right\}
 \right\rceil,&\varepsilon&=2^{-K},\\
L&=2+2\varepsilon^{-2},&
D(N,a,b)&=2+\left\lceil\left(\frac{2LH}{C}\right)^2\right\rceil.
\end{aligned}
\tag{2.3}
$$

There is a witness with $\deg p\leq D(N,a,b)$. All denominators in
(2.3) are positive; this includes the singleton case $a=b$.

**Proof.** Fix $N,a,b$ as stated. Thus $0<A\leq B<1$, so $\eta,C,H$ are
positive and finite. In particular $4C/\eta>1$, $K$ is a positive
integer, and $\varepsilon$ is positive and rational. The extra $1$ in
$K$ gives the strict inequalities

$$
\varepsilon<\frac1{8N},\qquad
\eta\varepsilon^{B-1}>4C.
\tag{2.4}
$$

For the second inequality, $K>\log_2(4C/\eta)/(1-B)$ implies
$2^{K(1-B)}>4C/\eta$. No subdivision of the order band is involved.

We first record the curvature expression that will control all its
orders. If $v\in C^1([0,1])$ and $v(0)=0$, put, for $A\leq\beta\leq B$,

$$
\begin{aligned}
J_\beta(v)&=\int_0^1(1-t)^\beta v(t)\,dt,\\
T_\beta v(x)&=\int_0^x(x-t)^{\beta-1}v'(t)\,dt
                  +(1-\beta)x^{\beta-2}J_\beta(v).
\end{aligned}
\tag{2.5}
$$

The classical beta integral and fractional-integral semigroup give
$v=I_{0+}^1v'$ and $I_{0+}^{\beta+1}v=I_{0+}^{\beta+2}v'$.
Twice differentiating the latter integral gives $I_{0+}^{\beta}v'$:
its twice differentiated kernel has exponent $\beta-1>-1$, and $v'$ is
continuous. Also
$I_{0+}^{\beta+1}v(1)=J_\beta(v)/\Gamma(\beta+1)$.
Consequently, using $\Gamma(\beta+1)=\beta\Gamma(\beta)$,

$$
\Gamma(\beta)F_{\beta+1,v}''(x)=T_\beta v(x),\qquad x>0.
\tag{2.6}
$$

The semigroup here follows by Fubini and the beta integral, with
absolutely integrable kernels of positive order; these are classical
fractional-calculus identities [LMS, Definition 1.1; KST, fractional
integrals]. Equation (2.6) also shows that this curvature is continuous
on $(0,1)$, since $I_{0+}^{\beta}v'$ is continuous there. We use it only
for $C^1$ functions vanishing at zero.

Use the rational piecewise-polynomial pulse

$$
h(s)=
\begin{cases}
s^2(1-s)^2,&0\leq s\leq1,\\
0,&s\notin[0,1].
\end{cases}
\tag{2.7}
$$

It is nonnegative and $C^1$ on $\mathbb R$, because both $h$ and its
first derivative vanish at $0$ and $1$. On $[0,1]$,

$$
h'(s)=2s(1-s)(1-2s),\quad
h''(s)=2-12s+12s^2,\quad |h''(s)|\leq2,
\quad \int_0^1h(s)\,ds=\frac1{30}.
\tag{2.8}
$$

The bound on $h''$ holds because its range there is $[-1,2]$.
Its continuous first derivative is therefore globally Lipschitz with
constant $2$, including across the two junctions.

Set

$$
c_j=\frac14+\frac{j-1}{2N},\quad
u_j(t)=h\left(\frac{t-c_j}{\varepsilon}\right),\quad
f(t)=t(1-t)+\sum_{j=1}^N\nu_j(t),
\tag{2.9}
$$

and choose, already at this point,

$$
l_j=c_j+\frac\varepsilon4,\qquad r_j=c_j+2\varepsilon.
\tag{2.10}
$$

The supports $[c_j,c_j+\varepsilon]$ are disjoint and contained in
$(0,1)$. The sample points (2.10) are rational and satisfy (2.1).
Indeed, $r_j<l_{j+1}$ follows from
$7\varepsilon/4<1/(2N)$, and
$r_N<3/4-1/(4N)<1$. All sample points lie in $[1/4,3/4]$.
The function $f$ is $C^1$, zero at both endpoints, and strictly positive
in the interior. It takes rational values at rational arguments.

For clarity, separate the local integral in (2.5) from its boundary
term, and denote it by $U_\beta v(x)$. The current pulse has a uniform
positive local contribution at $l_j$:

$$
\begin{aligned}
U_\beta\nu_j(l_j)
 &=\varepsilon^{\beta-1}
   \int_0^{1/4}(1/4-s)^{\beta-1}h'(s)\,ds\\
 &\geq\varepsilon^{\beta-1}h(1/4)
 =\frac9{256}\varepsilon^{\beta-1}
 \geq\eta\varepsilon^{\beta-1}.
\end{aligned}
\tag{2.11}
$$

Here $h'\geq0$ on $[0,1/4]$, the kernel is at least $1$ on its open
integration interval, and $\eta\leq1/120<9/256$.
At $r_j$, the whole pulse lies strictly to the left. Integration by
parts, with zero endpoint values of $h$, gives

$$
\begin{aligned}
U_\beta\nu_j(r_j)
 &=\varepsilon^{\beta-1}
   \int_0^1(2-s)^{\beta-1}h'(s)\,ds\\
 &=-(1-\beta)\varepsilon^{\beta-1}
   \int_0^1(2-s)^{\beta-2}h(s)\,ds\\
 &\leq-\frac{1-\beta}{120}\varepsilon^{\beta-1}
 \leq-\eta\varepsilon^{\beta-1}.
\end{aligned}
\tag{2.12}
$$

For the first inequality, $1\leq2-s\leq2$ and $-2<\beta-2<-1$
imply $(2-s)^{\beta-2}\geq1/4$; use (2.8).
Thus both signs retain a lower bound uniform over $[A,B]$.

We next bound all the other terms for this same $f$, not separately
optimized forcings. A later pulse has no local contribution at either
$l_j$ or $r_j$. Every earlier support has distance at least
$d=1/(4N)$ from either sample point. In fact its distance from $l_j$
is at least $1/(2N)-3\varepsilon/4>d$, and its distance from $r_j$
is still larger. If $i<j$ and $x$ is either sample point, integration
by parts in the original variable gives

$$
U_\beta\nu_i(x)=-(1-\beta)
 \int_{c_i}^{c_i+\varepsilon}(x-t)^{\beta-2}\nu_i(t)\,dt.
$$

Here $d\leq x-t\leq1$, so
$(x-t)^{\beta-2}\leq(x-t)^{-2}\leq d^{-2}$. Hence

$$
\sum_{i<j}|U_\beta\nu_i(x)|
 \leq\frac{N\varepsilon}{30d^2}
 =\frac{16N^3\varepsilon}{30}\leq16N^3.
\tag{2.13}
$$

For $g(t)=t(1-t)$, $|g'|\leq1$, so
$|U_\beta g(x)|\leq x^\beta/\beta\leq1/A$.
Finally $f\geq0$, $(1-t)^\beta\leq1$, $1-\beta\leq1$, and
$x^{\beta-2}\leq16$ at these sample points. Therefore the single
boundary correction, which includes every pulse, satisfies

$$
0\leq(1-\beta)x^{\beta-2}J_\beta(f)
 \leq16\left(\frac16+\frac{N\varepsilon}{30}\right)
 \leq16(N+1).
\tag{2.14}
$$

Together (2.13)–(2.14) bound the absolute value of the remainder after
removing the current local pulse by $C$ at each sample point. Since
$0<\varepsilon<1$ and $\beta\leq B$, (2.4), (2.11) and (2.12) yield

$$
T_\beta f(l_j)>3C,\qquad T_\beta f(r_j)<-3C
\quad(A\leq\beta\leq B,\ 1\leq j\leq N).
\tag{2.15}
$$

It remains to preserve these inequalities with one admissible rational
polynomial. Only the classical Bernstein derivative approximation is
needed here [VV, §2, equations (1)–(3) and Theorem 2]. Its quantitative
estimate for this $f$ is included to specify every choice in (2.3).
Because the pulse supports are disjoint, $f'$ is Lipschitz with constant

$$
L=2+2\varepsilon^{-2}.
\tag{2.16}
$$

Indeed $f''$ exists off the finitely many support endpoints and has
absolute value at most $L$. Integrating this bound on each piece and
using continuity of $f'$ across the endpoints proves the global
Lipschitz inequality. There is no factor $N$ in (2.16).

For any integer $n\geq2$, take the ordinary Bernstein polynomial

$$
B_nf(x)=\sum_{k=0}^nf(k/n)\binom nkx^k(1-x)^{n-k}.
\tag{2.17}
$$

The classical derivative identity, equivalently the first-difference
formula of [VV, equation (1)], is

$$
(B_nf)'(x)=\sum_{k=0}^{n-1}\binom{n-1}k x^k(1-x)^{n-1-k}
                  \int_0^1f'((k+s)/n)\,ds.
\tag{2.18}
$$

The weights in this sum have total mass $1$, mean $k/(n-1)=x$, and
variance $x(1-x)/(n-1)$ when interpreted as weights on $k/(n-1)$.
For each $k,s$,

$$
\left|\frac{k+s}{n}-x\right|
 \leq\left|\frac{k}{n-1}-x\right|+\frac1n.
$$

Applying the Lipschitz inequality and Cauchy–Schwarz to the finite
weighted sum in (2.18) consequently gives

$$
\begin{aligned}
\|(B_nf)'-f'\|_\infty
 &\leq L\left(\frac1{2\sqrt{n-1}}+\frac1n\right)\\
 &\leq\frac{2L}{\sqrt{n-1}}.
\end{aligned}
\tag{2.19}
$$

The variance identity follows from the binomial first and second
moments; thus (2.19) uses no unknown approximation constant.
Since $B_nf(0)=f(0)=0$, the fundamental theorem of calculus also bounds
$\|B_nf-f\|_\infty$ by the same derivative error.
These are classical approximation inputs, rather than separate
assertions of fractional inflection multiplicity. The endpoint and
weighted derivative estimates of [HNP] and [LW] are compatible stronger
approximation suppliers; no additional such estimate is required for
(2.19).

For any $e\in C^1([0,1])$ with $e(0)=0$ and
$\|e'\|_\infty\leq E$, one has $\|e\|_\infty\leq E$. At any
$x\in[1/4,1]$, (2.5) therefore gives the uniform estimate

$$
|T_\beta e(x)|
 \leq\frac EA+16E=HE\qquad(A\leq\beta\leq B).
\tag{2.20}
$$

In the integral term use $x^\beta/\beta\leq1/A$; in the boundary
term use $|J_\beta(e)|\leq E$ and $x^{\beta-2}\leq16$.
Now take $n=D(N,a,b)$ from (2.3), and set $p=B_nf$.
Since $n-1>(2LH/C)^2$, (2.19) and (2.20) imply

$$
|T_\beta(p-f)(x)|<C\quad(x\in[1/4,1],\ A\leq\beta\leq B).
$$

Thus (2.15) becomes

$$
T_\beta p(l_j)>2C>0,\qquad T_\beta p(r_j)<-2C<0
\quad(A\leq\beta\leq B).
\tag{2.21}
$$

All coefficients in (2.17) are rational because $f(k/n)$ is rational,
and $\deg p\leq n$. Its endpoint values are zero. Every interior
Bernstein weight is positive on $(0,1)$, and every interior sample
$f(k/n)$ is positive; since $n\geq2$, there is at least one such
sample. It follows directly that $p(x)>0$ for $0<x<1$.
This ensures positivity by construction, without inferring it from a
uniform approximation near the vanishing endpoints.

We next strengthen opposite endpoint signs to the strict signed
neighborhoods required in (1.4). Fix any $\beta\in[A,B]$ and write
$p(x)=\sum_{k=0}^nd_kx^k$. The classical monomial beta integral gives

$$
I_{0+}^{\alpha}x^k=\frac{k!}{\Gamma(k+\alpha+1)}x^{k+\alpha}.
$$

After two ordinary derivatives, (2.6) becomes the polynomial identity

$$
\begin{aligned}
x^{2-\beta}T_\beta p(x)&=R_\beta(x),\\
R_\beta(x)&=(1-\beta)J_\beta(p)
 +\sum_{k=0}^nd_k\frac{\Gamma(\beta)k!}{\Gamma(k+\beta)}x^{k+1}.
\end{aligned}
\tag{2.22}
$$

This polynomial has real coefficients and degree at most $n+1$;
its constant term is strictly positive because $1-\beta>0$ and
$J_\beta(p)>0$. Thus it is not the zero polynomial. For $x>0$ the
multiplier $x^{2-\beta}\Gamma(\beta)$ relating $F_{\beta+1,p}''$ to
$R_\beta$ is strictly positive.

A nonzero real polynomial has finitely many roots, and a constant
strict sign on each interval complementary to its real roots. In
$(l_j,r_j)$ order its roots increasingly. There is at least one root
by (2.21) and continuity. The complementary sign interval adjacent to
$l_j$ has sign $+$, whereas the one adjacent to $r_j$ has sign $-$.
In this finite list choose the first complementary interval with
negative sign. Its left endpoint $\xi_{\beta+1,j}$ is a root and the
preceding complementary interval has positive sign. Choose
$\delta_{\beta+1,j}>0$ smaller than the distances from that root to
$l_j,r_j$ and to every other root in $[l_j,r_j]$; when there is no
other root, only the first two distances are needed. All these
distances are positive. This gives (1.4) for $R_\beta$, and hence
for $F_{\beta+1,p}''$. Roots of even multiplicity elsewhere do not
obstruct this selection. The intervals are disjoint, so the selected
roots are distinct. No root selection across different orders is used.

Finally, $p$ is a polynomial with $p(1)=0$, nonnegative on $[0,1]$,
and nontrivial. It belongs to both regularity spaces in (1.3), and
$p'$ is bounded. For each $\alpha\in[a,b]$ the exponent
$(3-\alpha)/(2-\alpha)$ is positive, proving the weighted derivative
limit in (1.3). Also $p\in L^1(0,1)$ and $1<\alpha<2$. These are
precisely the input conditions for the converse direction of [LMS,
§3, equation (7)] quoted in Definition 1.1. Applying that converse to
this $p$ proves that (2.2) belongs to the source's
$H_0^{\alpha/2}(0,1)$ and satisfies (1.1) for every test function
there, with uniqueness. This application supplies the weak-solution
bridge, including the space membership, rather than deducing it from
a pointwise differential identity.

The pointwise identity is consistent with the same equation: the
classical semigroup and monomial formula give

$$
I_{0+}^{2-\alpha}F_\alpha(x)
 =I_{0+}^2p(x)-I_{0+}^{\alpha}p(1)\Gamma(\alpha)x,
$$

whose second derivative is $p$. The continuous value at zero is $0$,
since $I_{0+}^{\alpha}p(x)=O(x^\alpha)$ and
$x^{\alpha-1}\to0$; the value at $1$ is zero by (2.2).
All choices (2.3), (2.9), (2.10), and (2.17) depend only on $N,a,b$.
In particular, the construction treats $a=b$ without any limiting
argument or change of quantifiers. This proves the theorem. $\square$

## 3. Consequence and extent of the multiplicity statement

**Corollary 3.1 (absence of a forcing-independent finite bound).**
For each fixed $1<\alpha<2$, the number of downward strict transitions
of the weak solution (1.1), as $p$ ranges over rational polynomials
with $p(0)=p(1)=0$ and $p>0$ on $(0,1)$, has no finite upper bound.
More strongly, for every nonempty compact band $[a,b]\subset(1,2)$
and every integer $N\geq1$, one such polynomial has at least $N$
downward strict transitions at every order in the band, in $N$
common rational intervals.

**Proof.** The stronger assertion is Theorem 2.1. A finite
forcing-independent bound for a band is contradicted by taking $N$
larger than that bound. The fixed-order assertion follows by taking
$a=b=\alpha$. The forcings satisfy (1.3), so the same failure of a
finite upper bound holds in the larger forcing class of [LMS,
Theorem 5.2].

The assertions concern at least $N$ downward strict transitions.
They specify neither the exact total number of zeros nor simplicity,
continuous dependence of selected roots on the order, or a minimal
degree. The polynomial may depend on both $N$ and the band. For a
fixed polynomial positive on $(0,1)$, the monomial formula used in
(2.22) shows directly that

$$
F_{\alpha,p}''\longrightarrow p\quad\text{uniformly on every compact
subinterval of }(0,1)\quad\text{as }\alpha\uparrow2.
$$

Indeed each of the finitely many monomial coefficients and powers
converges uniformly there, while the boundary-curvature term tends
to zero. The positive minimum of $p$ on such a subinterval then makes
$F_{\alpha,p}''$ positive there for all sufficiently large $\alpha<2$.
Thus a fixed polynomial and fixed interior intervals cannot give the
same downward-transition conclusion for orders arbitrarily close
to $2$. The strict upper-band condition in Theorem 2.1 is consistent
with this direct limit.

The forcing equation here is $D_{0+}^{\alpha}F=p$ with independently
chosen nonnegative forcing. No identification of $p$ with an
eigenfunction is imposed. Consequently this argument gives no
inflection or Mittag–Leffler zero count for the constrained spectral
equations in [LMS, §6] or [EL]. $\square$

## 4. Mathematical citations

**[LMS]** Yulong Li, Rachel Morgan and Michael Siegrist,
*Concavity structure of fractional differential equations and zeros of
Mittag–Leffler functions*, [DOI 10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9).
Definition 1.1 specifies the operators; §3, equations (6)–(7), specifies
the weak formulation and its bidirectional integral representation;
Theorem 5.2 supplies (1.3); Conjecture 6.1 is the uniqueness assertion
addressed by the fixed-order example [R].

**[R]** [Li–Morgan–Siegrist inflection-point refutation](../../../Problems/li-morgan-siegrist-2026-inflection-points-conjecture-6-1.md),
with the fixed-order polynomial example and the separated-pulse idea
in its Triage section. The associated declaration is
[LiMorganSiegristInflectionRefutation.result](../../../D5/S0/Certificates/LiMorganSiegristInflectionRefutation.lean).
The mathematical addition of Theorem 2.1 relative to this source is the
simultaneous compact-band interaction bound, rational positive
polynomial approximation with a specified degree, and strict
transition conclusion in the original weak solution class.

**[VV]** Alexander Veretennikov and Evguenia Veretennikova,
*On convergence of partial derivatives of multivariate Bernstein
polynomials*, [arXiv:1507.05235v2](https://arxiv.org/abs/1507.05235v2),
§2, Theorem 2 and equations (1)–(3). The first-difference derivative
identity and derivative approximation are classical inputs to the
proof, not additional multiplicity results.

**[HNP]** Olga Holtz, Fedor Nazarov and Yuval Peres,
*New coins from old, smoothly*,
[arXiv:0808.1936v3](https://arxiv.org/abs/0808.1936v3), Lemmas 17 and
19–22; [DOI 10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5).
These supply Bernstein derivative and Lorentz approximation estimates.

**[LW]** [LorentzWeightedHolderControl](../../../D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.lean),
including its weighted derivative kernels, Lorentz jet estimates,
Taylor-remainder bounds, derivative control, Hölder seminorm control,
and weighted stability. These approximation conclusions, including
the proof-local estimates, are credited intermediate theory. The proof
of Theorem 2.1 uses the ordinary positive Bernstein operator and the
explicit first-difference bound (2.19).

**[KST]** Anatoly A. Kilbas, Hari M. Srivastava and Juan J. Trujillo,
*Theory and Applications of Fractional Differential Equations*,
North-Holland Mathematics Studies 204, fractional integrals and the
beta-integral semigroup. The monomial and semigroup identities used
inside Theorem 2.1 are classical fractional calculus.

**[EL]** Paul W. Eloe and Yulong Li,
*Existence, comparison, and monotonicity of principal eigenvalues of
fractional Sturm-Liouville problems involving Riemann-Liouville
derivatives*, [DOI 10.1007/s13540-026-00481-1](https://doi.org/10.1007/s13540-026-00481-1).
Its principal-eigenvalue equations constrain forcing through the
unknown eigenfunction, unlike the free-forcing construction of §2.

## 追加锚（本行以下为增补区）
