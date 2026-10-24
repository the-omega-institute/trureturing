---
bibkey: alladi1982roughmobius
authors: Krishnaswami Alladi
year: 1982
title: Asymptotic estimates of sums involving the Moebius function
doi: 10.1016/0022-314X(82)90060-9
url: https://doi.org/10.1016/0022-314X(82)90060-9
claim: Alladi’s original Theorem 1 gives a uniform signed rough-Möbius formula with its boundary compensation; it supplies compact-u prefix estimates but not the complete compensated signed Robin pairing.
strata_touched: []
license: citation-only
triage: anchor
---

# Signed Möbius sums over rough integers

Alladi's paper appeared in *Journal of Number Theory* **14** (1982),
86–98, DOI [10.1016/0022-314X(82)90060-9](https://doi.org/10.1016/0022-314X(82)90060-9).
The [University of Michigan deposit](https://deepblue.lib.umich.edu/items/a69cf193-aafb-43b7-9540-7b55c1460333)
supplies the [original scanned PDF](https://backend.production.deepblue-documents.lib.umich.edu/server/api/core/bitstreams/5a1463e5-878d-479d-ae59-8ffb43b18bcb/content):
13 pages, 469,456 bytes, SHA256
`2e560c69542bbd879f9c608fae023a76b0b5cd6c4305cc45a5bd00fe6d4f88b6`.
Definition (1.4), Theorem 1, printed p.87, the absolute-constant
convention on p.88, and §2, pp.90–91 were directly inspected;
equations were checked against the scan. No complete proof audit,
vendored source text or Lean verification is supplied.

Write $P^-(1)=\infty$, $u=\log X/\log y$, and

$$
M_{\mathrm{rough}}(X,y)
=\sum_{\substack{1\le n\le X\\P^-(n)>y}}\mu(n).
$$

Theorem 1 gives $M_{\mathrm{rough}}(X,y)=1$ for $y\ge X\ge1$ and,
uniformly for $2\le y<X$,

$$
\boxed{M_{\mathrm{rough}}(X,y)
=\frac{X\rho'(u)}{\log y}+\frac y{\log y}
+O\!\left(\frac{Xu^2}{\log^2y}\right),}
$$

where $\rho$ is the Dickman function. The implicit constant is absolute;
no numerical value is supplied. The unit and strict cutoff are retained.
For fixed $\delta>0$, $U>1+\delta$, the term $y/\log y$ is absorbed
by $O_{\delta,U}(X/\log^2y)$ uniformly on $1+\delta\le u\le U$.
Thus the compact-$u$ estimate is an existing original-source input.
The fixed-$u$ synopsis in Alladi–Goswami
[arXiv:2412.03088v1, §1.1](https://arxiv.org/html/2412.03088v1#S1.SS1)
is consistent with it; that synopsis omits the boundary term.

The original's higher expansion (2.17), p.91, has $O_n$ constants
and requires $n\le\lfloor u\rfloor-1$; its accompanying arbitrary-length
statement assumes $u\to\infty$. It supplies no growing-order constant
budget or signed factorial-kernel remainder at Robin's critical scale.

## Correspondence with a growing FIB prime section

For $Q(y)=\prod_{p\le y}p$, the coprime prefix of
[the FIB volume, §426](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
is exactly $M_{Q(y)}(z)=M_{\mathrm{rough}}(z,y)$.
Its fixed filter $P=210$ and the growing filter $Q(y)$ have different
uniformity obligations. The constants in §426.7 and §426.15 have not been
bounded uniformly for growing $Q(y)$.

At a source clock $A$, choosing $y=A^{1/u_0}$ with fixed $u_0>1$ and
$n\sim cA$ with fixed $c>0$ gives $\log n/\log y\to u_0$.
The original uniform theorem covers this compact-parameter sequence.
One filter must still be shared by all rows: choosing $y=n^{1/u_0}$
separately for each row does not invoke §426's same-filter identity.

A usable signed estimate still needs simultaneous control of the actual
rough prefix and its paired kernel at the same growing filter, the complete
original head compensation, the complementary range, and the selected
critical sources. The classical prefix formula alone does not give a sign
for the full Robin integral or prove RH. The distinct subpower range in the
[Alamoudi source](alamoudi2026subradicallysifted.md) is not substituted for
the fixed positive power cutoff here.

## The source-scale boundary $u\to1^+$

For real $y\ge2$ and $y\le X\le y^2$, the existing exact formula is

$$
M_{\mathrm{rough}}(X,y)=1-\pi(X)+\pi(y).
$$

Only the unit and primes in $(y,X]$ occur. If $X/y\to c>1$, PNT gives
$M_{\mathrm{rough}}(X,y)=-(c-1)y/\log y+o(y/\log y)$.
Here $u\to1^+$ and $\rho'(u)=-1/u$, so

$$
\frac{\log y}{y}
\left[M_{\mathrm{rough}}(X,y)-\frac{X\rho'(u)}{\log y}\right]
\longrightarrow1.
$$

The original theorem's $y/\log y$ term is exactly this compensation.
Dropping it cannot preserve an $O(X/\log^2y)$ error in this regime;
this does not contradict Alladi's actual uniform statement.

For an actual proper GA1 CA source retain $A=\log N$ and $y=P(N)$.
The [published GA1 envelope](../Arith/caveney2012sacaga.md), Theorem 13,
gives $y\sim A$ along any such family tending to infinity, and initial
CA prime support gives $\operatorname{rad}(N)=\prod_{p\le y}p$.
Rows $X=cA$, $c>1$ fixed, therefore use this same compensated boundary.
This includes the conditional selected critical maximizer; it asserts
no unbounded critical family, numerical threshold, joint kernel error,
or Robin/RH conclusion.

## Integrated same-filter power windows from the fixed-parameter input

This application uses the existing Alladi prefix input, classical PNT
and second Mertens estimate, and actual-kernel convergence of FIB §§433–434.
The dominated-integral argument needs only fixed-$u$ convergence; the
original uniform theorem supplies more. This is a paper-level application,
with no new rough-sum theorem, Lean verification or originality claim.

Let $z\to\infty$, $L=\log z$, $P_z=\prod_{p\le z}p$, and use exactly

$$
M_z(n)=\sum_{\substack{1\le r\le n\\P^-(r)>z}}\mu(r),\qquad P^-(1)=\infty,
\qquad
\eta_z(y)=\sum_{d\mid P_z}\mu(d)\eta(y/d).
$$

The actual row kernel $J_x^{\eta_z}(n)$ and complete identity
$I_\psi(x)=\sum_{n\ge1}M_z(n)J_x^{\eta_z}(n)$ are those of
[FIB §428](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
Every row shares this one filter, with the unit and strict prime cutoff
retained. Use the existing profile

$$
\Xi_\sigma(a)=e^{-\gamma_E}\int_0^\infty e^{-\sigma v}
\frac{e^{-av}\Phi(v)-1+(a-1)v}{v^2}\,dv,
\qquad \Phi(v)=\exp(\operatorname{Ein}(v)).
\tag{R1}
$$

First fix $\sigma>0$ and $0\le a<b<\infty$ with $\sigma+a>1$.
The actual source is $x=z^\sigma$, and the finite row window is
$z^{\sigma+a}\le n\le z^{\sigma+b}$. Then

$$
\boxed{
\lim_{z\to\infty}
\sum_{z^{\sigma+a}\le n\le z^{\sigma+b}}
M_z(n)J_{z^\sigma}^{\eta_z}(n)
=
\int_{\sigma+a}^{\sigma+b}\rho'(u)\Xi_\sigma(u-\sigma)\,du.
}
\tag{R2}
$$

This integrated conclusion keeps the same actual filter in every row.

### A bounded dominator from classical prime inputs

Fix $1<u_0<u_1<\infty$. The classical PNT and second Mertens estimate,
already used in the FIB source, supply for all sufficiently large $z$

$$
\pi(t)\le 2t/\log t\quad(t\ge z),\qquad
\sum_{z<p\le z^{u_1}}\frac1p\le\log u_1+1=:B.
\tag{R3}
$$

These classical prime estimates are reused. For an actual rough integer
$n\le X\le z^{u_1}$, its prime factors, counted with multiplicity, are
all greater than $z$, so their number is at most $K=\lfloor u_1\rfloor$.
For $k\ge1$ prime factors, count ordered tuples, which can only overcount.
After $k-1$ primes with product $Q$ are selected, a last prime exists only
when $X/Q>z$; (R3) bounds its count by $2X/(Q\log z)$.
Summing the preceding primes over $(z,z^{u_1}]$ therefore bounds the
$k$-factor count by $2XB^{k-1}/\log z$. Including the unit gives, for
$z^{u_0}\le X\le z^{u_1}$,

$$
|M_z(X)|\le
1+\frac{2X}{L}\sum_{j=0}^{K-1}B^j.
\tag{R4}
$$

No sign is inferred from this dominator. The prime-tuple count is used
only to pay domination inside this application, not as a newly claimed
sieve theorem. In particular $L|M_z(X)|/X$ has a bound independent of $z$
and of $u\in[u_0,u_1]$.

### Fixed-parameter convergence pays the integral

Set

$$
F_z(u)=\frac{L\,M_z(z^u)}{z^u},\qquad u\in[u_0,u_1].
$$

For each fixed $u>1$, the existing Alladi input gives
$F_z(u)\to\rho'(u)$. Equation (R4) bounds $|F_z|$ by one constant
on this fixed interval. Dominated convergence therefore gives, for each
continuous $h$ there,

$$
\int_{u_0}^{u_1}F_z(u)h(u)\,du
\longrightarrow\int_{u_0}^{u_1}\rho'(u)h(u)\,du.
\tag{R5}
$$

Dominated convergence suffices here; compact-parameter uniformity is
independently supplied by the original theorem above.

Indeed, on the cell $u\in[\log n/L,\log(n+1)/L)$ the actual prefix
$M_z(z^u)$ is exactly $M_z(n)$. Uniform continuity of $h$ and the exact
identity

$$
L\int_{\log n/L}^{\log(n+1)/L}z^{-u}\,du
=\frac1n-\frac1{n+1}
$$

show that

$$
\int_{u_0}^{u_1}F_z(u)h(u)\,du
-
\sum_{z^{u_0}\le n\le z^{u_1}}\frac{M_z(n)}{n^2}h(\log n/L)
\longrightarrow0.
\tag{R6}
$$

The first and last clipped cells have total error $O(1/(Lz^{u_0}))$
from (R4), before the fixed bound on $h$. Replacing
$1/[n(n+1)]$ by $1/n^2$ costs
$O(L^{-1}\sum_{n\ge z^{u_0}}n^{-2})=o(1)$.
The remaining uniform-continuity error is bounded by its modulus at
$O(1/(Lz^{u_0}))$ times a bounded total absolute row weight.

For (R2), take $u_0=\sigma+a$, $u_1=\sigma+b$, and
$h(u)=\Xi_\sigma(u-\sigma)$. FIB §434 gives

$$
\sup_{z^{u_0}\le n\le z^{u_1}}
|n^2J_{z^\sigma}^{\eta_z}(n)-h(\log n/L)|\longrightarrow0.
$$

By (R4), $\sum_{z^{u_0}\le n\le z^{u_1}}|M_z(n)|/n^2=O(1)$.
Thus replacing the actual kernel by its already supplied profile costs
$o(1)$. Equations (R5)–(R6) establish (R2).

### The actual critical clock can use the same integrated window

More generally let $x=x(z)$ satisfy $\log x/\log z\to1$. For any fixed
$0<a<b<\infty$, the same finite window $z^{1+a}\le n\le z^{1+b}$
has $n\ge x$ eventually and satisfies

$$
\boxed{
\sum_{z^{1+a}\le n\le z^{1+b}}M_z(n)J_x^{\eta_z}(n)
\longrightarrow
\int_{1+a}^{1+b}\rho'(u)\Xi_1(u-1)\,du.
}
\tag{R7}
$$

To justify the moving clock, use
$\sigma_z=\log x/L\to1$. FIB §434 already gives joint actual-kernel
convergence on positive compact $\sigma$ intervals, and its profile is
jointly continuous. Hence
$n^2J_x^{\eta_z}(n)\to\Xi_1(\log n/L-1)$ uniformly on this window.
The preceding dominated integral proof is unchanged. No moving-parameter
pointwise estimate for $M_z$ is assumed.

At an eligible selected Robin source, $z=P^+(N)$ and $x=\log N$ obey
$z<x<p^+$. Bertrand gives
$1<\log x/L<1+(\log2)/L$, paying the required clock limit along any
such family with supports tending to infinity. This conditional application does not assert an
unbounded family of critical maximizers or an effective threshold for
one fixed selected integer.

The Dickman derivative is strictly negative for $u>1$. The existing
kernel has two roots $\alpha_-(1)\in(0,1)$ and
$\alpha_+(1)\in(1,2)$, with signs $+,-,+$. Thus the limit in (R7) is
strictly negative if $[a,b]$ lies inside either positive-kernel interval,
and strictly positive if it lies inside the negative-kernel interval.
These signs belong to the same realized rough prefix and kernel.

The full complement remains

$$
\mathcal C_z(x)=I_\psi(x)
-\sum_{z^{1+a}\le n\le z^{1+b}}M_z(n)J_x^{\eta_z}(n),
$$

including the original unit row, every $n<x$, and the whole upper tail.
The existing unconditional PNT tail estimate gives $I_\psi(x)\to0$,
so this complement tends to the negative of the displayed window limit.
The order-one cancellation is not a lower bound at Robin's
$1/(\sqrt x\log x)$ scale. The joint window application uses existing
prefix and kernel inputs; the full same-source signed comparison
and RH remain unproved.

## A critical-scale bound for the complete upper row tail

The fixed-window limits above leave their complete complementary sum in
place. A different application of existing inputs controls every row
beyond one growing cutoff, at the Robin normalization itself. It uses the
ordinary Mertens bound already consumed in FIB §409, the actual smooth
semigroup identity in §428, the first-Mertens estimate in that section,
and the full factorial density in §429. This tail application does not
reprove Alladi, supply a new sieve theorem or numerical starting
threshold, or claim an experiment or Lean result.

The ordinary input is Lee–Leong,
[arXiv:2208.06141v5, Theorem 1.1, (9)](https://arxiv.org/html/2208.06141v5#S1.Thmtheorem1):

$$
|M(t)|<33.56t\log t\exp\!\left(-\sqrt{\log t/5.56}\right)
\qquad(t\ge e^{4589.20}),\qquad M(t)=\sum_{m\le t}\mu(m).
\tag{T1}
$$

Its versioned statement was directly inspected. The external proof and
computations are not independently rerun. This is the same source bound
as FIB (409.3), reused with its real-parameter domain and threshold.

Keep the actual $P_z,M_z,\eta_z,J_x^{\eta_z}$ above. Put $L=\log z$ and
assume $L\ge25$ and $z\le x\le2z$. Define

$$
R=1024L^2,\qquad H_z=e^R.
$$

Then the entire, absolutely summed upper row tail satisfies

$$
\boxed{
\sqrt x\log x
\sum_{n\ge\lceil H_z\rceil}|M_z(n)J_x^{\eta_z}(n)|<2^{-80}.
}
\tag{T2}
$$

This bound concerns the actual row sum with one filter and one source.
It does not assert a sign for the rows below $H_z$.

### Uniform small-prime semigroup budgets

Write $\mathcal S_z$ for the positive integers generated by primes
$p\le z$, with repetitions allowed. The already established identity is

$$
M_z(y)=\sum_{q\in\mathcal S_z,\ q\le y}M(y/q).
\tag{T3}
$$

The classical first-Mertens estimate used in FIB (CP.7) gives, for $z\ge2$,

$$
F(z)=\sum_{p\le z}\frac{\log p}{p}\le L+\log4+4<L+6.
$$

Also $S_z=\sum_{p\le z}\log p/(p-1)\le L+10$: its difference from $F(z)$
is at most $\sum_{n\ge2}\log n/[n(n-1)]\le4$, using
$\log n\le\sqrt n$, $n-1\ge n/2$ and integral comparison.
The finite Euler product at $1+1/L$, bounded by
$\zeta(1+1/L)\le1+L$, therefore gives

$$
\sum_{q\in\mathcal S_z}\frac1q
=E_z(1)^{-1}
\le e^{S_z/L}(1+L)<8L\qquad(L\ge25).
\tag{T4}
$$

Indeed the logarithm of the product ratio between $1$ and $1+1/L$
is at most $S_z/L$.

For $0\le h\le1/L$, one has $p^h\le e$ and
$p^{1-h}\ge\sqrt p$. Hence

$$
\sum_{p\le z}\frac{\log p}{p^{1-h}-1}
\le4eF(z).
$$

Integrating this logarithmic derivative over the interval of width $1/L$
shows

$$
\sum_{q\in\mathcal S_z}q^{-1+1/L}
=E_z(1-1/L)^{-1}<8e^{14}L.
\tag{T5}
$$

Here $4e(1+6/25)<14$. These are classical Euler-product and Rankin
estimates inside the application, rather than additional distribution
assumptions on the actual Möbius coefficients.

### The actual rough prefix, including its unit

For $n\ge e^{9178.4}$, put $r=\log n$ and split (T3) at $q=\sqrt n$.
For $q\le\sqrt n$, the argument of (T1) is at least $\sqrt n$;
$\log(n/q)\le r$ and $\log(n/q)\ge r/2$ give

$$
|M(n/q)|\le34(n/q)r\,e^{-\sqrt r/4}.
$$

The weaker exponent uses $2\cdot5.56<16$. For $q>\sqrt n$, retain
$|M(n/q)|\le n/q$ and the Rankin bound
$\sum_{q>\sqrt n}q^{-1}\le n^{-1/(2L)}\sum_q q^{-1+1/L}$.
Equations (T4)–(T5) yield

$$
\frac{|M_z(n)|}{n}
\le8L\left(34r e^{-\sqrt r/4}+e^{14}e^{-r/(2L)}\right).
\tag{T6}
$$

The $q=n$ endpoint and $M(1)=1$ remain in the second range whenever
applicable. The strict rough cutoff in $M_z$ is unchanged.

### One bound on the actual kernel over the entire upper range

Use FIB (429.3), namely
$|\ell G_{\eta,x}(\ell+v)|\le v^2/2+v+12$ for
$\ell=\log x\ge1$ and $v\ge0$. The complete finite divisor expression is

$$
J_x^{\eta_z}(n)=\sum_{d\mid P_z}\mu(d)
\int_{dn}^{d(n+1)}\frac{G_{\eta,x}(\log s)}{s^2}\,ds.
\tag{T7}
$$

For $n\ge x$, $r=\log n\ge\ell$, the maximal $v$ in a divisor fiber
is at most $r+\log d$, since $\ell\ge\log2$.
The exact fiber mass is $n/[d(n+1)]\le1/d$ after multiplication by $n^2$.

For $D_j=\sum_{d\mid P_z}(\log d)^j/d$, finite product differentiation
and (T4) give

$$
D_0\le8L,\qquad D_1\le10L^2,\qquad D_2\le24L^3.
\tag{T8}
$$

To see the moment bounds, the normalized divisor law has mean
$\sum_{p\le z}\log p/(p+1)\le L+6$ and variance
$\sum_{p\le z}p(\log p)^2/(p+1)^2\le LF(z)$.
Thus its second moment is at most $(L+6)^2+L(L+6)<3L^2$.
No divisor is removed from (T7). Taking absolute values gives

$$
\begin{aligned}
n^2|J_x^{\eta_z}(n)|
&\le\ell^{-1}\left[D_0(r^2/2+r+12)+D_1(r+1)+D_2/2\right]\\
&\le32r^2\qquad(n\ge x,\ L\ge25).
\end{aligned}
\tag{T9}
$$

This is an upper-tail bound, not an extension of the compact-parameter
kernel approximation or a claim of a kernel sign.

### Sum every remaining row and pay the normalization

For $r\ge R=1024L^2$, both functions
$r^3e^{-\sqrt r/4}$ and $r^2e^{-r/(2L)}$ are decreasing.
For either function $g$, decreasing integral comparison gives
$\sum_{n\ge\lceil e^R\rceil}g(\log n)/n\le
 g(R)e^{-R}+\int_R^\infty g(r)dr$.
Each integral below is at least its corresponding $g(R)$, so this
sum is at most twice the integral. Elementary Gamma-tail integration,
with $v_0=\sqrt R=32L$, gives

$$
\begin{aligned}
\int_R^\infty r^3e^{-\sqrt r/4}dr
&=8e^{-v_0/4}\sum_{j=0}^7\frac{7!}{(7-j)!}4^jv_0^{7-j}
 \le16v_0^7e^{-v_0/4}=2^{39}L^7e^{-8L},\\
\int_R^\infty r^2e^{-r/(2L)}dr
&=2L(R^2+4LR+8L^2)e^{-R/(2L)}
 \le2^{22}L^5e^{-512L}.
\end{aligned}
\tag{T10}
$$

In the first line, the polynomial is bounded by
$v_0^7\sum_{j\ge0}(28/v_0)^j\le2v_0^7$.
Since $\sqrt x\log x\le4Le^{L/2}$, (T6), (T9) and (T10) bound
the left side of (T2) by

$$
2^{56}\left(L^9e^{-15L/2}+L^7e^{-1023L/2}\right).
\tag{T11}
$$

Both terms decrease for $L\ge25$. At $L=25$, use
$25^9<2^{45}$, $25^7<2^{35}$, $e>2$ and $e^{14}<2^{23}$;
the first contribution is below $2^{-86}$ and the second below
$2^{-12696}$. Their sum is below $2^{-80}$, proving (T2).
These are elementary outward comparisons, not numerical experiments.

### What this pays at the selected Robin source

At the eligible source in the
[Polak note](polak2026finiterobinca.md#application-at-the-same-critical-source-and-clock),
put $x=A=\log N$ and $z=P^+(N)$. Its existing conditions give
$z<A<p^+<2z$. The Axler stop used there gives $\log A>26$;
hence $L=\log z>26-\log2>25$. Thus all thresholds above are paid
at this very source, without assuming an unbounded family of such integers.

The complete identity now reads

$$
I_\psi(A)=\sum_{1\le n<\lceil H_z\rceil}
M_z(n)J_A^{\eta_z}(n)+\mathcal T_z(A),\qquad
\sqrt A\log A\,|\mathcal T_z(A)|<2^{-80}.
\tag{T12}
$$

The finite sum includes the original unit row, every $n<A$, all intervening
scales and the same actual filter. Only the entire upper complement has
been bounded. In the normalization of the
[effective Nicolas core](../ArithSums/nicolas2025comparison.md#an-effective-core-bound-at-the-selected-ga2-source),
a lower bound of $-\mathcal E(\log A)+2^{-80}$ for this normalized finite
sum would suffice; it has not been supplied. The cutoff is enormous,
with logarithmic row exponent $\log H_z/\log z=1024\log z$, and no
computation or sign certificate for that finite sum is asserted.

The application pays one previously unbounded complete component at the
critical scale. It does not prove a compact-$u$ Alladi theorem, control
the remaining signed head, establish a practical algorithm, extend a
finite Robin verification range, or prove RH. The classical ordinary
Mertens estimate and the semigroup/Rankin mechanism are reused, without
an originality claim.

## A complete divisor-order remainder inside the finite critical head

Keep the same $L=\log z\ge25$, $z\le x\le2z$,
$P_z,M_z,J_x^{\eta_z}$ and $R=1024L^2$, $H_z=e^R$ from the
complete upper row bound above. Put

$$
K_z=\left\lceil\frac{L}{\log2}\right\rceil+160,
\qquad \ell=\log x.
$$

In the actual finite divisor-fiber identity (T7), split the kernel itself:

$$
\begin{aligned}
J_x^{\ge K_z}(n)
&=\sum_{\substack{d\mid P_z\\\omega(d)\ge K_z}}\mu(d)
\int_{dn}^{d(n+1)}G_{\eta,x}(\log s)s^{-2}\,ds,\\
J_x^{<K_z}(n)&=J_x^{\eta_z}(n)-J_x^{\ge K_z}(n).
\end{aligned}
\tag{D1}
$$

Every divisor of $P_z$ is square-free, so $\omega(d)$ counts its selected
primes. The complete remaining finite head has the uniform bound

$$
\boxed{
\sqrt x\log x
\sum_{1\le n<\lceil H_z\rceil}
|M_z(n)J_x^{\ge K_z}(n)|<2^{-80}.
}
\tag{D2}
$$

This uses the same full $M_z$ in every row. Truncating the kernel's divisor
order does not replace that prefix by a different sieve. The unit row
$n=1$ is included in (D2).

### A finite tilted divisor budget

Reuse (T4), $\prod_{p\le z}(1+1/p)<8L$. Finite products give

$$
D^{(2)}:=\sum_{d\mid P_z}\frac{2^{\omega(d)}}d
=\prod_{p\le z}(1+2/p)<64L^2.
\tag{D3}
$$

Normalize these positive weights only to compute their finite moments.
The number of selected primes has mean
$m_2=\sum_{p\le z}2/(p+2)$ and variance at most $m_2$.
For $0\le t\le1/2$, the elementary bound
$\log(1+t)\ge t-t^2/2\ge3t/4$ yields

$$
m_2\le2\sum_{p\le z}1/p
\le\frac83\log(8L)<L\qquad(L\ge25).
$$

For the last comparison, $L-(8/3)\log(8L)$ is increasing on this range
and is positive at $25$, using $\log200<6$.
The latter follows from $e>5/2$ and $(5/2)^6>200$.
Consequently the second moment is at most $m_2^2+m_2<2L^2$.
For each integer $K\ge0$, the complete order tails therefore satisfy

$$
\begin{aligned}
\sum_{\substack{d\mid P_z\\\omega(d)\ge K}}\frac1d
&<64L^2\,2^{-K},\\
\sum_{\substack{d\mid P_z\\\omega(d)\ge K}}\frac{\omega(d)}d
&<64L^3\,2^{-K},\\
\sum_{\substack{d\mid P_z\\\omega(d)\ge K}}\frac{\omega(d)^2}d
&<128L^4\,2^{-K}.
\end{aligned}
\tag{D4}
$$

Indeed $2^{-\omega(d)}\le2^{-K}$ on these actual divisors; multiply
this inequality by the positive tilted weights and their moments.
This is the classical finite Euler-product exponential-moment argument,
not a probability assumption on the primes or on the Möbius sequence.

### Pay every head row, including rows below the source clock

For a discarded divisor, $d\ge2^{K_z}\ge2^{160}z>x$.
Thus $dn>x$ for every $n\ge1$, and FIB (429.3) applies over the
entire discarded fiber even when $n<x$.
Write $Q=R+1$. In every head row, $n+1\le\lceil H_z\rceil$ and
$\log(n+1)\le R+1=Q$. If $j=\omega(d)$, then $\log d\le jL$,
so the nonnegative argument $v=\log(s/x)$ is at most $Q+jL$ on
$dn\le s\le d(n+1)$. The exact fiber mass gives

$$
|J_x^{\ge K_z}(n)|
\le\frac1{\ell n(n+1)}
\sum_{\substack{d\mid P_z\\\omega(d)\ge K_z}}
\frac{(Q+jL)^2/2+Q+jL+12}{d}.
\tag{D5}
$$

Use $|M_z(n)|\le n$, retaining its unit, and
$\sum_{1\le n<\lceil H_z\rceil}1/(n+1)\le\log\lceil H_z\rceil\le Q$.
Equations (D4)–(D5) bound the left side of (D2) by

$$
\sqrt x\,Q\,64L^2\,2^{-K_z}
\left[Q^2/2+Q+12+(Q+1)L^2+L^4\right].
\tag{D6}
$$

Since $Q\le1025L^2<2^{11}L^2$, the bracket is less than
$2^{20}L^4$. Also $\sqrt x<2e^{L/2}$, so (D6) is less than

$$
2^{38-K_z}L^8e^{L/2}
\le2^{-122}L^8e^{-L/2}<2^{-80}.
\tag{D7}
$$

For the final comparison, $L^8e^{-L/2}$ decreases on $L\ge25$;
at $25$, $25^8<2^{40}$ and $e^{-25/2}<2^{-25/2}$ make (D7)
less than $2^{-94.5}$. All comparisons are symbolic outward bounds;
no numerical experiment or optimality of $K_z$ is claimed.

### The complete two-remainder interface at the same selected source

The discarded divisor orders occur only in the finite head. The already
paid complete upper row tail has all divisor orders, in a disjoint row
range. Combining their exact decompositions gives

$$
I_\psi(x)=
\sum_{1\le n<\lceil H_z\rceil}M_z(n)J_x^{<K_z}(n)
+\mathcal T_z(x)+\mathcal D_z(x),
$$

$$
\sqrt x\log x\,|\mathcal T_z(x)+\mathcal D_z(x)|<2^{-79}.
\tag{D8}
$$

Here $\mathcal D_z$ is the full signed sum discarded in (D2), and
$\mathcal T_z$ is the complete row tail in (T12). No lower row,
prime contribution or transported unit compensation is omitted.
The original $d=1$ divisor is retained in $J_x^{<K_z}$.

At the same eligible selected Robin source, $x=A=\log N$ and
$z=P^+(N)$ satisfy the already paid conditions above. Thus a lower bound
of $-\mathcal E(\log A)+2^{-79}$ for this normalized retained finite sum
would supply the existing sufficient Robin condition. That lower bound
remains unproved. The new application pays the complete high-order
kernel contribution of every remaining head row; it supplies neither
signs for the retained sum nor a practical algorithm, a new finite Robin
verification range or RH. The tilted products and moments are classical
inputs applied to the actual existing kernel, with no originality or
Lean-certification claim.

## Uniform asymptotic far tails for a polynomially growing filter

This application uses the same actual $P_z,M_z,\eta_z,w$ and
$J_x^{\eta_z}$ as (CP.1)–(CP.3) of
[FIB §428](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
It reuses the complete fiber budget in §424 and the smooth-semigroup
identity (T3). The ordinary Mertens supplier is the stronger
Vinogradov–Korobov estimate in Lee–Leong
[arXiv:2208.06141v5, Theorem 1.1, (11)](https://arxiv.org/pdf/2208.06141v5),
already recorded with its threshold and constants in
[the Ng note, (N7)](ng2004summatorymobius.md#a-concrete-cutoff-coefficient-from-the-existing-explicit-supplier).
No new ordinary or rough Mertens theorem is supplied.

Write $\Lambda(u)=1+\log u$ for $u\ge1$ and define the actual
row norm with absolute values inside the integral by

$$
Q_{x,z}(n)=\int_x^\infty
|\eta_z(t/n)-\eta_z(t/(n+1))|w(t)\,dt.
$$

Here the absolute value is inside the integral. The complete
$\beta$-fiber norm, retaining every positive divisor order, is

$$
\mathcal B_{x,z}(n)=
\sum_{j\ge1}|\theta_{z,j}|
\sum_{m=jn}^{j(n+1)-1}Q_x(m),\qquad
\theta_z=\kappa_z*\beta.
$$

$Q_x$ denotes the original $R$-kernel norm in §424, not an
unfiltered factorial norm. The existing transport gives
$|J_x^{\eta_z}(n)|\le Q_{x,z}(n)\le\mathcal B_{x,z}(n)$.

Fix $A,b>0$ and $\kappa>A$. For sufficiently large $x$, put
$L=\log x$ and

$$
T_x=\left\lceil\exp\left(\frac{\kappa bL^2}{\log L}\right)
\right\rceil.
\tag{U1}
$$

The following asymptotic application is uniform on $2\le z\le x^b$:

$$
\boxed{
\sum_{n>T_x}|M_z(n)|\mathcal B_{x,z}(n)
\ll_{A,b,\kappa}x^{-A}.}
\tag{U2}
$$

Consequently it also bounds the tail with $Q_{x,z}(n)$ or
$|J_x^{\eta_z}(n)|$ in place of $\mathcal B_{x,z}(n)$. Constants
may depend on the fixed original $R,\beta$; the actual filter and
all its fibers are retained. A proof on paper follows; there is no
Lean verification or numerical starting threshold for this application.

### Reused complete kernel budget

Fix the lower integration limit at $e$. Nonnegativity gives
$Q_x(m)\le Q_e(m)$ for every $x\ge e$. Thus §424.3, §424.12
and (CP.3), with the same fixed finite $C_e$ and $A_{\beta,2}$, give

$$
\mathcal B_{x,z}(n)
\le C_ec_0^2A_{\beta,2}\frac{\Lambda(n)^2}{n^2}
\sum_{d\mid P_z}\frac{\Lambda(d)^2}{d}
\ll\frac{\Lambda(n)^2}{n^2}\log^3(2z).
\tag{U3}
$$

The last bound reuses the full divisor moments (T8). Their stated
range $\log z\ge25$ supplies the asymptotic bound; the bounded
range $2\le z\le e^{25}$ is absorbed into the fixed constant.
No divisor or jump endpoint is removed, and no $x$-dependent kernel
constant is treated as uniform.

### Ordinary cancellation and a moving smooth-semigroup tilt

Let $V(u)=u^{3/5}/(\log u)^{1/5}$ for $u>1$. The existing
Lee–Leong input, after absorbing its $\log v$ prefactor with
strict exponent slack, gives fixed $c,C>0$ with
$|M(v)|\le Cv e^{-cV(\log v)}$ for sufficiently large $v$.
Choose once and for all $A/\kappa<\vartheta<1$.

Split the exact identity (T3) at smooth integers $a\le y^\vartheta$.
In that range $y/a\ge y^{1-\vartheta}$, so the ordinary input and
the complete smooth harmonic mass in (T4) give an upper bound
$\ll_\vartheta y\log(2z)e^{-c_\vartheta V(\log y)}$.
For the complementary range, use $|M(y/a)|\le y/a$ and Rankin's
inequality. Uniformly in $z\ge2$ and $0<\delta\le1/4$, this yields

$$
\frac{|M_z(y)|}{y}
\ll_\vartheta \log(2z)e^{-c_\vartheta V(\log y)}
+y^{-\vartheta\delta}\mathcal E_z(\delta),\qquad
\mathcal E_z(\delta)=\prod_{p\le z}(1-p^{-1+\delta})^{-1},
\tag{U4}
$$

for all sufficiently large $y$, with the threshold independent of
$z,\delta$. This is the same semigroup/Rankin mechanism as (T6),
with the stronger ordinary input and a different parameter choice.

Now take

$$
\delta_x=\frac{\log L}{bL}.
\tag{U5}
$$

Eventually $0<\delta_x\le1/4$, and $z\le x^b$ implies
$\delta_x\log z\le\log L$. The higher prime-power terms in the
logarithm of the Euler product are uniformly summable, giving

$$
\log\mathcal E_z(\delta_x)
=\sum_{p\le z}p^{-1+\delta_x}+O(1).
$$

To keep the moving-parameter cost explicit, use the classical
first-Mertens identity $\sum_{p\le e^v}\log p/p=v+O(1)$,
already used in the semigroup budgets above. Put
$h_\delta(v)=(e^{\delta v}-1)/v$, a positive increasing function.
Partial summation gives

$$
\sum_{p\le z}\frac{e^{\delta\log p}-1}{p}
=\int_{\log2}^{\log z}h_\delta(v)\,dv
+O\bigl(h_\delta(\log z)+h_\delta(\log2)\bigr).
$$

For the common range in (U5),
$h_{\delta_x}(\log z)\le h_{\delta_x}(bL)=(L-1)/(bL)$ and

$$
\int_0^{\log L}\frac{e^u-1}{u}\,du\ll\frac L{\log L}.
$$

Together with the classical prime harmonic sum this proves

$$
\log\mathcal E_z(\delta_x)
\ll_b \log L+\frac L{\log L}=o(L),
\qquad 2\le z\le x^b.
\tag{U6}
$$

### Sum the complete far tail

Multiplying (U3) and (U4), and summing all $n>T_x$, bounds the
left side of (U2) by a fixed constant times

$$
\begin{aligned}
&\log^4(2z)\sum_{n>T_x}\frac{\Lambda(n)^2}{n}
 e^{-c_\vartheta V(\log n)}\\
&\quad+\log^3(2z)\mathcal E_z(\delta_x)
 \sum_{n>T_x}\frac{\Lambda(n)^2}{n^{1+\vartheta\delta_x}}.
\end{aligned}
\tag{U7}
$$

For the first term, integral comparison with $u=\log t$ and
strict exponent slack absorb the polynomial factor. At the chosen
cutoff,

$$
V(\log T_x)\asymp_{b,\kappa}
\frac{L^{6/5}}{(\log L)^{4/5}},\qquad
\frac{V(\log T_x)}L\longrightarrow\infty.
$$

Hence that whole term is $O(x^{-D})$ for any fixed $D>0$.
For the second term, decreasing integral comparison gives, uniformly
for $0<a\le1/4$ and sufficiently large $T$,

$$
\sum_{n>T}\frac{\Lambda(n)^2}{n^{1+a}}
\ll T^{-a}\left(
\frac{\Lambda(T)^2}{a}+\frac{\Lambda(T)}{a^2}+\frac1{a^3}
\right).
$$

Taking $a=\vartheta\delta_x$, the exponent is
$a\log T_x=\vartheta\kappa L+o(1)$. By (U6), all remaining
Euler and polynomial costs are
$\exp[O_b(L/\log L)+O_{b,\kappa,\vartheta}(\log L)]$.
Thus the second term is $x^{-\vartheta\kappa+o(1)}=O(x^{-A})$,
since $\vartheta\kappa>A$. This establishes (U2) with constants
independent of every allowed $z$.

### Exact scope of the improvement and the unpaid finite head

The existing full identity (CP.2) and (U2) give

$$
I_\psi(x)=\sum_{1\le n\le T_x}M_z(n)J_x^{\eta_z}(n)
+O_{A,b,\kappa}(x^{-A}),\qquad 2\le z\le x^b.
\tag{U8}
$$

The filter may be any function $z=z(x)$ in this range, including
at prime jumps. For example $b=\kappa=1$, $A=3/4$ gives a
tail $O(x^{-3/4})$, below $1/(\sqrt x\log^2x)$ asymptotically,
while keeping all rows from the unit through $T_x$ and every
positive divisor order inside each retained row.

| Existing or current application | Source and scope | Cutoff and evidence |
|---|---|---|
| (T2) | Actual growing primorial, $z\le x\le2z$ | $\log H_z=1024\log^2z$; explicit normalized error $<2^{-80}$ for $\log z\ge25$ |
| Ng (N9) | Actual odd-source pairing and its boundary | $\log N\sim18(\log x)^{5/3}(\log\log x)^{1/3}$; asymptotic critical error |
| (U2) | Actual primorial, uniformly $2\le z\le x^b$, with the complete fiber budget before integration | $\log T_x\sim\kappa b(\log x)^2/\log\log x$; asymptotic $O(x^{-A})$ |

For $z$ comparable to $x$, (U2) has a smaller asymptotic logarithmic
cutoff than (T2). The odd-source cutoff (N9) is smaller still, but
does not supply this growing-filter, complete fiber norm. Neither
comparison certifies a numerical improvement at (T2)'s finite
starting point. No optimal cutoff or practical computation is claimed.

This is a combined application of existing cancellation, kernel and
Euler-product inputs; no general literature-novelty claim is made.
The full signed finite head in (U8) still has no required one-sided
Robin estimate. In particular the far-tail budget supplies no sign
for that head, no square-root Möbius bound, no new Robin-safe integer
range and no RH proof.

## A uniform Halász input for the actual finite head

Granville, Harper and Soundararajan, *A new proof of Halász's theorem,
and its consequences*, [arXiv:1706.03749v1, §§1, 7.1–7.2](https://arxiv.org/html/1706.03749v1),
give an existing uniform supplier. The inspected statements are their
definition of $\mathcal C(\kappa)$, equation (7.3) and Proposition 7.2.
The parameter correspondence below is a source application; no new
mean-value theorem, critical estimate or Lean verification is claimed.

Keep one actual filter $z$, including its unit, and put

$$
f_z(n)=\mu(n)\mathbf1_{P^-(n)>z},\qquad
F_z(s)=\sum_{n\ge1}\frac{f_z(n)}{n^s}
=\frac1{\zeta(s)E_z(s)},\qquad
E_z(s)=\prod_{p\le z}(1-p^{-s}).
$$

For $\Re s>1$ the defining series converge absolutely. The coefficients
of $-F_z'/F_z$ are $-\log p$ at $p^j$ with $p>z$, and zero at $p^j$
with $p\le z$. Thus $f_z\in\mathcal C(1)$ with the same class constant
for every $z$. No fixed-$u$ asymptotic is needed for this membership.

For sufficiently large $X$ with $(\log X)^6\le z\le\sqrt X$, set
$u=\log X/\log z$, $c_0=1+1/\log X$, and define $m=m_z(X)$ by

$$
\max_{|t|\le u}\left|\frac{F_z(c_0+it)}{c_0+it}\right|=e^{-m}u.
$$

Equation (7.3), with $\kappa=1$, directly gives

$$
|M_z(X)|\ll\frac X{\log X}\bigl((1+m)e^{-m}u+1\bigr).
$$

The constant is uniform in the actual filter. Proposition 7.2 also gives

$$
|F_z(c_0+it)|\ll u^{3/4}
\left(\frac{\log(z+|t|)}{\log z}\right)^{1/4}.
$$

For the explicit (T12) head, write $L=\log z\ge100$.
Every $z^2\le X<H_z=\exp(1024L^2)$ satisfies the source domain because
$(\log X)^6\le(1024L^2)^6\le z$. Its frequency window has
$|t|\le u\le1024L$, so the displayed maximum is $\ll u^{3/4}$.
The lower rows retain the exact unit-and-prime formula
$M_z(X)=1-\max\{\pi(X)-\pi(z),0\}$ for $1\le X\le z^2$.
The value $L\ge100$ checks the parameter domain; it does not make the
source's implicit constants or starting threshold numerical.

This supplies uniform magnitude estimates across the explicit finite
head. The same paper already bounds the Dirichlet maximum; its available
strength and the complete signed pairing with $J_x^{\eta_z}$ remain
distinct obligations. Taking absolute values does not retain that joint
sign or supply the required critical lower bound. The smaller asymptotic
cutoff in (U2)/(U8) remains available. No Robin/RH conclusion follows.
