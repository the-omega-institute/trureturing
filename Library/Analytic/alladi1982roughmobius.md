---
bibkey: alladi1982roughmobius
authors: Krishnaswami Alladi
year: 1982
title: Asymptotic estimates of sums involving the Moebius function
doi: 10.1016/0022-314X(82)90060-9
url: https://doi.org/10.1016/0022-314X(82)90060-9
claim: The fixed-u asymptotic for the signed Möbius sum over rough integers is recorded in Alladi–Goswami 2412.03088v1 §1.1; the original compact-u uniform range and the growing-prime-filter kernel estimates are not verified here.
strata_touched: []
license: citation-only
triage: anchor
---

# Signed Möbius sums over rough integers

Alladi's paper appeared in *Journal of Number Theory* **14** (1982),
86–98, DOI [10.1016/0022-314X(82)90060-9](https://doi.org/10.1016/0022-314X(82)90060-9).
The checked statement is its explicit account in Krishnaswami Alladi and
Ankush Goswami, *Parity results concerning the generalized divisor function
involving small prime factors of integers*,
[arXiv:2412.03088v1, §1.1](https://arxiv.org/html/2412.03088v1#S1.SS1).
The original 1982 theorem and proof have not been directly inspected.
No source text is vendored and no Lean verification is supplied.

Write $P^-(n)$ for the least prime factor and set $P^-(1)=\infty$.
The source defines

$$
M_{\mathrm{rough}}(z,y)
=\sum_{\substack{1\le n\le z\\P^-(n)>y}}\mu(n).
$$

For each fixed $u=\log z/\log y>1$, §1.1 records, as $y\to\infty$,

$$
M_{\mathrm{rough}}(z,y)
=\frac{z\rho'(u)}{\log y}
+O_u\!\left(\frac{z}{(\log y)^2}\right),
$$

where $\rho$ is the Dickman function. This is a literature-attested input,
not a new asymptotic estimate. It uses the actual Möbius weight, includes
the unit, and uses a strict least-prime-factor cutoff. The unweighted
Buchstab count and Liouville weights are different objects.

The same subsection reports that Alladi established uniform estimates
over longer ranges, but does not give their precise hypotheses and errors.
This note therefore does not certify a bound uniform on
$u\in[1+\delta,U]$, for fixed $\delta>0,U>1+\delta$, or on a growing range.
Pointwise fixed-$u$ asymptotics do not supply those assertions.

## Correspondence with a growing FIB prime section

For $Q(y)=\prod_{p\le y}p$, the coprime prefix of
[the FIB volume, §426](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
is exactly $M_{Q(y)}(z)=M_{\mathrm{rough}}(z,y)$.
Its fixed filter $P=210$ and the growing filter $Q(y)$ have different
uniformity obligations. The constants in §426.7 and §426.15 have not been
bounded uniformly for growing $Q(y)$.

At a source clock $A$, choosing $y=A^{1/u_0}$ with fixed $u_0>1$ and
$n\sim cA$ with fixed $c>0$ gives $\log n/\log y\to u_0$. This moving-$u$ sequence is not
certified by the fixed-$u$ statement alone. Moreover, one filter must be
shared by all rows of the complete pairing: choosing $y=n^{1/u_0}$
separately for each row does not invoke §426's same-filter identity.

A usable signed estimate still needs simultaneous control of the actual
rough prefix and its paired kernel at the same growing filter, the complete
original head compensation, the complementary range, and the selected
critical sources. The classical prefix formula alone does not give a sign
for the full Robin integral or prove RH. The distinct subpower range in the
[Alamoudi source](alamoudi2026subradicallysifted.md) is not substituted for
the fixed positive power cutoff here.

## The source-scale boundary $u\to1^+$

The fixed-$u$ estimate above cannot retain an
$O(z/\log^2 y)$ error with one bounded constant when $z/y\to c>1$.
For all real $y\ge2$ and $y\le z\le y^2$, exact prime counting gives

$$
M_{\mathrm{rough}}(z,y)=1-\pi(z)+\pi(y).
$$

Indeed, a composite integer whose prime factors are all strictly greater
than $y$ exceeds $y^2$. The allowed integers in this range are therefore
the unit and the primes in $(y,z]$; their Möbius weights are $1$ and $-1$.
For $z/y\to c>1$, the classical prime number theorem yields

$$
M_{\mathrm{rough}}(z,y)
=-(c-1)\frac y{\log y}+o\!\left(\frac y{\log y}\right).
$$

Here $u=\log z/\log y\to1^+$ and eventually $1<u<2$. In that interval
$\rho'(u)=-1/u$, so

$$
\frac{\log y}{y}
\left[M_{\mathrm{rough}}(z,y)-\frac{z\rho'(u)}{\log y}\right]
\longrightarrow1.
$$

Thus this moving-boundary error is of order $y/\log y$, rather than
$z/\log^2 y$. This does not contradict the fixed-$u$ statement or settle
uniformity on any interval bounded away from $u=1$. It is an elementary
scope check using exact prime counting and the classical PNT, not a new
rough-sum theorem or a claim about Alladi's uninspected uniform estimates.

For an actual proper GA1 CA source, retain $A=\log N$ and
$y=P(N)$ as distinct quantities. The [published GA1 envelope](../Arith/caveney2012sacaga.md),
Theorem 13, gives $y\sim A$ as such sources tend to infinity. Initial CA
prime support gives $\operatorname{rad}(N)=Q(y)$. Hence source-scale rows
$z=cA$, for fixed $c>1$, have exactly this moving-boundary behavior with
the same filter $Q(y)$, including the unit. This source class contains the
conditional critical maximizer selected by the extraordinary-number
reduction; no unbounded critical sequence is assumed. The asymptotic
statement supplies no effective cutoff, growing-filter kernel estimate,
complete compensated remainder bound, or Robin/RH conclusion.

## Integrated same-filter power windows from the fixed-parameter input

The unverified compact-parameter pointwise estimate above is stronger than
what is needed for a finite integrated row window. This section uses only
the fixed-$u$ statement already attested in Alladi–Goswami §1.1, the
classical PNT and second Mertens estimate, and the existing actual-kernel
convergence of FIB §§433–434. The 1982 original's uniform theorem is not
claimed to have been inspected. All arguments here are paper-level; no
new rough-sum theorem, Lean verification or originality claim is made.

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

This is an integrated conclusion. It does not assert convergence uniform
in $u$ for the rough prefix.

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

This use of dominated convergence does not convert pointwise convergence
into uniform convergence. It is sufficient for the actual row window.

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
$1/(\sqrt x\log x)$ scale. The new joint window interface uses the
existing fixed-parameter rough sum without paying the stronger,
still unverified compact-parameter pointwise theorem. It leaves the full
same-source signed comparison and RH unproved.

## A critical-scale bound for the complete upper row tail

The fixed-window limits above leave their complete complementary sum in
place. A different application of existing inputs controls every row
beyond one growing cutoff, at the Robin normalization itself. It uses the
ordinary Mertens bound already consumed in FIB §409, the actual smooth
semigroup identity in §428, the first-Mertens estimate in that section,
and the full factorial density in §429. No Alladi uniform-parameter
formula, new sieve theorem, numerical experiment, effective starting
threshold for Alladi's theorem, or Lean result is asserted.

The ordinary input is Lee–Leong,
[arXiv:2208.06141v5, Theorem 1.1, (10)](https://arxiv.org/html/2208.06141v5#S1.Thmtheorem1):

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
