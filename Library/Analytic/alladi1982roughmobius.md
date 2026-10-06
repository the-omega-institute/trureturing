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
