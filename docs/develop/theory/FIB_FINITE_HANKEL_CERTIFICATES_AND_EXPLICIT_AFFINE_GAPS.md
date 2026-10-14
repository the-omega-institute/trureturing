# Explicit finite Hankel certificates and native affine capacity gaps

**Permanent reference input.** This volume contains ordinary handwritten
mathematics. Its statements and proofs are not Lean-verified results.

For an arbitrary finite real prefix, a bound on the rank of its one square
Hankel matrix prevents uniformly small relative error to the square-root
sequence once the prefix is sufficiently long. An explicit sufficient
Hankel index is

$$
B(N,\rho)=2^{16NK+4},\qquad
K=4N+10+\left\lceil\log_2\frac{128(1+\rho)}{1-\rho}\right\rceil,
\qquad N\ge1,\quad 0<\rho<1.
$$

The corresponding prefix has $2B(N,\rho)+1$ entries. The proof keeps the
entire boundary of a finite generating polynomial. It neither extends a
given prefix nor assumes a nonsingular Hankel block.

For the native affine contract of *Native FIB on the full open domain:
affine approximation and finite attainment*, including its §11
*Fixed-dimension uniform gaps and finite Hankel certificates*, this index
gives an explicit positive squared-error excess
$\Gamma_{\mathrm{exp}}(n,Z)$ at every fixed dimension bound $n$ when
$0<Z<2/3$. The norm remains the original Euclidean norm on all ten
outputs. The native application uses the companion's bounded-observable
theorem, with arbitrary preparation, arbitrary encoders, both affine
offsets, and all real native commands.

The finite theorem is self-contained in §§1–3. Sections 4–7 specify the
native dependencies and prove the quantitative application. Section 8
records the exact scope of the existing upper witnesses and boundary
regimes. Sources, classical ingredients, and remaining questions are in
§9.

## 1. The exact finite problem

**Definition 1.1 (Finite Hankel minimax).** Let $N\ge1$ and $m\ge0$ be
integers. Set $L_m=2m+1$. For a real vector
$u=(u_1,\ldots,u_{L_m})$, define

$$
H_m(u)=(u_{p+q+1})_{0\le p,q\le m},\qquad
\mathcal R_{N,m}
=\{u\in\mathbb R^{L_m}:\operatorname{rank}H_m(u)\le N\},
$$

$$
J_m(u)=\max_{1\le j\le L_m}\frac{|u_j-\sqrt j|}{\sqrt j},
\qquad
d_{N,m}=\min_{u\in\mathcal R_{N,m}}J_m(u).
\tag{1.1}
$$

The minimum exists by Lemma 1.2. The admissible objects are all real
vectors satisfying this one finite rank condition. There is no
extendibility, recurrence, realization, regularity, or positivity
assumption in the definition. In particular, no individual member of
$\mathcal R_{N,m}$ is asserted to extend to an infinite sequence of rank
at most $N$, or to arise from a native model.

The integer $m$ is the Hankel index: the matrix has $m+1$ rows and
columns, while the prefix has $2m+1$ scalar entries.

**Lemma 1.2 (Attainment and monotonicity).** For every $N\ge1$ and
$m\ge0$, the minimum in (1.1) is attained and
$0\le d_{N,m}\le1$. For fixed $N$, $d_{N,m}$ is nondecreasing in $m$.
If $m<N$, then $d_{N,m}=0$.

**Proof 1.2.** The rank condition is the vanishing of all
$(N+1)$-minors when such minors exist; otherwise it is vacuous.
It therefore defines a closed set. The zero vector is feasible and
has objective one. The set

$$
\{u\in\mathcal R_{N,m}:J_m(u)\le1\}
$$

is nonempty and closed, and lies in the compact box
$0\le u_j\le2\sqrt j$. The continuous function $J_m$ attains a minimum
on this set. Every feasible point outside it has objective greater than
one, so this is the global minimum. This argument includes a minimum
whose value is exactly one.

Truncate a feasible vector at index $m+1$ to its first $2m+1$ entries.
Its $H_m$ is the upper-left principal submatrix of $H_{m+1}$, so its
rank is at most $N$. Removing coordinates cannot increase the objective.
Applying this to a minimizer gives $d_{N,m}\le d_{N,m+1}$.
If $m<N$, every $(m+1)$-square matrix has rank at most $N$, and the
vector $u_j=\sqrt j$ is feasible with objective zero. $\square$

**Theorem 1.3 (Explicit arbitrary-prefix certificate).** For every
integer $N\ge1$ and real $0<\rho<1$, put

$$
C=\frac{128(1+\rho)}{1-\rho},\qquad
K=4N+10+\lceil\log_2 C\rceil,\qquad
B(N,\rho)=2^{16NK+4}.
\tag{1.2}
$$

Then

$$
d_{N,B(N,\rho)}>\rho.
\tag{1.3}
$$

Equivalently, at $m=B(N,\rho)$ there is no real vector satisfying both

$$
\operatorname{rank}H_m(u)\le N,\qquad
(1-\rho)\sqrt j\le u_j\le(1+\rho)\sqrt j
\quad(1\le j\le2m+1).
\tag{1.4}
$$

The equivalence uses the attained minimum, not an assumption that a
strict inequality for each vector automatically remains strict under an
infimum.

## 2. Complete finite proof of Theorem 1.3

**Proof 1.3.** Write

$$
a=1-\rho,\quad b=1+\rho,\quad
J=8NK,\quad m=2^{2J+4}=B(N,\rho),\quad L=2m+1,
$$

$$
t_-=m^{-1/2}=2^{-J-2},\qquad t_+=\frac14.
\tag{2.1}
$$

Here $a>0$, $C=128b/a>128$, and $K$ is a positive integer greater
than one. In particular

$$
J\ge8N\ge4,\qquad K\le J,\qquad N+\tfrac12\le J.
\tag{2.2}
$$

The elementary inequality $2^J\ge J$ for positive integers $J$
gives $m\ge N$. The interval $[t_-,1/4]$ is nonempty. Under
$x=-\log_2t$ it is exactly $[2,J+2]$, of length $J$.
Suppose (1.4) holds. All steps below concern this one finite vector.

### 2.1 Finite dependence and coefficient normalization

Set $b_j=u_{j+1}$ for $0\le j\le2m$; the unsubscripted $b$ still
denotes $1+\rho$. Since $m\ge N$, the first $N+1$ columns of
$H_m(u)$ exist and are dependent. Choose real coefficients, not all
zero, with

$$
\sum_{k=0}^N c_k b_{p+k}=0
\quad(0\le p\le m),\qquad
\sum_{k=0}^N|c_k|=1.
\tag{2.3}
$$

The second equality is obtained by dividing one nonzero dependence
vector by its positive absolute coefficient sum. No individual
coefficient is divided by. Either end coefficient and any intermediate
coefficient may vanish. This normalization concerns only an auxiliary
homogeneous relation; it places no bound on any recurrence or native
model parameter.

Define finite polynomials

$$
S(z)=\sum_{j=0}^{2m}b_jz^j,\qquad
Q(z)=\sum_{k=0}^Nc_kz^{N-k}.
\tag{2.4}
$$

Then $Q\ne0$, $\deg Q\le N$, and the coefficient absolute sum
$\|Q\|_{\mathrm{coeff},1}$ is one.

### 2.2 All coefficients and the retained boundary

For $0\le\ell\le2m+N$, polynomial multiplication gives the exact formula

$$
[z^\ell](QS)=
\sum_{k=\max(0,N-\ell)}^{\min(N,\,2m+N-\ell)}
c_k b_{\ell-N+k},
\tag{2.5}
$$

where an empty range means zero. Define

$$
P(z)=\sum_{\ell=0}^{N-1}
\left(\sum_{k=N-\ell}^{N}c_kb_{\ell-N+k}\right)z^\ell
\tag{2.6}
$$

and

$$
\mathscr E(z)=
\sum_{p=m+1}^{2m}
\left(\sum_{k=0}^{\min(N,\,2m-p)}c_kb_{p+k}\right)z^{N+p}.
\tag{2.7}
$$

For $\ell=N+p$ with $0\le p\le m$, the full range $0\le k\le N$
is available, because $p+k\le m+N\le2m$. Its coefficient vanishes
by (2.3). Consequently

$$
Q(z)S(z)=P(z)+\mathscr E(z)
\tag{2.8}
$$

is an exact identity. The low coefficients have degrees $0$ through
$N-1$; those from $N$ through $N+m$ vanish; all remaining possible
coefficients have degrees $m+N+1$ through $2m+N$ and are precisely
(2.7). If $P$ is nonzero its degree is at most $N-1$. These statements
remain valid when either polynomial loses degree. There are no
coefficients outside the displayed total range.

Every coefficient in (2.5) has absolute value at most
$b\sqrt{2m+1}$, using $|b_j|\le b\sqrt{2m+1}$ and (2.3).
For $z=1-t$ with $0<t\le1/4$, a finite geometric-sum estimate gives

$$
\begin{aligned}
|\mathscr E(1-t)|
&\le b\sqrt{2m+1}\,\frac{(1-t)^{m+N+1}}{t}\\
&\le 2b\sqrt m\,\frac{\exp(-mt)}t.
\end{aligned}
\tag{2.9}
$$

Indeed $2m+1\le4m$ and $1-t\le\exp(-t)$. The tail in (2.7)
has not been set equal to zero. No scalar beyond $b_{2m}$ has been
introduced.

### 2.3 Positive finite generating-polynomial estimates

For $t\in[t_-,1/4]$, set $z=1-t$. The assumed relative approximation
implies

$$
a\sum_{j=1}^L\sqrt j\,z^{j-1}
\le S(1-t)\le
b\sum_{j=1}^L\sqrt j\,z^{j-1}.
\tag{2.10}
$$

For the upper bound, finite Cauchy–Schwarz and the finite geometric
identities give

$$
\sum_{j=1}^L\sqrt j\,z^{j-1}
\le
\left(\sum_{j=1}^Ljz^{j-1}\right)^{1/2}
\left(\sum_{j=1}^Lz^{j-1}\right)^{1/2},
$$

$$
\sum_{j=1}^Lz^{j-1}=\frac{1-z^L}{t}\le t^{-1},\qquad
\sum_{j=1}^Ljz^{j-1}
=\frac{1-z^L(1+Lt)}{t^2}\le t^{-2}.
\tag{2.11}
$$

These are identities for finite sums of specified weights, not for
extended values of the prefix.

For the lower bound, put $q=\lfloor1/(2t)\rfloor$. Since
$1/(2t)\ge2$,

$$
q\ge\frac1{4t},\qquad
q\le\frac{\sqrt m}{2}\le L.
$$

For $1\le j\le q$, Bernoulli's integer inequality gives
$(1-t)^{j-1}\ge1-(j-1)t\ge1/2$. Also
$\sqrt j\ge j/\sqrt q$, whence

$$
\sum_{j=1}^q\sqrt j
\ge\frac{q(q+1)}{2\sqrt q}\ge\frac{q^{3/2}}2.
$$

Thus $S(1-t)\ge aq^{3/2}/4\ge at^{-3/2}/32$. Combining the two
bounds yields

$$
\frac a{32}t^{-3/2}\le S(1-t)\le bt^{-3/2}
\quad(t_-\le t\le1/4).
\tag{2.12}
$$

In particular $S$ is strictly positive on this interval. This positivity
follows from the hypothetical error bound $\rho<1$; it is not an extra
condition on the finite relaxation or on a native realization.

### 2.4 Denominator control away from root moduli

Factor the nonzero polynomial after substitution:

$$
Q(1-t)=\sum_{k=0}^d r_kt^k
=c\prod_{i=1}^d(t-\alpha_i),\qquad d=\deg Q\le N.
\tag{2.13}
$$

The roots are complex and counted with multiplicity. A constant
polynomial has $d=0$ and an empty product. Substituting $t=1-z$
back and using the binomial theorem shows

$$
1=\|Q\|_{\mathrm{coeff},1}
\le\sum_{k=0}^d|r_k|2^k
\le2^N\sum_{k=0}^d|r_k|.
$$

Expansion of the factorization gives
$\sum_k|r_k|\le|c|\prod_i(1+|\alpha_i|)$. Therefore

$$
|Q(1-t)|\ge
2^{-N}\prod_{i=1}^d\frac{|t-\alpha_i|}{1+|\alpha_i|}.
\tag{2.14}
$$

Call $t>0$ good for $Q$ if every root satisfies

$$
|\alpha_i|\le t/2\quad\hbox{or}\quad|\alpha_i|\ge2t.
\tag{2.15}
$$

Every $t$ is good for a constant $Q$. At a good $t$,
$|t-\alpha_i|\ge\max(t,|\alpha_i|)/2$ by the reverse triangle
inequality. For $0<t\le1$ and $r\ge0$,

$$
\frac{\max(t,r)}{1+r}\ge\frac t2.
$$

For $r\le1$ use $\max(t,r)\ge t$ and $1+r\le2$; for $r\ge1$
use $r/(1+r)\ge1/2\ge t/2$. Hence each factor in (2.14) is at
least $t/4$, and, since $d\le N$ and $t/4\le1$,

$$
|Q(1-t)|\ge2^{-N}(t/4)^d\ge(t/8)^N>0.
\tag{2.16}
$$

Zero roots satisfy the first alternative in (2.15). The estimate permits
repeated roots, complex roots, degree collapse, and equality at either
separation boundary.

### 2.5 Explicit suppression of the finite remainder

At a good $t\in[t_-,1/4]$, (2.8), (2.9), (2.12), and (2.16) imply

$$
\frac{\left|S(1-t)-P(1-t)/Q(1-t)\right|}{S(1-t)}
\le64\frac ba\,8^N\sqrt m\,\exp(-mt)t^{1/2-N}.
\tag{2.17}
$$

Since $N\ge1$, the exponent $1/2-N$ is negative. The inequalities
$t\ge m^{-1/2}$ and $mt\ge\sqrt m$ therefore bound the right side by

$$
64\frac ba\,8^Nm^{N/2+1/4}\exp(-\sqrt m).
\tag{2.18}
$$

This quantity is strictly below $1/2$, as the following symbolic
comparison shows. Twice (2.18) is
$C8^Nm^{N/2+1/4}\exp(-\sqrt m)$. Using
$m=2^{2J+4}$, $\sqrt m=2^{J+2}$, and $e>2$, it is at most
$2^{A_*}$, where

$$
A_*=\log_2C+3N+(N+\tfrac12)(J+2)-2^{J+2}.
\tag{2.19}
$$

The definition of $K$ gives $\log_2C+3N<K$. Together with (2.2),
this yields

$$
A_*<J^2+3J-2^{J+2}<0.
\tag{2.20}
$$

For the last inequality, $2^J\ge J^2$ for all integers $J\ge4$:
it is equality at $J=4$, and
$2J^2-(J+1)^2=(J-1)^2-2>0$ propagates it by induction. Thus
$2^{J+2}\ge4J^2>J^2+3J$.

Define $R(t)=P(1-t)/Q(1-t)$ at good $t$. This is real, and the
strict relative error bound gives
$S(1-t)/2<R(t)<3S(1-t)/2$. In particular,

$$
0<\frac a{64}t^{-3/2}\le R(t)\le2bt^{-3/2}.
\tag{2.21}
$$

The coefficient and root estimates concern the auxiliary polynomial,
not a lower bound on a native model denominator.

### 2.6 Excluding a zero numerator before factoring it

In the coordinate $x=-\log_2t$, a nonzero root $\alpha$ of $Q(1-t)$
has bad band

$$
|\alpha|/2<t<2|\alpha|,
$$

which becomes an open interval of length two before intersection with
$[2,J+2]$. There are at most $N$ such bands, counting multiplicity;
zero roots exclude nothing. Their union has length at most $2N<J$,
so a good $t$ exists.

If $P$ were the zero polynomial, the left side of (2.17) at that
good $t$ would equal one, contradicting its strict bound below $1/2$.
Thus $P\ne0$. Its degree is at most $N-1$. Numerator roots are used
only after this conclusion.

### 2.7 A long interval separated from every root scale

Let

$$
D_{\mathrm{deg}}=\deg P+\deg Q\le2N-1.
\tag{2.22}
$$

Substitution $z=1-t$ preserves the degree of a nonzero polynomial.
Exclude the same open band for every nonzero root of both $P(1-t)$
and $Q(1-t)$. There are at most $D_{\mathrm{deg}}$ intervals in the
$x$ coordinate. Their union has length at most $2D_{\mathrm{deg}}$.
Its complement in $[2,J+2]$ has at most $D_{\mathrm{deg}}+1$ closed
interval components, with singleton components permitted. One way to see
the component bound is to remove the open intervals one at a time:
each removal increases the number of components by at most one.

The total complementary length is at least

$$
J-2D_{\mathrm{deg}}\ge8NK-4N+2>4NK.
\tag{2.23}
$$

The last difference is $4N(K-1)+2>0$. If every component had length
at most $2K$, their total length would be at most
$2K(D_{\mathrm{deg}}+1)\le4NK$, a contradiction. A component
therefore has length strictly greater than $2K$.

Translate its endpoints back to $t_\ell<t_h$. Then

$$
q_*=\frac{t_h}{t_\ell}>2^{2K}.
\tag{2.24}
$$

For each root of either polynomial, connectedness and avoidance of its
open bad band imply that the entire interval is on one side of that
band. Consequently every root satisfies either

$$
|\alpha|\le t_\ell/2
\quad\hbox{or}\quad
|\alpha|\ge2t_h.
\tag{2.25}
$$

Zero roots belong to the first group. Closed endpoints retain the weak
inequalities in (2.25), so the preceding positive factor bounds still
hold there. Bands outside the available interval, duplicate bands,
touching bands, and common roots of $P$ and $Q$ do not increase either
the length or the component bounds. No cancellation of common roots is
needed.

### 2.8 The integer and half-integer exponents

For a small root, $|\alpha|\le t_\ell/2$, at either endpoint
$t/2\le|t-\alpha|\le3t/2$. Hence its endpoint ratio lies between
$q_*/3$ and $3q_*$. For a large root, $|\alpha|\ge2t_h$, the
corresponding inequalities are
$|\alpha|/2\le|t-\alpha|\le3|\alpha|/2$, and its endpoint ratio
lies between $1/3$ and $3$.

Let $k_*$ be the number of small numerator roots minus the number of
small denominator roots, with multiplicity. Then $k_*\in\mathbb Z$.
The leading constants cancel within each polynomial's endpoint ratio.
Both values of $R$ are positive by (2.21), so the modulus estimate is
an estimate of the actual ratio:

$$
3^{-D_{\mathrm{deg}}}q_*^{k_*}
\le\frac{R(t_h)}{R(t_\ell)}
\le3^{D_{\mathrm{deg}}}q_*^{k_*}.
\tag{2.26}
$$

On the other hand, (2.21) gives, since $(2b)/(a/64)=C$,

$$
C^{-1}q_*^{-3/2}
\le\frac{R(t_h)}{R(t_\ell)}
\le Cq_*^{-3/2}.
\tag{2.27}
$$

Comparison in both directions yields

$$
(C3^{D_{\mathrm{deg}}})^{-1}
\le q_*^{k_*+3/2}\le C3^{D_{\mathrm{deg}}}.
\tag{2.28}
$$

Every integer $k_*$ satisfies $|k_*+3/2|\ge1/2$. If the exponent
is positive use the upper bound in (2.28); if it is negative take
reciprocals and use the lower bound. Since $q_*>1$, either case implies

$$
q_*^{1/2}\le C3^{D_{\mathrm{deg}}}.
\tag{2.29}
$$

But

$$
\begin{aligned}
C3^{D_{\mathrm{deg}}}
&\le2^{\lceil\log_2C\rceil+2D_{\mathrm{deg}}}\\
&\le2^{\lceil\log_2C\rceil+4N-2}
=2^{K-12}<2^K,
\end{aligned}
\tag{2.30}
$$

whereas (2.24) gives $q_*^{1/2}>2^K$. This contradiction excludes
(1.4). Lemma 1.2 supplies a minimizer, so its objective cannot be less
than or equal to $\rho$. Thus $d_{N,B(N,\rho)}>\rho$. $\square$

## 3. Finite cases and the implicit selector

**Remark 3.1 (Rank, degree, and root cases).** Rank strictly below $N$
still supplies (2.3); the argument does not require exact rank $N$.
Rank zero forces all entries of $H_m$ to be zero, and every prefix
coordinate occurs in that matrix, so it already contradicts (1.4).
Neither an invertible leading block nor a nonzero end coefficient of
(2.3) is required. No recurrence is solved forward or backward.

If $Q$ is constant, its factorization has an empty product and every
$t$ is good. If $P$ is constant, it contributes no roots. The case
$P=0$ is excluded in §2.6 before numerator factorization. All roots
may be complex, repeated, zero, or common to both polynomials. The
argument uses only their moduli and multiplicities, with no separation
condition between different roots.

In particular $N=1$ is included. Then
$Q(z)=c_0z+c_1$, $P(z)=c_1b_0$, and (2.3) is
$c_0b_p+c_1b_{p+1}=0$. Since every available $b_j$ is positive,
neither $c_0$ nor $c_1$ can vanish. Thus $P$ is a nonzero constant,
$Q$ has degree one, and $D_{\mathrm{deg}}=1$. The same estimates
apply with $K=14+\lceil\log_2C\rceil$ and $J=8K$.

**Corollary 3.2 (Bound on the least index).** For $N\ge1$ and
$0<\rho<1$, the selector

$$
M(N,\rho)=\min\{m\ge0:d_{N,m}\ge\rho\}
\tag{3.1}
$$

exists and satisfies

$$
N\le M(N,\rho)\le B(N,\rho).
\tag{3.2}
$$

Moreover $d_{N,m}>\rho$ for every $m\ge B(N,\rho)$, and
$\lim_{m\to\infty}d_{N,m}=1$ for each fixed $N$.

**Proof 3.2.** Theorem 1.3 makes the set in (3.1) nonempty, with an
element at $B(N,\rho)$. Lemma 1.2 gives $d_{N,m}=0<\rho$ for
$m<N$ and gives the asserted tail inequality by monotonicity.
The nondecreasing sequence is bounded above by one. Its limit must be
at least every $\rho\in(0,1)$, so it is one. $\square$

The definitions, qualitative limit, and selector in (3.1) are those of
the companion [F], §§11.2–11.4. The quantitative addition is the
closed bound (3.2) and the strict finite certificate (1.3). The finite
proof above does not use the companion's infinite-rank growth lemma or
diagonal subsequence argument.

## 4. Native source, metric, and companion dependencies

The notation [F] denotes *Native FIB on the full open domain: affine
approximation and finite attainment*, including its continuation §11.
The native results used here have the following precise source locations.

| Native input | Location in [F] | Use here |
| --- | --- | --- |
| Probability law, phase transport, arbitrary preparation, and full current-ray reachability | §§1.1–1.2, Lemma 1.1 and Proposition 1.2 | Actual source and finite lawful chains |
| Original five expectation pairs and their Gram matrix | §1.3, Lemma 1.3 | Original ten-output Euclidean error |
| Exact affine contract and bounded-observable loss of the beta phase | Definition 2.1 and Theorem 3.3 | Beta-independent finite-error readout |
| Orthogonal output decomposition and worst-phase error | Proposition 4.1; §11.1, equation (11.3) | Fixed scalar residual |
| Finite relaxation and implicit selector and gap | §§11.2–11.4 | The quantities refined by (1.3) and §7 |
| Polynomial and height witnesses | §§7–8 and §11.6 | Upper estimates in the same model classes |
| Simultaneous paths and full all-times guards | §9 and §11.7 | Contract restrictions and upper witnesses |
| Literal dimension zero and guard-recovery exception | §11.5 | Boundary cases in §8 |

The long bounded-observable and approximation proofs belong to [F].
The finite proof in §§1–3 has no native premise. The application below
states the native data explicitly and derives its normalization and
uniform constants using the listed companion results.

**Definition 4.1 (Native source).** Fix $0<Z<1$, and write

$$
r=1-Z,\qquad H=r/2,\qquad
e_*=\sqrt{4ZH}=\sqrt{2Z(1-Z)},\qquad
\mathbb T=\mathbb R/(2\pi\mathbb Z).
\tag{4.1}
$$

In mode order $(0,1,2,3,13)$, the probability law and its tangent are

$$
p(k)=(k,H-k,Z,H-k,k),\qquad
d_{\mathrm{prob}}=(1,-1,0,-1,1)^{\mathsf T},
\qquad 0<k<H.
\tag{4.2}
$$

All entries of $p(k)$ are positive and their sum is one. Fix any
preparation height $k_0\in(0,H)$ and any preparation phases
$\theta_s^{\mathrm{in}}$. Under the negative-phase convention,
$\psi_s=\sqrt{p_s}\exp(-i\theta_s)$, and the original controls satisfy

$$
\dot p=d_{\mathrm{prob}}\dot k,\qquad
\dot\theta_s=\frac{(d_{\mathrm{prob}})_s}{p_s(k)I(k)}\dot\chi,
\qquad
I(k)=\frac2k+\frac2{H-k}=\frac r{k(H-k)}.
\tag{4.3}
$$

The phase increments relative to preparation have the form
$(u,v,0,v,u)$, with

$$
du=\left(\frac12-\frac kr\right)d\chi,\qquad
dv=-\frac kr\,d\chi,\qquad
\alpha=u-v,\quad\beta=u.
\tag{4.4}
$$

These are equalities of increments within groups, not restrictions on
the preparation phases. The coordinate change between $(u,v)$ and
$(\alpha,\beta)$ has an integer inverse and descends to $\mathbb T^2$.
After a common gauge choice the middle amplitude is $\sqrt Z>0$;
it fixes the representative of each ray. The moduli determine $k$,
and the nonzero phase factors determine the two circle coordinates. By [F],
Proposition 1.2, the exact reachable current-ray domain from each such
preparation is

$$
\mathcal M=(0,H)\times\mathbb T^2.
\tag{4.5}
$$

Producing histories are piecewise $C^1$ or absolutely continuous on
finite compact time intervals, remain at interior heights throughout,
and have finite phase variation. The initial real relation phase is
chosen consistently with
$d_{\mathrm{prob}}^{\mathsf T}\theta^{\mathrm{in}}$.
Queries are permitted at every finite prefix; no return loop or integer
winding is required. Real lifts may be used to integrate a history.
The state is the current ray, with no retained real phase lift,
endpoint state, or producing-history coordinate.

For every real $s,t$, the straight native commands are

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),\qquad
\operatorname{dom}P_s=\{(k,\alpha,\beta)\in\mathcal M:0<k+s<H\},
\tag{4.6}
$$

$$
Q_t(k,\alpha,\beta)
=\left(k,\alpha+\frac t2,\beta+
\left(\frac12-\frac kr\right)t\right),\qquad
\operatorname{dom}Q_t=\mathcal M.
\tag{4.7}
$$

Convexity of the height interval makes (4.6) exactly the guard for the
whole straight probability segment. Phase command parameters remain
arbitrary real numbers; only resulting state phases are circle classes.
Both signs and zero commands are included. If $|s|\ge H$, the
probability domain is empty.

**Proposition 4.2 (Original output identity, from [F]).** Let

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)).
$$

For each edge take the expectation pair of

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Their concatenation is $y:\mathcal M\to\mathbb R^{10}$. Set

$$
U(a)=\binom{\cos a}{\sin a},\qquad
R_a=\begin{pmatrix}\cos a&-\sin a\\ \sin a&\cos a\end{pmatrix},
\qquad J_{\mathrm{ref}}=\operatorname{diag}(1,-1),
$$

$$
A(k)=2\sqrt{k(H-k)},\qquad B_{\mathrm{nat}}(k)=2\sqrt{Zk},
$$

$$
D_0(a,b)=(a,b,a,J_{\mathrm{ref}}a,J_{\mathrm{ref}}a),\qquad
O=\bigoplus_{(i,j)\in\mathcal E}R_{\theta_i^{\mathrm{in}}-\theta_j^{\mathrm{in}}},
\qquad D=OD_0.
\tag{4.8}
$$

Then

$$
y(k,\alpha,\beta)=D\bigl(A(k)U(\alpha),B_{\mathrm{nat}}(k)U(\beta)\bigr),
\qquad D^{\mathsf T}D=4I_2\oplus I_2,
\tag{4.9}
$$

and $\|D(a,b)\|_2^2=4\|a\|_2^2+\|b\|_2^2$.

**Proof 4.2.** Under the stated sign convention, each expectation pair
is twice the real and imaginary parts of
$\overline\psi_i\psi_j$, whose phase is $\theta_i-\theta_j$.
The five increment differences are
$\alpha,\beta,\alpha,-\alpha,-\alpha$ in the displayed order.
Thus $D_0$ arranges the pairs and $O$ applies the preparation rotations.
Each of the four first-pair copies contributes $I_2$ to its Gram block,
the other pair contributes one $I_2$, and all blocks occupy disjoint
output entries. Orthogonality of $O$ and $J_{\mathrm{ref}}$ gives
(4.9). This is the identity of [F], Lemma 1.3. $\square$

All errors below use these ten entries and their ordinary Euclidean
norm, with the original factors of two. In particular (4.9) is not
a replacement of the metric by an unweighted four-output norm.
Since $A(k)\le H$ and $B_{\mathrm{nat}}(k)<e_*$, $y$ is uniformly
bounded.

## 5. The affine contract and the scalar residual

**Definition 5.1 (Literal straight-command class).** A model of integer
dimension $d\ge0$ consists of an arbitrary function $E:\mathcal M\to\mathbb R^d$,
one fixed affine decoder

$$
q_A(x)=c+LE(x)\in\mathbb R^{10},
\tag{5.1}
$$

and, for every real $s,t$, fixed ambient affine maps

$$
\mathcal U_s(z)=A_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t
\tag{5.2}
$$

such that

$$
E(P_sx)=\mathcal U_s(E(x))\quad(x\in\operatorname{dom}P_s),\qquad
E(Q_tx)=\mathcal V_t(E(x))\quad(x\in\mathcal M).
\tag{5.3}
$$

Both update and decoder offsets are allowed. All coefficients may depend
on the fixed source, preparation, and model. Update coefficients may also
depend on the command; the decoder is fixed across all commands.
No coefficient depends on the current state or its producing history.
There is no continuity,
measurability, boundedness, or injectivity requirement on $E$; no
continuity in the command parameter; and no assumed ambient inverse
or ambient group law. No sign, magnitude, or positivity restriction is
placed on model coefficients. Decoded vectors need not be native
physical outputs.

Identities hold on the entire actual domains (4.6)–(4.7). An empty
domain imposes no identity. This literal contract imposes source guards
on the execution, but does not require that their truth be recoverable
from the encoded point. Guard recovery is a separate restriction in §8.
No external height selector is supplied to the encoder or decoder.

**Definition 5.2 (Capacity and tolerances).** For an integer $n\ge0$, let
$\mathfrak F_{\le n}(Z)$ be all models of Definition 5.1 of dimensions
$0\le d\le n$, for an arbitrary fixed preparation. Define

$$
\operatorname{err}(A)=
\sup_{x\in\mathcal M}\|q_A(x)-y(x)\|_2\in[0,+\infty],
\qquad
e_n^{\mathrm{aff}}(Z)=
\inf_{A\in\mathfrak F_{\le n}(Z)}\operatorname{err}(A),
\tag{5.4}
$$

$$
\mathcal A_{\le n,Z}
=\{\epsilon\in[0,\infty):
\exists A\in\mathfrak F_{\le n}(Z),\
\operatorname{err}(A)\le\epsilon\}.
\tag{5.5}
$$

The convention for an empty class is $\inf\varnothing=+\infty$.
The literal class is nonempty for every $n$: the unique
zero-dimensional encoder, its unique updates, and the zero decoder have
finite error. Changing preparation rotates the output by a fixed
orthogonal map and leaves the increment-coordinate commands unchanged.
Rotating the decoder gives a bijection of the corresponding model
classes preserving errors and dimensions. Changing preparation height
changes producing histories but not (4.5). The capacity notation
therefore suppresses preparation.

Every encoder, every matrix, every row, and every offset may vary from
one model in this infimum to another.

**Theorem 5.3 (Inherited bounded-observable reduction).** In each model
of Definition 5.1, any fixed affine scalar functional of $E$ that is
bounded on every phase torus at fixed height is independent of $\beta$.
In particular a decoder of finite uniform error is independent of
$\beta$.

This is [F], Theorem 3.3, with its original unrestricted hypotheses.
That theorem uses finite-dimensional spaces of pointwise functions and
abstract unitary characters, without imposing regularity on them.
Its boundedness hypothesis concerns the scalar observable, not the
encoder. Here a finite-error decoder is bounded because $y$ is bounded,
so each decoded component satisfies that hypothesis. No assertion
about unbounded encoder coordinates or all encoder fibers is imported.

**Lemma 5.4 (Original-metric scalar residual).** Let $A$ have finite
error $\epsilon$, and put

$$
\Delta=\epsilon^2-4ZH.
$$

Then $\Delta\ge0$. With the homogeneous encoder
$F=(1,E)^{\mathsf T}$, there is a single real row $\lambda$ such that
$g(k)=\lambda F(k,0,0)$ and

$$
\left|g(H-x)-2\sqrt{(H-x)x}\right|
\le\sqrt{Zx+\Delta/4}
\quad(0<x<H).
\tag{5.6}
$$

**Proof 5.4.** As in [F], Proposition 4.1, use the fixed orthogonal
decomposition

$$
\binom{a(k,\alpha)}{b(k,\alpha)}
=(D^{\mathsf T}D)^{-1}D^{\mathsf T}q_A(k,\alpha,\beta),
\qquad
w=q_A-D(a,b).
\tag{5.7}
$$

Here $w\perp\operatorname{im}D$. All components are fixed affine
observables, and Theorem 5.3 makes them independent of $\beta$.
Orthogonality and (4.9) give the exact maximum over $\beta$:

$$
\max_{\beta\in\mathbb T}\|q_A-y\|_2^2
=\|w\|_2^2+
4\|a-A(k)U(\alpha)\|_2^2+
\bigl(\|b\|_2+B_{\mathrm{nat}}(k)\bigr)^2.
\tag{5.8}
$$

If $b\ne0$, take $U(\beta)=-b/\|b\|_2$; if $b=0$, every
$\beta$ has the same last term. All such phases are actual reachable
states by (4.5). In particular

$$
\epsilon^2\ge4\|a-A(k)U(\alpha)\|_2^2+4Zk.
\tag{5.9}
$$

Taking the supremum over interior heights gives
$\epsilon^2\ge4ZH$. This uses no value of $E$ at $k=H$.

Let $g(k)$ be the first component of $a(k,0)$. The fixed projection
in (5.7) followed by the fixed affine decoder makes it one row of
$(1,E)$, including the decoder offset. At $\alpha=0$, keep its
scalar squared error from (5.9) and set $k=H-x$. Then

$$
4\left|g(H-x)-2\sqrt{(H-x)x}\right|^2
\le\epsilon^2-4Z(H-x)=\Delta+4Zx,
$$

which is (5.6). The output component outside $\operatorname{im}D$
and the unused components have only been removed as nonnegative terms.
The coefficient $\Delta/4$ is forced by the original Gram factor
four. $\square$

## 6. A finite lawful chain gives the exact rank relaxation

**Lemma 6.1 (Homogeneous finite-chain factorization).** Suppose
$A\in\mathfrak F_{\le n}(Z)$ has finite error. For an integer $m\ge0$,
let $L=2m+1$ and choose $0<h<H/L$. Define

$$
v_j=\frac{g(H-jh)}{2\sqrt{Hh}}\quad(1\le j\le L),\qquad N=n+1.
\tag{6.1}
$$

Then $v\in\mathcal R_{N,m}$.

**Proof 6.1.** A phase-free probability leg from the preparation
height reaches $(H-h,0,0)$. Relative phase increments remain zero.
Repeating $P_{-h}$ at most $L-1$ times visits exactly the heights
$H-jh$, $1\le j\le L$. The minimum is $H-Lh>0$, and the maximum
$H-h$ is below $H$. Every whole probability segment lies between its
interior endpoints, so every prefix and intermediate point is lawful.

Homogenize the update for this model and this one command:

$$
T=\begin{pmatrix}1&0\\ b_{-h}&A_{-h}\end{pmatrix},
\qquad \xi=F(H-h,0,0).
$$

It has size $d+1\le n+1=N$. The exact identities along the finite
chain give

$$
g(H-jh)=\lambda T^{j-1}\xi,\qquad
v_{p+q+1}=(\lambda T^p)
\left(\frac{T^q\xi}{2\sqrt{Hh}}\right)
\quad(0\le p,q\le m).
\tag{6.2}
$$

All entries exist because $p+q+1\le2m+1=L$. Thus $H_m(v)$ is
the product of an $(m+1)$-by-$(d+1)$ matrix and a
$(d+1)$-by-$(m+1)$ matrix, proving the rank bound. $\square$

The matrices, homogeneous states, and readout rows in this lemma belong
to one model at a time. They need no common limit, norm bound, inverse,
or shared coefficients across models. Although powers of an ambient
matrix are algebraically defined, the proof uses their encoding
identities only on this finite lawful chain. It asserts neither an
infinite native execution nor a rank-preserving extension of arbitrary
feasible prefixes.

**Lemma 6.2 (Finite certificate transfer).** For the same model and
parameters, put

$$
\rho_0=\sqrt{\frac Z{4H}},\qquad
\eta_h=1-\sqrt{1-\frac{Lh}{H}}.
\tag{6.3}
$$

Then

$$
d_{N,m}\le J_m(v)
\le\eta_h+\sqrt{\rho_0^2+\frac{\Delta}{16Hh}}.
\tag{6.4}
$$

In particular, if $d_{N,m}-\eta_h>\rho_0$, then

$$
\Delta\ge
16Hh\left((d_{N,m}-\eta_h)^2-\rho_0^2\right)>0.
\tag{6.5}
$$

**Proof 6.2.** Substitute $x=jh$ into (5.6) and divide by
$2\sqrt{Hhj}$. The exact normalized inequality is

$$
\frac{\left|v_j-\sqrt j\sqrt{1-jh/H}\right|}{\sqrt j}
\le\sqrt{\rho_0^2+\frac{\Delta}{16Hhj}}
\quad(1\le j\le L).
\tag{6.6}
$$

Thus the original $\Delta/4$ becomes $\Delta/(16Hhj)$.
Because $\Delta\ge0$, $j\ge1$, and $jh\le Lh<H$, the triangle
inequality yields

$$
\frac{|v_j-\sqrt j|}{\sqrt j}
\le\eta_h+\sqrt{\rho_0^2+\frac{\Delta}{16Hh}}.
$$

Take the maximum and use the feasibility from Lemma 6.1 to obtain
(6.4). Under the additional hypothesis, the quantity
$d_{N,m}-\eta_h$ is positive and greater than $\rho_0$, so squaring
the resulting comparison with the square root preserves the inequality
and gives (6.5). $\square$

This is a necessary certificate. A feasible vector in (1.1) is not
thereby a native realization, and the certificate supplies no converse
construction of an encoder.

## 7. Explicit native affine capacity gap

**Definition 7.1 (Explicit constants below the transition).** For an
integer $n\ge0$ and $0<Z<2/3$, retain (4.1) and set

$$
N=n+1,\qquad
\rho_0=\sqrt{\frac Z{4H}},\qquad
\eta=\frac{1-\rho_0}{4},\qquad
\rho=\rho_0+2\eta=\frac{1+\rho_0}{2}.
\tag{7.1}
$$

Define

$$
K_Z=4(n+1)+10+
\left\lceil\log_2\left(\frac{128(3+\rho_0)}{1-\rho_0}\right)\right\rceil,
\qquad B_Z=2^{16(n+1)K_Z+4},
\tag{7.2}
$$

$$
L=2B_Z+1,\qquad
h=\frac{H(2\eta-\eta^2)}L,
\tag{7.3}
$$

and

$$
\Gamma_{\mathrm{exp}}(n,Z)=
\frac{16H^2}{2B_Z+1}(2\eta-\eta^2)
\left((\rho_0+\eta)^2-\rho_0^2\right).
\tag{7.4}
$$

These constants depend only on $n,Z$. Indeed $Z<2/3$ is equivalent
to $Z<4H$, so $0<\rho_0<1$, $0<\eta<1/4$, and
$\rho_0<\rho<1$. Also

$$
\frac{1+\rho}{1-\rho}=\frac{3+\rho_0}{1-\rho_0}.
\tag{7.5}
$$

Thus $K_Z$ and $B_Z$ are exactly the constants of Theorem 1.3 at
$(N,\rho)$, not constants for a different relative-error normalization.

**Theorem 7.2 (Explicit original-metric fixed-dimension gap).** For
every integer $n\ge0$, every $0<Z<2/3$, every allowed preparation, and every
finite-error model $A\in\mathfrak F_{\le n}(Z)$,

$$
\operatorname{err}(A)^2>4ZH+\Gamma_{\mathrm{exp}}(n,Z),
\qquad \Gamma_{\mathrm{exp}}(n,Z)>0.
\tag{7.6}
$$

Every model, including an infinite-error one, therefore satisfies the
corresponding nonstrict lower bound. For the capacity,

$$
e_n^{\mathrm{aff}}(Z)^2
\ge4ZH+\Gamma_{\mathrm{exp}}(n,Z)>4ZH,
\tag{7.7}
$$

and equivalently

$$
e_n^{\mathrm{aff}}(Z)-e_*
\ge
\frac{\Gamma_{\mathrm{exp}}(n,Z)}
{\sqrt{4ZH+\Gamma_{\mathrm{exp}}(n,Z)}+\sqrt{4ZH}}
>0.
\tag{7.8}
$$

**Proof 7.2.** The choice (7.3) obeys

$$
0<Lh=H(2\eta-\eta^2)<H,\qquad
H-Lh=H(1-\eta)^2>0,
$$

$$
\eta_h=1-\sqrt{1-Lh/H}
=1-\sqrt{(1-\eta)^2}=\eta.
\tag{7.9}
$$

Thus every point of the chain in Lemma 6.1 is an actual strictly
interior state. Use that lemma at $m=B_Z$. Theorem 1.3 and (6.4)
give

$$
\rho<d_{N,B_Z}\le J_{B_Z}(v)
\le\eta+\sqrt{\rho_0^2+\frac{\Delta}{16Hh}}.
\tag{7.10}
$$

Consequently the square root is strictly greater than
$\rho-\eta=\rho_0+\eta>0$. Squaring gives

$$
\Delta>
16Hh\left((\rho_0+\eta)^2-\rho_0^2\right)
=\Gamma_{\mathrm{exp}}(n,Z).
\tag{7.11}
$$

Both factors $2\eta-\eta^2=\eta(2-\eta)$ and
$(\rho_0+\eta)^2-\rho_0^2=\eta(2\rho_0+\eta)$ are positive.
Since $H>0$ and $L>0$, this also proves the positivity in (7.6).
An infinite-error model obeys the finite nonstrict bound automatically.
For finite errors, take the infimum of the bound
$\operatorname{err}(A)\ge\sqrt{4ZH+\Gamma_{\mathrm{exp}}}$ to
obtain (7.7). Rationalizing the difference of square roots gives
(7.8). $\square$

The modelwise inequality proved here is strict. The stated capacity
inequality is nonstrict; strictness is not passed through an infimum.
No minimizer at fixed dimension is inferred. All parameters of all
models and all preparations remain variable within the quantifiers:
only the homogeneous size bound $d+1\le n+1$ and the fixed source
parameter $Z$ enter the constants.

**Corollary 7.3 (Relation to the companion's implicit gap).** At the
same canonical $\rho$ in (7.1), let $M=M(N,\rho)$ be (3.1). The
implicit squared excess of [F], §11.4, is

$$
\Gamma_{\mathrm{imp}}(n,Z)=
\frac{16H^2}{2M+1}(2\eta-\eta^2)
\left((\rho_0+\eta)^2-\rho_0^2\right).
\tag{7.12}
$$

Then $M\le B_Z$ and

$$
0<\Gamma_{\mathrm{exp}}(n,Z)\le\Gamma_{\mathrm{imp}}(n,Z).
\tag{7.13}
$$

**Proof 7.3.** Corollary 3.2 gives $M\le B_Z$. All other factors
in (7.4) and (7.12) are identical and positive; replacing $2M+1$
by the no-smaller denominator $2B_Z+1$ proves (7.13). $\square$

The explicit value may be weaker than the implicit value. Its content
is a closed function of $n,Z$ and an explicit sufficient finite
index, without evaluating a finite minimax or searching over feasible
prefixes.

## 8. Matching contracts, inherited witnesses, and boundary regimes

### 8.1 Prescribed paths and separate guard recovery

**Definition 8.1 (Path and guard-recoverable restrictions).** In the
prescribed-path contract, require in addition one fixed affine update
for every prescribed finite native path, exact on its full lawful
source domain. For prescribed velocities $a_c=\dot k$ and
$b_c=\dot\chi$ on $[0,T]$ in the source regularity class, put

$$
\rho_{\mathrm{path}}(\tau)=\int_0^\tau a_c(v)\,dv,\qquad
\Delta_k=\rho_{\mathrm{path}}(T),\qquad
L_\chi=\int_0^T b_c(\tau)\,d\tau,
$$

$$
C_{\mathrm{path}}=\int_0^T
\rho_{\mathrm{path}}(\tau)b_c(\tau)\,d\tau.
\tag{8.1}
$$

The continuous function $\rho_{\mathrm{path}}$ is bounded on this
compact interval, and $b_c$ is absolutely integrable, so the mixed
integral exists. The source guard is

$$
0<k+\rho_{\mathrm{path}}(\tau)<H
\quad\hbox{for every }\tau\in[0,T],
\tag{8.2}
$$

equivalently
$k+\min_{[0,T]}\rho_{\mathrm{path}}>0$ and
$k+\max_{[0,T]}\rho_{\mathrm{path}}<H$. The extrema are attained,
which justifies these strict inequalities. Lawful endpoints alone do
not imply (8.2).

The endpoint formulas from [F], §9.1, are

$$
k'=k+\Delta_k,\qquad
\alpha'=\alpha+L_\chi/2,\qquad
\beta'=\beta+
\left(\frac12-\frac kr\right)L_\chi-\frac{C_{\mathrm{path}}}{r}.
\tag{8.3}
$$

The beta increment is the integral of
$(1/2-(k+\rho_{\mathrm{path}}(\tau))/r)b_c(\tau)$, giving the
negative mixed term in (8.3). Concatenating two relative path triples
gives

$$
(\Delta_1+\Delta_2,\ L_1+L_2,\
C_1+C_2+\Delta_1L_2).
\tag{8.4}
$$

These formulas describe the actual native source; they do not assume
that simultaneous paths split into finitely many straight commands.

Separately, call a model guard-recoverable when the encoded point and
the specified command determine whether that command's actual source
guard holds. Equivalently, for every command its domain indicator is
constant on each encoder fiber. For the straight contract this concerns
(4.6)–(4.7); for the path contract it also concerns (8.2). No such
condition is inserted into Definition 5.1.

Use superscripts $\mathrm{path}$, $\mathrm g$, and
$\mathrm{path,g}$ on $\mathfrak F_{\le n}$ and on its capacity to
denote these restrictions. Their inclusions are

$$
\mathfrak F_{\le n}^{\mathrm{path,g}}
\subseteq\mathfrak F_{\le n}^{\mathrm{path}}
\subseteq\mathfrak F_{\le n},\qquad
\mathfrak F_{\le n}^{\mathrm{path,g}}
\subseteq\mathfrak F_{\le n}^{\mathrm g}
\subseteq\mathfrak F_{\le n}.
\tag{8.5}
$$

Every lower bound in Theorem 7.2 therefore applies within each of
these restricted classes. For an empty class the convention
$\inf\varnothing=+\infty$ remains in force.

### 8.2 Upper witnesses under the same obligations

**Proposition 8.2 (Inherited polynomial witnesses and capacity bounds).**
For each integer $b\ge1$, all four contracts in (8.5) admit a model
of dimension $2b+3$ with

$$
\operatorname{err}(A)^2\le4ZH+\frac{8H^2}{\sqrt b}.
\tag{8.6}
$$

Consequently for $n\ge5$ and $b=\lfloor(n-3)/2\rfloor$, each capacity
$e_{n,\mathcal C}$ defined within one of these four classes satisfies,
when $0<Z<2/3$,

$$
4ZH+\Gamma_{\mathrm{exp}}(n,Z)
\le e_{n,\mathcal C}(Z)^2
\le4ZH+\frac{8H^2}{\sqrt{\lfloor(n-3)/2\rfloor}}.
\tag{8.7}
$$

Here $e_{n,\mathcal C}$ is notation for the capacity of the indicated
class, including $e_n^{\mathrm{aff}}$ for the literal class; it is not
an assertion that the four capacities coincide.

**Proof 8.2.** Use the interior Bernstein construction of [F],
§§7.1–7.3 and §11.6:

$$
\kappa_j=\frac{H(j+1)}{b+2},\qquad
P_b(k)=\sum_{j=0}^b
A(\kappa_j)\binom bj(k/H)^j(1-k/H)^{b-j}
=\sum_{j=0}^b\pi_j k^j.
\tag{8.8}
$$

Every node is interior. The companion's finite moment and
Cauchy–Schwarz proof, including $b=1$, gives

$$
|P_b(k)-A(k)|\le\sqrt2\,H b^{-1/4}
\quad(0<k<H).
\tag{8.9}
$$

Store $K_{\mathrm{ht}}=k$ and $f_j=k^jU(\alpha)$,
$0\le j\le b$, and use the fixed linear decoder
$D(\sum_{j=0}^b\pi_jf_j,0)$. This uses $1+2(b+1)=2b+3$
coordinates. By (4.9), its exact squared readout error is

$$
4(P_b(k)-A(k))^2+4Zk,
$$

so (8.9) proves (8.6). The decoder reads the stored features linearly;
it does not perform a nonlinear polynomial evaluation on the stored
height.

For all real straight commands use

$$
P_s:\quad K_{\mathrm{ht}}'=K_{\mathrm{ht}}+s,\qquad
f_j'=\sum_{h=0}^j\binom jh s^{j-h}f_h,
$$

$$
Q_t:\quad K_{\mathrm{ht}}'=K_{\mathrm{ht}},\qquad
f_j'=R_{t/2}f_j.
\tag{8.10}
$$

These maps are affine and exactly intertwine (4.6)–(4.7).
The binomial identities have their polynomial values also at zero
commands. On the actual image the probability guard is precisely
$0<K_{\mathrm{ht}}+s<H$, and the phase guard is the entire image.

For each prescribed path use the affine map of [F], Proposition 9.1,

$$
K_{\mathrm{ht}}'=K_{\mathrm{ht}}+\Delta_k,\qquad
f_j'=R_{L_\chi/2}
\sum_{h=0}^j\binom jh\Delta_k^{j-h}f_h.
\tag{8.11}
$$

Substitution gives $(k+\Delta_k)^jU(\alpha+L_\chi/2)$, exactly the
encoding of the actual endpoint. The source beta mixed term remains
present in (8.3); this particular allowed encoder forgets it.
The stored height determines the full guard (8.2). Replacing $T$
by any intermediate time in (8.1) gives the exact intermediate
encoding. Induction over finite lawful concatenations gives all finite
prefixes. At every such state the same uniform readout bound applies,
as established in [F], §§7.3 and 9.2.

Thus the upper witness belongs to each class separately. The lower
bound comes from (8.5) and Theorem 7.2, while $2b+3\le n$ gives
the upper bound in (8.7). $\square$

For every $\epsilon>e_*$, one sufficient degree in this inherited
construction is

$$
b=\max\left\{1,\
\left\lceil
\left(\frac{8H^2}{\epsilon^2-4ZH}\right)^2
\right\rceil\right\}.
\tag{8.12}
$$

This is an exact-real finite construction on the entire open source.
The degree and coordinate counts are sufficient bounds, not optimal
ones. The upper estimate is inherited content, used to compare the
explicit lower estimate under matching obligations.

### 8.3 Dimension zero, the transition, and tolerance endpoints

**Proposition 8.3 (Inherited zero-dimension and transition formulas).**
Under the literal contract,

$$
e_0^{\mathrm{aff}}(Z)=
\begin{cases}
1-Z/2,&0<Z<2/3,\\
e_*,&2/3\le Z<1.
\end{cases}
\tag{8.13}
$$

The zero decoder attains these infima. The same formula holds for
the zero-dimensional prescribed-path contract without guard recovery.
For $Z\ge2/3$ and every $n\ge0$, the literal and prescribed-path
capacities equal $e_*$, with tolerance set $[e_*,\infty)$.

For either guard-recoverable contract the zero-dimensional class is
empty, its capacity is $+\infty$, and it has no finite tolerance.
For $n\ge1$ these classes are nonempty; when $Z\ge2/3$, their
capacities equal $e_*$ and their tolerance sets are $[e_*,\infty)$.

**Proof 8.3.** These are the boundary results of [F], §11.5. The
short calculation also identifies their scope. A zero-dimensional
decoder is a constant $c$. At any fixed height, adding $\pi$ to
both phases sends $y$ to $-y$, and

$$
\frac{\|c-y\|_2^2+\|c+y\|_2^2}{2}
=\|c\|_2^2+\|y\|_2^2.
$$

Hence zero is optimal among constants. Its squared error is

$$
\sup_{0<k<H}f(k),\qquad
f(k)=16k(H-k)+4Zk.
\tag{8.14}
$$

The vertex is $k=H/2+Z/8$. When $Z<4H$ it is interior, giving

$$
\sup f=\frac{(4H+Z)^2}{4},\qquad
e_0^{\mathrm{aff}}(Z)=\frac{4H+Z}{2}=1-\frac Z2,
$$

$$
\bigl(e_0^{\mathrm{aff}}(Z)\bigr)^2-4ZH
=\frac{(4H-Z)^2}{4}>0.
\tag{8.15}
$$

When $Z\ge4H$,

$$
f(k)=4ZH+4(H-k)(4k-Z)<4ZH
\quad(0<k<H),
\tag{8.16}
$$

with supremum $4ZH$ as interior heights approach $H$. At
$Z=4H$ the difference is exactly $-16(H-k)^2$. No lawful state
need realize the supremum. The singleton encoder satisfies every
literal straight or prescribed-path affine identity. The floor from
Lemma 5.4 proves the claimed capacities for all $n$ in this regime.

For guard recovery take two heights $k_1<k_2$ and set
$s=H-(k_1+k_2)/2$. Then
$0<k_1+s<H$ but $k_2+s>H$. Their singleton encodings cannot
decide this guard, proving the zero-dimensional emptiness. This
already uses a straight command, so it holds for the path restriction
as well. For $n\ge1$ the height encoder $E(k,\alpha,\beta)=k$
with zero decoder has exact affine updates
$K'=K+s$, $K'=K$ for phase commands, and
$K'=K+\Delta_k$ for paths. It recovers the full straight and
all-times path guards. Its squared error is (8.14), which is finite
for all $Z$ and equals the floor when $Z\ge2/3$. $\square$

Thus below the transition the literal dimension-zero tolerance set is
$[1-Z/2,\infty)$, while the dimension-zero guard-recoverable
tolerance set is empty. Theorem 7.2 still applies at $n=0$, using
the homogeneous rank $N=1$; (8.13) supplies the stronger exact
dimension-zero result.

**Corollary 8.4 (Dimension limit and undecided fixed-dimension endpoint).**
For each of the four contracts, its nonempty finite-dimensional classes
are nested with dimension bound. Their capacities tend to $e_*$ as
$n\to\infty$. Allowing arbitrary finite dimension gives tolerance set

$$
\begin{cases}
(e_*,\infty),&0<Z<2/3,\\
[e_*,\infty),&2/3\le Z<1.
\end{cases}
\tag{8.17}
$$

For general positive fixed $n$ below $Z=2/3$, the exact capacity
and whether it is attained at its own value are not determined here.

**Proof 8.4.** Nesting gives nonincreasing capacities. The floor from
Lemma 5.4 and the upper estimate (8.6), with $b$ tending to infinity,
give their limit $e_*$. For guard recovery only $n=0$ is empty;
the height model supplies finite error at all $n\ge1$.
The degree choice (8.12) attains every strict tolerance above $e_*$
within each contract. Below the transition Theorem 7.2 excludes
equality for every finite dimension. At and above the transition
Proposition 8.3 supplies a finite attainer.

For any fixed nonempty class, its tolerance set is upward closed and
contains every number strictly above its infimum by the definition of
infimum. The lower endpoint belongs to that set exactly when some
model attains the infimum. The explicit lower bound and the witnesses
do not decide that endpoint for general positive fixed $n$ below the
transition. $\square$

For additional comparison below the transition, the constant zero
model gives $e_n^{\mathrm{aff}}\le1-Z/2$ for every $n$. The
prescribed-path class without guard recovery has the same upper
witness. The height model gives this upper bound in both
guard-recoverable classes for $n\ge1$. No equality of the different
capacities at general positive fixed dimension follows from these
common estimates.

## 9. Source credit, quantitative scope, and open boundaries

The substantive sources for this companion are:

- **[F]** *Native FIB on the full open domain: affine approximation and
  finite attainment*, including §11, *Fixed-dimension uniform gaps and
  finite Hankel certificates*. The dependency map in §4 specifies the
  source sections used. The native floor, qualitative nonattainment,
  uniform fixed-dimension gap, finite minimax and its qualitative limit,
  implicit selector, polynomial witnesses, path identities, and
  dimension-zero formulas are results of that source.
- **[Q]** *An explicit finite-prefix Hankel certificate from a truncated
  generating polynomial and separated root scales*. Its quantitative
  synthesis supplies the constants $C,K,B$ and
  $\Gamma_{\mathrm{exp}}$, and the finite polynomial and root-scale
  argument written out in §§1–3 and applied in §7.
- **[V]** *Independent handwritten verification of the explicit
  finite-prefix Hankel certificate and native affine capacity gap*.
  Its mathematical content includes the full coefficient-range
  expansion and detailed degree, root, boundary, and native
  normalization arguments. Mathematical support here is provided by
  the stated derivations and specified companion theorems, not by a
  verification label.

The native source [F] attributes its conventions to *Native FIB
continuation: exact affine obstruction and compact-band approximation*,
especially §§1–3 and §7.5, and through it to *AURIC FIB-ATOM:
Probability, Phase Transport and Holonomy*. Those are inherited
source attributions. No additional theorem from those nested sources
is a premise of this companion.

The general ingredients are classical: finite linear dependence,
closed determinantal conditions and compactness in finite-dimensional
real space, polynomial multiplication and factorization over
$\mathbb C$, the binomial and finite geometric identities,
Bernoulli's inequality, finite Cauchy–Schwarz estimates, and counting
the lengths and components of finitely many intervals. The native
premises in [F] additionally use finite-dimensional translation
representations and abstract characters; its upper witnesses use
Bernstein polynomials. Its qualitative proof uses finite Hankel shift
realizations, generalized eigenspaces, and finite geometric-sum
Cesaro cancellation. The quantitative finite proof here does not
invoke that infinite-sequence argument.

This is a repository-derived quantitative synthesis of those
ingredients and sources. It is not a claim of unsearched novelty,
worldwide priority, or externally verified bibliography. The handwritten
proof status applies to the whole volume.

The new quantitative statement concerns a necessary finite
certificate. In particular, $B$ is an explicit sufficient Hankel index,
and $2B+1$ is an explicit sufficient scalar-prefix length. A single
finite rank condition may admit vectors that do not extend or are
not native realizations. Neither the finite theorem nor its transfer
asserts a converse. The relative error assumption makes the
hypothetical finite samples positive, but arbitrary native coefficients
and arbitrary competing scalar readouts are not assumed positive.

The exact exponent in the index bound is

$$
16NK+4=
64N^2+160N+
16N\left\lceil\log_2\frac{128(1+\rho)}{1-\rho}\right\rceil+4.
\tag{9.1}
$$

This is a coarse bound. It does not evaluate $d_{N,m}$, the least
index $M$, or a native capacity. No practically small certificate,
efficient algorithm, conditioning bound, optimal dimension, or sharp
or matching rate follows. The lower gap (7.4) and the upper estimate
(8.6) do not match. The explicit dependence removes the implicit
selector from one sufficient lower certificate; it does not resolve
these further quantitative questions.

The following boundaries remain part of the conclusions.

- The exact capacity and attainment for general positive fixed $n$
  below the transition remain open. Modelwise strictness in (7.6)
  does not decide either question.
- Only bounded affine observables are known here to lose $\beta$.
  Unbounded encoder coordinates, all affine factors, and arbitrary
  encoder fibers are not classified.
- The source has $0<Z<1$ and $0<k<H$. Neither height endpoint nor
  the support-changing cases $Z=0,1$ are included. Approaching an
  endpoint in a scalar supremum does not add an endpoint state.
- The results concern actual current rays, one fixed affine readout,
  and all real native commands on their full domains. Retained
  history encoders, external state selectors, altered metrics,
  restricted command menus, injectivity requirements, physical-output
  restrictions, and finite-horizon variants are different problems.
- Guard recovery remains distinct from applying identities on literal
  source domains. The zero-dimensional emptiness result concerns only
  the former. General path guards remain all-times conditions.
- The homogeneous rank $N=n+1$ in this argument has no established
  identification with the hidden parameter in the original unrelated
  finite-hidden-$N$ attainment alternative. That alternative remains
  unresolved.
- Exact-real mathematical witnesses provide no finite-precision,
  robustness, physical-realization, training, or empirical
  machine-learning guarantee. No formal-kernel or model-diversity
  verification is asserted.

## 9.99 追加锚
