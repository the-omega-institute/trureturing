---
bibkey: srivastav2025sievevaughan
authors: Priyamvad Srivastav
year: 2025
title: Log-free bounds on exponential sums over primes
doi: null
url: https://arxiv.org/abs/2505.07803v2
claim: The sieve-weighted Vaughan identity retains exact von Mangoldt recovery for general normalized sieve weights by preserving extra convolution terms; the stated additive exponential-sum bound supplies no centered signed Robin-tail estimate at zero frequency.
strata_touched: []
license: citation-only
triage: anchor
---

# Exact recovery with sieve weights and the remaining signed estimate

The inspected primary is [arXiv:2505.07803v2](https://arxiv.org/html/2505.07803v2),
revised 27 January 2026; v1 was submitted 12 May 2025. The locators below
refer to v2. This note attributes the source's results and records their
parameter correspondence; it supplies neither an independent proof audit
nor Lean certification. The published identities and sieve arguments are
reused, not new project mathematics.

## The recovery operator includes additional convolutions

Write $*$ for Dirichlet convolution and $\mathbf 1(n)=1$ for $n\ge1$.
Juxtaposition of arithmetic functions means pointwise multiplication.
Section 2, Lemma 2.1 and its first Remark allow arbitrary weights with

$$
\lambda(1)=1,\qquad \theta+\theta'=\mu.
$$

With the source's least-common-multiple transform

$$
h(d)=\sum_{[d_1,d_2]=d}\lambda(d_1)\theta'(d_2),
$$

and $V>1$, the cited identity is

$$
\Lambda
=h*\log-\mathbf 1*h*\Lambda_{\le V}
 +\bigl[(\mathbf 1*\theta)(\mathbf 1*\lambda)\bigr]*\Lambda_{>V}
 +\Lambda_{\le V}.
\tag{SV1}
$$

Here $\Lambda_{\le V}$ and $\Lambda_{>V}$ truncate the complete
von Mangoldt function, including prime powers. The source also states
the corresponding identity for $\mu$. Its standard weight choice has
$1<U<U_1$, $R>1$, with $\theta'$ supported on $d\le U_1$ and
$\lambda$ on $d\le R$; consequently $h$ is supported on $d\le U_1R$.
The first Remark explicitly permits other normalized weight choices.

This recovery operator differs from requiring
$\sum_{d\mid m}a(d)=\Lambda(m)$ for a single coefficient vector $a$.
A restriction proved for that simple divisor response would not exclude
(SV1). Optimizing sieve weights and retaining exact recovery are compatible
in this published formulation, provided all additional terms are kept.
Those terms have no favorable sign asserted by Lemma 2.1.

## The divisor-to-frequency expansion is already supplied

The weights in equation (2.1) are

$$
\lambda(d)=\frac{d\mu(d)}{\varphi(d)}
 \frac{G_{qd}(R/d)}{G_q(R)}\mathbf 1_{(d,q)=1},
\qquad
G_\ell(x)=\sum_{\substack{r\le x\\(r,\ell)=1}}
 \frac{\mu(r)^2}{\varphi(r)}.
$$

Section 5.1, Lemma 5.1 gives, for every integer $n\ge1$,

$$
G_q(R)\sum_{d\mid n}\lambda(d)
=\sum_{\substack{r\le R\\(r,q)=1}}
 \frac{\mu(r)}{\varphi(r)}c_r(n),
\qquad
c_r(n)=\sum_{\substack{a\bmod r\\(a,r)=1}}e^{2\pi i an/r}.
\tag{SV2}
$$

The paper attributes this Selberg-weight/Ramanujan-sum connection to
Kobayashi and Huxley. The cited predecessors are Kobayashi,
*A note on the Selberg sieve and the large sieve*, Proc. Japan Acad. 49
(1973), 1–5, and Huxley, *The distribution of prime numbers* (1972).
Their full texts were not independently inspected here.

Thus an existing source supplies this particular transition from divisor
responses to additive frequency channels. It is not a new FIB spectral
theorem. Neither (SV1) nor (SV2) identifies these additive frequencies
with the nontrivial zeros of the Riemann zeta function or transports the
five Zeckendorf occupancy classes to the needed arithmetic amplitudes.

## The exponential-sum theorem keeps its original parameters

To distinguish the paper's small parameter from the Robin excess exponent,
write it as $\kappa$. Theorem 1 assumes $0<\kappa\le1/10$, sufficiently
large $x\ge x_0(\kappa)$, and

$$
u=\frac aq+\frac\delta x,\qquad (a,q)=1,
\qquad |\delta|\le\frac{x^{1/5+\kappa}}q,
\qquad 1\le q\le x^{2/5-\kappa},
\qquad \delta_0=\max\{1,|\delta|/4\}.
$$

It states the uncentered bound

$$
\left|\sum_{n\le x}\Lambda(n)e^{2\pi i nu}\right|
\le\frac q{\varphi(q)}
 \mathscr F_\kappa\!\left(
 \frac{\log(\delta_0q)}{\log x},
 \frac{\log^+(\delta_0/q)}{\log x}\right)
 \frac{x}{\sqrt{\delta_0q}},
\tag{SV3}
$$

with $\mathscr F_\kappa$ specified in equation (1.4) and
$\log^+z=\max\{\log z,0\}$. The theorem also bounds the corresponding
Möbius exponential sum. The Remarks explicitly include $q=1$ and $q=2$.
The source calls the result semi-explicit: $x_0(\kappa)$ is effectively
computable but is not given as a numerical threshold.

For the Robin Chebyshev sum, the additive frequency is $u=0$, represented
by $a=0$, $q=1$, $\delta=0$. Here $\delta_0=1$ and the two arguments of
$\mathscr F_\kappa$ are zero. The cited theorem bounds the uncentered
$\psi(x)$; it states no estimate for the centered difference
$\psi(x)-x$ at this frequency. Its nonzero-frequency savings cannot be
substituted for the original signed tail merely by changing coordinates.

## The same-source transport obligation

Use the [existing jointly selected source class](../Arith/caveney2012sacaga.md#restrict-the-unpaid-signed-estimate-to-this-joint-source-class),
with its same actual integer $N$, clock $A=\log N$, own CA price,
proper GA1, regularity and comparison against every integer $m\ge N$.
That source application is not Lean certified. Its fixed excess exponent
$0<\eta<1/2$ is independent of the parameter $\kappa$ in (SV3).

If (SV1) is used as the recovery supplier, write its entire right-hand side as

$$
\mathcal C(n)=\bigl(h*\log-\mathbf 1*h*\Lambda_{\le V}
 +[(\mathbf 1*\theta)(\mathbf 1*\lambda)]*\Lambda_{>V}
 +\Lambda_{\le V}\bigr)(n).
$$

For any chosen normalized weights, the unpaid quantitative input is a
same-source lower bound of the form

$$
\sqrt A\log A\,
\lim_{Y\to\infty}\int_A^Y
 \left(\sum_{n\le t}\mathcal C(n)-t\right)
 \frac{1+\log t}{t^2\log^2t}\,dt
\ge-B_{\rm new}(A),
\qquad
B_{\rm new}(A)=o\!\left(A^{1/2-\eta}\log A\right).
\tag{SV4}
$$

The weight choice may depend on $N$, but all terms in $\mathcal C$ must
use that same choice. Equation (SV1) provides the exact full
$\Lambda$ recovery in this expression, not an estimate for (SV4).
The subtracted baseline is still $t$ and the outer integration still
starts at the actual $A$. The inner summatory functions retain terms
below $A$ and all prime powers; the finite $\Lambda_{\le V}$ contribution
and every convolution crossing a cutoff remain present. The limit in
(SV4) is taken for the joint centered expression, without asserting
separate convergence of the components.

The original account

$$
-X_N=I_\psi(A)+K_N(A),\qquad
X_N=\log G(N)-\gamma,
$$

keeps its original $K_N(A)$. Neither the norm estimates used for the
type-II sums nor (SV3) supplies a sign or a rate for (SV4) on this
selected class. A future estimate must also justify its connection to
the actual CA competitors of this $N$. The source contributes an exact
alternative recovery mechanism and the existing additive-frequency
expansion; it contributes no new signed Robin margin in this application.

## A classical mean supplier for one fixed mixed response

For a specific permissible weight choice in (SV1), use the same actual
integer source and clock $A=\log N>1$, and put

$$
L=\log A,\qquad r=L/8,\qquad
R=e^r,\quad U=e^{2r},\quad U_1=e^{3r},\quad V=e^{4r},
$$

$$
\rho_z(d)=\mu(d)\log(z/d)\mathbf1_{d\le z},\qquad
\lambda=\rho_R/r,\qquad
\theta'=(\rho_{U_1}-\rho_U)/r,\qquad \theta=\mu-\theta'.
$$

These are logarithmic Barban–Vehov weights. They satisfy the general
identity's normalization; they are not the optimized weights in (2.1).
The source's quantitative exponential-sum theorems are not asserted
for this replacement. For the same LCM transform $h$, define

$$
H_A(y)=\sum_dh(d)\left\lfloor y/d\right\rfloor,\qquad
S_A=\sum_d\frac{h(d)}d,\qquad H_A^-(y)=\max\{-H_A(y),0\}.
$$

The finite support lies in $d\le RU_1=\sqrt A$. Use the bilinear form
$\langle f,g\rangle=\sum_{d,e}f(d)g(e)/[d,e]$, and put
$\mathcal Q(z)=\langle\rho_z,\rho_z\rangle$ and
$\mathcal E(a,b)=\langle\rho_b-\rho_a,\rho_b-\rho_a\rangle$.
The relevant existing supplier is Carneiro–Chirre–Helfgott–Mejía-Cordero,
[*Optimality for the two-parameter quadratic sieve*, arXiv:2005.03162v6](https://arxiv.org/abs/2005.03162v6),
Theorem 1.1, equations (1.7)–(1.8). Its normalized weights are defined
in (1.4)–(1.5). Multiplying the source's $M(1,z;h_0)$ by
$(\log z)^2$ gives $\mathcal Q(z)$; multiplying $M(a,b;h_0)$ by
$(\log(b/a))^2$ gives $\mathcal E(a,b)$. Thus the published expansions
read

$$
\mathcal Q(z)=\log z-\kappa_{\rm BV}
 +O\!\left(e^{-c_0\sqrt{\log z}}\right),
$$

$$
\mathcal E(a,b)=\log(b/a)-2\kappa_{\rm BV}
 +O\!\left(e^{-c_0\sqrt{\log(b/a)}}
           +e^{-c_0\sqrt{\log a}}\right).
$$

Here $\kappa_{\rm BV}$ is the constant in the cited Theorem 1.1,
distinct from the small parameter $\kappa$ in (SV3), and $c_0>0$.
Polarization supplies the parameter correspondence

$$
2r^2S_A=\mathcal Q(U_1)-\mathcal Q(U)
          -\mathcal E(R,U_1)+\mathcal E(R,U).
$$

Both leading terms and both second-order constants cancel. The cited
classical theorem therefore gives the two-sided envelope

$$
|S_A|\ll \frac{e^{-c_1\sqrt L}}{L^2}.
$$

Here $c_1>0$ is fixed.

This application is not a new mean theorem or Lean certification. It
does not determine the sign of $S_A$. Nor does it estimate all finite
negative responses: the exact floor correction remains

$$
H_A(y)=yS_A-\sum_dh(d)\{y/d\},
$$

with the full support retained even when $d>y$.

For the unchanged actual integer $N$, write $a_p=v_p(N)$ and
$\epsilon=1/(A\log A)$. The actual next-layer gains and losses are

$$
\beta_j(p)=\log\frac{1-p^{-(j+1)}}{1-p^{-j}},\qquad
\delta_{N,p,k}=\epsilon\log p-\beta_{a_p+k}(p).
$$

Own-price global CA optimality and decreasing layer gains supply
$0\le\delta_{N,p,k}\le\epsilon\log p$. The local negative-part
candidate asks for an eventual same-source bound

$$
\sup_{A\le x\le2A}
\frac{\sum_{p^k\le x}\delta_{N,p,k}H_A^-(x/p^k)}{\epsilon x}
\le A^{-\eta}.
$$

This candidate remains unpaid. A two-sided estimate for $S_A$, or
positivity of that mean alone, does not supply it. A proof of this
candidate would control only one local conversion defect; the Euler
gain, other recovery convolutions, centered baseline and complete
infinite tail in (SV4) would still need estimates with the same
source and weight choice. No original Robin-budget improvement is
claimed from the classical mean correspondence.

## Fixed-truncation Mellin interface and remaining source coupling

The same source's Theorem 1.2 also applies with the common parameters
$(D_1,D_2)=(1,R^3)$. The two normalized profiles have derivative
supports $(2/3,1)$ and $(0,1/3)$, respectively. Their derivative inner
product is zero, so this theorem supplies a two-sided error rather
than a positive main term for the fixed mixed mean. The following
interface uses the published Mellin kernel in section 2.1,
equation (2.5). The finite-truncation and local-residue computations
are mathematical applications of that kernel; no originality or
Lean certification is asserted.

Write

$$
\mathfrak G(s,w)=\prod_p\left(
1-\frac{p^{-2-s-w}(1-p^{-s})(1-p^{-w})}
{(1-p^{-1-s})(1-p^{-1-w})}\right).
$$

This is the source's Euler factor in equivalent notation, with

$$
\sum_{d,e\ge1}\frac{\mu(d)\mu(e)}{[d,e]d^s e^w}
=\frac{\zeta(1+s+w)\mathfrak G(s,w)}
       {\zeta(1+s)\zeta(1+w)}
\qquad(\Re s,\Re w>0).
$$

Keeping the actual finite $d$-cutoff, define

$$
P_R(w)=\sum_{d\le R}\frac{\mu(d)\log(R/d)}d
 \prod_{p\mid d}\frac{1-p^{-w}}{1-p^{-1-w}},
\qquad
F_R(w)=\frac{(R^{3w}-R^{2w})P_R(w)}{w^2\zeta(1+w)}.
$$

Summing the $e$-variable by its Euler product and applying Mellin
inversion gives the exact interface

$$
r^2S_A=\frac1{2\pi i}\int_{(c)}F_R(w)\,dw,
\qquad c>0.
\tag{SV5}
$$

Here $P_R(0)=r$ and $F_R(0)=r^2$ by removable continuation; zero is
not an omitted pole. Choose $0<b<1$ and $Y>0$ so that the boundary
of the rectangle with vertical sides $c,-b$ and horizontal sides
$\pm Y$ meets no zero of $\zeta(1+w)$. Let $\Gamma$ run from $c-iY$ to $-b-iY$,
then to $-b+iY$ and $c+iY$. The full finite-height identity is

$$
r^2S_A=
\sum_{\substack{\zeta(\nu)=0\\\Re\nu>1-b,\ |\Im\nu|<Y}}
 \operatorname{Res}_{w=\nu-1}F_R(w)
 +\mathcal E_R,
$$

$$
\mathcal E_R=\frac1{2\pi i}\left[
 \int_\Gamma F_R(w)\,dw
 +\int_{c-i\infty}^{c-iY}F_R(w)\,dw
 +\int_{c+iY}^{c+i\infty}F_R(w)\,dw\right].
$$

Zeros are summed by distinct position; pole orders retain their
multiplicities. The finite Euler factors have possible poles on
$\Re w=-1$, which this rectangle does not cross. In particular,
the auxiliary height $Y$ neither truncates away the remaining
contributions nor replaces the original arithmetic scale
$T=\sqrt A\log A$. For

$$
M_R(c)=\sum_{d\le R}\frac{|\mu(d)|\log(R/d)}d
 \prod_{p\mid d}\frac{1+p^{-c}}{1-p^{-1-c}},
$$

the two right-line tails obey

$$
\int_{|t|>Y}|F_R(c+it)|\,dt
\le\frac{2(R^{3c}+R^{2c})\zeta(1+c)M_R(c)}Y.
$$

No required fixed-power bound for $\mathcal E_R$ follows from this
identity or its displayed tail estimate.

For a fixed zero $\rho=\beta+i\tau$ with $\beta>1/2$ and $\tau>0$,
put $\alpha=\rho-1$ and $\delta=1-\beta\in(0,1/2)$. In a fixed
sufficiently small neighborhood of $\alpha$, the truncated factor
has the local expansion

$$
P_R(w)=R^{-w}\frac{\mathfrak G(-w,w)}{w^2\zeta(1-w)}
       +O_\rho(R^{\delta/2}).
\tag{SV6}
$$

Its contour derivation starts from

$$
P_R(w)=\frac1{2\pi i}\int_{(a)}
 \frac{R^s}{s^2}\frac{\zeta(1+s+w)}{\zeta(1+s)}
 \mathfrak G(s,w)\,ds,\qquad a>\delta,
$$

with the neighborhood chosen small enough for initial absolute
convergence. Move this line to $\Re s=\delta/2>0$. The only crossed
pole is $s=-w$. On the new line, $\zeta(1+s)$ has real-part parameter
greater than one, and $\Re w>-1/2$ ensures locally uniform absolute
convergence of this Euler product. The usual vertical growth bound
for $\zeta(1+s+w)$ together with $s^{-2}$ gives the stated error.
This local argument does not extend the source's narrower uniform
region by assertion. Uniformity on the neighborhood also controls
each fixed derivative of the error by Cauchy's estimate.

The coefficient in (SV6) is nonzero at $w=\alpha$. Indeed,

$$
\mathfrak G(-w,w)=\prod_p
 \frac{(p-1)(p+1-p^w-p^{-w})}
 {(p^{1+w}-1)(p^{1-w}-1)}.
$$

For $|\Re w|<1$ this product is locally absolutely convergent. Its
denominators are nonzero. If its numerator vanished and $z=p^w$,
then $z+z^{-1}=p+1$, whereas
$p^{-1}<|z|<p$ implies
$|z+z^{-1}|\le |z|+|z|^{-1}<p+1$. Thus every factor is nonzero.
Also $\zeta(1-\alpha)=\zeta(2-\rho)\ne0$ since its real-part
parameter exceeds one. The first term at $\alpha$ has size a
nonzero constant times $R^\delta$, so
$P_R(\rho-1)\ne0$ for all sufficiently large $R$.

Let $m\ge1$ be the multiplicity of $\rho$ and define

$$
C_\rho=
\frac{m\,\mathfrak G(1-\rho,\rho-1)}
 { (\rho-1)^4\zeta(2-\rho)\zeta^{(m)}(\rho)}\ne0.
$$

For this pair alone, the normalized residue contribution is

$$
\begin{aligned}
\mathcal Z_\rho(r)
&=\frac1{r^2}\left(
 \operatorname{Res}_{w=\rho-1}F_R(w)
 +\operatorname{Res}_{w=\bar\rho-1}F_R(w)\right)\\
&=-2r^{m-3}R^{-\delta}\Re(C_\rho e^{i\tau r})
 +O_\rho\!\left(r^{m-3}R^{-\delta}
       (r^{-1}+R^{-\delta/2})\right).
\end{aligned}
\tag{SV7}
$$

To obtain the coefficient, insert (SV6) into $F_R$. The main
meromorphic part is
$(R^{2w}-R^w)\mathfrak G(-w,w)/
 (w^4\zeta(1-w)\zeta(1+w))$.
The leading Laurent term of $1/\zeta(1+w)$ at $\alpha$ is
$m!/(\zeta^{(m)}(\rho)(w-\alpha)^m)$.
The $(m-1)$st derivative of $-R^w$ contributes
$-C_\rho r^{m-1}R^\alpha$ before normalization. Lower derivatives,
the $R^{2w}$ term and the error in (SV6) give the displayed local
error. Other zero contributions remain outside that local error.

For a rectangle containing this pair, let $\mathcal B_{\rho,N}$
contain all other residues and $\mathcal E_R$, divided by $r^2$.
Then $S_A=\mathcal Z_\rho(r)+\mathcal B_{\rho,N}$ exactly. If a
same-source estimate
$(S_A)_-\le C_\eta A^{-\eta}/L$ were supplied, (SV7) would require

$$
\begin{aligned}
2\Re(C_\rho e^{i\tau L/8})
\le{}&\frac{\mathcal B_{\rho,N}}
             {r^{m-3}A^{-\delta/8}}
 +K_\rho(r^{-1}+A^{-\delta/16})\\
&+\frac{C_\eta}{8}r^{2-m}A^{-\eta+\delta/8}
\end{aligned}
\tag{SV8}
$$

for a constant $K_\rho$ independent of $N$. When
$\beta>1-8\eta$, the last term tends to zero. Thus an individual
zero package cannot be paid by its decay alone at this scale;
the full other contributions or the actual source phases must be
controlled. Neither an actual negative-phase source subsequence
nor that compensating control is supplied here. Local oscillation
on continuous clocks does not establish a sign change of the full
$S_A$ or a failure on the selected integer family.

The phase in this interface is $\tau L/8$. Identifying it with FIB
composition rotation $C=MJ$ would require an additional intertwining
map preserving these weights and source conditions. This interface
constructs no such map. The CA fixed point, all-integer right-tail
maximality and source excess remain the joint hypotheses of the
original $N$; their implication of (SV8) is the open coupling
obligation. No required same-source one-sided mean bound,
negative-part bound or complete original Robin estimate is obtained
from this interface.
