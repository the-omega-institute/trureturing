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

## A classical higher-prime-power budget with the mean unpaid

Keep the same actual $N$, fixed $\eta$, weights and cutoffs. Write
$\sigma_A=(S_A)_-$ and, for each fixed integer $m\ge2$, define

$$
D_N^{(\ge m)}(x)=
\sum_{\substack{p^k\le x\\k\ge m}}
 \delta_{N,p,k}H_A^-(x/p^k).
$$

The finite-correlation supplier is Chen An,
[*A Generalization of Graham's Estimate on the Barban-Vehov Problem*,
arXiv:2206.10104v1](https://arxiv.org/abs/2206.10104v1), Theorem 1.3.
Its rational-field case, explicitly attributed there to Graham
(1978, p. 84), gives

$$
\mathcal C(w,z;t):=
\sum_{n\le t}\left(\sum_{d\mid n}\rho_w(d)\right)
             \left(\sum_{e\mid n}\rho_z(e)\right)
=t\log w+O(t),\qquad 1\le w<z\le t.
$$

No condition $wz\le t$ is imposed. For $y\ge U_1$, apply this
supplier with $(w,z,t)=(R,U_1,y)$ and $(R,U,y)$. For $U<y<U_1$,
first use the exact truncation relation

$$
\mathcal C(R,U_1;y)
=\mathcal C(R,y;y)+r\log(U_1/y),
$$

then apply the supplier with $(R,y,y)$ and $(R,U,y)$. The resulting
transition term $\log(U_1/y)/r$ in $H_A(y)$ is nonnegative.
For $1\le y\le U$, the divisor sum of $\theta'$ is supported only
at $n=1$, so $H_A(y)=1$ exactly. For $0\le y<1$, $H_A(y)=0$.
Consequently an absolute constant $C>0$ supplies

$$
H_A^-(y)=0\quad(0\le y\le U),\qquad
H_A^-(y)\le Cy/L^2\quad(y>U).
$$

The full-support floor correction supplies the second envelope

$$
H_A^-(y)\le \sigma_Ay+B_A,\qquad
B_A=\frac{(R-1)(U_1-U)}{r^2}
\le\frac{64\sqrt A}{L^2}.
$$

Indeed $\sum_d|h(d)|\le(\sum_d|\lambda(d)|)
(\sum_e|\theta'(e)|)\le B_A$; this bounds the entire fractional-part
sum, including $d>y$. Set

$$
E_A(y)=(H_A^-(y)-\sigma_Ay)_+,\qquad a=C/L^2.
$$

For all $y\ge0$ the two envelopes imply
$E_A(y)\le\min(ay,B_A)$ and
$H_A^-(y)\le\sigma_Ay+E_A(y)$. No sign of $S_A$ is assumed.

Reuse the [existing Dusart prime-power input](../Weil/dusart2010estimates.md#同一-robin-来源的有效素数幂修正):
$\Gamma_2(t)=\psi(t)-\vartheta(t)\ll\sqrt t$ and
$\vartheta(t)<2t$ for $t\ge1$. For every fixed $m\ge2$, classical
prime-power counting therefore gives

$$
\Gamma_m(t):=\sum_{\substack{p^k\le t\\k\ge m}}\log p
=\sum_{k=m}^{\lfloor\log_2t\rfloor}\vartheta(t^{1/k})
\le K_m t^{1/m}.
$$

Here $K_m$ is a fixed constant; the tail after $k=m$ is bounded by
$2\log_2t\,t^{1/(m+1)}=O_m(t^{1/m})$ for $t\ge2^m$, and the
count is zero below $2^m$. This is an application of the classical
counting bound, not a new prime-distribution theorem.

Put $b=B_A/x>0$ and $z=a/b>0$. Enlarging the nonnegative residual
sum to all $p,k\ge m$ and integrating against its counting measure
gives the exact identity

$$
\begin{aligned}
\sum_{p,\,k\ge m}\log p\min(a/p^k,b)
&=b\Gamma_m(z)+a\int_{(z,\infty)}\frac{d\Gamma_m(t)}t\\
&=a\int_z^\infty\frac{\Gamma_m(t)}{t^2}\,dt\\
&\le\frac{mK_m}{m-1}a^{1/m}b^{1-1/m}.
\end{aligned}
$$

The boundary terms cancel because $b=a/z$. The formula includes an
atom at $z$ in the first term, so it also holds when the real
splitting point is a prime power. Since
$0\le\delta_{N,p,k}\le\epsilon\log p$, the uniform application is

$$
\boxed{
\sup_{A\le x\le2A}\frac{D_N^{(\ge m)}(x)}{\epsilon x}
\le\mathfrak c_m\sigma_A
 +C_m\frac{A^{-\gamma_m}}{L^2},\qquad
\gamma_m=\frac{m-1}{2m},\quad
\mathfrak c_m=\sum_p\frac{\log p}{p^{m-1}(p-1)}<\infty.
}
\tag{SV9}
$$

All $k\ge m$ are retained. In particular $m=2$ gives the floor
residual $O(A^{-1/4}/L^2)$. If the separate same-source mean
requirement $\sigma_A=O(A^{-\eta}/L)$ were supplied, this complete
higher-power component would be $o(A^{-\eta})$ for the original
$0<\eta\le1/4$, including the endpoint. That requirement is unpaid;
the existing two-sided mean envelope does not have this fixed-power
rate. For $\eta>1/4$, the $m=2$ upper envelope alone is insufficient,
which does not refute the negative-part candidate.

For any original fixed $0<\eta<1/2$, take
$m_\eta=\lceil(1-2\eta)^{-1}\rceil\ge2$ and define the finite
low-layer residual on that same actual $N$ by

$$
\mathcal R_{N,\eta}=
\sup_{A\le x\le2A}\frac1{\epsilon x}
\sum_{k=2}^{m_\eta-1}\sum_{p^k\le x}
 \delta_{N,p,k}E_A(x/p^k).
$$

An empty sum is zero. Since $E_A\le H_A^-$ and
$\gamma_{m_\eta}\ge\eta$, the same envelopes give

$$
\mathcal R_{N,\eta}
\le\sup_{A\le x\le2A}\frac{D_N^{(\ge2)}(x)}{\epsilon x}
\le\mathcal R_{N,\eta}+\mathfrak c_2\sigma_A
 +C_{m_\eta}\frac{A^{-\gamma_{m_\eta}}}{L^2}.
\tag{SV10}
$$

The last term is unconditionally $o(A^{-\eta})$. Conditional on
the still-unpaid mean requirement, obtaining
$\sup_{A\le x\le2A}D_N^{(\ge2)}(x)/(\epsilon x)=o(A^{-\eta})$
is equivalent to $\mathcal R_{N,\eta}=o(A^{-\eta})$. This stronger
target is sufficient for the higher-power component of the local
candidate, whose original threshold is $A^{-\eta}$. For
$1/4<\eta\le1/3$ this leaves the square layer only; all $k\ge3$
residuals already have the required rate. No exponent is lowered.

The actual CA layer weights do not supply another power saving by
themselves. The logarithmic series gives
$\beta_{j+1}(p)\le p^{-1}\beta_j(p)$, and own-price optimality gives
$\beta_{a_p+1}(p)\le\epsilon\log p$. Thus for all $k\ge2$,

$$
(1-p^{1-k})\epsilon\log p
\le\delta_{N,p,k}\le\epsilon\log p.
$$

In particular, $D_N^{(\ge2)}(x)/(\epsilon x)$ is between one half
and one times $x^{-1}\sum_{p^k\le x,\,k\ge2}\log p\,H_A^-(x/p^k)$.
This comparison gives no lower bound for $H_A^-$ and leaves open
improvement through its sampling on the selected sources.

These bounds are paper-level applications of existing suppliers,
without Lean certification or a claim of original number theory.
The mean requirement, finite low layers when needed, prime layer
$k=1$, other recovery terms and full signed tail in (SV4) remain
unpaid. No complete Robin-budget gain follows from (SV9) or (SV10).

## A signed lowest-frequency band for these actual coefficients

Keep exactly the logarithmic weights, cutoffs and actual integer source
above. The following application uses the [existing classical Mertens
input](../Analytic/ng2004summatorymobius.md#reuse-of-the-unconditional-input),
not a new cancellation theorem. Write

$$
\mathcal W(u)=\frac{u^{3/5}}{(\log u)^{1/5}},\qquad
M(t)=\sum_{n\le t}\mu(n)\ll t e^{-c\mathcal W(\log t)}.
$$

All estimates in this section are for sufficiently large $A$, with fixed
positive constants. For an interval $I\subset(V/2,V]$, the actual LCM
decomposition forces

$$
[d,e]\in I\ \Longrightarrow\ (d,e)=1,\quad [d,e]=de,
\quad d>R/2,\quad e>U_1/2>U.
$$

Indeed $de/[d,e]<2$ and this ratio is the positive integer $(d,e)$.
Consequently

$$
\sum_{\ell\in I}h(\ell)
=\frac1{r^2}\sum_{R/2<d\le R}\mu(d)\log(R/d)
 \sum_{\substack{de\in I,\ e\le U_1\\(e,d)=1}}
 \mu(e)\log(U_1/e).
$$

The coprimality condition can be retained uniformly. The classical
finite convolution identity and a split at $a=\sqrt t$ give

$$
\begin{aligned}
M_d(t)&:=\sum_{\substack{n\le t\\(n,d)=1}}\mu(n)
 =\sum_{\substack{a\le t\\a\mid d^\infty}}M(t/a),\\
|M_d(t)|&\ll
t e^{-c_1\mathcal W(\log t)}\frac d{\varphi(d)}
+t^{3/4}\prod_{p\mid d}(1-p^{-1/2})^{-1}.
\end{aligned}
$$

Here $a\mid d^\infty$ means that every prime factor of $a$ divides $d$.
The first term uses
$\mathcal W((\log t)/2)\asymp\mathcal W(\log t)$; the second is the
usual Rankin bound on the complementary smooth reciprocal sum.
The elementary bounds $d/\varphi(d)\ll\log(2d)$ and
$\prod_{p\mid d}(1-p^{-1/2})^{-1}\ll d^{1/4}$ then yield

$$
M_d(t)\ll U_1e^{-c_2\mathcal W(L)}
\quad(d\le R,\ U_1/2\le t\le U_1).
$$

The polynomial remainder is $O(U_1^{5/6})$ since $U_1=R^3$.
It and the logarithmic factor are absorbed by decreasing $c_2$.
Abel summation against $\log(U_1/e)$ on the inner interval, followed
by $\log(R/d)\le\log2$, therefore gives the uniform application

$$
\left|\sum_{\ell\in I}h(\ell)\right|
\ll \frac V{L^2}e^{-\kappa\mathcal W(L)},
\qquad I\subset(V/2,V],\quad \kappa>0.
\tag{SV11}
$$

To identify its actual finite frequency band, put $b(t)=\{t\}-1/2$,
$c_A=\frac12\sum_\ell h(\ell)$ and
$g_A(y)=F_A(y)-c_A=\sum_\ell h(\ell)b(y/\ell)$. Reuse the classical
Vaaler approximation, as stated in Baker, Banks, Brüdern, Shparlinski
and Weingartner, [*Piatetski-Shapiro sequences*,
arXiv:1203.5884v1](https://arxiv.org/pdf/1203.5884v1), §2, equation
(2.1), PDF p.6, with attribution there to Vaaler (1985). The source
statement was inspected; its underlying proof is not independently
audited here. Use its polynomial $P_J$ and nonnegative majorant $D_J$, with
$|b-P_J|\le D_J$ and $|\widehat P_J(n)|\ll1/|n|$ for $n\ne0$.
At integers the representatives are explicitly
$b=-1/2$, $P_J=0$ and $D_J=1/2$. Define

$$
g_{A,J}(y)=\sum_\ell h(\ell)P_J(y/\ell),\qquad
r_{A,J}(y)=\sum_\ell|h(\ell)|D_J(y/\ell),
$$

$$
b_{A,J}(\xi)=
\sum_{\substack{\ell\le V,\ 1\le|n|\le J\\n/\ell=\xi}}
h(\ell)\widehat P_J(n).
$$

The finite positive frequency band $\mathscr B_+=[1/V,2/V)$ forces
$n=1$ and $V/2<\ell\le V$. Thus its merged coefficients are exactly
$b_{A,J}(1/\ell)=h(\ell)\widehat P_J(1)$, without an infinite
Fourier substitution or a missing harmonic cutoff. Abel summation
using (SV11) gives, for every interval $\mathcal I\subset\mathscr B_+$,
$y\ge0$ and integer $J\ge1$,

$$
\left|\sum_{\xi\in\mathcal I}b_{A,J}(\xi)e^{2\pi i y\xi}\right|
\ll\frac V{L^2}e^{-\kappa\mathcal W(L)}(1+y/V).
\tag{SV12}
$$

In particular the real contribution of this band and its conjugate,

$$
g_{\rm top,J}(y)=2\Re\!\left(
\widehat P_J(1)\sum_{V/2<\ell\le V}h(\ell)e^{2\pi i y/\ell}\right),
$$

has the same bound. Put $g_{\rm rest,J}=g_{A,J}-g_{\rm top,J}$ and
$Z_{\rm rest,J}(y)=c_A+g_{\rm rest,J}(y)-y(S_A)_+$. The exact identity
$E_A(y)=[c_A+g_A(y)-y(S_A)_+]_+$ and the positive part's
$1$-Lipschitz property show where this bound is consumed. For a block
$\mathcal P$ of actual primes, $y_p=x/p^k\le Y$, and
$w_{N,p,k}=\delta_{N,p,k}/\epsilon$, let
$M_{\mathcal P}=\sum_{p\in\mathcal P}w_{N,p,k}$. Then

$$
\begin{aligned}
\frac1x\sum_{p\in\mathcal P}w_{N,p,k}E_A(y_p)
\le{}&\frac1x\sum_{p\in\mathcal P}w_{N,p,k}
 [Z_{\rm rest,J}(y_p)]_+\\
&+C\frac{M_{\mathcal P}}x\frac V{L^2}
 e^{-\kappa\mathcal W(L)}(1+Y/V)
+\frac1x\sum_{p\in\mathcal P}w_{N,p,k}r_{A,J}(y_p).
\end{aligned}
\tag{SV13}
$$

No sign of $S_A$ or replacement of the actual weights is assumed.
For a dyadic block $\mathcal P\subset\{p:P<p\le2P\}$ with
$Y=x/P^k$, the existing $w_{N,p,k}\le\log p$ and
$\vartheta(2P)<4P$ give $M_{\mathcal P}\ll(x/Y)^{1/k}$.
At $Y\asymp V$, fixed $k\ge2$ and $A\le x\le2A$, the displayed
band term is therefore $O_k(A^{-\gamma_k}L^{-2}e^{-\kappa\mathcal W(L)})$,
$\gamma_k=(k-1)/(2k)$. For each remaining layer $k<m_\eta$,
$\eta>\gamma_k$ and $\mathcal W(L)=o(L)$, so this upper bound
alone does not reach $o(A^{-\eta})$. Other bands, the actual positive
part, and the pointwise remainder are still present. This is an
application of existing classical inputs, without Lean certification
or a claim of original number theory; it gives no complete Robin gain.

## A small-truncation boundary for the absolute remainder envelope

Use the classical Fejér-normalized Vaaler majorant

$$
D_J(t)=\frac1{2(J+1)^2}
 \left(\frac{\sin\pi(J+1)t}{\sin\pi t}\right)^2
=\frac1{2(J+1)}\sum_{|n|\le J}
 \left(1-\frac{|n|}{J+1}\right)e^{2\pi i nt},
$$

with continuous value $1/2$ at integers. This is the standard
Vaaler construction, attributed to
[Vaaler (1985)](https://doi.org/10.1090/S0273-0979-1985-15349-2);
the original proof has not been independently inspected. The
approximation statement used above is also supplied by the inspected
Baker et al. equation (2.1). All estimates below retain the actual
coefficients and hold for sufficiently large $A$.

Choose primes $q,s$ in the fixed-ratio ranges

$$
3R/4<q\le7R/8,\qquad 3U_1/4<s\le7U_1/8.
$$

These ranges are disjoint and $V/2<qs<V$. The only permitted
LCM decomposition at $\ell=qs$ is $d=q,e=s$: the preceding
coprimality observation gives $de=qs$, while $s>R$ and $qs>U_1$.
Thus

$$
h(qs)=\frac{\log(R/q)\log(U_1/s)}{r^2}\gg L^{-2},
\qquad
\sum_{V/2<\ell\le V}|h(\ell)|\gg\frac V{L^4}.
\tag{SV14}
$$

The second bound directly applies the [existing unconditional prime
number theorem](../Weil/dusart2010estimates.md#robin-支撑损失所需的渐近输入)
to the two fixed-ratio intervals; it is not a new prime-counting result.
Each pair gives a different product, and their count is
$\gg RU_1/(\log R\log U_1)\asymp V/L^2$.

If $U<y<2U$, $\ell>V/2$ and $J+1\le V/(8U)$, then
$0<(J+1)y/\ell<1/2$. The elementary bounds
$\sin\pi u\ge2u$ for $0\le u\le1/2$ and
$\sin\pi t\le\pi t$ imply $D_J(y/\ell)\ge2/\pi^2$.
Together with (SV14), this gives
$r_{A,J}(y)\gg V/L^4$ throughout $U<y<2U$.

For a fixed integer $k\ge2$, define the full active-sample cost

$$
\mathcal T_{N,k,J}(x)=\frac1x\sum_{p^k<x/U}
 w_{N,p,k}r_{A,J}(x/p^k).
$$

The actual own-price comparison already established above gives
$(1-p^{1-k})\log p\le w_{N,p,k}\le\log p$.
Consequently the primes with $x/(2U)<p^k<x/U$ have weighted
mass $\gg_k(x/U)^{1/k}$, by the same prime number theorem.
Uniformly for $A\le x\le2A$,

$$
\mathcal T_{N,k,J}(x)
\gg_k\frac V{xL^4}\left(\frac xU\right)^{1/k}
\asymp_k\frac{A^{-1/2+3/(4k)}}{L^4},
\qquad J\ge1,\quad J+1\le\frac V{8U}.
\tag{SV15}
$$

For squares this is $A^{-1/8}/L^4$, larger than the already
available $A^{-1/4}/L^2$ residual upper envelope for $E_A$.
This is a lower bound for the absolute approximation envelope,
not for $E_A$ or the signed error.

Both terms of the Fourier upper budget must therefore be retained.
Put $B_1=\sum_\ell|h(\ell)|\le B_A$,
$M_{N,k}(x)=\sum_{p^k<x/U}w_{N,p,k}$ and
$\mathcal S_{N,k,x}(\alpha)=\sum_{p^k<x/U}
w_{N,p,k}e^{2\pi i\alpha x/p^k}$. The Fejér formula gives

$$
\begin{aligned}
\mathcal T_{N,k,J}(x)\le{}&
\frac{B_1M_{N,k}(x)}{2x(J+1)}\\
&+\frac1{x(J+1)}\sum_\ell|h(\ell)|
 \sum_{n=1}^J\left(1-\frac n{J+1}\right)
 |\mathcal S_{N,k,x}(n/\ell)|.
\end{aligned}
\tag{SV16}
$$

At $J+1=\lfloor V/(16U)\rfloor$, the first term is
$O_k(A^{-3/4+3/(4k)}/L^2)$, using
$M_{N,k}(x)\ll_k(x/U)^{1/k}$ and $B_A\ll V/L^2$.
Its ratio to the lower scale in (SV15) is
$O_k(A^{-1/4}L^2)\to0$. Hence the second, oscillatory upper-budget
term in (SV16) is itself at least a fixed positive multiple of
the scale in (SV15) eventually. Paying only the zero-frequency
term cannot pay this absolute envelope.

This excludes only the small-$J$ sufficient condition that asks
the whole absolute envelope to be small. It excludes neither
larger $J$ nor cancellation in the signed error, and gives no
counterexample to the actual-source target or Robin's inequality.
The estimates are attributed paper-level applications, not
Lean-certified conclusions or claims of original number theory.

A weaker joint condition remains possible. Write
$\Delta_J=g_A-g_{A,J}$. The elementary positive-part inequality

$$
[Z+\Delta]_+\le[Z]_+
 +[\Delta_+-(-Z)_+]_+
$$

and the same band removal give

$$
E_A(y)\le[Z_{\rm rest,J}(y)]_+
 +[(\Delta_J(y))_+-(-Z_{\rm rest,J}(y))_+]_+
 +|g_{\rm top,J}(y)|.
$$

Only the positive signed error exceeding the actual negative
margin is charged in this expression. No quantitative joint
bound at the original $\eta$ rate has been supplied for it.
The remaining bands, mean requirement, low prime-power layers,
prime layer $k=1$, recovery terms and complete signed tail (SV4)
remain unpaid; the original source and target are unchanged.

## Exact-integer sample corrections are paid by a classical divisor bound

Keep the actual normalized weights, so $|\lambda(d)|,|\theta'(d)|\le1$.
For a positive integer $m$, the LCM definition gives the jump coefficient

$$
J_A(m):=\sum_{\ell\mid m}h(\ell)
=\left(\sum_{d\mid m}\lambda(d)\right)
 \left(\sum_{e\mid m}\theta'(e)\right),
\qquad |J_A(m)|\le\tau(m)^2.
\tag{SV17}
$$

Here $\tau$ is the ordinary divisor-count function. Put $J_A(y)=0$
for positive noninteger $y$. Use the symmetric sawtooth representative
$b_{\rm sym}(t)=b(t)+\tfrac12\mathbf1_{\mathbb Z}(t)$, with value zero
at integers, and define $g_{{\rm sym},A}(y)=\sum_\ell h(\ell)b_{\rm sym}(y/\ell)$.
For $y>0$, $g_{{\rm sym},A}(y)=g_A(y)+\tfrac12J_A(y)$. For
$E_{{\rm sym},A}(y)=[c_A+g_{{\rm sym},A}(y)-y(S_A)_+]_+$,
the positive part's Lipschitz property gives

$$
|E_A(y)-E_{{\rm sym},A}(y)|\le\tfrac12|J_A(y)|.
\tag{SV18}
$$

The same finite Vaaler polynomial $P_J$ approximates $b_{\rm sym}$
with nonnegative majorant $D_J-\tfrac12\mathbf1_{\mathbb Z}$:
off the integers the original estimate applies; at integers both
$b_{\rm sym}$ and $P_J$ are zero and $D_J=1/2$.
Thus a midpoint Fourier convention can be used only with the explicit
correction (SV18) when returning to the original response.

For every prime-power layer, including $k=1$, the global own-price
comparison gives $0\le w_{N,p,k}\le\log p$. Define its full endpoint cost

$$
C_N(x):=\frac1{2x}\sum_{\substack{p^k\le x\\k\ge1}}
 w_{N,p,k}|J_A(x/p^k)|.
$$

If $x$ is noninteger this cost is zero. If $x=M$ is a positive integer,
only $p^k\mid M$ contribute. Since $\tau(M/p^k)\le\tau(M)$ and
$\sum_{p^k\mid M}\log p=\log M$, (SV17) gives

$$
C_N(M)\le\frac{\tau(M)^2\log M}{2M}.
\tag{SV19}
$$

Directly reuse [Nicolas's divisor-count maximizing
reference](nicolas1971repartition.md#objective-and-arbitrary-integer-decomposition),
printed p.117, equations (6)–(8), with fixed exponent $\nu=1/8$.
Its reference $Q_\nu$ maximizes $\tau(m)m^{-\nu}$ over all positive
integers, and therefore

$$
\tau(m)\le\tau(Q_\nu)Q_\nu^{-\nu}m^\nu,
\qquad
\sup_{A\le x\le2A}C_N(x)
\ll A^{-3/4}\log A=o(A^{-\eta})
\quad(0<\eta<1/2).
\tag{SV20}
$$

The constant is independent of the selected $N$ and $A$; $Q_\nu$ is a
fixed divisor-count reference, distinct from the actual CA integer $N$
and its varying price $\epsilon$. This pays the exact-integer
representative correction for all layers in the original local sampling
budget. It is a classical application, not a new divisor estimate or a
Lean-certified result. It controls neither near-jump errors nor the
signed-error/negative-margin coupling, mean, low-layer residuals, general
prime-layer cost, recovery terms or complete signed Robin tail.

## A common large truncation pays the higher-power approximation error

Keep the original sawtooth representative and actual coefficients. Put
$M_J=J+1$ and retain every layer in

$$
\mathcal T^{(\ge2)}_{N,J}(x)
=\frac1x\sum_{\substack{p,\ k\ge2\\p^k<x/U}}
 w_{N,p,k}\sum_{\ell\le V}|h(\ell)|D_J(x/(p^k\ell)).
$$

For each fixed auxiliary $0<\nu<1$, the existing Nicolas reference at
exponent $\nu/4$ gives $\tau(n)^2\log n\ll_\nu n^\nu$.
The actual weights and the LCM definition therefore give the aggregate
mass at any positive integer jump $n$:

$$
\begin{aligned}
\sum_{\substack{p,\ k\ge2,\ \ell\\p^k\ell\mid n}}
 w_{N,p,k}|h(\ell)|
&\le\tau(n)^2
 \sum_{\substack{p,\ k\ge2\\p^k\mid n}}\log p\\
&\le\tau(n)^2\log n\ll_\nu n^\nu.
\end{aligned}
\tag{SV21}
$$

Indeed $\sum_{\ell\mid n}|h(\ell)|\le\tau(n)^2$ follows by taking
absolute values before the LCM sum, using $|\lambda|,|\theta'|\le1$.
The divisor-growth input is reused, rather than reproved.

The Fejér formula gives
$D_J(t)\le\min(1/2,(8M_J^2\|t\|^2)^{-1})$, with its original value
$1/2$ at integers. For $q=p^k\ell\le2x$, assign the summand to
$n=q\lfloor x/q+1/2\rfloor$. Then $1\le n\le2x$, $q\mid n$ and
$\|x/q\|=|x-n|/q$. Consequently

$$
D_J(x/q)\le\tfrac12
 \min\left(1,\frac{(x/M_J)^2}{|x-n|^2}\right).
\tag{SV22}
$$

At $x=n$ the minimum means one. For every real $x$ and $a>0$,
$\sum_{n\in\mathbb Z}\min(1,a^2/|x-n|^2)\ll1+a$: retain the
nearest integers, count those within distance $a$, and sum the
square-reciprocal tail. Grouping (SV22) by $n$ and using (SV21) thus
bounds all $q\le2x$ contributions, uniformly for $A\le x\le2A$, by
$O_\nu(A^\nu(A^{-1}+M_J^{-1}))$.

For $q>2x$, use $D_J(x/q)\le q^2/(8M_J^2x^2)$. No part of the
support $\ell>x/p^k$ is discarded. The existing
$\Gamma_2(z)\ll\sqrt z$ and $B_1\le B_A\ll V/L^2$ give

$$
\begin{aligned}
\mathcal T_{q>2x}
&\le\frac{B_AV^2}{8M_J^2x^3}
 \left(\frac xU\right)^2\Gamma_2(x/U)\\
&\ll\frac{A^{3/8}}{M_J^2L^2}.
\end{aligned}
\tag{SV23}
$$

Together these bounds yield the actual, all-layer sampling estimate

$$
\sup_{A\le x\le2A}\mathcal T^{(\ge2)}_{N,J}(x)
\ll_\nu A^\nu(A^{-1}+M_J^{-1})
 +\frac{A^{3/8}}{M_J^2L^2}.
\tag{SV24}
$$

Choose the same $J=\lceil V\rceil$ for every sample and layer. With
$\nu=(1/2-\eta)/2$, the original fixed $0<\eta<1/2$ is unchanged and

$$
\sup_{A\le x\le2A}\mathcal T^{(\ge2)}_{N,J}(x)
\ll_\nu A^{-1/2+\nu}+A^{-5/8}L^{-2}
=o(A^{-\eta}/L).
\tag{SV25}
$$

This estimates the full real-variable envelope directly at a larger
$J$. It leaves (SV15) intact and does not bound the two Fourier
upper-budget terms in (SV16) separately.

To return to the original response, retain all frequency bands jointly:
$Z_{{\rm all},J}(y)=c_A+g_{A,J}(y)-y(S_A)_+$.
Then $|E_A(y)-[Z_{{\rm all},J}(y)]_+|\le r_{A,J}(y)$.
Let $\mathcal R^{\rm poly}_{N,\eta,J}$ be the residual (SV10) with
$E_A$ replaced by $[Z_{{\rm all},J}]_+$, restricted to the same active
samples $p^k<x/U$ and $2\le k<m_\eta$. Since $E_A(y)=0$ for $y\le U$,
(SV25) and the Lipschitz property give

$$
|\mathcal R_{N,\eta}-\mathcal R^{\rm poly}_{N,\eta,J}|
=o(A^{-\eta}/L),\qquad J=\lceil V\rceil.
\tag{SV26}
$$

Likewise the positive signed error exceeding the negative margin is
bounded by $r_{A,J}$, so its higher-power sampled cost is paid by
(SV25). The remaining polynomial positive part is not bounded by
this argument. The constants, drift and lowest frequency band must
still be estimated jointly. This is an application of existing
Fejér, divisor-growth and prime-power inputs, without a claim of
original number theory or Lean certification. The mean, general
prime layer, recovery terms and complete signed Robin tail remain open.

## A classical high-harmonic supplier on critical rectangular blocks

Directly reuse [Liu–Wu–Yang, Proposition 3.1, equation
(3.2)](liuwuyang2021variant.md), retaining all four terms of that
published estimate. Write $e(t)=e^{2\pi it}$ and, for an actual rectangle
$P<p\le2P$, $D<\ell\le2D$, $H<j\le2H$, put $Y=x/P^k$ and

$$
B_{D,H,J}(y)=\sum_{D<\ell\le2D}h(\ell)
 \sum_{\substack{H<j\le2H\\j\le J}}
 \widehat P_J(j)e(jy/\ell).
$$

Here $P,D,H\ge1$, $k\ge2$ is fixed, $A\le x\le2A$ and
$H\le J=\lceil V\rceil$. Set the source parameters to

$$
(\alpha,\beta,\gamma,\delta)=(1,k,1,0),\qquad
(M_{\rm src},N_{\rm src},X_{\rm src})=(P,D,HY/D).
$$

Its remaining hypothesis is $H\le P^{k-1}D$. The actual prime and
active-sample indicators, $w_{N,p,k}$, $H\widehat P_J(j)$ and any
test values $|u_p|\le1$ enter $a_{j,p}$; $h(\ell)$ enters $b_\ell$.
Normalize the coefficients using $w\le\log(2P)$,
$|\widehat P_J(j)|\ll H^{-1}$ and
$|h(\ell)|\le\tau(\ell)^2$. The existing Nicolas input absorbs this
divisor factor into an arbitrarily small fixed power of $A$.
The source theorem is uniform in these coefficients, so choosing
$u_p$ as the complex sign of the actual block sum gives

$$
\begin{aligned}
\frac1x\sum_{\substack{P<p\le2P\\p^k<x/U}}
 w_{N,p,k}|B_{D,H,J}(x/p^k)|
\ll_{k,\nu}\frac{A^\nu}{x}\bigg[&
 \sqrt{xP^{1-k}}+D\sqrt{P/H}\\
 &+P\sqrt D+PD\sqrt{D/(HY)}\bigg].
\end{aligned}
\tag{SV27}
$$

The source $X_{\rm src}^{\varepsilon}$, coefficient logarithms and
dyadic summation losses are absorbed by choosing smaller auxiliary
exponents before the prescribed $\nu>0$. No independence of the
test values from the actual coefficients is required. The same bound
handles conjugate frequencies and actual positive-part indicators.

On $D\asymp Y\asymp V$, $P\asymp A^{1/(2k)}$, (SV27) reduces to

$$
\ll_{k,\nu} A^\nu
 \left(A^{-3/4+1/(2k)}+A^{-\gamma_k}H^{-1/2}\right),
\qquad \gamma_k=\frac{k-1}{2k}.
\tag{SV28}
$$

For an unpaid fixed layer $2\le k<m_\eta$, choose a fixed $d>0$
small enough that $2(\eta-\gamma_k)+d<1/2$, and set
$H_0=A^{2(\eta-\gamma_k)+d}$. Taking
$0<\nu<\min(d/2,3/4-1/(2k)-\eta)$ pays the dyadic blocks
$H\ge H_0$ in this critical region to $o(A^{-\eta})$.
The source condition holds throughout these blocks for large $A$,
since $J\asymp A^{1/2}$ and $P^{k-1}D\asymp A^{1-1/(2k)}$.

This supplies only the indicated high harmonics on critical
rectangles. Low harmonics, other rectangles, the joint drifted
positive part and the complete original budget remain unestimated.
It is a direct application of an existing exponential-sum theorem,
not a new prime-distribution result or an identification of its
frequencies with FIB composition rotations.

## The same approximation budget includes the prime layer at a larger cutoff

Let $\mathcal T^{(\ge1)}_{N,J}$ be the full-support sampling envelope
defined above with $k\ge1$, retaining the active condition $p^k<x/U$.
The grouping in (SV21)–(SV22) applies unchanged: with all layers,
$\sum_{p^k\mid n,\,k\ge1}\log p=\log n$, so the mass at each positive
integer jump is still at most $\tau(n)^2\log n\ll_\nu n^\nu$.
For $q>2x$, directly reuse the existing classical bound $\psi(z)\ll z$
in place of $\Gamma_2(z)\ll\sqrt z$ in (SV23). This bounds the full far
support by
$B_AV^2/(M_J^2U^3)\ll A^{3/4}/(M_J^2L^2)$.
Consequently

$$
\begin{aligned}
\sup_{A\le x\le2A}\mathcal T^{(\ge1)}_{N,J}(x)
&\ll_\nu A^\nu(A^{-1}+M_J^{-1})
 +\frac{A^{3/4}}{M_J^2L^2},\\
\sup_{A\le x\le2A}\mathcal T^{(\ge1)}_{N,J_1}(x)
&\ll_\nu A^{-1+\nu}+A^{-5/4}L^{-2}
 =o(A^{-\eta}/L),\\
J_1&=\lceil A\rceil,\qquad \nu=(1-\eta)/2,
\qquad 0<\eta<1/2.
\end{aligned}
\tag{SV29}
$$

This is a corollary of the same classical suppliers and jump grouping,
with the original coefficients, representative, source and $\eta$.
It pays the prime-layer approximation error as well. The prime-layer
polynomial positive part is not bounded by (SV29).

For the higher-power residual, keep $J_0=\lceil V\rceil$. At each
actual sample the two polynomial positive parts differ by at most
$r_{A,J_0}+r_{A,J_1}$. Summing over the same active samples and using
(SV25) and (SV29) gives
$|\mathcal R^{\rm poly}_{N,\eta,J_1}
-\mathcal R^{\rm poly}_{N,\eta,J_0}|=o(A^{-\eta}/L)$.
Thus the existing $J_0$ high-harmonic supplier remains usable for this
residual. No application of Liu–Wu–Yang to the extra $J_1$ harmonics is
asserted. The mean, joint polynomial positive parts, other recovery terms
and complete signed Robin tail remain unpaid. This application has no
Lean certification and makes no claim of original number theory.

## Exact local-support recombination pays high harmonics on all rectangles

Keep the original actual source, fixed $\eta$, integer representative and
full mean $\sigma_A=(S_A)_-$. The finite floor response gives
$E_A(y)=[-H_A(y)-\sigma_Ay]_+$. Put

$$
c_A(y)=\tfrac12\sum_{\ell\le y}h(\ell),\qquad
s_A(y)=\sum_{\ell\le y}\frac{h(\ell)}\ell,\qquad
g_{{\rm loc},J}(y)=\sum_{\ell\le y}h(\ell)P_J(y/\ell),
$$

where $h$ still has its original support $\ell\le V$. Then

$$
\begin{aligned}
Z_{{\rm loc},J}(y)
&=c_A(y)+g_{{\rm loc},J}(y)-y(s_A(y)+\sigma_A),\\
|E_A(y)-[Z_{{\rm loc},J}(y)]_+|
&\le\sum_{\ell\le y}|h(\ell)|D_J(y/\ell)
\le r_{A,J}(y).
\end{aligned}
\tag{SV30}
$$

This is exact recombination of the original floor sum: its terms with
$\ell>y$ are zero. Their fractional-part contributions in the earlier
full-support expression are combined with its full linear term, rather
than discarded. The full $\sigma_A$ remains in (SV30); it is not replaced
by the negative part of $s_A(y)$. The common $J_0=\lceil V\rceil$
approximation cost is already paid by (SV25).

Apply the existing four-term supplier (SV27) on dyadic blocks, now keeping
$\ell\le y_p=x/p^k$ inside each block. This moving prefix can be handled
by standard finite Fourier completion. For an integer dyadic $D\ge1$,
write $Q=2D$ and $b_p=\max(0,\min(D,\lfloor y_p\rfloor-D))$. On
$v=\ell-D\in\{1,\ldots,D\}$ the exact identity is

$$
\begin{aligned}
\mathbf1_{v\le b_p}
&=\sum_{r=0}^{Q-1}\beta_r(p)e(rv/Q),\qquad
\beta_r(p)=\frac1Q\sum_{u=1}^{b_p}e(-ru/Q),\\
|\beta_r(p)|&\le\frac{C}{1+\min(r,Q-r)},\qquad
\sum_{r=0}^{Q-1}\frac{C}{1+\min(r,Q-r)}\ll\log(2D).
\end{aligned}
\tag{SV31}
$$

Finite Fourier orthogonality supplies the identity and the finite
geometric-sum bound supplies the displayed majorants. For each $r$,
put the normalized $\beta_r(p)$ in the allowed coefficient $a_{j,p}$,
together with the actual test sign, own-price weight and sample flags;
put $h(\ell)e(r(\ell-D)/Q)$ in $b_\ell$. Thus (SV27) still applies with
only a logarithmic completion cost. No unestimated separation of a joint
$p,\ell$ indicator is assumed.

For a nonempty block, $D\le\min(V,Y)$ with $Y=x/P^k$. Under the original
source condition $H\le P^{k-1}D$, the four terms in (SV27) give the uniform
block cost

$$
\ll_{k,\nu}A^\nu
 \left(A^{-1/2}+A^{-\gamma_k}H^{-1/2}\right),
\qquad \gamma_k=\frac{k-1}{2k}.
\tag{SV32}
$$

Indeed the first term is at most $A^{-1/2}$. Splitting at $Y=V$ gives
$P\sqrt D/x\ll A^{-3/4+1/(2k)}\le A^{-1/2}$,
$D\sqrt P/x\ll A^{-1/2+1/(4k)}\le A^{-\gamma_k}$ and
$PD\sqrt{D/Y}/x\ll A^{-\gamma_k}$. These are bounds for the same
rectangle. If the source condition fails, use direct absolute values:
the cost is $\ll_{k,\nu}A^\nu PD/x$, and
$PD<HP^{2-k}\le J_0$ for $k\ge2$. This again costs
$O_{k,\nu}(A^{-1/2+\nu})$ without using the source theorem outside its
range. The term $\ell=1$, outside the dyadic denominator blocks, has
total cost $O_{k,\nu}(A^{-1+3/(4k)+\nu})$ from $p^k<x/U$ and the
harmonic coefficient bound, and fits the same budget.

For $1\le H_0\le J_0$, define the complete local high-frequency part

$$
\mathcal G_{k,>H_0}(y)
=\sum_{\ell\le y}h(\ell)
 \sum_{H_0<|j|\le J_0}\widehat P_{J_0}(j)e(jy/\ell).
$$

Dyadic decomposition includes the block crossing $H_0$: take
$H\ge H_0/2$ and retain both flags $j>H_0$ and $j\le J_0$ in
$a_{j,p}$. Summing (SV32), its condition-failure bound and the
$\ell=1$ contribution, and including conjugate frequencies, yields

$$
\sup_{A\le x\le2A}\frac1x
 \sum_{p^k<x/U}w_{N,p,k}
 |\mathcal G_{k,>H_0}(x/p^k)|
\ll_{k,\nu} A^\nu
 \left(A^{-1/2}+A^{-\gamma_k}H_0^{-1/2}\right).
\tag{SV33}
$$

Here $k\ge2$ is fixed. Divisor normalization, completion and all dyadic
losses are absorbed by choosing smaller auxiliary exponents before the
prescribed $\nu>0$. The bound is uniform in the same actual $x$ and
sample-dependent test signs; no independent source phases are chosen.

For each original unpaid layer $2\le k<m_\eta$, take a common fixed
$0<d<1-2\eta$ and set
$H_{0,k}=A^{2(\eta-\gamma_k)+d}$. Its exponent lies between zero and
$1/2$. Choose $0<\nu<\min(d/2,1/2-\eta)$; then (SV33) is
$o(A^{-\eta})$ for every such layer. Define

$$
g_{{\rm loc},k}^{\rm low}(y)
=\sum_{\ell\le y}h(\ell)
 \sum_{1\le|j|\le H_{0,k}}\widehat P_{J_0}(j)e(jy/\ell),
$$

and let $\mathcal R^{\rm low}_{N,\eta}$ be (SV10)'s residual over the
same active samples, replacing $E_A(y_p)$ in each layer $k$ by
$[c_A(y_p)+g_{{\rm loc},k}^{\rm low}(y_p)
-y_p(s_A(y_p)+\sigma_A)]_+$. Equation (SV30), the positive part's
Lipschitz property and (SV33) give

$$
|\mathcal R_{N,\eta}-\mathcal R^{\rm low}_{N,\eta}|
=o(A^{-\eta}).
\tag{SV34}
$$

Empty layer sums remain zero. This applies the same published supplier
to all rectangles after exact local-support recombination, extending
the critical-rectangle scope of (SV28). The low frequencies, moving
constant and drift remain jointly inside the same positive part; they
have no bound here at the required rate. The separate full-mean
requirement, prime layer, other recovery terms and complete signed
Robin tail remain unpaid. This is an attributed application of
classical inputs without Lean certification, original-number-theory
priority or an identification with FIB composition rotation.

## Actual deep-layer weights differ only below the residual target scale

Retain the same selected $N$, its actual $A=\log N$, original $\eta$,
$E_A$, active samples and finite layers in $\mathcal R_{N,\eta}$. Let
$\widetilde{\mathcal R}_{A,\eta}$ be that same supremum with only
$w_{N,p,k}$ replaced by $\log p$. The existing own-price layer comparison
gives $0\le\log p-w_{N,p,k}\le p^{1-k}\log p$ for $k\ge2$.
Using the original envelope $E_A\le B_A$, the difference between the
two nonnegative sums at each $x\in[A,2A]$ is at most

$$
\frac{B_A}{x}\left(
 \sum_{p\le\sqrt{x/U}}\frac{\log p}{p}
 +\sum_p\sum_{k\ge3}\frac{\log p}{p^{k-1}}\right)
=\frac{B_A}{x}\left(
 \sum_{p\le\sqrt{x/U}}\frac{\log p}{p}+\mathfrak c_2\right).
$$

The existing $\vartheta(t)<2t$ input and Abel summation give
$\sum_{p\le z}(\log p)/p\ll\log(2z)$; $\mathfrak c_2<\infty$
is already defined in (SV9). Since $B_A\ll\sqrt A/L^2$, the bound
is uniformly $O(A^{-1/2}/L)$. Pointwise order and the supremum
inequality therefore give, without requiring either supremum to be
attained,

$$
0\le\widetilde{\mathcal R}_{A,\eta}-\mathcal R_{N,\eta}
\ll\frac{A^{-1/2}}L=o(A^{-\eta}/L),\qquad 0<\eta<1/2.
\tag{SV35}
$$

Thus the original local requirement
$\mathcal R_{N,\eta}=o(A^{-\eta})$ is equivalent to the same requirement
for $\widetilde{\mathcal R}_{A,\eta}$ along the same selected sources.
The actual clock has not been replaced by an arbitrary continuous one.
This application first uses the envelope for $E_A$; it does not assert
that an arbitrary polynomial positive part is bounded by $B_A$.
Transport to a polynomial residual requires the already paid
approximation comparison (SV26).

The depth-dependent lowering of these weights changes this residual
only below its target scale. This leaves open compensation from the
actual selected clock, the joint low response and other terms of the
complete recovery identity. It provides neither the separate mean
bound nor a complete signed Robin estimate, and has no Lean
certification or claim of original number theory.

## Rectangle-dependent cutoffs also pay some of the lowest harmonics

The four-term supplier retains more information than the uniform
critical cutoff in (SV34). For the same local-support rectangle, put

$$
Q_k(P,D)=\frac{D\sqrt P}{A}
 +\frac{P^{1+k/2}D^{3/2}}{A^{3/2}},\qquad
t_k(P,D)=A^{2\eta+d}Q_k(P,D)^2,
\tag{SV36}
$$

where $d$ and the auxiliary exponents obey the choices in (SV34).
Since $A\le x\le2A$, (SV27) with the exact prefix completion (SV31)
gives the block cost
$\ll_{k,\nu}A^\nu(A^{-1/2}+Q_k(P,D)H^{-1/2})$ under its size
condition. The two terms of $Q_k$ are precisely the second and fourth
terms of that supplier, before maximizing over rectangles.

Remove from the existing low part only the frequencies
$t_k(P,D)<|j|\le H_{0,k}$. If $t_k\ge1$, include the crossing
dyadic block $H\ge t_k/2$ and both exact frequency flags. If $t_k<1$,
all positive frequencies in that rectangle are removed and $H\ge1$.
In either case $Q_k/\sqrt H\ll A^{-\eta-d/2}$ on the removed blocks.
The flags are allowed in $a_{j,p}$ for each fixed $P,D,H$.
When the source size condition fails, the already paid direct bound
from (SV32) applies instead. Finite dyadic summation, with the same
small-exponent slack as before, costs $o(A^{-\eta})$ uniformly in $x$.

This deletion includes $j=1$ when $t_k<1$. To handle that singleton
within the source's convention $H<h\le2H$, take source $H=1$, keep
only $h=2$ in $a_{h,p}$, and set
$X_{\rm src}=x/(2P^kD)$. The phase is then exactly $x/(p^k\ell)$,
the condition $1\le P^{k-1}D$ holds, and the four cost terms change
only by fixed factors. Negative frequencies are conjugates. The entire
$\ell=1$ harmonic contribution is separately paid by the absolute
bound already used in (SV32), also when its lowest frequencies are
included.

Let $P(p)$ be the dyadic scale satisfying $P(p)<p\le2P(p)$ for the
actual prime $p$. Define the remaining response, depending on $p$ and $x$, by

$$
\begin{aligned}
g_{{\rm ad},k}(p;x)
={}&\sum_{\substack{D\ \mathrm{dyadic}\\D\le V}}
 \sum_{\substack{D<\ell\le2D\\\ell\le\min(V,y_p)}}h(\ell)
 \sum_{1\le|j|\le\min(J_0,H_{0,k},t_k(P(p),D))}
 \widehat P_{J_0}(j)e(jy_p/\ell),\qquad y_p=x/p^k.
\end{aligned}
$$

The dyadic denominator sum begins at $D=1$; it excludes the separately
paid $\ell=1$. In the original residual, replace $E_A(y_p)$ by
$[c_A(y_p)+g_{{\rm ad},k}(p;x)-y_p(s_A(y_p)+\sigma_A)]_+$ and call
the resulting supremum $\mathcal R^{\rm ad}_{N,\eta}$. The constants,
full mean, drift, active samples and own-price weights are unchanged.
The positive-part Lipschitz inequality and (SV34) therefore give

$$
|\mathcal R_{N,\eta}-\mathcal R^{\rm ad}_{N,\eta}|
=o(A^{-\eta}).
\tag{SV37}
$$

For fixed scales $P\asymp A^u$, $D\asymp A^v$, an entire rectangle,
including its first harmonic, is paid if

$$
u+2v<2-2\eta-d,\qquad
(k+2)u+3v<3-2\eta-d.
$$

These sufficient conditions describe a region, rather than a single
example; they are not necessary conditions for a useful estimate.
The retained rectangles and their joint constant/drift positive part
still have no bound here at the required rate. This is another
parameter-specific application of the same published four-term
supplier, without a new exponential-sum theorem, Lean certification
or complete signed Robin gain.

## A published moment obstruction applies to the original linear factor

The remaining joint estimate cannot be supplied by assuming that linear
smoothing automatically gives uniformly bounded high moments of each
factor. Granville–Koukoulopoulos–Maynard, [*Sieve weights and their
smoothings*, arXiv:1606.06781v4](https://arxiv.org/abs/1606.06781v4),
definition (1.9) and Theorem 1.3, directly apply to the original
$\lambda(d)=\mu(d)(1-\log d/\log R)_+$. With the source's moment
index $k=3$ and smoothing exponent $1$, their exponent is
$\binom63-6(1+1)=8$. Thus

$$
\mathcal M_6(R):=
\sum_{d_1,\ldots,d_6\le R}
 \frac{\lambda(d_1)\cdots\lambda(d_6)}{[d_1,\ldots,d_6]}
=c_{3,1}(\log R)^8+O((\log R)^7),\qquad c_{3,1}>0.
\tag{SV38}
$$

At the unchanged actual clock, $R=A^{1/8}$. Expanding the sixth power
of $\Lambda_R(n)=\sum_{d\mid n}\lambda(d)$ gives

$$
\frac1A\sum_{n\le A}\Lambda_R(n)^6
=\mathcal M_6(R)+O\!\left(\frac{R^6}{A}\right)
=c_{3,1}(\log R)^8+O((\log R)^7+A^{-1/4}).
$$

The expansion error uses only $|\lambda(d)|\le1$ for the actual
$d\ge1$ and $|\lfloor A/[d_1,\ldots,d_6]\rfloor
-A/[d_1,\ldots,d_6]|\le1$. This is an application of the published
moment theorem, not a new high-moment result or Lean certification.

It rules out a uniformly bounded sixth moment for this single factor
under ordinary integer averaging. It does not rule out compensation in
the mixed LCM response $h$, in its drifted positive part, or under the
actual reciprocal-prime-power sampling: those are different quantities
and measures. In particular, (SV38) is neither a lower bound for the
unpaid residual nor a counterexample to its required estimate. Replacing
the linear weight by a more smoothed one would change the recovery
contract and does not inherit the estimates for the current $h$.

## The original response envelopes localize the unpaid prime samples

Choose a fixed $0<\omega<1/2-\eta$ and retain only the original
finite unpaid layers $2\le k<m_\eta$. Put

$$
P_-=A^{1/2-\eta-\omega},\qquad
P_{+,k}=A^{(\eta+\omega)/(k-1)}.
$$

Let $\mathcal R^{\rm win}_{N,\eta}$ be the original $E_A$ residual
with the additional sample condition $P_-<p\le P_{+,k}$, intersected
with the same active condition $p^k<x/U$. Apply the envelopes to
$E_A$, before any polynomial replacement. At each $x\in[A,2A]$, the
discarded small-prime part in a layer is at most

$$
\frac{B_A}{x}\sum_{p\le P_-}\log p
\ll\frac{A^{-1/2}P_-}{L^2}
=\frac{A^{-\eta-\omega}}{L^2}.
$$

For the large-prime part, use $E_A(x/p^k)\le Cx/(p^kL^2)$ and
the existing $\vartheta(t)<2t$ input. Abel summation gives, for $z\ge1$,
$\sum_{p>z}(\log p)/p^k\le 2kz^{1-k}/(k-1)$. Thus this part is
also $\ll_k A^{-\eta-\omega}/L^2$. Enlarging each discarded
nonnegative sum is legitimate, including primes outside the active
range. Finite layer summation and the pointwise order therefore imply

$$
0\le\mathcal R_{N,\eta}-\mathcal R^{\rm win}_{N,\eta}
\ll_{\eta,\omega}\frac{A^{-\eta-\omega}}{L^2},
\tag{SV39}
$$

without requiring an attained supremum. For each unpaid layer
$\gamma_k<\eta$, so
$P_-<A^{1/(2k)}<P_{+,k}$. This is an explicit prime window
containing the critical scale; its exponent width need not be small.
Empty layers and empty intersections still contribute zero.

In this same window, replace the response by the joint adaptive
positive part of (SV36)–(SV37), and denote its residual by
$\mathcal R^{\rm ad,win}_{N,\eta}$. The absolute approximation
errors only shrink on a sample subset, and the window flags are
permitted in the arbitrary $a_{j,p}$ arrays used to delete harmonics.
Consequently the original sampled $L^1$ argument applies to this
subset with the same rate. Together with (SV39), it gives

$$
|\mathcal R_{N,\eta}-\mathcal R^{\rm ad,win}_{N,\eta}|
=o(A^{-\eta}).
\tag{SV40}
$$

This conclusion uses that absolute-error argument, not an inference
from the difference of the two unrestricted suprema in (SV37).
The constants and full drift stay jointly inside each retained positive
part. No envelope for an arbitrary polynomial positive part has been
assumed. The remaining task is now restricted in prime samples as well
as in harmonics and denominators; the separate mean, prime layer,
other recovery terms and complete signed tail still need their original
estimates. Equations (SV39)–(SV40) are a localization application of
the existing envelopes and prime-counting input, without a new
prime-distribution theorem or Lean certification.

## Shared sampling primes can be removed from the periodic sector

Retain the same actual source, original fixed $\eta$, support $V=\sqrt A$,
and full local slope $s_A(y)$ and mean $\sigma_A$. For each sampling prime
$p$, define

$$
F_{A,p}^{\rm cop}(y)
=\sum_{\substack{\ell\le\min(V,y)\\p\nmid\ell}}
 h(\ell)\{y/\ell\},\qquad
E_{A,p}^{\rm cop}(y)
=[F_{A,p}^{\rm cop}(y)-y(s_A(y)+\sigma_A)]_+.
$$

The local floor identity in (SV30) gives the same expression for $E_A$
before the condition $p\nmid\ell$ is inserted. Only its fractional-part
sector is removed. In particular, the original $s_A(y)$ still contains
the terms with $p\mid\ell$, and $\sigma_A$ still uses the full $S_A$.

Directly reuse $|h(\ell)|\le\tau(\ell)^2$, the Nicolas divisor-growth
supplier already used in (SV27), and $0\le\{t\}<1$. For every prescribed
$\nu>0$, they give

$$
|E_A(y)-E_{A,p}^{\rm cop}(y)|
\le\sum_{\substack{\ell\le\min(V,y)\\p\mid\ell}}|h(\ell)|
\ll_\nu A^\nu\frac{\min(V,y)}p.
\tag{SV41}
$$

The count is zero when $p>\min(V,y)$; $\ell=1$ is never removed.
This is an absolute coefficient-counting bound and requires no
independence between the prime and the denominator.

For any fixed $k\ge1$, use the original $0\le w_{N,p,k}\le\log p$
where that weight is defined. The existing $\vartheta(t)<2t$ input and
Abel summation give, with $z=(x/V)^{1/k}\ge1$,

$$
\begin{aligned}
\frac1x\sum_p\log p\,\frac{\min(V,x/p^k)}p
&=\frac Vx\sum_{p\le z}\frac{\log p}p
  +\sum_{p>z}\frac{\log p}{p^{k+1}}\\
&\ll_k\frac Vx\log(2z)+z^{-k}
\ll_k A^{-1/2}\log(2A),\qquad A\le x\le2A.
\end{aligned}
$$

An atom at $p=z$ belongs to the first sum. All summands in this
majorant are nonnegative, so the same bound holds on the original
active samples, their prime window, or any subset. Choosing a smaller
auxiliary divisor exponent first absorbs the logarithm. Thus for every
prescribed $\nu>0$ and fixed $k$,

$$
\sup_{A\le x\le2A}\frac1x
 \sum_{p^k<x/U}w_{N,p,k}
 |E_A(x/p^k)-E_{A,p}^{\rm cop}(x/p^k)|
\ll_{k,\nu} A^{-1/2+\nu}.
\tag{SV42}
$$

For the original finite unpaid layers, choose $0<\nu<1/2-\eta$.
Their total is $o(A^{-\eta})$. The fixed-layer estimate also permits
$k=1$, but it is not an estimate for an unbounded sum of layers or a
bound for the remaining prime-layer response.

The same deletion applies directly to the already retained adaptive
polynomial. Define

$$
c_{A,p}^{\rm cop}(y)
=\tfrac12\sum_{\substack{\ell\le y\\p\nmid\ell}}h(\ell),
$$

and define $g_{{\rm ad},k}^{\rm cop}(p;x)$ by inserting $p\nmid\ell$
in the denominator sum of $g_{{\rm ad},k}(p;x)$, with all its original
frequency cutoffs intact. Since $|\widehat P_{J_0}(j)|\ll1/|j|$, removing
the common-prime terms from the constant and oscillatory sectors costs
at most

$$
C\log(2J_0)
 \sum_{\substack{\ell\le\min(V,y_p)\\p\mid\ell}}|h(\ell)|.
$$

The same sampling calculation pays this extra logarithm. In the
original window, replace the retained adaptive response by

$$
[c_{A,p}^{\rm cop}(y_p)+g_{{\rm ad},k}^{\rm cop}(p;x)
 -y_p(s_A(y_p)+\sigma_A)]_+,
\qquad y_p=x/p^k,
$$

and call its residual $\mathcal R^{\rm ad,win,cop}_{N,\eta}$.
The positive part's Lipschitz bound, the sampled absolute bound above,
and (SV40) give

$$
|\mathcal R_{N,\eta}-\mathcal R^{\rm ad,win,cop}_{N,\eta}|
=o(A^{-\eta}).
\tag{SV43}
$$

The supremum need not be attained. No coprimality indicator is assumed
to factor into the independent coefficient arrays of (SV27): this
comparison deletes the common-prime sector by absolute counting after
the existing harmonic comparisons. Neither $E_{A,p}^{\rm cop}$ nor an
arbitrary new polynomial positive part is asserted to inherit the
original $E_A$ envelopes or its vanishing below $U$. The original active
flags and the full local slope and mean remain explicit.

This is an application of existing divisor-growth and prime-counting
inputs to the original response, not a new coprime exponential-sum
theorem, original-number-theory claim, or Lean certification. It removes
the shared sampling prime from the retained periodic and constant
sectors. The coprime low response, its joint full drift, the separate
mean estimate, prime layer, other recovery terms and complete signed
Robin tail still have no bound here at the original target rate.

## The actual response has a quadratic bound just above its cutoff

Keep the original weights, actual source and fixed exponent. Write

$$
a_R(n)=\sum_{d\mid n}\lambda(d),\qquad
b_A(n)=\sum_{e\mid n}\theta'(e).
$$

The defining finite LCM sum gives
$H_A(y)=\sum_{n\le y}a_R(n)b_A(n)$. For $n\le U$,
$b_A(n)=\mathbf1_{n=1}$. If
$U<n\le U(1+\delta)<\min(2U,U_1)$, every proper divisor of $n$
is at most $U$. Only the divisor $e=n$ can differ from the untruncated
Möbius response, and

$$
b_A(n)=\theta'(n)-\mu(n)
=-\frac{\mu(n)}r\log(n/U).
$$

Consequently, uniformly for real $U<y\le U(1+\delta)$,

$$
H_A(y)=1-\frac1r\sum_{U<n\le y}
 \mu(n)a_R(n)\log(n/U).
\tag{SV44}
$$

There is no rounding of the observation endpoint. For sufficiently
large $A$, every $0<\delta\le1/2$ satisfies the displayed cutoff
conditions. The existing absolute weight bounds give

$$
\begin{aligned}
\sum_{U<n\le U(1+\delta)}|a_R(n)|
&\le\sum_{d\le R}|\lambda(d)|
 \left(\left\lfloor\frac{U(1+\delta)}d\right\rfloor
       -\left\lfloor\frac Ud\right\rfloor\right)\\
&\le\delta U(1+r)+\frac{R-1}r.
\end{aligned}
$$

Here $\sum|\lambda(d)|/d\le1+r$ and
$\sum|\lambda(d)|\le(R-1)/r$. The first follows from
$|\lambda(d)|\le1$ and the harmonic-sum bound; the second is the
same decreasing-logarithm sum used in the original $B_A$ envelope.
Using $\log(n/U)\le\delta$, $r\ge1$ and the unchanged
$\sigma_A\ge0$ in $E_A(y)=[-H_A(y)-\sigma_Ay]_+$ gives

$$
E_A(y)\le2\delta^2U+\frac{\delta R}{r^2},
\qquad U<y\le U(1+\delta).
\tag{SV45}
$$

This controls the complete original positive part. It does not estimate
the mean by a power, remove its compensation, or bound the constant
and oscillatory sectors separately.

For the square layer put $P=(x/U)^{1/2}$, $A\le x\le2A$, and
restrict to any subset of the actual primes satisfying

$$
U<x/p^2\le U(1+\delta).
$$

They lie in $[P(1+\delta)^{-1/2},P)$, containing at most
$C\delta P+1$ integers. The endpoint term is retained. Moreover
$p\ge A^{3/8}/\sqrt{1+\delta}>U(1+\delta)$ eventually, uniformly
in $x$ and $\delta$. Thus every denominator in the moving local
support is smaller than $p$, and
$E_{A,p}^{\rm cop}(x/p^2)=E_A(x/p^2)$ with the full drift and mean.
Equation (SV45) and $w_{N,p,2}\le\log p$ yield

$$
\begin{aligned}
\sup_{A\le x\le2A}\frac1x
 \sum_{U<x/p^2\le U(1+\delta)}
 w_{N,p,2}E_A(x/p^2)
\ll{}&L\delta^3A^{-3/8}+L\delta^2A^{-3/4}\\
&+\frac{\delta^2A^{-1/2}}L
 +\frac{\delta A^{-7/8}}L.
\end{aligned}
\tag{SV46}
$$

Only when the original fixed $3/8<\eta<1/2$, choose
$b=(\eta-3/8)/3$ and $\delta_{2,A}=A^{-b}/L$. The first term is
$A^{-\eta}/L^2$ and the other three have strictly larger power
exponents. The whole bound is $O_\eta(A^{-\eta}/L^2)$.
Restricting to the original prime window preserves this bound.
Removing these square samples from the original nonnegative residual
therefore changes its supremum by at most that amount; an attained
supremum is unnecessary.

For comparison, the old $E_A(y)\ll y/L^2$ envelope and the same
short-interval integer count give only
$O(\delta A^{-3/8}/L+A^{-3/4}/L)$ here. With $\delta=\delta_{2,A}$,
its first term is $A^{-\eta+2b}/L^2$, so that upper bound does not
pay this wider strip. This is a comparison of sufficient bounds,
not a lower bound on the actual response. When $\eta\le3/8$,
the old envelope and the existing $\vartheta(P)\ll P$ supplier already
pay a fixed-width square strip at $O(A^{-3/8}/L^2)$; that case is
not an additional payment.

The finite onset calculation is an application of the original weight
definitions and counting bounds, not a new classical sieve theorem,
historical originality claim or Lean certification. It pays the complete
response only in the displayed shrinking strip. The critical region
$y\asymp V$, remaining low layers, mean rate, prime layer, other recovery
terms and full signed Robin tail retain their original obligations.

## A published short-sum bound also pays prime-layer onset samples

The floor-counting error in (SV45) can be avoided in a sufficiently
long onset interval by directly reusing [Henriot's corrected 2014
New Theorem 5](shiuhenriot2026growingmoments.md#henriot-and-the-indispensable-erratum),
[erratum printed p.377](https://doi.org/10.1017/S0305004114000280).
Use its single primitive polynomial $Q(t)=t$ and the fixed function
$F(n)=\tau(n)$. Its parameters are

$$
g=k=r_Q=1,\qquad \alpha=1/4,\quad\delta_{\rm coef}=1,
\quad\varepsilon=1/800<1/400,\quad A_0=2,
$$

with a fixed divisor-growth constant $B_0=B_0(\varepsilon)$.
The class follows from multiplicativity,
$\tau(p^j)=j+1\le2^j$ and the same classical divisor-growth input
already used in (SV27). These constants do not grow with the Robin
source. Here $\delta_{\rm coef}$ is the theorem's polynomial parameter,
not the interval width $\delta$.

Set the source's lower endpoint to $U$ and its interval length to
$\Delta=\delta U$. Its range is satisfied when
$U^{1/4}<\Delta\le U$ and $U$ is sufficiently large.
For this same single-factor polynomial, the corrected root density
recorded in the cited note is

$$
\frac{\breve\rho_Q(a)}{a\kappa(a)}
=\frac1a\prod_{p\mid a}(1-1/p)\le\frac1a.
$$

The existing harmonic divisor sum is at most $(1+\log U)^2$.
[Rosser--Schoenfeld Theorem 8, (3.28)](../Arith/rosser1962approximate.md)
gives $\prod_{p\le U}(1-1/p)\ll1/\log U$.
Thus the corrected theorem supplies

$$
\sum_{U<n\le U(1+\delta)}\tau(n)\ll\delta U\log U,
\qquad U^{1/4}<\delta U\le U.
$$

This invokes the existing short-sum theorem; it does not reprove it
or extend Shiu's literal $0<a<q$ residue statement to $a=q=1$.
Since $|\lambda(d)|\le1$ gives $|a_R(n)|\le\tau(n)$,
substitution into the unchanged (SV44) yields

$$
E_A(y)\ll\delta^2U,
\qquad U<y\le U(1+\delta),\quad
0<\delta\le1/2,\quad\delta U>U^{1/4}.
\tag{SV47}
$$

The positive terms $1$ and $\sigma_Ay$ are retained in the exact
response before this upper bound is taken. The theorem includes real
endpoints; there is no omitted unit error in the inner short sum.

For $k=1,2$, put $P_k=(x/U)^{1/k}$ and
$a_k=\tfrac34(1-1/k)$, so $a_1=0$, $a_2=3/8$.
The actual onset primes lie in
$[P_k(1+\delta)^{-1/k},P_k)$.
Its integer count is $O_k(\delta P_k+1)$, and each prime has
$\log p=O(L)$ for $A\le x\le2A$. The unchanged weights
$0\le w_{N,p,k}\le\log p$ and (SV47) give

$$
\sup_{A\le x\le2A}\frac1x
 \sum_{U<x/p^k\le U(1+\delta)}
 w_{N,p,k}E_A(x/p^k)
\ll_k L\delta^3A^{-a_k}+L\delta^2A^{-3/4}.
\tag{SV48}
$$

The outer endpoint term is explicit. For both $k=1,2$,
$p>y=x/p^k$ eventually throughout this strip. Hence the same
estimate applies exactly to $E_{A,p}^{\rm cop}(y)$ with the full
local slope and mean. Any original sample or window subset is allowed.

For the original fixed $0<\eta<1/2$, choose

$$
\delta_{1,A}=A^{-\eta/3}/L.
\tag{SV49}
$$

Its inner length is $A^{1/4-\eta/3}/L\gg U^{1/4}$; the exponent
gap is $3/16-\eta/3>1/48$. Equation (SV48) for $k=1$ becomes
$O_\eta(A^{-\eta}/L^2)$, since its second term has exponent
$3/4+2\eta/3>\eta$. Thus this shrinking part of the original prime
layer, including its entire drifted positive part, is paid at
$o(A^{-\eta})$ without assuming the missing mean rate.
The old envelope and the same integer count would give
$O(\delta_{1,A}/L+A^{-3/4}/L)$, which does not pay this strip.
Again this compares sufficient upper bounds, not actual lower bounds.

When the original $\eta>3/8$, the square width $\delta_{2,A}$ in
(SV46) also satisfies the short-sum condition. Equation (SV48)
gives the same $O_\eta(A^{-\eta}/L^2)$ payment with a simpler
two-term bound; it is not a second payment of that square strip.
For $\eta\le3/8$ the existing fixed-width square payment remains
the applicable reuse.

The square strip can be deleted from the original nonnegative residual
before applying (SV40)--(SV43). Restricting each of their existing
sampled absolute-error bounds to the retained samples preserves the
adaptive comparison at $o(A^{-\eta})$. This uses the bounds on the
original response; it gives no new polynomial positive part the
original envelopes or vanishing property. The prime-layer calculation
concerns its original response and does not import the higher-layer
adaptive cutoffs into $k=1$.

These are attributed applications of the corrected short-sum and
prime-product suppliers, without Lean certification or a historical
originality claim. They control onset strips only. The remaining prime
and square samples, critical region $y\asymp V$, other finite low layers,
same-source mean rate, remaining recovery convolutions and complete
signed Robin tail still require estimates at the original fixed rate.

## Reusing short prime intervals enlarges the paid onset range

The outer integer count in (SV48) can be replaced by the existing
[Nicolas comparison note's (GS4)](nicolas2025comparison.md#the-local-prime-input-and-its-uniform-range).
That application supplies the uniform short-increment bound from
Guth--Maynard Corollary 1.3, including longer intervals and the
prime-power correction. Combining the two existing inputs keeps the
actual source, its full drifted positive part, and the original fixed
exponent.

For $k=1,2$, put $P_k=(x/U)^{1/k}$, $A\le x\le2A$, and
$c_k=P_k(1+\delta)^{-1/k}$. In addition to (SV47)'s conditions,
suppose $h_k=P_k-c_k+1\ge P_k^{2/3}$ throughout this window.
Apply (GS4) with its dummy clock $Y=P_k$, lower endpoint
$u=c_k-1$ and interval length $h_k$. For sufficiently large $A$,
$Y/2\le u<Y$ and $u+h_k=Y\le3Y/2$; also
$h_k\asymp_k\delta P_k$. The onset primes lie in $[c_k,P_k)$,
contained in $(c_k-1,P_k]$. Hence (GS4) directly gives

$$
\sum_{c_k\le p<P_k}\log p
\le\psi(P_k)-\psi(c_k-1)\ll_k\delta P_k.
$$

The enlarged interval includes the endpoint contribution. The supplier
is uniform at these real endpoints, and any subset of the original
prime samples is allowed. With the unchanged $w_{N,p,k}\le\log p$,
equation (SV47) now gives

$$
\sup_{A\le x\le2A}\frac1x
 \sum_{U<x/p^k\le U(1+\delta)}
 w_{N,p,k}E_A(x/p^k)
\ll_k\delta^3 A^{-a_k},
\qquad a_k=\tfrac34(1-1/k).
\tag{SV50}
$$

For $k=1$ and every original fixed $0<\eta<1/2$, and for $k=2$
only when the original $3/8<\eta<1/2$, choose

$$
b_k=\frac{\eta-a_k}{3}>0,\qquad
\widehat\delta_{k,A}=\frac{A^{-b_k}}{\log L}.
\tag{SV51}
$$

These widths satisfy all hypotheses uniformly in $A\le x\le2A$.
Indeed $\widehat\delta_{1,A}U=A^{1/4-\eta/3}/\log L\gg U^{1/4}$;
the square layer has a larger exponent. At the outer endpoints,
$h_1\asymp A^{3/4-\eta/3}/\log L\gg P_1^{2/3}$ because
$3/4-\eta/3>7/12>1/2$, and
$h_2\asymp A^{3/8-(\eta-3/8)/3}/\log L\gg P_2^{2/3}$ because
$3/8-(\eta-3/8)/3>1/3>1/4$.
Both widths tend to zero. Equation (SV50) yields

$$
O_\eta\!\left(\frac{A^{-\eta}}{(\log L)^3}\right)
=o(A^{-\eta})
$$

for the complete original response on these strips. Throughout them
$p>y=x/p^k$, so the coprime response equals the original response,
including its mean and drift. Deleting the square samples before
(SV40)--(SV43) again uses those equations' existing sampled
absolute-error bounds on the retained subset. No higher-layer adaptive
cutoff or envelope for a new polynomial positive part is imported
into the prime layer.

This is a logarithmic enlargement at the original $o(A^{-\eta})$
target. At (SV51)'s width, the existing integer-count bound (SV48)
has first term $O(LA^{-\eta}/(\log L)^3)$, which does not establish
that target. This comparison concerns sufficient upper bounds, not
a lower bound on the actual response. The explicit widths (SV51)
are $L/\log L$ times those in (SV46) and (SV49). When $\eta\le3/8$, the previously
paid fixed-width square strip is likewise reused without recounting it.
The stronger $O(A^{-\eta}/L^2)$ estimates on the narrower old strips
remain available. The power exponent has not improved, the prime strip
still shrinks, and the remaining samples, mean rate, critical region,
other recovery terms and complete signed Robin tail remain unpaid.
This is an attributed parameter application of the existing (SV47)
and (GS4), without a historical originality or Lean-certification claim.
