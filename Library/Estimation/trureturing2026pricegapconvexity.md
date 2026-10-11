---
bibkey: trureturing2026pricegapconvexity
authors: trureturing research synthesis
year: 2026
title: Actual Robin price gaps, forced-core tail records and the selected-sign boundary
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md
claim: Under the original source-window hypotheses, the complete selected response retains actual price-gap costs; every inactive-forced-prime core is a strict all-integer right-tail record with original-exponent own-size excess. A synthetic positive-reference model excludes height-and-envelope plus numerical full-Q reasoning alone. Actual favorable slack and RH remain unproved.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Actual price gaps and the same-source signed estimate

Assume the qualifying original window in
[N1--N2 and PT1--PT11](../ArithSums/trureturing2026extrawindowpairing.md).
These sources belong to the supplied RH-failure route. This is a
supplier-relative paper application, with no Lean verification,
literature priority claim or proof of RH. The existing source construction,
finite pressure identity, full-Q estimates and quadrature are reused.
The classical convex-order hinge characterization is reused inside the
application. The added interface is its correspondence with the actual
nonlinear selector and the complete original-source gap response; no new
generic convex-order theorem is asserted.

Keep $W(u)=\log(\sigma(u)/u)$, $f(v)=\log\log v$,
$\lambda(v)=1/(v\log v)$ and $w=-\lambda'>0$. Let
$K(v)=\log N_v^{\rm str}$ be the actual strict layer inventory and
$Q=K-\psi$, with the complete prime-power function $\psi$.
Let $dK$ be the atomic measure assigning every actual activation its full
layer mass, including all simultaneous activations. Strict $K$ is left
continuous and has $dK([a,b))=K(b)-K(a)$. The weak, right-continuous
$\psi$ has $d\psi((a,b])=\psi(b)-\psi(a)$ and its full
von Mangoldt atoms. Define the signed measure $dQ=dK-d\psi$; the mixed
function $Q=K-\psi$ is not assigned a common half-open increment convention.
All integrations below use these measures with their actual atoms.
The original finite core set is

$$
\mathcal C_X=\{u\in\mathbb N:5040\mid u,\ \log u\le R,
\text{ every prime divisor of }u\text{ is at most }R\}.
$$

The nonempty envelope is
$V_X(t)=\max_{u\in\mathcal C_X}\Phi_t(u)$, where
$\Phi_t(u)=W(u)-f(t+\log u)$. Take all original prime labels in the
window, $p_0<\cdots<p_m$, $m\ge1$, with $t_i=\log p_i$,
$\delta_i=t_{i+1}-t_i>0$ and $A_i=\log N_{p_i}^{\rm mult}$.
Their canonical least-core selector is
$\mathcal A_X(t)=t+\log u_{\min}(t)$.
N1 supplies all endpoint ties and N2 supplies all-choice ordering.
The common source start is enlarged so that
$\ell>\max\{11,\log R+1\}$, using the existing
$\ell/\log R\to\infty$.

## Real-parameter active cores retain the actual strict inventory

For every $t\in[t_0,t_m]$ and every active core $u$, put
$A=t+\log u$. All-choice ordering and the two actual endpoint
all-tie bounds put $A$ in $[\ell,R]$. Every insertion of a prime
$q\le R$ stays in the original finite core domain, since

$$
\log(uq)\le R-t+\log R<R.
$$

Deleting a layer beyond the mandatory 5040 exponents also stays in that
domain. For the actual layer reward per logarithmic mass
$r_{q,j}=[W(q^j)-W(q^{j-1})]/\log q$, strict concavity and maximality
give

$$
r_{q,v_q(u)+1}
\le\frac{f(A+\log q)-f(A)}{\log q}<\lambda(A),
$$

and, for a removable last layer,

$$
r_{q,v_q(u)}
\ge\frac{f(A)-f(A-\log q)}{\log q}>\lambda(A).
$$

The deletion argument has $A-\log q>1$ by the stated headroom.
Mandatory layers are already strictly active by the supplied $A>11$
activation calculation. For $q>R$, the decreasing layer rewards satisfy
$r_{q,j}\le r_{q,1}<\lambda(q)<\lambda(A)$.
Consequently

$$
\boxed{u=N_A^{\rm str},\qquad A\text{ is not an actual activation time}.}
\tag{PG1}
$$

This extends the finite envelope's inventory interface to its real
parameters. The cores remain literal integers; $e^t$ is not declared a
new prime label or a new original arithmetic source.

## Full dominance pays a nonnegative prefix cost on every actual gap

For an actual switch $s\in[t_0,t_m)$, let $U,V$ be the smallest and
largest active cores and put

$$
\alpha=s+\log U,\quad\beta=s+\log V,\quad
G_s=(\alpha,\beta),\quad Y_s(z)=s+K(z).
$$

Ignore only zero-length gaps. PG1 gives
$K(\alpha)=\alpha-s$, $K(\beta)=\beta-s$ and no actual activation
atom at either endpoint. Every $N_z^{\rm str}$, $\alpha\le z\le\beta$,
satisfies $U\mid N_z^{\rm str}\mid V$ and belongs to the same
$\mathcal C_X$. Keep its full envelope deficit
$\Delta_s(z)=V_X(s)-\Phi_s(N_z^{\rm str})\ge0$.

Reuse the finite pressure identity with the real shift $s$ and keep
$C_z(y)=f(z)+\lambda(z)(y-z)-f(y)\ge0$. It gives

$$
\Phi_s(N_z^{\rm str})-\Phi_s(U)
=\int_\alpha^z[Y_s(v)-v]w(v)\,dv+C_z(Y_s(z)).
$$

Thus the continuous prefix cost

$$
\mathscr P_s(z)=-\int_\alpha^z[Y_s(v)-v]w(v)\,dv
=\Delta_s(z)+C_z(Y_s(z))\ge0,
\qquad \mathscr P_s(\alpha)=\mathscr P_s(\beta)=0
\tag{PG2}
$$

retains both full-core dominance and the actual concavity cost.
Extend it by zero outside $G_s$. Since both $Y_s(z)$ and $z$ lie in
$[\alpha,\beta]$, the decreasing curvature gives the additional bound

$$
\mathscr P_s(z)\ge\frac{w(\beta)}2[Y_s(z)-z]^2.
\tag{PG3}
$$

No comparability of $\alpha,\beta$ is assumed. These are consequences
of full dominance, not replacements for dominance over every core.
They concern the whole real-parameter switch gap; the previously supplied
N4.5 arriving-clock contact and its preceding negative integral are reused.

## Two moments and the price-coordinate hinge identity

Use the finite signed event measure
$d\mu_s=(dK-dv)|_{G_s}$, with every actual activation mass retained.
The own-clock endpoints and the exact switch equality imply

$$
\int_{G_s}d\mu_s=0,\qquad
\int_{G_s}\lambda(v)\,d\mu_s(v)=0.
\tag{PG4}
$$

Indeed $K(\beta)-K(\alpha)=\beta-\alpha$, while the activation
reward identity and the tie give
$\int_{G_s}\lambda(v)dK(v)=W(V)-W(U)
=f(\beta)-f(\alpha)=\int_\alpha^\beta\lambda(v)dv$.
Finite integration by parts, or finite Fubini, then gives for every $z>1$

$$
\int_{G_s}(\lambda(v)-\lambda(z))_+d\mu_s(v)
=-\mathscr P_s(z)\le0.
\tag{PG5}
$$

For $z$ outside the gap the two moments make this exactly zero.
The standard hinge representation, or uniform convex piecewise-linear
approximation on the compact price interval, therefore gives for every
continuous convex $\varphi$

$$
\int_{G_s}\varphi(\lambda(v))dK(v)
\le\int_{G_s}\varphi(\lambda(v))dv.
\tag{PG6}
$$

The coordinate is the decreasing price $\lambda$, not the original clock.
All simultaneous activations retain their complete $\log q$ masses.

## The original price tent has an exact gap response

For an original canonical clock $A_i$, keep PT1's
$a_i=A_i-A_i^{4/5}$, $b_i=A_i+A_i^{4/5}$,
$m_{-,i}=\lambda(a_i)-\lambda(A_i)>0$ and
$m_{+,i}=\lambda(A_i)-\lambda(b_i)>0$.
For any such clock $A$, the original kernel has the exact expression

$$
\begin{aligned}
k_A(v)={}&\frac{(\lambda(v)-\lambda(b))_+}{m_+}
-\left(\frac1{m_-}+\frac1{m_+}\right)
 (\lambda(v)-\lambda(A))_+\\
&+\frac{(\lambda(v)-\lambda(a))_+}{m_-}.
\end{aligned} \tag{PG7}
$$

Every canonical $A_i$ lies outside each open gap $G_s$. At a switch
label the least-core convention selects its left endpoint. Hence
$\mathscr P_s(A_i)=0$, and PG5 yields

$$
\boxed{\int_{G_s}k_{A_i}(v)[dK(v)-dv]
=-\frac{\mathscr P_s(a_i)}{m_{-,i}}
-\frac{\mathscr P_s(b_i)}{m_{+,i}}\le0.}
\tag{PG8}
$$

A gap contained in one affine price segment contributes exactly zero.
Every remaining contribution is retained through the actual edge costs;
no gap is deleted as a sparse exceptional set. PG8 controls complete
stock $dK-dv$, not the prime measure alone.

## Exact decomposition of the original discrete joint response

Keep the original weights

$$
W_X(v)=\sum_{i=0}^{m-1}\delta_iA_i^{-3/10}k_{A_i}(v),\qquad
L_X=\sum_{i=0}^{m-1}\delta_i>0.
$$

Let $I_X=[A_0,A_m]$ and $D_X=I_X\setminus\bigcup_sG_s$.
Include switches at $t_0$ and exclude switches at $t_m$.
On each fixed-core selector branch, PG1 makes $K$ constant; it also
excludes activation atoms at active endpoints. Therefore

$$
dK(D_X)=0,\qquad |D_X|=L_X.
\tag{PG9}
$$

Other active cores at a multiple tie can have own clocks inside a gap.
Those finitely many points are not removed from $\mathcal C_X$, have
no activation atom by PG1, and do not affect the measure statements.
Define the four complete quantities

$$
\begin{aligned}
\mathsf E_X&=\int_{(1,\infty)\setminus I_X}W_X(v)[dK(v)-dv],\\
\mathsf S_X&=\int_{D_X}W_X(v)dv\ge0,\\
\mathsf G_X&=-\sum_s\int_{G_s}W_X(v)[dK(v)-dv]\ge0,\\
\mathsf Q_X&=\int W_X(v)dQ(v).
\end{aligned} \tag{PG10}
$$

Writing $\mathscr P_X=\mathscr P_s$ on each gap and zero elsewhere,
PG8 gives the explicit full gap cost

$$
\mathsf G_X=\sum_{i=0}^{m-1}\delta_iA_i^{-3/10}
\left[\frac{\mathscr P_X(a_i)}{m_{-,i}}
+\frac{\mathscr P_X(b_i)}{m_{+,i}}\right].
\tag{PG11}
$$

Partition the finite support into $I_X^c,D_X,\bigcup_sG_s$ and use
$d\psi-dv=(dK-dv)-dQ$. This gives the exact original response

$$
\boxed{\sum_n\Lambda(n)W_X(n)-\int W_X(v)dv
=\mathsf E_X-\mathsf S_X-\mathsf G_X-\mathsf Q_X.}
\tag{PG12}
$$

No new quadrature error, thinning or shortened prime window is introduced.
Exterior flux has support only in
$[A_0-A_0^{4/5},A_0)\cup(A_m,A_m+A_m^{4/5}]$.
Both endpoints, all weights and both costs depend on the same arithmetic.
A reference prime-power atom at a switch endpoint remains in $d\psi$.
It contributes its negative full mass to $dQ$, even though $dK$ has no
activation there; subtraction of $\mathsf Q_X$ restores its complete
$\Lambda$ weight in PG12.

The original two terminal costs are separate from PG2's switch costs.
Keep the actual $Y_{-,i},Y_{+,i}$ from PT2 and define the two costs separately:

$$
\mathsf C_X^-=\sum_{i=0}^{m-1}
\frac{\delta_iA_i^{-3/10}}{m_{-,i}}C_{a_i}(Y_{-,i})\ge0,
\qquad
\mathsf C_X^+=\sum_{i=0}^{m-1}
\frac{\delta_iA_i^{-3/10}}{m_{+,i}}C_{b_i}(Y_{+,i})\ge0.
$$

PT2 still gives

$$
\mathsf E_X-\mathsf S_X-\mathsf G_X+
\mathsf C_X^-+\mathsf C_X^+\le0.
\tag{PG13}
$$

## The favorable exterior estimate remains the unpaid sign

Reuse the complete pointwise full-Q supplier:

$$
\mathsf Q_X=d_0L_X+r_X,\quad d_0=(\sqrt2-1)/2,\quad
|r_X|\le\eta_XL_X,\quad
\eta_X=C_Q\sup_{\ell\le A\le R}\mathcal F_Q(A)\longrightarrow0.
\tag{PG14}
$$

All seven errors and their common unknown start remain. PT8 requires
$\mathsf E_X-\mathsf S_X-\mathsf G_X\ge\varepsilon L_X+r_X$.
A sufficient still-unproved target is one fixed $\eta>0$ such that,
beyond every common analytic/source start, some qualifying original
full window satisfies

$$
\boxed{\mathsf E_X\ge\mathsf S_X+\mathsf G_X+\eta L_X.}
\tag{PG15}
$$

Once $\eta_X\le\eta/2$, this supplies PT8 with fixed
$\varepsilon=\eta/2$. It would contradict PG13 on that same window.
The cost signs and exact moment cancellations do not establish this
lower bound on exterior flux. No favorable prime sign follows from
convex order of the complete stock measure or from the old upper comparison.
The independent fixed-source signed finite-head obligation and RH also
remain unresolved.

For historical reuse, the [Erdős--Nicolas benefit](../ArithSums/erdosnicolas1975repartition.md)
is the existing fixed-linear-price loss. At a nonlinear switch the
endpoint prices are $\lambda(\alpha)>\lambda(\beta)$; adjacency of
these cores in the classical CA sequence has not been proved. Classical
neighboring-CA restrictions therefore cannot bound this $V/U$ without
that additional correspondence.

## The actual inactive-forced-prime core is a strict right-tail record

Keep the original fixed $b,d$, qualifying witness $X$, every original
prime label $p$, and every maximizing tie $N=pu$ supplied by N1. Put
$t=\log p$, $B=\log u$, $A=B+t$, and $c_p=\log(1+1/p)$.
The actual $p$ is absent from $u$ and strictly inactive:
$c_p<t\lambda(A)$. Keep $F(n)=W(n)-f(\log n)$ and define

$$
D_t(y)=f(y+t)-f(y),\qquad a_p=D_t(B)-c_p.
$$

Uniformly over all these labels and ties, $B\to\infty$ as $X\to\infty$.
Otherwise a bounded sequence of cores has bounded $W(u)$, while
$A\ge\ell\to\infty$ and $c_p\le e^{-\ell}$, forcing
$F(N)=W(u)+c_p-f(A)\to-\infty$. This contradicts N1's positive height.
Enlarge only the common start until $B>11$.

Strictly decreasing $\lambda=f'$ gives
$D_t(B)>t\lambda(B+t)>c_p$. Absent-prime multiplicativity therefore gives

$$
a_p>0,\qquad F(u)=F(N)+a_p,
\tag{CR1}
$$

and the following actual all-integer comparison holds for every $v>u$:

$$
\boxed{
F(u)-F(v)\ge
\begin{cases}
a_p,&p\mid v,\\
D_t(B)-D_t(\log v),&p\nmid v.
\end{cases}}
\tag{CR2}
$$

Both lower bounds are strictly positive. To prove CR2 first suppose
$5040\mid v$. If $p\mid v$, full-domain maximality of $N$ gives
$F(v)\le F(N)$. Otherwise $pv$ is in that same maximization domain and
$F(pv)=F(v)+c_p-D_t(\log v)$. Comparing $pv$ with $pu$ proves the
second branch. It is positive because
$D_t'(y)=\lambda(y+t)-\lambda(y)<0$.

For arbitrary $v>u$, use the actual integer
$v^*=\operatorname{lcm}(5040,v)$. At clocks above $11$ every missing
mandatory 5040 layer has reward per logarithmic mass strictly above the
current $\lambda$; its finite $f$-increment per mass is strictly below
that price. Inserting all missing mandatory layers gives
$F(v^*)\ge F(v)$. Since $p\ge29$, $p\mid v^*$ iff $p\mid v$.
Also $v^*\ge v>u$ and
$D_t(B)-D_t(\log v^*)\ge D_t(B)-D_t(\log v)$.
The already proved comparisons at $v^*$ therefore give CR2.

Consequently the same actual core is the unique maximizer of $F$ on
all integers $v\ge u$. This compares every larger integer, not merely
multiples of $u$. It is a consequence for **every original core**;
the [existing CNS tail-selection mechanism](../Arith/caveney2012sacaga.md)
is reused and is not reconstructed as a new source family. CR2 does not
make nonlinear switch cores adjacent in the classical CA sequence.

## The original power excess transfers without losing its exponent

The same cores retain, with the original fixed $b,d$, the own-size bound

$$
\boxed{F(u)-\gamma\ge\frac d{64}B^{-b},\qquad B=\log u.}
\tag{CR3}
$$

The common eventual start can depend on $b,d$ but not on the label or tie.
Indeed CR1 and the original source height give

$$
F(u)-\gamma\ge\frac d2X^{-b}+D_t(B)-c_p.
\tag{CR4}
$$

If $B\ge X$, CR1 immediately gives the stronger $dB^{-b}/2$.
If $B<X$ and $B\ge t$, then $A\le2B$, eventually
$\log A\le2\log B$, and the original
$\ell=(d/8)X^{1-b}\log X$ gives

$$
D_t(B)\ge\frac{t}{A\log A}
\ge\frac{\ell}{4B\log B}
=\frac d{32}B^{-b}
 \left(\frac XB\right)^{1-b}\frac{\log X}{\log B}
\ge\frac d{32}B^{-b}.
$$

If $B<X$ and $B<t$, monotonicity in $t$ instead gives

$$
D_t(B)\ge f(2B)-f(B)
=\log\left(1+\frac{\log2}{\log B}\right)
\ge\frac{\log2}{2\log B}\ge\frac d{32}B^{-b}
$$

eventually, since the original $b>0$ is fixed. Finally,
$c_pB^b\le e^{-\ell}R^b\to0$, using $B\le R$ and
$\log R=o(\ell)$. Thus $c_p\le dB^{-b}/64$ uniformly and CR4 proves CR3.
No new zero-abscissa hypothesis or output exponent is substituted.
CR3 constrains the actual value at the actual core; it gives no favorable
sign for PG15's compactly supported response.

## Maximum-preserving contact recursion is stationary on these tails

For any such core $u$, any nonincreasing functions $q_k$ on
$\{n\in\mathbb N:n\ge u\}$, any $s_k>0$ and any $a\ge0$, CR2 directly
implies that

$$
n\longmapsto e^{s_kF(n)}+a q_k(n)
\tag{CR5}
$$

has unique maximum $u$. For every $n>u$ its first term is strictly smaller
and its second term is no larger. This elementary implication is an
application, not a new generic contact theorem. Restriction to any subset
containing $u$ leaves the conclusion unchanged; no CA membership is inferred
from the restriction itself.

The [existing Musin contact source](../Analytic/musin2026higherorder.md),
Theorem 4.1, concerns a specified classical CA domain and reference,
positive decreasing $q_k$, coordinate-transition conditions and a
normalization limit. Its reference convention is not transplanted to $u$.
CR5 supplies a concrete stationary-tail consequence for the actual cores.
A FIB encoding of these same maximum-preserving contacts inherits it;
other recursions remain outside this assertion. Cofinal later witnesses
can have smaller positive excesses, so cofinality does not force escape
from one fixed strict tail maximum.

## Height and full-envelope geometry alone do not supply PG15

The following synthetic atomic construction tests only a proposed
height-plus-envelope abstraction. It is not actual divisor arithmetic:
its rewards are not prime-layer rewards, it has no actual $\psi$ or
actual prime-power full-Q supplier, and its model clocks do not replace the original $A_i$.
It gives no counterexample to RH or to implication from the full actual
RH-failure hypotheses to PG15.

Fix the same $0<b<1/2$, $d>0$, set $c=2bd$, and put

$$
h(x)=x+cx^{1-b}\log x,\qquad z_j=h(j).
$$

Choose a fixed sufficiently large integer $j_0\ge3$. Use states
$j\ge j_0-1$, with clocks $j$, and the strict inventory

$$
K_*(v)=j_0-1+\sum_{j\ge j_0}\mathbf1_{\{z_j<v\}}.
$$

Realize the initial mass $j_0-1$, if an all-positive-tail measure is needed,
by $j_0-1$ fixed unit atoms strictly between $1$ and $h(j_0-1)$.
All tested tents eventually have $A-A^{4/5}>h(j_0-1)$; define
$\kappa=h^{-1}$ only on that tail. A precise reward normalization is

$$
\mathcal W_j=f(j)+\gamma+
\sum_{r=j+1}^{\infty}\bigl(f(r)-f(r-1)-\lambda(h(r))\bigr).
$$

It gives $\mathcal W_j-\mathcal W_{j-1}=\lambda(z_j)$ and
$\mathcal W_j-f(j)\to\gamma$. The series converges because

$$
\lambda(z_j)-[f(j)-f(j-1)]
=-c j^{-b-1}(1+o(1))
$$

is absolutely summable. Its tail gives

$$
\mathcal W_j-f(j)-\gamma
=(c/b+o(1))j^{-b}=(2d+o(1))j^{-b}.
\tag{CR6}
$$

These values are eventually strictly decreasing, so all sufficiently
large states are strict right-tail records. They also satisfy the
numerical H2 upper envelope eventually, because
$j^{-b}=o((\log j)^{-2})$.

For $t\ge0$ use the complete state envelope
$V_*(t)=\max_{j\ge j_0-1}[\mathcal W_j-f(t+j)]$.
The adjacent tie is the unique $s_j$ satisfying

$$
f(s_j+j)-f(s_j+j-1)=\lambda(z_j),\qquad
s_j=z_j-j+\tfrac12+O(j^{-1}).
\tag{CR7}
$$

The $s_j$ are eventually strictly increasing: their leading difference
is $c(1-b)j^{-b}\log j$, which dominates the displayed remainder.
The adjacent objective difference is strictly increasing in $t$.
Thus for $s_j<t<s_{j+1}$ it is positive through state $j$ and negative
afterward, so $j$ dominates **every** state. The finitely many initial
states are irrelevant for sufficiently large $t$. For each fixed $t\ge0$, the limiting state objective is $\gamma$ and
its excess is eventually positive, since
$f(j+t)-f(j)=O_t((j\log j)^{-1})=o(j^{-b})$.
Together with the ordered switches this pays attainment at an actual state.
At the active clock $A=t+j$ one has
$z_j<A<z_{j+1}$ and $K_*(A)=j=A-t$. Every switch gap has length one,
contains exactly its full unit activation atom, and has zero total and
price moment by CR7. Its endpoints do not activate. Full dominance
supplies the same nonnegative prefix cost as PG2, with the model rewards.

For every integer $X\to\infty$, retain every ordinary prime label in
$[e^{\ell_X},e^{2\ell_X}]$, with the original numerical
$\ell_X=(d/8)X^{1-b}\log X$. The candidate state $j=X$ gives uniformly
for $t\in[\ell_X,2\ell_X]$

$$
f(X+t)-f(X)\le t\lambda(X)\le\frac d4X^{-b},\qquad
V_*(t)-\gamma\ge(7d/4+o(1))X^{-b}\ge\frac d2X^{-b}.
\tag{CR8}
$$

For $t=\theta\ell_X$, $1\le\theta\le2$, CR7 more precisely gives
$j/X=(\theta/(16b))^{1/(1-b)}(1+o(1))$ and $A\sim j$, uniformly
including ties. Thus $j\asymp X$ and $A\asymp X$ for every active state
on these whole windows, with constants depending only on $b,d$.
Their original numerical bounds $\ell_X\le A\le R_X$ hold eventually.
Their selected excesses are $O(X^{-b})$, so the numerical H2 bound holds
there as well. Adding the unchanged label reward $c_p$ leaves the model
optimizer unchanged and only increases its height. This label use does not turn a state into an actual integer core or its
reward into a divisor sum. The H2 scope is only the own-state and selected-clock
numerical bounds just proved. For a fixed label $p$ and $j\to\infty$,
$\mathcal W_j+c_p-f(j+\log p)\to\gamma+c_p>\gamma$; the model therefore
does **not** satisfy global arithmetic H2 over all labelled competitors.

Let $\kappa=h^{-1}$ on the sufficiently large real tail. Then
$|K_*(v)-\kappa(v)|\le1$ and

$$
\kappa'(v)-1=-c(1-b)v^{-b}\log v\,(1+o(1)).
$$

Use exactly the original price tent $k_A$ and width $A^{4/5}$.
Its existing area asymptotic and $\int|k_A'|=2$ are reused.
Finite Stieltjes integration by parts bounds the response from
$K_*-\kappa$ by $2$, since the tent vanishes at both support endpoints.
Uniformity on that support consequently gives

$$
\boxed{
A^{-3/10}\int k_A(v)[dK_*(v)-dv]
=-c(1-b)A^{1/2-b}\log A\,(1+o(1))\longrightarrow-\infty.}
\tag{CR9}
$$

Retain all labels, least active states and original positive coefficients
in the corresponding model weight
$W_X^*(v)=\sum_i\delta_i(A_i^*)^{-3/10}k_{A_i^*}(v)$.
Because $A_i^*\asymp X$ uniformly, CR9 gives

$$
\frac1{L_X}\int W_X^*(v)[dK_*(v)-dv]\longrightarrow-\infty,
\qquad
\frac{\mathsf E_X^*-\mathsf S_X^*-\mathsf G_X^*}{L_X}
\longrightarrow-\infty.
\tag{CR10}
$$

Thus fixed cofinal normalized height, strict tail records and complete
nonlinear-envelope dominance alone do not force favorable stock sign.
This model establishes only the insufficiency of the stated
height-and-envelope abstraction; the actual arithmetic interfaces and global
labelled-competitor H2 remain outside its scope. CR1--CR10 are
supplier-relative paper deductions, with no Lean verification or priority
claim; the independent signed finite head, PG15 and RH remain unresolved.
## A positive atomic reference can also retain the numerical full-Q estimate

Keep the preceding synthetic model, whose actual-source implications are
not used here. It can be equipped with a positive weak reference inventory
having the same pointwise full-Q asymptotic form as the reused PT3
supplier; PG14 is its weighted consequence. This remains a
synthetic model: none of its reference atoms is identified with an actual
prime power, and no actual $\Lambda$, Euler product or zeta explicit formula
is supplied.

Set $a_* =\sqrt2-1=2d_0$ and $T(v)=v-a_*\sqrt v$ on a sufficiently
large real tail. The map is strictly increasing there. At each model
activation $z_j$, let $\tau_j$ be the unique later clock satisfying
$T(\tau_j)=z_j$ and define the positive right-continuous reference

$$
\Psi_*(v)=j_0-1+\sum_{j\ge j_0}\mathbf1_{\{\tau_j\le v\}},
\qquad Q_*(v)=K_*(v)-\Psi_*(v),\quad dQ_*=dK_*-d\Psi_*.
$$

All reference atoms have positive unit mass and are retained. The baseline
constant affects no tested tail measure and can be realized by the same
fixed lower positive atoms as the original synthetic stock. No common
half-open increment convention is assigned to the mixed function $Q_*$. For sufficiently large $v$, the existing
inverse clock $\kappa=h^{-1}$ gives

$$
Q_*(v)=q(v)+O(1),\qquad
q(v)=\kappa(v)-\kappa(T(v)),
\tag{CR11}
$$

with a uniform bounded discrepancy, regardless of strict/weak endpoint
contacts. Differentiating the smooth inverse, not an infinite zero series,
gives $\kappa'(v)=1+O(v^{-b}\log v)$ and
$\kappa''(v)=O(v^{-b-1}\log v)$. Therefore

$$
q'(v)=\kappa'(v)-\kappa'(T(v))
     +\frac{a_*}{2\sqrt v}\kappa'(T(v))
=\frac{d_0}{\sqrt v}+O(v^{-b-1/2}\log v).
\tag{CR12}
$$

For the original $h_A=A^{4/5}$, $a=A-h_A$, $b_A=A+h_A$, integrate this
identity and retain the bounded discrepancy at both endpoints. Uniformly
for $a\le t\le b_A$,

$$
Q_*(t)-Q_*(a)=\frac{d_0}{\sqrt A}(t-a)
+O\left(\frac{h_A^2}{A^{3/2}}
 +h_A A^{-b-1/2}\log A+1\right).
\tag{CR13}
$$

Relative to $h_A/\sqrt A$ this error is
$O(A^{-1/5}+A^{-b}\log A+A^{-3/10})=o(1)$.
For the original fixed $b>0$, $A^{-b}\log A=o(1/\log A)$;
thus the error is also bounded by a fixed multiple of the existing
seven-term $\mathcal F_Q(A)$ after a common start. This compares the
numerical error form; it does not realize the actual prime-power supplier.

The original tent's area and variation then give, by finite integration
by parts with the same signed event measure,

$$
A^{-3/10}\int k_A(v)dQ_*(v)=d_0+o(1).
\tag{CR14}
$$

Uniformly over the complete model label window,
$\int W_X^*dQ_*=(d_0+o(1))L_X$.
CR9--CR10 remain unchanged, and the reference response is exactly

$$
\int W_X^*(v)[d\Psi_*(v)-dv]
=\mathsf E_X^*-\mathsf S_X^*-\mathsf G_X^*
 -\int W_X^*(v)dQ_*(v).
\tag{CR15}
$$

Its ratio to $L_X$ still tends to $-\infty$. Hence even adding a positive
atomic reference and the numerical full-Q response to the retained height
and envelope abstraction does not supply PG15. The actual prime/divisor coefficients, integer-source realization and
global H2 over all labelled competitors remain absent, with the H2 scope
fixed above. Nonnegativity of the reference measure and that asymptotic
coefficient alone therefore do not pay the missing comparison. This conclusion does not establish nonimplication from the full
actual RH-failure hypotheses, refute RH or prove the actual estimate.

## The complete signed-tail consumer remains at the core's own clock

For each original core $u$ in CR1--CR3 put $B=\log u$,
$L_B=\log B$ and $T_B=\sqrt B\,L_B$. Its strict all-integer right-tail
property gives the existing GA2 condition by taking $v=au$ for each
integer $a\ge2$; $a=1$ is equality. Uniform $B\to\infty$ permits one
common source start after which

$$
B\ge\max\{\log N^{(0)},e^{26}\},
$$

so the supplier thresholds $u\ge N^{(0)}$ and $L_B\ge26$ both hold.
There is no numeric value supplied for that common witness start. Apply of the [existing complete GA2 core identity
and effective allowance](../ArithSums/nicolas2025comparison.md#the-same-effective-allowance-on-actual-ga2-cores),
A3--A5, after one common start. Keep its entire original improper integral

$$
I_\psi(B)=\int_B^\infty(\psi(v)-v)
\frac{1+\log v}{v^2\log^2v}\,dv,
\qquad \gamma-F(u)=I_\psi(B)+K_u(B),
\qquad T_B K_u(B)>\mathcal E(L_B).
$$

Here $K_u(B)$ is the supplier's extended arithmetic core, distinct from
PG1's strict inventory clock $K(v)$. Every extra support term, prime power,
elementary correction and infinite endpoint in that supplier remains.
CR3 gives the instantiated all-original-core upper comparison

$$
\boxed{
T_B I_\psi(B)<-\mathcal E(L_B)
-\frac d{64}B^{1/2-b}\log B.}
\tag{CR16}
$$

The existing allowance is $\mathcal E(L_B)>0.65$ for $L_B\ge26$,
and the original $0<b<1/2$ and $d>0$ are fixed. Thus, for every fixed $M\ge0$, one common sufficiently
large witness start makes $T_B I_\psi(B)<-M$ for **every** original label
and maximizing tie. This is uniform on the entire original family, with
no clock comparison between $B$ and $X$ required.

This uses the [existing CNS oscillation/tail consumer](../Arith/caveney2012sacaga.md#inherited-oscillation-relaxes-the-eventual-signed-target)
with CR3's newly paid original-core scope and exponent; it does not repeat
that consumer as a new analytic theorem or introduce a different kernel.
The integral is evaluated at $B=\log u$, not at the forced integer clock
$A=\log(pu)$, an auxiliary prime or a freely selected real center. A lower
bound at one of those other clocks cannot be transported here without its
own estimate. CR16 supplies no lower bound at $B$, no PG15 exterior slack,
and no estimate for the independent fixed-source finite head. Those
obligations and RH remain unproved. This is a paper application only,
with no Lean verification or originality claim.

## The full removal gain pays a linear complete-head allowance

Keep the original fixed $b,d$, witness $X$, every label $p$ and every
maximizing tie $N=pu$ from CR1--CR4. Write $t=\log p$,
$B=\log u$, $A=B+t$, $s_B=\sqrt B\log B$, and
$v_{p,u}=t/\sqrt B$. The same actual core is $u=N_A^{\rm str}$,
so $K(A)=B$.

The [existing full-real-clock activation correction](../ArithSums/nicolas2025comparison.md#the-arithmetic-correction-vanishes-at-the-paid-heat-scale)
is valid for the strict prefix. It gives
$K(x)=\psi(x)+O(\sqrt x[\log(2x)]^{5/2})$ for every real $x>1$.
Reuse its unconditional PNT input and the original uniform escape of the
source clocks. Then, uniformly over all original labels and ties,

$$
K(A)=A+o(A),\qquad A/B\longrightarrow1,\qquad t/B\longrightarrow0.
\tag{CR17}
$$

This uses no short-interval estimate, no own-clock optimum at $B$, and
no comparison $B\ge X$.

### The retained height increment supplies its own coefficient

CR4 retains the full same-source height

$$
F(u)-\gamma\ge\frac d2X^{-b}+D_t(B)-c_p,
\qquad c_p=\log(1+1/p)\le e^{-\ell}.
$$

The strictly decreasing price gives
$t/(A\log A)\le D_t(B)\le t/(B\log B)$. Define the normalized
removal coefficient

$$
\chi_{p,u}=\frac{B\log B}{t}[D_t(B)-c_p].
$$

Using the original $t\ge\ell$, $A\le R$ and $\log R=o(\ell)$,

$$
\frac{B\log B}{A\log A}
-\frac{R\log R}{\ell}e^{-\ell}
\le\chi_{p,u}\le1.
\tag{CR18}
$$

The lower correction tends to zero, while CR17 sends the first term to
one. Consequently $\chi_{p,u}\to1$ uniformly on the entire original
family. Both the original constants and all ties remain; the common
analytic/source start is existential, with no numeric value supplied.
In particular

$$
s_B[D_t(B)-c_p]=\chi_{p,u}v_{p,u}.
$$

Reuse the [existing unrestricted integer identity OCQ13](../ArithSums/nicolas2025comparison.md)
at this same core clock. Let $R_{\rm pp}(B)$ denote its original
unrestricted prime-power reserve and $d_B(u)$ its actual own-price
defect. They are distinct from the source-window ceiling $R$, strict
stock $K(v)$ and extended GA2 core $K_u(B)$ in CR16. The supplier keeps
all positive integers, including one, and gives

$$
-s_B I_\psi(B)
=s_B(F(u)-\gamma)+s_B R_{\rm pp}(B)+s_Bd_B(u),
\qquad R_{\rm pp}(B)\ge0,\quad d_B(u)\ge0.
$$

Thus the unabridged height, rather than a second use of CR3's partly
height-derived bound, supplies

$$
-s_B I_\psi(B)\ge
\frac d2\sqrt B\log B\,X^{-b}+\chi_{p,u}v_{p,u}.
\tag{CR19}
$$

No positive contribution is counted twice.

### The residual margin keeps the original witness scale

Fix $0\le\kappa<1$ once. Uniform convergence in CR18 permits one
common start with $\chi_{p,u}\ge(1+\kappa)/2$. If $B\ge X$, the first
term of CR19 is at least $(d/2)X^{1/2-b}\log X$. If $B<X$, then

$$
v_{p,u}\ge\frac\ell{\sqrt X}
=\frac d8X^{1/2-b}\log X,
$$

and the remaining $(\chi_{p,u}-\kappa)v_{p,u}$ is at least
$d(1-\kappa)X^{1/2-b}\log X/16$. Both branches retain nonnegative
other terms. Therefore every original label and maximizing tie satisfies

$$
\boxed{
-s_BI_\psi(B)\ge
\kappa\frac{\log p}{\sqrt B}
+\frac{d(1-\kappa)}{16}X^{1/2-b}\log X.}
\tag{CR20}
$$

The last term tends to infinity uniformly because the original
$b<1/2$ is fixed. In particular $\kappa=1/2$ leaves the coefficient
$d/32$. The boundary $\kappa=1$ is not established by this argument.
Neither $v_{p,u}$ alone nor a different source clock is required to
have a diverging lower bound.

These are paper applications of the named suppliers, without Lean
verification or a claim of literature originality.

## The complete original-window head may carry the removal allowance

Keep the entire improper integral in CR16 and all its original zero
coefficients, actual real parts, multiplicities, elementary correction
and endpoint conventions. For an admissible moving-clock cutoff write
a complete finite-head upper enclosure as

$$
\begin{aligned}
U(B,T)={}&s_B\left[
2\operatorname{Re}\sum_{0<\operatorname{Im}\rho\le T}
 m_\rho F_B(\rho)+R_{\rm elem}(B)\right]
+E_{\rm full}(B,T),\\
-s_BI_\psi(B)&\le U(B,T).
\end{aligned}
$$

Here $F_B$ is the [supplier's original coefficient (M1)](../ArithSums/nicolas2025comparison.md#a-fixed-positive-scale-mixture-cannot-remove-the-functional-equation-weight)
with its variable $A$ set to this same $B$, and $R_{\rm elem}(B)$ is
that supplier's pole-and-trivial-zero correction, with its positive
normalized sign retained. The [existing signed suffix contract
(J1)--(J6)](../ArithSums/nicolas2025comparison.md#a-signed-infinite-height-allowance-from-the-existing-landau-formula)
applies for $B\ge e^2$ and $T\ge8$. Its signed prime-power main term
keeps its displayed sign. The [moving cut $T=B^{1/4}\log B$](../ArithSums/nicolas2025comparison.md#a-moving-cut-makes-this-signed-suffix-allowance-tend-to-zero)
pays an asymptotically vanishing suffix allowance; it does not bound
the remaining head. The complete $E_{\rm full}$ must pay every omitted suffix, coefficient
approximation and enclosure error exactly once in the supplier's actual
domain. Exact coefficients introduce no coefficient-approximation
error. A symbolic remainder or a finite verified zero range does not
establish this upper-enclosure contract at arbitrary moving clocks.

CR20 now allows the still-unproved pointwise upper target

$$
U(B,T)\le M+\kappa\frac{\log p}{\sqrt B}
\tag{CR21}
$$

with one fixed finite $M\ge0$ and $0\le\kappa<1$. It is also sufficient to
control one complete original window jointly. Keep $p_0<\cdots<p_m$,
$\delta_i=\log p_{i+1}-\log p_i>0$ for $0\le i<m$, and
$L_X=\sum_{i=0}^{m-1}\delta_i$. The final label $p_m$ remains the
original window boundary. For each allowed assignment of maximizing
ties define

$$
V_X^{\rm lag}=\sum_{i=0}^{m-1}\delta_i
\frac{\log p_i}{\sqrt{B_i}},\qquad B_i=\log u_i.
$$

The same positive weights applied to CR20 give

$$
\sum_{i=0}^{m-1}\delta_i[-s_{B_i}I_\psi(B_i)]
\ge\kappa V_X^{\rm lag}
+\frac{d(1-\kappa)}{16}X^{1/2-b}\log X\,L_X.
\tag{CR22}
$$

A sufficient obligation is: for fixed finite $M\ge0$ and
$0\le\kappa<1$, beyond every common
analytic/source start, some original qualifying **full** window has the
following property. Every allowed assignment of maximizing ties admits
admissible cutoffs $T_i$, with complete remainder contracts at those same
cores, satisfying

$$
\boxed{
\sum_{i=0}^{m-1}\delta_iU(B_i,T_i)
\le ML_X+\kappa V_X^{\rm lag}.}
\tag{CR23}
$$

The quantifier order is

$$
\begin{gathered}
\exists\,M\ge0,\ \kappa\in[0,1)\quad
\forall\,\text{common finite starts}\quad
\exists\,\text{qualifying original full window}\quad\\
\forall\,\text{allowed maximizing-tie assignments}\quad
\exists\,\text{admissible cutoffs and complete contracts}.
\end{gathered}
$$

The starts do not depend on individual labels or
ties. CR22--CR23 would imply

$$
\left[\frac{d(1-\kappa)}{16}X^{1/2-b}\log X-M\right]L_X\le0,
$$

contradicting the original $X\to\infty$ and $L_X>0$. No thinning,
free-center mean or favorable tie selection enters the comparison.
CR21 and CR23 are sufficient conditions, not necessary ones; neither
has been proved.

### Any fixed quadratic lag is already absorbed by this height gain

For the same original sources put $z_{p,u}=t^2/B^{3/2}$. The exact
relation

$$
z_{p,u}=\frac tBv_{p,u}
\tag{CR24}
$$

and CR17 show that, for every fixed finite $C\ge0$ and fixed
$0<\kappa<1$, one common eventual start makes
$Cz_{p,u}\le\kappa v_{p,u}$ for every original label and tie. The same
comparison holds after applying the original positive window weights.
Thus the original full-height gain already permits any fixed quadratic
coefficient in the head upper target, including $1/2$ and larger
constants. No estimate of the own-price defect is needed for that
consumer. This is a relative comparison; it asserts no divergence of
either lag allowance.

The linear allowance is a supplier-relative application of the original
removal height and actual stock/PNT correspondence. The complete moving
finite-head upper condition, cofinal joint upper condition, original
PG15 exterior sign, boundary $\kappa=1$ and RH remain unproved. No
literature originality, new pressure decomposition or Lean verification
is claimed.

## A legal integer competitor leaves a strict curvature shortfall

Keep the original sources, labels and maximizing ties from CR1--CR4,
with $N=pu$, $A=B+t$, $B=\log u$, $t=\log p$ and
$u=N_A^{\rm str}$. Enlarge the common source start so that $B>11$.
Use the existing strict inventory and unrestricted own-price defect,
including the integer $1$ in its pressure domain. Put

$$
C=N_B^{\rm str},\qquad k=K(B)=\log C,\qquad Y=t+k,
\qquad L_{p,u}=F(N)-F(pC).
$$

Strict inventory nesting gives $C\mid u$. The original activation
calculation at clocks above $11$ gives $5040\mid C$, and $p\nmid u$
also gives $p\nmid C$. Thus $pC$ is a literal competitor in the
original complete domain of multiples of $5040p$, so $L_{p,u}\ge0$.
This uses the [original domain and strict-prefix
suppliers](../ArithSums/trureturing2026extrawindowpairing.md), N1/N4,
and PG1; neither CA adjacency nor GA1 is required.

Reuse PG2's concavity cost
$C_B(y)=f(B)+\lambda(B)(y-B)-f(y)$. The pressure optimizer at
$\lambda(B)$ is $C$, so the existing defect definition reads

$$
d_B(u)=W(C)-\lambda(B)k-W(u)+\lambda(B)B.
$$

Multiplication by the same absent prime adds $c_p=\log(1+1/p)$
to both divisor responses. Substitution into the actual competitor
loss therefore gives the exact same-source account

$$
t\lambda(B)-D_t(B)-d_B(u)=L_{p,u}+C_B(Y).
\tag{CR25}
$$

Its strictness has an integer witness. Write $r=u/C\in\mathbb N_{>0}$.
Because $p\nmid u$, $r\ne p$, and

$$
Y-B=\log(p/r),\qquad
|\log(p/r)|\ge\log(1+1/p)=c_p.
$$

For $r\ge p+1$ this follows directly; for $r\le p-1$ the stronger
bound is $\log(p/(p-1))>c_p$. Both $B$ and $Y$ are greater than $1$
and at most $A$, since $k\le B$. Integrating the decreasing curvature
$w=-\lambda'$ on the interval between $B$ and $Y$ gives
$C_B(Y)\ge w(A)(Y-B)^2/2$. Consequently every original label and tie
satisfies

$$
\boxed{
d_B(u)\le t\lambda(B)-D_t(B)-\frac{w(A)}2c_p^2
<t\lambda(B)-D_t(B).}
\tag{CR26}
$$

Even when $pC$ is another maximizing tie and $L_{p,u}=0$, the integer
gap remains strictly positive. The same original positive weights give

$$
\sum_{i<m}\delta_i s_{B_i}
\bigl[d_{B_i}(u_i)-t_i\lambda(B_i)+D_{t_i}(B_i)\bigr]
=-\sum_{i<m}\delta_i s_{B_i}
\bigl[L_{p_i,u_i}+C_{B_i}(Y_i)\bigr]<0.
$$

Thus the defect alone cannot supply the proposed lower bound
$d_B(u)\ge t\lambda(B)-D_t(B)$, even after full-window averaging.
This excludes that particular supply condition; it does not exclude a
comparison using the original height, reserve or another joint relation.
In the complete unrestricted same-core identity, CR25 instead gives

$$
\boxed{
-s_BI_\psi(B)=\frac t{\sqrt B}
+s_B\left[F(N)-\gamma+R_{\rm pp}(B)
-L_{p,u}-C_B(Y)-c_p\right].}
\tag{CR27}
$$

The original height occurs once. A coefficient-one comparison would
still have to pay $L_{p,u}+C_B(Y)+c_p$ from that height, the reserve or
a proved same-source signed estimate. CR26's strict gap has no fixed
normalized positive lower bound asserted here. The complete
coefficient-one condition, CR21/CR23, PG15/J and RH remain unproved.
This is an application of the named suppliers, without a new generic
pressure theorem, literature originality claim or Lean verification.
