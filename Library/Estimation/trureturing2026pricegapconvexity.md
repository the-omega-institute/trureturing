---
bibkey: trureturing2026pricegapconvexity
authors: trureturing research synthesis
year: 2026
title: Actual Robin price gaps, forced-core tail records and the selected-sign boundary
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/cf052b34b8b275b74ea62a8860481c927eb77daa/Library/Estimation/trureturing2026pricegapconvexity.md
claim: Under the original source-window hypotheses, the complete selected response retains actual price-gap costs; every inactive-forced-prime core is a strict all-integer right-tail record with original-exponent own-size excess. A synthetic positive-reference model excludes height-and-envelope plus numerical full-Q reasoning alone. A cited unrefereed density theorem extends the original high-frequency range and complete compensated clock transport. Exact total-clock pressure raises the pure-future joint margin throughout the original range. Actual favorable slack and RH remain unproved.
strata_touched:
  - D5/S3/Analytic/Variational/JointReciprocalFunctional
license: Apache-2.0
triage: anchor
---

# Actual price gaps and the same-source signed estimate

Assume the qualifying original window in
[N1--N2 and PT1--PT11](../ArithSums/trureturing2026extrawindowpairing.md).
These sources belong to the supplied RH-failure route. This is a
supplier-relative paper application, with no literature priority claim or
proof of RH. The scalar-root existence and uniqueness, explicit smooth
normalized profile, and sharp attained JVM1--JVM2 analytic variational
values are formalized in
`D5/S3/Analytic/Variational/JointReciprocalFunctional.lean` for every
$0<b\le1$, over the full bounded positive almost everywhere measurable
class. This formalization does not verify the remaining source-window,
arithmetic, strict-gain or RH claims in this note. The existing source construction,
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

## Exact linear compensation loses absolute height summability

Fix one original qualifying full window and one allowed assignment of
maximizing ties. Keep every $0\le i<m$, the original positive
$\delta_i=t_{i+1}-t_i$, the last boundary label $p_m$,
$A_i=B_i+t_i$ and the exact actual relation $K(A_i)=B_i$.
Fix $\kappa>0$. This section examines a way of incorporating the
linear allowance into the zero coefficients; it does not redefine
the complete upper enclosure $U$ in CR21/CR23.

Use the [original complete coefficient (M1)](../ArithSums/nicolas2025comparison.md#a-fixed-positive-scale-mixture-cannot-remove-the-functional-equation-weight),
the same elementary correction $r_B=s_BR_{\rm elem}(B)$, and
$Q=K-\psi$ with weak, right-continuous $\psi$. For real $x>1$, let
$\Lambda_{\mathbb R}(x)=\log q$ at an actual integer prime power
$x=q^j$, and zero otherwise. The classical symmetric-height formula
retains the endpoint term:

$$
\psi(A)-A
=-\lim_{T\to\infty}\sum_{|\operatorname{Im}\rho|\le T}
m_\rho\frac{A^\rho}{\rho}
-\log(2\pi)-\frac12\log(1-A^{-2})
+\frac12\Lambda_{\mathbb R}(A).
$$

The actual relation $t_i=A_i-\psi(A_i)-Q(A_i)$ thus forces the
compensated coefficient

$$
C_{X,\kappa}(\rho)=\sum_{i<m}\delta_i
\left[s_{B_i}F_{B_i}(\rho)
-\frac{\kappa A_i^\rho}{\sqrt{B_i}\rho}\right].
\tag{CR28}
$$

It yields the complete signed account

$$
\begin{aligned}
\sum_{i<m}\delta_i\left[-s_{B_i}I_\psi(B_i)
-\frac{\kappa t_i}{\sqrt{B_i}}\right]
={}&\lim_{T\to\infty}\sum_{|\operatorname{Im}\rho|\le T}
m_\rho C_{X,\kappa}(\rho)\\
&+\sum_{i<m}\delta_i\left\{
r_{B_i}+\frac{\kappa}{\sqrt{B_i}}
\left[Q(A_i)-\log(2\pi)-\frac12\log(1-A_i^{-2})
+\frac12\Lambda_{\mathbb R}(A_i)\right]\right\}.
\end{aligned}
\tag{CR29}
$$

All actual prime-power corrections, real parts, multiplicities and
elementary terms remain. The integral clock is still $B_i$; no
transport of $I_\psi(B_i)$ to $A_i$ or artificial remainder is used.

### Common signs on the actual dependent phase torus

For an actual zero $\rho=\beta+i\tau$, $\tau>0$, put
$D_{X,\kappa}(\rho)=2\operatorname{Re}C_{X,\kappa}(\rho)$,
$a_i=\log A_i>0$ and $\omega_i=\delta_i/\sqrt{B_i}>0$.
The original coefficient estimate H1--H5 is
$F_{B_i}(\beta+i\tau)=O_{B_i}(\tau^{-2})$, uniformly for
$0<\beta<1$. Directly expanding the added coefficient gives

$$
D_{X,\kappa}(\rho)
=-\frac{2\kappa}{\tau}
\sum_{i<m}\omega_i A_i^\beta\sin(\tau a_i)
+O_{X,\kappa,\mathbf u}(\tau^{-2}).
\tag{CR30}
$$

The error is summable over all actual zeros with their multiplicities.
The new leading term instead has decay $1/\tau$.

Reuse [Ford--Zaharescu's unconditional fixed smooth-test
theorem](../Weil/fordzaharescu2005zerophases.md), Corollary 2.
For every fixed nonzero real $\xi$, its exponential character test at
frequency $|\xi|/(2\pi)$ gives

$$
\sum_{0<\tau\le T}m_\rho e^{i\xi\tau}=o(N(T)),
\qquad N(T)\sim\frac{T\log T}{2\pi}.
$$

Keep all frequency relations by defining the compact subgroup

$$
H=\overline{\{r(a_0,\ldots,a_{m-1})\bmod2\pi:r\in\mathbb R\}}.
$$

For an integer character $\mathbf h$, a zero dot product
$\mathbf h\cdot\mathbf a=0$ gives the value $1$ identically;
a nonzero dot product gives normalized average zero by the cited
theorem. These are exactly the Fourier coefficients of Haar
probability on $H$. Character density therefore shows that the actual
vectors $\tau\mathbf a\bmod2\pi$, counted with multiplicity,
equidistribute on $H$. Neither independence of the $a_i$ nor LI of
zero ordinates is assumed.

Choose a sufficiently small positive $r_0$ so that
$0<r_0a_i<\pi/2$ for every $i<m$. A relative open neighborhood
$\Omega_+$ of this actual flow point has
$\sin\theta_i\ge\eta>0$ simultaneously for every coordinate;
$\Omega_-=-\Omega_+$ has all opposite inequalities. Both have
positive Haar measure. Continuous nonnegative bumps supported inside
them give positive proportions of actual zeros, without an interval
indicator or a boundary-measure assumption.

At the first region $1\le A_i^\beta\le A_i$ and all original weights
are positive. Hence CR30 gives $D_{X,\kappa}(\rho)\le-c/\tau$
at all sufficiently high zeros in that region, for some $c>0$.
The second region gives $D_{X,\kappa}(\rho)\ge c'/\tau$.
The real-part factors cannot destroy these common signs.

### Both positive and negative full tail budgets diverge

A phase region with multiplicity count
$N_\Omega(T)\gg T\log T$ satisfies, by partial summation,

$$
\sum_{\substack{0<\tau\le T\\\tau\mathbf a\in\Omega}}
\frac{m_\rho}{\tau}\gg(\log T)^2.
$$

The same zero count gives the matching upper bound for all zeros.
Writing $x_+=\max(x,0)$, CR30 consequently gives

$$
\boxed{
\begin{aligned}
\sum_{0<\tau\le T}m_\rho(D_{X,\kappa}(\rho))_+
&\asymp_{X,\kappa,\mathbf u}(\log T)^2,\\
\sum_{0<\tau\le T}m_\rho(-D_{X,\kappa}(\rho))_+
&\asymp_{X,\kappa,\mathbf u}(\log T)^2.
\end{aligned}}
\tag{CR31}
$$

For a fixed window there are finitely many labels and maximizing-tie
assignments. Taking minima of the positive constants and maxima of
the starts gives common bounds over every allowed assignment in that
fixed window. No rate uniform in jointly growing $X,T$ is supplied.

Thus exact linear compensation, followed by full-window aggregation
and conjugate pairing, cannot be paid by an absolute or positive-part
infinite suffix budget. Removing any finite individual heads $T_i$
leaves the same divergence beyond $\max_iT_i$. The finite deterministic
terms in CR29 cannot pay this infinite budget. In particular the added
$1/\rho$ coefficient cannot use the original $1/\tau^2$ absolute
suffix supplier without a new signed estimate.

The prescribed symmetric, signed height sum in CR29 still converges
by the actual explicit formula; its two divergent sign parts cancel
conditionally. This conclusion does not exclude the original complete
$U$, signed height-block or contour estimates, or a finite truncation
with fully paid errors. At $\kappa=0$ the added coefficient vanishes
and the original response remains absolutely summable. The argument
uses the actual original window, not a synthetic spectrum, and reuses
the existing coefficient, phase and zero-count suppliers. It asserts
neither literature originality nor Lean verification. CR21/CR23,
PG15/J and RH remain unproved.

## A selected-height supplier pays the complete signed compensated suffix

Keep every original source and maximizing tie from CR17--CR24,
$A=B+t$, $B=\log u$, $t=\log p$, $s_B=\sqrt B\log B$, and the
original full window with all positive $\delta_i$, $i<m$, and last
boundary label $p_m$. Fix $0\le\kappa<1$. The [Cully-Hugill--Johnston
selected-height supplier](../Analytic/cullyhugilljohnston2026truncation.md),
Theorem 1.2 and Table 1 of arXiv:2402.04272v3, is applied directly.
It uses weak $\psi$ and the actual zeros with their real parts and
multiplicities; no new generic truncation theorem is asserted here.

The row $\alpha=1/2$, $\omega=1$, $M=19.81$ requires
$A\ge\exp(10^{13})$. For
$Y_A=(\sqrt A-4)/4$, the strict supplier bounds
$\max\{51,\log^2A\}<Y_A<(\sqrt A-2)/4$ hold on that domain.
Thus each actual $A$ admits a cutoff

$$
\tau_A\in\left[\frac{\sqrt A-4}{4},
\frac{\sqrt A-4}{2}\right],\qquad
\psi(A)=A-2\operatorname{Re}\sum_{0<\operatorname{Im}\rho\le\tau_A}
m_\rho\frac{A^\rho}{\rho}+e_A,
\qquad |e_A|\le\frac{79.24A}{\sqrt A-4}.
\tag{CR32}
$$

Uniform original-source escape supplies one common sufficiently large
witness start after which every original label and tie meets this
supplier threshold. No numeric witness start is supplied. The
existence of $\tau_A$ cannot be strengthened to arbitrary prescribed
heights or a common favorable height for different sources.

### The degree-one endpoint is paid in the same real paired ordering

Let $q(A)=\log(2\pi)+\tfrac12\log(1-A^{-2})$ and use CR29's
$\Lambda_{\mathbb R}$. The real conjugate-pair tail is interpreted
by the same symmetric-height limit as the complete explicit formula:

$$
H_A(\tau)=\lim_{T\to\infty}2\operatorname{Re}
\sum_{\tau<\operatorname{Im}\rho\le T}
m_\rho\frac{A^\rho}{\rho}.
$$

Comparing the complete weak-$\psi$ formula to CR32 gives exactly

$$
H_A(\tau_A)=-e_A-q(A)+\frac12\Lambda_{\mathbb R}(A),
\qquad
\left|H_A(\tau_A)+q(A)-\frac12\Lambda_{\mathbb R}(A)\right|
\le\frac{79.24A}{\sqrt A-4}.
\tag{CR33}
$$

The half-prime-power endpoint and elementary terms are retained.
This is a paired real tail contract; it asserts no ordinary complex
positive-ordinate half-sum convergence at prime powers. No estimate
of the actual distance to the nearest other prime power is needed:
the cited theorem pays the complete weak-$\psi$ error in its domain.

### Combine both complete suffixes exactly once

Reuse the [existing full signed suffix J4](../ArithSums/nicolas2025comparison.md#a-signed-infinite-height-allowance-from-the-existing-landau-formula)
at the same actual $B$ and selected cutoff $\tau_A$. Write
$\mathcal J(B)=\log(2B)\log\log(3B)$ and

$$
\begin{aligned}
2s_B\operatorname{Re}\sum_{\operatorname{Im}\rho>\tau_A}
m_\rho F_B(\rho)&=-\mu_B(\tau_A)+e_F(B,\tau_A),\\
\mu_B(\tau)&=\frac{(1+1/\log B)\Lambda_{\mathbb R}(B)}
{\pi\sqrt B\,\tau}\ge0,\\
|e_F(B,\tau)|&\le\varepsilon_F(B,\tau),\\
\varepsilon_F(B,\tau)&=C_F\left[
\frac{\sqrt B[\mathcal J(B)+\log(2\tau)]}{\tau^2}
+\frac{\log B+1}{\sqrt B\,\tau}\right].
\end{aligned}
$$

Here $C_F$ is the existing supplier's uniform constant, without a
certified numerical value. Its full coefficient approximation and
height-integration errors are already paid once in $e_F$.
The favorable $-\mu_B$ retains its sign.

For each allowed assignment choose the individual cutoffs $\tau_i$
supplied by CR32 at the actual $A_i$. Define the actual compensated
suffix, with no original label removed,

$$
\mathcal R_X(\boldsymbol\tau)=\sum_{i<m}\delta_i
\left[
2s_{B_i}\operatorname{Re}\sum_{\operatorname{Im}\rho>\tau_i}
m_\rho F_{B_i}(\rho)
-\frac{\kappa}{\sqrt{B_i}}H_{A_i}(\tau_i)\right].
$$

CR33 and the complete original J4 contract therefore give

$$
\boxed{
\begin{aligned}
\left|\mathcal R_X(\boldsymbol\tau)
-\sum_{i<m}\delta_i\left[
-\mu_{B_i}(\tau_i)
+\frac{\kappa}{\sqrt{B_i}}
\left(q(A_i)-\frac12\Lambda_{\mathbb R}(A_i)\right)\right]\right|
\le{}&\sum_{i<m}\delta_i\left[
\varepsilon_F(B_i,\tau_i)
+\frac{79.24\kappa A_i}{\sqrt{B_i}(\sqrt{A_i}-4)}\right].
\end{aligned}}
\tag{CR34}
$$

All actual real parts and multiplicities are unchanged. No replacement
of $1/\rho$ by $1/(i\operatorname{Im}\rho)$ is made, so no such
approximation error is added. The two supplier errors occur exactly
once. The primary pole-and-trivial-zero term $q(A)$ is distinct from
the integrated response's $R_{\rm elem}(B)$.

CR17 gives $\tau_i\asymp\sqrt{A_i}\asymp\sqrt{B_i}$ uniformly,
$\varepsilon_F(B_i,\tau_i)=o_X(1)$,
$\mu_{B_i}(\tau_i)=o_X(1)$, and
$[|q(A_i)|+\Lambda_{\mathbb R}(A_i)]/\sqrt{B_i}=o_X(1)$.
Also

$$
\frac{79.24\kappa A_i}{\sqrt{B_i}(\sqrt{A_i}-4)}
=79.24\kappa\frac{\sqrt{A_i/B_i}}{1-4/\sqrt{A_i}}
=79.24\kappa+o_X(1).
$$

Applying the original positive weights to these uniform pointwise
allowances gives

$$
\boxed{|
\mathcal R_X(\boldsymbol\tau)|
\le[79.24\kappa+o_X(1)]L_X.}
\tag{CR35}
$$

For each fixed $0\le\kappa<1$, beyond one common unknown source and
analytic start, every qualifying original full window and every
allowed tie assignment admit these individual cutoffs and complete
contracts. The error is uniform in all original labels and ties, not
merely for one fixed window. Its positive weighted sum needs no
separate estimate for the number of labels. Eventually $80L_X$ pays
this suffix alone; it is not the complete upper target's total budget.
The supplied constant payment is $O(1)$ per unit original weight,
not a vanishing bound. At $\kappa=0$, the degree-one term disappears
and there is no need to raise the existing J6 cutoff for its sake.

### The head and actual stock remain a joint obligation

The selected cutoffs are of order $\sqrt B$, larger than the original
degree-two cutoff $B^{1/4}\log B$. The classical actual zero count
puts $\Theta(\sqrt B\log B)$ positive-ordinate terms in the new head,
compared with $\Theta(B^{1/4}\log^2B)$ at the original cut. This
states the item counts, not the cost of certifying their real parts,
multiplicities or numerical enclosures.

Define the actual compensated finite head at these same individual
selected cutoffs by

$$
\mathcal H_{X,\kappa}(\boldsymbol\tau)
=2\operatorname{Re}\sum_{i<m}\delta_i
\sum_{0<\operatorname{Im}\rho\le\tau_i}m_\rho
\left[s_{B_i}F_{B_i}(\rho)
-\frac{\kappa A_i^\rho}{\sqrt{B_i}\rho}\right].
$$

Adding CR34's suffix to this head and CR29's actual deterministic
terms gives the exact account

$$
\begin{aligned}
\sum_{i<m}\delta_i\left[-s_{B_i}I_\psi(B_i)
-\frac{\kappa t_i}{\sqrt{B_i}}\right]
={}&\mathcal H_{X,\kappa}(\boldsymbol\tau)\\
&+\sum_{i<m}\delta_i\left[
r_{B_i}+\frac{\kappa Q(A_i)}{\sqrt{B_i}}
-\mu_{B_i}(\tau_i)\right]+\mathfrak e_{X,\kappa},\\
|\mathfrak e_{X,\kappa}|\le{}&
\sum_{i<m}\delta_i\left[
\varepsilon_F(B_i,\tau_i)
+\frac{79.24\kappa A_i}{\sqrt{B_i}(\sqrt{A_i}-4)}\right],
\qquad r_B=s_BR_{\rm elem}(B).
\end{aligned}
\tag{CR36}
$$

The degree-one $q$ and half-prime-power terms cancel algebraically
between the explicitly retained suffix center and CR29's conversion
of $t_i=A_i-K(A_i)$; they are not omitted. The original integrated
elementary correction $r_{B_i}$ and actual stock $Q(A_i)$ remain.
CR36 pays no error from numerically enclosing the finite head: such
errors still require their own complete contracts.

Small suffix errors do not make this signed head-and-stock value
favorable. One cannot choose a different favorable head cutoff and
assume it is compatible with the supplier-selected heights. CR34--35
pay no actual stock or complete-head sign, provide no common height
for separate pointwise applications, and do not prove CR21/CR23,
PG15/J or RH. This is a supplier-relative application of the cited
truncation theorem and existing J4, without a literature-originality
claim, a repeated generic tail theorem or Lean verification.

## The existing full-real normal form pays the stock term

Keep all original fixed $b,d$, qualifying witnesses, full windows,
positive weights, final boundary labels and maximizing ties from
CR17--CR36. The [archived workload supplier's full-real normal form
and strict-endpoint transfer](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events)
apply to the identical actual inventory $K$, weak $\psi$ and price.
Reuse that statement directly:

$$
Q(x)=K(x)-\psi(x)=(\sqrt2-1)\sqrt x+o(\sqrt x).
$$

This holds through activation events; no regular-return membership is
asserted for the original $A_i$ or $B_i$. CR17 and uniform source escape
therefore give, for every original label and tie,

$$
\frac{Q(A_i)}{\sqrt{B_i}}
=\frac{Q(A_i)}{\sqrt{A_i}}\sqrt{\frac{A_i}{B_i}}
=\sqrt2-1+o_X(1).
\tag{CR37}
$$

The real start in the supplier and the original source start are both
existential. Uniformity here follows from a full-real asymptotic and
uniform $A_i/B_i\to1$; no distribution of the selected clocks or
exceptional-center exclusion is needed.

The [existing elementary bound](../ArithSums/nicolas2025comparison.md#paying-the-thresholds-and-retaining-the-signed-obligation)
gives $0<r_{B_i}\le\log(2\pi)/\sqrt{B_i}=o_X(1)$.
CR34 retains $\mu_{B_i}(\tau_i)\ge0$ and its uniform $o_X(1)$
bound at the CR32-selected individual cutoffs. Thus for every fixed
$0\le\kappa<1$, the full deterministic term in CR36 is paid:

$$
\boxed{
\sum_{i<m}\delta_i
\left[r_{B_i}+\frac{\kappa Q(A_i)}{\sqrt{B_i}}
-\mu_{B_i}(\tau_i)\right]
=\left[\kappa(\sqrt2-1)+o_X(1)\right]L_X.}
\tag{CR38}
$$

This includes the actual signed stock, all higher layers and endpoint
ties; it does not replace them by separately attainable optimizers.
The positive weights sum to $L_X$, so there is no cost proportional to
the number of labels.

Together with CR36's complete suffix contract, this supplies the
one-sided enclosure

$$
\boxed{
\sum_{i<m}\delta_i\left[-s_{B_i}I_\psi(B_i)
-\frac{\kappa t_i}{\sqrt{B_i}}\right]
\le\mathcal H_{X,\kappa}(\boldsymbol\tau)
+\left[\kappa(79.24+\sqrt2-1)+o_X(1)\right]L_X.}
\tag{CR39}
$$

Each suffix error is paid once and the favorable $-\mu$ is retained.
Exact coefficients create no numerical enclosure error; if the head
is numerically enclosed, every such error must be added separately.
CR39 pays the deterministic term that was still retained in CR36;
it supplies no favorable sign of the head.

For the same fixed $\kappa$, an eventual cofinal-full-window upper
bound $\mathcal H_{X,\kappa}(\boldsymbol\tau)\le M_H L_X$,
with one fixed finite $M_H$, every allowed tie assignment and cutoffs
satisfying the complete CR32--CR34 contracts, would now pay CR23
with a fixed enlarged constant. This is only the unpaid consumer of
CR39, not a new RH criterion or an established head estimate.
The head and tail must use the same individually selected cutoff for
each label, with every maximizing tie retained; independently favorable
choices do not supply those contracts.

The full-real normal form is existing arithmetic, directly credited
to the archived primary and its historical references. This addition
only pays its actual CR36 consumer after the explicit strict-endpoint
and same-clock correspondence; it does not reprove that normal form,
claim literature originality or supply Lean verification. The
complete signed head upper estimate, CR21/CR23, PG15/J and RH remain
unproved.


## The prime interval supplier and both competitor costs control actual stock

Keep every original source, label and maximizing tie from CR17--CR27,
$N=pu$, $A=B+t$, $B=\log u$, $t=\log p$, $u=N_A^{\rm str}$,
$K(A)=B$. In particular $t/B\to0$ uniformly. Write

$$
C=N_B^{\rm str},\qquad k=K(B),\qquad D=B-k=K(A)-K(B)\ge0,
\qquad Y=t+k=A-D.
$$

Here $D$ is actual added layer mass on $[B,A)$, distinct from the
own-price defect $d_B(u)$, CR25's integer loss $L_{p,u}$ and the
original source-window ceiling. All its simultaneous activations retain
their individual $\log p$ masses.

### Reuse a uniform prime interval bound and the complete frontier mass

The [Ramaré--Schlage-Puchta interval supplier](../Scale/ramare2008bruntitchmarsh.md),
Theorem 1.1, is used directly. The existing first-frontier inequalities
$1/(q+1)<\log(1+1/q)<1/q$ place each first-layer activation clock
$a_{q,1}$ strictly between $q$ and $q+1$. Thus activations in
$[B,B+z)$ come from actual primes in $(B-1,B+z)$.

For $\sqrt B\le z\le B/2$, round that prime interval outward to
integer endpoints. Its length is $z+O(1)$, its primes have
$\log q\le\log(2B)$, and the uniform cited theorem gives a
first-layer mass at most

$$
\frac{2[z+O(1)]\log(2B)}{\log[z+O(1)]+3.53}\le cz
$$

beyond one common real start, for each fixed $c>4$. Uniformity follows
from $\log z\ge\tfrac12\log B$. For $0\le z<\sqrt B$,
monotonicity bounds this mass by $c\sqrt B$.

The [existing full-real frontier normal form](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events)
and the [ordinary prime-square decomposition](../ArithSums/nicolas2025comparison.md#what-remains-after-the-prime-square-contribution)
already pay the entire higher actual layer mass as $O(\sqrt x)$,
including the strict endpoints and all growing indices. Indeed the
strict full-real inventory is $K(x)=\psi(x)+(\sqrt2-1)\sqrt x+o(\sqrt x)$,
its first layer is $\vartheta(x)+O(\log x)$, and
$\psi(x)-\vartheta(x)=\sqrt x+o(\sqrt x)$. The higher actual mass
is consequently $(\sqrt2+o(1))\sqrt x$. This reuses the complete
frontier estimates; no fixed-layer expansion is summed over infinitely
many indices. At $x=B+z\le3B/2$ their full increment is therefore
$O(\sqrt B)$. We obtain a finite $H_c$ and common real start with

$$
\boxed{
K(B+z)-K(B)\le cz+H_c\sqrt B
\quad(B\text{ beyond the start},\ 0\le z\le B/2).}
\tag{CR40}
$$

The same normal form gives $|Q(x)|\le C_Q\sqrt x$ eventually.
That bound is an existing supplier consequence, not new arithmetic.
No numerical values for $H_c,C_Q$ or the common start are certified.

### Keep the layer work and the legal competitor's concavity cost

The original CR25 account is

$$
d_B(u)+L_{p,u}+C_B(Y)=E_t,
\qquad E_t=t\lambda(B)-D_t(B),\qquad L_{p,u}\ge0.
$$

Reuse $\lambda(x)=1/(x\log x)$ and its decreasing positive curvature
$w=-\lambda'$. The actual finite layer account, including layers tied
at $B$ and excluding those tied at $A$, reads

$$
d_B(u)=\int_{[B,A)}[\lambda(B)-\lambda(v)]\,dK(v).
$$

Define $J=\int_{[B,A)}(v-B)\,dK(v)$. The complete event measure is
used in both integrals. Then

$$
d_B(u)\ge w(A)J,\qquad
C_B(Y)\ge\frac{w(A)}2(t-D)^2,\qquad
E_t\le\frac{w(B)t^2}2.
$$

The concavity estimate is in its original domain: CR25 gives
$B,Y>1$ and $B,Y\le A$. Hence

$$
\boxed{2J+(t-D)^2\le\mathfrak r t^2,
\qquad \mathfrak r=\frac{w(B)}{w(A)}\longrightarrow1.}
\tag{CR41}
$$

The convergence is uniform in every original label and tie by CR17.
The source height and prime-power reserve have not been spent here.

Translate the actual layer measure on $[B,A)$ to $\mu$ on $[0,t)$,
with total mass $D$, and set $h=H_c\sqrt B$. Eventually $t\le B/2$,
so CR40 gives $\mu([0,z))\le cz+h$ for $0\le z\le t$.
Finite integration gives

$$
J=\int_0^t[D-\mu([0,z))]\,dz
\ge\frac{(D-h)_+^2}{2c}.
$$

The last step integrates the positive lower envelope
$[D-h-cz]_+$; its support lies in $[0,t]$ since $D\le ct+h$.
Endpoint atoms do not alter this ordinary integral. Thus

$$
\frac{(D-h)_+^2}{c}+(t-D)^2\le\mathfrak r t^2.
$$

Using $(D-h)_+^2\ge D^2-2Dh$ and solving the resulting quadratic,

$$
\begin{aligned}
D&\le\frac c{c+1}\left[
 t+\frac hc+\sqrt{\left(t+\frac hc\right)^2
 +\frac{c+1}c(\mathfrak r-1)t^2}\right]\\
&\le\left[\frac{2c}{c+1}+\frac{\mathfrak r-1}2\right]t
 +\frac{2H_c}{c+1}\sqrt B.
\end{aligned}
\tag{CR42}
$$

Here $\mathfrak r\ge1$, and the second line uses
$\sqrt{v^2+s}\le v+s/(2v)$ with $v\ge t>0$.
For each fixed $\eta>0$, choose $c>4$ sufficiently close to $4$
and then one common source start. Since $2c/(c+1)\to8/5$,

$$
\boxed{
B-K(B)\le(8/5+\eta)t+C_\eta\sqrt B.}
\tag{CR43}
$$

This uses both retained costs in CR41. A bound on the price defect
alone does not supply the displayed coefficient by this argument.
The $\sqrt B$ allowance is essential; no divergence of $t/\sqrt B$
is assumed.

### The actual prime-error interaction is paid on the full window

The exact same-source identities are

$$
B-\psi(B)=D+Q(B),\qquad
\psi(A)-\psi(B)-t=D-t+Q(B)-Q(A).
$$

Since $A/B\to1$ and $|Q(x)|\le C_Q\sqrt x$ eventually, CR43 gives

$$
\begin{aligned}
B-\psi(B)&\le(8/5+\eta)t+C'_\eta\sqrt B,\\
\psi(A)-\psi(B)-t&\le(3/5+\eta)t+C''_\eta\sqrt B,\\
\sum_{i<m}\delta_i\frac{\psi(A_i)-\psi(B_i)-t_i}{\sqrt{B_i}}
&\le(3/5+\eta)V_X^{\rm lag}+C''_\eta L_X.
\end{aligned}
\tag{CR44}
$$

One common sufficiently large start covers every original label,
full window and maximizing-tie assignment. All fixed constants may
depend on $\eta$ and the suppliers; they do not depend on a selected
label or tie. No favorable sampling, new source or thinning is used.
This is a supplier-relative actual arithmetic estimate, without a
literature-originality or Lean-verification claim. CR44 controls one
signed prime-error interaction, not the full original integral or its
finite head; CR21/CR23, PG15/J and RH remain unproved.


## A single core-selected height pays the complete compensation change

Keep CR40--44's actual sources and all original window conventions.
Fix $0<\kappa<1$ and $0<a<5\kappa/8$ once. Choose a fixed
$\eta>0$ with $a(8/5+\eta)\le\kappa$. Define, retaining every
actual zero's real part and multiplicity,

$$
Z_x(T)=2\operatorname{Re}\sum_{0<\operatorname{Im}\rho\le T}
m_\rho\frac{x^\rho}{\rho}.
$$

Apply the [existing CHJ selected-height supplier](../Analytic/cullyhugilljohnston2026truncation.md)
directly at the same actual core clock $B$, with
$Y_B=(\sqrt B-4)/4$. Beyond one common unknown source start,
$B\ge\exp(10^{13})$ and the strict supplier domain holds. It gives
one individual height $\tau_B\in[Y_B,2Y_B]$ such that

$$
\psi(B)=B-Z_B(\tau_B)+e_B,
\qquad |e_B|\le\frac{79.24B}{\sqrt B-4}\le80\sqrt B.
$$

Combining this actual error contract with CR44, rather than choosing
an independently favorable head, yields

$$
\boxed{
\frac{aZ_B(\tau_B)-\kappa t}{\sqrt B}
\le a(C'_\eta+80).}
\tag{CR45}
$$

No $A$-selected height is imposed in this route. In particular these
$B$-selected heights are not asserted to satisfy CR34's separate
$A$-tail contracts.

### Pay the original compensation, its change and all deterministic terms jointly

For one label define the actual finite heads at one common *individual*
height $T$ by

$$
\begin{aligned}
H_{A,\kappa}(T)&=2\operatorname{Re}
\sum_{0<\operatorname{Im}\rho\le T}m_\rho
\left[s_BF_B(\rho)-\frac{\kappa A^\rho}{\sqrt B\rho}\right],\\
H_{B,a}(T)&=2\operatorname{Re}
\sum_{0<\operatorname{Im}\rho\le T}m_\rho
\left[s_BF_B(\rho)-\frac{aB^\rho}{\sqrt B\rho}\right].
\end{aligned}
$$

The first is the original CR28 compensation; the second is a comparison
head whose entire change is retained below. Let $S_{A,\kappa}(T)$ be
the original compensated suffix in CR29's real symmetric-height ordering.
It asserts no ordinary complex positive-ordinate limit. Put

$$
\mathcal D_{A,\kappa}=r_B+\frac\kappa{\sqrt B}
\left[Q(A)-q(A)+\tfrac12\Lambda_{\mathbb R}(A)\right].
$$

The complete original account is

$$
H_{A,\kappa}(T)+S_{A,\kappa}(T)+\mathcal D_{A,\kappa}
=-s_BI_\psi(B)-\kappa t/\sqrt B.
$$

Subtract the comparison head at that same height. With the *original*
full degree-two suffix
$T_F(B,T)=2s_B\operatorname{Re}\sum_{\operatorname{Im}\rho>T}m_\rho F_B(\rho)$,
the exact result is

$$
\begin{aligned}
S_{A,\kappa}(T)+H_{A,\kappa}(T)-H_{B,a}(T)
+\mathcal D_{A,\kappa}
=T_F(B,T)+r_B+\frac{aZ_B(T)-\kappa t}{\sqrt B}.
\end{aligned}
$$

The actual stock, pole/trivial-zero and half-prime-power terms cancel
only within this joint equality; none is dropped separately.
Reuse CR34's complete original J4 account
$T_F(B,T)=-\mu_B(T)+e_F(B,T)$ with
$\mu_B\ge0$ and $|e_F|\le\varepsilon_F$.
At $T=\tau_B\asymp\sqrt B$, its full allowance is $o_X(1)$
uniformly, as is $r_B$. CR45 therefore pays, with a fixed finite
constant $C_{\eta,a}$,

$$
\boxed{
\sum_{i<m}\delta_i\left[
 S_{A_i,\kappa}(\tau_i)+H_{A_i,\kappa}(\tau_i)
 -H_{B_i,a}(\tau_i)+\mathcal D_{A_i,\kappa}\right]
\le C_{\eta,a}L_X.}
\tag{CR46}
$$

This jointly pays the original $A$-compensated suffix, its complete
finite-head change to $B$-compensation and every deterministic term.
It does not assert favorable signs or separate small bounds for those
three pieces. It requires no intersection of favorable height sets.
Every sufficiently large qualifying original full window and every
tie assignment admit individual $B$-selected heights; there is no
common-height assertion across different cores.

### Retain a complete original-coefficient upper enclosure

At these heights use the complete original $F_B$ enclosure

$$
U(B,\tau_B)=2s_B\operatorname{Re}
\sum_{0<\operatorname{Im}\rho\le\tau_B}m_\rho F_B(\rho)
+r_B-\mu_B(\tau_B)+\varepsilon_F(B,\tau_B)
\ge-s_BI_\psi(B).
$$

Exact coefficients introduce no coefficient approximation error.
CR45 and the same signed suffix contract give

$$
\boxed{
\sum_{i<m}\delta_iU(B_i,\tau_i)
\le\kappa V_X^{\rm lag}+C_{\eta,a}L_X
+\sum_{i<m}\delta_iH_{B_i,a}(\tau_i).}
\tag{CR47}
$$

The final same-clock compensated head remains unpaid. A sufficient
cofinal-full-window upper bound for it must retain every maximizing
tie, these actual height contracts, all real parts and multiplicities,
and any numerical enclosure errors. None is supplied here.

CR43's actual arithmetic bound permits the fixed comparison coefficient
$a<5\kappa/8$ and makes the joint payment without presuming a favorable
head or a separate $A$-tail estimate. It does not replace the original
coefficient, count the source height twice, expend the reserve or
assume self-tangency of the cores. The named prime interval theorem,
CHJ supplier and original J4 are directly reused. This is a
supplier-relative paper application with no originality or Lean claim;
the complete CR21/CR23 upper estimate, PG15/J and RH remain unproved.

### A sharper zero-free strip still cannot pay the same-cutoff head

The recent [Liu zero-free supplier](../Analytic/liu2026quasirh.md) reports
the boundary

$$
\beta_0=\frac{1507-2\sqrt{921}}{1653}=0.874957\ldots
$$

for the real parts of the nontrivial zeros of the zeta function. Treat
this as a supplier premise only; its external proof and reported Lean
formalization have not been independently built here. Even granting this
stronger boundary, a direct absolute estimate does not close CR47.

Indeed, the existing coefficient estimate (U2) gives, for
$\rho=\beta+i\gamma$ with $\gamma\ge4$,

$$
|F_B(\rho)|
\le \frac{2w(B)B^{\beta-1}}{\gamma^2}
\le \frac{2w(B)B^{\beta_0-1}}{\gamma^2}.
$$

The classical zero count makes
$\sum_{4\le\gamma\le T}m_\rho/\gamma^2=O(1)$ uniformly in $T$;
the finitely many zeros below $4$ obey the same $B^{\beta_0-1}$ scale
with a supplier-dependent constant. Since
$s_B=\sqrt B\log B$ and
$w(B)=(1+\log B)/(\log B)^2$,

$$
s_B\sum_{0<\gamma\le T}m_\rho|F_B(\rho)|
\ll B^{\beta_0-1/2}.
$$

For the comparison term in $H_{B,a}$, the zero-count estimate
$\sum_{0<\gamma\le T}m_\rho/\gamma=O((\log T)^2)$ gives

$$
\frac{a}{\sqrt B}
\sum_{0<\gamma\le T}m_\rho\left|\frac{B^\rho}{\rho}\right|
\ll aB^{\beta_0-1/2}(\log T)^2.
$$

Thus at the actual $T=\tau_B\asymp\sqrt B$,

$$
|H_{B,a}(\tau_B)|
\ll (1+a(\log B)^2)B^{\beta_0-1/2}
=O\!\left(B^{0.374957\ldots}(\log B)^2\right).
$$

This is an upper envelope, not a claim that the signed head has this
size. It proves only that a zero-free half-plane, even with the reported
improvement, cannot replace the missing signed cancellation. The required
input remains a same-height upper bound retaining the actual phases,
real parts and multiplicities; improving a fixed strip exponent above
$1/2$ does not supply that bound.

## A fixed-zero obstruction to individual complex-modulus budgets

Keep H1's one fixed exponent $\eta$, its $d>0$, every original full
window, every maximizing tie, the positive weights $\delta_i$, and the
actual core clocks $B_i$. Assume RH failure and put

$$
\Theta=\sup_{\gamma>0}\operatorname{Re}\rho\in(1/2,1],\qquad
1-\Theta<\eta<1/2,\qquad
\ell_X=(d/8)X^{1-\eta}\log X,\qquad
M_X=X^{1/2-\eta}\log X.
$$

Use CR45--CR47's fixed real comparison parameter $0<a<5\kappa/8$
and each actual selected height
$\tau_i\in[(\sqrt{B_i}-4)/4,(\sqrt{B_i}-4)/2]$ with its original
explicit-formula error contract. The argument does not select new
heights, discard ties, change the window or replace its weights.
Its conclusion concerns the budget

$$
\mathcal A_X=2\sum_i\delta_i
 \sum_{0<\gamma\le\tau_i}m_\rho|c_{B_i,a}(\rho)|,\qquad
c_{B,a}(s)=s_BF_B(s)-\frac{aB^s}{\sqrt B\,s}.
$$

The complex modulus is taken before conjugate pairing and before
aggregation of labels or zeros. This is a different quantity from
$\sum_i\delta_iH_{B_i,a}(\tau_i)$, from the modulus of an aggregated
complex sum, and from a sum of absolute real parts.

### A real compensation cannot remove the imaginary coefficient

Reuse the complete Laplace representation VJ1 in
[the Mertens note](../ArithSums/fabbian2026mertens.md).
For $L=\log B\ge2$, write

$$
d\mu_L(z)=L(1+z)e^{-Lz}\,dz,\qquad
J_L(s)=\int_0^\infty\frac{d\mu_L(z)}{1+z-s},\qquad
c_{B,a}(s)=\frac{B^{s-1/2}}s[J_L(s)-a].
$$

All these integrals converge on $0<\operatorname{Re}s<1$.
For $\rho=\beta+i\gamma$, $0<\beta<1$, $\gamma>0$,

$$
\operatorname{Im}J_L(\rho)
=\int_0^\infty
 \frac{\gamma}{(1+z-\beta)^2+\gamma^2}\,d\mu_L(z).
$$

The elementary exponential moments give

$$
q_L:=\mu_L([0,\infty))=1+1/L,\qquad
\int_0^\infty(1+z)^2\,d\mu_L(z)
=1+3/L+6/L^2+6/L^3.
$$

Since $0\le\beta\le1$ and $z\ge0$,
$(1+z-\beta)^2\le(1+z)^2$. The normalized second moment is at most
$19/6$ for $L\ge2$: after clearing its positive denominators, the
required inequality is exactly

$$
(L-2)(13L^2+27L+18)\ge0.
$$

Apply the usual integral Jensen inequality for the convex reciprocal
function to the probability measure $q_L^{-1}\mu_L$ and the positive
denominator $(1+z-\beta)^2+\gamma^2$. Its denominator and reciprocal
are integrable, the latter being bounded by $\gamma^{-2}$. It gives

$$
\operatorname{Im}J_L(\rho)
\ge\frac{q_L\gamma}{\gamma^2+19/6}.
$$

Jensen and its equivalent Cauchy--Schwarz application are the standard
integral inequalities in [Durrett, *Probability: Theory and Examples*,
version 5, Theorems 1.5.1--1.5.2, printed page 25](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf).
Reciprocal convexity and the exponential moments are also reused
standard results. The number $19/6$ is the maximum of the stated
normalized second-moment relaxation, attained at $L=2,\beta=0$;
this does not assert sharpness or equality for the resolvent integral
on the original open zero strip. Because $a$ is real,
$|J_L(\rho)-a|\ge\operatorname{Im}J_L(\rho)$. Therefore

$$
\boxed{
|c_{B,a}(\rho)|\ge
\frac{q_L\gamma}{|\rho|(\gamma^2+19/6)}B^{\beta-1/2}.}
\tag{MB1}
$$

MB1 is valid for every real $a$. Its use here keeps the original
fixed allowed parameter. It is stronger than the bound obtained by
restricting the same integral to $0\le z\le1/L$, which has factor
$(1-e^{-1})\gamma/(\gamma^2+4)$. Positive imaginary part before
multiplication by $B^{i\gamma}/\rho$ gives no sign for the resulting
real part.

### Every original core eventually contains one fixed zero in its head

Reuse the complete original zero formula and its pole and trivial-zero
correction $r_B=O(B^{-1/2})$ from
[the Nicolas note](../ArithSums/nicolas2025comparison.md), and the
classical zero-count consequence
$S_2=\sum_{\gamma>0}m_\rho/\gamma^2<\infty$.
In VJ1 the real part of $\rho(1+z-\rho)$ is
$\gamma^2+\beta(1+z-\beta)\ge\gamma^2$.
Thus the complete original, uncompensated coefficients satisfy

$$
|s_BF_B(\rho)|\le q_L B^{\beta-1/2}/\gamma^2,
\qquad
|s_BI_\psi(B)|\le C B^{\Theta-1/2}\quad(B\ge e^2)
$$

for a fixed $C>0$. This sums the full degree-two original
coefficients; it does not assert absolute convergence of the
compensated infinite series. In particular it remains valid when
$\Theta=1$, without inserting a coarse $O(x^\Theta)$ prime-error
bound into an improper integral.

CR20 gives $-s_BI_\psi(B)\ge\kappa t/\sqrt B$ for every original
label and tie. Combining these two inequalities, with $t_i\ge\ell_X$,
yields

$$
\boxed{B_i\ge b_X:=((\kappa/C)\ell_X)^{1/\Theta}.}
\tag{MB2}
$$

Set

$$
\beta_c=\frac12+\frac{\Theta(1/2-\eta)}{1-\eta}.
$$

Then $\Theta-\beta_c=(\Theta+\eta-1)/(2(1-\eta))>0$.
By the definition of the supremum, choose one fixed actual zero
$\rho_*=\beta_*+i\gamma_*$ with $\gamma_*>0$ and $\beta_*>\beta_c$.
No zero attaining $\Theta$ is required. Put

$$
q_*=(\beta_*-1/2)/\Theta>0,\qquad
\varepsilon=(1-\eta)q_*-(1/2-\eta)>0.
$$

MB2 implies $b_X\to\infty$. Hence the lower bound on every original
$\tau_i$ eventually exceeds this one fixed $\gamma_*$, uniformly
over the full window and all ties. MB1, $q_L\ge1$, and the original
positive weights now give

$$
\mathcal A_X\ge C_*\sum_i\delta_i B_i^{\beta_*-1/2}
\ge C_* b_X^{\beta_*-1/2}L_X
$$

with a fixed $C_*>0$, after changing the constant where necessary.
Consequently, for every sufficiently large qualifying original window,
every maximizing-tie assignment and every height satisfying the
original height contracts,

$$
\boxed{
\frac{\mathcal A_X}{M_XL_X}
\ge C_{**}X^\varepsilon(\log X)^{q_*-1}\longrightarrow\infty.}
\tag{MB3}
$$

The fixed zero and common starting point are not asserted computable.
The proof also covers $\Theta=1$; it uses $\Theta+\eta>1$ and never
requires supremum attainment.

### What the budget obstruction leaves unresolved

MB3 rules out paying CR47's remaining target by $\mathcal A_X$, or
by an upper allowance no smaller than this individual-complex-modulus
budget. It supplies no corresponding lower bound for the signed head,
for a sum of absolute real parts, or for a sum aggregated before
taking its modulus. Conjugate pairing, cross-zero cancellation and
cross-label cancellation remain available routes.

For example, if a future same-source estimate establishes
$S_X:=\sum_i\delta_iH_{B_i,a}(\tau_i)\le C_0M_XL_X$, then MB3 forces

$$
\frac{(S_X)_+}{\mathcal A_X}
\ll X^{-\varepsilon}(\log X)^{1-q_*}\longrightarrow0.
$$

This quantifies a necessary one-sided cancellation for such an upper-bound
route; it does not establish the cancellation. To leave CR20's strict
remaining margin, the displayed upper-bound route additionally needs
$C_0<d(1-\kappa)/16$. The joint signed
estimate in CR47 and RH remain unresolved. MB1--MB3 are
supplier-relative paper deductions using the cited original formula,
H1, CR20 and CR45--CR47, with no originality or Lean-verification claim.

## Prime existence bounds the weight of each actual core

Retain the same qualifying RH-false full windows, every original label
$p_0<\cdots<p_m$, and every allowed assignment of full-domain maximizing
ties. Write, as in CR17--CR47,

$$
N_i=p_iU_i,\quad U_i=N_{A_i}^{\rm str},\quad
t_i=\log p_i,\quad B_i=\log U_i,\quad A_i=B_i+t_i,
\qquad 0\le i\le m.
$$

The weighted labels are $0\le i<m$, with
$\delta_i=t_{i+1}-t_i>0$, $L_X=\sum_{i<m}\delta_i$, and
$\max_{i<m}\delta_i\le E=e^{-5\ell_X/12}$. The final label $p_m$
is still the original boundary. Existing full-window counting gives
$L_X\sim\ell_X$; no label thinning is made.

Use the [N2 all-choice ordering](../ArithSums/trureturing2026extrawindowpairing.md#4-n2-the-exact-common-finite-core-and-all-choices-of-ties):
$U_i\mid U_j$ and $B_i\le B_j$ whenever $i<j$, and $A_i<A_j$.
Consequently all weighted occurrences of one actual core $U$ form a
contiguous block $a\le i\le b<m$. This is equality of literal integer
cores, not equality of coarse FIB labels or of an approximate clock.
The [existing cofinal constant-core edge result CW2](../ArithSums/nicolas2025comparison.md#exact-log-2-rigidity)
is reused; it asserts neither a long constant-core run nor a bound for
the total weight of a repeated core. The estimate here applies to every
such block in every allowed tie assignment, whether or not CW2 selects
one of its edges.

### Retain the strict activation and the last outgoing weight

Suppose a prime-existence supplier gives, for every sufficiently large
real $x$, a prime $q$ with $x<q\le x+H(x)$. Use it at the actual
departure $x=A_a$. The already paid first-layer interface gives
$q<a_{q,1}<q+1\le A_a+H(A_a)+1$.

Strict inventory equality $N_{A_a}^{\rm str}=N_{A_b}^{\rm str}=U$
excludes every actual activation in $[A_a,A_b)$. Indeed a layer activating
there is excluded at $A_a$ and included at $A_b$, contradicting equality.
If $A_b\ge A_a+H(A_a)+1$, then the displayed $a_{q,1}$ lies strictly
between $A_a$ and $A_b$, giving this contradiction. Thus

$$
A_b-A_a<H(A_a)+1.
$$

The case $a=b$ satisfies the same inequality. Higher-layer and
simultaneous activations are retained in the inventory; they can only
shorten this constant-core interval. No upper bound for their number
is assumed, and no equality layer is inserted at a strict endpoint.

Since $B_b=B_a$, the exact weighted telescope is

$$
\begin{aligned}
w_X(U)&:=\sum_{i=a}^b\delta_i
=t_{b+1}-t_a\\
&=(A_b-A_a)+\delta_b
\le H(A_a)+1+E.
\end{aligned}
\tag{SM1}
$$

The term $\delta_b$ is indispensable: its left endpoint has core $U$
even if label $b+1$ has another core. For the terminal block $b=m-1$
it uses precisely the original boundary label $p_m$. SM1 therefore does
not drop either a switching weight or the last weight of the full window.
All supplier starts can be paid uniformly, since $A_a\ge\ell_X\to\infty$.

### Directly consume prime existence, rather than reprove a gap theorem

The [Baker--Harman--Pintz primary Theorem 1](../Scale/bakerharmanpintz2001primegaps.md)
and its explicit forward conversion BHP-F supply $H(x)=2x^\vartheta$,
$\vartheta=21/40$. Therefore every original core block satisfies

$$
\boxed{w_X(U)\le2A_a^{21/40}+1+E.}
\tag{SM2}
$$

This does not replace the stronger prime-count contracts used in N1 or
the original full-window construction. The original GM mesh $E$ is kept.
No new prime-gap or sieve theorem, numerical analytic start, literature
priority or complete Lean verification is claimed.

Define the original probability measure on actual core clocks by

$$
\nu_X=\frac1{L_X}\sum_{i<m}\delta_i\,\boldsymbol\delta_{B_i},
\qquad B_{\max,X}=\max_{i<m}B_i,
$$

where $\boldsymbol\delta_B$ is a Dirac mass. Since $t_a\le2\ell_X$,
SM2 gives both the local and full-window bounds

$$
\begin{aligned}
\nu_X(\{B\})&\le
\min\left(1,\frac{2(B+2\ell_X)^{21/40}+1+E}{L_X}\right),\\
\sup_B\nu_X(\{B\})&\le
\min\left(1,\frac{2(B_{\max,X}+2\ell_X)^{21/40}+1+E}{L_X}\right).
\end{aligned}
\tag{SM3}
$$

The first formula is for clocks of actual cores; absent clocks have zero
mass. These are deterministic bounds for the original positive weights,
uniform in all original tie choices. No probability law for independent
zero phases has been substituted for $\nu_X$.

### The additional clock regime and the signed-head debt

With $L_X\sim\ell_X$, a sufficient extra regime for SM3 to imply
$\sup_B\nu_X(\{B\})\to0$ is

$$
B_{\max,X}=o(\ell_X^{40/21}).
\tag{SM4}
$$

For an all-choice assertion this regime must hold uniformly over the
allowed tie assignments. The existing exponential ceiling $R$ does not
supply SM4. Conversely, MB2 supplies
$B_{\min,X}\ge c\ell_X^{1/\Theta}$ for one fixed $c>0$. If
$\Theta\le21/40$, this lower bound excludes the sufficient regime SM4.
That failure does not prove actual concentration: SM4 is a sufficient
condition for this particular upper bound, not a necessary condition for
the actual atom masses to vanish.

For the existing CR45--CR47 core-selected-height route, one may apply
the CHJ supplier once per distinct $B$ and choose its resulting $\tau_B$
for every label with that core. All that route's error contracts depend
on this same $B$, so the exact remaining head can then be written

$$
\sum_{i<m}\delta_iH_{B_i,a}(\tau_{B_i})
=L_X\int H_{B,a}(\tau_B)\,d\nu_X(B).
\tag{SM5}
$$

This is a finite regrouping of the existing admissible-height route;
it does not impose a common height on different cores. Arbitrary previously
chosen individual masks cannot be replaced by $\tau_B$ without their
own unchanged contracts. The other $A$-selected-height route remains
subject to its separate hypotheses.

Even a supplied SM4 and vanishing atom masses would not establish
cancellation of $e^{i\gamma\log B}$, control the growing family of zero
frequencies, or bound the amplitude-weighted signed integral in SM5.
SM1--SM3 pay an actual residence-weight interface using existing
arithmetic and prime existence; they do not pay the signed upper estimate
with CR20's required strict margin. CR21/CR23, CR47 and RH remain unproved.

## The retained witness height bounds the actual selected core clocks

Keep the original fixed $\Theta,\eta,d$, every qualifying full window,
and all maximizing ties from MB1--MB3 and SM1--SM5. The following
additional clock estimate consumes the existing unabridged CR19 height
and the complete uncompensated zero-series bound from MB2's proof.
It requires no prime-distribution, ambient sampling or phase hypothesis.

Beyond one common source start CR18 has $\chi_{p,u}>0$, and CR19 gives

$$
-s_B I_\psi(B)\ge
\frac d2\sqrt B\log B\,X^{-\eta}
+\chi_{p,u}\frac t{\sqrt B}.
$$

The already paid complete bound is
$|s_BI_\psi(B)|\le C B^{\Theta-1/2}$. It retains the full
uncompensated original coefficient and its convergent reciprocal-square
zero sum; no compensated infinite $1/\rho$ series is made absolutely
summable. Dropping only the nonnegative second term in the lower bound
therefore gives

$$
\frac d2\sqrt B\log B\,X^{-\eta}
\le C B^{\Theta-1/2},\qquad
\boxed{B^{1-\Theta}\log B\le C_dX^\eta.}
\tag{SC1}
$$

This is a necessary estimate on each actual selected $B$, uniform in
the original labels and tie assignments. The height is not spent twice:
SC1 only constrains the possible clocks by the same already-established
lower and upper values of the complete response. No second independent
positive reserve is created.

### A polynomial ceiling when the zero-real-part supremum is below one

If $\Delta:=1-\Theta>0$, MB2 and
$\ell_X=(d/8)X^{1-\eta}\log X$ give $\log B\ge c_1\log X$
uniformly for one $c_1>0$ and sufficiently large original witnesses.
Substitution in SC1 yields

$$
\boxed{
B_{\max,X}\ll_{\Theta,\eta,d}
\left(\frac{X^\eta}{\log X}\right)^{1/(1-\Theta)}.}
\tag{SC2}
$$

The implied constant includes the fixed original suppliers and is
independent of label and tie choice. No uniformity as $\Theta\uparrow1$
is asserted. SC2 bounds actual selected clocks; it is stronger than
using the exponential source-window ceiling alone. At $\Theta=1$,
SC1 instead gives only $\log B\ll X^\eta$, which does not improve
the existing $\log R\asymp X^{\eta/2}$ ceiling.

### The range in which the repeated-core mass actually decays

Put $\alpha_X=\sup_B\nu_X(\{B\})$. Existing CR17 has
$t_i/B_i\to0$ uniformly, with $t_i\ge\ell_X$, so
$B_{\max,X}+2\ell_X\le2B_{\max,X}$ eventually. Combining SC2 with
SM3 and the unchanged $L_X\sim\ell_X$, for $\vartheta=21/40$,
gives

$$
\alpha_X\ll
X^{\vartheta\eta/(1-\Theta)-(1-\eta)}
(\log X)^{-1-\vartheta/(1-\Theta)}+\ell_X^{-1}.
\tag{SC3}
$$

Thus the previously sufficient clock regime SM4, and consequently
$\alpha_X\to0$, are paid for every allowed tie assignment whenever
the original fixed parameters satisfy

$$
\boxed{
\Theta<1,\qquad 1-\Theta<\eta<\frac12,\qquad
\eta\le\frac{1-\Theta}{1-\Theta+21/40}.}
\tag{SC4}
$$

The last inequality permits equality: the power of $X$ in SC3 is then
zero and the negative logarithmic power still tends to zero. Equivalently,
SC2 divided by $\ell_X^{40/21}$ tends to zero in this same range.
Every statement here retains the original supplied $\eta$; no stronger
oscillation supplier or a more favorable replacement exponent is assumed.
The parameter interval in SC4 can be nonempty only when $\Theta>21/40$.
For other fixed parameters with $\Theta<1$, SC2 still holds but this
bound need not imply mass decay. The $\Theta\le21/40$ incompatibility
already stated after SM4 concerns that sufficient regime, not an
arithmetic concentration theorem.

SC1--SC4 are source-specific paper applications of the existing CR19
and MB2 bounds. They add no generic inequality, prime theorem or Lean
declaration, and make no literature-originality or kernel-verification
claim. The quantity tending to zero in SC4 is the maximum **normalized**
single-core mass; the unnormalized maximum $w_X(U)$ need not tend to
zero. Even in this paid parameter range, phases, amplitude weights,
zero multiplicities and actual individual masks remain jointly constrained
in SM5. Neither SC4 nor mass decay supplies the signed finite-head bound
with the strict coefficient $C_0<d(1-\kappa)/16$. Robin/RH remain unproved.

## The paid clock ceiling removes a lower real-part sector of the finite head

Keep the original RH-failure suppliers, fixed $\Theta,\eta,d$, every
qualifying full window, every maximizing tie and CR45--CR47's fixed
$0<a<5\kappa/8$. In particular the original $\eta$ is not replaced.
The following application uses SC2 and the exact-coefficient majorants
already used in MB2 and the zero-free-strip comparison. It adds no
zero-density, zero-free or generic summation theorem.

For a fixed $\sigma\ge1/2$, define a subhead at the same actual height
by restricting the existing finite sum:

$$
H^{\le\sigma}_{B,a}(T)=2\operatorname{Re}
\sum_{\substack{0<\operatorname{Im}\rho\le T\\
                  \operatorname{Re}\rho\le\sigma}}
m_\rho\left[s_BF_B(\rho)-\frac{aB^\rho}{\sqrt B\,\rho}\right].
$$

Let $H^{>\sigma}_{B,a}(T)$ be its complementary subhead. Thus
$H_{B,a}(T)=H^{\le\sigma}_{B,a}(T)+H^{>\sigma}_{B,a}(T)$ exactly.
All actual real parts, multiplicities, labels and height masks remain;
the already paid suffix and compensation change are not reapplied to
either subhead separately.

### Apply the existing coefficient bounds to the retained submultiset

MB2 already uses
$|s_BF_B(\rho)|\le(1+1/\log B)B^{\beta-1/2}/\gamma^2$
and $\sum_{\gamma>0}m_\rho/\gamma^2<\infty$. The existing zero-count
consequence also gives
$\sum_{0<\gamma\le T}m_\rho/|\rho|=O(1+\log^2T)$.
For $\beta\le\sigma$, $B\ge e^2$ and the original
$\tau_B\asymp\sqrt B$, these bounds directly supply

$$
\left|H^{\le\sigma}_{B,a}(\tau_B)\right|
\le C_a B^{\sigma-1/2}(1+\log^2 B).
\tag{SR1}
$$

The constant is independent of the original labels, ties and legal
heights. This is the owner's existing absolute majorant applied to a
submultiset, not a new estimate for the zeros.

Put $M_X=X^{1/2-\eta}\log X$ and
$S_X^{\le\sigma}=\sum_{i<m}\delta_i
H^{\le\sigma}_{B_i,a}(\tau_{B_i})$. Suppose first that
$\Delta=1-\Theta>0$. With $h=\sigma-1/2\ge0$, SC2 gives
$B_{\max,X}^{h}\ll X^{\eta h/\Delta}(\log X)^{-h/\Delta}$
and $1+\log^2 B_{\max,X}\ll(\log X)^2$. Since all original
$\delta_i$ are positive and sum to $L_X$, the quantitative consequence is

$$
\boxed{
\frac{|S_X^{\le\sigma}|}{M_XL_X}
\ll_{\Theta,\eta,d,a,\sigma}
X^{-\varepsilon_\sigma}
(\log X)^{1-(\sigma-1/2)/(1-\Theta)},\qquad
\varepsilon_\sigma=
\frac12-\eta-\frac{\eta(\sigma-1/2)}{1-\Theta}.}
\tag{SR2}
$$

This bound retains the negative logarithmic power in SC2. Therefore,
with all parameters fixed as supplied,

$$
\boxed{
\frac12\le\sigma<\sigma_{\rm safe}:=
\frac12+\frac{(1-\Theta)(1/2-\eta)}{\eta}
\quad\Longrightarrow\quad
|S_X^{\le\sigma}|=o(M_XL_X).}
\tag{SR3}
$$

At $\sigma=\sigma_{\rm safe}$ the remaining logarithmic power is
$2-1/(2\eta)$. Hence this endpoint also obeys SR3 when the original
$\eta<1/4$. For $\eta\ge1/4$ SR2 alone does not supply the endpoint
little-$o$ conclusion; it does not prove that the actual sector is large.
No SC4 atom-decay hypothesis or cross-label phase cancellation is used.

### Retain the spectral range and the strict remaining margin

The original $\eta>1-\Theta$ gives

$$
\Theta-\sigma_{\rm safe}
=\frac{\eta-(1-\Theta)}{2\eta}>0.
\tag{SR4}
$$

Thus SR3 leaves a nonempty possible real-part range below the actual
zero-real-part supremum. It neither proves that no zeros remain nor
bounds their signed aggregate. For any allowed fixed cut, the original
target with a constant strictly below $d(1-\kappa)/16$ is equivalent
to the same target for $S_X^{>\sigma}$, allowing an arbitrarily small
fixed loss of margin: the absolute difference is $o(M_XL_X)$ uniformly
over the original windows, all ties and admissible heights.

When $\Theta=1$, SC2 is unavailable. For the sector $\sigma=1/2$ only,
the original ceiling $B_i\le R$ with
$\log R\asymp X^{\eta/2}$ instead gives

$$
\frac{|S_X^{\le1/2}|}{M_XL_X}
\ll_a\frac{X^{2\eta-1/2}}{\log X}.
\tag{SR5}
$$

Consequently this sector is negligible when the original
$0<\eta\le1/4$, including equality. No positive-width sector above
$1/2$ is removed by this argument when $\Theta=1$.

SR1--SR5 are source-specific paper applications of the already paid
clock and coefficient estimates. They narrow an unpaid spectral range;
they do not supply its signed bound, replace an original mask, establish
literature originality or constitute Lean verification. The full Robin
comparison and RH remain unproved.

## Legal core-height choices differ only below the target scale

Keep the complete original coefficient, the same actual core clocks,
all labels and ties, and CR45--CR47's fixed $a,\kappa$. This application
uses the already paid degree-two suffix and CHJ contracts. A height is
called admissible here only if it lies in CR45's interval

$$
\frac{\sqrt B-4}{4}\le T\le\frac{\sqrt B-4}{2}
$$

and satisfies that route's original complete formula

$$
\psi(B)=B-Z_B(T)+e_B(T),\qquad |e_B(T)|\le80\sqrt B.
$$

CR45 supplies an admissible height for every sufficiently large actual
core. This definition does not declare every point in the interval
admissible, or change an existing mask from a different height route.

### Remove the legal-height variable using the complete accounts

Write $E(u)=u-\psi(u)$ and define the height-independent same-clock
quantity

$$
G_a(B)=-s_BI_\psi(B)-\frac{aE(B)}{\sqrt B},
\qquad
\mathcal G_X=\sum_{i<m}\delta_iG_a(B_i).
$$

The original full formula and CR34's degree-two suffix are

$$
-s_BI_\psi(B)=2s_B\operatorname{Re}
\sum_{\gamma>0}m_\rho F_B(\rho)+r_B,
\qquad
T_F(B,T)=-\mu_B(T)+e_F(B,T).
$$

Their complete endpoint and elementary terms are retained. In
particular $\mu_B\ge0$, $|e_F|\le\varepsilon_F$, and at
$T\asymp\sqrt B$ the already established bounds give
$|r_B|+\mu_B(T)+\varepsilon_F(B,T)=o_X(1)$ uniformly in the
original sources and allowed heights. The CHJ formula at that same
height gives $Z_B(T)=E(B)+e_B(T)$. Subtracting these two complete
accounts, rather than optimizing an independently chosen head, yields

$$
\boxed{
H_{B,a}(T)=G_a(B)-r_B+\mu_B(T)-e_F(B,T)
-\frac{ae_B(T)}{\sqrt B},\qquad
|H_{B,a}(T)-G_a(B)|\le80a+o_X(1).}
\tag{HC1}
$$

This conclusion holds also when $\Theta=1$. It uses the actual
CHJ error and signed suffix contracts; no absolute summability of
the compensated infinite $1/\rho$ series is imposed.

For any admissible assignment of the original individual heights,
positivity of the original weights therefore gives

$$
\boxed{
|S_X(\boldsymbol T)-\mathcal G_X|
\le(80a+o_X(1))L_X.}
\tag{HC2}
$$

Two admissible assignments on the same window and the same maximizing
ties consequently differ by at most $(160a+o_X(1))L_X$. Repeated
cores need not be given the same height for this comparison, although
SM5 permits that choice in this route. Different cores are not asserted
to share a common admissible height.

### Preserve the cofinal quantifiers and the strict constant

The original $M_X=X^{1/2-\eta}\log X$ tends to infinity because
the supplied $\eta<1/2$. Thus HC2 is $o(M_XL_X)$. Put
$C_*=d(1-\kappa)/16$. The existence of a constant $C_0<C_*$ such
that the original sufficient signed-head estimate holds is equivalent
to the corresponding estimate for $\mathcal G_X$, with an arbitrarily
small fixed loss of margin in either direction.

Both statements retain the same source quantifiers: beyond every common
finite source start there is an original qualifying full window on
which every maximizing tie assignment satisfies the bound; the head
version also requires admissible heights. If the head estimate holds,
HC2 transfers it to $\mathcal G_X$. Conversely, if the latter estimate
holds, CR45 supplies heights for each actual core, and HC2 transfers
the bound to every such admissible assignment. Choose a fixed
$\epsilon<C_*-C_0$ and then one common start with
$(80a+o_X(1))/M_X<\epsilon$ to preserve the strict constant.
The original $\eta,a$ and all full-window outgoing weights are unchanged.

In particular, searching among heights satisfying these same contracts
can change the aggregate only by $O_a(L_X)$. It cannot by itself supply
an $M_XL_X$-scale saving. HC2 does not bound $\mathcal G_X$ or
show that the required favorable full windows exist.

### The remaining same-clock comparison is a future prime-deficit average

The original improper integral gives an exact alternative readout. For
$L=\log B$, set

$$
k_L(v)=\frac{L(1+L+\log v)}{v^2(L+\log v)^2},\qquad v\ge1.
$$

Changing variables $u=Bv$ in $I_\psi(B)$ yields

$$
\boxed{
G_a(B)=\frac1{\sqrt B}
\left[\int_1^\infty E(Bv)k_{\log B}(v)\,dv-aE(B)\right].}
\tag{HC3}
$$

The convergence is the original integral's convergence. The kernel is
positive and normalized: it is the negative derivative of
$L/[v(L+\log v)]$, whose values at $v=1$ and at infinity are $1$
and $0$. This is a change of variable in the existing formula, not a
new prime-error estimate.

CR44 already controls a specified same-source interaction through
$A=B+t$ and $K(A)=B$. It does not control the future-deficit average
in HC3. A bound for that average at the actual selected cores is still
needed. A FIB re-encoding or rotation of the same readout supplies no
such estimate without an additional proved source relation.

HC1--HC3 are paper applications of the existing complete accounts,
with no new generic theorem, literature-originality claim or Lean
verification. They eliminate legal-height optimization from the leading
unpaid issue; the original signed Robin target and RH remain unproved.

## The original budget pays the head above an auxiliary selected height

Keep HC1--HC3's actual source, all original windows and ties, fixed
$a$, outgoing weights $\delta_i$ and admissible upper heights $\tau_i$.
Use FH1/CP1's deterministic ceiling $\log B_i\le Y:=\mathsf Y_X$
with $Y\to\infty$ and $Y=O((\log X)^2)$. Write $M=M_X$,
$L=L_X$ and $b=\min_{i<m}B_i$. The original source gives
$b/\ell_X\to\infty$ and

$$
\frac{\sqrt{\ell_X}}{M_X}
=\sqrt{\frac d8}\frac{X^{\eta/2}}{\sqrt{\log X}}
\longrightarrow\infty.
$$

Here $\eta>0$ follows from the original $1-\Theta<\eta<1/2$.
Set $T^0_{B,X}=\sqrt B\,Y^2/M$. Uniformly over the actual cores,

$$
\frac{T^0_{B,X}}{\log^2B}\ge\frac{\sqrt b}{M}\longrightarrow\infty,
\qquad
\frac{T^0_{B,X}}{\sqrt B}=\frac{Y^2}{M}\longrightarrow0.
$$

Thus $\max\{51,\log^2 B\}<T^0_{B,X}<(\sqrt B-2)/4$
at one common source start. Directly apply the
[adopted CHJ selected-height theorem](../Analytic/cullyhugilljohnston2026truncation.md#exact-supplier-contract),
with its same $\alpha=1/2$, $\omega=1$ row and lower parameter
$T^0_{B,X}$. It supplies an individual auxiliary height with

$$
\widehat\tau_{B,X}\in[T^0_{B,X},2T^0_{B,X}],\qquad
\psi(B)=B-Z_B(\widehat\tau_{B,X})+\widehat e_B,
\qquad
|\widehat e_B|\le19.81\frac{M}{Y^2}\sqrt B.
\tag{BH1}
$$

The auxiliary cuts carry BH1's error contract. The original upper
heights retain HC1's $80\sqrt B$ contract and original admissibility
definition. Since $Y^2/M\to0$, every auxiliary cut is below every
original admissible upper height at a common source start. Each cut
is selected at its own actual core; no common height is required.

Both finite explicit formulas use the same weak $\psi(B)$. Their
full baseline cancels exactly, giving

$$
\frac{|Z_B(\tau_B)-Z_B(\widehat\tau_{B,X})|}{\sqrt B}
\le80+19.81\frac{M}{Y^2}.
\tag{BH2}
$$

All prime-power endpoints are retained in the two formulas. For
the degree-two part, reuse DH3's recorded coefficient bound and
the reciprocal-square zero count:

$$
|s_BF_B(\rho)|\le\frac{2\sqrt B}{\gamma^2},\qquad
\sum_{\gamma>T}\frac{m_\rho}{\gamma^2}
\ll\frac{\log(eT)}T\quad(T\ge4).
$$

Since $\widehat\tau_{B,X}\ge\sqrt B\,Y^2/M$ and
$\log(e\widehat\tau_{B,X})\ll Y$, these give

$$
\left|2s_B\operatorname{Re}
\sum_{\widehat\tau_{B,X}<\gamma\le\tau_B}
 m_\rho F_B(\rho)\right|
\ll\frac{\sqrt B\log(e\widehat\tau_{B,X})}
         {\widehat\tau_{B,X}}
\ll\frac{M}{Y}.
$$

Combine this with BH2 for the complete original coefficient
$c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho$.
The original positive weights then yield

$$
\boxed{
\sum_{i<m}\delta_i
\left|2\operatorname{Re}
\sum_{\widehat\tau_{B_i,X}<\gamma\le\tau_i}
 m_\rho c_{B_i,a}(\rho)\right|
\ll_a L_X\left(1+\frac{M_X}{\mathsf Y_X}\right)
=o(M_XL_X).}
\tag{BH3}
$$

This pays the actual complete upper slice across all zero real
parts, including $\Theta=1$, with the original upper masks and
all multiplicities. The degree-one contribution is bounded after
conjugate pairing through BH2; no termwise absolute bound for it
is used. Positivity of the residence weights introduces no
independence assumption.

The auxiliary cuts satisfy
$\widehat\tau_{B_i,X}/\tau_i\ll\mathsf Y_X^2/M_X\to0$
uniformly, while their minimum tends to infinity. Removing this
precise slice changes the original weighted head by $o(M_XL_X)$.
The remaining head still contains every fixed zero eventually;
its signed estimate is unproved. This is a paper parameter
application of the existing CHJ and coefficient suppliers,
without a new truncation theorem, literature-priority claim or
Lean certification. The full Robin comparison and RH remain
unproved.

## The published BHP count controls total local core occupation

Keep all original qualifying full windows, all maximizing ties and the
strict inventory from SM1--SM5. The additional supplier is the
[unnumbered concluding estimate in the BHP proof](../Scale/bakerharmanpintz2001primegaps.md#the-published-proofs-quantitative-forward-count),
printed p.562. Put $b_0=9/100$ and $\vartheta=21/40$. For all sufficiently
large real $x$, that published estimate gives
$\pi(x+x^\vartheta)-\pi(x)\ge b_0x^\vartheta/\log x$.
It is a lower count, not an asymptotic prime-count formula or a new sieve
theorem. The transfers below use this count directly.

### A lower increment of the same complete strict inventory

There is one finite real start such that, for all $v\ge u$ beyond it,

$$
\boxed{K(v)-K(u)\ge
b_0\bigl(v-u-1-v^\vartheta\bigr)_+.}
\tag{LO1}
$$

Here $z_+=\max(0,z)$. Equality $v=u$, and more generally $v-u\le1$,
is covered by monotonicity. For $v-u>1$, start at $x_0=u$ and set
$x_{j+1}=x_j+x_j^\vartheta$. Stop at the largest $n$ with
$x_n\le v-1$. This is a finite construction, and

$$
0\le v-1-x_n<x_n^\vartheta\le v^\vartheta.
$$

In each completed interval the actual primes have $\log q\ge\log x_j$,
so the cited count gives

$$
\sum_{x_j<q\le x_{j+1}}\log q
\ge\log x_j[\pi(x_{j+1})-\pi(x_j)]
\ge b_0x_j^\vartheta.
$$

These prime intervals are disjoint. Every such prime belongs to
$(u,v-1]$. The existing first-layer rule $q<a_{q,1}<q+1$ puts its
activation strictly in $(u,v)$, including when $q=v-1$. Its mass
therefore occurs in $K(v)-K(u)$ with the original strict endpoints.
Higher-layer and simultaneous activations remain in that complete
inventory and have nonnegative mass. Summing the displayed lower
bounds gives
$K(v)-K(u)\ge b_0(x_n-u)\ge b_0(v-u-1-v^\vartheta)$.
Combine this with monotonicity to obtain LO1. The allowance is at
BHP scale $v^{21/40}$; it has not been reduced to $\sqrt v$.

### Retain the total outgoing weight of a block of different cores

For every consecutive block $0\le r\le s<m$ in a sufficiently large
original full window, all-choice ordering gives $B_s\ge B_r$. Write
$b=B_s-B_r$ and $\tau=t_s-t_r$. The exact source relations are

$$
A_s-A_r=b+\tau,\qquad K(A_s)-K(A_r)=b.
$$

Using the weaker linear form of LO1 gives
$b\ge b_0(b+\tau-1-A_s^\vartheta)$, hence
$\tau\le(91/9)b+1+A_s^\vartheta$. The complete weight telescope is
$\sum_{i=r}^s\delta_i=t_{s+1}-t_r=\tau+\delta_s$. Consequently

$$
\boxed{\sum_{i=r}^s\delta_i
\le\frac{91}{9}(B_s-B_r)+1+A_s^\vartheta+\delta_s.}
\tag{LO2}
$$

This includes $r=s$. At $s=m-1$, $\delta_s$ uses precisely the original
terminal label $p_m$. The last outgoing weight is kept even when its
right endpoint has another core. LO2 requires no bound on the number
of distinct cores in the block.

Retain the same probability measure
$\nu_X=L_X^{-1}\sum_{i<m}\delta_i\boldsymbol\delta_{B_i}$ and let
$\mathfrak e_X=\max_{i<m}\delta_i$ denote the original label mesh,
distinct from the prime error $E(u)$. For every $y,h\ge0$,

$$
\boxed{L_X\nu_X([y,y+h])\le
\min\!\left\{L_X,\frac{91}{9}h+1+
(y+h+2\ell_X)^\vartheta+\mathfrak e_X\right\}.}
\tag{LO3}
$$

If the interval contains any actual clock, its indices form one
consecutive block by all-choice monotonicity. On that block,
$B_s-B_r\le h$, $A_s=B_s+t_s\le y+h+2\ell_X$ and
$\delta_s\le\mathfrak e_X$. Apply LO2 and the trivial total-weight
bound. An empty interval has zero weight. All actual $A_r$ tend to
infinity uniformly, so the common start is independent of $y,h$ and
of the tie assignment.

### Total occupation at the original head's spatial resolution

Let $B_{\min,X}=\min_{i<m}B_i$ and
$B_{\max,X}=\max_{i<m}B_i$. For fixed $D>0$, put

$$
I_{y,D}=\left[y,y\exp\!\left(\frac D{\sqrt y}\right)\right],
\qquad y\ge B_{\min,X}/2.
$$

Uniformly over all allowed ties, for sufficiently large original
windows,

$$
\boxed{\sup_{y\ge B_{\min,X}/2}\nu_X(I_{y,D})
\ll_D\frac{(B_{\max,X}+2\ell_X)^\vartheta+
1+\mathfrak e_X}{L_X}.}
\tag{LO4}
$$

A nonempty cell has $y\le B_{\max,X}$, and its length is at most
$2D\sqrt y$ beyond one common start. Apply LO2 to its actual block,
use $A_s\le B_{\max,X}+2\ell_X$, and absorb
$\sqrt{B_{\max,X}}$ into $B_{\max,X}^{21/40}$.
These cells have log-clock width $D/\sqrt y$, corresponding to the
original heights comparable to $\sqrt B$. No height or mask is changed.

In exactly the already paid SC4 region,

$$
\Theta<1,\qquad 1-\Theta<\eta<\frac12,
\qquad \eta\le\frac{1-\Theta}{1-\Theta+21/40},
$$

SC4 gives $B_{\max,X}^{21/40}=o(L_X)$ uniformly in the ties.
The existing $2\ell_X=o(B_{\max,X})$, $L_X\sim\ell_X$ and mesh
bound then give

$$
\boxed{\sup_{\text{allowed ties}}
\sup_{y\ge B_{\min,X}/2}\nu_X(I_{y,D})\longrightarrow0.}
\tag{LO5}
$$

The original supplied $\eta$ is unchanged, and SC4's equality case
remains included. Outside this region, and at $\Theta=1$, LO1--LO4
still apply but no vanishing assertion follows from these bounds.
LO5 controls the total normalized occupation of arbitrarily many
different cores in each cell, rather than only individual atom masses.
It does not provide phase balance, a bandwidth-weighted sampling
estimate or an upper bound for the original signed $G_a$-mean.

LO1--LO5 are source-specific paper applications of the published lower
count and existing inventory/source contracts. The prime estimate
belongs to BHP; no sieve improvement, literature-priority claim, new
Lean declaration or kernel-verification claim is made. The remaining
signed Robin estimate and RH are unproved.

## The same lower count sharpens both retained stock costs

Keep the complete actual sources, all ties and the original fixed
parameters of CR40--CR47 and LO1--LO5. Write, for an actual label,

$$
A=B+t,\qquad D=B-K(B),\qquad
J=\int_{[B,A)}(v-B)\,dK(v).
$$

Fix $c>4$ and use CR40's constant $H_c$. Put
$h_c=H_c\sqrt B$, $e_B=b_0(1+A^\vartheta)$ and
$\mathfrak r_B=w(B)/w(A)$, with the same $b_0=9/100$ and
$\vartheta=21/40$. The symbol $e_B$ here is a lower-increment
allowance, not HC1's CHJ truncation error $e_B(T)$.

### Keep both envelopes on the same terminal layer interval

Translate the complete layer measure on $[B,A)$ to $\mu$ on $[0,t)$.
Its mass is $D$, and the existing finite layer identity is
$J=\int_0^t\mu([z,t))\,dz$. Since $t/B\to0$, eventually $t\le B/2$.
CR40's upper prefix bound and LO1's lower terminal bound give,
for $0\le z\le t$,

$$
\begin{aligned}
\mu([z,t))&\ge D-h_c-cz,\\
\mu([z,t))=K(A)-K(B+z)&\ge b_0(t-z)-e_B.
\end{aligned}
$$

The second line at $z=t$ is trivial; at every other $z$ it is the
weaker linear form of LO1. The intervals and strict endpoints are
those of the same actual inventory. Combining the bounds yields

$$
\mu([z,t))\ge b_0(t-z)
+[D-h_c-b_0t-(c-b_0)z]_+-e_B.
$$

CR40 also gives $D-h_c\le ct$, so the positive-part term has its
entire support in $[0,t]$. Integration gives

$$
\boxed{J\ge\frac{b_0t^2}{2}
+\frac{(D-h_c-b_0t)_+^2}{2(c-b_0)}-e_Bt.}
\tag{ST1}
$$

Now reuse both costs in CR41, $2J+(t-D)^2\le\mathfrak r_Bt^2$.
Substitution gives the actual-source constraint

$$
\boxed{b_0t^2+\frac{(D-h_c-b_0t)_+^2}{c-b_0}
+(t-D)^2\le\mathfrak r_Bt^2+2e_Bt.}
\tag{ST2}
$$

No separately optimal prefix and suffix measures are combined: both
envelopes constrain the same $\mu$, and both curvature costs belong
to the same legal integer competitor. Neither the witness height nor
the prime-power reserve is spent in this calculation. ST1--ST2 hold
beyond a common source start also when $\Theta=1$.

### A strictly smaller coefficient in the unchanged SC4 region

Assume precisely SC4's original fixed-parameter region, displayed
before LO5. Its uniform clock estimate and $t_i\ge\ell_X\sim L_X$
give

$$
\frac{e_{B_i}}{t_i}\to0,\qquad
\frac{h_c}{t_i}\to0,\qquad \mathfrak r_{B_i}\to1
$$

uniformly over all original labels and maximizing ties. LO1 also
gives $D_i/t_i\ge b_0-e_{B_i}/t_i$. CR41 bounds these ratios above
by $1+\sqrt{\mathfrak r_{B_i}}$, since $J\ge0$.

For any limiting ratio $z\ge b_0$, divide ST2 by $t^2$ to get

$$
b_0+\frac{(z-b_0)^2}{c-b_0}+(1-z)^2\le1,
$$

equivalently
$(c+1-b_0)z^2-2cz+cb_0\le0$. Its upper root is
$[c+\sqrt{c(1-b_0)(c-b_0)}]/(c+1-b_0)$.
Taking $c\downarrow4$ yields

$$
\boxed{b_0-o_X(1)\le\frac{D_i}{t_i}
\le\xi_*+o_X(1),\qquad
\xi_*=
\frac{4+\sqrt{4(1-b_0)(4-b_0)}}{5-b_0}
=\frac{400+2\sqrt{35581}}{491}.}
\tag{ST3}
$$

The uniform upper claim means that for every fixed $\varepsilon>0$
there is one common source start with $D_i/t_i\le\xi_*+\varepsilon$
for every original label and tie. First fix $c>4$ with its upper root
below $\xi_*+\varepsilon/2$, then use the uniform vanishing errors.
This does not assert a numerical start or an explicit convergence rate.

Here $\xi_*\approx1.58301<8/5$. Indeed the limiting quadratic at
$z=8/5$ is

$$
(5-b_0)\frac{64}{25}-8\frac85+4b_0
=\frac{36b_0}{25}>0,
$$

and $8/5$ is to the right of its vertex. Thus ST3 strictly improves
CR43's asymptotic stock coefficient in this parameter region.
It neither changes the original $\eta$ nor strengthens CR43 outside
SC4; there the finite allowance $e_Bt$ in ST2 is retained.

### Transfer the improved cost to the same local prime comparison

Reuse CR44's exact common-source identities

$$
E(B)=D+Q(B),\qquad
\psi(A)-\psi(B)-t=D-t+Q(B)-Q(A).
$$

The existing $Q(x)=O(\sqrt x)$ and $A/B\to1$ pay the endpoint
corrections. Hence in SC4, for every fixed $\varepsilon>0$ beyond
one common source start,

$$
\begin{aligned}
E(B_i)&\le(\xi_*+\varepsilon)t_i+O(\sqrt{B_i}),\\
\boxed{\sum_{i<m}\delta_i
\frac{\psi(A_i)-\psi(B_i)-t_i}{\sqrt{B_i}}
\le(\xi_*-1+\varepsilon)V_X^{\rm lag}+O(L_X).}
\end{aligned}
\tag{ST4}
$$

The lag weight is the original
$V_X^{\rm lag}=\sum_{i<m}\delta_it_i/\sqrt{B_i}$.
All original positive weights, their last outgoing endpoint and all
ties are retained. The coefficient $\xi_*-1\approx0.58301$ is
strictly below CR44's $3/5$ only under the stated SC4 condition.
The fixed comparison parameter $a$ has not been reselected.

ST1--ST4 apply the published BHP count and both existing competitor
costs to the same actual layer measure. They are paper applications,
without a new prime theorem, literature-priority or Lean-verification
claim. This stronger local $B$--$A$ comparison does not bound HC3's
future-deficit average minus $aE(B)$. The original signed-head upper
estimate with $C_0<d(1-\kappa)/16$ and RH remain unproved.

## The existing uniform count pays a sharper local comparison on longer lags

The [Guth--Maynard supplier](../Analytic/guthmaynard2024largevalues.md#the-short-interval-input),
Corollary 1.3 of arXiv:2405.20552v2, already gives a uniform prime-count
asymptotic for lengths between $x^{17/30+\epsilon}$ and $x^{99/100}$.
Use that existing theorem directly, without repeating its proof or its
FIB sampling applications. Here its consumer is the original complete
strict inventory between the same actual clocks $B_i$ and $A_i=B_i+t_i$.
The source windows, supplied $\eta$, every maximizing tie and all outgoing
weights remain unchanged.

### Match the interval length using the paid clock ceiling

Put $\Delta=1-\Theta>0$. Assume the original fixed parameters satisfy

$$
\boxed{1-\Theta<\eta<\frac12,\qquad
\eta<\frac{1-\Theta}{1-\Theta+17/30}.}
\tag{SI1}
$$

This is a restriction on the supplied $\eta$, not a choice of a new
oscillation exponent. Fix once an interval exponent
$17/30<r<99/100$ with $\eta\le\Delta/(\Delta+r)$; SI1 permits such
a choice. SC2 and the original $\ell_X=(d/8)X^{1-\eta}\log X$ give

$$
\frac{B_{\max,X}^{r}}{\ell_X}
\ll X^{r\eta/\Delta-(1-\eta)}
(\log X)^{-1-r/\Delta}\longrightarrow0.
$$

The exponent of $X$ is nonpositive, including when
$\eta=\Delta/(\Delta+r)$; the logarithmic exponent is strictly negative.
Consequently $t_i/B_i^r\to\infty$ uniformly in labels and ties.
The existing CR17 supplies $t_i/B_i\to0$. This range is contained in
SC4, but its boundary at $\eta=\Delta/(\Delta+17/30)$ is not included:
the cited theorem requires a fixed positive $\epsilon$.

### Partition a long actual lag into admitted intervals

For one actual label write $A=B+t$ and set $H=(2B)^r$.
Eventually $A\le2B$ and $t/H\to\infty$ uniformly. Put
$n=\lfloor t/H\rfloor\ge1$, $h=t/n$, and
$x_j=B+jh$ for $0\le j<n$. Then

$$
H\le h\le2H,\qquad B\le x_j<A\le2B.
$$

With $\epsilon=r-17/30>0$ fixed, every block meets the supplier's
moving-start conditions:

$$
x_j^{17/30+\epsilon}=x_j^r\le H\le h,
\qquad h\le2(2B)^r\le x_j^{99/100}
$$

beyond a single common start. Thus no assumption that the whole lag
$t$ is at most $B^{99/100}$ is needed. The count theorem on each block is

$$
\pi(x_j+h)-\pi(x_j)=\frac h{\log x_j}
+O_r\bigl(h\exp[-(\log x_j)^{1/4}]\bigr).
$$

For $\theta_1(x)=\sum_{q\le x,\ q\text{ prime}}\log q$, the logarithms
of the primes in $(x_j,x_j+h]$ lie between $\log x_j$ and
$\log(x_j+h)$. Multiplying the upper and lower count estimates by
these endpoint logarithms gives, uniformly over the blocks,

$$
\left|\theta_1(x_j+h)-\theta_1(x_j)-h\right|
\le C_rh\left[
\log(2B)\exp[-(\log B)^{1/4}]
+\frac{H}{B\log B}\right].
$$

The blocks are disjoint in the original right-continuous counting
convention. Summing their full lengths gives $t$, so define

$$
\varepsilon_r(B)=C_r\left[
\log(2B)\exp[-(\log B)^{1/4}]
+\frac{B^{r-1}}{\log B}\right]\longrightarrow0
$$

with an enlarged fixed $C_r$. Then
$|\theta_1(A)-\theta_1(B)-t|\le\varepsilon_r(B)t$.
The existing complete normal form $Q=K-\psi=O(\sqrt x)$ and the
classical higher-power bound $\psi-\theta_1=O(\sqrt x)$ give
$K-\theta_1=O(\sqrt x)$ on all real clocks. These are full cumulative
estimates: strict activation endpoints, simultaneous layers and higher
prime powers are retained, rather than identified with the first-layer
count. Since $A/B\to1$, their endpoint correction is $O(\sqrt B)$.
For the same actual $D=K(A)-K(B)$ this yields

$$
\boxed{|D-t|\le\varepsilon_r(B)t+C\sqrt B,\qquad
\frac{D_i}{t_i}\longrightarrow1}
\tag{SI2}
$$

uniformly over every original label and maximizing tie in SI1.
The last assertion uses $t_i/B_i^r\to\infty$ and $r>1/2$.
No convergence rate in $X$ or numerical supplier start is asserted.

### Retain the absolute local error and the original compensation

Use the same-source identities from CR44 and ST4,
$E(B)=D+Q(B)$ and
$\psi(A)-\psi(B)-t=D-t+Q(B)-Q(A)$. With an enlarged constant,

$$
\begin{aligned}
|E(B_i)-t_i|&\le\varepsilon_r(B_i)t_i+C\sqrt{B_i},\\
|\psi(A_i)-\psi(B_i)-t_i|
&\le\varepsilon_r(B_i)t_i+C\sqrt{B_i}.
\end{aligned}
$$

All original weights are positive. Hence the full outgoing sum,
including the last weight with endpoint $p_m$, satisfies

$$
\boxed{\sum_{i<m}\delta_i
\frac{|\psi(A_i)-\psi(B_i)-t_i|}{\sqrt{B_i}}
\le\sum_{i<m}\delta_i\varepsilon_r(B_i)
\frac{t_i}{\sqrt{B_i}}+CL_X
=o_X(V_X^{\rm lag})+O(L_X).}
\tag{SI3}
$$

The relative little-o is uniform in ties: the actual minimum core clock
tends to infinity, so the supremum of $\varepsilon_r(B_i)$ tends to zero.
This replaces the positive fixed local coefficient in ST4 by a vanishing
relative allowance only in the stricter range SI1. It does not extend
SI1 to $\Theta=1$ or to SC4's remaining parameters.

Finally keep HC3's complete future term

$$
\mathcal H_X=\sum_{i<m}\frac{\delta_i}{\sqrt{B_i}}
\int_1^\infty E(B_iv)k_{\log B_i}(v)\,dv.
$$

Its existing convergence and all original coefficients are unchanged.
The same local estimate, with the original fixed $a$, gives

$$
\boxed{
\left|\mathcal G_X-
(\mathcal H_X-aV_X^{\rm lag})\right|
\le a\sum_{i<m}\delta_i\varepsilon_r(B_i)
\frac{t_i}{\sqrt{B_i}}+C_aL_X.}
\tag{SI4}
$$

In particular the subtraction is retained, with a controlled error
on the same actual clocks; it is not discarded or assigned an independent
sign. The displayed error is $o(V_X^{\rm lag})+O_a(L_X)$.
No bound $V_X^{\rm lag}=O(M_XL_X)$ has been supplied here, so this is
not asserted to be $o(M_XL_X)$. The subexponential relative allowance
from the cited theorem must not be treated as an arbitrary power saving.
The complete future term $\mathcal H_X$ and its joint relation to the
original lag remain unpaid.

SI1--SI4 are an application of the existing uniform count and paid clock
ceiling to the original local interval and compensation. They introduce
no new prime theorem, generic sampling theorem, literature-priority claim
or Lean declaration. The original all-tie signed comparison, its strict
constant and RH remain unproved.


### The same error is below the target scale on the original large-core part

Keep every original index and weight; divide the account only by the
actual condition $B_i\ge X$. Put
$\mathcal I_X^+=\{i<m:B_i\ge X\}$ and retain its complementary indices
in the full target. The original $t_i\le2\ell_X$ gives

$$
V_X^+=\sum_{i\in\mathcal I_X^+}\delta_i\frac{t_i}{\sqrt{B_i}}
\le\frac{2\ell_X}{\sqrt X}L_X
=\frac d4 M_XL_X.
$$

In SI1, $\sup_{B\ge X}\varepsilon_r(B)\to0$, since the displayed
function tends to zero. The SI3 pointwise estimates therefore imply

$$
\boxed{
\sum_{i\in\mathcal I_X^+}\frac{\delta_i}{\sqrt{B_i}}
\bigl(|E(B_i)-t_i|+
|\psi(A_i)-\psi(B_i)-t_i|\bigr)
=o_X(M_XL_X).}
\tag{SI5}
$$

Here $L_X=o(M_XL_X)$ uses the unchanged $\eta<1/2$.
The estimate is uniform in all ties, including an empty large-core part;
its last original outgoing weight is included whenever its index meets
the condition. With

$$
\mathcal G_X^+=\sum_{i\in\mathcal I_X^+}\delta_iG_a(B_i),\qquad
\mathcal H_X^+=\sum_{i\in\mathcal I_X^+}\frac{\delta_i}{\sqrt{B_i}}
\int_1^\infty E(B_iv)k_{\log B_i}(v)\,dv,
$$

the original compensated quantity consequently satisfies

$$
\mathcal G_X^+=\mathcal H_X^+-aV_X^+
+o_X(M_XL_X).
$$

This pays the local replacement error on the actual large-core part at
the original target scale. It does not bound $\mathcal H_X^+$ or its
signed combination, and the original small-core part $B_i<X$ is still
retained and unpaid. No new source family, favorable window or eventual
absence of small cores is inferred. This application keeps SI1's narrower
range and does not assert a global $V_X^{\rm lag}=O(M_XL_X)$.
SI1 has a nonempty supplied-parameter range only when $\Theta>17/30$.


## The existing density estimate pays a growing high-frequency head sector

Reuse the [Guth--Maynard fixed-real-part density supplier](../Analytic/guthmaynard2024largevalues.md#the-zero-density-input-for-cumulative-contributions),
Theorem 1.2 of arXiv:2405.20552v2. Write its exponent as

$$
g(\sigma)=\frac{15(1-\sigma)}{3+5\sigma},\qquad
N(\sigma,T)\le T^{g(\sigma)+o(1)}.
$$

Only finitely many fixed real-part arguments will be used; no uniform
$o(1)$ over moving $\sigma$ is assumed. The actual zeros and their
multiplicities are the same as in the original compensated heads.
This application introduces no density theorem or new zero-free premise.
Keep the original fixed $\Theta,\eta,d,a$, all qualifying full windows,
every maximizing tie and every original outgoing weight.

### Conditions on the original parameters and the fixed cuts

Put $\Delta=1-\Theta>0$, $\mu=1/2-\eta$ and retain SR3's
$\sigma_{\rm safe}=1/2+\Delta(1/2-\eta)/\eta$. Assume

$$
\boxed{\sigma_{\rm safe}>\frac35,\qquad
h_*:=\frac{\eta-\Delta}{2\Delta[1-g(\Theta)]}
<\frac{1-\eta}{2}.}
\tag{DH1}
$$

The original $\Delta<\eta<1/2$ gives
$\sigma_{\rm safe}<\Theta$. Thus DH1 implies $\Theta>3/5$,
$g(\Theta)<1$ and $h_*>0$, so its denominator is positive.
These are additional restrictions on the supplied parameters; $\eta$
is not reselected. Neither SI1 nor SC4 is assumed, and no claim at
$\Theta=1$ is made.

Fix $h_*<h<(1-\eta)/2$ and define

$$
\mathfrak p_h(\sigma)=
\frac{\eta(\sigma-1/2)}{\Delta}+h[g(\sigma)-1].
$$

At the already defined safe boundary,

$$
\mathfrak p_h(\sigma_{\rm safe})
=\mu+h[g(\sigma_{\rm safe})-1]<\mu,
$$

while

$$
\mathfrak p_h(\Theta)-\mu
=\frac{\eta-\Delta}{2\Delta}-h[1-g(\Theta)]<0.
$$

By continuity fix once $3/5<\sigma_0<\sigma_{\rm safe}$ sufficiently
close to $\sigma_{\rm safe}$ that $\mathfrak p_h(\sigma_0)<\mu$.
All these cuts depend only on the original fixed parameters.
Since $g''(\sigma)=1200/(3+5\sigma)^3>0$, the power allowance is
convex on $[\sigma_0,\Theta]$. Its maximum is at an endpoint. Hence

$$
\varepsilon_0:=\mu-
\max\{\mathfrak p_h(\sigma_0),\mathfrak p_h(\Theta)\}>0.
\tag{DH2}
$$

### Apply the density estimate to the complete original coefficients

Keep the exact original coefficient

$$
c_{B,a}(\rho)=s_BF_B(\rho)-\frac{aB^\rho}{\sqrt B\,\rho}
=\frac{B^{\rho-1/2}}{\rho}[J_{\log B}(\rho)-a].
$$

For $B\ge e^2$ and $\rho=\beta+i\gamma$ with $\gamma\ge1$,
MB2's existing degree-two bound and $|\rho|\ge\gamma$ give

$$
|c_{B,a}(\rho)|
\le B^{\beta-1/2}
\left[\frac{1+1/\log B}{\gamma^2}+\frac a\gamma\right]
\le(a+2)\frac{B^{\beta-1/2}}\gamma.
$$

This bounds the entire coefficient, including the original subtraction;
it is not a degree-two-only estimate or a change of compensation.
Put $H_X=X^h$. At the original individual legal heights $\tau_i$, define

$$
\mathcal R_X=2\sum_{i<m}\delta_i
\sum_{\substack{H_X<\gamma\le\tau_i\\\beta>\sigma_0}}
m_\rho|c_{B_i,a}(\rho)|.
$$

Then, uniformly over all original ties and legal height assignments,

$$
\boxed{\mathcal R_X=o(M_XL_X).}
\tag{DH3}
$$

To verify the estimate, choose a fixed finite partition of
$[\sigma_0,\Theta]$ of maximum width $\delta>0$. For a bin with left
endpoint $\sigma_j$, the existing fixed-parameter density bound and
dyadic summation imply, for every sufficiently small fixed $\epsilon>0$,

$$
\sum_{\substack{\gamma>H_X\\\beta\ge\sigma_j}}
\frac{m_\rho}{\gamma}
\ll_{\sigma_j,\epsilon}H_X^{g(\sigma_j)-1+\epsilon}.
$$

Indeed, on $(2^kH_X,2^{k+1}H_X]$ the reciprocal height is at most
$(2^kH_X)^{-1}$ and the count is at most
$C(2^{k+1}H_X)^{g(\sigma_j)+\epsilon}$. The geometric sum converges
when $g(\sigma_0)+\epsilon<1$. The same $\epsilon$ and one common
height start suffice for the finitely many fixed bins.

SC2 gives $B_{\max,X}\ll X^{\eta/\Delta}$ after discarding only its
favorable logarithmic factor. A bin therefore contributes at most

$$
C L_X B_{\max,X}^{\sigma_j+\delta-1/2}
H_X^{g(\sigma_j)-1+\epsilon}
\ll L_X X^{\mathfrak p_h(\sigma_j)+\eta\delta/\Delta+h\epsilon}.
$$

Fix $\delta,\epsilon$ small enough that
$\eta\delta/\Delta+h\epsilon<\varepsilon_0/2$ and
$g(\sigma_0)+\epsilon<1$. DH2 now bounds the finite bin sum by
$O(L_XX^{\mu-\varepsilon_0/2})=o(M_XL_X)$, proving DH3.
Extending the nonnegative absolute sum beyond each actual $\tau_i$ is
used only as an upper bound for the original masked sector. No actual
mask, coefficient, phase or multiplicity is replaced.

This restricted high-real-part reciprocal-height sum is absolutely
convergent because $g(\sigma_0)<1$. It does not make the full compensated
$1/\rho$ series absolutely summable; CR34 and the earlier complete
compensation obstruction remain unchanged. DH3 pays a specified growing
high-frequency sector, not the full signed head or RH.


## The surviving original head has one common cutoff under DH1

Keep DH1--DH3's fixed cuts and the same original core-selected legal
heights from CR45. Since $t_i/B_i\to0$ and $t_i\ge\ell_X$,
one common start has $B_i\ge\ell_X$ uniformly in all labels and ties.
Every original legal $\tau_i\ge(\sqrt{B_i}-4)/4$ is eventually at least
$\sqrt{B_i}/8$. Thus

$$
\frac{H_X}{\min_i\tau_i}
\ll X^{h-(1-\eta)/2}(\log X)^{-1/2}\longrightarrow0.
$$

In particular every original head contains the same actual zero set
with $0<\gamma\le H_X$. Define its unabridged complementary-real-part
contribution

$$
\mathcal P_X^{\rm common}
=2\operatorname{Re}
\sum_{\substack{0<\gamma\le H_X\\\beta>\sigma_0}}
m_\rho\sum_{i<m}\delta_i c_{B_i,a}(\rho).
$$

Finite summation is exchanged only after establishing common membership.
Every coefficient retains its original $J_{\log B_i}(\rho)-a$,
real part, phase and multiplicity; the full original outgoing sum,
including its last endpoint $p_m$, remains inside.

Apply the already proved SR3 directly at the fixed
$\sigma_0<\sigma_{\rm safe}$, rather than at a moving threshold or an
unpaid endpoint. It pays the whole lower-real-part subhead at the
original individual heights. DH3 pays the absolute complementary-real-part
portion above $H_X$. The resulting exact partition of those original
heads therefore gives

$$
\sum_{i<m}\delta_i H_{B_i,a}(\tau_i)
=\mathcal P_X^{\rm common}+o_X(M_XL_X).
$$

Finally reuse HC2's original complete height account, with its
$O_a(L_X)$ discrepancy and $M_X\to\infty$, to obtain

$$
\boxed{\mathcal G_X
=\mathcal P_X^{\rm common}+o_X(M_XL_X).}
\tag{DH4}
$$

The error is uniform in all original maximizing ties and admissible
height assignments. Consequently the original cofinal-full-window,
all-tie upper comparison for $\mathcal G_X$ can be transferred to
$\mathcal P_X^{\rm common}$, and conversely, with an arbitrarily small
fixed loss of strict margin below $d(1-\kappa)/16$. No cofinal window is
created or shortened by the partition.

The cut $H_X$ is a place to split an existing legal head; it is not
asserted to be an admissible CHJ height, and CHJ is not reapplied there.
The original heights have not been optimized to buy a leading saving.
The saving comes from a proved density bound on the original discarded
sector, together with the already paid SR and HC accounts.

For a nonempty parameter example, if the originally supplied
$(\Theta,\eta)=(3/4,13/50)$, then
$\sigma_{\rm safe}=19/26$, $h_*=9/200$ and
$(1-\eta)/2=37/100$. The fixed cuts $h=1/10$, $\sigma_0=7/10$ obey
DH1--DH2: $g(\sigma_0)=9/13$,
$\mathfrak p_h(\sigma_0)=288/1625$,
$\mathfrak p_h(\Theta)=97/450$, and the endpoint margin below
$\mu=6/25$ is $11/450$. This is a conditional parameter example; it
supplies neither an actual value of $\Theta$ nor a replacement for the
original $\eta$.

The common cutoff still grows. Each fixed actual off-critical zero
ultimately lies inside it, so the earlier fixed-zero budget obstruction
is retained. A bound for one fixed zero pair does not bound the growing
common head without a joint family estimate. DH4 proves no cancellation
or upper budget for that head.

DH1--DH4 are source-specific paper applications of the existing density,
coefficient, clock, lower-sector and height suppliers. There is no new
generic density or sampling theorem, literature-priority claim, Lean
declaration or kernel verification. The signed common-head comparison,
the complete original target and RH remain unproved. The Ingham extension
below supplies another parameter range for the same reduction; neither
density application covers $\Theta=1$.


## The published Ingham estimate extends the same head reduction below three fifths

Reuse Chourasiya--Simonič,
[arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2), Corollary 1
and Table 1, already used for a different coefficient in
[the interpolation note](../Weil/corvalan2023interpolation.md#a-zero-density-contour-for-the-actual-band-coefficient).
For every fixed $1/2<\sigma<1$, their estimate implies

$$
N(\sigma,T)\ll_\sigma T^{d_I(\sigma)}\log^3(2T),\qquad
 d_I(\sigma)=\frac{3(1-\sigma)}{2-\sigma}<1.
$$

The source counts $\beta\ge\sigma$, $0<\gamma\le T$ with
multiplicity and states its bound for $T\ge3\cdot10^{12}$; bounded
lower heights are absorbed into the constant. The published estimate
is used directly. Its exponent improves $g(\sigma)$ for
$1/2<\sigma<7/10$ and agrees at $7/10$.

Keep every original supplier, fixed $\Theta,\eta,d,a$, full window,
maximizing tie, outgoing weight and legal height of DH3--DH4. Suppose
that these originally supplied parameters satisfy

$$
\boxed{\frac12<\Theta\le\frac7{10},\qquad
\Delta<\eta<
 U(\Theta):=\frac{1-\Theta^2}{1+2\Theta-2\Theta^2}.}
\tag{IH1}
$$

Here $\Delta=1-\Theta$, $\mu=1/2-\eta$ and
$\sigma_{\rm safe}=1/2+\Delta\mu/\eta$ retain their meanings.
For this range, $\Delta<U(\Theta)<1/2$, so IH1 is a nonempty
restriction on the original parameters. It does not replace their
supplied $\eta$. Since
$1-d_I(\Theta)=(2\Theta-1)/(2-\Theta)>0$, its upper restriction
is equivalent to

$$
h_I^*:=\frac{\eta-\Delta}{2\Delta[1-d_I(\Theta)]}
<\frac{1-\eta}{2}.
$$

Fix $h_I^*<h<(1-\eta)/2$ and any fixed
$1/2<\sigma_0<\sigma_{\rm safe}<\Theta$. For
$\sigma\in[\sigma_0,\Theta]$, put

$$
\mathfrak p_h^I(\sigma)=
\frac{\eta(\sigma-1/2)}\Delta+h[d_I(\sigma)-1].
$$

Unlike the convex exponent in DH2, $d_I$ is concave. Its needed
power bound follows instead from

$$
(\mathfrak p_h^I)'(\sigma)
=\frac\eta\Delta-\frac{3h}{(2-\sigma)^2}
>1-\frac{150}{169}=\frac{19}{169}>0,
$$

using $\eta/\Delta>1$, $h<1/2$ and
$(2-\sigma)^2\ge169/100$. Consequently

$$
\boxed{\varepsilon_I:=\mu-\mathfrak p_h^I(\Theta)
=h[1-d_I(\Theta)]-\frac{\eta-\Delta}{2\Delta}>0,\qquad
\mathfrak p_h^I(\sigma)\le\mu-\varepsilon_I.}
\tag{IH2}
$$

Apply DH3's finite-bin argument to the same complete coefficient
$c_{B,a}(\rho)$ with $H_X=X^h$, including $\beta=\Theta$ in the
last bin if attained. For each fixed bin left endpoint
$\sigma_j$, the cited density bound and the same dyadic summation give
$\sum_{\gamma>H_X,\,\beta\ge\sigma_j}m_\rho/\gamma
\ll H_X^{d_I(\sigma_j)-1+\epsilon}$, with a common sufficiently
small fixed $\epsilon>0$ over the finitely many bins. Because
$d_I(\sigma_0)<1$, this reciprocal-height sum converges. Choose the
fixed bin width $\delta$ and $\epsilon$ so that
$\eta\delta/\Delta+h\epsilon<\varepsilon_I/2$ and
$d_I(\sigma_0)+\epsilon<1$. The existing coefficient bound and SC2
then give

$$
\boxed{2\sum_{i<m}\delta_i
\sum_{\substack{X^h<\gamma\le\tau_i\\\beta>\sigma_0}}
m_\rho|c_{B_i,a}(\rho)|
\ll L_XX^{\mu-\varepsilon_I/2}=o(M_XL_X).}
\tag{IH3}
$$

As in DH3, extending each nonnegative sum above its original height
is only an upper bound. No coefficient, subtraction, phase or mask
is replaced. The inequality $h<(1-\eta)/2$ puts $X^h$ below every
original legal height at one common start. SR3 pays the full sector
$\beta\le\sigma_0$, and HC2 supplies the same complete height account.
Thus the actual reduction DH4 also holds under IH1:

$$
\boxed{\mathcal G_X=
2\operatorname{Re}
\sum_{\substack{0<\gamma\le X^h\\\beta>\sigma_0}}
m_\rho\sum_{i<m}\delta_i c_{B_i,a}(\rho)
+o(M_XL_X).}
\tag{IH4}
$$

The error has the same uniformity over all original full windows,
ties and legal heights. It transfers their original cofinal upper
comparison with an arbitrarily small fixed loss of strict margin.

For a conditional example outside DH1, take the original parameters
$\Theta=11/20$, $\eta=23/50$. Then
$\mu=1/25$, $\sigma_{\rm safe}=62/115<3/5$,
$d_I(\Theta)=27/29$ and $h_I^*=29/180$.
The fixed cuts $h=1/5$, $\sigma_0=53/100$ satisfy IH1--IH2 with
$\varepsilon_I=7/2610$. This supplies no actual value of $\Theta$
and does not authorize reselecting $\eta$.

IH1--IH4 retain the growing common low head. Every fixed actual
off-critical zero ultimately lies inside it, and its joint signed
upper estimate is still required. The extension excludes $\Theta=1$.
It is an application of existing density, clock, coefficient and height
results to the original source, with no new density theorem,
literature-priority claim, Lean declaration or kernel certification.
The full Robin comparison and RH remain unproved.


## A local frequency cut controls a compact band without a clock ceiling

Keep MB1--MB3's actual source, every original full window and tie,
CR45--CR47's fixed $a$, the positive outgoing weights $\delta_i$,
and the original individual legal heights $\tau_i$. Reuse the
[Huxley density exponent recorded in Guth--Maynard, equation (1.3)](../Analytic/guthmaynard2024largevalues.md#the-zero-density-input-for-cumulative-contributions).
For each fixed $3/4\le\sigma<1$ and fixed $\varepsilon>0$, it gives

$$
N(\sigma,T)\ll_{\sigma,\varepsilon}T^{d_H(\sigma)+\varepsilon},
\qquad d_H(\sigma)=\frac{3(1-\sigma)}{3\sigma-1}.
$$

Fix $5/6<\sigma_0<\sigma_1<1$. Define
$e_h(\sigma)=\sigma-1/2+h[d_H(\sigma)-1]$. Since

$$
e_{1/2}(\sigma)
=\frac{(1-\sigma)(5-6\sigma)}{2(3\sigma-1)}<0,
$$

compactness permits a fixed $0<h<1/2$ with

$$
\epsilon_H:=-\max_{\sigma\in[\sigma_0,\sigma_1]}e_h(\sigma)>0.
\tag{HR1}
$$

The local lower cut is $B_i^h$. Its upper mask remains the actual
$\tau_i\in[(\sqrt{B_i}-4)/4,(\sqrt{B_i}-4)/2]$; hence the lower
cut lies below every legal upper height at a common source start.
For the complete coefficient, DH3's proof already supplies
$|c_{B,a}(\rho)|\le(a+2)B^{\beta-1/2}/\gamma$ for $\gamma\ge1$.
This retains the original $-aB^{\rho-1/2}/\rho$ subtraction.

Apply DH3's finite-bin argument directly in the clock $B$. Choose
disjoint half-open bins $J_j$ covering $[\sigma_0,\sigma_1]$,
closing the last bin at $\sigma_1$, with width at most
$\epsilon_H/4$. Write their endpoints as $\sigma_j,\sigma_{j+1}$.
At each fixed left endpoint $\sigma_j$, dyadic
summation of the cited density bound gives
$\sum_{\gamma>T,\,\beta\ge\sigma_j}m_\rho/\gamma
\ll T^{d_H(\sigma_j)-1+\varepsilon}$.
Choose one fixed $\varepsilon>0$ with
$h\varepsilon\le\epsilon_H/4$ and
$d_H(\sigma_j)+\varepsilon<1$ for every bin. Then

$$
\begin{aligned}
\sum_{\substack{\gamma>B^h\\
\beta\in J_j}}
 m_\rho|c_{B,a}(\rho)|
&\ll B^{\sigma_{j+1}-1/2+h[d_H(\sigma_j)-1+\varepsilon]}\\
&\le B^{-\epsilon_H/2}.
\end{aligned}
\tag{HR2}
$$

Only finitely many fixed real-part parameters are used. Extending
this positive bound beyond $\tau_i$ is an upper estimate for the
selected subhead. Summing the bins and the original residence gives

$$
\boxed{
\mathcal R_X^{\rm band}:=
2\sum_{i<m}\delta_i
\sum_{\substack{B_i^h<\gamma\le\tau_i\\
                 \sigma_0\le\beta\le\sigma_1}}
 m_\rho|c_{B_i,a}(\rho)|
\ll L_Xb_X^{-\epsilon_H/2}
=o(L_X)=o(M_XL_X).}
\tag{HR3}
$$

Here $b_X=\min_{i<m}B_i\to\infty$ and
$\sum_{i<m}\delta_i=L_X$. The constants are uniform over original
windows, ties and legal height assignments. No upper bound on the
core clocks or restriction $\Theta<1$ is used, so HR3 also applies
when $\Theta=1$ on its original supplied parameter range.

For a concrete nonempty choice, take
$\sigma_0=9/10$, $\sigma_1=99/100$ and $h=499/1000$.
The identity $d_H''(\sigma)=36/(3\sigma-1)^3>0$ makes $e_h$ convex,
and its endpoint values are $-93/8500$ and $-69/49250$.
Thus $\epsilon_H=69/49250$ gives
$\mathcal R_X^{\rm band}\ll L_Xb_X^{-69/98500}$.

Deleting exactly this subset from the original weighted real head
changes that head by at most $\mathcal R_X^{\rm band}$. All low
frequencies and real parts outside the fixed band remain in its
complement. No estimate uniform as $\sigma_1\uparrow1$ is established here,
and no sign for that complement is supplied. It is a paper application
of the cited density estimate and existing coefficient bound, with
no new density theorem, literature-priority claim or Lean
certification. The full signed comparison, Robin inequality and RH
remain unproved.


## Existing bounded-variation quadrature transports every original core tie

Reuse N1--N2, PG1 and the actual real-parameter finite envelope from
[the original full-window source](../ArithSums/trureturing2026extrawindowpairing.md).
PT9 already applies bounded-variation quadrature to the original price-tent
readout at the total clock. Its supplier is S. S. Dragomir, *The Ostrowski
integral inequality for mappings of bounded variation*, Corollary 7,
equations (5.16)--(5.17), printed p.507,
[DOI 10.1017/S0004972700036662](https://doi.org/10.1017/S0004972700036662),
also cited in the [Nicolas comparison note](../ArithSums/nicolas2025comparison.md).
The published mesh-times-variation bound is reused here for the different
core-clock readout. No generic quadrature theorem is proved anew.

Keep the original fixed $\Theta,\eta,d,a$, the full prime-label list,
$t_i=\log p_i$, every outgoing $\delta_i=t_{i+1}-t_i$ for $i<m$, and
its actual boundary $t_m$. Write the original coarse ceiling as
$R_X=\exp(c_RX^{\eta/2})$, where $c_R>0$ is fixed, and reuse the paid
label mesh

$$
\max_{i<m}\delta_i\le\varepsilon_X^{\rm lab}:=
\exp(-5\ell_X/12),\qquad
\ell_X=(d/8)X^{1-\eta}\log X,\qquad L_X=t_m-t_0\sim\ell_X.
$$

For the same finite integer-core domain $\mathcal C_X$, put

$$
\mathcal B_X(t)=\log u_{\min}(t)=\mathcal A_X(t)-t,
\qquad t\in[t_0,t_m].
$$

This is the existing least-core selector, observed at its core clock
rather than its total clock. Real $t$ is an interpolation parameter;
$e^t$ is not declared a new prime label or an actual integer source.

### The actual nested integer chain bounds the number of switches

Let $\mathscr U_X$ be the finite set of all cores active anywhere on
$[t_0,t_m]$, including cores active only at a multiple tie. N2 orders all
choices at distinct parameters. PG1 identifies each active core as the
literal strict inventory at its own clock $t+\log u$. At one parameter,
ordering two different cores orders those clocks as well. Inventory
nesting therefore puts the whole set in one divisibility chain:

$$
V_0\mid V_1\mid\cdots\mid V_{J_X},\qquad
V_0<V_1<\cdots<V_{J_X}.
$$

Every successive quotient is an integer at least two. Hence

$$
\boxed{J_X\log2\le\log V_{J_X}-\log V_0\le R_X.}
\tag{CQ1}
$$

Each genuine envelope switch moves to a strictly larger core, so there
are at most $J_X$ such switches. A switch at $t_0$ is included and one
at $t_m$ is excluded for the outgoing quadrature. Simultaneous activation
masses and intermediate tied cores remain in the chain; they are not
counted as independent prime labels or discarded as exceptional sources.
The least-core clock $\mathcal B_X$ is constant between these switches.

### Apply the existing quadrature bound with every original tie tag

Let $\mathscr B_X=\{\log V_j:0\le j\le J_X\}$ and let
$g:\mathscr B_X\to\mathbb R$ be any bounded readout, with
$F_g=\max_{B\in\mathscr B_X}|g(B)|$. Fix an arbitrary original
maximizing-tie assignment $\mathcal T=(U_i)_{i=0}^m$, and put
$B_i=\log U_i$ as before. Start with the step function
$g(\mathcal B_X(t))$ and, at each original weighted tag $t_i$, assign
it the value $g(B_i)$. Call the resulting function $h_{\mathcal T}$.
It differs from the least-core readout only at finitely many tie points,
so its ordinary integral is unchanged.

There is no variation between switches. At a switch, the two one-sided
values and the assigned value are all bounded by $F_g$; their two jumps
have total size at most $4F_g$. The left boundary needs at most one
such jump, and the unsampled right boundary retains the least-core value.
Thus $\operatorname{Var}_{[t_0,t_m]}h_{\mathcal T}\le4J_XF_g$.
Apply Dragomir's existing arbitrary-partition result to the original
partition $(t_i)$ and its left tags. This gives, uniformly in all ties,

$$
\boxed{
\left|\sum_{i<m}\delta_i g(B_i)
-\int_{t_0}^{t_m}g(\mathcal B_X(t))\,dt\right|
\le4\varepsilon_X^{\rm lab}J_XF_g
\le\frac4{\log2}\varepsilon_X^{\rm lab}R_XF_g.}
\tag{CQ2}
$$

For a complex readout, applying the same supplier to its real and
imaginary parts gives the same bound with $4$ replaced by $8$.
This treatment includes a label lying exactly at a multiple switch.
The last original weight still uses $t_m$; no prime tag is removed,
no arbitrary shortened window is introduced, and no favorable tie is
chosen. The continuous integral records occupation of the same actual
finite integer-core envelope. Its pushforward in the core clock is
still atomic, rather than Lebesgue measure in $B$ or an independent
sampling law.

### Core Mellin readouts have no frequency derivative loss in this transport

For $1/2\le\sigma\le1$ and any $\gamma\in\mathbb R$, take
$g(B)=B^{\sigma-1/2+i\gamma}$. All active core clocks are eventually
greater than one: the original all-tie lower endpoint tends to infinity,
and N2 orders every intervening active core above it. Since $B\le R_X$,
$|g(B)|=B^{\sigma-1/2}\le\sqrt{R_X}$. Consequently

$$
\boxed{
\sup_{\mathcal T}\sup_{\substack{1/2\le\sigma\le1\\\gamma\in\mathbb R}}
\left|\sum_{i<m}\delta_i B_i^{\sigma-1/2+i\gamma}
-\int_{t_0}^{t_m}\mathcal B_X(t)^{\sigma-1/2+i\gamma}\,dt\right|
\le\frac8{\log2}\varepsilon_X^{\rm lab}R_X^{3/2}=o_X(1).}
\tag{CQ3}
$$

Indeed the logarithm of the last scale is
$-5\ell_X/12+(3/2)c_RX^{\eta/2}\to-\infty$, because the unchanged
$\eta<1/2$ implies $1-\eta>\eta/2$. The bound uses only the readout's
magnitude, not a derivative in $\gamma$. It is therefore uniform in
frequency and retains actual real parts and phases.

CQ3 controls only transport error. It does not make the continuous
Mellin integral small or impose a favorable phase distribution. A uniform
error for one readout cannot be summed over an infinite zero family
without a separately paid coefficient sum. CQ1--CQ3 are applications of
the existing actual-source and quadrature suppliers, without a new
sampling theorem, literature-priority claim or Lean verification.
No $\Theta<1$, SI1, SC4 or DH1 condition is needed for this transport;
the original signed comparison and RH remain unproved.


## The complete compensated sum has a tie-independent continuous account

Keep CQ1--CQ3's actual finite core selector and every original full-window
endpoint. Reuse the [Trudgian all-prime-power PNT bound](../Weil/trudgian2014pnt.md),
Theorem 1 of arXiv:1401.2689v2. Its recorded modulus $b(\log v)$ satisfies
$(\log v)^2b(\log v)\to0$. Thus some fixed $C_{\rm PNT}$ and one common
real start give

$$
|E(v)|=|v-\psi(v)|\le C_{\rm PNT}\frac v{\log^2v}.
$$

This is a weaker consequence of the existing unconditional supplier,
not a new prime-error theorem, an RH premise or an estimate at selected
phases. Every prime power and the weak endpoint convention of $\psi$
remain. The lower endpoint's original all-tie core clock tends to
infinity; N2 therefore puts every intervening active core above this
same PNT start after enlarging only the common source start.

### A coarse majorant pays the whole improper future integral

For an active core clock $B$, let $L=\log B\ge1$ and use the original
HC3 kernel, subtraction and infinite upper endpoint. Directly applying
the reused PNT bound gives

$$
\begin{aligned}
\left|\int_1^\infty E(Bv)k_L(v)\,dv\right|
&\le C_{\rm PNT}B
\int_1^\infty\frac{v k_L(v)}{(L+\log v)^2}\,dv\\
&=C_{\rm PNT}BL
\int_0^\infty\frac{1+L+y}{(L+y)^4}\,dy\\
&=C_{\rm PNT}B\left(\frac1{2L}+\frac1{3L^2}\right).
\end{aligned}
$$

The last integral is absolutely convergent. It integrates the complete
future error majorant, rather than using the nonintegrable coarse bound
$|E(Bv)|=O(Bv)$ with the same kernel. Applying the same PNT supplier
also to the retained local subtraction yields

$$
\boxed{
|G_a(B)|\le C_{\rm PNT}\sqrt B
\left[\frac1{2\log B}+\frac{a+1/3}{\log^2 B}\right]
\le C_{\rm PNT}(a+5/6)\sqrt{R_X}.}
\tag{CQ4}
$$

This is only a coarse absolute majorant for quadrature. It is not the
original $M_X$-scale signed upper estimate, and the favorable PNT
decay has not been promoted to a saving on that target.

### Apply the original quadrature to the entire compensated readout

Define the same-envelope continuous account

$$
\mathcal J_X=\int_{t_0}^{t_m}G_a(\mathcal B_X(t))\,dt.
$$

It uses the original full label interval, actual integer-core response,
complete future prime-deficit average and fixed original $a$. CQ2 and
CQ4 give uniformly in every original maximizing-tie assignment

$$
\boxed{
\sup_{\mathcal T}
|\mathcal G_{X,\mathcal T}-\mathcal J_X|
\le\frac{4C_{\rm PNT}(a+5/6)}{\log2}
\varepsilon_X^{\rm lab}R_X^{3/2}=o_X(1).}
\tag{CQ5}
$$

The scale tends to zero by the already established exponent comparison
in CQ3. In particular, any two allowed original tie assignments have
compensated sums differing by $o_X(1)$, not just a relative stock error.
The original full-window estimate with a constant strictly below
$C_*=d(1-\kappa)/16$ is consequently equivalent to the estimate

$$
\mathcal J_X\le C_0 M_XL_X,\qquad C_0<C_*,
\qquad M_X=X^{1/2-\eta}\log X,
$$

with an arbitrarily small fixed loss of strict margin in either
direction. Indeed $M_XL_X\to\infty$ and CQ5 pays the absolute difference
uniformly in all ties on each original window. Both statements keep
one common cofinal sequence of qualifying original full windows;
CQ5 does not prove that a favorable sequence exists.

No $\Theta<1$, SI1, SC4 or DH1 assumption is used in CQ4--CQ5.
Thus this transfer also applies when $\Theta=1$, under the same original
source suppliers. It neither changes $\eta$ nor transports a free-center
average onto the original source without paying that transport.
The measure in $B$ is still the occupation of $\mathcal B_X(t)$,
including all its skips and constant-core branches; no smooth inverse
inventory, Fourier decay or phase independence follows.

### The already reduced common head transports by the same account

If DH1 or IH1 holds, retain the corresponding actual growing cutoff $H_X=X^h$,
fixed real-part cut $\sigma_0$ and exact common-head readout

$$
P_X(B)=2\operatorname{Re}
\sum_{\substack{0<\gamma\le H_X\\\beta>\sigma_0}}
 m_\rho c_{B,a}(\rho).
$$

The existing complete coefficient majorants and zero-count consequence,
as already used in SR1, give
$\sup_{B\in\mathscr B_X}|P_X(B)|
\ll_a\sqrt{R_X}(1+\log^2H_X)$.
CQ2 pays its transport by
$O_a(\varepsilon_X^{\rm lab}R_X^{3/2}(1+\log^2H_X))=o_X(1)$.
Reuse DH4 or IH4 once and exchange only its finite common sum to obtain

$$
\boxed{
\mathcal J_X=
2\operatorname{Re}
\sum_{\substack{0<\gamma\le H_X\\\beta>\sigma_0}}
 m_\rho\int_{t_0}^{t_m}
 c_{\mathcal B_X(t),a}(\rho)\,dt
+o_X(M_XL_X).}
\tag{CQ6}
$$

The original subtraction, real parts, phases and multiplicities remain.
No explicit formula is applied at $H_X$, no original legal mask is
optimized, and no error is summed over an infinite compensated series.
CQ6 is a quantitative continuous representation of the same unpaid
common head; its growing joint signed bound is still required.

CQ4--CQ6 are source-specific paper applications of existing PNT,
quadrature and spectral suppliers. They supply no new PNT, generic
sampling theorem, literature-priority claim, Lean declaration or kernel
verification. The actual continuous signed estimate, original Robin
comparison and RH remain unproved.


## The existing PNT modulus bounds original clocks also at supremum one

Work conditionally under the original H1 source hypotheses. Assume RH
failure, retain the actual zero-real-part supremum and supplied parameters

$$
\Theta\in(1/2,1],\qquad 1-\Theta<\eta<1/2,\qquad d>0,
\qquad 0<\kappa<1,\qquad 0<a<5\kappa/8.
$$

Here $\eta$ is the original H1/CR19 exponent denoted $b$ there;
$a$ is CR45--CR47's fixed compensation parameter. Keep all original
labels $t_i=\log p_i$, $i=0,\ldots,m$, their full window and every
maximizing tie. Reuse the original unabridged CR19 height and
[Trudgian's all-prime-power PNT modulus](../Weil/trudgian2014pnt.md),
Theorem 1 of arXiv:1401.2689v2. Write

$$
r_{\rm PNT}=6.455,\qquad
 a_{\rm PNT}=\sqrt{\frac8{17\pi}},\qquad
b(y)=a_{\rm PNT}(y/r_{\rm PNT})^{1/4}
 e^{-\sqrt{y/r_{\rm PNT}}}.
$$

These are the supplier's constants; $a_{\rm PNT}$ is unrelated to the
original compensation parameter $a$. Its bound is
$|\psi(v)-v|/v\le b(\log v)$ for every real $v\ge23$.
Keep N1/N2's exact ceiling $R$ and common finite source domain

$$
\mathcal C_X=\{u\in\mathbb N_{>0}:5040\mid u,\ \log u\le R,
\ \text{every prime divisor of }u\text{ is at most }R\},
\qquad h\in[\ell_X,2\ell_X].
$$

This is the original finite integer-core domain, not a real relaxation.
Let $\mathcal U_i$ be its entire set of active cores at $h=t_i$ and put

$$
B^{\rm end}_{\max,X}
=\max_{0\le i\le m}\ \max_{u\in\mathcal U_i}\log u.
$$

This maximum includes the terminal label and all its ties. The existing
weighted-label maximum $B_{\max,X}=\max_{i<m}B_i$ for any original
tie assignment is at most $B^{\rm end}_{\max,X}$.
All original core clocks tend uniformly to infinity. Choose one common
existential source start for N1/N2, every original label and endpoint tie,
all intervening active cores, CR19's nonnegative removal term, $B\ge23$,
$B\ge e^2$, $L=\log B>1$ and, in CP3, $\sigma_X\le1$.
No numeric start is supplied. No additional $\Theta<1$ supplier or
short-interval hypothesis is used; the inherited source hypotheses remain.

### Consume the complete integral and the retained height once

In the original improper integral, the change $v=e^y$ gives

$$
|I_\psi(B)|\le\int_L^\infty b(y)\frac{1+y}{y^2}\,dy
\le2a_{\rm PNT}r_{\rm PNT}^{-1/4}
 \int_L^\infty y^{-3/4}e^{-\sqrt{y/r_{\rm PNT}}}\,dy.
$$

With $z=\sqrt{y/r_{\rm PNT}}$, this is at most

$$
4a_{\rm PNT}\int_{\sqrt{L/r_{\rm PNT}}}^\infty z^{-1/2}e^{-z}\,dz
\le4a_{\rm PNT}r_{\rm PNT}^{1/4}L^{-1/4}
 e^{-\sqrt{L/r_{\rm PNT}}}.
$$

For each original label and tie, every future endpoint, prime power
and complete coefficient of the original integral remains. CR19's nonnegative second term may be dropped
from its lower bound, yielding $-I_\psi(B)\ge(d/2)X^{-\eta}$.
The same response therefore satisfies

$$
\sqrt{L/r_{\rm PNT}}+\frac14\log L
\le\eta\log X+
\log\frac{8a_{\rm PNT}r_{\rm PNT}^{1/4}}d.
$$

Put $C_d=\max\{0,\log(8a_{\rm PNT}r_{\rm PNT}^{1/4}/d)\}$.
Since $L>1$, this proves uniformly in every original label and tie

$$
\boxed{
\log B^{\rm end}_{\max,X}\le r_{\rm PNT}(\eta\log X+C_d)^2.}
\tag{CP1}
$$

This is a necessary bound on the same actual cores, obtained by comparing
the already retained height with an existing unconditional integral
majorant. It creates no second positive reserve. The original finite
domain $\mathcal C_X$, parameter range $[\ell_X,2\ell_X]$ and exact
ceiling $R$ are unchanged; CP1 bounds the clocks selected inside them. N2 also puts all intervening real-parameter active
cores below the largest original endpoint core, so the same bound
applies to their clocks. Where $\Theta<1$, SC2's stronger polynomial
ceiling remains available. CP1 additionally covers $\Theta=1$.

### The whole critical-line subhead is below scale for every original exponent

At the original individual legal heights, reuse SR1 with $\sigma=1/2$.
Positive original weights and CP1 give

$$
\boxed{
\frac{|S_X^{\le1/2}|}{M_XL_X}
\ll_{\eta,d,a}
X^{-(1/2-\eta)}(\log X)^3\longrightarrow0,
\qquad M_X=X^{1/2-\eta}\log X.}
\tag{CP2}
$$

All ties, real parts, multiplicities and original masks remain.
This holds throughout the inherited range $1-\Theta<\eta<1/2$;
when $\Theta=1$ that range is $0<\eta<1/2$. It extends the
critical-line conclusion that SR5 alone supplied only
for $\eta\le1/4$. It uses neither SC2 nor an assumed phase cancellation.

### A shrinking real-part band also has a paid bound

Fix a constant

$$
0<\zeta<\frac{1/2-\eta}{r_{\rm PNT}\eta^2},\qquad
\sigma_X=\frac12+\frac\zeta{\log X},\qquad
\epsilon_\zeta=\frac12-\eta-r_{\rm PNT}\eta^2\zeta>0.
$$

The proof of SR1 uses the full reciprocal-square sum and the full
reciprocal-height partial sum. Its constant is independent of the
real-part threshold: for $B\ge e^2$, simply bound every retained
$B^{\beta-1/2}$ by $B^{\sigma_X-1/2}$. Thus it may be applied at this
moving cut without a uniform moving-parameter density theorem.
Since $B_{\max,X}\le B^{\rm end}_{\max,X}$, CP1 gives
$B_{\max,X}^{\sigma_X-1/2}\ll_{\eta,d,\zeta}
X^{r_{\rm PNT}\eta^2\zeta}$ and
$1+\log^2 B_{\max,X}=O_{\eta,d}((\log X)^4)$.
Consequently the same original subhead satisfies

$$
\boxed{
\frac{|S_X^{\le\sigma_X}|}{M_XL_X}
\ll_{\eta,d,a,\zeta}
X^{-\epsilon_\zeta}(\log X)^3\longrightarrow0.}
\tag{CP3}
$$

This conclusion retains all original legal height assignments and holds
also when $\Theta=1$. No endpoint atom is moved: the sector is defined
by the inclusive actual condition $\beta\le\sigma_X$ and its complement
is retained. The extra band above the critical line shrinks to it. Every fixed actual
zero with $\beta>1/2$ eventually remains outside the retained sector;
zeros with $\beta<1/2$ remain included. CP3 supplies no fixed-width
zero-free region or signed bound for the remaining head.

CP1--CP3 are applications of the existing PNT, complete-height and
coefficient suppliers to the original selected source. They introduce
no PNT or density theorem, literature-priority claim, Lean declaration
or kernel verification. The complementary signed comparison and RH
remain unproved.


## The retained stronger PNT narrows the same unpaid real-part sector

Keep CP1--CP3's original conditional source hypotheses, fixed supplied
$\Theta,\eta,d,\kappa,a$, exact N1/N2 finite domain and full parameter
window, every original label including $t_m$, and every maximizing tie.
Use the same endpoint-inclusive $B^{\rm end}_{\max,X}$ and weighted
$B_{\max,X}\le B^{\rm end}_{\max,X}$. The original source clock is
$B=\log u$; below $U_X=\log X$ and $L=\log B$ are different quantities.
All starts are common existential starts in the original fixed parameters
and the auxiliary constants below, never label- or tie-dependent.

### Reuse the published PNT shape and its existing inverse scale

The [Nicolas supplier note](../ArithSums/nicolas2025comparison.md)
already records Fiori--Jaskari, arXiv:2609.23222v2, Theorem 1.1 and
Table 1, and its complete-integral consequence. Put

$$
V(y)=\frac{y^{3/5}}{(\log y)^{1/5}},\qquad
D=\frac52\left(\frac53\right)^{1/5}
 \left(\frac{2000}{161967}\right)^{3/5}.
$$

At sufficiently large real arguments the source's extra exponential
factor is at least one. Thus its leading $D$ supplies, for any fixed
$0<c<D$, the already used complete-future majorant

$$
|I_\psi(B)|\le C_c e^{-cV(\log B)}.
$$

The loss $D-c$ absorbs the integrated kernel's polynomial factor;
all prime powers and the improper upper endpoint remain. The source
statement and table are reused: this application does not independently
audit the external analytic proof or computations. It asserts no new
PNT or generic integration theorem.

Reuse CP1's original CR19 consequence
$-I_\psi(B)\ge(d/2)X^{-\eta}$ for every original label and tie.
Combining the two bounds on that same response gives

$$
cV(L)\le\eta U_X+\log(2C_c/d).
\tag{VC1}
$$

The [existing inverse-scale calculation](../Analytic/ng2004summatorymobius.md),
(N5), is the identity
$V(KU^{5/3}(\log U)^{1/3})\sim K^{3/5}(3/5)^{1/5}U$.
Its variables map here to $U=U_X$, its original cutoff logarithm to
$L=\log B$, and its target exponent $1/2$ to the original supplied
$\eta$. No Mertens or odd-prefix bound from that note is transported
to this different arithmetic response; only its scalar inverse is reused.

Fix $K>0$ satisfying

$$
D(3/5)^{1/5}K^{3/5}>\eta.
$$

Choose a fixed $c<D$ still satisfying
$c(3/5)^{1/5}K^{3/5}>\eta$. Eventual monotonicity of $V$ and the
reused inverse imply that $L\ge KU_X^{5/3}(\log U_X)^{1/3}$ would
contradict VC1. Therefore, with every original endpoint and tie retained,

$$
\boxed{
\log B^{\rm end}_{\max,X}
\le K(\log X)^{5/3}(\log\log X)^{1/3}.}
\tag{VC2}
$$

N2 gives the same ceiling for intervening active real-parameter clocks;
those labels do not create new prime-labelled sources. VC2 is a necessary
restriction inside the unchanged source domain, not a new positive reserve.
It includes $\Theta=1$. Where $\Theta<1$, SC2's polynomial source-clock
ceiling remains stronger. Neither the original $\eta$ nor $a$ is reselected.

### Apply the unchanged full coefficient majorant to the wider shrinking band

Reuse SR1 and CP3's threshold-independent absolute majorant. Fix

$$
0<\zeta<\frac{1/2-\eta}{K},\qquad
\widetilde\sigma_X=\frac12+
 \frac{\zeta}{(\log X)^{2/3}(\log\log X)^{1/3}},\qquad
\widetilde\epsilon_\zeta=\frac12-\eta-K\zeta>0.
$$

One common start makes $\widetilde\sigma_X\le1$. VC2 supplies
$B_{\max,X}^{\widetilde\sigma_X-1/2}\le X^{K\zeta}$ and
$1+\log^2 B_{\max,X}=O_K((\log X)^{10/3}(\log\log X)^{2/3})$.
With the original positive outgoing weights summing to $L_X$ and
$M_X=X^{1/2-\eta}\log X$, the same retained subhead obeys

$$
\boxed{
\frac{|S_X^{\le\widetilde\sigma_X}|}{M_XL_X}
\ll_{\eta,d,a,K,\zeta}
X^{-\widetilde\epsilon_\zeta}
 (\log X)^{7/3}(\log\log X)^{2/3}\longrightarrow0.}
\tag{VC3}
$$

The same SR1 majorant applied separately at $\sigma=1/2$ gives its
critical-line subhead this bound with $\widetilde\epsilon_0=1/2-\eta$. Relative to CP3's $1/\log X$ width,
the new band has a larger scale by
$(\log X/\log\log X)^{1/3}$, up to the fixed allowed constants.
This is a consequence of the existing stronger PNT shape at the actual
source clocks, not a new density theorem or moving-parameter density claim.

All original legal height masks, real parts, phases and multiplicities
remain. The complement uses the actual strict condition
$\beta>\widetilde\sigma_X$ and is not discarded. Every fixed zero with
$\beta>1/2$ eventually remains in that unpaid complement; zeros with
$\beta<1/2$ remain in the controlled sector. No positive-width zero-free
region is obtained. The existing removal account permits an arbitrarily
small fixed loss of the strict signed margin, but VC3 supplies no signed
bound for the complementary head or the actual continuous integral.

VC1--VC3 are source-specific paper applications of retained external
PNT, full-height, inverse-scale and coefficient results. They establish
no literature-priority claim, new generic theorem, Lean declaration or
kernel verification. The original full-window signed comparison and RH
remain unproved.

## The preserved height and lag gains have a larger joint lower margin

Keep CP1's original conditional source hypotheses, including
$\Theta\in(1/2,1]$, the supplied $1-\Theta<\eta<1/2$, $d>0$,
$0<\kappa<1$, and the original $0<a<5\kappa/8$. Every original
full window, label, maximizing tie and outgoing weight is retained.
Use the same $A=B+t$, $B=\log u$, $t=\log p$, strict actual core,
and $M_X=X^{1/2-\eta}\log X$. This application consumes CR19,
CR43--CR44 and HC1--HC3; it introduces no new height or prime-error
supplier.

### Combine both positive source terms before splitting by core size

First fix any positive capacity coefficient $C$ with $aC<1$ for which
one constant $H_C$ and a common source start supply
$E(B)\le Ct+H_C\sqrt B$. CR18--CR19, at that same core and
with their complete positive reserves retained, then give

$$
G_a(B)\ge
\frac d2\sqrt B\log B\,X^{-\eta}
+(\chi_{p,u}-aC)\frac t{\sqrt B}-aH_C,
\qquad \chi_{p,u}\longrightarrow1.
\tag{JM1}
$$

The height and removal gain have not been counted as independent
copies of the same contribution: JM1 is their single original CR19
account, followed by the one-sided local error bound.
Put $z=B/X$. Since $t\ge\ell_X=(d/8)X^{1-\eta}\log X$,
division by $M_X$ yields

$$
\frac{G_a(B)}{M_X}\ge
\frac d2\sqrt z\frac{\log B}{\log X}
+\frac d8\frac{\chi_{p,u}-aC}{\sqrt z}
-\frac{aH_C}{M_X}.
\tag{JM2}
$$

CR17 and $t\ge\ell_X$ imply $B/\ell_X\to\infty$ uniformly.
Consequently $\log B/\log X\ge(1-\eta)/2$ beyond one common start.
The second positive term in JM2 excludes $z\to0$ from any sequence
with bounded normalized response, and the first excludes $z\to\infty$.
On each fixed compact subinterval of $(0,\infty)$,
$\log B/\log X=1+\log z/\log X\to1$ uniformly. Thus the ordinary
arithmetic--geometric mean inequality, applied on that compact interval,
gives the uniform lower limit $(d/2)\sqrt{1-aC}$.
The two excluded tails have arbitrarily large lower bounds; they are
not deleted source configurations. CR44 supplies this hypothesis for every fixed $C>8/5$. For each
requested positive error, first choose such a fixed $C$ close enough
to $8/5$ that $aC<1$ and the limiting margin loses less than half
that error, and then choose one common source start. This gives

$$
\boxed{
R_0:=\frac d2\sqrt{1-\frac85a},\qquad
\forall\epsilon>0\quad
G_a(B_i)\ge(R_0-\epsilon)M_X
\quad\text{for every original label and tie eventually}.}
\tag{JM3}
$$

The original restriction on $a$ makes the square root strictly positive.
It also gives $R_0>(d/2)\sqrt{1-\kappa}>d(1-\kappa)/16$.
There is no assumption $B\ge X$, no lag-to-square-root divergence
requirement, and no additional $\Theta<1$ premise in JM1--JM3.
The existing AM--GM inequality is reused; no new generic minimization
theorem or attainability of the minimizing core ratio is claimed.

All original weights are positive. HC2 and CQ5 therefore transport
JM3, with an arbitrarily small fixed loss, to each original head for
every admissible individual height assignment satisfying CR45 and
to the same actual continuous integral:

$$
\mathcal G_{X,\mathcal T}\ge(R_0-\epsilon)M_XL_X,\qquad
S_X(\boldsymbol T)\ge(R_0-\epsilon)M_XL_X,\qquad
\mathcal J_X\ge(R_0-\epsilon)M_XL_X.
\tag{JM4}
$$

These hold eventually on every qualifying full window, every allowed
maximizing-tie assignment $\mathcal T$ and every admissible height
assignment $\boldsymbol T$. The integral is CQ5's
$\mathcal J_X=\int_{t_0}^{t_m}G_a(\mathcal B_X(t))\,dt$, distinct
from the local layer work $J$ below. HC2's $O_a(L_X)$ and CQ5's
$o(1)$ errors are below that scale. In particular, a same-source upper estimate with any fixed
$C_0<R_0$ on a common cofinal sequence of original full windows
would already contradict this RH-failure source. This pays a larger
available lower margin; it does **not** supply that upper estimate,
favorable windows, phase cancellation or the original signed target.
Neither the target nor the RH completion criterion is replaced by
the local bounds below.

## Published uniform counts sharpen capacity at the actual lag scale

Keep JM1--JM4's original source, all full windows and maximizing ties,
and the original fixed $\eta,a$. For this additional application put
$\Delta=1-\Theta>0$ and

$$
\omega=\frac{\Delta(1-\eta)}{\eta},\qquad
\frac12<\omega\le\frac{17}{30}.
\tag{LS1}
$$

When $\omega>17/30$, the stronger existing SI1--SI3 already give
$D/t\to1$ and are reused instead. LS1 includes the boundary
$\omega=17/30$ that SI1's strict condition does not cover. Write
$D=K(A)-K(B)=B-K(B)$ and use the same complete actual layer
measure $\mu$ on $[0,t)$, with work $J=\int r\,d\mu(r)$.
The strict endpoint conventions and all simultaneous higher layers
are unchanged. This local $J$ is distinct from CQ5's $\mathcal J_X$.

### The source floor pays a fixed-exponent blocking allowance

Fix $1/2<s<\omega$. SC2 and the unchanged source floor give

$$
\frac{B_{\max,X}^{s}}{\ell_X}
\ll X^{s\eta/\Delta-(1-\eta)}
(\log X)^{-1-s/\Delta}\longrightarrow0.
\tag{LS2}
$$

In particular $(B^s+\sqrt B)/t\to0$ uniformly on every original
label and tie. All auxiliary exponents and coefficients below are
fixed before selecting one common source start.

The [Iwaniec published count](../Scale/iwaniec1982bruntitchmarsh.md),
Theorem 14 and the final paragraph on printed p.121, supplies, for
every fixed $C>4/(1+s)$, an all-centre bound
$\pi(x+x^s)-\pi(x)\le Cx^s/\log x$ beyond one start.
For any fixed $c>4/(1+s)$ choose $4/(1+s)<C<c$.
First-layer activations in $[B,B+z)$ still come from actual primes
in $(B-1,B+z)$. Starting at $x_0=B-1$, take
$x_{j+1}=x_j+x_j^s$ until these consecutive intervals cover that
actual prefix. Since $0\le z\le t=o(B)$, all block endpoints are
$B(1+o_X(1))$, and the last overhang is $O(B^s)$ uniformly in $z$.
In each block the logarithmic prime weights multiply the count by
at most $\log(x_j+x_j^s)$; their ratio to $\log x_j$ tends to one.
The fixed slack from $C$ to $c$ absorbs that ratio.

Summing the blocks and adding only CR40's already supplied complete
higher-layer mass gives

$$
\boxed{\mu([0,z))\le cz+h_{s,c}(B),\qquad
h_{s,c}(B)=O_{s,c}(B^s)+O(\sqrt B)=o_X(t),
\quad 0\le z\le t.}
\tag{LS3}
$$

The zero-length prefix is trivial. All incomplete blocks are paid,
and no centre, original prime tag, tie or exceptional interval is
discarded. This uses a stronger published count, rather than
repeating the existing sieve proof. The published Section 6 states
its results without proofs; that external proof is not independently
audited here. For $s<1$ its $4/(1+s)$ coefficient is strictly smaller
than the $2/s$ supplied by the recorded uniform Ramaré--Schlage-Puchta
bound at the same blocking scale.

### Consume the same two-cost calculation and BHP terminal envelope

CR41 and the existing finite layer integration before CR42 now give

$$
\frac{(D-h_{s,c}(B))_+^2}{c}+(t-D)^2
\le\mathfrak r_Bt^2,\qquad \mathfrak r_B\to1.
$$

The algebra only requires a positive capacity coefficient, not CR40's
old $c>4$ supplier restriction. For each requested error, first fix
$s<\omega$ sufficiently close to $\omega$, then fix
$c>4/(1+s)$ sufficiently close to that threshold, and finally take
one common start for the vanishing errors. The existing upper root
$2c/(c+1)$ therefore yields

$$
\boxed{\frac Dt\le\frac8{5+\omega}+o_X(1).}
\tag{LS4}
$$

This is uniformly below $8/5$ throughout LS1. If
$21/40\le\omega\le17/30$, SC2 also pays ST1's BHP terminal
allowance $e_B/t\to0$, including equality at $21/40$ by its negative
logarithmic factor. LS3 and that existing lower terminal envelope
constrain the same $\mu$. Consume ST1--ST2's already derived root

$$
\xi(c,b)=\frac{c+\sqrt{c(1-b)(c-b)}}{c+1-b},
\qquad c>b,\quad0<b<1.
$$

The same fixed-coefficient/common-start order gives

$$
\boxed{\frac Dt\le
\xi\!\left(\frac4{1+\omega},\frac9{100}\right)+o_X(1).}
\tag{LS5}
$$

At $\omega=21/40$ its upper coefficient is approximately
$1.43839661$, below ST3's $1.583011267$. These are formula values,
not arithmetic attainability or sharpness claims.

### Independent two-sided counts above the strict eleven-twentieths cut

If $11/20<\omega\le17/30$, fix one sufficiently small positive
$\varepsilon$ with $s=11/20+\varepsilon<\omega$. The independent
[Baker--Harman--Pintz Theorem 3(I)](../Scale/bakerharmanpintz1997goldbach.md),
printed p.4, at $q=1$, supplies the constants $0.99$ and $1.01$
for every sufficiently large centre and every length
$x^s\le M\le x/\log x$. In particular $M=x^s$ is admitted.
Fix also $c>1.01$ and $0<b<0.99$.

Backward blocks $x_{j+1}=x_j-x_j^s$ from the actual prefix's
right endpoint cover $(B-1,B+z)$ at an overhang cost $O(B^s)$.
Their upper counts and each prime's own logarithmic weight give
$\mu([0,z))\le cz+h_B$, with
$h_B=O_{s,c}(B^s)+O(\sqrt B)$.
For the terminal part retain only primes in $(B+z,A-1]$, whose
first-layer activations lie strictly inside $(B+z,A)$. Complete
backward blocks from $A-1$ leave uncovered length $O(B^s)$,
including the empty or shorter-than-one-block case. The fixed slack
below $0.99$ absorbs the ratio of the smallest logarithmic prime
weight to the block's $\log x$. Thus the same complete measure has

$$
\mu([z,t))\ge b(t-z)-e_B,\qquad
e_B=O_{s,b}(1+B^s)=o_X(t),\quad0\le z\le t.
$$

Higher layers are nonnegative in this lower estimate and remain
paid in the upper estimate. Both envelopes concern the same actual
measure. Reuse ST1--ST2's existing competitor root, first choosing
fixed $c\downarrow1.01$ and $b\uparrow0.99$ to each requested
precision and then one common source start. This gives

$$
\boxed{0.99-o_X(1)\le\frac Dt
\le q_{\rm BHP}+o_X(1),\qquad
q_{\rm BHP}=\xi(1.01,0.99)\approx1.004130069.}
\tag{LS6a}
$$

The strict $\omega>11/20$ condition, fixed epsilon and published
length upper bound are retained. The full external analytic proof
and its numerical estimates are not independently re-audited.
BHP's printed p.4 also reports serious errors in Lou--Yao [19].
Its bibliography reference has not been bound to a title and year
from the inspected excerpt. Neither Lou--Yao 1992 nor Lou--Yao 1993
is used as a supplier in the displayed coefficient below; their
printed statements remain recorded in their respective citation
notes, without a theorem-refutation claim. In particular the
near-unit $6/11<\omega\le11/20$ coefficient is not asserted;
LS5's independently supplied coefficient remains available there.

### Transfer the improved stock to the original local account and margin

The selected published inputs supply the following usable coefficient;
this is not a best-known or optimal-constant assertion:

$$
q(\omega)=
\begin{cases}
8/(5+\omega),&1/2<\omega<21/40,\\
\xi(4/(1+\omega),9/100),&21/40\le\omega\le11/20,\\
q_{\rm BHP},&11/20<\omega\le17/30.
\end{cases}
$$

Reuse CR44's exact identities
$E(B)=D+Q(B)$ and
$\psi(A)-\psi(B)-t=D-t+Q(B)-Q(A)$, with the same
$Q(x)=O(\sqrt x)$ and $A/B\to1$. For every fixed positive error,
one common start gives

$$
\begin{aligned}
E(B_i)&\le(q(\omega)+\epsilon)t_i+H_Q\sqrt{B_i},\\
\sum_{i<m}\delta_i
\frac{\psi(A_i)-\psi(B_i)-t_i}{\sqrt{B_i}}
&\le(q(\omega)-1+\epsilon)V_X^{\rm lag}+O(L_X).
\end{aligned}
\tag{LS7}
$$

In the strict BHP 1997 region the lower side of LS6a also pays
the absolute local error with coefficient $0.01+\epsilon$, plus
$O(\sqrt B)$. This is a fixed small relative allowance, not $o(t)$,
and no estimate
$V_X^{\rm lag}=O(M_XL_X)$ for the entire source is inferred.

LS7 supplies JM1's capacity hypothesis for every fixed
$C>q(\omega)$ with $aC<1$. Fix that $C$ to the requested precision
before taking one common source start. JM1--JM4 then give the
further actual-source margin

$$
\boxed{R_\omega=\frac d2\sqrt{1-aq(\omega)}>R_0,}
\tag{LS8}
$$

in the same uniform $R_\omega-\epsilon$ sense, on every original
full window, every tie and every admissible individual height
assignment. The original $a<5\kappa/8$ also makes
$\kappa-aq(\omega)>0$; inserting LS7 into CR46's existing joint
compensation account improves its lag coefficient to
$-(\kappa-aq(\omega)-\epsilon)$ with its existing $O_a(L_X)$
allowance. That same gain is not counted again as a separate reserve.

The full future average in HC3 remains. An upper bound for $E(B)$
gives a lower bound for $-aE(B)$, so these local improvements
strengthen the lower margin and paid compensation, rather than
provide the missing upper estimate for $\mathcal J_X$.
All original weights, terminal labels, parameters, masks and ties
are retained. These are additional project applications of existing
published counts, finite layer integration and competitor roots;
no new generic theorem, Lean declaration, kernel verification,
attainability or literature-originality claim is made. The original
full signed upper estimate, complementary spectral contribution
and RH remain unproved.

## Compact localization improves the margin without a subunit zero supremum

Keep JM1--JM4's complete original conditional source, including
$\Theta=1$ when allowed. This application does not assert LS1 on the
whole source. Instead put $\tau=1-\eta>1/2$ and use the displayed
scalar coefficient $q(\tau)$ when $\tau\le17/30$. Define

$$
Q_\eta=
\begin{cases}
q(1-\eta),&1-\eta\le17/30,\\
1,&1-\eta>17/30.
\end{cases}
\tag{JM5}
$$

Here $q$ means LS4--LS6a's explicit piecewise formula. The
$q(\omega)$ **global stock assertion** still requires LS1; only
its scalar formula and the already matched count suppliers are used
below. No global $D/t\le Q_\eta+o(1)$ claim is made outside that
scope.

### The baseline coercive bound supplies the required localization

Fix any finite level $K$. JM2 with a fixed $C>8/5$, $aC<1$,
and its uniform positive coefficients implies that every original
label satisfying $G_a(B)/M_X\le K$ has
$z=B/X$ in one fixed compact interval $[r_K,R_K]\subset(0,\infty)$
beyond a common source start. Both tails have lower bounds exceeding
$K$. This is a necessary condition on a bounded response, not an
assumption that every core is comparable to $X$ or a deletion of
source configurations.

On any such fixed compact interval the original floor itself gives

$$
\sup_{r_K\le B/X\le R_K}\frac{B^s}{t}
\ll_{K,s}\frac{X^{s-(1-\eta)}}{\log X}\longrightarrow0
\qquad(1/2<s\le1-\eta).
\tag{JM6}
$$

The equality case in this scale calculation is paid by $1/\log X$.
The Iwaniec transfer LS3 therefore applies there with the fixed
exponent $s=1-\eta$. The BHP terminal allowance is negligible when
$1-\eta\ge21/40$, including equality. For the BHP 1997 input,
choose one fixed sufficiently small
positive $\varepsilon$ with $11/20<s=11/20+\varepsilon\le1-\eta$.
Every block has $M=x^s\le x/\log x$ eventually. Such a choice is
available precisely in its strict region of the scalar formula.
All block costs, strict endpoints and higher
layers stay in the preceding actual-source transfers.

If $1-\eta>17/30$, fix
$17/30<r<\min(1-\eta,99/100)$. JM6 gives $t/B^r\to\infty$
on the compact interval. Reuse SI2's partition into admitted
Guth--Maynard intervals and its complete endpoint correction to
obtain $D/t\to1$ there. That partition only requires this length
condition and CR17's $t/B\to0$; SC2 and SI1 were its previous
global suppliers, not hypotheses of the published count itself.
The strict $1-\eta>17/30$ cut is retained.

Thus for every fixed compact interval, every positive error has a
common start with $E(B)\le(Q_\eta+\epsilon)t+H_Q\sqrt B$ for its
original labels and ties. This extends a **localized** consumer;
it does not extend SI1's global statement to $\Theta=1$.

### A bounded-response contradiction transports the stronger lower margin

All branches in JM5 have $Q_\eta<8/5$. Fix a positive requested
error and a finite $K$ larger than the proposed margin. If a cofinal
sequence of original labels violated the proposed uniform lower
bound, its normalized responses would be bounded above by $K$.
JM2 puts that sequence in $[r_K,R_K]$. First choose a fixed
$C>Q_\eta$, sufficiently close to $Q_\eta$ that $aC<1$ and its
margin loss is below the requested precision; then use the preceding
localized estimate at one common start. JM1--JM2, with
$\log B/\log X\to1$ uniformly on this compact interval, and the
same existing AM--GM inequality contradict that violating sequence.
Consequently

$$
\boxed{R_\eta=\frac d2\sqrt{1-aQ_\eta}>R_0,\qquad
G_a(B_i)\ge(R_\eta-\epsilon)M_X}
\tag{JM7}
$$

eventually for every original label and tie, without a $\Theta<1$
premise. Positivity of all original weights and the unchanged
HC2/CQ5 transfers give the same lower bound, multiplied by $L_X$,
for $\mathcal G_{X,\mathcal T}$, every admissible
$S_X(\boldsymbol T)$ and $\mathcal J_X$ on every original full
window. No favorable subsequence of windows is constructed.

For example, when the original $\eta<13/30$, the reused uniform
interval asymptotic gives $Q_\eta=1$ and hence
$R_\eta=(d/2)\sqrt{1-a}$, including $\Theta=1$ under the original
conditional hypotheses. At $\eta=13/30$ the asymptotic branch is
not asserted; the strictly admitted BHP 1997 branch remains.
All strict supplier cuts and fixed-precision common starts are kept.
The improvement is in the lower margin; the original signed upper
estimate on a cofinal family and RH remain unproved. No new generic
compactness, minimization, prime theorem or Lean declaration is
introduced, and no literature-originality or kernel claim is made.

## A common future horizon pays the complete remote remainder

Keep CP1 and JM1--JM7's original conditional source, all endpoints,
labels, maximizing ties and fixed $\Theta,\eta,d,\kappa,a$.
Use CQ5's same actual continuous selector $\mathcal B_X(t)$ on
$[t_0,t_m]$, $L_X=t_m-t_0$, $s_B=\sqrt B\log B$ and the original
$M_X=X^{1/2-\eta}\log X$. No favorable window is selected here.
This application consumes HC3, CQ5, VC1--VC2 and the scalar inverse
already used in VC2; it introduces no new PNT or generic tail theorem.

### One complete tail serves every original core

Write the original absolute-coordinate kernel as

$$
k(u)=\frac{1+\log u}{u^2\log^2u},\qquad
I_\psi(v)=\int_v^\infty(\psi(u)-u)k(u)\,du.
$$

Choose one deterministic ceiling $\mathsf Y_X\to\infty$ with
$\log B\le\mathsf Y_X$ for every original endpoint and intervening
active core. VC2 supplies
$\mathsf Y_X=K(\log X)^{5/3}(\log\log X)^{1/3}$,
with its stated fixed condition on $K$, including $\Theta=1$.
When $\Theta<1$, SC2 and N2 instead permit the smaller choice
$\mathsf Y_X=C\log X$, with any fixed $C>\eta/(1-\Theta)$
and one common source start. Neither choice depends on a tie.

Fix $H>0$ with

$$
D(3/5)^{1/5}H^{3/5}>1/2,
\qquad
\mathsf U_X=\exp\!\left[
H\mathsf Y_X^{5/3}(\log\mathsf Y_X)^{1/3}\right].
$$

Then $\log\mathsf U_X/\mathsf Y_X\to\infty$, so this horizon
eventually lies beyond every original core. The complete-integral
PNT supplier recorded in VC1 bounds $|I_\psi(\mathsf U_X)|$ by
$C_c\exp[-cV(\log\mathsf U_X)]$ for every fixed $0<c<D$.
Choose such a fixed $c$ still satisfying
$c(3/5)^{1/5}H^{3/5}>1/2$. The reused Ng (N5) scalar inverse
then supplies a fixed $\epsilon_H>0$ and common start with
$cV(\log\mathsf U_X)\ge(1/2+\epsilon_H)\mathsf Y_X$.
Consequently

$$
\boxed{
|I_\psi(\mathsf U_X)|
\int_{t_0}^{t_m}s_{\mathcal B_X(t)}\,dt
\le C_c\mathsf Y_Xe^{-\epsilon_H\mathsf Y_X}L_X
=o(L_X)=o(M_XL_X).}
\tag{FH1}
$$

This pays the complete tail from $\mathsf U_X$ to infinity,
including every prime power. It does not discard the future interval
between the actual selected clocks and this common horizon.
The horizon's log scale is $O((\log X)^{5/3}(\log\log X)^{1/3})$
under SC2, and
$O((\log X)^{25/9}(\log\log X)^{8/9})$ under VC2 alone.
These are sufficient asymptotic scales with existential common
starts, not numerical cutoff, effective-computation or optimality claims.

There is also a fully published-input alternative. CP1 already supplies

$$
|I_\psi(v)|\le
4a_{\rm PNT}r_{\rm PNT}^{1/4}(\log v)^{-1/4}
e^{-\sqrt{\log v/r_{\rm PNT}}}.
$$

Use its deterministic ceiling
$\mathsf Y_X=r_{\rm PNT}(\eta\log X+C_d)^2$, fix
$H_0>r_{\rm PNT}/4$, and instead choose
$\mathsf U_X=\exp(H_0\mathsf Y_X^2)$. Evaluating that existing
complete-integral bound at this horizon and using the same occupation
bound gives

$$
|I_\psi(\mathsf U_X)|\int_{t_0}^{t_m}s_{\mathcal B_X(t)}\,dt
\ll_{H_0}\mathsf Y_X^{1/2}
\exp\!\left[-\left(\sqrt{H_0/r_{\rm PNT}}-\frac12\right)
\mathsf Y_X\right]L_X=o(L_X).
$$

Its log horizon is $O((\log X)^4)$, including $\Theta=1$.
With SC2's smaller ceiling it is $O((\log X)^2)$ for fixed
$\Theta<1$. Thus paying a common complete tail does not require the
newer Fiori--Jaskari preprint; that input supplies the smaller stated
horizon. The remainder of the finite account applies to either chosen
horizon. Neither complete analytic proof is independently re-audited.

Define the complete finite-horizon response by

$$
\mathsf J_X^{\rm fin}=
\int_{t_0}^{t_m}\left[
s_{\mathcal B_X(t)}
\int_{\mathcal B_X(t)}^{\mathsf U_X}E(u)k(u)\,du
-\frac{aE(\mathcal B_X(t))}{\sqrt{\mathcal B_X(t)}}
\right]dt,
\qquad E(u)=u-\psi(u).
$$

The original local subtraction is unchanged. Splitting the same
improper integral at $\mathsf U_X$ gives the exact remainder

$$
\boxed{
\mathcal J_X-\mathsf J_X^{\rm fin}
=-I_\psi(\mathsf U_X)
\int_{t_0}^{t_m}s_{\mathcal B_X(t)}\,dt
=o(L_X).}
\tag{FH2}
$$

CQ5 and FH1 therefore make the original all-tie signed target
and its finite-horizon version equivalent, with an arbitrarily
small fixed loss of the strict constant $C_0<d(1-\kappa)/16$.
Both retain one common cofinal sequence of original full windows.
Neither estimate is established by the tail bound.

### The finite account requires a lower bound for one actual prime-power test

The same finite interval gives a direct arithmetic consumer. For
$2\le n\le\mathsf U_X$ set

$$
\begin{aligned}
\mathsf W_X(n)=\int_{t_0}^{t_m}\Bigg[
&s_{\mathcal B_X(t)}
\left\{\frac1{\max(\mathcal B_X(t),n)\log\max(\mathcal B_X(t),n)}
-\frac1{\mathsf U_X\log\mathsf U_X}\right\}\\
&-\frac a{\sqrt{\mathcal B_X(t)}}
\mathbf1_{\{n\le\mathcal B_X(t)\}}\Bigg]dt,
\end{aligned}
$$

and let the corresponding continuum reference be

$$
\mathsf P_X=
\int_{t_0}^{t_m}\left[
s_B\left(\log\log\mathsf U_X-\log\log B
+\frac1{\log B}-\frac1{\log\mathsf U_X}\right)
-a\sqrt B\right]dt,
\qquad B=\mathcal B_X(t).
$$

Reuse $k(u)=-\frac d{du}(1/(u\log u))$,
$\int uk(u)\,du=\log\log u-1/\log u$ and the finite exact
prime-power sum $\psi(u)=\sum_{n\le u}\Lambda(n)$. Exchanging
only that finite sum and the finite integrals gives

$$
\boxed{
\mathsf J_X^{\rm fin}
=\mathsf P_X-
\sum_{2\le n\le\mathsf U_X}\Lambda(n)\mathsf W_X(n).}
\tag{FH3}
$$

All weights come from the same actual selector; no new probability
law, free-centre average or smooth inverse replaces its residence.
The weak $n\le B$ convention retains the local prime-power endpoints.
Terms with $n>\mathsf U_X$ are paid by FH1 rather than silently omitted.

These weights are nonnegative eventually. Pointwise in $t$, if $B<n$
the local subtraction vanishes and the bracket in $\mathsf W_X(n)$
is nonnegative. If $n\le B$, it equals

$$
\frac1{\sqrt B}\left[
1-a-\frac{B\log B}{\mathsf U_X\log\mathsf U_X}\right]\ge0,
$$

since the ratio tends to zero uniformly for $\log B\le\mathsf Y_X$
and the original fixed $a<5\kappa/8<1$. Thus the precise unpaid
finite-source interface is

$$
\boxed{
\sum_{2\le n\le\mathsf U_X}\Lambda(n)\mathsf W_X(n)
\ge\mathsf P_X-C_0M_XL_X,
\qquad C_0<d(1-\kappa)/16.}
\tag{FH4}
$$

FH4 must hold on a common cofinal sequence of the original full
windows, with the same retained source and constants. Weight
nonnegativity alone supplies no comparison with $\mathsf P_X$.
In particular these weights are not decreasing tests. Extend the same
formula from integers $n$ to real $r\in[2,\mathsf U_X]$ and let
$\nu_X$ be the actual occupation measure of $\mathcal B_X$.
The integral term involving $\max(B,r)$ is continuous in $r$.
At any core $B$ with positive residence, the retained local subtraction
therefore gives the exact right jump

$$
\mathsf W_X(B+)-\mathsf W_X(B)
=\frac{a\nu_X(\{B\})}{\sqrt B}>0.
$$

This is the original compensation, not a new freely chosen atom.
Between the finitely many core clocks the same antiderivative gives
$\mathsf W_X'(r)=-k(r)\int_{B<r}s_B\,d\nu_X(B)\le0$.
Thus nonnegative weights still retain both continuous decrease and
source-dependent positive jumps; a theorem for decreasing weights
cannot be transferred by asserting only nonnegativity.
The existing interval lower counts and fixed-anchor negative
primitive do not provide that source-dependent comparison at the
required scale; no independent signed supplier is asserted here.
The common tail is controlled, while this finite arithmetic lower
bound, the original signed upper estimate and RH remain unproved.
FH1--FH4 are a project application and exact consumer of existing
complete-integral PNT, inverse-scale and finite partial-summation
inputs, without a new generic theorem, literature-priority claim,
Lean declaration or kernel verification.

## The original occupation pays all higher prime powers below its target scale

Retain FH1--FH4's original source, full windows, actual selector,
all endpoint ties and fixed $\Theta,\eta,d,\kappa,a$. Reuse the complete
square-root comparison in [Nicolas (GPP2)](../ArithSums/nicolas2025comparison.md#uniform-full-tail-comparison)
and its existing kernel moment (GPP4). Their analytic suppliers are
[Dusart arXiv:1002.0442v1](https://arxiv.org/pdf/1002.0442v1),
Lemma 3.3 and Theorem 5.2; their proofs and computations are not repeated.
The new consumer is the original compensated selector, including its
local subtraction, rather than GPP's mean-one dilation transport.
This is a `repo-derived` paper application of those inputs, not a new
prime-counting theorem, literature-priority claim or Lean verification.

### Keep the actual square atoms and the same compensation

Write

$$
\vartheta(u)=\sum_{p\le u}\log p,\qquad
P_{\ge2}(u)=\psi(u)-\vartheta(u)
=\sum_{\substack{k\ge2\\p^k\le u}}\log p,
\qquad E_\vartheta(u)=u-\vartheta(u).
$$

These functions keep every actual weak endpoint; the core selector
continues to come from the original full arithmetic envelope. Define
$G_a^\vartheta(B)$ by replacing $E$ with $E_\vartheta$ in HC3's
complete response, with the same $a$, and put

$$
\begin{aligned}
\mathsf H_{\ge2}(B)&=
 s_B\int_B^\infty P_{\ge2}(u)k(u)\,du
 -\frac{aP_{\ge2}(B)}{\sqrt B},\\
\mathcal J_X^\vartheta&=
 \int_{t_0}^{t_m}G_a^\vartheta(\mathcal B_X(t))\,dt.
\end{aligned}
$$

The exact split $E=E_\vartheta-P_{\ge2}$ gives

$$
G_a(B)=G_a^\vartheta(B)-\mathsf H_{\ge2}(B).
\tag{FP1}
$$

In particular the local prime-power term is subtracted inside
$\mathsf H_{\ge2}$; it is not counted a second time as extra reserve.
No prime label, core, residence length or compensating parameter changes.

### Reuse the uniform complete-tail comparison at every original clock

For $B>(3594641)^2$, GPP2 supplies, uniformly for $u\ge B$,

$$
|P_{\ge2}(u)-\sqrt u|\le\epsilon(B)\sqrt u,
\qquad
\epsilon(B)=\frac4{5\log^2B}+\frac{89}{50}B^{-1/6}.
$$

This is precisely GPP2 with its lower endpoint $s=B$; its auxiliary
$A$ may be set to $100B/99$. Use the already evaluated GPP4 moment

$$
2-\frac2{\log B}
\le s_B\int_B^\infty\sqrt u\,k(u)\,du<2.
$$

Positivity of $k$ and the same comparison at $u=B$ consequently give

$$
\boxed{
|\mathsf H_{\ge2}(B)-(2-a)|
\le\frac2{\log B}+(2+a)\epsilon(B).}
\tag{FP2}
$$

Let $b_X$ be the least core clock among the original active cores
and endpoint ties. The existing all-tie endpoint bound and N2 give
$b_X\to\infty$. The right side of FP2 decreases to zero uniformly
for $B\ge b_X$. Integrating it against the actual residence, of
mass exactly $L_X$, yields

$$
\boxed{
\left|\mathcal J_X-\mathcal J_X^\vartheta+(2-a)L_X\right|
\le\left[\frac2{\log b_X}+(2+a)\epsilon(b_X)\right]L_X
=o(L_X).}
\tag{FP3}
$$

Thus the complete higher-power response has the favorable sign
$-(2-a)L_X+o(L_X)$ in the original account. This assertion is uniform
on the original windows, including $\Theta=1$; it assumes no independent
sampling law, transverse phase speed or mean-one property of residence.
Because the original fixed $\eta<1/2$ gives $M_X\to\infty$,
this entire contribution is $o(M_XL_X)$. It cannot alone cancel the
positive original JM7 margin, which has order $M_XL_X$.

### The same finite test loses only a paid higher-power contribution

Use either common horizon already paid in FH1. Set
$\mathsf A_X=\int s_{\mathcal B_X(t)}dt\le e^{\mathsf Y_X/2}\mathsf Y_XL_X$.
The same GPP2--GPP4 bounds pay the complete higher-power tail by

$$
0\le\mathsf A_X\int_{\mathsf U_X}^\infty P_{\ge2}(u)k(u)\,du
\le 2(1+\epsilon(b_X))
\frac{\mathsf Y_X}{\log\mathsf U_X}
\exp\left[\frac{\mathsf Y_X-\log\mathsf U_X}{2}\right]L_X
=o(L_X).
$$

Here $\log\mathsf U_X/\mathsf Y_X\to\infty$ for either FH1 horizon.
No complete future interval is omitted without this bound.
FH1 together with this estimate also pays the common remote tail for
$E_\vartheta=E+P_{\ge2}$.

Retain exactly FH3's $\mathsf W_X$ and $\mathsf P_X$, and define

$$
\mathsf S_X^{(1)}=
\sum_{p\le\mathsf U_X}(\log p)\mathsf W_X(p),\qquad
\mathsf S_X^{(\ge2)}=
\sum_{\substack{k\ge2\\p^k\le\mathsf U_X}}
 (\log p)\mathsf W_X(p^k).
$$

Subtract FH3's finite identity from its identical $\vartheta$ version,
or exchange the same finite prime-power sum once, to get

$$
\boxed{
\begin{aligned}
\mathsf S_X^{(\ge2)}&=
 \int_{t_0}^{t_m}\mathsf H_{\ge2}(\mathcal B_X(t))dt
 -\mathsf A_X\int_{\mathsf U_X}^\infty P_{\ge2}(u)k(u)\,du\\
&=(2-a)L_X+o(L_X).
\end{aligned}}
\tag{FP4}
$$

Its weak cutoff convention includes $p^k=B$ and $p^k=\mathsf U_X$.
In particular it is nonnegative eventually, also directly from FH3's
nonnegative actual weights. All squares and every higher layer are
retained, including powers below the least core clock.

Accordingly FH4 is equivalent, with an arbitrarily small fixed loss
of its strict constant, to the still-unproved first-power test

$$
\boxed{
\mathsf S_X^{(1)}\ge\mathsf P_X-C_0M_XL_X,
\qquad C_0<d(1-\kappa)/16.}
\tag{FP5}
$$

For example FH4 with one fixed strict $C_0$ implies FP5 with any fixed
$C_1$ satisfying $C_0<C_1<d(1-\kappa)/16$, eventually on that same
cofinal sequence, because FP4 is $o(M_XL_X)$. Conversely FP5 implies
FH4 with the same constant eventually, by the higher-power sum's
nonnegativity. The analogous buffered equivalence for the complete
continuous accounts follows from FP3 and CQ5. None selects a favorable
sequence or establishes its required lower bound.

This pays a full arithmetic component of the original finite test,
rather than assigning it an assumed favorable sign. The outstanding
obligation is a quantitative lower bound for actual first-power primes
under the unchanged residence weights; their positive jumps remain.
No total-prime cancellation follows from a Fibonacci inclusion law or
from the geometric conservation of a different observable. The original
signed upper estimate, all-integer Robin inequality and RH remain unproved.

## The natural finite prime test is outside the convolution-square class

Use FH3's exact actual $\mathsf W_X$, including every retained local
subtraction, and either paid common horizon. The normalization below
reuses [Connes--Consani arXiv:2006.13771v1](https://arxiv.org/pdf/2006.13771v1),
Appendix A, equations (144)--(146), and Appendix B, equation (149).
The version agrees with the [existing source note](../Weil/connesconsani2021archimedean.md);
its Theorem 6.11, not the introduction's differing imaginary-sign
convention, is the adopted small-support comparison.
This `repo-derived` application identifies a test-class obstruction for
this particular actual finite weight. It is not a new Weil criterion,
an exclusion of all possible positivity approaches or a Lean proof.

### Match the prime-power functional in the unitary normalization

Extend the same FH3 formula to real $r\ge1$ and set it to zero for
$r>\mathsf U_X$. For $r\ge1$ define

$$
f_X(r)=\frac12\sqrt r\,\mathsf W_X(r),\qquad
f_X(r^{-1})=f_X(r).
\tag{WT1}
$$

This defines a real inversion-symmetric function supported in
$[\mathsf U_X^{-1},\mathsf U_X]$. The source's half-density change
of convention gives the unitary prime-local functional

$$
W_p(f)=(\log p)\sum_{k\ge1}p^{-k/2}
\bigl(f(p^k)+f(p^{-k})\bigr).
$$

Thus the complete arithmetic part matches exactly:

$$
\boxed{\sum_pW_p(f_X)=
\sum_{2\le n\le\mathsf U_X}\Lambda(n)\mathsf W_X(n).}
\tag{WT2}
$$

Here only finite prime-power evaluations are taken. The nonsmooth
$f_X$ is not declared admissible for the full archimedean distribution
or the source trace theorem. Matching the finite-prime evaluations
alone does not transport the pole or archimedean terms of an explicit
formula, nor identify the continuum reference $\mathsf P_X$ with them.

### Its original low-clock plateau violates a necessary positive-definite law

Let $b_X$ be the least original active core clock, and write

$$
\mathsf Z_X=\int_{t_0}^{t_m}\mathcal B_X(t)^{-1/2}dt,
\qquad
m_X=(1-a)\mathsf Z_X
-\frac{\mathsf A_X}{\mathsf U_X\log\mathsf U_X},
\qquad
\mathsf A_X=\int_{t_0}^{t_m}s_{\mathcal B_X(t)}dt.
$$

For $1\le r<b_X$, every indicator $r\le B$ equals one and every
$\max(B,r)$ equals $B$. The actual finite weight is therefore
$\mathsf W_X(r)=m_X$. Moreover,

$$
\frac{\mathsf A_X}{\mathsf U_X\log\mathsf U_X}
\le\frac{e^{\mathsf Y_X}\mathsf Y_X}
{\mathsf U_X\log\mathsf U_X}\mathsf Z_X
=o(\mathsf Z_X).
$$

Indeed $s_B=(B\log B)B^{-1/2}$ and $\log B\le\mathsf Y_X$.
Since the fixed $a<1$, $L_X>0$ and $\mathsf Z_X>0$, we have
$m_X>0$ eventually. Also the original $b_X\to\infty$ gives $b_X>2$.
Consequently

$$
\boxed{f_X(2)=\sqrt2\,f_X(1)>f_X(1)>0.}
\tag{WT3}
$$

Any positive-definite function on the multiplicative group satisfies
$|f(r)|\le f(1)$: the two-point Gram matrix for $1,r$ is positive
semidefinite. In particular a convolution square $g*g^*$, with
$g^*(r)=\overline{g(r^{-1})}$ and Haar measure $dr/r$, satisfies
this necessary law by Cauchy--Schwarz. Equation WT3 violates it.
Therefore the actual $f_X$ is not positive definite and cannot equal
such a convolution square, even before imposing smoothness or Mellin
vanishing. A smoothing preserving both its values at $1$ and $2$
still fails the same necessary law.

The adopted Connes--Consani Theorem 6.11 tests smooth $g*g^*$ with
$\operatorname{supp}g\subset[2^{-1/2},2^{1/2}]$ and
$\widehat g(-i/2)=0$, with the stated rank-one correction involving
$|\widehat g(0)|^2$. The actual finite test lacks that convolution-square
property and also has growing support. Nonnegative $\mathsf W_X$
and a positive trace in another test class therefore do not supply FH4.

This excludes direct substitution of WT1 into that theorem. A different
test, a positive-definite completion or a one-sided approximation is
not ruled out. Such a route still must pay its change in the actual
prime pairing and retain the full pole and archimedean contributions
at the original $M_XL_X$ scale. No such paid replacement is supplied
here; FP5, the original signed estimate and RH remain unproved.

## Core-scale smoothing preserves the reference and pays the actual prime change

Keep FH1--FH4, FP1--FP5 and WT1--WT3's original source, full windows,
actual residence, endpoint ties and fixed parameters. The smoothing
operation is ordinary convolution, as already used in the
[project's smooth-window construction](../Weil/frankliebseiringer2006hardy.md#a-smooth-realization-of-the-physical-windows).
No new convolution, bounded-variation or prime-distribution theorem is
asserted. This `repo-derived` paper application estimates its arithmetic
cost for the actual compensated weights and preserves their continuum
reference. It supplies no signed lower bound or Lean verification.

### Smooth each kernel while keeping the original residence

Use either FH1 common horizon, so eventually $16<B<\mathsf U_X$
for every original active clock. Let $b_X$ be the same all-tie least
clock as FP2, and define one common auxiliary scale

$$
Q_X=\min\left\{\sqrt{M_X/\mathsf Y_X},\ b_X^{1/4}\right\}.
$$

With VC2's stated polylogarithmic $\mathsf Y_X$, both entries tend
to infinity, while $Q_X\mathsf Y_X/M_X\to0$ and
$Q_X/\sqrt{b_X}\le b_X^{-1/4}\to0$. These are consequences of
the unchanged source and $\eta<1/2$, not new residence premises. Extend each FH3 single-core weight
onto the whole real line by

$$
w_B(r)=
\begin{cases}
 s_B\left[\dfrac1{\max(B,r)\log\max(B,r)}
 -\dfrac1{\mathsf U_X\log\mathsf U_X}\right]
 -\dfrac a{\sqrt B}\mathbf1_{\{r\le B\}},&r\le\mathsf U_X,\\
 0,&r>\mathsf U_X.
\end{cases}
$$

For negative $r$ the maximum is still the positive $B$. This weight
is constant to the left of $B$, is nonnegative eventually by FH3,
and vanishes continuously at $\mathsf U_X$. Its value at $B$ retains
the original weak endpoint. Its total-variation measure is exactly

$$
d|Dw_B|(v)=\frac a{\sqrt B}\,\boldsymbol\delta_B(dv)
+s_B\mathbf1_{(B,\mathsf U_X)}(v)k(v)\,dv.
\tag{MR1}
$$

Here the first term is the original positive right jump; the second
is the absolute value of the original continuous decrease.
There is no new endpoint atom at the common horizon.

Choose one fixed nonnegative even $\rho\in C_c^\infty(-1,1)$
with $\int\rho(z)dz=1$. Set $h_B=Q_X\sqrt B$ and

$$
\widetilde w_B(r)=\int_{-1}^1\rho(z)w_B(r-h_Bz)\,dz,
\qquad
\widetilde{\mathsf W}_X(r)=
\int_{t_0}^{t_m}\widetilde w_{\mathcal B_X(t)}(r)\,dt.
$$

The actual selector has finitely many cores, so the latter integral
is a finite residence-weighted sum of smooth functions. It is smooth,
nonnegative, and zero for
$r>\mathsf V_X:=\mathsf U_X+Q_X\sqrt{B^{\rm end}_{\max,X}}$.
Here $B^{\rm end}_{\max,X}$ is CP1/VC2's existing maximum over
all endpoint ties; N2 puts every intervening core below it. The
outgoing-label-only $B_{\max,X}$ is not used for this support.
Residence is not convolved or replaced by a new sampling law.
The finite sums below include all new evaluations between
$\mathsf U_X$ and $\mathsf V_X$.

### The continuum reference is preserved exactly

Let

$$
c_B=\frac{1-a}{\sqrt B}
-\frac{s_B}{\mathsf U_X\log\mathsf U_X}
$$

be the original constant plateau. Since $h_B<B$ and
$w_B(r)=c_B$ throughout $[-h_B,h_B]$, every $|q|\le h_B$
satisfies

$$
\int_0^\infty w_B(r-q)dr
=\int_0^\infty w_B(r)dr+q c_B.
$$

These integrals are finite on the half-line. The even mollifier has
zero first moment, so convolution and finite integration give

$$
\boxed{
\int_0^\infty\widetilde{\mathsf W}_X(r)dr
=\int_0^\infty\mathsf W_X(r)dr=\mathsf P_X.}
\tag{MR2}
$$

The last equality is the same finite Fubini account as FH3, with
its full low-clock plateau. No continuum baseline is fitted after
smoothing, and no prime below the least clock is dropped.

### Charge the discrete arithmetic change to the original variation

For $|q|\le h_B$, the variation measure in MR1 controls every
$|w_B(n-q)-w_B(n)|$ by its mass on the closed interval between
$n-q$ and $n$. Closed endpoints cover the retained weak value at $B$.
A fixed $v$ is charged by at most $2h_B+1$ integers with
$|n-v|\le h_B$, and all such $n\ge2$ have
$\log n\le\log(v+h_B)$. Thus the elementary
$0\le\Lambda(n)\le\log n$ gives

$$
\sum_{n\ge2}\Lambda(n)|w_B(n-q)-w_B(n)|
\le(2h_B+1)\int_B^{\mathsf U_X}
\log(v+h_B)\,d|Dw_B|(v).
$$

The integral includes the atom at $B$. The common start has $Q_X\ge1$ and $Q_X/\sqrt{b_X}<1/2$.
For every $B\ge b_X$, $v\ge B$ therefore gives $h_B\le v/2$, $\log(v+h_B)\le2\log v$ and
$(1+\log v)/\log v\le2$. Applying these directly to MR1 yields

$$
\begin{aligned}
\int_B^{\mathsf U_X}\log(v+h_B)d|Dw_B|(v)
&\le\frac{2a\log B}{\sqrt B}
 +4s_B\int_B^{\mathsf U_X}\frac{dv}{v^2}\\
&\le(2a+4)\frac{\log B}{\sqrt B}.
\end{aligned}
$$

As $2h_B+1\le3Q_X\sqrt B$ and the original $a<1$, every shift,
and then its nonnegative mollifier average, consequently has cost

$$
\sum_{n\ge2}\Lambda(n)
|\widetilde w_B(n)-w_B(n)|\le18Q_X\log B.
$$

Integrating against the actual residence, using
$\log B\le\mathsf Y_X$, proves the paid arithmetic comparison

$$
\boxed{
\begin{aligned}
\sum_{n\ge2}\Lambda(n)
|\widetilde{\mathsf W}_X(n)-\mathsf W_X(n)|
&\le18Q_X\mathsf Y_X L_X=o(M_XL_X),\\
\sum_p(\log p)
|\widetilde{\mathsf W}_X(p)-\mathsf W_X(p)|
&\le18Q_X\mathsf Y_X L_X=o(M_XL_X).
\end{aligned}}
\tag{MR3}
$$

All sums are finite. The second inequality restricts the same
nonnegative sum to first-power primes; it does not compare
independent extrema. For the little-$o$ statement choose VC2's
$\mathsf Y_X=K(\log X)^{5/3}(\log\log X)^{1/3}$,
which includes $\Theta=1$. The original fixed $\eta<1/2$ gives
$\mathsf Y_X/M_X\to0$. Neither a short-interval PNT, a new
prime-counting start nor RH is used in this arithmetic cost.

Combining MR2--MR3, FP5 is equivalent, with an arbitrarily small
fixed loss of its strict constant on the same cofinal original
windows, to

$$
\sum_{p\le\mathsf V_X}(\log p)\widetilde{\mathsf W}_X(p)
\ge\mathsf P_X-C_0M_XL_X,
\qquad C_0<d(1-\kappa)/16.
\tag{MR4}
$$

MR4 is unproved. The smoothing radii exceed $\sqrt B$ by the common growing factor
$Q_X$, while staying $o(B)$ uniformly. Their larger width is paid
by MR3, without a bandlimit or Fourier-cancellation assertion.
Smoothness does not imply a decreasing weight,
a favorable prime sign, fixed testing complexity or control of its
zero-frequency baseline. The difference estimate, rather than
unpaid endpoint deletion, pays the changed prime evaluations.

### A prime-free calibration gives a smooth compact multiplicative test

The original plateau also persists after smoothing:
$\widetilde{\mathsf W}_X(r)=m_X$ for
$r\le b_X-Q_X\sqrt{b_X}$, with the same positive $m_X$ as WT3.
At this fixed window, $B-Q_X\sqrt B$ increases for $B\ge b_X$,
since its derivative is $1-Q_X/(2\sqrt B)>0$. The plateau endpoint
tends to infinity because $Q_X/\sqrt{b_X}\to0$, so it eventually
contains $[1,2]$.

Take a fixed smooth even $0\le\chi\le1$, equal to one near zero
and supported in $|x|<(\log2)/2$. Define

$$
F_X(x)=\frac12(1-\chi(x))e^{|x|/2}
\widetilde{\mathsf W}_X(e^{|x|})
+\frac12\chi(x)m_X\cosh(x/2),
\qquad \widetilde f_X(e^x)=F_X(x).
\tag{MR5}
$$

The cutoff removes the cusp at $x=0$; away from zero the convolved
weight is smooth. Hence $\widetilde f_X$ is real,
inversion-symmetric and in $C_c^\infty(\mathbb R_+^*)$, with
support inside $[\mathsf V_X^{-1},\mathsf V_X]$.
No prime-power argument $|x|=k\log p\ge\log2$ lies in the
calibration support. The finite arithmetic part therefore remains
exactly

$$
\sum_pW_p(\widetilde f_X)=
\sum_{n\ge2}\Lambda(n)\widetilde{\mathsf W}_X(n)
$$

in WT2's adopted unitary normalization. The calibration changes no
prime evaluation; MR3 has already paid the convolution change.
The resulting test is a smooth compact input for the cited full
explicit-formula convention, with all pole and archimedean terms
still required. They are not identified with $\mathsf P_X$ by this
construction, and no Mellin vanishing condition is imposed.

WT3's previously established obstruction still applies, since
$\widetilde f_X(1)=m_X/2$ and
$\widetilde f_X(2)=\sqrt2m_X/2$. Thus admissible regularity does
not put this test into the convolution-square positivity class.
The paid comparison opens a smooth-testing interface for the same
arithmetic problem; the actual weighted first-prime lower bound,
original signed upper estimate and RH remain unproved.

## The paid smoothing retains the original fixed Mellin readout

Keep MR1--MR5's actual kernels, common horizon, auxiliary factor,
residence and endpoint ties. The following `repo-derived` paper
application uses the [existing complete coefficient NH1](../ArithSums/nicolas2025comparison.md#absolute-full-weight-cost-at-a-fixed-negative-heat-time),
ordinary Taylor's formula and MR1's exact variation. It introduces
no new Mellin-transform or approximation theorem. Its consumer is
the original compensated kernel after the paid arithmetic smoothing;
it does not supply the signed first-prime bound or Lean verification.

Fix $s=\sigma+i\gamma$ with $0<\sigma<1$ before taking $X\to\infty$.
For each actual core define the one-sided coefficients

$$
H_B(s)=\int_0^\infty w_B(r)r^{s-1}\,dr,
\qquad
\widetilde H_B(s)=\int_0^\infty\widetilde w_B(r)r^{s-1}\,dr.
$$

Positive real powers use the real logarithm. These integrals are
finite: the weight is bounded near zero and has finite upper support.
They concern the arithmetic kernels, rather than the Fourier transform
of MR5's calibrated symmetric multiplicative test.

### The zero first moment pays a second-order coefficient change

Let $Dw_B$ be the signed distributional derivative from MR1, so

$$
Dw_B=\frac a{\sqrt B}\boldsymbol\delta_B
-s_B\mathbf1_{(B,\mathsf U_X)}k(v)\,dv.
$$

The retained weak value at $B$ is represented by
$w_B(r)=-\int\mathbf1_{\{r\le v\}}Dw_B(v)$.
Since $h_B<B/2$, every $v$ in this finite variation support has
$v+h_Bz>0$. Finite Fubini consequently gives the exact difference

$$
\widetilde H_B(s)-H_B(s)
=-\frac1s\int_B^{\mathsf U_X}
\left[\int_{-1}^1\rho(z)(v+h_Bz)^s\,dz-v^s\right]Dw_B(v).
\tag{MF1}
$$

The integral includes the original atom at $B$. Put
$\mu_2=\int z^2\rho(z)dz\le1$. The even mollifier's zero first
moment removes the linear Taylor term. For $|h_Bz|\le v/2$,
$|(t^s)''|=|s(s-1)|t^{\sigma-2}$ supplies

$$
\frac1{|s|}
\left|\int\rho(z)(v+h_Bz)^s dz-v^s\right|
\le2^{1-\sigma}|s-1|\mu_2h_B^2v^{\sigma-2}.
$$

MR1 and $\log B>1$ also give

$$
\begin{aligned}
\int_B^{\mathsf U_X}v^{\sigma-2}d|Dw_B|(v)
&\le aB^{\sigma-5/2}
 +2\sqrt B\int_B^\infty v^{\sigma-4}dv\\
&=\left(a+\frac2{3-\sigma}\right)B^{\sigma-5/2}.
\end{aligned}
$$

Here $\log B(1+\log v)/\log^2v\le2$ for $v\ge B$;
no prime-error bound or free residence law is used. Thus

$$
\boxed{
|\widetilde H_B(s)-H_B(s)|
\le C_{s,a,\rho}Q_X^2B^{\sigma-3/2},
\qquad
C_{s,a,\rho}=2^{1-\sigma}|s-1|\mu_2
\left(a+\frac2{3-\sigma}\right).}
\tag{MF2}
$$

The normalized coefficient change is at most
$C_{s,a,\rho}Q_X^2/B\le C_{s,a,\rho}b_X^{-1/2}\to0$,
uniformly over every original core and tie. This is a fixed-$s$
comparison, not a uniform estimate over an infinite zero family.

### Retain the complete coefficient and the finite horizon correction

Use NH1 with its lower endpoint equal to the core clock $B$ or
the common horizon $\mathsf U_X$:

$$
F_A(s)=\frac{A^{s-1}}{s\log A}
+\int_A^\infty\frac{r^{s-2}}{\log r}\,dr
=\frac{A^{s-1}}{s\log A}+E_1((1-s)\log A).
$$

The original finite cutoff and compensation give the exact application

$$
H_B(s)=s_B\bigl(F_B(s)-F_{\mathsf U_X}(s)\bigr)
-\frac a{s}B^{s-1/2}.
\tag{MF3}
$$

This reuses the complete NH1 coefficient; neither its plateau nor its
tail is omitted. Set

$$
K_a(s)=\frac1{s(1-s)}-\frac a{s}
=\frac{1-a+as}{s(1-s)},\qquad
\mathsf R_X^{\rm hor}=\frac{\mathsf U_X}{B^{\rm end}_{\max,X}}\longrightarrow\infty.
$$

For clarity, the quantitative remainder uses only the positive-half-line
NH1 integral. After $r=Bv$, the factor
$\log B/(\log B+\log v)$ differs from one by at most
$\log v/\log B$. The elementary integrals of
$v^{\sigma-2}$ and $v^{\sigma-2}\log v$ on $[1,\infty)$ therefore give,
for every original core,

$$
\left|B^{1/2-s}H_B(s)-K_a(s)\right|
\le\frac1{(1-\sigma)^2\log b_X}
+\left(\frac1{1-\sigma}+\frac1{|s|}\right)(\mathsf R_X^{\rm hor})^{\sigma-1}.
$$

The second term retains both the missing complete tail beyond
$\mathsf U_X$ and its finite constant cutoff. Combining with MF2,
put

$$
\epsilon_X(s)=\frac1{(1-\sigma)^2\log b_X}
+\left(\frac1{1-\sigma}+\frac1{|s|}\right)(\mathsf R_X^{\rm hor})^{\sigma-1}
+C_{s,a,\rho}\frac{Q_X^2}{b_X}\longrightarrow0.
$$

Then the same actual residence satisfies

$$
\boxed{
\left|\int_{t_0}^{t_m}\widetilde H_{\mathcal B_X(t)}(s)dt
-K_a(s)\int_{t_0}^{t_m}\mathcal B_X(t)^{s-1/2}dt\right|
\le\epsilon_X(s)\int_{t_0}^{t_m}\mathcal B_X(t)^{\sigma-1/2}dt.}
\tag{MF4}
$$

Since $a<1$, the numerator of $K_a(s)$ has positive real part
$1-a+a\sigma$; hence $K_a(s)\ne0$ throughout this fixed strip.
The paid smoothing preserves each core's nonzero leading coefficient
and leaves the original occupation's fixed Mellin readout in MF4.
It does not make that readout small or determine its phase.

The MF4 error is relative to the displayed occupation magnitude.
That magnitude has not been bounded by $M_XL_X$, so MF4 is not an
additional target-scale payment. No interchange with an infinite zero
sum, zero-frequency cancellation, full pole/archimedean identification
or bound uniform in growing $|\gamma|$ is asserted. MR3 pays the
arithmetic change; suppression of high frequencies alone does not
establish MR4. The actual original signed lower bound and RH remain
unproved.

## The smooth arithmetic test pays a common spectral tail and its full reference correction

Keep FH1--FH4, FP1--FP5, MR1--MR5 and MF1--MF4's original full
windows, actual selector residence, endpoint ties and fixed parameters.
The generic inputs are the existing full zero-count moments used in
SR1 and [the complete reciprocal-square tail](../ArithSums/nicolas2025comparison.md#pay-the-discrepancy-over-all-actual-zeros),
and [Connes--Consani arXiv:2006.13771v1](https://arxiv.org/pdf/2006.13771v1),
Appendix B, equations (147)--(150), in WT2's adopted normalization.
The source's linear explicit formula is used, with no convolution-square
positivity or Mellin-vanishing hypothesis. No new zero-count, explicit-
formula or transform-decay theorem is asserted. This `repo-derived`
paper application pays those inputs for the actual smoothed arithmetic
kernel, including its full pole and archimedean reference difference.
It supplies no signed head bound or Lean verification.

For this section put

$$
C=B^{\rm end}_{\max,X},\quad b=b_X,\quad U=\mathsf U_X,
\quad Q=Q_X,\quad Y=\mathsf Y_X,\quad L=L_X,
\qquad
\mathsf H_X^{\rm hor}=1+\log\frac{\log U}{\log b}.
$$

Every original residence core belongs to $[b,C]$. Use one common start
with $b>e^4$, $h_B=Q\sqrt B<B/2$ and the MR5 plateau containing $[1,2]$.
Define the one-sided actual coefficient

$$
\mathfrak M_X(s)=\int_0^\infty
\widetilde{\mathsf W}_X(r)r^{s-1}\,dr
=\int_{t_0}^{t_m}\widetilde H_{\mathcal B_X(t)}(s)\,dt,
\qquad \Re s>0.
$$

Finite Fubini gives the second equality. Constancy near zero and finite
upper support make these integrals finite. The notation is distinct
from the Mellin transform of the compact symmetric multiplicative test.

### Keep the remote derivative endpoint in the actual two-derivative budget

Write $\rho_h(x)=h^{-1}\rho(x/h)$. Differentiating MR1's signed
variation once more after convolution gives exactly

$$
\begin{aligned}
\widetilde w_B''(r)
={}&\frac a{\sqrt B}\rho_{h_B}'(r-B)
-s_Bk(B)\rho_{h_B}(r-B)\\
&+s_Bk(U)\rho_{h_B}(r-U)
-s_B\int_B^U k'(v)\rho_{h_B}(r-v)\,dv.
\end{aligned}
\tag{MT1}
$$

Although $Dw_B$ has no atom at $U$, the endpoint of its density
contributes to this second derivative. The same $h_B$ appears at $B$,
at $U$ and inside the $v$-integral; replacing it by $h_v$ would change
MR1--MR3's actual kernel.

For $v\ge B$, the convolution support has $r\le v+h_B\le3v/2$.
Thus the four terms in MT1 have weighted absolute integrals
$\int_0^\infty r^2|\cdot|dr$ bounded respectively by

$$
\frac{9a}{4}\|\rho'\|_1\frac BQ,
\qquad \frac92\sqrt B,
\qquad \frac92\sqrt B,
\qquad \frac94s_B\int_B^U v^2|k'(v)|\,dv.
$$

Direct differentiation of the original $k$ gives

$$
-k'(v)=\frac1{v^3}
\left(\frac2{\log v}+\frac3{\log^2v}+\frac2{\log^3v}\right),
$$

so its retained integral is at most
$2\log(\log U/\log B)+4/\log B$. Integrating these inequalities
against the same actual residence proves, with a fixed finite constant,

$$
\boxed{
\mathsf D_{2,X}:=\int_0^\infty
r^2|\widetilde{\mathsf W}_X''(r)|dr
\le C_{\rho,a}L
\left[\frac C Q+\sqrt C\,Y\,\mathsf H_X^{\rm hor}\right].}
\tag{MT2}
$$

In particular the budget is logarithmic in $\log U$, rather than
proportional to the remote support length $U$.

### A common cutoff pays the complete absolute zero tail

The ordinary integration-by-parts decay mechanism is the same one
used by the [existing closed-strip two-jet estimate](../../D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay.lean).
Here it is applied to the displayed one-sided arithmetic coefficient.
For $s=\sigma+i\gamma$, $0<\sigma<1$, twice integrating by parts gives

$$
\mathfrak M_X(s)=\frac1{s(s+1)}
\int_0^\infty\widetilde{\mathsf W}_X''(r)r^{s+1}\,dr.
$$

The first boundary term vanishes at zero because $\sigma>0$;
the derivative itself is zero near zero. Both upper boundary terms
vanish by smooth compact upper support. All derivative support lies
above $b/2>1$, so $r^{\sigma+1}\le r^2$ there. For every actual zero
$\varrho=\beta+i\gamma$ with $|\gamma|>T\ge4$, MT2 and the existing
multiplicity-weighted count consequently give

$$
\boxed{
\sum_{|\gamma|>T}m_\varrho|\mathfrak M_X(\varrho)|
\le C_{\rho,a}\frac{L\log(eT)}T
\left[\frac C Q+\sqrt C\,Y\,\mathsf H_X^{\rm hor}\right].}
\tag{MT3}
$$

The reused count is $N(T)\ll T\log(eT)$ and its complete consequence
$\sum_{|\gamma|>T}m_\varrho/\gamma^2\ll\log(eT)/T$.
Every actual multiplicity and both ordinate signs are retained. The
finite zero set below the stated start remains in the head.

Take the common, endpoint-inclusive cutoff

$$
\mathsf T_X=\frac C{Q^2}.
$$

Since $Q^2\le\sqrt b\le\sqrt C$, it has
$\mathsf T_X\ge\sqrt C\to\infty$ and $\log\mathsf T_X\le Y$.
Substitution in MT3 therefore proves

$$
\boxed{
\sum_{|\gamma|>\mathsf T_X}m_\varrho
|\mathfrak M_X(\varrho)|
\le C_{\rho,a}L
\left[QY+Y^2\mathsf H_X^{\rm hor}\right]
=o(M_XL_X).}
\tag{MT4}
$$

The first term is paid by MR3's $QY/M_X\to0$. Either FH1 common
horizon has $\log U=O((\log X)^4)$, hence
$\mathsf H_X^{\rm hor}=O(\log\log X)$. VC2's unchanged ceiling gives

$$
\frac{Y^2\mathsf H_X^{\rm hor}}{M_X}
\ll X^{-(1/2-\eta)}
(\log X)^{7/3}(\log\log X)^{5/3}\longrightarrow0.
$$

This covers $\Theta=1$ without DH1, a zero-density restriction or
separation of $\mathsf T_X$ from zero ordinates. The cutoff splits an
absolutely convergent zero sum; it is not a newly admissible CHJ height.
It is not asserted shorter than earlier conditional masked-head cuts.

### Use the full smooth explicit formula, retaining its reference difference

Use exactly MR5's $\widetilde f_X$ and set

$$
g_X(r)=r^{-1/2}\widetilde f_X(r),\qquad
G_X(s)=\int_0^\infty g_X(r)r^{s-1}dr,
\qquad g_X^\sharp(r)=r^{-1}g_X(r^{-1})=g_X(r).
$$

This is a compact smooth multiplicative test. The prime-free calibration
leaves $g_X(p^k)=\widetilde{\mathsf W}_X(p^k)/2$ and its sharp value
the same. The cited Appendix B formula thus applies directly as

$$
\sum_{n\ge2}\Lambda(n)\widetilde{\mathsf W}_X(n)
=\mathsf P_X^{\rm Weil}
-\sum_\varrho m_\varrho G_X(\varrho)
-\mathcal W_{\mathbb R}(g_X),
\qquad
\mathsf P_X^{\rm Weil}=G_X(0)+G_X(1).
\tag{MT5}
$$

The zero sum is over all actual nontrivial zeros. No positivity theorem
is substituted for this linear identity. Write $m=m_X$ and, on $r\ge1$,

$$
c_\chi(r)=\frac14\chi(\log r)(r^{-1}-1),\qquad
 g_X(r)=\frac12\widetilde{\mathsf W}_X(r)+m c_\chi(r).
$$

The equality uses the actual plateau on the calibration interval. The
sharp symmetry and MR2 give the exact pole reference

$$
\mathsf P_X^{\rm Weil}
=\mathsf P_X-m
+\int_1^\infty\frac{\widetilde{\mathsf W}_X(r)}rdr
+2m\int_1^{\sqrt2}c_\chi(r)(1+r^{-1})dr.
$$

Its difference from $\mathsf P_X$ is controlled as follows. The original
nonnegative weight is at most $B^{-1/2}$ everywhere. For $r\ge2B$,
$r-h_B\ge3r/4$ gives
$\widetilde w_B(r)\le(8/3)s_B/(r\log r)$. Consequently

$$
0\le m\le\frac L{\sqrt b},\qquad
\int_1^\infty\frac{\widetilde w_B(r)}rdr
\le\frac{\log(2B)+4/3}{\sqrt B},
\qquad
\int_1^\infty\frac{\widetilde{\mathsf W}_X(r)}rdr
\ll L\frac{\log b}{\sqrt b}.
$$

The last step uses monotonic decrease of
$(\log(2B)+4/3)/\sqrt B$ for $B\ge b>e^4$; the arithmetic weight
itself is not declared decreasing. Thus
$|\mathsf P_X^{\rm Weil}-\mathsf P_X|\ll_\chi L\log b/\sqrt b$.

Keep the source's entire archimedean distribution, including its
subtraction beyond the test's support:

$$
\mathcal W_{\mathbb R}(g_X)
=(\log4\pi+\gamma_E)g_X(1)
+\int_1^\infty
\frac{2g_X(r)-m/r}{r-r^{-1}}dr.
$$

On $[1,\sqrt2]$ the actual plateau makes the integrand exactly
$m(1-\chi(\log r)/2)/(r+1)$, removing the apparent singularity.
Above $\sqrt2$ its absolute value is at most
$2\widetilde{\mathsf W}_X(r)/r+2m/r^2$. The latter term also pays
its full range beyond the support. Hence
$|\mathcal W_{\mathbb R}(g_X)|\ll_\chi L\log b/\sqrt b$.

For $0<\Re s<1$, the exact passage to the one-sided coefficient is

$$
G_X(s)=\frac{\mathfrak M_X(s)+\mathfrak M_X(1-s)}2
+m r_\chi(s),
$$

where

$$
r_\chi(s)=\int_1^{\sqrt2}c_\chi(r)
(r^{s-1}+r^{-s})dr
-\frac12\left(\frac1s+\frac1{1-s}\right).
$$

Both endpoint values of $c_\chi$ vanish. Two integrations by parts
on this fixed interval bound its Mellin integral by
$O_\chi(|\gamma|^{-2})$ uniformly for $0\le\Re s\le1$ and
$|\gamma|\ge1$. The rational pair is kept together as
$1/[s(1-s)]$, with the same decay. The existing reciprocal-square
zero count therefore gives an absolutely convergent calibration sum;
its finite low-zero part is retained.

MT2--MT3 give absolute convergence for the one-sided zero sums, allowing
$\varrho\mapsto1-\varrho$ in the preceding identity. MT5 now yields

$$
\boxed{
\mathsf P_X-\sum_{n\ge2}\Lambda(n)\widetilde{\mathsf W}_X(n)
=\sum_\varrho m_\varrho\mathfrak M_X(\varrho)
+\mathsf E_X^{\rm Weil},}
\tag{MT6}
$$

with the exact retained correction

$$
\mathsf E_X^{\rm Weil}
=\mathsf P_X-\mathsf P_X^{\rm Weil}
+\mathcal W_{\mathbb R}(g_X)
+m_X\sum_\varrho m_\varrho r_\chi(\varrho),
\qquad
|\mathsf E_X^{\rm Weil}|\ll_\chi L\frac{\log b}{\sqrt b}=o(L_X).
$$

The poles are not defined equal to the continuum reference. The full
pole, archimedean and calibration discrepancy is instead explicitly
constructed and paid for this particular source.

### The unchanged first-prime deficit leaves one signed right-half head

Define

$$
\begin{aligned}
D_X^{(1)}&=\mathsf P_X-
 \sum_p(\log p)\mathsf W_X(p),\\
Z_X^{\rm right}(\mathsf T_X)
&=2\Re\sum_{\substack{0<\gamma\le\mathsf T_X\\\beta>1/2}}
m_\varrho\int_{t_0}^{t_m}
\widetilde H_{\mathcal B_X(t)}(\varrho)dt.
\end{aligned}
$$

The original unsmoothed weights remain in $D_X^{(1)}$; MR3 pays their
transport into the displayed smooth head. The same MF1 step-kernel
representation gives, for $0<\beta\le1/2$,

$$
\begin{aligned}
|\widetilde H_B(\varrho)|
&\le\frac{2^{\beta}}{|\varrho|}
\left[\frac a{\sqrt B}B^\beta
+s_B\int_B^U v^\beta k(v)dv\right]\\
&\le\frac{\sqrt2(a+4)}{|\varrho|}B^{\beta-1/2}
\le\frac{\sqrt2(a+4)}{|\varrho|}.
\end{aligned}
$$

Applying the already used SR1 zero-count moment to the same submultiset
pays that lower-half head by
$O_a(L(1+\log^2\mathsf T_X))=O_a(LY^2)=o(M_XL_X)$.
Conjugate pairing, MT4 and MT6 then retain precisely the right-half
head above. FP4 contributes the same positive higher-prime-power debit
$(2-a)L_X+o(L_X)$ when returning to first-power primes; it is charged
once, not reused as a second reserve. Combining these paid accounts
with MR3 gives

$$
\boxed{
|D_X^{(1)}-Z_X^{\rm right}(\mathsf T_X)|
\le C_{\rho,\chi,a}L
\left[QY+Y^2\mathsf H_X^{\rm hor}+1+
\frac{\log b}{\sqrt b}\right]+o(L_X)
=o(M_XL_X).}
\tag{MT7}
$$

All cores, phases and multiplicities in the head belong to the same
original residence. Uniformity includes every original tie and
$\Theta=1$. FP5's strict upper budget therefore transfers, with an
arbitrarily small fixed margin loss on the same cofinal full windows,
to the single requirement

$$
\boxed{
Z_X^{\rm right}(\mathsf T_X)\le C_1M_XL_X,
\qquad C_1<d(1-\kappa)/16.}
\tag{MT8}
$$

MT8 is unproved. The tail and reference payments do not supply a
favorable cofinal sequence or a sign for this growing head. Every fixed
actual zero eventually belongs to the common cutoff. MF2's already
established fixed-frequency comparison is reused; smoothness and
high-frequency suppression do not pay the original residence's
remaining phase relation. No independent sampling law, positive-
definite completion, infinite-family cancellation or RH conclusion
is inferred. The original first-prime bound, full signed upper estimate,
all-integer Robin inequality and RH remain unproved.


## The joint height account forces complete-response occupation at the total clock

Keep JM1--JM7's original RH-failure source, its fixed
$1-\Theta<\eta<1/2$, $d>0$, $0<\kappa<1$ and
$0<a<5\kappa/8$. Retain every original full window, prime label,
maximizing tie and outgoing weight. The complete response remains

$$
G_a(x)=s_x\int_x^\infty E(v)k(v)dv-\frac{aE(x)}{\sqrt x},
\qquad s_x=\sqrt x\log x,\quad E=x-\psi,
\quad k(x)=\frac{1+\log x}{x^2\log^2x}.
$$

The improper integral and all prime powers are retained. The generic
inputs are the already used finite centered-tail account, positive
weight estimates, bounded-variation quadrature and AM--GM inequality.
The new consumer is the same source's response at its total clock
$A=B+t$, followed by its unweighted real-center occupation. This
`repo-derived` paper application gives no upper estimate for the
original signed head, no new prime theorem and no Lean verification.

### Keep the local cancellation before bounding the past part

At an original label, PG1 gives $K(A)=B$. Put

$$
q=\frac{s_B}{s_A},\qquad
c=\frac{B\log B}{A\log A},\qquad
\mathsf H(x)=s_x\int_x^\infty E(v)k(v)dv.
$$

For sufficiently large source clocks, $0<q,c\le1$. Splitting the
same convergent integral, equivalently using the retained centered-tail
account, gives exactly

$$
\begin{aligned}
qG_a(A)
&=\mathsf H(B)-s_B\int_B^A E(v)k(v)dv
  -\frac{acE(A)}{\sqrt B},\\
E(A)&=t+Q(A),\qquad Q=K-\psi.
\end{aligned}
\tag{AO1}
$$

Thus the local $E(B)$ contribution cancels before its capacity is
estimated. No assumption about the size of the complete signed
difference $G_a(B)-G_a(A)$ is made. CR19's unabridged height and
removal gain supply

$$
\mathsf H(B)\ge
\frac d2\sqrt B\log B\,X^{-\eta}
+\chi_{p,u}\frac t{\sqrt B},\qquad
\chi_{p,u}\longrightarrow1
$$

uniformly in the original labels and ties. Both positive reserves
belong to that single original account.

Fix one capacity coefficient $C>8/5$. CR43--CR44 give, after one
common start,

$$
D_B:=B-K(B)=K(A)-K(B)\le Ct+H_C\sqrt B,
\qquad |Q(v)|\le H_Q\sqrt v.
$$

For every $v\in[B,A]$, monotonicity of the complete strict inventory
gives $K(v)\ge K(B)$. CR17 permits $A\le2B$. Consequently

$$
E(v)=v-K(v)+Q(v)
\le(C+1)t+(H_C+\sqrt2H_Q)\sqrt B.
$$

The original $k$ is positive and decreasing, and
$s_Bk(B)\le2B^{-3/2}$. Therefore a fixed constant $C_*$ supplies
the one-sided bound

$$
s_B\int_B^A E(v)k(v)dv
\le C_*\frac tB\frac t{\sqrt B}+C_*\frac tB.
\tag{AO2}
$$

Its direction is sufficient in AO1. The uniform $t/B\to0$ is
consumed on this retained past contribution, without converting
$o(V_X^{\rm lag})$ into $o(M_XL_X)$. Also
$acQ(A)/\sqrt B\le a\sqrt2H_Q$. Combining AO1--AO2, for every
fixed positive $\epsilon<1-a$, one common start gives

$$
qG_a(A)\ge
\frac d2\sqrt B\log B\,X^{-\eta}
+(1-a-\epsilon)\frac t{\sqrt B}-C_a.
\tag{AO3}
$$

All original choices are covered, including $\Theta=1$. The
normalization has been retained with its sign: the right side is
eventually positive uniformly, so $q\le1$ then permits
$G_a(A)\ge qG_a(A)$. No signed upper bound is divided by an
unpaid normalization factor.

### The same coercive calculation gives a total-clock margin

Set $M_X=X^{1/2-\eta}\log X$, $z=B/X$ and
$\ell_X=(d/8)X^{1-\eta}\log X$. Since every original
$t\ge\ell_X$, AO3 yields

$$
\frac{qG_a(A)}{M_X}\ge
\frac d2\sqrt z\frac{\log B}{\log X}
+\frac d8\frac{1-a-\epsilon}{\sqrt z}
-\frac{C_a}{M_X}.
$$

CR17 and the original floor give
$\log B/\log X\ge(1-\eta)/2$ beyond one common start.
The two positive terms exclude both $z\to0$ and $z\to\infty$
from any sequence of bounded normalized responses. On the remaining
fixed compact interval, $\log B/\log X\to1$ uniformly. Apply
JM2--JM3's already used AM--GM calculation there, first fixing
$\epsilon$ and then letting its fixed requested loss decrease.
This proves the same-source total-clock conclusion

$$
\boxed{
R_A:=\frac d2\sqrt{1-a},\qquad
\forall\delta>0\quad
G_a(A_i)\ge(R_A-\delta)M_X
\quad\text{for every original label and tie eventually}.}
\tag{AO4}
$$

It is a lower bound at $A_i$, with the full future integral and
original compensation. It does not assert an $o(M_XL_X)$
recentring difference or extend SI1's short-interval asymptotic.
The equality of $R_A$ with JM7's scalar margin when
$\eta<13/30$ does not identify their observations: AO4 concerns
$G_a(A_i)$ and holds for the entire original range $\eta<1/2$.
No attainment of the minimizing core ratio is asserted.

### Apply the existing total-clock quadrature to a clipped response

The already used complete-integral PNT estimate gives constants,
independent of $X$, with

$$
\int_2^\infty |E(v)|k(v)dv<\infty,
\qquad |E(v)|\le C_Ev\quad(v\ge2).
$$

On $[\ell_X,R_X]$, the ordinary derivative between prime-power
atoms is

$$
G_a'(v)=s_v'\int_v^\infty E(r)k(r)dr
-s_vE(v)k(v)-\frac a{\sqrt v}
+\frac{aE(v)}{2v^{3/2}},
\qquad s_v'=\frac{\log v+2}{2\sqrt v}.
$$

Each actual von Mangoldt atom contributes the retained positive
jump $a\Lambda(n)/\sqrt n$. The displayed density has absolute
integral $O_a(\sqrt{R_X}\log(eR_X))$. The elementary bound
$\Lambda(n)\le\log n$ gives
$\sum_{n\le R_X}\Lambda(n)/\sqrt n
\le2\sqrt{R_X}\log(eR_X)$. Thus the actual complete response has

$$
\operatorname{Var}_{[\ell_X,R_X]}G_a
\le C_a\sqrt{R_X}\log(eR_X).
\tag{AO5}
$$

No derivative of an infinite zero series or monotonicity of $G_a$
is used.

Fix $0<\tau<\tau'<R_A$, and define the bounded nonnegative readout

$$
F_X(v)=\min\left\{1,
\frac{(\tau'M_X-G_a(v))_+}{(\tau'-\tau)M_X}\right\}.
$$

AO4 makes every original left-tag value $F_X(A_i)$ zero beyond a
common start. Clipping is Lipschitz, so AO5 bounds its variation
by $C_a\sqrt{R_X}\log(eR_X)/[(\tau'-\tau)M_X]$.
Use the original least-core total clock $\mathcal A_X(t)$.
Assign $F_X(A_i)$ at the finitely many original tie tags. N2's
all-choice ordering leaves the tagged total-clock map nondecreasing;
composition cannot increase the readout's variation. Its integral
is unchanged by those finitely many assignments. The same Dragomir
arbitrary-partition bound already used in PT9 therefore gives

$$
0\le\int_{t_0}^{t_m}F_X(\mathcal A_X(t))dt
\le C_a\frac{\varepsilon_X^{\rm lab}
\sqrt{R_X}\log(eR_X)}{(\tau'-\tau)M_X}
=:\Delta_X=o(1/M_X).
$$

The unchanged label mesh is at most $e^{-5\ell_X/12}$ and
$\log R_X=o(\ell_X)$, which pay the last rate. Every original
outgoing weight, including the terminal one, is retained.

Now reuse PT10 and PG9 exactly. For the canonical visited set
$D_X=[\mathcal A_X(t_0),\mathcal A_X(t_m)]\setminus\bigcup_jG_j$,
they give $\mathcal A_{X\#}dt=\mathbf1_{D_X}dv$ up to
measure-zero endpoints and $|D_X|=L_X$. Since $F_X=1$ wherever
$G_a\le\tau M_X$,

$$
\boxed{
|D_X\cap\{G_a\le\tau M_X\}|\le\Delta_X,
\qquad
|D_X\cap\{G_a>\tau M_X\}|\ge L_X-\Delta_X.}
\tag{AO6}
$$

In particular the full real-center superlevel set in the selected
total-clock range has Lebesgue measure at least $L_X-o(1/M_X)$.
This is the original source's complete-response occupation; it is
not a replacement of its atomic $B$-occupation by Lebesgue measure.
Nonnegative clipping uses PT10's visited-set restriction and requires
no assigned sign for the skipped intervals.

### The remaining supplier is a complete-response large-value estimate

For a fixed $\tau<R_A$, an upper measure estimate below
$(1-\zeta)L_X$, with any fixed $\zeta>0$, on a common cofinal
sequence of these same original total-clock ranges would contradict
AO6 and hence exclude that RH-failure source. Such an estimate is
not supplied here. Its endpoints and threshold still come from the
same original windows.

Gafni--Tao's fixed-relative-error short-increment exceptional sets
are different observations. AO6 supplies a complete-response
superlevel requirement, not an inclusion in those short-increment
sets, a shrinking-tolerance theorem or an unconditional upper bound
for this new set. Fixed-anchor negative primitives and normal local
increments do not determine this complete future response.
The original signed upper estimate, MT8's actual-residence head,
the all-integer Robin inequality and RH remain unproved.
This application reuses its generic inequalities and existing
total-clock occupation identity; no new generic theorem,
literature-priority claim or kernel verification is made.


## Retain the compensation while controlling forward primitive excursions

Keep the original source and every full window, parameter and tie from
JM1--JM7, AO1--AO6 and MT8. In particular $0<a<5\kappa/8$,
$\eta<1/2$, $M_X=X^{1/2-\eta}\log X$ and
$C_*=d(1-\kappa)/16>0$ are unchanged. Write
$\mathcal J_X=\int_{t_0}^{t_m}G_a(\mathcal B_X(t))dt$ as in CQ5.
The source-specific consumer below keeps most of the original local
subtraction while moving the lower endpoint of its future integral
from $B$ to $A=B+t$. It then bounds that future by ordinary
real-center primitive excursions. This is a `repo-derived` paper
application; the resulting amplitude-weighted upper obligation is
unproved and is not a new prime theorem or Lean result.

### Absorb the finite past into the same local subtraction

At every intervening selected real clock, PG1 gives $K(A)=B$.
Put

$$
\Delta(A)=K(A)-K(K(A))=B-K(B)\ge0,
\qquad E(B)=\Delta(A)+Q(B).
$$

Nonnegativity follows from $B\le A$ and monotonicity of $K$.
All-choice ordering and CR17 extend the original uniform $t/B\to0$
to this entire real window: $t\le2\ell_X$ and its least core is at
least the original least left-endpoint core, whose ratio to
$\ell_X$ tends to infinity. The existing uniform
$|Q(v)|\le H_Q\sqrt v$ is retained.

Let $r=t/B$ and $c=B\log B/(A\log A)$. Monotonicity of the complete
$\psi$ gives $E(v)\le E(B)+v-B$ on $[B,A]$. The original decreasing
positive kernel, its exact integral, and $s_Bk(B)\le2B^{-3/2}$ give

$$
\begin{aligned}
I_{\rm past}:=s_B\int_B^A E(v)k(v)dv
&\le\frac{1-c}{\sqrt B}E(B)+\frac{t^2}{B^{3/2}}\\
&\le2r\frac{\Delta(A)}{\sqrt B}+2H_Qr
 +\frac{t^2}{B^{3/2}}.
\end{aligned}
\tag{PE1}
$$

Here $0\le1-c\le2r$ follows by integrating the derivative of
$v\log v$; no sign is assigned to $E(B)$.
If $t\le B^{3/4}$, the last term in PE1 is at most one.
If $t>B^{3/4}$, apply the existing LO1 with $u=B$, $v=A$.
Since $A/B\to1$ uniformly and $21/40<3/4$, it gives
$\Delta(A)\ge(9/200)t$ beyond one common start. Hence
$t^2/B^{3/2}\le(200/9)r\Delta(A)/\sqrt B$ in this second case.
For every fixed $0<\epsilon<a$, both cases therefore give

$$
I_{\rm past}\le\epsilon\frac{\Delta(A)}{\sqrt B}+2H_Q+1.
$$

Subtract the original $aE(B)/\sqrt B$ before discarding any term.
The remaining $Q(B)$ term is bounded by $aH_Q$, so

$$
\boxed{
G_a(B)\le s_B\int_A^\infty E(v)k(v)dv
 -(a-\epsilon)\frac{\Delta(A)}{\sqrt B}+C_\epsilon.}
\tag{PE2}
$$

The constant and start are uniform in the original labels and ties
and in their selected real interpolation. This uses no SI1,
$B\ge X$, $\Theta<1$ or bound on $V_X^{\rm lag}$.
CR24 already absorbs a quadratic lag into the positive removal gain;
PE2 instead absorbs it into the same actual local subtraction and
retains a nonnegative compensation credit for an upper comparison.
Neither the complete future integral nor the full recentering
error is declared small.

### Reuse the paid common horizon and bound its forward primitives

Use FH1's unchanged common horizon $\mathsf U_X$. It is eventually
beyond all original $A$ clocks as well as their cores, since
$A\le2B$ and $\log\mathsf U_X/\mathsf Y_X\to\infty$.
FH1 pays the integrated remote tail once at $o(L_X)$.
For any real center $x\ge b_X$, put $u_j=2^jx$ and
$v_j=\min(2u_j,\mathsf U_X)$. Define

$$
P_{X,j}(x)=u_j^{-3/2}
\sup_{u_j\le v\le v_j}\int_{u_j}^vE(w)dw
\quad(u_j<\mathsf U_X),
\qquad P_{X,j}(x)=0\quad(u_j\ge\mathsf U_X).
\tag{PE3}
$$

These are nonnegative continuous bounded readouts on each compact
center shell, using the actual complete $\psi$. The primitive is
continuous even at its prime-power atoms. Integrating each shell by
parts, with $F(v)=\int_{u_j}^vE(w)dw$, gives

$$
\int_{u_j}^{v_j}E(v)k(v)dv
=F(v_j)k(v_j)-\int_{u_j}^{v_j}F(v)k'(v)dv
\le u_j^{3/2}P_{X,j}(x)k(u_j).
$$

Consequently

$$
s_x\int_x^{\mathsf U_X}E(v)k(v)dv
\le\sum_j2^{-j/2}\frac{\log x}{\log(2^jx)}
\left(1+\frac1{\log(2^jx)}\right)P_{X,j}(x).
$$

All summands on the right are nonnegative. Thus multiplication by
$s_B/s_A\le1$ preserves this upper bound without dropping a signed
normalization factor. Set $c_X=1+1/\log b_X$ and
$N_X=\lceil\log_2(\mathsf U_X/b_X)\rceil$.
For the canonical visited set $D_X$ in PG9, define

$$
V_X^K=\int_{D_X}
\frac{K(x)-K(K(x))}{\sqrt{K(x)}}dx\ge0.
$$

Use PE2 and precisely PT10/PG9's existing total-clock change of
variables. Together with FH1 this gives

$$
\boxed{
\mathcal J_X\le c_X\sum_{j<N_X}2^{-j/2}
\int_{D_X}P_{X,j}(x)dx
 -(a-\epsilon)V_X^K+O_\epsilon(L_X)+o(L_X).}
\tag{PE4}
$$

No domination of atomic $B$-occupation or sign of skipped intervals
is assumed. The only new consumer of the occupation identity is
this nonnegative forward-primitive bound with its original credit.

### Count amplitudes on the same window, rather than only centers

Cover all possible $A$ centers by the dyadic shells
$S_r=[2^rb_X,2^{r+1}b_X)$, stopping after
$C_X+2\ell_X$, where $C_X$ is the original endpoint core ceiling.
There are $O(\mathsf Y_X)$ center shells. The existing refined FH1
horizon gives
$N_X=O(\mathsf Y_X^{5/3}(\log\mathsf Y_X)^{1/3})$, including
$\Theta=1$. Keep every future shell with its actual weight;
$\sum_{j<N_X}2^{-j/2}\le S:=2+\sqrt2$.

Put $L_{X,r}=|D_X\cap S_r|$, so $\sum_rL_{X,r}=L_X$, and define
ordinary unselected Lebesgue exceptional measures

$$
e_{X,r,j}(z)=|\{x\in S_r:P_{X,j}(x)>zM_X\}|.
$$

For fixed $\tau>0$ let

$$
\mathcal E_X(\tau)=\sum_{j<N_X}2^{-j/2}\sum_r
\int_\tau^\infty\min\{L_{X,r},e_{X,r,j}(z)\}dz.
\tag{PE5}
$$

The existing coarse PNT input $|E(v)|\le H_2v/\log^2v$ yields
$P_{X,j}(x)\le(3H_2/2)\sqrt{2^jx}/\log^2(2^jx)$ whenever the
shell is active. This supplies finite amplitude ceilings, not an
$M_X$-scale bound. Reuse the layer-cake formula inside the actual
consumer: the intersection at each level has measure at most both
$L_{X,r}$ and $e_{X,r,j}(z)$. Hence

$$
\sum_{j<N_X}2^{-j/2}\int_{D_X}P_{X,j}(x)dx
\le M_X[S\tau L_X+\mathcal E_X(\tau)].
$$

FH2--FH3, FP4, MR2--MR3 and MT7 already give
$\mathcal J_X-Z_X^{\rm right}(T_X)=o(M_XL_X)$.
Apply this paid transfer once, and use $M_X\to\infty$ in PE4:

$$
\boxed{
Z_X^{\rm right}(T_X)\le
c_XM_X[S\tau L_X+\mathcal E_X(\tau)]
 -(a-\epsilon)V_X^K+o(M_XL_X).}
\tag{PE6}
$$

The head, every actual zero and multiplicity, its prescribed cutoff,
all original ties and the single common cofinal sequence remain
unchanged. No smoothing loss is paid separately per shell.

A sufficient next supplier, not proved here, is that some fixed
$\epsilon\in(0,a)$, $\tau>0$ and $\delta>0$ satisfy

$$
c_X\left[S\tau+\frac{\mathcal E_X(\tau)}{L_X}\right]
 -(a-\epsilon)\frac{V_X^K}{M_XL_X}\le C_*-\delta
\tag{PE7}
$$

on a common cofinal sequence of original full windows.
Retain $c_X$ exactly: a potentially large cancellation against
$V_X^K$ does not permit replacing it by one for free.
The stronger condition $\tau=C_*/(4S)$ and
$\mathcal E_X(\tau)\le(C_*/4)L_X$ would give, after enlarging one
common start, $Z_X^{\rm right}(T_X)\le(3C_*/4)M_XL_X$ even without
using the credit. Neither condition has been established.

The observable PE3 explicitly retains

$$
\int_u^vE(w)dw=(v-u)E(u)
+\int_u^v[(w-u)-(\psi(w)-\psi(u))]dw.
$$

The already recorded Gafni--Tao short-increment result controls a
different observable, not this baseline-containing primitive.
The newer [Harm short-progression refinements](../Analytic/shortuniformity2026robininterfaces.md#short-increment-refinements-and-the-retained-robin-baseline)
also concern increments; their pointwise and mean-square refinements
do not supply PE7. Even at the visited initial center,
$E(A)=t+Q(A)$ is endogenous and cannot be set to zero.
A primitive allowance of order $M_Xu^{3/2}$ would require a relative
$u^2$ allowance of order $M_X/\sqrt u$, which is not one fixed
tolerance across the full retained horizon. Counting exceptional
centers without their amplitudes therefore leaves the stated gap.
The finite past is paid jointly with the original subtraction;
the amplitude-weighted forward-primitive estimate, original signed
upper comparison, all-integer Robin inequality and RH remain unproved.

## Future visits to the same selected set have a paid compensation bound

Retain the complete original source, every full window and all ties from
PE1--PE7, including $\Theta=1$. Use the same canonical $D_X$, horizon
$\mathsf U_X$, real-center shells, future-shell weights and amplitude
normalization. This is a `repo-derived` paper application of PE2's
existing two-case lag estimate and PT10/PG9's occupation interface.
No new generic perturbation theorem, prime estimate or Lean result is
asserted. The application controls only future integration over the
same visited set; the unvisited future remains in the upper obligation.

Define

$$
\rho_X=\sup_{\substack{t\in[t_0,t_m]\\u\text{ active at }t}}
\frac{t}{\log u}\longrightarrow0,
\qquad
g_X(x)=\frac{K(x)-K(K(x))}{\sqrt{K(x)}}\quad(x\in D_X).
$$

The uniform limit is already supplied in PE2's real-clock scope,
including all active ties. In particular $V_X^K=\int_{D_X}g_X(x)dx$.
For almost every $w\in D_X$, put $B(w)=K(w)$ and
$t(w)=w-B(w)\in[t_0,t_m]$. The same actual complete error satisfies
$E(w)=t(w)+Q(w)$, with $|Q(w)|\le H_Q\sqrt w$.

Split the complete error spatially, without changing $\psi$:

$$
E_X^\circ(w)=\mathbf1_{D_X^c}(w)E(w).
$$

Define $P_{X,j}^\circ$, $e_{X,r,j}^\circ$ and
$\mathcal E_X^\circ(\tau)$ by the exact formulas PE3 and PE5,
replacing $E$ only by $E_X^\circ$. Their lower endpoints, upper
endpoints, zero conventions, $N_X$, $S_r$, $L_{X,r}$ and $M_X$
are unchanged. Every skipped gap and every exterior future point
through $\mathsf U_X$ remains in this complement. The integral
primitive remains continuous even where its integrand has jumps.

### Bound the perturbation on ordinary centers before taking occupations

Write $T_r=2^rb_X$. For any ordinary center $y\in S_r$ and
$u=2^jy<\mathsf U_X$, comparison of the two suprema gives

$$
\begin{aligned}
|P_{X,j}(y)-P_{X,j}^\circ(y)|
&\le u^{-3/2}
 \int_{D_X\cap[u,\min(2u,\mathsf U_X)]}|E(w)|dw\\
&\le\frac{t_mL_X}{u^{3/2}}+
 \frac{\sqrt2H_QL_X}{u}\\
&\le h_{rj}:=
 \frac{t_mL_X}{(2^jT_r)^{3/2}}+
 \frac{\sqrt2H_QL_X}{2^jT_r}.
\end{aligned}
\tag{VP1}
$$

When $u\ge\mathsf U_X$, both readouts are zero. The centers in
VP1 need not belong to $D_X$: this uniform shell bound controls
the unselected exceptional measures in PE5 as well as selected
values. No sign on $E$ or on a skipped interval is used.

A uniform perturbation by $h_{rj}$ shifts each normalized amplitude
threshold by at most $h_{rj}/M_X$. Integrating the corresponding
superlevel inclusions, with the cap $L_{X,r}$ retained, changes

$$
\int_\tau^\infty
\min\{L_{X,r},e_{X,r,j}(z)\}dz
$$

by at most $L_{X,r}h_{rj}/M_X$, in either direction, for every
$\tau\ge0$. This is the usual superlevel perturbation bound applied
inside the present consumer, rather than a separately delivered
generic lemma. Summing the original weights and enlarging only
the finite geometric sums gives

$$
\begin{aligned}
M_X|\mathcal E_X(\tau)-\mathcal E_X^\circ(\tau)|
\le{}&\frac43t_mL_X\sum_rL_{X,r}T_r^{-3/2}\\
&+\frac{\sqrt2}{1-2^{-3/2}}H_QL_X
 \sum_rL_{X,r}T_r^{-1}.
\end{aligned}
\tag{VP2}
$$

For $x\in D_X\cap S_r$, one has $T_r\le x<2T_r$ and
$B(x)\le x$. The original full label window has
$t_0\ge\ell_X$, $t_m\le2\ell_X$ and
$L_X=t_m-t_0\le\ell_X$, so $t_mL_X\le2t(x)^2$.
Also $L_X/x\le t(x)/B(x)\le\rho_X$.
Since $(8/3)2^{3/2}<8$ and
$2\sqrt2/(1-2^{-3/2})<5$, VP2 consequently gives

$$
M_X|\mathcal E_X(\tau)-\mathcal E_X^\circ(\tau)|
\le8\int_{D_X}\frac{t(x)^2}{B(x)^{3/2}}dx
 +5H_Q\rho_XL_X.
$$

Reuse the two cases already proved in the PE2 argument:
when $t\le B^{3/4}$ the ratio $t^2/B^{3/2}$ is at most one;
otherwise $\Delta(x)\ge(9/200)t$ beyond the same common start.
They give $t^2/B^{3/2}\le1+(200/9)\rho_Xg_X(x)$.
Thus, uniformly in the original full windows, all ties and every
$\tau\ge0$,

$$
\boxed{
M_X|\mathcal E_X(\tau)-\mathcal E_X^\circ(\tau)|
\le\frac{1600}{9}\rho_XV_X^K+
 (8+5H_Q\rho_X)L_X.}
\tag{VP3}
$$

This pays the amplitude-integrated effect of revisiting $D_X$,
without assuming $V_X^K=O(M_XL_X)$.

### Keep the correction inside the same signed upper account

For the unchanged $c_X$ put

$$
\gamma_X=\frac{1600}{9}c_X\rho_X\longrightarrow0,
\qquad
\omega_X=\frac{c_X(8+5H_Q\rho_X)}{M_X}\longrightarrow0.
$$

Apply VP3 once in PE6. The original head and already paid transfer
remain unchanged, and the resulting upper account is

$$
\boxed{
\begin{aligned}
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le{}&c_X\left[S\tau+
 \frac{\mathcal E_X^\circ(\tau)}{L_X}\right]\\
&-(a-\epsilon-\gamma_X)
 \frac{V_X^K}{M_XL_X}+\omega_X+o(1).
\end{aligned}}
\tag{VP4}
$$

For fixed $0<\epsilon<a$, the retained credit coefficient is
eventually positive. The term
$\gamma_XV_X^K/(M_XL_X)$ need not tend to zero and is not
discarded. The logarithmic factor $c_X$ is kept exactly.

The restricted estimate VP3 is supplied; the remaining sufficient
supplier is a strict joint upper comparison

$$
c_X\left[S\tau+\frac{\mathcal E_X^\circ(\tau)}{L_X}\right]
-(a-\epsilon-\gamma_X)\frac{V_X^K}{M_XL_X}
+\omega_X\le C_*-\delta
\tag{VP5}
$$

for some fixed $\epsilon\in(0,a)$, $\tau>0$ and $\delta>0$
on one common cofinal sequence of the original full windows.
VP5 is not proved here. In particular $E_X^\circ$ retains the
entire unvisited future, not just skipped gaps, and no sign or
phase balance is assigned to it. This application introduces
neither an independent sample nor a favorable tie choice or a
new subsequence. The original strict signed-head estimate,
all-integer Robin inequality and RH remain unproved.

## Actual activation counts pay a class of skipped-gap excursions

Keep the original full source, all ties, clocks, windows and parameters
from PG1--PG3, PE3--PE6 and VP1--VP5. This application pays the internal
deviation on an explicitly classified family of actual skipped gaps.
It retains their baseline, every unclassified gap and the entire exterior
future through $\mathsf U_X$. It is a `repo-derived` paper application,
not a new generic prime theorem, Lean result or proof of VP5 or RH.

### Reuse the classical restriction on simultaneous threshold layers

The [existing Erdős--Nicolas note](../ArithSums/erdosnicolas1975repartition.md#exact-zero-benefit-exceptions-use-at-most-four-branches)
records Proposition 4(c)--(d) and its proof, printed pp.70--71.
The classical six-exponentials argument excludes a common positive
threshold for three distinct primes. Reuse that restriction for the
actual inventory's threshold price $\lambda(\xi)$; do not infer that
two cores at a nonlinear switch are adjacent CA integers.

In the present parameters the actual $p$-layer reward is

$$
r_{p,j}=\frac1{\log p}
\log\frac{p^{j+1}-1}{p(p^j-1)},
\qquad \lambda(\xi)=r_{p,j}.
$$

The layers of one prime have strictly decreasing rewards. Thus at most
two layers activate at one actual time. Also
$r_{p,j}\le\log(1+1/p)/\log p<\lambda(p)$, so the decreasing
price gives $p<\xi$. Retaining the full mass of every simultaneous
activation therefore gives

$$
dK(\{\xi\})\le2\log\xi.
\tag{AC1}
$$

For an original switch gap $G_s=(\alpha_s,\beta_s)$ let
$h_s=\beta_s-\alpha_s$ and let $m_s$ count its distinct actual
activation times. PG1's endpoint contacts and absence of activation
atoms at the endpoints give

$$
h_s=K(\beta_s)-K(\alpha_s)
\le2m_s\log\beta_s.
\tag{AC2}
$$

The restriction AC1 is classical. AC2 uses it on the same actual
inventory; $m_s$ is not uniformly bounded and the whole switch gap
is not treated as one threshold event.

### Classify actual gaps before comparing their primitives

Choose $\upsilon_X>0$ with $2\upsilon_X<b_X^{1/4}$, where $b_X$
is PE3's unchanged all-tie least core clock. Every gap endpoint is
at least $b_X$. Define the family

$$
\mathscr G_X^{(\upsilon)}=
\left\{G_s:
m_s\log(2\alpha_s)\le\upsilon_X\alpha_s^{3/4}\right\}.
\tag{AC3}
$$

This is a classification within each original window. It does not
discard a window, select a favorable tie or impose a sign on $E$.
If a classified gap had $\beta\ge2\alpha$, AC2 and monotonicity of
$v/\log v$ for $v>e$ would give

$$
m_s\ge\frac{\beta}{4\log\beta}
\ge\frac{\alpha}{2\log(2\alpha)},
\qquad
\upsilon_X\ge\frac{\alpha^{1/4}}2\ge\frac{b_X^{1/4}}2,
$$

a contradiction. Consequently, for every classified gap,

$$
\beta_s<2\alpha_s,
\qquad h_s\le2\upsilon_X\alpha_s^{3/4}.
\tag{AC4}
$$

Write $r_s(w)=w-s-K(w)$ on that gap. The original decomposition is
$E(w)=s+Q(w)+r_s(w)$, with $Q=K-\psi$. Define only a comparison
integrand,

$$
\widehat E_X^{(\upsilon)}(w)=E_X^\circ(w)
-\sum_{G_s\in\mathscr G_X^{(\upsilon)}}
\mathbf1_{G_s}(w)r_s(w).
\tag{AC5}
$$

On a classified gap it equals $s+Q(w)$. On $D_X$ it is zero;
everywhere else it is the unchanged $E_X^\circ$. In particular it
preserves all unclassified gaps and both exterior portions that an
ordinary center can see. It is not a modified prime-counting function.

Form $\widehat P_{X,j}^{(\upsilon)}$,
$\widehat e_{X,r,j}^{(\upsilon)}$ and
$\widehat{\mathcal E}_X^{(\upsilon)}(\tau)$ by the original
PE3--PE5 and VP definitions, replacing only the integrand by AC5.
Keep the original centers, shell cap $L_{X,r}$, normalization $M_X$,
horizon and the zero convention when $2^jx\ge\mathsf U_X$.
These primitives are finite and continuous on each compact center
shell: AC5 is locally bounded and has the original finite horizon.

### Pay only the last unfinished classified gap

Reuse the actual nonnegative PG2 pressure, with no new dominance
assumption: $\mathscr P_s'=r_sk$, $\mathscr P_s\ge0$ and
$\mathscr P_s(\alpha)=\mathscr P_s(\beta)=0$. Since $k$ decreases,
integration by parts gives, for every $y\in[\alpha,\beta]$,

$$
\int_y^\beta r_s(w)dw
=-\frac{\mathscr P_s(y)}{k(y)}
-\int_y^\beta\mathscr P_s(w)(1/k(w))'dw\le0.
$$

Endpoint contact and monotonicity of $K$ also give
$w-\beta\le r_s(w)\le w-\alpha$. For
$\alpha\le y\le z\le\beta$, apply this pointwise bound and the
preceding suffix inequality in the two directions:

$$
\int_y^z r_s(w)dw
\le\frac12\min\{(z-\alpha)^2,(\beta-z)^2\}
\le\frac{h_s^2}{8}.
\tag{AC6}
$$

For any one interval $[u,v]$, its initial classified-gap suffix and
every complete classified gap have nonpositive residual contribution.
Only its final unfinished classified gap can leave a positive one.
If both endpoints lie in the same gap, AC6 applies directly.
Thus this bound is not summed over all gaps. For the original forward
range $u\le v\le\min(2u,\mathsf U_X)$, that last gap has
$\alpha_s<v\le2u$. AC4 and AC6 give

$$
u^{-3/2}\int_u^v
\sum_{G_s\in\mathscr G_X^{(\upsilon)}}
\mathbf1_{G_s}(w)r_s(w)dw
\le\frac{h_s^2}{8u^{3/2}}
\le\sqrt2\,\upsilon_X^2.
$$

If there is no unfinished classified gap, the left side is nonpositive.
This comparison holds at each original endpoint $v$ before taking
the same supremum. For every ordinary center $x\ge b_X$, including
centers outside $D_X$, it follows that

$$
P_{X,j}^\circ(x)
\le\widehat P_{X,j}^{(\upsilon)}(x)
+\sqrt2\,\upsilon_X^2.
\tag{AC7}
$$

Move the normalized amplitude threshold by
$\sqrt2\upsilon_X^2/M_X$ inside the same capped layer-cake
consumer used in VP3. Each shell integral changes in this upper
direction by at most $\sqrt2\upsilon_X^2L_{X,r}/M_X$.
Since $\sum_rL_{X,r}=L_X$ and
$\sum_{j<N_X}2^{-j/2}\le S=2+\sqrt2$, this gives, for all $\tau\ge0$,

$$
M_X\mathcal E_X^\circ(\tau)
\le M_X\widehat{\mathcal E}_X^{(\upsilon)}(\tau)
+(2+2\sqrt2)\upsilon_X^2L_X.
\tag{AC8}
$$

AC8 is a one-sided occupation comparison, not a bound on the absolute
difference. Its cost has no factor counting gaps, center shells or
future shells.

### Keep the same credit and all remaining future contributions

One choice needing no extra arithmetic hypothesis is

$$
\upsilon_X=\min\{b_X^{1/8},M_X^{1/4}\}\longrightarrow\infty.
\tag{AC9}
$$

The original $b_X,M_X\to\infty$ make its strict size condition
eventually valid, and $\upsilon_X^2/M_X\le M_X^{-1/2}\to0$.
Substitute AC8 once into VP4 to obtain

$$
\boxed{
\begin{aligned}
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le{}&c_X\left[S\tau+
\frac{\widehat{\mathcal E}_X^{(\upsilon)}(\tau)}{L_X}\right]\\
&-(a-\epsilon-\gamma_X)\frac{V_X^K}{M_XL_X}
+\omega_X
+\frac{(2+2\sqrt2)c_X\upsilon_X^2}{M_X}+o(1).
\end{aligned}}
\tag{AC10}
$$

The explicit added term tends to zero independently of the size of
$V_X^K/(M_XL_X)$. The exact $c_X$ and the entire credit coefficient
remain. All original full windows, maximizing ties and the full
$\Theta\in(1/2,1]$ range are retained; no favorable subsequence is
introduced.

This partial payment covers only $r_s$ on AC3's classified gaps.
No positive proportion or eventual coverage of all gaps is established.
Even if every gap qualified, their $s+Q(w)$ baselines and the entire
exterior future would remain in AC5. The missing sufficient estimate
is still a strict joint upper comparison for this residual occupation
and the same $V_X^K$ credit, leaving $C_*-\delta$ for fixed positive
parameters on the original common cofinal sequence. That estimate,
MT8, the all-integer Robin inequality and RH remain unproved.

## The original source clock localizes skipped-gap baselines

Retain AC1--AC10's complete original source and its classified family
$\mathscr G_X^{(\upsilon)}$, with AC9's choice of $\upsilon_X$.
This `repo-derived` paper application pays a specific remaining term:
the source-time baseline of every actual gap above an auxiliary clock
cutoff. Its input $s<t_m\le2\ell_X$ is the original full-window bound
already used in VP2--VP3. The square-root $Q$ allowance and the
ordinary-center capped-occupation perturbation argument are also
reused. No new generic perturbation theorem, literature prime estimate
or Lean result is asserted.

### Localize the baseline without truncating the future horizon

Let $\mathscr G_X$ contain all original skipped gaps and put
$\mathfrak G_X=\bigcup_{G_s\in\mathscr G_X}G_s$. Keep the original
$I_X,D_X,\mathsf U_X$ and $\widehat E_X^{(\upsilon)}$.
For any $H>0$ define only a comparison integrand:

$$
E^{\rm loc}_{X,H}(w)=\widehat E_X^{(\upsilon)}(w)
-\mathbf1_{\mathfrak G_X}(w)Q(w)
-\sum_{G_s\in\mathscr G_X}
 s\,\mathbf1_{G_s\cap[H,\infty)}(w).
\tag{BL1}
$$

The actual gaps are disjoint. Thus, almost everywhere, BL1 is zero
on $D_X$, is $s\mathbf1_{\{w<H\}}$ on a classified gap, is
$s\mathbf1_{\{w<H\}}+r_s(w)$ on an unclassified gap, and is the
original $E(w)$ outside $I_X$. It retains every unclassified residual
and both exterior portions visible to an ordinary center. Neither
$K$ nor $\psi$ nor an original clock is changed.

Define $P^{\rm loc}_{X,H,j}$, $e^{\rm loc}_{X,H,r,j}$ and
$\mathcal E^{\rm loc}_{X,H}(\tau)$ by PE3--PE5's exact formulas,
replacing only the integrand by BL1. Their centers, endpoints, shell
caps $L_{X,r}$, normalization $M_X$, future-shell weights, horizon
and zero convention remain unchanged. The primitive is continuous
on compact center shells even if $H$ cuts through a gap.

### Pay the high-clock part at every ordinary center

Put

$$
C_{1/2}=\frac23(2\sqrt2-1),\qquad
h_{X,H}=\frac{t_m}{\sqrt H}+C_{1/2}H_Q.
$$

Beyond the existing common start for $|Q(w)|\le H_Q\sqrt w$,
fix any ordinary center $x\ge b_X$, any future index $j$, and
$u=2^jx<\mathsf U_X$. For every permitted endpoint
$u\le v\le\min\{2u,\mathsf U_X\}$, disjointness and
$0<s<t_m$ give

$$
\left|\int_u^v
[\widehat E_X^{(\upsilon)}(w)-E^{\rm loc}_{X,H}(w)]dw\right|
\le H_Q\int_u^{2u}\sqrt w\,dw
+t_m|[u,2u]\cap[H,\infty)|.
\tag{BL2}
$$

The first integral is $C_{1/2}u^{3/2}$. For the second term,

$$
u^{-3/2}|[u,2u]\cap[H,\infty)|\le H^{-1/2}.
$$

Indeed for $u\ge H$ it is at most $u^{-1/2}$; for $u<H$, writing
$z=u/H\in(0,1)$ reduces it to
$(2z-1)_+/z^{3/2}\le1$. The latter follows from
$z^{3/2}-2z+1\ge0$ on $[0,1]$: this expression decreases to zero
there, since its derivative is $(3/2)\sqrt z-2<0$.

Normalize BL2 and take the two suprema over the same endpoints.
For every ordinary center, including centers outside $D_X$,

$$
\boxed{
|\widehat P_{X,j}^{(\upsilon)}(x)-P^{\rm loc}_{X,H,j}(x)|
\le h_{X,H}.}
\tag{BL3}
$$

When $u\ge\mathsf U_X$ both readouts are zero. BL3 therefore also
controls the unselected center measures in the occupation consumer.
Apply the existing VP2--VP3 capped-superlevel perturbation argument:
a threshold shift of $h_{X,H}/M_X$ changes each amplitude integral
by at most $L_{X,r}h_{X,H}/M_X$, in either direction, for every
$\tau\ge0$. Summing the unchanged weights and using
$\sum_rL_{X,r}=L_X$ and $\sum_{j<N_X}2^{-j/2}\le S=2+\sqrt2$ gives

$$
\boxed{
M_X|\widehat{\mathcal E}_X^{(\upsilon)}(\tau)
-\mathcal E^{\rm loc}_{X,H}(\tau)|
\le S\left(\frac{t_m}{\sqrt H}+C_{1/2}H_Q\right)L_X.}
\tag{BL4}
$$

No gap count, coverage fraction, selected-center density or upper
bound on the lag credit appears. BL4 is an absolute comparison of
these two occupation functionals; AC8's earlier removal of classified
residuals remains a separate one-sided comparison.

### Use the witness scale rather than a bound on the original clocks

The unchanged normalization supplies

$$
t_m\le2\ell_X=\frac d4M_X\sqrt X.
$$

Consequently BL4 gives, uniformly in the original full windows,
all maximizing ties and $\tau\ge0$,

$$
\frac{|\widehat{\mathcal E}_X^{(\upsilon)}(\tau)
-\mathcal E^{\rm loc}_{X,H}(\tau)|}{L_X}
\le\frac{Sd}{4}\sqrt{\frac XH}
+\frac{SC_{1/2}H_Q}{M_X}.
\tag{BL5}
$$

For $H=RX$ this bounds the first term by $Sd/(4\sqrt R)$.
For the single deterministic choice

$$
H_X=X(\log X)^2,
$$

it instead gives

$$
\boxed{
\frac{|\widehat{\mathcal E}_X^{(\upsilon)}(\tau)
-\mathcal E^{\rm loc}_{X,H_X}(\tau)|}{L_X}
\le\frac{Sd}{4\log X}+\frac{SC_{1/2}H_Q}{M_X}=o(1).}
\tag{BL6}
$$

This pays the high-clock source-time baselines of all actual gaps,
including high-activation-complexity gaps. It does not bound their
residuals. The estimate uses neither polynomial original clocks nor
a horizon ending at $H_X$, and retains $\Theta=1$. It does not assert
that any original clock lies below $H_X$. In particular, the entire
exterior future and every unclassified residual above $H_X$ stay in
BL1. The $Q$ allowance is already available independently; the
additional payment is for the retained $s$-term above $H_X$.

### Insert the payment in the unchanged joint account

Apply BL4 once to AC10, keeping the exact $c_X$ and credit coefficient:

$$
\boxed{
\begin{aligned}
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le{}&c_X\left[S\tau+
\frac{\mathcal E^{\rm loc}_{X,H}(\tau)}{L_X}\right]
-(a-\epsilon-\gamma_X)\frac{V_X^K}{M_XL_X}\\
&+\omega_X+\frac{(2+2\sqrt2)c_X\upsilon_X^2}{M_X}
+\frac{c_XS}{M_X}\left(\frac{t_m}{\sqrt H}+C_{1/2}H_Q\right)
+o(1).
\end{aligned}}
\tag{BL7}
$$

For $H=H_X$ the newly displayed allowance is at most
$c_XS[d/(4\log X)+C_{1/2}H_Q/M_X]\to0$.
It introduces no new multiple of $V_X^K$; the potentially large
$\gamma_XV_X^K/(M_XL_X)$ remains inside the original coefficient.
No assumption $V_X^K=O(M_XL_X)$ is used. The absolute difference
between the joint accounts formed from the two occupations is also
bounded by this same allowance, even if their separate terms are large.
Every comparison is uniform before choosing the original cofinal
sequence, so no new sequence or favorable tie is introduced.

At $H=H_X$, the remaining comparison integrand is exactly, almost
everywhere,

$$
E^{\rm loc}_{X,H_X}(w)=\mathbf1_{I_X^c}(w)E(w)
+\sum_{G_s\in\mathscr G_X}s\mathbf1_{G_s\cap\{w<H_X\}}(w)
+\sum_{G_s\notin\mathscr G_X^{(\upsilon)}}\mathbf1_{G_s}(w)r_s(w).
$$

A sufficient supplier, still unproved, is that fixed
$0<\epsilon<a$, $\tau>0$ and $\delta>0$ satisfy

$$
c_X\left[S\tau+
\frac{\mathcal E^{\rm loc}_{X,H_X}(\tau)}{L_X}\right]
-(a-\epsilon-\gamma_X)\frac{V_X^K}{M_XL_X}
\le C_*-\delta
\tag{BL8}
$$

on one common cofinal sequence of the original qualifying full
windows, retaining every original label and maximizing tie.
BL6 gives no favorable occupation bound for the baseline below $H_X$,
no estimate for the retained unclassified residuals and no signed
bound for the exterior $E$. Near $w\asymp X$, even the baseline
majorant $t_m/\sqrt w$ is of order $M_X$; the same localization bound
does not pay that term with a vanishing allowance.
The strict combined supplier BL8, MT8, the all-integer Robin inequality
and RH remain unproved. This application has no Lean/kernel proof.
## Weighted short-interval counts pay more actual gap residuals

Retain the full source, all original windows and ties, $\Theta=1$,
BL1--BL7's horizon and exact credit. The new consumer is the positive
residual area on a comparable actual gap. It uses the published
[Thorner--Zaman weighted short-interval estimate](../Analytic/shortuniformity2026robininterfaces.md#effective-weighted-prime-counts-in-short-intervals),
with LO1's already established first-layer endpoint rule. The original
PG2 suffix sign and AC/VP capped-occupation comparison are reused.
This is a `repo-derived` paper application, not a new prime theorem,
generic perturbation theorem, Lean result or RH proof.

### Match the published weighted count to the actual strict inventory

Use Theorem 1.1 of arXiv:2108.10878v2 with modulus $2$, residue $1$
and fixed $\varepsilon_{\rm TZ}=1/60$. There is no nontrivial real
character modulo $2$, so the exceptional-zero branch is absent;
$\lambda_{\rm TZ}=1$ and $\theta_{\rm TZ}+\varepsilon_{\rm TZ}=3/5$.
The actual increment intervals used below start at $\alpha\to\infty$,
so all their primes are odd; restriction to odd primes already gives
the lower bound in PA1's wider length range.
The parameter $\varepsilon_{\rm TZ}$ is independent of the fixed
$\epsilon$ in BL7's credit coefficient.

Put

$$
\Phi(y)=\left(\frac{\log y}{\log\log y}\right)^{1/3},\qquad
\mathfrak e(y)=e^{-c\Phi(y)}.
$$

The published effective constants, with a smaller fixed $c>0$, give
fixed $C>0$ and one start such that, uniformly for
$\alpha\le z\le2\alpha$ and $z^{3/5}\le h\le z$,

$$
\sum_{z-h<p\le z}\log p\ge h[1-C\mathfrak e(\alpha)].
\tag{PA1}
$$

Indeed the source's error denominator at modulus $2$ is

$$
\log2+(\log(z/h))^{2/3}
 (\log^+\log(z/h))^{1/3}
 +(\log z)^{2/5}(\log\log z)^{1/5}.
$$

It is at most a fixed multiple of
$(\log\alpha)^{2/3}(\log\log\alpha)^{1/3}$ in this range.
The first product is zero by its continuous convention when
$\log(z/h)=0$. The numerator is at least $\log\alpha$,
which supplies PA1 after decreasing $c$.
These are weighted prime sums; no extra $\log\alpha$ factor is
charged to a prime-count error.

### Bound positive residual area on every comparable actual gap

Let $G_s=(\alpha,\beta)$ be any original actual gap with
$h=\beta-\alpha\le\alpha$. Set $T_\alpha=1+(2\alpha)^{3/5}$.
PG1's endpoint contact and monotonicity of the same strict $K$ give

$$
r_s(\alpha+t)=t-[K(\alpha+t)-K(\alpha)]\le t
\qquad(0\le t\le h).
$$

If $t\ge T_\alpha$, every prime in $(\alpha,\alpha+t-1]$
has its first activation strictly in $(\alpha,\alpha+t)$ by the
existing rule $p<\xi_{p,1}<p+1$. Its full $\log p$ mass belongs
to this $K$ increment. Higher layers and simultaneous activations
remain nonnegative parts of the same full inventory. In PA1 take
$z=\alpha+t-1$ and $h_{\rm TZ}=t-1$. Then
$\alpha\le z\le2\alpha$, $z-h_{\rm TZ}=\alpha$ and
$h_{\rm TZ}\ge(2\alpha)^{3/5}\ge z^{3/5}$, so

$$
r_s(\alpha+t)
\le t-(t-1)[1-C\mathfrak e(\alpha)]
\le1+C\mathfrak e(\alpha)t.
$$

Integrating these nonnegative upper bounds on the two ranges gives

$$
\boxed{
\int_\alpha^\beta(r_s(w))_+dw
\le\frac{T_\alpha^2}{2}+h
 +\frac C2\mathfrak e(\alpha)h^2
\ll\alpha^{6/5}+h+\mathfrak e(\alpha)h^2.}
\tag{PA2}
$$

If $h<T_\alpha$, the first upper bound alone suffices. PA2 therefore
holds for every sufficiently large comparable actual gap, independently
of the following classification. Its right side also bounds
$\int_y^z r_s(w)dw$ for every $\alpha\le y\le z\le\beta$.
Unlike the generic $h^2/8$ estimate, PA2 gives a decaying coefficient
on the long-range quadratic term using an actual arithmetic count.
The contact at $\alpha$ is essential; an exterior interval without
that contact would retain its unbounded starting baseline.

### Enlarge the paid class without claiming any coverage fraction

Keep AC9's unchanged $\upsilon_X=\min\{b_X^{1/8},M_X^{1/4}\}$ and
set

$$
\mathscr G_X^{\rm ar}
=\left\{G_s:
h_s\le\upsilon_X\alpha_s^{3/4}
             e^{c\Phi(\alpha_s)/2}\right\}.
\tag{PA3}
$$

Every endpoint has $\alpha_s\ge b_X$. Since
$\upsilon_X\le b_X^{1/8}\le\alpha_s^{1/8}$ and
$\Phi(y)/\log y\to0$, eventually
$e^{c\Phi(\alpha_s)/2}\le\alpha_s^{1/16}$. Thus
$h_s/\alpha_s\le\alpha_s^{-1/16}\le b_X^{-1/16}\to0$
uniformly throughout this class. PA2 applies there beyond one common
start, including arbitrarily large original clocks.

AC4 already gives $h_s\le2\upsilon_X\alpha_s^{3/4}$ on the old
class $\mathscr G_X^{(\upsilon)}$. Since
$e^{c\Phi(\alpha_s)/2}\to\infty$ uniformly for $\alpha_s\ge b_X$,

$$
\mathscr G_X^{(\upsilon)}\subseteq\mathscr G_X^{\rm ar}
\tag{PA4}
$$

beyond that same enlarged start. No existence or positive proportion
of newly admitted gaps is asserted.

The criteria can be distinguished without assigning such a gap to
an actual window. If an actual gap satisfies
$3\upsilon_X\alpha_s^{3/4}\le h_s\le
\upsilon_X\alpha_s^{3/4}e^{c\Phi(\alpha_s)/2}$, its first-layer
activation times are distinct because they lie in disjoint
$(p,p+1)$ intervals. PA1 applied up to $\beta_s-1$ consequently gives

$$
m_s\log(2\alpha_s)
\ge\sum_{\alpha_s<p\le\beta_s-1}\log p
\ge(1-o(1))h_s>\upsilon_X\alpha_s^{3/4}.
$$

Such a gap would be outside AC3's old class and inside PA3. This
conditional comparison does not prove that a gap in that band exists.

### Apply the existing last-unfinished-gap and occupation consumers

Remove only the still-unpaid residuals in the added class:

$$
R_X^{\rm add}(w)=
\sum_{G_s\in\mathscr G_X^{\rm ar}\setminus\mathscr G_X^{(\upsilon)}}
\mathbf1_{G_s}(w)r_s(w),\qquad
E_X^{\rm red}(w)=E^{\rm loc}_{X,H_X}(w)-R_X^{\rm add}(w).
\tag{PA5}
$$

PG2's nonpositive unweighted suffix is available on every actual gap,
not only on AC3's classified family. Reuse the AC6--AC7 consumer:
in any interval $[u,v]$ the initial suffix and every complete added
gap have nonpositive contribution. Only the final unfinished added
gap can need payment; if both endpoints are in one gap, PA2 applies
directly. For $u\le v\le\min\{2u,\mathsf U_X\}$ its left endpoint
satisfies $\alpha_s<v\le2u$. Dividing PA2 by $u^{3/2}$ and using PA3,
$h_s\le\alpha_s$ and $\alpha_s\ge b_X$, gives one fixed $C_2>0$ with

$$
u^{-3/2}\int_u^vR_X^{\rm add}(w)dw
\le J_X:=C_2[\upsilon_X^2+b_X^{-3/10}].
\tag{PA6}
$$

Here $\mathfrak e(\alpha_s)h_s^2/\alpha_s^{3/2}
\le\upsilon_X^2$ and $h_s/\alpha_s^{3/2}\le\alpha_s^{-1/2}$.
When no final unfinished added gap exists, the integral is nonpositive.
There is no factor counting gaps or future shells.

Define $P_{X,j}^{\rm red}$, $e_{X,r,j}^{\rm red}$ and
$\mathcal E_X^{\rm red}(\tau)$ by the unchanged PE3--PE5 formulas,
with integrand PA5 and the original zero convention. PA6 holds before
taking the same endpoint supremum at every ordinary center
$x\ge b_X$, including centers outside $D_X$. Directly applying
VP/AC's existing capped layer-cake comparison gives

$$
P_{X,H_X,j}^{\rm loc}(x)\le P_{X,j}^{\rm red}(x)+J_X,
\qquad
\mathcal E_{X,H_X}^{\rm loc}(\tau)
\le\mathcal E_X^{\rm red}(\tau)+\frac{SJ_X}{M_X}L_X.
\tag{PA7}
$$

All original caps $L_{X,r}$, center shells, future weights and the
full horizon remain. PA7 is one-sided, not an absolute perturbation
estimate. It uses no selected-center density or $|S_r|/L_{X,r}$ factor.

### Retain the remaining baseline, exterior and credit together

Apply PA7 once in BL7. The original explicitly paid allowances are
unchanged, and the additional normalized allowance is

$$
\Delta_X^{\rm add}:=\frac{c_XSJ_X}{M_X}
\le C_2Sc_X\left[M_X^{-1/2}
+\frac{b_X^{-3/10}}{M_X}\right]\longrightarrow0.
\tag{PA8}
$$

The leading upper account is therefore the same expression with
$\mathcal E_X^{\rm red}$ replacing $\mathcal E_{X,H_X}^{\rm loc}$:

$$
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le c_X\left[S\tau+\frac{\mathcal E_X^{\rm red}(\tau)}{L_X}\right]
-(a-\epsilon-\gamma_X)\frac{V_X^K}{M_XL_X}
+\mathfrak r_X^{\rm old}+\Delta_X^{\rm add},
$$

where $\mathfrak r_X^{\rm old}=o(1)$ denotes exactly BL7's old
allowances at $H=H_X$, including $\omega_X$ and the AC9 payment.
The exact $c_X$ and entire credit coefficient remain; no new
multiple of $V_X^K$ is introduced or discarded.

Almost everywhere, the retained integrand is exactly

$$
E_X^{\rm red}(w)=\mathbf1_{I_X^c}(w)E(w)
+\sum_{G_s\in\mathscr G_X}s\mathbf1_{G_s\cap\{w<H_X\}}(w)
+\sum_{G_s\notin\mathscr G_X^{\rm ar}}\mathbf1_{G_s}(w)r_s(w).
$$

Thus every low-clock baseline, the entire exterior arithmetic future
and every residual outside PA3 remain. Added residuals are paid on
their whole gaps, including portions above $H_X$. No original source,
window, tie, phase or horizon is changed, and no new cofinal sequence
is selected.

The remaining sufficient strict joint upper has not been established.
For the full contradiction objective, JM4's already recorded budget
$R_0-\delta$, or JM7's $R_\eta-\delta$, with fixed $\delta>0$,
can be used on the same original cofinal sequence; the stronger
MT8/BL8 budget remains unproved as well. These existing lower-margin
routes are reused, not new conclusions of PA1--PA8. The near-clock
baselines, remaining residuals and exterior $E$ still need a single
joint arithmetic estimate against the original credit.
The original strict signed upper, all-integer Robin inequality and RH
remain unproved; this application has no Lean/kernel verification.


## Direct actual-center integration pays every complete gap residual

Keep the original full source, all ties and every qualifying full window
from PE2, PG1--PG3, PG9 and JM1--JM7, including $\Theta=1$.
This `repo-derived` paper application uses the actual selected centers
before PE3's ordinary-center endpoint suprema. It pays all original
gap residuals by their existing exact weighted cancellation, rather
than assuming they belong to PA3's classified family. The remaining
low-clock baseline and full upper exterior still require a joint
estimate against the original credit. No new generic kernel identity,
prime theorem, literature-priority claim or Lean result is asserted.

Let $B(t)=\mathcal B_X(t)$, $A(t)=t+B(t)$,
$s_B=\sqrt B\log B$, $k=-\lambda'$, and
$\rho_X=\sup t/B\to0$, with PE2/VP1's same actual real-clock scope.
Keep $I_X=[A_0,A_m]$, $D_X$ and the original actual gaps
$G_s=(\alpha_s,\beta_s)$ from PG9, including switches at $t_0$
and excluding switches at $t_m$. The canonical endpoint $A_m$ is
unchanged. All endpoint tie tags have measure zero in source integration.
The common FH1 horizon $\mathsf U_X$ remains beyond $A_m$.

### Apply the existing gap equality before taking a primitive supremum

At almost every selected source time $t$, all future actual gaps lie
wholly above $A(t)$ and below $A_m$. PG2 gives, on every such gap,

$$
\int_{\alpha_s}^{\beta_s}r_s(w)k(w)dw
=\mathscr P_s(\beta_s)-\mathscr P_s(\alpha_s)=0,
\qquad r_s(w)=w-s-K(w).
\tag{DR1}
$$

Earlier gaps lie below $A(t)$ and contribute nothing to its forward
integral. Thus DR1 removes every gap residual from that actual signed
integral, including gaps outside PA3. On $D_X$ the same original
$E(w)$ equals $t(w)+Q(w)$; on $G_s$ it equals $s+Q(w)+r_s(w)$.
No sign on $Q$ or on the upper exterior is added.

For $H>0$, put $q_s=\min\{\beta_s,H\}$ and define the actual
low-clock baseline exposure

$$
\begin{aligned}
\mathfrak B_{X,H}
&=\int_{t_0}^{t_m}s_{B(t)}
 \sum_{\substack{t\le s<t_m\\\alpha_s<H}}
 s[\lambda(\alpha_s)-\lambda(q_s)]dt\\
&=\sum_{\substack{t_0\le s<t_m\\\alpha_s<H}}
 s[\lambda(\alpha_s)-\lambda(q_s)]
 \int_{t_0}^{s}s_{B(t)}dt\ge0.
\end{aligned}
\tag{DR2}
$$

The second expression is finite Fubini on the same source. When $H$
cuts a gap, its partial price difference is retained. It does not
truncate DR1's residual integration. No size estimate for DR2 follows
from writing it as this sum.

Retain the complete upper exterior in the signed quantity

$$
\mathfrak T_X=
\left(\int_{t_0}^{t_m}s_{B(t)}dt\right)
\int_{A_m}^{\mathsf U_X}E(w)k(w)dw.
\tag{DR3}
$$

The entire interval $(A_m,\mathsf U_X)$, even for superpolynomial
$\mathsf U_X$, is present. FH1 separately pays the remote tail beyond
$\mathsf U_X$ at $o(L_X)$. There is no lower exterior in a forward
integral starting at an actual $A(t)\in I_X$.

### Pay future visits and the high-clock baseline in this direct account

Reuse $|Q(w)|\le H_Q\sqrt w$ and GPP4's already evaluated positive
kernel moment. Because $B\le A$, it gives

$$
s_B\int_A^{A_m}|Q(w)|k(w)dw\le2H_Q.
$$

For future visits to $D_X$, monotonicity of $k$ and
$s_Bk(A)\le s_Bk(B)\le2B^{-3/2}$ give

$$
s_B\int_{D_X\cap[A,A_m]}t(w)k(w)dw
\le\frac{2t_mL_X}{B^{3/2}}
\le\frac{4t^2}{B^{3/2}}.
$$

The last inequality uses only the original full window:
$L_X\le\ell_X\le t$ and $t_m\le2\ell_X\le2t$.
Reuse exactly PE2's two cases. If $t\le B^{3/4}$ the last ratio is
at most four; otherwise $\Delta(A)=B-K(B)\ge(9/200)t$.
With the unchanged
$V_X^K=\int_{D_X}\Delta(x)/\sqrt{K(x)}dx$, the original
PT10/PG9 change of variables therefore gives

$$
\int_{t_0}^{t_m}s_{B(t)}
 \int_{D_X\cap[A(t),A_m]}t(w)k(w)dw\,dt
\le\frac{800}{9}\rho_XV_X^K+4L_X.
\tag{DR4}
$$

For the remaining gap baseline above $H$, disjointness, $s<t_m$
and $s_B\lambda(\max\{A,H\})\le1/\sqrt H$ give the uniform bound

$$
s_B\sum_{t\le s<t_m}s
 \int_{G_s\cap[H,\infty)}k(w)dw
\le\frac{t_m}{\sqrt H}.
$$

These payments involve neither a classified-gap coverage fraction nor
a count of gaps or future shells. Set $H_X=X(\log X)^2$ as in BL6.
Then $t_m\le(d/4)M_X\sqrt X$ pays this high-clock contribution by
$[d/(4\log X)]M_XL_X$.

### Keep the remaining signed exposure and exact credit together

Apply PE2, DR1--DR4 and the paid FH1 tail once. Reuse the existing
$\mathcal J_X-Z_X^{\rm right}(T_X)=o(M_XL_X)$ transfer. For each fixed
$0<\epsilon<a$, put $\widetilde\gamma_X=(800/9)\rho_X\to0$.
The resulting actual signed upper account is

$$
\boxed{
\begin{aligned}
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le{}&\frac{\mathfrak B_{X,H_X}+\mathfrak T_X}{M_XL_X}
 -(a-\epsilon-\widetilde\gamma_X)
 \frac{V_X^K}{M_XL_X}\\
&+\frac{d}{4\log X}+O_\epsilon(M_X^{-1})+o(1).
\end{aligned}}
\tag{DR5}
$$

This route branches at PE2, before the ordinary-center suprema and
capped occupation. Consequently DR5 contains no $c_X$ multiplier;
it does not replace $c_X$ by one or discard its credit correction in
PA8. The direct coefficient $\widetilde\gamma_XV_X^K/(M_XL_X)$ is
kept exactly; no bound on $V_X^K/(M_XL_X)$ is assumed.

The all-gap residual payment in DR1 does not bound the ordinary-center
occupation $\mathcal E_X^{\rm red}$. Those centers may cut a gap,
where the complete weighted cancellation is unavailable. PA8 and its
ordinary-center classified-residual account remain as separate estimates.

The generic pressure and Stieltjes identities also remain existing
results. In particular, for $\mathcal H(t)=V_X(t)+t\lambda(A(t))$,
PG1 and the [existing pressure-margin definition](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#98-完整价格裕度的临界切片与严格自匹配归约)
give $\mathcal H(t)=\gamma-\mathfrak D(A(t))$. Expressing DR2 or
its unrestricted variant as an envelope variation therefore supplies
no new positive reserve or quantitative upper bound.

The unpaid requirement is a same-source strict joint upper estimate
for DR5's first two terms below JM4's existing $R_0-\delta$, or the
applicable JM7 $R_\eta-\delta$, for one fixed $\delta>0$ on a common
cofinal sequence of the original full windows. Neither the positive
low-clock baseline nor the signed full upper exterior has been paid
by DR1--DR5. The original signed upper comparison, all-integer Robin
inequality and RH remain unproved. This application simplifies the
actual selected-source account without asserting a new arithmetic
supplier, an actual favorable sequence or kernel verification.


## Monotone source variation bounds the complete gap baseline

Keep PG1--PG3, PG9, PE2 and DR1--DR4 on the original full windows,
all maximizing ties and the same common cofinal source, including
$\Theta=1$. This is a `repo-derived` paper application of finite
Stieltjes integration by parts and the classical opposite-monotonicity
integral comparison. It gives a quantitative bound for the previously
retained gap baseline; it asserts no new generic inequality, literature
priority, arithmetic sign supplier or Lean/kernel result.

Write $B(t)=\mathcal B_X(t)$, $A(t)=B(t)+t$,
$s_B=\sqrt B\log B$, and set

$$
S(t)=\int_{t_0}^{t}s_{B(v)}\,dv,\qquad
S_m=S(t_m),\qquad
\mathsf L_X=\int_{t_0}^{t_m}\frac{t}{\sqrt{B(t)}}\,dt,
\qquad c_{\rm win}=\frac{2t_m}{t_m+t_0}\le\frac43.
$$

Here $\mathsf L_X$ is a continuous readout of the existing source lag;
it is not $L_X=t_m-t_0$ or the exact inventory credit $V_X^K$.
N2 and CQ1 already give a nondecreasing finite step function $B$.
Define the nonnegative complete gap baseline, before BL's clock split,

$$
\mathfrak B_X^{\rm all}
=\sum_{t_0\le s<t_m}
 sS(s)[\lambda(\alpha_s)-\lambda(\beta_s)].
\tag{BV1}
$$

DR2 gives $0\le\mathfrak B_{X,H}\le\mathfrak B_X^{\rm all}$
for every $H$. No actual gap, intermediate activation or higher layer
is removed by this comparison. A switch at $t_0$ has $S(t_0)=0$;
the original endpoint $A_m$ is the least-core terminal clock, with
no switch at $t_m$ charged to BV1.

### Use the same source price drops and retain both terminal debits

Put $g(t)=\lambda(A(t))$. On each open branch, $A'(t)=1$, so
$-g'(t)=k(A(t))$. At a switch $s$, its price drop is exactly
$\lambda(\alpha_s)-\lambda(\beta_s)$. Use right limits in the
Stieltjes measure at interior switches, retaining the terminal left
trace $g(t_m)=g(t_m-)=\lambda(A_m)$; the values at the finitely many
ties do not change any ordinary integral. Since $S$ is continuous, finite integration
by parts with $tS(t)$ gives

$$
\mathfrak B_X^{\rm all}
=\int_{t_0}^{t_m}[S(t)+ts_{B(t)}]\lambda(A(t))\,dt
-t_mS_m\lambda(A_m)
-\int_{t_0}^{t_m}tS(t)k(A(t))\,dt.
\tag{BV2}
$$

The source remains the same actual inventory and selector. BV2 is
finite Stieltjes accounting, rather than a new pressure identity.
The terminal term uses the unchanged $A_m$; no extra terminal tie or
favorable endpoint is chosen.

Monotonicity of $B$ and $B>1$ imply
$S(t)\le(t-t_0)s_{B(t)}$ and
$s_{B(t)}\lambda(A(t))\le B(t)^{-1/2}$.
Consequently the first integral in BV2 is at most
$\int_{t_0}^{t_m}(2t-t_0)/\sqrt{B(t)}\,dt$.
For the nonincreasing function $y(t)=B(t)^{-1/2}$, the existing
opposite-monotonicity integral comparison gives

$$
\int_{t_0}^{t_m}ty(t)\,dt
\le\frac{t_0+t_m}{2}\int_{t_0}^{t_m}y(t)\,dt.
$$

It follows, without any clock localization or bounded-credit premise,
that

$$
\boxed{
\mathfrak B_{X,H}
\le\mathfrak B_X^{\rm all}
\le c_{\rm win}\mathsf L_X
-t_mS_m\lambda(A_m)-\mathsf C_X,
\qquad
\mathsf C_X=\int_{t_0}^{t_m}tS(t)k(A(t))\,dt\ge0.}
\tag{BV3}
$$

The coefficient is at most $4/3$ because the original window has
$t_m\le2\ell_X\le2t_0$. Its arithmetic attainability or sharpness
on actual source windows is not asserted. The two debit terms are
independently nonnegative and explicitly retained.

### Consume the bound before splitting the high-clock baseline

Use PE2 and DR1--DR4 directly with BV1, before the auxiliary $H_X$
cut, and the unchanged paid FH1 remote tail. Every future complete-gap
residual vanishes by DR1, the future selected visits cost at most
$\widetilde\gamma_XV_X^K+4L_X$, and the interior $Q$ costs $O(L_X)$.
Thus the existing original-head transfer gives

$$
\frac{Z_X^{\rm right}(T_X)}{M_XL_X}
\le
\frac{c_{\rm win}\mathsf L_X+\mathfrak T_X
-t_mS_m\lambda(A_m)-\mathsf C_X}{M_XL_X}
-(a-\epsilon-\widetilde\gamma_X)
 \frac{V_X^K}{M_XL_X}
+O_\epsilon(M_X^{-1})+o(1),
\quad \widetilde\gamma_X=\frac{800}{9}\rho_X.
\tag{BV4}
$$

No high-clock part is dropped: the entire baseline was bounded at
once in BV3, so BV4 does not add BL6's separate high-clock allowance.
Keep the full original horizon, even when $\mathsf U_X$ is
superpolynomial. The terminal debit combines with DR3 exactly as

$$
\mathfrak T_X-t_mS_m\lambda(A_m)
=S_m\int_{A_m}^{\mathsf U_X}[E(w)-t_m]k(w)\,dw
-t_mS_m\lambda(\mathsf U_X).
\tag{BV5}
$$

Both the complete exterior and its finite terminal remainder remain.
No sign is imposed on the anchored exterior in BV5, and no boundedness
hypothesis is imposed on $\mathsf L_X/(M_XL_X)$. In particular,
$\mathsf L_X$ is not silently replaced by $V_X^K$.
The exact correction $\widetilde\gamma_XV_X^K/(M_XL_X)$ is retained.

BV3 bounds a retained cost by a known source readout and terminal
debits, while BV4--BV5 locate the remaining same-source arithmetic
comparison. To contradict the existing JM4 or applicable JM7 lower
margin, their complete normalized signed upper still has to lie below
$R_0-\delta$ or $R_\eta-\delta$ for a fixed $\delta>0$ on the same
common cofinal original-window sequence. This strict comparison,
all-integer Robin inequality and RH remain unproved.

## An inventory lower count pays part of the lag without a clock ceiling

Keep BV1--BV5's original full windows, every maximizing tie and the same
common cofinal source, including $\Theta=1$. Reuse LO1 with
$b_0=9/100$ and $\vartheta=21/40$, and retain
$\rho_X=\sup_t t/B(t)\to0$. This is a `repo-derived` paper
application of the existing count and an elementary scalar optimization,
not a new prime theorem, generic inequality or Lean/kernel result.
No upper bound on $B$, $\mathsf L_X/(M_XL_X)$ or
$V_X^K/(M_XL_X)$ is imposed.

### Optimize the existing incomplete-block allowance before integrating

At the actual selected real clock, PG1 gives $A=B+t$, $K(A)=B$ and
$\Delta(A)=K(A)-K(K(A))=B-K(B)\ge0$. LO1 gives

$$
t-\frac{\Delta(A)}{b_0}
\le\min\{t,1+A^\vartheta\}.
$$

For positive $t,c$ and $\vartheta>1/2$, splitting at
$b=(t/c)^{1/\vartheta}$ gives the elementary identity

$$
\sup_{b>0}\frac{\min\{t,cb^\vartheta\}}{\sqrt b}
=c^{1/(2\vartheta)}t^{1-1/(2\vartheta)}.
$$

Use $A\le(1+\rho_X)B$ and
$\min\{t,1+u\}\le1+\min\{t,u\}$. Since
$1-1/(2\vartheta)=1/21$, the actual source therefore satisfies

$$
\frac{t-\Delta(A)/b_0}{\sqrt B}
\le\frac1{\sqrt B}+\sqrt{1+\rho_X}\,t^{1/21}.
\tag{LC1}
$$

Define the nonnegative explicit allowance

$$
\mathsf E_X^{\rm lag}
=\sqrt{1+\rho_X}\,\frac{21}{22}
 (t_m^{22/21}-t_0^{22/21})
+\int_{t_0}^{t_m}\frac{dt}{\sqrt{B(t)}}.
$$

The existing exact occupation identity for the visited set $D$ gives
$V_X^K=\int_{t_0}^{t_m}\Delta(A(t))/\sqrt{B(t)}\,dt$.
Integrating LC1 yields the ceiling-free, one-sided comparison

$$
\boxed{V_X^K\ge b_0
 (\mathsf L_X-\mathsf E_X^{\rm lag}).}
\tag{LC2}
$$

All higher and simultaneous layers remain in LO1's complete inventory.
The estimate applies to every selected branch; finite tie values do not
alter its occupation integrals. It neither identifies $V_X^K$ with
$\mathsf L_X$ nor supplies a two-sided asymptotic.

### Spend only the retained fraction of the same compensation

Fix $0<\epsilon<a$ and enlarge the common start until
$h_X=a-\epsilon-\widetilde\gamma_X>0$, with BV4's unchanged
$\widetilde\gamma_X=(800/9)\rho_X$. Keep BV5's whole anchored exterior

$$
\mathsf T_X^\circ
=S_m\int_{A_m}^{\mathsf U_X}[E(w)-t_m]k(w)\,dw
-t_mS_m\lambda(\mathsf U_X).
$$

Let $\mathcal R_X$ denote BV4--BV5's normalized upper expression
$(c_{\rm win}\mathsf L_X+\mathsf T_X^\circ-\mathsf C_X-h_XV_X^K)
/(M_XL_X)$, before its already retained $O_\epsilon(M_X^{-1})+o(1)$.
For every $z\in[0,1]$, spend the fraction $z$ of the same credit in
LC2, leaving the rest unchanged. This gives

$$
\boxed{
\mathcal R_X\le
\frac{(c_{\rm win}-zb_0h_X)\mathsf L_X
 +\mathsf T_X^\circ-\mathsf C_X-(1-z)h_XV_X^K}{M_XL_X}
+\frac{zb_0h_X\mathsf E_X^{\rm lag}}{M_XL_X}.}
\tag{LC3}
$$

Thus the paid lag coefficient is exactly $zb_0h_X$, with the displayed
error. The $\widetilde\gamma_X$ correction has not been discarded;
without a bounded normalized credit it cannot be replaced by zero.
No part of the exterior, terminal debit or remaining credit is omitted.

### The original scale determines when this allowance is negligible

The source floor, $t_m\le2\ell_X=(d/4)M_X\sqrt X$, and the uniform
$B_{\min,X}\to\infty$ give

$$
\boxed{
\frac{\mathsf E_X^{\rm lag}}{M_XL_X}
\ll X^{(40\eta-19)/42}(\log X)^{-20/21}
 +o(M_X^{-1}).}
\tag{LC4}
$$

Indeed the first integral is at most
$\sqrt{1+\rho_X}\,L_Xt_m^{1/21}$, while the second is at most
$L_X/\sqrt{B_{\min,X}}$. Substitute the original
$M_X=X^{1/2-\eta}\log X$ in $t_m^{1/21}/M_X$.
Consequently the LC3 payment has $o(1)$ normalized error whenever
$\eta\le19/40$, including equality and including $\Theta=1$.
LC1--LC4 themselves retain every original $\eta<1/2$; above $19/40$
the explicit allowance remains and is not declared negligible.

This pays a quantitative fraction of BV4's lag by its actual
second-iterate credit, without the global SI1 clock ceiling. The
remaining lag coefficient is still positive, and the anchored exterior
still has no supplied sign. The complete strict comparison below
$R_0-\delta$ or the applicable $R_\eta-\delta$, all-integer Robin
inequality and RH remain unproved. No literature-originality claim or
new generic formal declaration is made.

## Two sieve substitutions leave the finite prime test unpaid

Retain FH1--FH4's literal weight, complete common horizon, all original
full windows and every maximizing tie, including $\Theta=1$. The
following are applications of published sieve hypotheses to that same
weight. They neither reprove a sieve theorem nor establish FH4, a
bilinear bound or RH. Write $U=\mathsf U_X$, $W=\mathsf W_X$, and put

$$
b=\min_tB(t),\qquad C=\max_tB(t),\qquad
\Omega=\int_{t_0}^{t_m}B(t)^{-1/2}dt,\qquad
S=\int_{t_0}^{t_m}\sqrt{B(t)}\log B(t)dt.
$$

The extrema may be enlarged over the original endpoint ties. The source
already gives $b/\ell_X\to\infty$ and $\log C/\log U\to0$.
Use MR1's existing variation and MR2's unchanged reference on $[0,U]$:
$\operatorname{TV}(W)\le(1+a)\Omega$,
$0\le W\le\Omega$ and $\int_0^UW=\mathsf P_X$.
The constant extension down to zero retains the actual low-clock
plateau. Classical bounded-variation rectangle quadrature then has
error $O_a(\Omega)$ on every free divisor lattice and its interval
restrictions. This is the existing free-integer interface; it is not
an estimate for an arithmetic coefficient in the inner sum.

### The whole-horizon growth hypothesis fails

John Friedlander and Henryk Iwaniec, *Asymptotic sieve for primes*,
Annals of Mathematics 148 (1998), 1041--1065,
[arXiv:math/9811186v1](https://arxiv.org/pdf/math/9811186v1),
version 1 November 1998, Theorem 2 on PDF p.19, explicitly assumes
(1.4) on PDF p.1. With its notation replaced by $\mathcal A$, that
condition is

$$
\mathcal A(x)\gg\mathcal A(\sqrt x)(\log x)^2,
\qquad \mathcal A(y)=\sum_{n\le y}a_n.
$$

Consider the direct substitution $x=U$, $a_n=W(n)$ for $1\le n\le U$,
and zero otherwise. Including $n=1$ changes no von Mangoldt sum.
Quadrature and FH3's continuum reference give
$\mathcal A(U)=\mathsf P_X+O_a(\Omega)$. Moreover

$$
\frac{\mathsf P_X}{S}
\ge\log\frac{\log U}{\log C}-\frac1{\log U}\longrightarrow\infty,
\qquad
\frac{\Omega}{S}\le\frac1{b\log b}\longrightarrow0.
$$

Indeed the omitted term in the first inequality is
$(1-a)\int\sqrt B\,dt/S\ge0$. Eventually $C<\sqrt U$, so on
$[\sqrt U,U]$ the exact weight is $S[\lambda(r)-\lambda(U)]$.
Consequently

$$
\begin{aligned}
\mathcal A(U)-\mathcal A(\sqrt U)
&=S\left[\log2-\frac{1-U^{-1/2}}{\log U}\right]+O_a(\Omega),\\
\frac{\mathcal A(\sqrt U)}{\mathcal A(U)}&\longrightarrow1.
\end{aligned}
$$

Thus no uniform positive constant makes (1.4) hold along this
whole-horizon substitution. This rules out that direct application,
not all uses of the asymptotic sieve. Localizing the weight to separate
blocks can change the growth ratio; the theorem's distribution,
coefficient-size and bilinear hypotheses, its absolute $M_XL_X$ error
and any required uniformity over the moving family would still need
proof. Neither this source's analytic proof nor its other hypotheses
are certified here.

### The paid divisor level gives no positive linear lower main term

D. R. Heath-Brown, *Lectures on Sieves*,
[arXiv:math/0209360v1](https://arxiv.org/pdf/math/0209360v1),
version 25 September 2002, Corollary 5.1 on PDF p.36, records the
Rosser--Iwaniec dimension-one lower sieve. In its notation
$s=\log y/\log z$, and PDF p.27 defines $f(s)=0$ for $0<s\le2$.
The corollary retains both the sieve asymptotic error and the sum of
divisor remainders. The original Iwaniec theorem is cited through
these authored lectures, without a new proof or Lean verification.
Its pointwise sieve-weight inequalities extend to the nonnegative real
weights $W(n)$ by finite linearity. For $\omega(p)=1$, the classical
Mertens estimate
$\sum_{w\le p<z}(\log p)/p=\log(z/w)+O(1)$ supplies the stated
dimension-one density hypothesis.

For example, the existing free-lattice variation bound pays the level

$$
D=\left\lfloor\frac{M_X\sqrt b}{(\log U)^2}\right\rfloor,
\qquad
\sum_{d<D}|r_d|\ll_a D\Omega
\ll_a\frac{M_XL_X}{(\log U)^2}=o(M_XL_X)
$$

for the divisor remainders of $W$ restricted to any interval
$(R,2R]\cap[1,U]$. Its continuum main term is the integral of that
same restricted weight divided by $d$; the local density is $1/d$.
This only reuses the elementary free-integer payment. Since
$\log U=(\log X)^{O(1)}$ and

$$
\frac{\ell_X}{M_X^2}
=\frac d8\frac{X^\eta}{\log X}\longrightarrow\infty,
$$

one has $D\to\infty$ and $D/b\to0$ on the original fixed-parameter
source. Here $d$ in $\ell_X$ is the original source constant, distinct
from the divisor index in the preceding sum.

For $R\ge b$, take $y=D$ and $z=\sqrt{2R}+1$ in the lower sieve.
Every surviving integer in the restricted interval is prime. The
strict inequality $z>\sqrt{2R}$ matters because the source sieves by
$p<z$; equality could leave the endpoint square when $\sqrt{2R}$ is
prime. Nevertheless

$$
0<s=\frac{\log D}{\log z}<2,
\qquad f(s)=0
$$

at this paid level. Hence the corollary has no positive lower main
coefficient here. The weighted prime sum is not asserted to vanish,
and neither its sieve asymptotic error nor a composite-removal cost
at a smaller $z$ has been paid by this observation. For the exact
prime-log weight $W(n)\log n$, the interval-restricted variation is
$O_a(\Omega\log U)$. On each individual restricted block, the same $D$
therefore pays its divisor remainder by
$O_a(M_XL_X/\log U)=o(M_XL_X)$; $s$ and its zero lower main coefficient
are unchanged. No $o(M_XL_X)$ sum of these per-block allowances over the
full horizon is claimed. FP1--FP5's separate higher-prime-power payment
is unchanged. Stronger divisor information or a different arithmetic
argument is not excluded.

These two parameter correspondences locate missing hypotheses for
the actual FH test. They supply no replacement for the unchanged
same-source signed comparison, BV/LC account or strict margin. The
finite prime lower bound and RH remain unproved; no literature
originality or kernel verification is claimed.

## Stronger published counts increase the ceiling-free lag payment

Retain BV4--BV5 and LC1--LC4's original source, complete horizon,
all full windows and every maximizing tie. The count-to-inventory
transfer below reuses LS6a's BHP lower envelope and SI2's admitted
blocks; the scalar optimization and fractional-credit rule are
exactly those already used in LC. The added consumer is a larger
lag payment in the same upper account, rather than JM7's localized
lower-margin calculation. This is a paper application of published
results, without a new prime theorem, originality claim or Lean
verification.

### Retain the incomplete block until after scalar optimization

Fix a lower coefficient $b_*>0$ and a block exponent
$1/2<\vartheta<99/100$ admitted by one of these existing suppliers:

| Published input | Fixed lower coefficient | Strict exponent condition |
|---|---|---|
| [BHP 1997, Theorem 3(I), $q=1$](../Scale/bakerharmanpintz1997goldbach.md) | $b_*<0.99$ | $\vartheta>11/20$ |
| [Guth--Maynard, Corollary 1.3, arXiv:2405.20552v2](../Analytic/guthmaynard2024largevalues.md#the-short-interval-input) | $b_*<1$ | $\vartheta>17/30$ |

The BHP statement requires one fixed sufficiently small positive
$\varepsilon$. Choose it with $11/20+\varepsilon\le\vartheta$;
blocks of length $x^\vartheta$ then satisfy its lower length bound
and eventually its upper bound $x/\log x$. For Guth--Maynard take
fixed $\varepsilon=\vartheta-17/30>0$ and forward block length
$(2B)^\vartheta$. Its centres lie in $[B,2B]$, so this length is
between the required $x^\vartheta$ and $x^{99/100}$ eventually.
No upper restriction on the complete lag $t$ by either block-length
ceiling is imposed.

At any original selected real branch, retain only primes in
$(B,A-1]$, where $A=B+t$. Their first-layer activation clocks obey
$B<p<a_{p,1}<p+1\le A$, so all their $\log p$ masses belong to
$\Delta(A)=K(A)-K(B)$. Strict endpoints and simultaneous higher
layers are preserved; every higher-layer contribution is nonnegative.
Complete backward BHP blocks, or forward Guth--Maynard blocks, cover
this prime interval except for length $O(B^\vartheta)+O(1)$.
All centres are $B(1+o_X(1))$. Each prime keeps its own logarithmic
weight, and the fixed slack below $0.99$ or $1$ pays the conversion
from the published count. The shorter-than-one-block case is covered
by $\Delta(A)\ge0$. Thus one fixed $c=c_{\vartheta,b_*}\ge1$ and
one common start give, on every original branch and tie,

$$
\Delta(A)\ge b_*[t-c(1+B^\vartheta)].
\tag{LC5}
$$

The constant and start can depend on the fixed supplier parameters;
they do not depend on an individual core or its size relative to $X$.
No $\Theta<1$ premise or global core-clock ceiling enters LC5.

Combine LC5 with $\Delta(A)\ge0$ before using LC1's scalar identity.
With $p_\vartheta=1-1/(2\vartheta)>0$, it gives

$$
\frac{t-\Delta(A)/b_*}{\sqrt B}
\le\frac{c}{\sqrt B}+c^{1/(2\vartheta)}t^{p_\vartheta}.
$$

Define the nonnegative allowance

$$
\mathsf E_X^{\vartheta,b_*}
=\frac{c^{1/(2\vartheta)}}{1+p_\vartheta}
 (t_m^{1+p_\vartheta}-t_0^{1+p_\vartheta})
+c\int_{t_0}^{t_m}\frac{dt}{\sqrt{B(t)}}.
$$

The same exact occupation identity used in LC2 yields

$$
\boxed{V_X^K\ge
 b_*[\mathsf L_X-\mathsf E_X^{\vartheta,b_*}].}
\tag{LC6}
$$

This is an additive allowance. It does not replace an uncontrolled
$o(1)\mathsf L_X$ or assume that $V_X^K/(M_XL_X)$ is bounded.

### The original scale pays the allowance on stricter parameter ranges

Substitute the unchanged $t_m\le(d/4)M_X\sqrt X$ and
$M_X=X^{1/2-\eta}\log X$ into the preceding allowance. Uniform
$B_{\min,X}\to\infty$ gives

$$
\boxed{
\frac{\mathsf E_X^{\vartheta,b_*}}{M_XL_X}
\ll_{\vartheta,b_*,d}
 X^{1/2-(1-\eta)/(2\vartheta)}
 (\log X)^{-1/(2\vartheta)}+o(M_X^{-1}).}
\tag{LC7}
$$

Consequently the allowance is $o(1)$ when the fixed exponent satisfies
$\vartheta\le1-\eta$, including equality by the negative logarithmic
power. Choose the fixed precision and exponent before taking the common
source start. The available payments are:

| Original supplied $\eta$ | Admissible fixed lower coefficient |
|---|---|
| $\eta<13/30$ | Any $0<b_*<1$ |
| $13/30\le\eta<9/20$ | Any $0<b_*<0.99$ |
| $9/20\le\eta\le19/40$ | LC1--LC4's existing $b_0=9/100$ |

Every row retains the original $1-\Theta<\eta<1/2$, including
$\Theta=1$ where allowed. The first two rows use only that same
supplied $\eta$; they do not reselect an oscillation exponent.
Neither $\eta=13/30$ in the Guth--Maynard branch nor $\eta=9/20$
in the BHP 1997 branch passes its strict supplier cut. Coefficient
$b_*=1$, coefficient $b_*=0.99$ in the BHP branch, a moving
precision $b_*(X)$ and a numerical common start are not asserted.
For $\eta>19/40$ the existing explicit allowances remain available
but are not declared negligible.

### Spend the stronger coefficient in the unchanged upper account

Keep LC3's $h_X=a-\epsilon-(800/9)\rho_X>0$ and its complete
$\mathsf T_X^\circ$, $\mathsf C_X$ and $\mathcal R_X$.
For every fixed $z\in[0,1]$, apply LC6 to only the $z$ fraction of
the same inventory credit. This gives

$$
\boxed{
\mathcal R_X\le
\frac{(c_{\rm win}-zb_*h_X)\mathsf L_X
 +\mathsf T_X^\circ-\mathsf C_X-(1-z)h_XV_X^K}{M_XL_X}
+\frac{zb_*h_X\mathsf E_X^{\vartheta,b_*}}{M_XL_X}.}
\tag{LC8}
$$

On the first two table ranges, the paid lag coefficient is therefore
exactly $zb_*h_X$, with an $o(1)$ additive error from LC7. The
$\rho_XV_X^K$ correction remains inside $h_X$; the unspent credit
is still $(1-z)h_XV_X^K$. No credit is counted twice.

Since $c_{\rm win}>1$, $b_*<1$ and $h_X<a<5/8$, the remaining
lag coefficient stays greater than $1-a>0$. The full anchored
exterior, its finite terminal remainder and the rest of the original
joint comparison remain. A larger paid coefficient does not establish
the strict upper bound below the same-source JM margin, all-integer
Robin inequality or RH.

### A separately qualified preprint count branch

The [adopted-supplier note](../Scale/bakerharmanpintz2001primegaps.md#a-newer-preprint-statement-and-the-adopted-supplier)
already records Runbo Li's versioned preprint and the absence of an
independent audit of its numerical sieve proof and integral certificates.
If the lower counts in [arXiv:2308.04458v8, Theorem 2, printed p.2](https://arxiv.org/pdf/2308.04458v8)
are taken as premises, the same LC5--LC8 consumer has the following
additional parameter branches. These are supplier-relative consequences;
they do not replace the established BHP/Guth--Maynard inputs above or
certify the preprint's proof.

| Fixed preprint parameter $s$ | Displayed lower constant $LB(s)>$ | Conservative fixed $b_*$ | Original supplied $\eta$ |
|---|---|---|---|
| $0.525$ | $0.249$ | $0<b_*<0.249$ | $\eta<0.475$ |
| $0.524$ | $0.209$ | $0<b_*<0.209$ | $\eta<0.476$ |
| $0.523$ | $0.169$ | $0<b_*<0.169$ | $\eta<0.477$ |
| $0.522$ | $0.134$ | $0<b_*<0.134$ | $\eta<0.478$ |
| $0.521$ | $0.075$ | $0<b_*<0.075$ | $\eta<0.479$ |
| $0.520$ | $0.004$ | $0<b_*<0.004$ | $\eta<0.480$ |

The source supplies counts at exponent $\vartheta=s+\delta$ for
fixed sufficiently small $\delta>0$, at sufficiently large integer
centres. First fix a table row and $b_*$, then choose such a fixed
$\delta$ with $s+\delta\le1-\eta$. This is possible in the displayed
strict $\eta$ range; no exact exponent $s$ is substituted into
Theorem 2.

Here the integer-centre restriction can be handled without assuming a
new all-real count. Start at $n_0=\lfloor A-1\rfloor$ and use complete
backward blocks with

$$
n_{j+1}=\lfloor n_j-n_j^\vartheta\rfloor\ge B.
$$

Since primes are integers,
$\pi(n_j-n_j^\vartheta)=\pi(n_{j+1})$. Thus the source counts the
disjoint prime blocks $(n_{j+1},n_j]$ exactly, with no missing or
twice-counted endpoint prime. Their geometric lengths belong to
$[n_j^\vartheta,n_j^\vartheta+1)$. The fixed slack below the displayed
lower constant pays both this length rounding and the conversion to
each prime's own $\log p$ mass: uniformly over these blocks,
$\log(n_j-n_j^\vartheta)/\log n_j\to1$ and
$n_j^\vartheta/(n_j-n_{j+1})\to1$.

Discard only the final incomplete block and the less-than-two unit
allowance between $n_0$ and $A$. They cost $O(1+B^\vartheta)$,
because $A/B\to1$. Every retained prime still obeys
$B<p<a_{p,1}<p+1\le A$. If no block fits, use $\Delta(A)\ge0$.
Consequently LC5 holds with one fixed enlarged $c$ on every original
branch and tie, and LC6--LC8 apply unchanged. LC7 makes its allowance
$o(1)$ in each displayed range, without a core-clock ceiling or a
bounded normalized lag or credit.

Under this separately stated supplier premise, choosing
$9/100<b_*<0.249$ in the first row increases the payment on
$9/20\le\eta<19/40$, while the remaining rows
provide positive payments beyond $19/40$ up to the strict cut
$\eta<12/25$. The original $1-\Theta<\eta<1/2$ remains, including
$\Theta=1$ where allowed. The established stronger counts already
dominate these coefficients on their shorter ranges. All exterior and
unspent-credit terms in LC8 remain, so neither this conditional branch
nor the preprint count alone supplies the missing strict signed bound
or a proof of RH.

## Local pole cancellation exceeds the small absolute-norm allowance

Retain WT1--WT3 and MR5's actual smoothed test, original full windows
and every maximizing tie. Set $F_X(x)=\widetilde f_X(e^x)$ and use
$\widehat F_X(z)=\int_{\mathbb R}F_X(x)e^{-izx}dx$. This is the same
real even compact smooth test as MT5, which gives

$$
\widehat F_X(i/2)=\widehat F_X(-i/2)
=\frac{\mathsf P_X^{\rm Weil}}2,\qquad
\mathsf P_X^{\rm Weil}=\mathsf P_X
+O_\chi\!\left(L_X\frac{\log b_X}{\sqrt{b_X}}\right),
$$

where $b_X=\min_t\mathcal B_X(t)$. Fix $0<r_*<\log2$, and let
$c_X\in L^1(\mathbb R)$ be real and even, supported in $[-r_*,r_*]$.
It changes no prime-power evaluation of $F_X$. For either
$\epsilon\in\{1,-1\}$, suppose $H_X=\epsilon F_X+c_X$ satisfies
$\widehat H_X(i/2)=\widehat H_X(-i/2)=0$. Evenness then gives

$$
\int_{\mathbb R}c_X(x)\cosh(x/2)dx
=-\epsilon\frac{\mathsf P_X^{\rm Weil}}2,\qquad
\boxed{\|c_X\|_1\ge
\frac{\mathsf P_X^{\rm Weil}}{2\cosh(r_*/2)}.}
\tag{WT4}
$$

The inequality is the usual bounded-weight integral estimate; no new
generic norm theorem is asserted. Its actual-source scale follows
without redoing the continuum account. The
[whole-horizon growth comparison](#the-whole-horizon-growth-hypothesis-fails)
already supplies $\mathsf P_X/S_X\to\infty$ for
$S_X=\int_{t_0}^{t_m}\sqrt{B(t)}\log B(t)dt$.
Since $S_X\ge L_X\sqrt{b_X}\log b_X$, the displayed MT5 error is
negligible relative to $\mathsf P_X$. Reuse CR17's
$b_X/\ell_X\to\infty$ and the original scales:

$$
\frac{\sqrt{\ell_X}}{M_X}
=\sqrt{\frac d8}\,
\frac{X^{\eta/2}}{\sqrt{\log X}}\longrightarrow\infty,
\qquad
\boxed{\frac{\|c_X\|_1}{M_XL_X}\longrightarrow\infty.}
\tag{WT5}
$$

Here the unchanged $1-\Theta<\eta<1/2$ and $\Theta\le1$ imply
$\eta>0$, including $\Theta=1$. No upper bound on $b_X/X$ or
bounded normalized lag is used.

Thus a prime-free local correction cannot both cancel these pole
moments and satisfy the sufficient absolute allowance
$\|c_X\|_1=o(M_XL_X)$. For general corrections this does not force a large full signed
pole-minus-archimedean contribution: cancellation between large terms
remains outside this absolute-norm estimate. An integrable
correction suffices for WT4; an explicit-formula application still
requires its own smoothness and domain conditions.

In the [adopted Connes--Consani theorem](../Weil/connesconsani2021archimedean.md),
the vanishing condition is on the factor $g$. If $H=g*g^*$ and
$\widehat g(-i/2)=0$, both pole moments of $H$ vanish; their vanishing
alone supplies neither a factor nor positivity. Also a local correction
leaves $\epsilon F_X$ unchanged outside $[-r_*,r_*]$, so its growing
support still violates that theorem's fixed support contract. WT4--WT5
are a paper application boundary, without Lean verification or a new
Robin upper estimate. The required signed comparison and RH remain
unproved.

## A smooth paid completion narrows the signed local-correction boundary

Keep the same MR5 test $F=F_X$, full windows, all endpoint ties and
common horizon $U$ from MT1--MT6. Put
$C=B^{\rm end}_{\max,X}$, $Q=Q_X$, $Y=\mathsf Y_X$, $L=L_X$ and
$D=2+\sqrt C/Q$. The following is an actual-source paper application;
the smooth spectral factorization and small-support spectral floor are
reused from the sources cited below. No generic positivity theorem,
Lean verification or improvement of the original Robin upper is asserted.

### Complete the actual test without losing smoothness

MR1 and MR5 give $\|F\|_\infty+\|F\|_1+\|F'\|_1\ll L$.
For the second derivative, use MT1 with weight $r^{3/2}$ rather than
MT2's $r^2$. Its four terms cost respectively

$$
O_{\rho,a}(\sqrt B/Q),\qquad O_{\rho,a}(1),\qquad
O_{\rho,a}(1),\qquad
s_B\int_B^U O_\rho(v^{3/2}|k'(v)|)dv=O_\rho(1).
$$

The third term is the remote $U$ endpoint; it is retained. The final
bound follows from MT1's displayed $k'$ and $s_B=\sqrt B\log B$,
without a ceiling on $U/B$. In the additive coordinate,

$$
(r\partial_r)^2(\sqrt r\,w)
=\tfrac14\sqrt r\,w+2r^{3/2}w'+r^{5/2}w''.
$$

Integrate with $dx=dr/r$, then against the actual residence. The fixed
MR5 calibration contributes $O_\chi(L)$. Consequently

$$
\|F''\|_1\ll LD,\qquad
|\widehat F(\xi)|\ll
L\min(1,|\xi|^{-1},D|\xi|^{-2})\quad(\xi\ne0).
\tag{WT6}
$$

Fix $0<\tau<\log2$. Choose a fixed nonnegative real even smooth $u$
with sufficiently narrow compact support in $(-\tau/2,\tau/2)$.
For $u^*(x)=\overline{u(-x)}$, put $\psi=u*u^*$. Then $\psi\ge0$,
$\widehat\psi\ge0$, its support is compactly contained in
$(-\tau,\tau)$, and the choice can ensure
$\widehat\psi\ge m>0$ on $[-2,2]$.
Let $I_0=[-2,2]$ and
$I_j=\{\xi:2^j\le|\xi|\le2^{j+1}\}$ for $j\ge1$. Define

$$
a_j=m^{-1}2^j\sup_{\xi\in I_j}|\widehat F(\xi)|,
\qquad c_X(x)=\sum_{j\ge0}a_j\psi(2^jx).
\tag{WT7}
$$

These bands cover the real axis. At each frequency in $I_j$, the
$j$th Fourier summand alone is at least $|\widehat F|$; every other
summand is nonnegative. WT6 gives

$$
a_0\ll L,\qquad a_j\ll L\min(1,D2^{-j})\ (j\ge1),\qquad
\sum_j2^{-j}a_j\ll L,\qquad
\sum_j(1+j)a_j\ll L(1+\log D)^2.
$$

There is no smoothing after taking this majorant. For each fixed $X$,
the actual $F$ is compact smooth, so for every $N$ one also has
$a_j\ll_{X,N}2^{-j(N-1)}$. Taking $N>k+1$ proves uniform convergence
of the $k$th derivative series for every $k$. All supports lie in one
fixed compact subinterval of $(-\tau,\tau)$; hence
$c_X\in C_c^\infty(-\tau,\tau)$ is real, even and nonnegative.
The $L^1$ summability permits Fourier interchange and proves
$\widehat c_X\ge|\widehat F|$. Thus both $c_X-F$ and $c_X+F$ are
positive definite. No change to $F$ or its prime evaluations is needed.

### Pay the full correction, including all complex zeros

For an additive test $H$, use MT5's exact normalization

$$
G_H(s)=\int_{\mathbb R}H(x)e^{(s-1/2)x}dx,\qquad
\mathcal P(H)=G_H(0)+G_H(1)
=\int_{\mathbb R}2\cosh(x/2)H(x)dx,
$$

and $\mathscr W(H)=\mathcal P(H)+\mathcal A(H)-\Pi(H)$, where
$\mathcal A(H)=-\mathcal W_{\mathbb R}(r^{-1/2}H(\log r))$
and $\Pi$ is the complete finite-prime term. This is the full Weil
functional, not the archimedean part alone.
For $\psi_j(x)=\psi(2^jx)$, the full archimedean integral satisfies
$|\mathcal A(\psi_j)|\ll_\tau1+j$: near zero use smooth evenness,
between scales $2^{-j}$ and $1$ integrate the subtraction against
$dx/x$, and retain its exponential tail beyond the support. The same
bound holds for the absolute integral, so the weighted summability
above justifies Fubini, including the $c_X(0)$ subtraction.
Also $|\mathcal P(c_X)|\ll_\tau\|c_X\|_1\ll_\tau L$.

For every nontrivial zero $\varrho=\beta+i\gamma$, two integrations
by parts on the shrinking bump give, uniformly in $0\le\beta\le1$,

$$
|G_{\psi_j}(\varrho)|\ll_\tau
\min(2^{-j},2^j/\gamma^2)\quad(\gamma\ne0).
$$

Use MT3's full multiplicity count and reciprocal-square tail, split at
$\max(4,2^j)$, keeping both ordinate signs and all low zeros. They give
$\sum_\varrho m_\varrho|G_{\psi_j}(\varrho)|\ll_\tau1+j$.
Thus the correction's complete account is

$$
\boxed{
|\mathcal P(c_X)|+|\mathcal A(c_X)|
+\sum_\varrho m_\varrho|G_{c_X}(\varrho)|
\ll_\tau L(1+\log D)^2
\ll_\tau LY^2=o(M_XL_X).}
\tag{WT8}
$$

Its prime term is zero by $\tau<\log2$. Absolute convergence justifies
all correction interchanges. The last two ways of accounting for the
same explicit formula do not create two independent reserves.
The final scale uses only $Q\ge1$, $C\le e^Y$ and the original
$Y^2/M_X\to0$; no bounded clock ratio, changed window or restriction
excluding $\Theta=1$ is introduced.

### A restricted local replacement has a large signed debit

Now fix $\tau$ sufficiently small that the existing
[Suzuki small-window floor](../Weil/frankliebseiringer2006hardy.md#reuse-the-stronger-small-window-spectral-floor)
has $\lambda^W_{\tau/2}>0$, in addition to $\tau<\log2$.
Suppose a real even $c_X^\flat\in C_c^\infty(-\tau,\tau)$ satisfies

$$
c_X^\flat-F_X\text{ is positive definite},\qquad
\widehat{c_X^\flat-F_X}(i/2)
=\widehat{c_X^\flat-F_X}(-i/2)=0.
\tag{WT9}
$$

No existence of such replacements is asserted. Their pole condition
implies $\mathcal P(c_X^\flat)=\mathsf P_X^{\rm Weil}$.
Set $Z=c_X^\flat+c_X$. This is compact smooth with the same small
support, and it is positive definite since it is the sum of
$c_X^\flat-F_X$ and $F_X+c_X$. Reuse the smooth Boas--Kac
factorization in [Connes--Consani, Proposition 3.2, manuscript p.17](../Weil/connesconsani2021archimedean.md):
$Z=v*v^*$ with smooth $v$ supported in $[-\tau/2,\tau/2]$.
The factor may be complex and need not be even; Suzuki's stated domain
covers it. Therefore
$\mathscr W(Z)\ge\lambda^W_{\tau/2}\|v\|_2^2
=\lambda^W_{\tau/2}Z(0)$.

Positive definiteness gives $|Z(x)|\le Z(0)$. Separately, $c_X\ge0$
gives $\mathcal P(Z)\ge\mathsf P_X^{\rm Weil}$. Together,

$$
\mathsf P_X^{\rm Weil}\le\mathcal P(Z)
\le8\sinh(\tau/2)Z(0),\qquad
\boxed{\mathscr W(c_X^\flat)\ge
\frac{\lambda^W_{\tau/2}}{8\sinh(\tau/2)}
\mathsf P_X^{\rm Weil}-O_\tau(L_XY^2).}
\tag{WT10}
$$

WT4--WT5's actual-source comparison gives
$\mathsf P_X^{\rm Weil}/(M_XL_X)\to\infty$. Consequently WT10
forces $\mathscr W(c_X^\flat)/(M_XL_X)\to+\infty$ along any cofinal
family satisfying WT9. Unlike the absolute-norm obstruction, this
excludes even a signed $O(M_XL_X)$ upper allowance for this restricted
class. The argument uses WT9's upper-oriented positive-definite
comparison and vanishing pole moments; arbitrary local corrections and
wider supports are not covered.

WT7--WT8 do not supply those vanishing moments: their pole mass is
only $O_\tau(L_X)$, whereas the actual test's pole mass is larger than
$M_XL_X$. Moreover, $c_X-F_X$ retains the original growing support.
Real-axis Fourier order does not determine the sign of the full Weil
functional at the complex zero arguments. The missing same-source
signed comparison on this growing-support test, and hence the original
strict Robin upper and RH, remain unproved. This continuation retains
an application of existing source results, not a literature-priority
claim or a new formalized theorem.

## A remote completion cancels the actual poles at small signed cost

Keep WT6--WT8's actual $F_X$, $c_X$ and $H_X=c_X-F_X$, with all
original windows, maximizing ties, layers and common horizon. This
application reuses the complete explicit formula and the
[Johnston--Yang cumulative prime-power error](../Weil/johnstonyang2022pnt.md).
The autocorrelation construction and the all-support constrained Weil
criterion in [Connes--Consani, Appendix C, Proposition C.1](../Weil/connesconsani2021archimedean.md#vanishing-constraints-and-the-remaining-semilocal-comparison)
are existing tools. The additional interface here is an explicit
pole-null completion of this same test, with its support and signed
cost paid on the original scales. No generic criterion, literature
priority or Lean verification is asserted.

### Add positive-definite mass far beyond the original support

Write $A_X=\log\mathsf V_X$ for MR5's original additive support
ceiling for $F_X$; FH1 gives $A_X=O((\log X)^4)$. To distinguish that width from
the pole deficit, put

$$
N_X=-\mathcal P(H_X)
=\mathsf P_X^{\rm Weil}-\mathcal P(c_X)>0.
$$

The inequality holds cofinally: WT4--WT5 give
$\mathsf P_X^{\rm Weil}/(M_XL_X)\to\infty$, whereas WT8 gives
$\mathcal P(c_X)=O_\tau(L_X)$ and $M_X\to\infty$.
The support bound and WT6--WT8's $L^1$ estimate also give
$N_X\ll_\tau L_Xe^{A_X/2}$.
Use the same fixed nonzero even nonnegative autocorrelation $\psi$
as WT7. For $R>A_X+2\tau+\log2$, define

$$
q_R(x)=2\psi(x)+\psi(x-R)+\psi(x+R),\qquad
\widehat q_R(\xi)=2(1+\cos R\xi)\widehat\psi(\xi)\ge0.
$$

This is the usual autocorrelation identity applied to
$u+u(\cdot-R)$, not a new positivity theorem.
Evenness gives the exact moment and completion

$$
\mathcal P(q_R)=2(1+\cosh(R/2))\mathcal P(\psi),\qquad
e_X=\varepsilon_Xq_{R_X},\qquad
\varepsilon_X=\frac{N_X}{\mathcal P(q_{R_X})}>0,
\qquad H_X'=H_X+e_X.
\tag{WT11}
$$

Thus $H_X'$ remains real, even, compact smooth and positive definite.
Since $\mathcal P(H_X')=0$ and it is even, both individual pole
moments $G_{H_X'}(0)$ and $G_{H_X'}(1)$ vanish. Also
$c_X'=c_X+e_X$ still satisfies $\widehat c_X'\ge|\widehat F_X|$.
The auxiliary completion is supported in
$[-R_X-\tau,R_X+\tau]$; the original $F_X$ and its arithmetic
evaluations have not changed.

### Retain every remote prime power in the signed account

For $R>\tau+\log2$, the central bump has no prime-power term and
the negative translated bump does not meet $\log n$ for $n\ge2$.
Consequently the complete prime term is

$$
\Pi(q_R)=2\sum_{n\ge2}\Lambda(n)n^{-1/2}\psi(\log n-R).
$$

Set
$\eta_\tau(R)=\sup_{|v-R|\le\tau}9.39v^{1.515}
e^{-0.8274\sqrt v}$, with $R-\tau\ge\log2$.
Apply the cited cumulative bound for $\Psi(t)-t$ to the compact
weight $w_R(t)=2t^{-1/2}\psi(\log t-R)$. Its endpoint terms vanish
and
$w_R'(t)=2t^{-3/2}[\psi'(\log t-R)-\psi(\log t-R)/2]$.
Stieltjes integration therefore gives

$$
\Pi(q_R)=e^{R/2}\mathcal P(\psi)
+O_\psi(e^{R/2}\eta_\tau(R)).
$$

Here the main term is exactly $\int w_R(t)dt$, using evenness of
$\psi$. The sum includes all prime powers in the added band
$|\log n-R|<\tau$; it is not replaced by a prime-free correction.
The full Gamma convention in MT5 gives for the translated pair

$$
\mathcal A\bigl(\psi(\cdot-R)+\psi(\cdot+R)\bigr)
=-2\int_0^\infty
\frac{e^{-x/2}\psi(x-R)}{1-e^{-2x}}\,dx
=O_\psi(e^{-R/2}).
$$

Its value at zero is zero, so it has no Gamma subtraction term.
The central term retains its whole contribution $2\mathcal A(\psi)$,
including the subtraction outside the support. Since
$\mathcal P(q_R)=(2+e^{R/2}+e^{-R/2})\mathcal P(\psi)$,
the same test's pole and prime main terms cancel. Thus

$$
|\mathscr W(q_R)|\ll_\psi1+e^{R/2}\eta_\tau(R),\qquad
\boxed{|\mathscr W(e_X)|\ll_\psi
N_X\bigl(e^{-R_X/2}+\eta_\tau(R_X)\bigr).}
\tag{WT12}
$$

This pays the full signed functional, not the sum of the absolute
pole and prime contributions. Indeed $\mathcal P(e_X)=N_X$ and
$\Pi(e_X)=N_X+O_\psi(N_X[e^{-R_X/2}+\eta_\tau(R_X)])$ are both
large on the original scale. No absolute complex-zero-sum estimate
for $e_X$ is inferred.

### Choose a sufficient radius and transfer the original target

Take $Z_X=1+A_X+\log X$ and one fixed $K$ with
$0.8274\sqrt K>3$. Put $R_X=KZ_X^2$. It eventually satisfies the
separation required above, and the polynomial factor in
$\eta_\tau(R_X)$ is absorbed by the strict exponential slack:

$$
\eta_\tau(R_X)=O_\tau(e^{-3Z_X}),\qquad
N_X(e^{-R_X/2}+\eta_\tau(R_X))=o(L_X),\qquad
R_X=O((\log X)^8).
\tag{WT13}
$$

This uses the already owned square-root-logarithm PNT error; a sharper
PNT supplier is unnecessary for this payment. For each fixed $k$,
$\|e_X^{(k)}\|_1\le4\varepsilon_X\|\psi^{(k)}\|_1$ and
$\varepsilon_X\ll_\psi N_Xe^{-R_X/2}$, so its small ordinary norms
do not express the large exponentially weighted pole mass.
Linearity and WT8 now give

$$
\mathscr W(H_X')=\mathscr W(H_X)+o(L_X),\qquad
\mathscr W(c_X')=O_\tau(L_XY_X^2)=o(M_XL_X).
\tag{WT14}
$$

A lower bound for $\mathscr W(H_X')$ with a fixed strict margin on
the original $M_XL_X$ scale would therefore transfer to $H_X$ with
the same margin and an $o(M_XL_X)$ allowance. This does not reselect
a window, discard a tie or impose a bounded normalized clock, and it
includes $\Theta=1$ on its original parameter range.

WT10's obstruction concerns a fixed small-support replacement, so it
does not apply to this remote completion. Conversely, the added support
does not satisfy the fixed prime-free support contract of the
archimedean positivity theorem. The all-support constrained criterion
still needs its positivity estimate. The added remote prime powers
must also be present in any semilocal comparison. The semilocal note
now supplies a separate bound for the added term,
[\(\operatorname{Tr}(D_{S_X}(h_{e_X})P_{S_X})=o(L_X)\)](../Weil/connesconsanimoscovici2024semilocal.md#the-remote-pole-null-completion-has-a-negligible-semilocal-trace),
using its actual orthogonal projection and the prescribed family
$S_X=\{\infty\}\cup\{p:p\le\mathsf V_X\}$ for the original test's
support scale. This family need not contain every prime through the
remote completion's enlarged support. On the enlarged
all-primes-through-completed-support family, the same added term has
[trace at least a constant times \(N_X/R_X^7\)](../Weil/connesconsanimoscovici2024semilocal.md#the-enlarged-support-family-retains-a-large-remote-trace),
which exceeds $M_XL_X$ along the original qualifying cofinal family.
Its full signed arithmetic cost remains $o(L_X)$, so a negligible
arithmetic--trace transfer fails for this enlarged family and specified
completion. A joint signed comparison using this unmodified Sonin trace
must retain the growing correction together with the added remote
prime powers and original $H_X$ trace. Such a comparison is not excluded
by this lower bound.

The [exact pole-compensated negative cutoff comparison](../Weil/connesconsanimoscovici2024semilocal.md#exact-pole-compensation-pays-the-remote-negative-cutoff-overlap)
gives a separate quantitative payment on the same enlarged place set:
$\widetilde n_{R_X+\sigma}(e_X)=o(L_X)$ and
$\|\mathsf R T_{e_X}\mathsf P\|_{\mathcal S_1}=o(L_X)$.
These are nonnegative operator allowances beyond WT12's signed
arithmetic cost. Consequently the completed test $H_X+e_X$ and
$H_X$ differ by $o(L_X)$ in the entire negative-overlap plus boundary
allowance of that same compensated lower comparison. This uses the
existing pole-compensating unitary and weighted Hankel estimate,
retains WT13's original radius, and is a paper application without
Lean certification. The negative cutoff overlap of $H_X$ itself
remains uncontrolled; the large unmodified positive Sonin trace is
unchanged. The original strict signed upper, Robin and RH remain
unproved.

### The same original test has a paid boundary remainder

For WT7's actual $H_X=c_X-F_X$, reuse the
[complete boundary application](../Weil/connesconsanimoscovici2024semilocal.md#the-original-test-pays-its-complete-boundary-remainder)
of positive-convolution localization, Plancherel and the standard
Hilbert--Schmidt product estimate. It uses the existing
$c_X(0)\ll_\tau L_X\mathsf Y_X^2$ and
$\|F_X\|_\infty\ll L_X$, with the unchanged support ceiling
$A_X=\log\mathsf V_X$. Under the original FH1 choices, including
$\Theta=1$, it gives

$$
\boxed{
\|\mathsf R T_{H_X}\mathsf P\|_{\mathcal S_1}
\ll_\tau(1+A_X)L_X\mathsf Y_X^2
=o(M_XL_X),\qquad
\|\mathsf R T_{H_X+e_X}\mathsf P\|_{\mathcal S_1}
=o(M_XL_X).}
\tag{WT15}
$$

The second estimate also uses (48)'s already paid boundary cost of
$e_X$ in that semilocal application. Thus the source's complete boundary remainder is below the
original budget on the same compensated operator. The positive-minus-negative
bulk remains uncontrolled; this paper application supplies neither
its signed estimate nor the Robin upper or RH. It introduces no new
operator theorem or Lean verification.


## Half-isolated zeros pay an additional part of the original compensated head

Keep the original source windows, every maximizing tie, the fixed compensation $a$,
all outgoing weights $\delta_i>0$ with sum $L_X$, and all original legal heights
$\tau_i\asymp\sqrt{B_i}$. Assume the originally supplied $1/2<\Theta<1$ and
$1-\Theta<\eta<1/2$; neither parameter is reselected. Put
$M=M_X=X^{1/2-\eta}\log X$ and retain the complete original coefficient
$c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho$.
This `repo-derived` paper application uses the
[Maynard--Pratt half-isolated zero count](../Zeros/maynardpratt2023halfisolated.md),
not their finite-vertical-line Hypothesis $\mathcal F$. It adds no general density
theorem, literature-priority claim or Lean certification.

### The actual submultiset and its budget-dependent lower cut

Let $\mathcal H$ be the actual upper-half-plane zeros that are half-isolated in
Definitions 8--9 of [Maynard--Pratt, author v2](https://arxiv.org/pdf/2206.11729v2).
Every occurrence has its actual multiplicity $m_\rho$. For the same original core,
define only a cut inside its existing head:

$$
H_{B,X}=\max\{51,\sqrt B/M^{19/10}\},
\qquad
\mathcal R_X^{\rm hi}
=2\sum_{i<m}\delta_i
\sum_{\substack{\rho\in\mathcal H,\ H_{B_i,X}<\gamma\le\tau_i\\
                 3/5\le\beta\le3/4}}
m_\rho|c_{B_i,a}(\rho)|.
\tag{SIH1}
$$

Then there is a constant depending only on the fixed original suppliers and
parameters such that, at one common source start,

$$
\boxed{\mathcal R_X^{\rm hi}\ll M_X^{39/40}L_X=o(M_XL_X).}
\tag{SIH2}
$$

This is an absolute estimate for the specified submultiset of the original complete
coefficients. It is not a count of all zeros, and its complement is retained.

### Apply the existing count at finitely many fixed real parts

Write $\mu=1/2-\eta>0$ and choose a fixed
$D>\eta/[(1-\Theta)\mu]$. SC2 supplies $B_i\le M^D$ for all original cores
beyond one common start. Corollary 5 of the cited author version gives, for each
fixed $\sigma>1/2$ and every fixed $\epsilon>0$, a dyadic half-isolated count
$O_{\sigma,\epsilon}(T^{2(1-\sigma)+\epsilon})$.
If the count is read without multiplicities, the existing local zero count bounds
each multiplicity by $O(\log T)$; start with $\epsilon/2$ and absorb this factor
into the other $\epsilon/2$. No simplicity hypothesis is used.

Partition $[3/5,3/4]$ into finitely many disjoint half-open bins, closing the final
right endpoint. Let their endpoints be $\sigma_j,\sigma_{j+1}$ and their maximum
width be $\omega$. Fix $\epsilon<1/10$ and $\omega>0$ small enough that
$D(\omega+\epsilon/2)<1/40$. All these choices are independent of $X$, the core,
the tie and the height assignment. The density exponent is less than one at every
left endpoint. The existing dyadic reciprocal-height argument therefore gives,
for every $H\ge51$,

$$
\sum_{\substack{\rho\in\mathcal H,\ \gamma>H\\\beta\ge\sigma_j}}
\frac{m_\rho}{\gamma}
\ll_{\sigma_j,\epsilon}H^{1-2\sigma_j+\epsilon}.
\tag{SIH3}
$$

The constants cover the bounded initial range as well. No estimate uniform over a
moving real-part parameter, or over $\Theta\uparrow1$, is asserted.

DH3's existing full-coefficient bound
$|c_{B,a}(\rho)|\le(a+2)B^{\beta-1/2}/\gamma$ now bounds a bin by
$C B^{\sigma_{j+1}-1/2}H_{B,X}^{1-2\sigma_j+\epsilon}$.
If $H_{B,X}=\sqrt B/M^{19/10}\ge51$, this is at most

$$
C M^{(19/10)(2\sigma_j-1-\epsilon)}
 B^{\sigma_{j+1}-\sigma_j+\epsilon/2}
\le C M^{19/20+D(\omega+\epsilon/2)}
\le C M^{39/40}.
$$

If instead $H_{B,X}=51$, then $B\le51^2M^{19/5}$ and the same bin is at most
$C B^{1/4}\le C M^{19/20}$. Summing the fixed bins and the original positive
weights proves SIH2. Extending the positive sum beyond $\tau_i$ was only an upper
bound; the original individual upper masks and full subtraction remain unchanged.

### Relation to the previously paid upper slice

The lower endpoint of BH1's auxiliary interval is
$T^0_{B,X}=\sqrt B\,\mathsf Y_X^2/M$, with $\mathsf Y_X\to\infty$.
The original source gives $\sqrt{b_X}/M\to\infty$, where $b_X=\min_i B_i$.
Consequently

$$
\sup_i\frac{H_{B_i,X}}{T^0_{B_i,X}}
\le\frac{51M}{\sqrt{b_X}\,\mathsf Y_X^2}
   +\frac{M^{-9/10}}{\mathsf Y_X^2}\longrightarrow0.
\tag{SIH4}
$$

Thus SIH2 pays the specified half-isolated contribution also between this lower cut
and the already paid auxiliary cuts. $H_{B,X}$ is not declared a CHJ-admissible
height, and no explicit formula is reapplied there.

For comparison of certified power ranges, the allowed fixed parameters
$(\Theta,\eta)=(3/4,7/20)$ have $M=X^{3/20+o(1)}$ and SC2 permits the power
envelope $B=X^{7/5+o(1)}$. At that envelope the SIH1 cut is $X^{83/200+o(1)}$.
At $\beta=3/4$, the Guth--Maynard exponent $g(3/4)=5/9$ would give the existing
all-zero reciprocal-height majorant the power
$7/20-(4/9)(83/200)=149/900>3/20$; that majorant would need a lower cut with
power greater than $9/20$. The half-isolated count has exponent $1/2$ and gives
$7/20-(1/2)(83/200)=57/400<3/20$ before the fixed-bin losses paid above.
This comparison exhibits an additional certified parameter range; it asserts
neither attainment of the clock envelope nor existence of zeros in that cell,
and an unsuccessful upper majorant is not a lower bound on the actual sum.

Deleting exactly SIH1's submultiset changes the original weighted real head by at
most SIH2. All non-half-isolated zeros, real parts outside $[3/5,3/4]$, and the
remaining low frequencies stay in the exact complementary head, with their own
original masks. No reflection closure of $\mathcal H$ is required for this direct
absolute comparison. The full signed head, original joint Robin estimate and RH
remain unproved.

At $\Theta=1$, CP1 gives only $\log B=O((\log X)^2)$ for this argument; the
unspecified $T^{o(1)}$ loss in Corollary 5 cannot be replaced by $M^{o(1)}$ on that
range. SIH2 is not asserted there. Nor does the result supply a sign or a budget
for the complete half-isolated head below $H_{B,X}$.


## An all-scale half-isolated sector is paid also at supremum one

Keep CP1, BH1--BH3 and the original complete coefficients, windows, all ties,
weights and legal upper masks. This application permits the original
$1/2<\Theta\le1$, with its unchanged $1-\Theta<\eta<1/2$.
Write $M=M_X=X^{1/2-\eta}\log X$ and retain
$\log B_i\le\mathsf Y_X=O((\log X)^2)$.
The argument localizes a hypothesis in
[Maynard--Pratt's flexible detector proof](../Zeros/maynardpratt2023halfisolated.md).
It assumes no finite-vertical-line hypothesis for the full zero set and gives no
estimate for its unselected complement. This is a `repo-derived` paper application,
with no new general zero-density theorem, priority or Lean-certification claim.

### The stronger local property is imposed on each selected zero

For a dyadic $T$ and an upper-half-plane zero $\rho_0$ with $T\le\gamma_0<2T$,
let $\mathcal H_\ast(T)$ consist of those actual zeros that are
$Y$-half-isolated in the cited Definition 8 for **every**
$\exp((\log\log T)^3)\le Y\le T$.
The definition is used above a fixed sufficiently large absolute $T_\ast$.
Dyadic bins below $T_\ast$ are left outside this selected submultiset.
This all-scale property is stronger than Definition 9's existential property;
it is not asserted for every half-isolated zero or for every zero.
Every selected zero has its original multiplicity.

Use the same source cut $H_{B,X}=\max\{51,\sqrt B/M^{19/10}\}$.
For each zero, let $T_\rho=2^{\lfloor\log_2\gamma\rfloor}$ and define

$$
\mathcal R_X^\ast
=2\sum_{i<m}\delta_i
\sum_{\substack{H_{B_i,X}<\gamma\le\tau_i,\ 3/5\le\beta\le3/4\\
T_\rho\ge T_\ast,\ \rho\in\mathcal H_\ast(T_\rho)}}
m_\rho|c_{B_i,a}(\rho)|.
\tag{SAH1}
$$

Then, uniformly in all original windows, ties and legal height assignments,

$$
\boxed{\mathcal R_X^\ast\ll M_X^{39/40}L_X=o(M_XL_X).}
\tag{SAH2}
$$

The constant and common source start depend only on the fixed original suppliers
and parameters. In particular this assertion includes $\Theta=1$.

### Localize the published flexible-detector argument

The first step of the proof of Lemma 35 uses Hypothesis $\mathcal F$ to infer that
its zero is $Y$-half-isolated at every scale in the preceding range.
For $\mathcal H_\ast(T)$ this conclusion is the explicit local membership condition.
The rest of that proof uses Proposition 16 at residual scales only.
At target length $A=T$, set $A_1=A$, choose
$U_j\in[\sqrt{A_j},A_j]$ by Proposition 16, replace $A_{j+1}=A_j/U_j$,
and stop when $A_{j+1}\le\exp((\log\log T)^4)$.
Every required isolation parameter $\sqrt{A_j}$ is inside the declared range
for sufficiently large $T$. The published construction therefore uses
$O(\log\log T)$ factors and yields a common family of detectors $P$ with

$$
\#\mathscr D_T\le\exp(C(\log\log T)^3),\qquad
|P(\rho_0)|\ge\exp(-C(\log\log T)^3),
$$

$$
P(s)=\sum_n b_P(n)n^{-s},\quad
|b_P(n)|\le\exp(C(\log\log T)^3),\quad
n\in[T\exp(-C(\log\log T)^4),\ T\exp(C(\log\log T)^2)].
\tag{SAH3}
$$

The family is independent of $\rho_0$; the point selects a detector from it.
These bounds are the existing product construction and its coefficient/family
counts, with the use of $\mathcal F$ replaced by its precise local consequence.
No use is made of Proposition 21's additional global cluster assumptions.

Apply the discrete-to-continuous inequality of the cited Lemma 27 and the classical
mean-square theorem for Dirichlet polynomials. The existing local zero count
bounds the total multiplicity in each smoothing interval of length $O((\log T)^2)$
by $O((\log T)^3)$. Real-part transport is elementary: for $\sigma\le\beta\le1$,

$$
|P(\beta+i\gamma)|^2
\le2|P(\sigma+i\gamma)|^2
 +2\int_\sigma^1|P'(u+i\gamma)|^2du.
$$

The derivative adds at most $O((\log T)^2)$ to the coefficient-square norm.
Consequently the same mean-square bound, uniformly for $3/5\le\sigma\le3/4$,
is at most a fixed logarithmic factor times
$(T+N_T)\sum_n|b_P(n)|^2n^{-2\sigma}$, where
$N_T=T\exp(C(\log\log T)^2)$.
The support and coefficient bounds in SAH3 make this
$T^{2(1-\sigma)}\exp(C'(\log\log T)^4)$.
Summing over the common detector family and paying its lower detection threshold
gives the quantitative bound

$$
\sum_{\substack{\rho\in\mathcal H_\ast(T)\\\beta\ge\sigma}}m_\rho
\ll T^{2(1-\sigma)}\exp(C_\ast(\log\log T)^4),
\qquad 3/5\le\sigma\le3/4.
\tag{SAH4}
$$

All constants are uniform on this compact real-part interval. This derivation
retains the quantitative loss; Corollary 5's unspecified $T^{o(1)}$ has not been
substituted for it.

### Spend the quantitative loss at the actual source clocks

For one actual core, split only SAH1's finite masked ordinates into dyadic bins.
Every participating $T$ satisfies $T\ge H_{B,X}/2$ and $T\ll\sqrt B$.
Thus $\sqrt B/T\le2M^{19/10}$.
For the real-part weight use the exact positive representation

$$
B^{\beta-1/2}
=B^{1/10}+(\log B)\int_{3/5}^{\beta}B^{\sigma-1/2}d\sigma.
$$

On each dyadic bin, SAH4 and DH3's complete coefficient bound therefore bound
its contribution by

$$
C_a\exp(C_\ast(\log\log T)^4)
(1+\log B)M^{19/20}.
$$

Indeed $B^{\sigma-1/2}T^{1-2\sigma}=(\sqrt B/T)^{2\sigma-1}$ and
$1/5\le2\sigma-1\le1/2$; its maximum is at most a constant times $M^{19/20}$,
including the case $\sqrt B/T<1$.
There are $O(1+\log B)$ bins. CP1 gives, uniformly in the original cores,

$$
\exp(C_\ast(\log\log T)^4)(1+\log B)^2
\le\exp(O((\log\log X)^4))=M^{o(1)}.
$$

Since the original $\eta<1/2$ is fixed, this factor is at most $M^{1/40}$
at one common source start. Sum the original weights to prove SAH2.
No polynomial core-clock ceiling or restriction $\Theta<1$ is used.

As in SIH4, this lower cut lies uniformly below BH1's auxiliary cuts.
SAH2 therefore pays an actual submultiset also below the previously paid upper
slice. The full subtraction, all original masks and all multiplicities are retained.
Low dyadic bins below $T_\ast$, low frequencies below $H_{B,X}$, real parts outside
the chosen band, and zeros failing the all-scale condition remain in the exact
complement. No assertion of membership, nonempty occupancy or favorable phase is
inferred from the existence of this estimate. The full signed Robin joint comparison,
all-integer Robin and RH remain unproved.


## One local isolation scale suffices under the sharper original clock ceiling

Keep SIH1 and SAH1's original complete coefficients, positive outgoing weights,
every source window and maximizing tie, all multiplicities, and the individual legal
upper heights. This `repo-derived` paper application uses the already retained VC2
clock ceiling. It includes the original $\Theta=1$ case and replaces the preceding
all-scale local isolation condition by an existential condition in a specified range.
It does not estimate the whole ordinary half-isolated class or its complement.
The analytical methods and detector are existing tools, without a priority or
Lean-certification claim.

### Keep the scale of the published detector quantitative

For a sufficiently large dyadic $T$, put

$$
v_T=\sqrt{(\log T)(\log\log T)}.
$$

Let $\mathcal H_\circ(T)$ be the actual zeros with $\beta\ge1/2$ and
$T\le\gamma<2T$ that are
$Y$-half-isolated in Maynard--Pratt's Definition 8 for at least one $Y$ satisfying

$$
\tfrac12v_T\le\log Y\le2v_T.
\tag{OSH1}
$$

Both ends lie inside Definition 9's allowed range at one sufficiently large fixed
start, uniformly for these ordinates. Count every selected zero with its actual
multiplicity. The [published Proposition 16](../Zeros/maynardpratt2023halfisolated.md)
gives a common grid of at most $(\log T)^{152}$ values of $U$, with
$Y\le U\le Y^2$, such that one of the polynomials

$$
P_U(s)=\sum_n\Lambda(n)w_0(n/U)n^{-s}
$$

satisfies $|P_U(\rho)|\ge c_0(\log T)^{-100}$ for each selected zero.
The chosen detector lies in the restricted common grid

$$
\mathscr U_\circ(T)=\mathscr U(T)\cap
 [\exp(v_T/2),\exp(4v_T)],
$$

where $\mathscr U(T)$ is Proposition 16's grid. Thus
$v_T/2\le\log U\le4v_T$ for every grid value used below.
This uses the unconditional single-scale proposition; neither
Hypothesis $\mathcal F$ nor Lemma 35 is needed.

For each $U\in\mathscr U_\circ(T)$ set

$$
k=\left\lfloor\frac{\log T}{\log(2U)}\right\rfloor,
\quad Q_U=P_U^k=\sum_n b_U(n)n^{-s},
\quad N=(2U)^k,\quad D=(U/2)^k.
$$

At the fixed start $k\ge1$, and

$$
\frac{T}{2U}<N\le T,\qquad
D=N4^{-k}>\frac{T}{2U}4^{-k},\qquad
k\log\log T\ll v_T.
\tag{OSH2}
$$

The coefficients vanish outside $[D,N]$. To bound them without a growing-order
divisor-square loss, directly use the classical identity
$\sum_{d\mid n}\Lambda(d)=\log n$. Induction gives
$\Lambda^{*k}(n)\le(\log n)^k$, where $*$ here is Dirichlet convolution.
With $C_w=\max\{1,\|w_0\|_\infty\}$, this yields

$$
|b_U(n)|\le C_w^k\Lambda^{*k}(n)
\le(C_w\log T)^k\quad(n\le N).
$$

The detection threshold for $Q_U$ is at least $\exp(-C v_T)$.
Its coefficients, and their real-part derivatives' coefficients, are bounded by a
fixed power of $N$ at the common start, because $\log N\sim\log T$ and
$k\log\log T=O(v_T)=o(\log T)$.

Apply the same published Lemma 27, multiplicity-aware local zero count,
real-part transport and classical polynomial mean-square inequality already used
in SAH4. The smoothing intervals have overlap $O((\log T)^3)$, including
multiplicity. The real-part derivative adds a logarithmic factor only.
The negligible error in Lemma 27 is smaller than half the detection threshold.
Uniformly for $3/5\le\sigma\le3/4$, the mean square is bounded by a fixed
logarithmic factor times

$$
(T+N)\sum_{n\ge D}|b_U(n)|^2n^{-2\sigma}
\ll T(C_w\log T)^{2k}D^{1-2\sigma}
\le T^{2(1-\sigma)}
 \exp\!\bigl(C(\log U+k\log\log T)\bigr).
$$

The convergent sum $\sum_{n\ge D}n^{-2\sigma}\ll D^{1-2\sigma}$ is uniform on
the displayed compact interval. OSH2, the detection threshold and the polynomial
number of grid values therefore give the quantitative subset count

$$
\boxed{
N_\circ(\sigma;T,2T)
:=\sum_{\substack{\rho\in\mathcal H_\circ(T)\\\beta\ge\sigma}}m_\rho
\ll T^{2(1-\sigma)}\exp(C_\circ v_T),
\qquad 3/5\le\sigma\le3/4.}
\tag{OSH3}
$$

This is a parameter application of the short detector and the existing mean-square
argument. It is not attributed to Corollary 5 as a quantitative statement for every
ordinary half-isolated zero.

### Spend that loss using VC2 on the same actual cores

Choose one fixed sufficiently large $T_\circ$ for the preceding application.
With the unchanged $H_{B,X}=\max\{51,\sqrt B/M^{19/10}\}$ and
$T_\rho=2^{\lfloor\log_2\gamma\rfloor}$, define

$$
\mathcal R_X^\circ
=2\sum_{i<m}\delta_i
\sum_{\substack{H_{B_i,X}<\gamma\le\tau_i,\ 3/5\le\beta\le3/4\\
T_\rho\ge T_\circ,\ \rho\in\mathcal H_\circ(T_\rho)}}
m_\rho|c_{B_i,a}(\rho)|.
\tag{OSH4}
$$

Reuse the positive integral representation of $B^{\beta-1/2}$ in the payment
following SAH4, and
the complete original bound $|c_{B,a}(\rho)|\le(a+2)B^{\beta-1/2}/\gamma$.
OSH3 then bounds one participating dyadic bin by
$C_a\exp(C_\circ v_T)(1+\log B)M^{19/20}$.
Indeed $T\ge H_{B,X}/2$ and $T\ll\sqrt B$, so the same maximum of
$(\sqrt B/T)^{2\sigma-1}$ is at most $C M^{19/20}$.
There are $O(1+\log B)$ bins, all finite at the original individual upper mask.

The necessary loss payment uses the already retained stronger VC2, not CP1 alone:

$$
\log B_{\max,X}^{\rm end}
\le K(\log X)^{5/3}(\log\log X)^{1/3},\qquad
v_T\ll_K(\log X)^{5/6}(\log\log X)^{2/3}.
$$

Since the original $\eta<1/2$ is fixed,

$$
\exp(C_\circ v_T)(1+\log B)^2=M_X^{o(1)}.
$$

At one common source start this factor is at most $M_X^{1/40}$. Summing the
original positive weights proves, including $\Theta=1$,

$$
\boxed{\mathcal R_X^\circ\ll M_X^{39/40}L_X=o(M_XL_X).}
\tag{OSH5}
$$

After choosing a common fixed dyadic start, every SAH1 all-scale zero satisfies
OSH1, so this pays at least that submultiset under VC2. OSH1 requires only one
local scale, rather than isolation at all the residual scales used in SAH3.
SIH2 already covers this class for fixed $\Theta<1$; the added application is the
weaker local condition at $\Theta=1$. No occurrence of an extra actual zero is
asserted. SAH2 remains independently valid under CP1's weaker clock ceiling.

The cut remains below the already paid BH1 auxiliary slice as in SIH4. All zeros
without a witness in OSH1's range, the low dyadic bins, lower frequencies and real
parts outside the displayed band remain in the exact complement. Overlapping
subsets do not produce additive reserves. The whole ordinary half-isolated class
at $\Theta=1$, the original signed joint Robin comparison and RH remain unproved.


## The ordinary half-isolated subhead has a source-relative allowance at supremum one

Keep JM1--JM7's original conditional source, its fixed
$\Theta\in(1/2,1]$, $1-\Theta<\eta<1/2$, $d>0$ and
$0<a<5\kappa/8$. Keep every original full window, maximizing tie,
positive outgoing weight and admissible individual height. Use exactly
SIH1's actual ordinary half-isolated zeros, real-part interval
$[3/5,3/4]$ and lower cut
$H_{B,X}=\max\{51,\sqrt B/M_X^{19/10}\}$; no extra isolation-scale
condition is imposed. This application uses the existing count SIH3,
full coefficient bound, unabridged height JM1 and HC1--HC2. It does not
assert SIH2's uniform absolute $o(M_XL_X)$ allowance at $\Theta=1$.

### Keep the small power of the actual core before spending its height

Write $M=M_X$, $\mu=1/2-\eta>0$, and, at one original core, put

$$
\begin{aligned}
r_X^{\rm hi}(B,\tau)
&=2\!\sum_{\substack{\rho\in\mathcal H,\ H_{B,X}<\gamma\le\tau\\
                      3/5\le\beta\le3/4}}
   m_\rho|c_{B,a}(\rho)|,\\
h_X(B)&=\frac d2X^{-\eta}\sqrt B\log B,\qquad
\mathscr H_X=\sum_{i<m}\delta_i h_X(B_i).
\end{aligned}
$$

For every fixed $r>0$, SIH3 and the coefficient bound already used
in SIH2 give, after a common source start,

$$
\boxed{r_X^{\rm hi}(B,\tau)\ll_{r,a} M^{19/20}B^r.}
\tag{HIA1}
$$

Here it suffices to take $r<1/10$. Choose a fixed finite real-part
partition with maximum width $\omega$ and a fixed count loss
$\epsilon>0$ such that $\omega+\epsilon/2\le r$ and $\epsilon<1/10$.
For $H_{B,X}=\sqrt B/M^{19/10}\ge51$, the pre-SC2 bound in SIH2 is

$$
C M^{(19/10)(2\sigma_j-1-\epsilon)}
 B^{\sigma_{j+1}-\sigma_j+\epsilon/2}
\le C M^{19/20}B^r.
$$

If $H_{B,X}=51$, its other already used bound is
$C B^{1/4}\le C M^{19/20}$. Constants cover the bounded initial
zero range. Multiplicities are retained as in SIH3. The positive sum
may be extended past $\tau$ only for this upper estimate; the actual
upper mask is unchanged. No moving-real-part density theorem,
polynomial ceiling SC2 or logarithmic ceiling CP1/VC2 is used.

Now fix $r=\mu/160$. Split the estimate at $B=X^2$, keeping both
parts of the original source. If $B\le X^2$, HIA1 gives

$$
\frac{r_X^{\rm hi}(B,\tau)}M
\ll X^{-3\mu/80}(\log X)^{-1/20}.
$$

If $B>X^2$, use $r<1/2$ and $\log B\ge2\log X$ to obtain

$$
\begin{aligned}
\frac{r_X^{\rm hi}(B,\tau)}{h_X(B)}
&\ll_{\eta,d,a}M^{19/20}X^\eta
  \frac{B^{r-1/2}}{\log B}\\
&\ll_{\eta,d,a}
 X^{-1/2-3\mu/80}(\log X)^{-1/20}.
\end{aligned}
$$

Consequently one fixed constant gives
$e_X=C_{\eta,d,a}X^{-3\mu/80}(\log X)^{-1/20}\to0$, with

$$
\boxed{r_X^{\rm hi}(B,\tau)\le e_X\bigl(M_X+h_X(B)\bigr),\qquad
\mathcal R_X^{\rm hi}
\le e_X\bigl(M_XL_X+\mathscr H_X\bigr).}
\tag{HIA2}
$$

These are uniform over all original cores, ties and legal heights,
including $\Theta=1$. The allowance depends on the same source's
retained positive height. No bound $\mathscr H_X=O(M_XL_X)$ is assumed,
and HIA2 is not reported as an absolute $o(M_XL_X)$ estimate.

### Remove exactly this subhead while retaining the full lower margin

Choose one fixed $C>8/5$ with $aC<1$. JM1 and its uniform
$\chi_{p,u}\to1$ give, beyond a common source start,

$$
G_a(B)\ge h_X(B)-aH_C,\qquad
\mathscr H_X\le\mathcal G_X+aH_CL_X.
\tag{HIA3}
$$

The remaining lag coefficient in JM1 is nonnegative at that start.
Thus the height is spent only within the original joint response;
it is not counted as another independent reserve.

Define the removed real contribution using the same actual terms:

$$
q_X^{\rm hi}(B,\tau)
=2\operatorname{Re}
 \!\sum_{\substack{\rho\in\mathcal H,\ H_{B,X}<\gamma\le\tau\\
                      3/5\le\beta\le3/4}}
 m_\rho c_{B,a}(\rho),\qquad
S_X^{\rm rem}(\boldsymbol\tau)
=S_X(\boldsymbol\tau)-\sum_{i<m}\delta_iq_X^{\rm hi}(B_i,\tau_i).
$$

In particular $|q_X^{\rm hi}|\le r_X^{\rm hi}$. HIA2--HIA3 and the
unchanged HC2 error give directly

$$
\begin{aligned}
S_X^{\rm rem}(\boldsymbol\tau)
&\ge\mathcal G_X-O_a(L_X)-\mathcal R_X^{\rm hi}\\
&\ge(1-e_X)\mathcal G_X-e_XM_XL_X-O_a(L_X).
\end{aligned}
\tag{HIA4}
$$

The fixed constants in the last line may also depend on the original
capacity supplier. Since $1-e_X>0$ eventually, JM7 can now be applied
with its direction preserved. For every fixed requested
$\varepsilon>0$, one common source start supplies

$$
\boxed{S_X^{\rm rem}(\boldsymbol\tau)
\ge(R_\eta-\varepsilon)M_XL_X}
\tag{HIA5}
$$

on every original qualifying full window, for every maximizing-tie
assignment and every admissible individual height assignment. In fact
JM7 also gives $\mathcal G_X\ge(R_\eta/2)M_XL_X$ eventually, so
HIA2--HIA3 imply $\mathcal R_X^{\rm hi}/\mathcal G_X=O(e_X)$.
The full ordinary half-isolated contribution in this high-frequency
mask is a vanishing fraction of the same complete source response,
even where its uniform absolute $o(M_XL_X)$ bound was not supplied.

An upper estimate for this exact remaining head with any fixed
constant below $R_\eta$, on the original cofinal full windows and with
all original tie and height quantifiers, would contradict HIA5. No
such estimate or favorable window is constructed here. All non-half-
isolated zeros, frequencies below $H_{B,X}$ and real parts outside
$[3/5,3/4]$ remain, with their original coefficients and masks.
SIH2, SAH and OSH remain their separate absolute allowances; overlapping
payments are not added as reserves. This is a source application of
existing estimates, not a new density theorem, a literature-priority
claim, a Lean verification or a proof of Robin or RH.


## The retained source height pays every zero in the same frequency mask

Keep JM1--JM7's original conditional source, all full windows, maximizing
ties, positive outgoing weights, actual zero multiplicities and individual
legal upper heights. In this application the originally supplied parameters
must satisfy

$$
\Theta\in(1/2,1],\qquad 1-\Theta<\eta<\frac9{28},\qquad
\mu=\frac12-\eta>\frac5{28}.
$$

The original restrictions on $d,\kappa,a$ are unchanged. This is a
restriction on the supplied $\eta$, not permission to reselect it. In
particular the application includes $\Theta=1$ on this range. Retain
SIH1's same lower cut

$$
H_{B,X}=\max\{51,\sqrt B/M_X^{19/10}\},\qquad
M_X=X^\mu\log X,
$$

and its same real-part interval $[3/5,3/4]$. Here the sum includes
**all** actual zeros in that mask, without any half-isolation assumption:

$$
\begin{aligned}
r_X^{\rm all}(B,\tau)
&=2\!\sum_{\substack{H_{B,X}<\gamma\le\tau\\
                       3/5\le\beta\le3/4}}
 m_\rho|c_{B,a}(\rho)|,\\
\mathcal R_X^{\rm all}
&=\sum_{i<m}\delta_i r_X^{\rm all}(B_i,\tau_i).
\end{aligned}
$$

The complete coefficient is still
$c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho$.
The result is a source application of the existing general density
estimates and the same retained positive height. No new density theorem
is asserted.

### Match the general density loss to the original positive height

Reuse IH3's Ingham input for $3/5\le\sigma\le7/10$ and DH3's
[Guth--Maynard input](../Analytic/guthmaynard2024largevalues.md#the-zero-density-input-for-cumulative-contributions)
for $7/10\le\sigma\le3/4$. Write

$$
D(\sigma)=
\begin{cases}
3(1-\sigma)/(2-\sigma),&3/5\le\sigma\le7/10,\\
15(1-\sigma)/(3+5\sigma),&7/10\le\sigma\le3/4,
\end{cases}
\qquad
U(\sigma)=\frac{19}{10}[1-D(\sigma)],\quad
E(\sigma)=\sigma-1+\frac{D(\sigma)}2.
$$

The two density exponents agree at $7/10$. Both published estimates
count actual zeros with multiplicity. Their existing fixed-parameter
reciprocal-height consequence is
$\sum_{\gamma>H,\,\beta\ge\sigma}m_\rho/\gamma
\ll_{\sigma,\epsilon}H^{D(\sigma)-1+\epsilon}$ for $H\ge51$.
Only finitely many fixed real-part parameters are used below.

On the first segment, direct substitution gives

$$
\frac{E(\sigma)}{1-U(\sigma)}
=\frac{5(1-\sigma)(2\sigma-1)}{39-48\sigma}
\le\frac19.
$$

The denominator is positive, and the last inequality is equivalent to
$90(\sigma-7/10)(\sigma-4/3)\ge0$. On the second segment,

$$
\frac{E(\sigma)}{1-U(\sigma)}
=\frac{5(1-\sigma)(9-10\sigma)}{6(43-55\sigma)}
\le\frac5{28}.
$$

Its denominator is positive; after clearing it, the last inequality is
$280(3/4-\sigma)(\sigma+1/35)\ge0$. Also $D$ is decreasing on
both segments, so $1-U\ge7/45$ throughout this interval. Consequently,
with one fixed positive parameter

$$
q=\frac7{90}\left(\mu-\frac5{28}\right)>0,
\qquad
(1-U(\sigma))\mu-E(\sigma)\ge2q.
\tag{AHA1}
$$

Use disjoint half-open bins with $7/10$ as an endpoint, closing the
final bin at $3/4$. Choose their maximum width $\omega>0$ and one
fixed $\epsilon>0$ so that $\omega+\epsilon/2\le q$ and
$D(\sigma_j)+\epsilon<1$ at every left endpoint. DH3's existing full
coefficient bound and reciprocal-height sum bound a bin by

$$
C B^{\sigma_{j+1}-1/2}H_{B,X}^{D(\sigma_j)-1+\epsilon}
\le C M_X^{U(\sigma_j)}B^{E(\sigma_j)+q}.
\tag{AHA2}
$$

Indeed, $H_{B,X}\ge\sqrt B/M_X^{19/10}$ and the height exponent
is negative. This also covers the branch $H_{B,X}=51$; bounded initial
heights are in the existing constant. The favorable factor
$M_X^{-19\epsilon/10}$ has only been discarded. Extending each
positive sum above $\tau$ is an upper estimate; no actual upper mask
is changed.

Let $r_{X,j}^{\rm all}$ denote the contribution of one bin, and write
$h_X(B)=(d/2)X^{-\eta}\sqrt B\log B$, as in HIA2. For
$B\le X$, divide each bound in AHA2 by $M_X$ and use AHA1 to get

$$
\frac{r_X^{\rm all}(B,\tau)}{M_X}
\ll X^{-q}(\log X)^{-7/45}.
$$

For $B>X$, $E(\sigma_j)+q<1/2$, so division by $h_X(B)$ gives

$$
\begin{aligned}
\frac{r_{X,j}^{\rm all}(B,\tau)}{h_X(B)}
&\ll X^\eta M_X^{U(\sigma_j)}
 \frac{B^{E(\sigma_j)+q-1/2}}{\log B}\\
&\ll X^{-(1-U(\sigma_j))\mu+E(\sigma_j)+q}
 (\log X)^{U(\sigma_j)-1}\\
&\ll X^{-q}(\log X)^{-7/45}.
\end{aligned}
$$

The displayed binwise estimates are summed over a fixed finite
partition. Here $0<E(\sigma)\le1/4$ and $q<7/180$ ensure the
negative power of $B$ used in the second case. This splits only the
estimate, retaining both parts of the original source. In particular,
no upper clock ceiling and no assumption $B\asymp X$ is used.

Thus, for one constant depending on the fixed original parameters
and suppliers,

$$
\boxed{
\begin{aligned}
e_X^{\rm all}&=C X^{-q}(\log X)^{-7/45}\longrightarrow0,\\
r_X^{\rm all}(B,\tau)&\le e_X^{\rm all}[M_X+h_X(B)],\\
\mathcal R_X^{\rm all}
&\le e_X^{\rm all}[M_XL_X+\mathscr H_X].
\end{aligned}}
\tag{AHA3}
$$

The estimates are uniform on all original windows, ties and legal
individual height assignments on the stated original exponent range,
including $\Theta=1$. As in HIA2, $\mathscr H_X$ need not be
$O(M_XL_X)$; AHA3 is not an absolute $o(M_XL_X)$ assertion.

### Remove the whole masked class in the unchanged signed account

Apply HIA3's already established
$\mathscr H_X\le\mathcal G_X+O_a(L_X)$ and HIA4--HIA5's same
comparison, now with AHA3's actual all-zero allowance. If
$S_X^{\rm rem,all}(\boldsymbol\tau)$ deletes precisely the real
contribution of the zeros in this same mask from the original full
head, then

$$
\begin{aligned}
S_X^{\rm rem,all}(\boldsymbol\tau)
&\ge(1-e_X^{\rm all})\mathcal G_X
 -e_X^{\rm all}M_XL_X-O_a(L_X),\\
S_X^{\rm rem,all}(\boldsymbol\tau)
&\ge(R_\eta-\varepsilon)M_XL_X
\quad\text{eventually for every fixed }\varepsilon>0,\\
\mathcal R_X^{\rm all}/\mathcal G_X&=O(e_X^{\rm all})\longrightarrow0.
\end{aligned}
\tag{AHA4}
$$

All original full-window, maximizing-tie and legal-height quantifiers
are retained. The positive height is used only inside the same
complete response. This controls non-half-isolated zeros in the mask
as well as the half-isolated zeros already covered by HIA1--HIA5.
It leaves that earlier result's wider $\eta<1/2$ scope intact.
The fact that the estimate covers a larger class does not assert that
any added zeros actually exist or carry a positive fraction of the
original response.

The whole masked class is removed, but frequencies below $H_{B,X}$,
real parts outside $[3/5,3/4]$, and their original complete signed
contributions remain. No favorable cofinal full window or sufficient
upper bound for this remaining head is supplied. Overlapping allowances
are not added as independent reserves. This is a paper application of
existing general density and source inequalities, with no new density
theorem, literature-priority claim, Lean verification, all-integer Robin
inequality or RH proof.


## The original height pays the complete lower real-part head

Keep JM1--JM7's original conditional source, fixed
$\Theta\in(1/2,1]$, $1-\Theta<\eta<1/2$, $d>0$ and the original
$0<a<5\kappa/8$. Keep every full window, maximizing tie, positive
outgoing weight, actual zero multiplicity and legal individual upper
height. No stronger restriction on the supplied $\eta$ is imposed.
Put

$$
\mu=\frac12-\eta>0,\qquad
\sigma_0=1-\eta=\frac12+\mu,\qquad
\sigma_* =\frac12+\frac\mu2.
$$

At the original upper height, define the entire inclusive lower
real-part contribution, without a lower frequency cut:

$$
\begin{aligned}
r_X^{\rm low}(B,\tau)
&=2\!\sum_{\substack{0<\gamma\le\tau\\\beta\le1-\eta}}
 m_\rho|c_{B,a}(\rho)|,\\
\mathcal R_X^{\rm low}
&=\sum_{i<m}\delta_i r_X^{\rm low}(B_i,\tau_i),\qquad
c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho.
\end{aligned}
$$

This includes all actual zeros in the stated region, including low
frequencies and the boundary $\beta=1-\eta$. It uses neither
half-isolation nor an upper clock ceiling.

### Reuse reciprocal-height summability away from the critical line

Reuse the general fixed-parameter Ingham input already recorded in
IH1--IH4, [Chourasiya--Simonič, Corollary 1 and Table 1](https://arxiv.org/html/2507.15184v2).
Since $\sigma_*>1/2$, its density exponent
$d_I(\sigma_*)=3(1-\sigma_*)/(2-\sigma_*)$ is strictly less than
one. DH3's existing reciprocal-height consequence, with a fixed
positive loss smaller than $1-d_I(\sigma_*)$, therefore supplies

$$
\sum_{\substack{\gamma>0\\\beta\ge\sigma_*}}
\frac{m_\rho}{|\rho|}<\infty.
$$

Bounded initial ordinates are included in the constant. This is the
standard density summation already used in DH3 and IH3, not a new
summation theorem. SR1 also already uses the complete sums
$\sum_{\gamma>0}m_\rho/\gamma^2<\infty$ and
$\sum_{0<\gamma\le\tau}m_\rho/|\rho|\ll1+\log^2(2+\tau)$,
with actual multiplicities.

Apply these existing bounds to the two parts
$\beta<\sigma_*$ and $\sigma_*\le\beta\le\sigma_0$.
SR1's original degree-two and degree-one coefficient bounds give,
uniformly at every original $\tau\asymp\sqrt B$,

$$
\begin{aligned}
r_X^{\rm low}(B,\tau)
&\ll_{a,\eta}
 B^{\mu/2}(1+\log^2 B)+B^\mu\\
&\ll_{a,\eta} B^\mu
\quad\text{beyond one fixed core start}.
\end{aligned}
\tag{LHA1}
$$

The first term is absorbed because $\mu>0$ is fixed. The original
subtraction remains inside each coefficient. No infinite
reciprocal-height sum over the critical-line zeros is asserted.

### Pay the inclusive endpoint with the same source height

Keep $M_X=X^\mu\log X$ and the original
$h_X(B)=(d/2)X^{-\eta}\sqrt B\log B$ from HIA2.
For $B\le X$, LHA1 gives
$r_X^{\rm low}(B,\tau)/M_X\ll1/\log X$. For $B>X$, it gives

$$
\frac{r_X^{\rm low}(B,\tau)}{h_X(B)}
\ll_{a,\eta,d}\frac{X^\eta B^{-\eta}}{\log B}
\le\frac{C_{a,\eta,d}}{\log X}.
$$

Here $\eta>0$. Both parts of the original source remain; the split
is used only in the estimate. All original core clocks escape to
infinity uniformly, so LHA1's core start can be included in one common
source start. Summing the unchanged positive outgoing weights gives

$$
\boxed{
\mathcal R_X^{\rm low}
\le\frac{C_{a,\eta,d}}{\log X}
 [M_XL_X+\mathscr H_X],\qquad
\frac{\mathcal R_X^{\rm low}}{\mathcal G_X}
=O_{a,\eta,d}\!\left(\frac1{\log X}\right)\longrightarrow0.}
\tag{LHA2}
$$

The second statement reuses HIA3's
$\mathscr H_X\le\mathcal G_X+O_a(L_X)$ and JM7's
$\mathcal G_X\ge(R_\eta/2)M_XL_X$ eventually. The height is spent
only inside that same complete response. No assumption
$\mathscr H_X=O(M_XL_X)$ or absolute $o(M_XL_X)$ conclusion is made.

Let $S_X^{\rm rem,low}(\boldsymbol\tau)$ be the original head after
deleting precisely the real contribution of this entire lower
real-part class. HC2 and the already used HIA4--HIA5 comparison apply
with LHA2's allowance. Thus, for every fixed $\varepsilon>0$,

$$
\boxed{S_X^{\rm rem,low}(\boldsymbol\tau)
\ge(R_\eta-\varepsilon)M_XL_X\quad\text{eventually}.}
\tag{LHA3}
$$

This holds on every original qualifying full window, for every
maximizing-tie assignment and every admissible individual height
assignment, throughout the original parameter range including
$\Theta=1$. It pays a full fixed-width lower real-part head, including
its low frequencies, beyond SR3's ceiling-dependent cut and CP3's
shrinking band. The earlier absolute and source-relative estimates
remain valid under their own hypotheses; overlapping contributions
are not counted twice.

The original source still has $1-\eta<\Theta$. In particular MB3's
fixed-zero obstruction is not removed: its cut satisfies
$\beta_c-(1-\eta)=\mu(\Theta+\eta-1)/(1-\eta)>0$.
The exact remaining head has $\beta>1-\eta$ and its original upper
masks and complete coefficients. No sufficient signed upper bound
for that head, favorable cofinal full window, all-integer Robin
inequality or RH proof is supplied. This is a paper source application
of existing density, coefficient and joint-height estimates, with no
new density theorem, literature-priority claim or Lean verification.


## A uniform near-one density input pays a lower high-frequency cut

Keep JM1--JM7's original conditional source, its fixed
$\Theta\in(1/2,1]$, $1-\Theta<\eta<1/2$, $d>0$ and
$0<a<5\kappa/8$. Keep every full window, maximizing tie, positive
outgoing weight, actual zero multiplicity and legal individual upper
height. Write $M=M_X=X^{1/2-\eta}\log X$, $L=L_X$ and
$b_X=\min_{i<m}B_i$. The original source already gives
$\sqrt{b_X}/M\to\infty$, as used in BH1 and SIH4. Put

$$
\sigma_\circ=\frac{9999}{10000},\qquad
H_{B,X}=\max\{51,\sqrt B/M\}.
$$

At one common source start, $H_{B,X}=\sqrt B/M\to\infty$
uniformly over all original cores and is below every original legal
upper height $\tau\asymp\sqrt B$. Define the actual complete-coefficient
allowance

$$
\begin{aligned}
r_X^{\rm edge}(B,\tau)
&=2\!\sum_{\substack{H_{B,X}<\gamma\le\tau\\\beta\ge\sigma_\circ}}
 m_\rho|c_{B,a}(\rho)|,\\
\mathcal R_X^{\rm edge}
&=\sum_{i<m}\delta_i r_X^{\rm edge}(B_i,\tau_i),\qquad
c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho.
\end{aligned}
$$

There is no fixed upper real-part endpoint below one and no
half-isolation requirement.

### Reuse Ford's uniform near-unity bound and the zero-free region

Kevin Ford, *Vinogradov's integral and bounds for the Riemann zeta
function*, [arXiv:1910.08209v1](https://arxiv.org/pdf/1910.08209v1),
printed p.2, consequence (iii) of Theorem 1, records

$$
N(\sigma,T)\ll T^{58.05(1-\sigma)^{3/2}}\log^{15}T
\qquad(9/10\le\sigma\le1).
\tag{NE1}
$$

The source count uses $\sigma\le\Re\rho\le1$ and
$|\Im\rho|\le T$, so it bounds the positive-height count used here,
with multiplicities. This uniform estimate is distinct from
HR1's finitely many fixed-$\sigma$ bounds with $T^\varepsilon$ loss.
For $\sigma_\circ\le\sigma<1$,
$58.05\sqrt{1-\sigma}\le0.5805<1$, hence the same input implies

$$
N(\sigma,T)\ll T^{1-\sigma}\log^{15}T
\quad\text{uniformly for }\sigma_\circ\le\sigma<1.
$$

The standard dyadic reciprocal-height argument already used in DH3
therefore gives, uniformly in that entire real-part interval,

$$
A(\sigma,H):=
\sum_{\substack{\gamma>H\\\beta\ge\sigma}}
 \frac{m_\rho}{\gamma}
\ll H^{-\sigma}(\log H)^{15}
\qquad(H\ge51).
\tag{NE2}
$$

Indeed, the dyadic terms have ratios bounded away from one because
$\sigma\ge\sigma_\circ>0$; their polynomial logarithmic factors
have a common summable majorant. No moving $T^\varepsilon$ loss or
moving implicit constant is introduced.

The same primary, printed pp.1--2, records the classical
Vinogradov--Korobov zero-free region
$1-\beta\gg(\log\gamma)^{-2/3}(\log\log\gamma)^{-1/3}$
for $\gamma\ge3$, with an absolute positive constant. Since the
actual mask has $51<\gamma\le\tau<\sqrt B$, all its actual zeros
satisfy, after decreasing a fixed positive constant if necessary,

$$
\beta\le1-\nu_B,\qquad
\nu_B=\frac{c_0}{(\log B)^{2/3}(\log\log B)^{1/3}}.
\tag{NE3}
$$

These analytic results remain external inputs; their proofs are not
reproved or Lean-certified here. In particular NE3 is a cap only on
the finite actual mask. It is not imposed on the zeros above $\tau$
when NE2 is used as a positive upper bound.

### Bound the actual finite layer integral before summing windows

Reuse DH3's full-coefficient estimate
$|c_{B,a}(\rho)|\le(a+2)B^{\beta-1/2}/\gamma$ for $\gamma\ge1$.
If $1-\nu_B<\sigma_\circ$, the selected class is empty.
Otherwise the positive layer identity for $B^{\beta-1/2}$ gives

$$
\begin{aligned}
r_X^{\rm edge}(B,\tau)\ll_a{}&
 B^{\sigma_\circ-1/2}A(\sigma_\circ,H_{B,X})\\
 &+\log B\int_{\sigma_\circ}^{1-\nu_B}
       B^{\sigma-1/2}A(\sigma,H_{B,X})\,d\sigma.
\end{aligned}
\tag{NE4}
$$

Every reciprocal-height tail on the right is an upper bound for the
same finite masked layer. Their extension to infinite heights is
used only for that positive upper estimate. For
$\sigma_\circ\le\sigma\le1-\nu_B$, NE2 and
$H_{B,X}=\sqrt B/M$ give

$$
\begin{aligned}
B^{\sigma-1/2}H_{B,X}^{-\sigma}
&=M^{\sigma}B^{-(1-\sigma)/2}\\
&\le M\exp[-\nu_B\log B/2],
\qquad \log H_{B,X}\le\tfrac12\log B.
\end{aligned}
$$

Consequently

$$
\boxed{r_X^{\rm edge}(B,\tau)
\ll_a M(\log B)^{16}
 \exp\!\left[-\frac{c_0}{2}
      \left(\frac{\log B}{\log\log B}\right)^{1/3}\right].}
\tag{NE5}
$$

The function multiplying $M$ tends to zero as $B\to\infty$.
Since all original cores satisfy $B_i\ge b_X\to\infty$ and
$\sum_i\delta_i=L$, NE5 proves the uniform absolute allowance

$$
\boxed{\mathcal R_X^{\rm edge}=o(M_XL_X).}
\tag{NE6}
$$

All constants and source starts retain the original fixed parameters;
no uniformity as $\eta\downarrow0$ is asserted. No upper clock ceiling,
restriction $\Theta<1$, or reselection of the supplied $\eta$ is used.
Thus the estimate includes the original $\Theta=1$ case.

BH1's already paid auxiliary interval starts at
$T^0_{B,X}=\sqrt B\,\mathsf Y_X^2/M$, with
$\mathsf Y_X\to\infty$. Here
$H_{B,X}/T^0_{B,X}=\mathsf Y_X^{-2}\to0$ uniformly.
NE6 therefore also controls the stated near-one class below those
auxiliary cuts. This cut is only a mask for an absolute estimate;
no new CHJ explicit formula or height-admissibility claim is made.
It extends HR3's compact-band control to real parts approaching one,
with its own stated lower cut.

Deleting exactly this actual class changes the original weighted real
head by $o(M_XL_X)$. HC2 and JM7 then retain its original lower margin,
up to an arbitrarily small fixed loss, on every original full window,
tie and admissible height assignment. If it is combined with LHA3,
use disjoint deletion masks: retain only $\beta>1-\eta$ in this
additional deletion, so overlaps are not paid twice. The resulting
remaining head has $\beta>1-\eta$ and either
$\beta<\sigma_\circ$ or $\gamma\le H_{B,X}$.
Every fixed actual zero still eventually lies below $H_{B,X}$.
No signed upper bound for that remaining head, favorable cofinal
window, full Robin inequality or RH proof is supplied. This is an
application of classical density and zero-free inputs to the same
source, without a new density theorem or literature-priority claim.


## The retained response pays all real parts above the same local cut

Keep JM1--JM7's original conditional source, all full windows,
maximizing ties, positive outgoing weights, actual multiplicities and
legal individual upper heights. Impose the additional restriction on
the originally supplied exponent

$$
\boxed{\eta<\eta_D(\Theta):=
\frac{2-\min\{\Theta,7/10\}}3.}
\tag{FHA1}
$$

For $\Theta\ge7/10$, including $\Theta=1$, this reads
$\eta<13/30$. For $\Theta<7/10$, it reads
$\eta<(2-\Theta)/3$. The original condition $1-\Theta<\eta<1/2$
is retained; no supplied parameter is reselected. This is a
`repo-derived` paper application of the existing Ingham and
[Guth--Maynard fixed-real-part density inputs](../Analytic/guthmaynard2024largevalues.md#the-zero-density-input-for-cumulative-contributions),
the retained positive source height, LHA2 and NE6. It introduces no
new density theorem, literature-priority claim or Lean verification.

Write $M=M_X=X^\mu\log X$, $\mu=1/2-\eta$, $L=L_X$ and retain
NE1--NE6's same lower cut

$$
H_{B,X}=\max\{51,\sqrt B/M\}.
$$

The original source gives $\sqrt{b_X}/M\to\infty$, so uniformly
over all actual cores this equals $\sqrt B/M$ eventually and is
below every original legal $\tau\asymp\sqrt B$. No upper clock
ceiling is used. Define the entire actual high-frequency allowance

$$
\mathcal R_X^{\rm high}
=2\sum_{i<m}\delta_i
 \sum_{H_{B_i,X}<\gamma\le\tau_i}
 m_\rho|c_{B_i,a}(\rho)|,
\qquad
c_{B,a}(\rho)=s_BF_B(\rho)-aB^{\rho-1/2}/\rho.
$$

There is no restriction on the real part in this definition. The
complete coefficient and original upper masks remain unchanged.

### The compact middle class has a strict source-height exponent gap

Set $u=1-\eta$ and $v=\min\{\Theta,\sigma_\circ\}$, with NE1's
$\sigma_\circ=9999/10000$. The actual middle class is
$u<\beta<\sigma_\circ$; its upper endpoint also respects
$\beta\le\Theta$. If $u\ge v$, that class is empty and its allowance
is zero. Otherwise work on the fixed compact interval $[u,v]$.

Reuse the published density exponents, with their existing
reciprocal-height consequence at finitely many fixed real parts:

$$
D(\sigma)=
\begin{cases}
3(1-\sigma)/(2-\sigma),&\sigma\le7/10,\\
15(1-\sigma)/(3+5\sigma),&\sigma\ge7/10,
\end{cases}
\qquad E(\sigma)=\sigma-1+\frac{D(\sigma)}2.
$$

The two exponents agree at $7/10$, and $0<D<1$ on $[u,v]$.
Moreover

$$
\frac{1-\sigma}{D(\sigma)}=
\begin{cases}
(2-\sigma)/3,&\sigma\le7/10,\\
(3+5\sigma)/15,&\sigma\ge7/10.
\end{cases}
$$

FHA1 therefore gives
$\mu D(\sigma)-E(\sigma)=1-\sigma-\eta D(\sigma)>0$ throughout
this interval. Since also $\mu D>0$, compactness gives a fixed
positive gap

$$
r_0:=\min_{\sigma\in[u,v]}
 \{\mu D(\sigma)-\max(E(\sigma),0)\}>0.
\tag{FHA2}
$$

Choose a fixed $q>0$ with $4q\le r_0$ and
$\max_{[u,v]}E+q<1/2$. Use finitely many disjoint half-open bins,
closing the last endpoint when needed, with $7/10$ as an endpoint
whenever it lies inside the interval. Choose the maximum width
$\omega$ and one fixed density loss $\epsilon>0$ so that
$\omega+\epsilon/2\le q$ and
$D(\sigma_j)+\epsilon<1$ at every left endpoint. No uniformity of
a moving-real-part $o(1)$ is assumed.

Let $r_{X,j}^{\rm mid}(B,\tau)$ be twice the absolute complete
coefficient sum in one actual middle-class bin. Write
$D_j=D(\sigma_j)$ and $E_j=E(\sigma_j)$. DH3's existing bound
$|c_{B,a}(\rho)|\le(a+2)B^{\beta-1/2}/\gamma$ and the existing
reciprocal-height estimate give

$$
\begin{aligned}
r_{X,j}^{\rm mid}(B,\tau)
&\ll B^{\sigma_{j+1}-1/2}
 H_{B,X}^{D_j-1+\epsilon}\\
&\le M^{1-D_j}B^{E_j+q}.
\end{aligned}
$$

The favorable $M^{-\epsilon}$ is discarded only after the exact
substitution $H_{B,X}=\sqrt B/M$. Extending the positive
reciprocal-height sum above $\tau$ is an upper bound for the same
finite mask; it changes no original height assignment.

For $B\le X$, use
$B^{E_j+q}\le X^{\max(E_j,0)+q}$, giving

$$
\frac{r_{X,j}^{\rm mid}(B,\tau)}M
\ll X^{-\mu D_j+\max(E_j,0)+q}(\log X)^{-D_j}
\ll X^{-3q}.
$$

Here $E_j$ can be negative near one; replacing $B^{E_j}$ by
$X^{E_j}$ would have the wrong direction. For $B>X$, retain
$h_X(B)=(d/2)X^{-\eta}\sqrt B\log B$ from HIA2. Since
$E_j+q<1/2$,

$$
\begin{aligned}
\frac{r_{X,j}^{\rm mid}(B,\tau)}{h_X(B)}
&\ll X^\eta M^{1-D_j}
 \frac{B^{E_j+q-1/2}}{\log B}\\
&\ll X^{-\mu D_j+E_j+q}(\log X)^{-D_j}
\ll X^{-3q}.
\end{aligned}
$$

Both parts of the original core source are retained. Summing the
fixed finite bins and actual positive outgoing weights proves, with
$\mathscr H_X=\sum_{i<m}\delta_i h_X(B_i)$,

$$
\boxed{\mathcal R_X^{\rm mid}
\le C X^{-q}[M_XL_X+\mathscr H_X].}
\tag{FHA3}
$$

An empty middle class satisfies this with zero allowance.

### Combine disjoint actual classes inside the same complete response

Partition the high-frequency mask into
$\beta\le1-\eta$, $1-\eta<\beta<\sigma_\circ$, and
$\beta>1-\eta$, $\beta\ge\sigma_\circ$. Bound these by LHA2's
entire lower-real-part allowance, FHA3 and NE6, respectively. The
actual classes are disjoint even when $1-\eta\ge\sigma_\circ$;
that case has no middle class. Consequently

$$
\boxed{
\begin{aligned}
\mathcal R_X^{\rm high}
&\le\left(\frac C{\log X}+CX^{-q}\right)
 [M_XL_X+\mathscr H_X]+o(M_XL_X),\\
\frac{\mathcal R_X^{\rm high}}{\mathcal G_X}&\longrightarrow0.
\end{aligned}}
\tag{FHA4}
$$

The second line spends only HIA3's already retained
$\mathscr H_X\le\mathcal G_X+O_a(L_X)$ and JM7's
$\mathcal G_X\ge(R_\eta/2)M_XL_X$ eventually. It does not assume
$\mathscr H_X=O(M_XL_X)$ or assert an absolute $o(M_XL_X)$ bound
for the whole high-frequency allowance.

Deleting precisely this full high-frequency real contribution from
the original head retains its lower margin, up to any fixed
positive loss, by HC2 and FHA4. If the entire LHA lower-real-part
class is deleted as well, charge it once and add only the disjoint
middle and near-one high-frequency classes. The exact remaining head
then has mask

$$
\boxed{\beta>1-\eta,\qquad
0<\gamma\le H_{B_i,X},\qquad
S_X^{\rm rem}(\boldsymbol\tau)
\ge(R_\eta-\varepsilon_0)M_XL_X\quad\text{eventually}}
\tag{FHA5}
$$

for every fixed $\varepsilon_0>0$, on every original qualifying full
window, maximizing-tie assignment and legal individual height
assignment satisfying FHA1. This removes the middle high-frequency
class left after LHA3 and NE6 at the same lower cut. AHA4 retains its
own smaller cut $\sqrt B/M_X^{19/10}$ on its narrower real-part band
and supplied-parameter range; it is not replaced by a stronger claim
at that smaller cut.

Every fixed actual zero with $\beta>1-\eta$ still eventually lies
in FHA5's remaining low-frequency mask. No sufficient signed upper
estimate for that head or favorable cofinal window is supplied.
All-integer Robin and RH remain unproved. The bounds are not claimed
uniform as FHA1 approaches equality or the supplied parameters vary.


## One common polynomial-height raw head retains the original response

Keep FHA1's restriction on the originally supplied exponent and all of
JM1--JM7's original conditional source:

$$
1-\Theta<\eta<\min\{1/2,\eta_D(\Theta)\},\qquad
\eta_D(\Theta)=\frac{2-\min\{\Theta,7/10\}}3.
$$

Every original full window, maximizing tie, positive outgoing weight
$\delta_i$, actual zero multiplicity and complete coefficient
$c_{B_i,a}(\rho)$ remains. Write $M=M_X=X^\mu\log X$,
$\mu=1/2-\eta>0$, $L=L_X$, $u=1-\eta$ and
$h_X(B)=(d/2)X^{-\eta}\sqrt B\log B$,
$\mathscr H_X=\sum_{i<m}\delta_i h_X(B_i)$.
Define one common summation cut and the finite raw head

$$
\begin{aligned}
T_X&=\max\{51,X^\eta\},\\
\mathcal P_X
&=2\operatorname{Re}
 \sum_{\substack{0<\gamma\le T_X\\\beta>u}}
 m_\rho\sum_{i<m}\delta_i c_{B_i,a}(\rho).
\end{aligned}
\tag{CPH1}
$$

The original legal $\tau_i\asymp\sqrt{B_i}$ are retained in the
explicit formulas. The cut $T_X$ need not be below every $\tau_i$;
it is not claimed CHJ-admissible. Both shortening and extension of
the original masks are paid below before exchanging the finite sums.

This is a `repo-derived` paper application of the same published
Ingham, Guth--Maynard and Ford density inputs, the
Vinogradov--Korobov zero-free region, and the existing coefficient
and source-height accounts. Their proofs are reused, not reproved.
There is no new density theorem, literature-priority claim or Lean
verification.

### Pay the right-part truncation at the common cut

For each original core and legal height put

$$
r_X^{\rm cut}(B,\tau)
=2\!\sum_{\substack{T_X<\gamma\le\tau\\\beta>u}}
 m_\rho|c_{B,a}(\rho)|.
$$

If $u<v:=\min\{\Theta,\sigma_\circ\}$, reuse FHA2's fixed
compact interval $[u,v]$, its density exponent $D(\sigma)$,
$E(\sigma)=\sigma-1+D(\sigma)/2$ and positive gap $r_0$.
The actual middle class has $u<\beta<\sigma_\circ$ and respects
$\beta\le\Theta$; if empty its allowance is zero. On this compact
interval,

$$
1-\sigma-\eta D(\sigma)\ge r_0,
\qquad
\mu-\max\{E(\sigma),0\}>r_0.
$$

The first follows from FHA2 since $\max(E,0)\ge E$; the second
uses $D<1$. Choose one fixed finite bin partition, respecting the
$7/10$ junction and actual endpoint masks, and a fixed density loss
$\epsilon>0$. Choose their maximum width $\omega$ and loss small
enough that $D_j+\epsilon<1$,
$\omega+\eta\epsilon<r_0/2$,
$\omega+\epsilon/2<r_0/2$ and $v+\omega<1$.
DH3's full-coefficient and reciprocal-height bounds then give

$$
r_{X,j}^{\rm cut}(B,\tau)
\ll B^{\sigma_j+\omega-1/2}
 X^{\eta(D_j-1+\epsilon)}.
$$

For $B\le X$, division by $M$ bounds this by
$C X^{\sigma_j-1+\eta D_j+\omega+\eta\epsilon}/\log X$.
For $B>X$, division by $h_X(B)$ gives the same upper bound,
since $\sigma_j+\omega-1<0$. Thus the fixed finite middle-bin
sum is at most $CX^{-q}[M+h_X(B)]$ for some fixed $q>0$.
No upper clock ceiling or $B\asymp X$ assumption is used.

For the remaining right-part class $\beta\ge\sigma_\circ$,
reuse NE2 and the finite actual-mask cap NE3. Its positive layer
bound is NE4 with $T_X$ in place of the lower cut. Only the
actual layers with $\sigma\le1-\nu_B$ occur. For $B\le X$,

$$
\frac{B^{\sigma-1/2}X^{-\eta\sigma}}M
=\frac{(B/X)^{\sigma-1/2}}
 {\log X}X^{-(1-\eta)(1-\sigma)}
\le\frac{\exp[-(1-\eta)\nu_X\log X]}{\log X}.
$$

Here $\nu_B\ge\nu_X$ beyond one common start. NE2's logarithmic
factor and the layer's $\log B$ cost are bounded by a fixed power
of $\log X$, which this exponential absorbs. For $B>X$,

$$
\frac{B^{\sigma-1/2}X^{-\eta\sigma}}{h_X(B)}
=\frac2{d\log B}
 \exp[-(1-\sigma)(\log B-\eta\log X)]
\le\frac2{d\log B}
 \exp[-(1-\eta)\nu_B\log B].
$$

Again the exponential absorbs the fixed logarithmic costs,
uniformly for $B\ge X$. An empty actual edge mask contributes
zero. This proves, with some $e_X\to0$ depending only on the
original fixed parameters,

$$
\sum_{i<m}\delta_i r_X^{\rm cut}(B_i,\tau_i)
\le e_X[M_XL_X+\mathscr H_X].
\tag{CPH2}
$$

The zero-free cap is used only for the actual finite mask below
$\tau_i$. Infinite reciprocal-height tails remain positive upper
bounds on its layers, without imposing that cap on other zeros.

### Pay extensions above smaller original legal heights

Define the disjoint extension allowance

$$
r_X^{\rm ext}(B,\tau)
=2\!\sum_{\substack{\tau<\gamma\le T_X\\\beta>u}}
 m_\rho|c_{B,a}(\rho)|.
$$

The original legal-height lower bound gives $\tau\ge\sqrt B/8$
eventually. Thus a nonempty extension requires
$B<64X^{2\eta}<X$ eventually. All original core clocks escape
uniformly, so the same lower-height and density starts apply.

On a nonempty compact middle class the same fixed bins give

$$
r_{X,j}^{\rm ext}(B,\tau)
\ll B^{\sigma_j+\omega-1/2}
       \tau^{D_j-1+\epsilon}
\ll B^{E_j+\omega+\epsilon/2}.
$$

Since $B\le X$, its ratio to $M$ is at most
$C X^{\max(E_j,0)+\omega+\epsilon/2-\mu}/\log X=o(1)$,
by the second compact gap above. This also keeps the correct
inequality direction when $E_j<0$.

For the near-one extension, use NE2 at $\tau$ and the full layer
integral only up to $1$. No finite-mask zero-free cap from the
old height is imposed on the newly added zeros. Uniformly in
$\sigma_\circ\le\sigma<1$,

$$
B^{\sigma-1/2}\tau^{-\sigma}
\le 8^\sigma B^{-(1-\sigma)/2}\le8.
$$

The boundary layer and integral therefore cost
$O_a((\log B)^{16})=O_a((\log X)^{16})=o(M)$, since $\mu>0$
is fixed. Consequently

$$
\sum_{i<m}\delta_i r_X^{\rm ext}(B_i,\tau_i)
=o(M_XL_X).
\tag{CPH3}
$$

This extension is a finite sum of the original complete
coefficients. It changes no explicit-formula height or error term.

### Aggregate the same actual zero set before taking its sign

LHA2 already pays the entire inclusive class $\beta\le u$ in
the original heads. The remaining right-part head differs from
CPH1 by precisely the cut and extension masks above. Each term is
charged once. Positivity of the unchanged weights, HC2, CPH2 and
CPH3 give

$$
|\mathcal P_X-\mathcal G_X|
\le\left(\frac C{\log X}+e_X\right)
 [M_XL_X+\mathscr H_X]+o(M_XL_X)+O_a(L_X).
$$

Reuse HIA3's $\mathscr H_X\le\mathcal G_X+O_a(L_X)$ and JM7's
$\mathcal G_X\ge(R_\eta/2)M_XL_X$ eventually. It follows that

$$
\boxed{
\frac{\mathcal P_X}{\mathcal G_X}\longrightarrow1,
\qquad
\forall\varepsilon_0>0\quad
\mathcal P_X\ge(R_\eta-\varepsilon_0)M_XL_X
\quad\text{eventually}.}
\tag{CPH4}
$$

Uniformity retains every original full window, maximizing tie and
admissible individual height assignment satisfying FHA1, including
$\Theta=1$. The common raw head itself no longer depends on the
height assignment. The error is source-relative; an absolute
$o(M_XL_X)$ error for the whole comparison is not asserted.

DH4's raw common head remains under its narrower DH1 hypotheses
and clock ceiling, with its own absolute error. MT7's common head
retains its smoothed coefficients and maximum-core-dependent cut.
CPH1--CPH4 instead provide one raw polynomial-height actual zero
set without a subunit zero-supremum or clock ceiling, paying the
extensions when the cut exceeds some original heights. They do not
replace DH4's stronger absolute comparison on its own scope.

Every fixed actual zero with $\beta>1-\eta$ eventually belongs
to this growing common set. The original outgoing weights and
complete complex coefficients must be aggregated on that same
set. No sufficient signed upper estimate for their aggregate,
favorable cofinal window, all-integer Robin bound or RH proof is
supplied. The remaining task is the signed common-head estimate,
not another high-frequency or lower-real-part payment.


## The complete response has a source-relative change from core to total clock

Keep JM1--JM7's original conditional RH-failure source and all its
full windows, maximizing ties and positive outgoing weights. Add only
the restriction on the originally supplied exponent

$$
\boxed{1-\Theta<\eta<13/30,\qquad \Theta\le1.}
\tag{WRC1}
$$

No supplied parameter is reselected. Keep $0<a<5\kappa/8$,
$M=M_X=X^{1/2-\eta}\log X$, $L=L_X$ and the complete response

$$
G_a(x)=s_x\int_x^\infty E(v)k(v)dv-\frac{aE(x)}{\sqrt x},
\quad s_x=\sqrt x\log x,\quad E=x-\psi.
$$

Both the full future integral and the original compensation remain.
For each original label write $A=B+t$, $t=\log p$ and
$u=N_A^{\rm str}$, so $K(A)=B$. Define
$\Delta=K(A)-K(B)=B-K(B)\ge0$ and $Q=K-\psi$ as before.
The same symbols $\Delta$ and $L$ here do not denote the
zero-supremum defect or the local $\log B$.

The following is a `repo-derived` paper application of AO1's exact
account, JM1's coercivity, the existing Guth--Maynard short-interval
input consumed in SI2 and JM6, and the already used quadrature.
There is no new prime-counting theorem, literature-priority claim
or Lean verification. In particular SI1's global clock ceiling is
not extended: the count is used only on bounded $B/X$, and the
remaining original cores are paid by their own positive height.

### Keep the full response in the exact recentering identity

Fix once $C>8/5$ with $aC<1$. CR43--CR44, JM1, JM7 and the
uniform $\chi_{p,u}\to1$ give fixed $c_1,c_2,c_3>0$ and $C_1$
with, at one common source start,

$$
\begin{aligned}
\Delta&\le Ct+C_1\sqrt B,\qquad |Q(v)|\le H_Q\sqrt v,\\
G_a(B)&\ge c_1h_X(B)+c_2\frac t{\sqrt B}-C_1,
\quad h_X(B)=\frac d2X^{-\eta}\sqrt B\log B,\\
G_a(B)&\ge c_3M.
\end{aligned}
\tag{WRC2}
$$

Thus $G_a(B)>0$ and
$h_X(B)+t/\sqrt B+1\ll G_a(B)$ uniformly. This consumes the
same complete response, not a second copy of its height or lag.
All original core clocks escape uniformly, and CR17 supplies
$\rho_X:=\sup t/B\to0$.

Put $q=s_B/s_A$ and $c=B\log B/(A\log A)$. AO1 gives exactly

$$
qG_a(A)-G_a(B)
=\frac a{\sqrt B}[\Delta-t+(1-c)t+Q(B)-cQ(A)]
 -I_{\rm past},
\qquad
I_{\rm past}=s_B\int_B^A E(v)k(v)dv.
\tag{WRC3}
$$

No sign or smallness has been assigned to the full recentering
error in obtaining this identity. In particular the local $E(B)$
term is not dropped before the subtraction.

For $B\le v\le A$, monotonicity of the strict inventory gives
$0\le v-K(v)\le t+\Delta$. WRC2 and $A\le2B$ therefore give
$|E(v)|\le C_2(t+\sqrt B)$. Since $s_Bk(B)\le2B^{-3/2}$,

$$
|I_{\rm past}|\le C_3\frac tB
 \left(\frac t{\sqrt B}+1\right)=o(G_a(B))
$$

uniformly over the original labels and ties. Also $q\to1$,
$0\le1-c\le2t/B$ and
$|Q(B)-cQ(A)|/\sqrt B=O(1)$. By WRC2, every term on WRC3's
right except $(\Delta-t)/\sqrt B$ is thus $o(G_a(B))$.
This controls the whole improper future account through an exact
identity; its absolute magnitude is not separately assumed small.

### Pay the remaining increment error on both parts of the original source

Fix a finite $R>1$. WRC1 permits a single fixed exponent
$17/30<r<\min\{1-\eta,99/100\}$. On all original cores
$B\le RX$, the unchanged floor
$t\ge\ell_X=(d/8)X^{1-\eta}\log X$ gives

$$
\frac{t}{B^r}\ge\frac{d}{8R^r}
 X^{1-\eta-r}\log X\longrightarrow\infty.
$$

Together with CR17's uniform $t/B\to0$, this is precisely the
length condition needed by SI2's already proved fixed-block
application of the published uniform prime-count asymptotic.
The complete endpoint correction $K-\theta_1=O(\sqrt x)$ remains.
Consequently, for this fixed $R$,

$$
\sup_{\substack{\text{original labels and ties}\\B\le RX}}
\frac{|\Delta-t|}{t}\longrightarrow0.
\tag{WRC4}
$$

The $O(\sqrt B)$ endpoint allowance is negligible because
$t/B^r\to\infty$ and $r>1/2$. Constants may depend on the fixed
$R$ and $r$; no count uniform in a growing $R$ is asserted.
Using WRC2 now pays $|\Delta-t|/\sqrt B=o(G_a(B))$ on this
bounded-ratio part.

For the retained part $B>RX$, use only WRC2's capacity and height.
Since $t\le2\ell_X$, $B>X$ and $\log B\ge\log X$,

$$
\begin{aligned}
\frac{|\Delta-t|}{\sqrt B\,G_a(B)}
&\ll\frac{t/\sqrt B+1}{G_a(B)}\\
&\ll\frac{t/\sqrt B}{h_X(B)}+\frac1M\\
&\ll\frac{X\log X}{B\log B}+\frac1M
\le\frac{C_4}{R}+\frac{C_5}{M}.
\end{aligned}
\tag{WRC5}
$$

To obtain a requested positive precision, first fix $R$ large
enough and then take the common start for WRC4 and WRC5. No
source configuration is removed or made comparable to $X$.
This proves $|\Delta-t|/\sqrt B=o(G_a(B))$ uniformly over
all original cores. WRC3, WRC2 and $q\to1$ therefore yield

$$
\boxed{\sup_{\text{original labels and ties}}
 \frac{|G_a(A)-G_a(B)|}{G_a(B)}\longrightarrow0.}
\tag{WRC6}
$$

There is no absolute $o(M)$ claim for the pointwise recentering
error, nor an assumption that $G_a(B)=O(M)$.

### The original weighted response equals its visited total-clock integral relatively

Define the original core sum and the total-clock sum with the same
tags and outgoing weights:

$$
\mathcal G_X=\sum_{i<m}\delta_iG_a(B_i),\qquad
\mathcal G_X^{A}=\sum_{i<m}\delta_iG_a(A_i).
$$

Positivity in WRC2 permits summing the pointwise absolute allowances
before using any sign. Thus
$|\mathcal G_X^A-\mathcal G_X|=o(\mathcal G_X)$ uniformly in all
tie assignments on each original full window.

Use AO5's existing bounded variation of the complete response,
AO6's same total-clock selector and the already used Dragomir
quadrature, now for $G_a$ itself rather than its clipped readout.
The mesh-times-variation error is at most

$$
C_a\varepsilon_X^{\rm lab}\sqrt{R_X}\log(eR_X)=o(1).
$$

All original endpoint tie tags are retained. PT10/PG9's exact
pushforward is supported on the actual visited set $D_X$, with
$|D_X|=L_X$; no skipped interval or independent sampling law is
inserted. It follows that

$$
\boxed{
\mathcal I_X^A:=\int_{D_X}G_a(v)dv,
\qquad
\frac{\mathcal G_X^A}{\mathcal G_X}\longrightarrow1,
\qquad
\frac{\mathcal I_X^A}{\mathcal G_X}\longrightarrow1.}
\tag{WRC7}
$$

These statements retain the original full windows and every
maximizing tie, and include $\Theta=1$ under WRC1. They pay the
full core-to-total-clock change that AO4--AO6 did not assert small;
CQ5 continues to describe the separate atomic core occupation.
The comparison is source-relative. It does not strengthen DH4's
absolute comparison or identify $D_X$ with its whole enclosing
interval.

WRC1 implies FHA1, so the existing raw common head also satisfies
$\mathcal P_X/\mathcal I_X^A\to1$ by CPH4 and WRC7. Neither this ratio nor WRC7 gives a signed upper bound for
$\mathcal I_X^A$. The remaining comparison is on the same selected
set, including its original omissions and full future response.
No favorable cofinal sequence, all-integer Robin bound or RH proof
is supplied. No uniformity as $\eta\uparrow13/30$ is asserted.

## The complete future integral has a full-range common head at the total clock

Keep CR17--CR20's original conditional RH-failure source, every
original full window, maximizing tie and positive outgoing weight,
and the originally supplied parameters

$$
1-\Theta<\eta<1/2,\qquad \Theta\le1,\qquad
M=X^{1/2-\eta}\log X,\qquad L=t_m-t_0.
\tag{FCT1}
$$

The original fixed positive compensation parameter $a$ is unchanged.
Use the already defined complete future account from AO1,

$$
\mathsf H(x)=s_x\int_x^\infty E(v)k(v)dv,
\qquad s_x=\sqrt x\log x,\qquad E=x-\psi,
\qquad \mathsf H(x)=G_a(x)+\frac{aE(x)}{\sqrt x}.
$$

This is the original uncompensated account from CR19--CR23 and
MB2, not a new RH criterion or a claim that the local compensation
is negligible. It retains all prime powers and the infinite endpoint.
The additional source application transports this account to the
actual total clock and pays a common raw finite zero mask throughout
FCT1. It reuses CR19, AO1--AO6, the original degree-two coefficient
and the classical zero count. No new PNT, zero-density theorem,
literature-priority or Lean verification is asserted.

### Transport the whole future account without a short-interval asymptotic

At each original label retain $A=B+t$, $u=N_A^{\rm str}$,
$K(A)=B$, $\Delta=B-K(B)$ and $Q=K-\psi$.
CR17--CR19 and CR43--CR44 give fixed positive constants with

$$
\begin{aligned}
\mathsf H(B)&\ge h_X(B)+\chi_{p,u}\frac t{\sqrt B},
&h_X(B)&=\frac d2X^{-\eta}\sqrt B\log B,
&\chi_{p,u}&\longrightarrow1,\\
0\le\Delta&\le Ct+C_1\sqrt B,
&|Q(v)|&\le H_Q\sqrt v,
&\rho_X:=\sup\frac tB&\longrightarrow0.
\end{aligned}
$$

The fixed capacity coefficient can be any original $C>8/5$.
JM2--JM3's scalar coercivity argument applies to the single
unabridged CR19 account: the height excludes $B/X\to\infty$ and
the lag excludes $B/X\to0$ for bounded $\mathsf H(B)/M$.
On a fixed compact positive range of $B/X$, $\log B/\log X\to1$.
For every fixed requested $\epsilon>0$, its same AM--GM calculation
therefore gives

$$
\mathsf H(B)\ge(d/2-\epsilon)M,
\qquad h_X(B)+t/\sqrt B+1\ll\mathsf H(B)
\tag{FCT2}
$$

eventually, uniformly in every original label and tie. No attained
minimizing core ratio or bounded normalized response is assumed.

Put $q=s_B/s_A$. Splitting the same full integral, as in AO1, gives
exactly

$$
q\mathsf H(A)-\mathsf H(B)
=-I_{\rm past},\qquad
I_{\rm past}=s_B\int_B^A E(v)k(v)dv.
$$

For $B\le v\le A$, monotonicity and $K(A)=B$ imply
$0\le v-K(v)\le t+\Delta$. Thus
$|E(v)|\ll t+\sqrt B$ and $s_Bk(B)\le2B^{-3/2}$ give

$$
|I_{\rm past}|\ll\frac tB\left(\frac t{\sqrt B}+1\right)
=o(\mathsf H(B)).
$$

Since $q\to1$, FCT2 yields the uniform full-range transport

$$
\boxed{\sup_{\text{original labels and ties}}
\frac{|\mathsf H(A)-\mathsf H(B)|}{\mathsf H(B)}\longrightarrow0.}
\tag{FCT3}
$$

Only the complete future account is transported in FCT3.
The term $(\Delta-t)/\sqrt B$ in WRC3 belongs to the retained
local compensation; FCT3 neither bounds it nor extends WRC6
for $G_a$ beyond its stated exponent range. No short-interval
asymptotic is used here.

### Retain the actual visited set and original quadrature

Write

$$
\mathcal H_X^B=\sum_{i<m}\delta_i\mathsf H(B_i),\qquad
\mathcal H_X^A=\sum_{i<m}\delta_i\mathsf H(A_i),\qquad
\mathcal I_X^H=\int_{D_X}\mathsf H(v)dv.
$$

FCT2--FCT3 and the original positive weights give
$\mathcal H_X^A/\mathcal H_X^B\to1$ and
$\mathcal H_X^B\ge(d/2-\epsilon)ML$ eventually.
AO5's complete-integral variation calculation, with the local
compensation absent from this readout, gives
$\operatorname{Var}\mathsf H\ll\sqrt{R_X}\log(eR_X)$ on the
same total-clock range. Use AO6's tagged monotone selector and
original label mesh, and PT10/PG9's exact pushforward onto $D_X$.
The existing quadrature allowance is
$O(\varepsilon_X^{\rm lab}\sqrt{R_X}\log(eR_X))=o(1)$.
Consequently

$$
\boxed{\frac{\mathcal I_X^H}{\mathcal H_X^B}\longrightarrow1,
\qquad \frac{\mathcal H_X^A}{\mathcal H_X^B}\longrightarrow1.}
\tag{FCT4}
$$

Here $D_X$ is exactly the original visited set, with every skipped
switch interval retained as an omission. AO5--AO6's coarse ceiling
and mesh are still used for quadrature. This does not make the atomic
core occupation Lebesgue measure or impose independent sampling.

### Pay both deleted zero sectors on one common raw height

Use the existing full original formula from MB2 and HC1 at $x=A_i$:

$$
\mathsf H(x)=2\operatorname{Re}\sum_{\gamma>0}
 m_\rho s_xF_x(\rho)+r_x,\qquad
|s_xF_x(\rho)|\le2x^{\beta-1/2}/\gamma^2,
\qquad r_x=O(x^{-1/2}).
$$

It is absolutely convergent for each actual $x$ and retains its
original elementary correction. In particular no conditionally
convergent compensated $1/\rho$ series is substituted. Set

$$
T_X=\max\{51,X^\eta\log X\},\qquad
\mu=1/2-\eta>0.
$$

The classical reciprocal-square zero count, used already in MB2
and BH3, pays the whole suffix, with all real parts and
multiplicities:

$$
2\sum_{\gamma>T_X}m_\rho|s_xF_x(\rho)|
\ll\frac{\sqrt x\log(eT_X)}{T_X}.
$$

At every actual $x=A_i$, FCT2--FCT3 imply
$h_X(x)\ll\mathsf H(x)$, $M\ll\mathsf H(x)$ and
$\log x\gg_\eta\log X$. Therefore the last bound, divided by
$\mathsf H(x)$, is $O_\eta(1/\log X)$.
For the disjoint lower-real-part class in the remaining finite head,

$$
2\sum_{\substack{0<\gamma\le T_X\\\beta\le1-\eta}}
 m_\rho|s_xF_x(\rho)|\ll x^\mu.
$$

If $x\le X$, divide by $\mathsf H(x)\gg M$; if $x>X$,
divide by $\mathsf H(x)\gg X^{-\eta}\sqrt x\log x$.
Both give $O_\eta(1/\log X)$. The elementary correction is
uniformly $o(\mathsf H(x))$ since all actual clocks escape and
$M\to\infty$. These are absolute payments for the two stated
sectors, relative to this same positive response.

Define the one common actual raw head

$$
\mathcal P_X^H=2\operatorname{Re}
\sum_{\substack{0<\gamma\le T_X\\\beta>1-\eta}}
m_\rho\sum_{i<m}\delta_i s_{A_i}F_{A_i}(\rho).
$$

Summing the paid positive absolute bounds with the unchanged weights
gives, throughout FCT1,

$$
\boxed{\frac{\mathcal P_X^H}{\mathcal H_X^B}\longrightarrow1,
\qquad \frac{\mathcal P_X^H}{\mathcal I_X^H}\longrightarrow1.}
\tag{FCT5}
$$

In particular every fixed requested $\epsilon>0$ has

$$
\boxed{\mathcal P_X^H\ge(d/2-\epsilon)M_XL_X
\quad\text{eventually on every original full window and tie}.}
\tag{FCT6}
$$

The common height is only a raw summation cut for the absolutely
convergent original degree-two formula. No CHJ admissibility or
common legal explicit-formula height is asserted. It includes
$\Theta=1$ on the entire originally supplied $\eta<1/2$ range,
without a clock-ratio ceiling or a prime-counting restriction.
The original coarse quadrature ceiling remains as specified above.

CR21's uncompensated account and its signed upper obligation were
already present. FCT3--FCT5 supply the additional full-range clock
transport, actual-visited-integral comparison and common finite-mask
payment; they do not reclassify those existing accounts as new.
The remaining low-frequency head has its actual phases, complete
$F_{A_i}$ coefficients, original weights and multiplicities. Every
fixed zero with $\beta>1-\eta$ eventually remains in it.
No strict signed upper on that head or $\mathcal I_X^H$, favorable
cofinal sequence, all-integer Robin bound or RH proof is supplied.
FCT3--FCT5 do not assert equality with the compensated sums, an
absolute $o(M_XL_X)$ transport error, or uniformity as $\eta\uparrow1/2$.


## The actual contact set excludes primes and pays both energy bulk terms

Reuse PG1, CQ1, AO5--AO6 and FCT1--FCT5 on their original conditional
RH-failure source, every original full window and maximizing tie, and
every originally fixed $1-\Theta<\eta<1/2$, including $\Theta=1$.
Keep the complete future account $\mathsf H=sJ$,
$J(x)=\int_x^\infty E(v)k(v)dv$, and the original positive compensation
parameter unchanged. This is a `repo-derived` paper application of the
existing integer-competitor interface, finite Stieltjes integration by
parts and the already used bounded-variation quadrature. It asserts no
new generic theorem, literature priority or Lean/kernel verification.

### Every active real clock avoids the first-prime measure

Suppose an original active core $u$ at a real parameter $t$ has total
clock $A=t+\log u=q$ prime. PG1 gives $q>11$, $q\le R_X$ and
$u=N_q^{\rm str}$. Its first $q$-layer reward per logarithmic mass is
strictly below $\lambda(q)$, since
$\log(1+1/q)<1/q$. Thus $q\nmid u$. PG1's existing headroom makes
$uq$ a literal legal competitor in the same finite core domain.
But its objective cost satisfies exactly

$$
f(q+\log q)-f(q)
=\log\left(1+\frac{\log(1+\log q/q)}{\log q}\right)
<\log(1+1/q)=W(uq)-W(u),
$$

by $\log(1+y)<y$ for $y>0$. Hence $\Phi_t(uq)>\Phi_t(u)$,
a contradiction. This argument treats every original real parameter
and every active tie, including all trace endpoints. Consequently,
with $\vartheta$ the first-power Chebyshev function,

$$
\boxed{D_X\cap\mathbb P=\varnothing,\qquad
\int_{D_X}g\,d\vartheta=0.}
\tag{CE1}
$$

The second equality holds for every real-valued test $g$ on this finite
range. It is an exact source selection constraint, not a statement
that $D_X$ has zero Lebesgue measure or that proper prime powers are
excluded. Real $t$ remains an interpolation parameter; $e^t$ is not
reclassified as an original prime label.

### Keep the exact boundary and proper-prime-power pairing

CQ1 makes $D_X$ a finite union of intervals, possibly with isolated
trace points. For Stieltjes integrals choose the half-open representative
$D_X^*=\bigcup_j(r_j,z_j]$ of its positive-length components. This
leaves $\int_{D_X}\mathsf H(x)dx$ unchanged. Keep this representative
explicitly at every proper-prime-power endpoint; no equality between
atom sums for different endpoint conventions is assumed.

The complete $\mathsf H$ is continuous and locally absolutely
continuous, whereas $E=x-\psi$ is right-continuous and locally of
bounded variation. Since $J'=-Ek$ almost everywhere, finite integration
by parts on each $(r_j,z_j]$ gives

$$
\int_{(r_j,z_j]}\mathsf H\,dE
=[E\mathsf H]_{r_j}^{z_j}
-\int_{r_j}^{z_j}\frac{s'}sE\mathsf H\,dx
+\int_{r_j}^{z_j}skE^2\,dx.
$$

Define the actual signed component boundary sum, proper-power pairing
and two bulk terms by

$$
\begin{aligned}
B_D&=\sum_j[E\mathsf H]_{r_j}^{z_j},&
C_D^{\rm pp}&=\sum_{\substack{p^k\in D_X^*\\k\ge2}}
 (\log p)\mathsf H(p^k),\\
M_D&=\int_{D_X}\frac{s'}sE\mathsf H\,dx,&
Q_D&=\int_{D_X}skE^2\,dx\ge0.
\end{aligned}
$$

Using $dE=dx-d\psi$ and CE1, with every proper power retained, yields

$$
\boxed{\mathcal I_X^H=B_D+C_D^{\rm pp}-M_D+Q_D.}
\tag{CE2}
$$

All occurrences of $\mathsf H$, including those at atoms and component
endpoints, retain their original infinite future integral.

### The same source pays both bulk terms relatively

Put $S_H=\mathcal H_X^B$, $b_X=\min_tB(t)$ and
$\epsilon_X^{\rm en}=\rho_X+b_X^{-1/2}\to0$, where
$\rho_X=\sup_t t/B(t)\to0$ on the whole real window as in PE2.
The original uniform floor and all-choice ordering supply $b_X\to\infty$;
no clock-ratio ceiling or bounded $S_H/(M_XL_X)$ is imposed.

Absolute value does not increase variation. Apply FCT4's existing
quadrature to $|\mathsf H|$ composed with the same tagged monotone
selector. FCT2--FCT3 give positivity only at the original labels,
which is sufficient for

$$
\int_{D_X}|\mathsf H|dx
=\sum_{i<m}\delta_i\mathsf H(A_i)+o(1)\sim S_H.
$$

For $h(t)=t/\sqrt{B(t)}$, monotonicity of the finite step function $B$
gives tagged variation at most $(2t_m+L_X)/\sqrt{b_X}$.
The original mesh $\varepsilon_X^{\rm lab}\le e^{-5\ell_X/12}$ and
$t_m\le2\ell_X$ therefore pay its quadrature as well. FCT2's same
coercivity gives

$$
\int_{t_0}^{t_m}\frac{t}{\sqrt{B(t)}}dt
=\sum_{i<m}\delta_i\frac{t_i}{\sqrt{B_i}}+o(1)\ll S_H,
\qquad L_X\ll S_H/M_X=o(S_H).
\tag{CE3}
$$

The absolute-value quadrature in this argument does not infer a sign
at every real point or proper-power atom.
For almost every $x=A(t)\in D_X$, reuse exactly
$E(x)=t+Q(x)$, $|Q(x)|\le H_Q\sqrt x$ and $A/B\to1$.
Since $s'/s=1/(2x)+1/(x\log x)$ and $s_xk(x)\le2x^{-3/2}$,

$$
\left|\frac{s'}sE\right|\ll\epsilon_X^{\rm en},
\qquad
0\le s_xk(x)E(x)^2
\ll\frac{t^2}{B^{3/2}}+\frac1{\sqrt B}
\ll\epsilon_X^{\rm en}\left(\frac t{\sqrt B}+1\right).
\tag{CE4}
$$

The exact visited-set pushforward, CE3 and absolute-value quadrature
now pay both complete bulk terms:

$$
\boxed{|M_D|+Q_D\ll\epsilon_X^{\rm en}S_H=o(S_H).}
\tag{CE5}
$$

In particular the positive square term was estimated, rather than
dropped from an upper comparison. CE2 and FCT4 give

$$
\boxed{\frac{|\mathcal I_X^H-B_D-C_D^{\rm pp}|}{S_H}\longrightarrow0,
\qquad
\frac{B_D+C_D^{\rm pp}}{\mathcal I_X^H}\longrightarrow1.}
\tag{CE6}
$$

CE1 supplies actual arithmetic information about the selected set;
CE5 pays both bulk components on that same source. Neither asserts
absolute $o(M_XL_X)$ error. Every component boundary and the proper-power
pairing in CE6 still need their joint signed upper estimate, with no
separate sign assigned to either term. The original FH weighted
first-prime test uses its different nonlocal weight and remains unpaid;
CE1 must not be substituted for a bound on that test. The original
compensated $G_a$, DR baseline/exterior account and its strict upper
obligation retain their stated scopes. No favorable cofinal sequence,
all-integer Robin inequality or RH proof is supplied.


## The proper-power pairing and stock boundary have a vanishing joint remainder

Reuse CE1--CE6 on their entire original conditional RH-failure source:
every original full window and active tie, every originally fixed
$1-\Theta<\eta<1/2$, including $\Theta=1$, and the complete future
$\mathsf H=s\int_x^\infty Ek$. Keep the original positive compensation
parameter unchanged. The estimate below is a `repo-derived` application
of the already used finite Stieltjes identity to the actual stock error;
it asserts no new generic theorem, literature priority or Lean verification.

### Keep the same stock and the same proper-power endpoint atoms

Use exactly CE2's representative $D_X^*=\bigcup_j(r_j,z_j]$. By
PG1 and PG9, $K$ is constant on every closed positive-length component,
including its actual trace endpoints. On each such component put

$$
Q=K-\psi,\qquad \tau(x)=x-K(x),\qquad
B_Q=\sum_j[Q\mathsf H]_{r_j}^{z_j},\qquad
B_\tau=\sum_j[\tau\mathsf H]_{r_j}^{z_j}.
$$

At each actual trace endpoint, $\tau$ is the original real source
parameter. In particular no endpoint value is replaced by a free clock
or an independently selected trace. The same $C_D^{\rm pp}$ from CE2
retains all proper-prime-power atoms in this explicit half-open set.

On each component $Q$ is right-continuous and locally of bounded
variation, with $dQ=-d\psi$. Since $\mathsf H$ is continuous and locally
absolutely continuous, finite Stieltjes integration by parts and CE1 give

$$
\begin{aligned}
B_Q
&=\int_{D_X^*}\mathsf H\,dQ+
  \int_{D_X}Q\mathsf H'\,dx\\
&=-C_D^{\rm pp}+\int_{D_X}Q\mathsf H'\,dx.
\end{aligned}
$$

Thus the exact joint identity, with the same endpoints on both sides, is

$$
\boxed{B_Q+C_D^{\rm pp}=\int_{D_X}Q\mathsf H'\,dx,
\qquad B_D=B_\tau+B_Q.}
\tag{SB1}
$$

### The original stock error controls this joint component

The complete future derivative is
$\mathsf H'=(s'/s)\mathsf H-skE$ almost everywhere. Reuse CE4's
$Q(x)=O(\sqrt x)$, $E(A(t))=t+Q(A(t))$, $A/B\to1$ and
$sk\ll x^{-3/2}$. For almost every $x=A(t)\in D_X$ these give

$$
|Q\mathsf H'|(A(t))
\ll\frac{|\mathsf H(A(t))|}{\sqrt{B(t)}}
   +\frac{t}{B(t)}+\frac1{\sqrt{B(t)}}.
$$

Use the same $b_X$, $\rho_X$ and
$\epsilon_X^{\rm en}=\rho_X+b_X^{-1/2}\to0$ as CE3--CE5.
The exact pushforward $A_\#dt=\mathbf1_{D_X}dx$ and the existing
bounds $\int_{D_X}|\mathsf H|dx\sim S_H$ and
$L_X\ll S_H/M_X$ now yield

$$
\boxed{\begin{aligned}
|B_Q+C_D^{\rm pp}|
&\ll b_X^{-1/2}S_H+\epsilon_X^{\rm en}L_X\\
&\ll\left(b_X^{-1/2}+
       \frac{\epsilon_X^{\rm en}}{M_X}\right)S_H=o(S_H).
\end{aligned}}
\tag{SB2}
$$

This bounds the proper-power and stock-boundary combination. This joint
estimate alone neither bounds the terms separately in absolute value nor
assigns either sign.
Every proper-power endpoint atom and the infinite future of every
$\mathsf H$ remain. No bound on $S_H/(M_XL_X)$ is imposed.

Combining SB1--SB2 with CE2 and CE5 gives the consequence

$$
\boxed{\begin{aligned}
|\mathcal I_X^H-B_\tau|
&\ll\left(\epsilon_X^{\rm en}+b_X^{-1/2}+
       \frac{\epsilon_X^{\rm en}}{M_X}\right)S_H=o(S_H),\\
\frac{B_\tau}{\mathcal I_X^H}&\longrightarrow1.
\end{aligned}}
\tag{SB3}
$$

SB2 supplies the quantitative joint remainder; SB3 is its consequence,
not an independent signed upper estimate or a new criterion. The actual
lag boundary $B_\tau$ still requires a strict signed upper on the
original qualifying source. These errors are relative to $S_H$, not
absolute $o(M_XL_X)$. The original nonlocal FH first-prime test remains
unpaid. No favorable cofinal sequence, equality with compensated $G_a$,
strict all-integer Robin inequality or RH proof is supplied.


## Original compensation pays a one-sided actual lag-boundary transfer

Keep the original conditional RH-failure source, every full window and
maximizing tie, every originally fixed $1-\Theta<\eta<1/2$ including
$\Theta=1$, and the original fixed $a>0$. Reuse PG1/PG9, PE2,
CQ5, FCT2--FCT4 and CE/SB on their stated domains. The complete future
$\mathsf H$ and CE2's explicit half-open representative $D_X^*$ remain
unchanged. This `repo-derived` paper application uses the existing
bounded-variation quadrature and finite component integration by parts;
it asserts no new generic theorem, literature priority or Lean verification.

### The original positive labels pay the integrated negative response

Write $\mathsf H_-(x)=\max\{-\mathsf H(x),0\}$ and

$$
q_X=\varepsilon_X^{\rm lab}\sqrt{R_X}\log(eR_X)=o(1).
$$

FCT4 retains the absolute $O(q_X)$ quadrature allowance, in addition
to its displayed relative comparisons. The negative-part map is
$1$-Lipschitz, so $\operatorname{Var}(\mathsf H_-)$ is at most
$\operatorname{Var}(\mathsf H)$. FCT2--FCT3 give
$\mathsf H_-(A_i)=0$ at every original label and allowed tie beyond
one common start. Apply that same tagged monotone-selector quadrature
and the exact visited-set pushforward to obtain

$$
\boxed{N_X:=\int_{D_X}\mathsf H_-(x)dx=O(q_X)=o(1).}
\tag{SB4}
$$

This is an integrated sign estimate. It does not assert pointwise
positivity at every real clock, proper-power atom or trace endpoint.
The mesh and coarse clock ceiling are exactly those already used in FCT4.

### Bound the lag-boundary error in one direction before taking a norm

On each original positive-length component, $\tau=x-K(x)$ is the
actual source parameter, with $\tau'=1$. Its endpoints and $B_\tau$
are exactly those of SB1. Using the complete derivative
$\mathsf H'=(s'/s)\mathsf H-skE$ gives the exact finite identity

$$
\mathcal I_X^H-B_\tau
=-\int_{D_X}\tau\frac{s'}s\mathsf H\,dx
 +\int_{D_X}\tau skE\,dx.
$$

The first coefficient is nonnegative and at most $C\rho_X$, where
$\rho_X=\sup_t t/B(t)\to0$. Hence its upper contribution is at most
$C\rho_XN_X$. For the other term, reuse $E(A(t))=t+Q(A(t))$,
$|Q(x)|\le H_Q\sqrt x$, $A/B\to1$ and $sk\ll x^{-3/2}$:

$$
\int_{D_X}\tau skE\,dx
\ll\int_{t_0}^{t_m}\left(\frac{t^2}{B(t)^{3/2}}+
                              \frac{t}{B(t)}\right)dt.
$$

Retain the original nonnegative credit

$$
V_X^K=\int_{t_0}^{t_m}\frac{\Delta(A(t))}{\sqrt{B(t)}}dt,
\qquad \Delta(A)=B-K(B)\ge0.
$$

PE2's existing two-case estimate bounds $t^2/B^{3/2}$ by one when
$t\le B^{3/4}$, and otherwise by
$(200/9)\rho_X\Delta(A)/\sqrt B$. Also
$\int t/B\,dt\le\rho_XL_X$. Thus, for a fixed source constant $C$,

$$
\boxed{\mathcal I_X^H
\le B_\tau+C\rho_XV_X^K+O(L_X)+O(\rho_Xq_X).}
\tag{SB5}
$$

This one-sided error bound imposes no ceiling on $S_H/(M_XL_X)$ or
$V_X^K/(M_XL_X)$. It does not replace SB3's distinct two-sided,
source-relative comparison by an absolute norm bound.

### Consume the original compensation once

Keep CQ5's original continuous account
$\mathcal J_X=\int_{t_0}^{t_m}G_a(B(t))dt$. PE2, with any fixed
$0<\epsilon<a$, says

$$
G_a(B(t))\le\frac{s_{B(t)}}{s_{A(t)}}\mathsf H(A(t))
 -(a-\epsilon)\frac{\Delta(A(t))}{\sqrt{B(t)}}+C_\epsilon.
$$

For $0<q\le1$, $q\mathsf H\le\mathsf H+\mathsf H_-$ for either
sign of $\mathsf H$. Since $s_B/s_A\le1$, SB4 and the same exact
pushforward therefore give

$$
\boxed{\mathcal J_X
\le\mathcal I_X^H-(a-\epsilon)V_X^K+O_\epsilon(L_X)+O(q_X).}
\tag{SB6}
$$

Combining SB5 and SB6 retains the correction to the credit coefficient:

$$
\boxed{\mathcal J_X
\le B_\tau-(a-\epsilon-C\rho_X)V_X^K
       +O_\epsilon(L_X)+O(q_X).}
\tag{SB7}
$$

No boundedness of the normalized credit is used to discard that correction.
For a fixed fraction, take $\epsilon=a/4$ and enlarge the common start
until $C\rho_X\le a/4$. CQ5 then transports this bound to every
original allowed tie assignment $\mathcal T$:

$$
\boxed{\begin{aligned}
\mathcal J_X&\le B_\tau-\frac a2V_X^K+O_a(L_X)+o(1),\\
\mathcal G_{X,\mathcal T}
&\le B_\tau-\frac a2V_X^K+O_a(L_X)+o(1).
\end{aligned}}
\tag{SB8}
$$

Because $M_X\to\infty$, the uncredited allowance in SB8 is absolute
$o(M_XL_X)$. The compensation is the existing fixed source credit;
this account and DR/BV/LC do not provide two independently spendable
copies of it. All original proper powers, gaps, ties, trace conventions
and infinite future endpoints remain.

SB4--SB8 pay the one-sided original compensated-source-to-boundary
transfer without a ceiling on its complete response. They do not extend
WRC's two-sided $G_a$ transport beyond its stated $\eta<13/30$ range,
identify $G_a$ with $\mathsf H$, or pay the nonlocal FH first-prime test.
The same-source signed boundary-minus-credit still needs its strict
upper against the original lower margin. No favorable cofinal sequence,
strict all-integer Robin inequality or RH proof is supplied.


## All real active contacts control the proper-power atom signs

Keep the original conditional RH-failure source, every full window and
active tie, and every originally fixed $1-\Theta<\eta<1/2$, including
$\Theta=1$. Reuse N1--N2, PG1/PG9, FCT1 and CE2's actual half-open
representative. The complete future $\mathsf H$, all proper powers and
trace endpoints remain. This `repo-derived` paper application uses the
existing unrestricted pressure and reserve identities; it asserts no
new generic theorem, literature priority or Lean verification.

### The endpoint envelope supplies height at every real parameter

Use the same finite integer-core envelope $V_X(t)$ from PG1, and put
$c_m=\log(1+1/p_m)\le e^{-\ell_X}$. N1--N2's exact correspondence
at the original right boundary gives

$$
V_X(t_m)=F(N_{p_m}^{\rm mult})-c_m
\ge\gamma+\frac d2X^{-\eta}-c_m.
$$

Every $\Phi_t(u)=W(u)-f(t+\log u)$ decreases in $t$, so its finite
maximum decreases as well. Consequently every real parameter in the
same window and every active tie satisfy

$$
\boxed{V_X(t)-\gamma\ge h_X^{\rm env}:=
\frac d2X^{-\eta}-c_m>0,
\qquad h_X^{\rm env}X^\eta\longrightarrow d/2.}
\tag{APC1}
$$

Real $t$ is still an interpolation parameter; $e^t$ is not asserted to
be a prime label or an additional integer source.

### Apply the existing pressure formula at the actual total clock

Write $R_{\rm pp}(x)$ for the unrestricted reserve $R(x)$ in
[GAK29/GAK38 and AVB32--AVB34](../ArithSums/nicolas2025comparison.md),
distinct from the source-window ceiling. Reuse its full-real positivity
and zero-at-infinity normalization. In particular, AVB33 and the existing
full-real $Q(x)=(\sqrt2-1)\sqrt x+o(\sqrt x)$ give
$R_{\rm pp}(x)=\int_x^\infty Q(v)w(v)dv>0$ eventually.
Uniform source escape pays this real start; no numeric witness start
is asserted.

For any real active core put $B=\log u$ and $A=B+t$ as before.
PG1 gives $u=N_A^{\rm str}$, so the unrestricted pressure at
$\lambda(A)$ is $W(u)-\lambda(A)B$. The existing pressure and tail
identities, with every reference atom retained, therefore give inside
this application

$$
\begin{aligned}
\frac{\mathsf H(A)}{s_A}=-I_\psi(A)
&=V_X(t)-\gamma+R_{\rm pp}(A)+t\lambda(A),\\
\mathsf H(A)
&=s_A[V_X(t)-\gamma+R_{\rm pp}(A)]+\frac t{\sqrt A}.
\end{aligned}
$$

The zero pressure defect is at $A$; the different own-price defect
at $B$ has not been set to zero. This uses the existing pressure-margin
identity, without extending CR43 or the compensated WRC transport.
APC1 now yields, uniformly over every real active tie and trace endpoint,

$$
\boxed{\mathsf H(A)\ge
h_X^{\rm env}\sqrt A\log A+\frac t{\sqrt A}>0.}
\tag{APC2}
$$

FCT2's existing scalar coercivity applies directly at $A$. Indeed
$t\ge\ell_X=(d/8)X^{1-\eta}\log X$. If $A/X\to0$, the lag term
in APC2 divided by $M_X$ diverges; if $A/X\to\infty$, its height term
diverges. On a compact positive range of $z=A/X$,
$\log A/\log X\to1$, and

$$
\frac d2\sqrt z+\frac d8\frac1{\sqrt z}\ge\frac d2.
$$

Thus for every fixed $\epsilon>0$, beyond one common original source
start,

$$
\boxed{\mathsf H(A)\ge(d/2-\epsilon)M_X,
\qquad \frac d2X^{-\eta}s_A+\frac t{\sqrt A}+1
\ll\mathsf H(A).}
\tag{APC3}
$$

These bounds hold at all real active clocks, including unsampled
contacts and all active cores at a multiple tie. They give no sign on
skipped open gaps or inactive clocks, and no uniformity as
$\eta\uparrow1/2$ is asserted.

### Keep the actual proper-power atoms in the signed boundary account

Use exactly $D_X^*=\bigcup_j(r_j,z_j]$ from CE2/SB1. Every point in
these components, including its retained trace endpoints, has its
actual active core by PG1/PG9. APC3 therefore applies at every retained
proper power. Define its complete unweighted mass only for this account:

$$
Z_X^{\rm pp}=\sum_{\substack{q^k\in D_X^*\\k\ge2}}\log q\ge0.
$$

For every fixed $0<\epsilon<d/2$, the existing pairing satisfies

$$
\boxed{C_D^{\rm pp}\ge(d/2-\epsilon)M_XZ_X^{\rm pp}\ge0.}
\tag{APC4}
$$

All powers, multiplicities and the actual half-open endpoint atoms
remain. No positive occupancy or lower count of these atoms is asserted;
the sum can be empty. SB1--SB2 then supply the separate one-sided
stock-boundary constraint, for a fixed existing SB2 constant $C_{\rm SB}$,

$$
\boxed{B_Q\le C_{\rm SB}
\left(b_X^{-1/2}+\frac{\epsilon_X^{\rm en}}{M_X}\right)S_H
 -(d/2-\epsilon)M_XZ_X^{\rm pp}.}
\tag{APC5}
$$

This does not assign a sign to $B_Q$, or bound either term in absolute
value. APC5 uses SB2's source-relative allowance; that estimate alone
does not give an absolute $o(M_XL_X)$ bound. On the same actual contacts $\mathsf H_-=0$, so
SB4's integrated allowance can also be replaced by zero there. That
simplification supplies no additional credit or improvement of SB8's
already paid target scale.

APC1--APC5 supply pointwise contact coercivity and an actual proper-power
atom sign, using the endpoint envelope and exact pressure correspondence.
They do not pay the complete $B_D+C_D^{\rm pp}$ or boundary-minus-credit
strict upper, the original nonlocal FH first-prime test, all-integer
Robin or RH. Every original source condition and the single-use
compensation remain.


## The stock-boundary and proper-power remainder has an absolute payment

Keep SB1 and APC1--APC5 on the original conditional RH-failure source,
every full window and allowed tie, and every originally fixed
$1-\Theta<\eta<1/2$, including $\Theta=1$. Use exactly the same
$D_X^*=\bigcup_j(r_j,z_j]$, complete future $\mathsf H$, proper-power
atoms and trace endpoints. This `repo-derived` paper application reuses
CQ4's full-integral majorant and the existing source derivative. It
asserts no new generic estimate, literature priority or Lean verification.

### Use the existing full-integral majorant before taking a source norm

CQ4 already evaluates the complete improper-integral majorant from the
unconditional coarse PNT input. Apply that existing bound, without the
local compensation, at the real clock $x=A(t)$:

$$
|\mathsf H(x)|\le C_{\rm PNT}\sqrt x
\left[\frac1{2\log x}+\frac1{3\log^2x}\right].
$$

Its input $|E(v)|\le C_{\rm PNT}v/\log^2v$ holds for every future
$v\ge x$ after the same real start. No horizon truncation or bound on
$\mathsf H/M_X$ or $S_H/(M_XL_X)$ is used.

Use the complete derivative from SB1--SB2 and its exact coefficients:

$$
\mathsf H'=\frac{s'}s\mathsf H-skE,
\qquad \frac{s'}s=\frac1{2x}+\frac1{x\log x},
\qquad s_xk(x)=\frac{1+1/\log x}{x^{3/2}}.
$$

On every actual visited branch, the existing full-real bound
$|Q(x)|\le H_Q\sqrt x$ and identities $x=A(t)=B(t)+t$,
$E(A(t))=t+Q(A(t))$ therefore give almost everywhere

$$
|Q(x)\mathsf H'(x)|
\le C\left[\frac1{\log x}+\frac t x+\frac1{\sqrt x}\right]
\le C\omega_X,
\qquad
\omega_X:=\frac1{\log b_X}+\rho_X+b_X^{-1/2}\longrightarrow0.
$$

Here $b_X=\min_tB(t)$ and $\rho_X=\sup_t t/B(t)$ are exactly the
original uniformly escaping clock floor and vanishing lag ratio.
Use PG9's exact pushforward and $|D_X|=L_X$, retaining the local clock
in the majorant before integration. This yields the absolute payment

$$
\boxed{\int_{D_X}|Q\mathsf H'|dx
\le C\omega_XL_X=o(L_X).}
\tag{ASP1}
$$

No maximum-to-minimum clock ratio or normalized response ceiling enters.
This is an integral of $|Q\mathsf H'|$, not the total variation of
$Q\mathsf H$; the latter still contains the actual proper-power jumps.

### Keep the cancellation with the actual endpoint atoms

Apply the existing exact SB1 identity with its unchanged half-open
representative. ASP1 gives

$$
\boxed{\begin{aligned}
|B_Q+C_D^{\rm pp}|&\le C\omega_XL_X=o(L_X),\\
|B_D+C_D^{\rm pp}-B_\tau|&\le C\omega_XL_X.
\end{aligned}}
\tag{ASP2}
$$

The second line uses $B_D=B_\tau+B_Q$ and the same single remainder.
Since $M_X\to\infty$, this is also an absolute $o(M_XL_X)$ allowance
for these boundary expressions. It does not bound either cancelling
term in absolute value or consume any compensation credit.

For every fixed $0<\epsilon<d/2$, consume APC4's actual atom sign in
this same account to obtain

$$
\boxed{B_Q\le C\omega_XL_X
 -(d/2-\epsilon)M_XZ_X^{\rm pp}.}
\tag{ASP3}
$$

The proper-power mass $Z_X^{\rm pp}$ is unchanged and may be zero.
No sign for $B_Q$, positive atom occupancy or separate absolute component
bound is asserted. ASP3 pays the allowance in this one-sided constraint
absolutely, strengthening APC5's source-relative allowance.

ASP1--ASP3 pay this exact stock-boundary/proper-power remainder at the
original target scale, with the complete future and every endpoint
retained. They do not pay the separate pure-future energy terms, supply
a two-sided absolute comparison of $\mathcal I_X^H$ and $B_\tau$, or
establish the strict upper for the complete boundary-minus-credit.
The original nonlocal FH first-prime test, all-integer Robin inequality
and RH remain unproved. No uniformity as $\eta\uparrow1/2$ is asserted.

## The actual envelope descent strictly raises the full-window lower margin

Keep JM1--JM7's complete original conditional source, every originally
fixed $1-\Theta<\eta<1/2$, including $\Theta=1$ when allowed, and all
original full windows, outgoing weights and maximizing ties. Put
$\tau=1-\eta$, $Q=Q_\eta$, $b=1-aQ>0$ and
$R_\eta=(d/2)\sqrt b$. Reuse N2's finite actual integer-core envelope,
CR17--CR19, APC1, HC2 and CQ5. The existing capacity suppliers are used
only at original prime labels, with JM5--JM6's unchanged strict cuts.
This is a `repo-derived` paper application, with no new generic inequality,
prime theorem, literature-priority claim or Lean/kernel verification.

### Retain the changing height in the same own-core pressure account

Write $B(t)=\mathcal B_X(t)$, $A(t)=B(t)+t$ and
$s_B=\sqrt B\log B$. N2's finite envelope calculus gives

$$
\Delta V(t):=V_X(t)-V_X(t_m)
=\int_t^{t_m}\lambda(A(v))\,dv\ge0,
\qquad \lambda(x)=\frac1{x\log x}.
\tag{EDH1}
$$

The derivative formula holds off the finite switch set; choosing another
active tie at those points leaves the integral unchanged. At an original
tag $t_i$, let $B_i=\log U_i$ be any original maximizing core, and put
$h_m=V_X(t_m)-\gamma$ and $D_t(B)=f(B+t)-f(B)$ as in CR18. The exact
own-core account used in CR19 yields

$$
\begin{aligned}
\mathcal R_i&:=G_a(B_i)-s_{B_i}\Delta V(t_i)\\
&=s_{B_i}[h_m+D_{t_i}(B_i)+R_{\rm pp}(B_i)+d_{B_i}(U_i)]
-\frac{aE(B_i)}{\sqrt{B_i}}.
\end{aligned}
\tag{EDH2}
$$

Here $F(U_i)=V_X(t_i)+D_{t_i}(B_i)$, and both displayed reserves are
the original nonnegative ones. APC1 gives
$h_m\ge(d/2)X^{-\eta}-c_m$ with $c_m\le e^{-\ell_X}$.
Removing the changing height has not removed the terminal height or lag.

Fix $C_0>8/5$ with $aC_0<1$, and set
$\alpha=d\tau/8$ and $\beta=d(1-aC_0)/16>0$.
CR17, the original-tag capacity bound and the same price comparison as
CR18 give, for $z_i=B_i/X$,

$$
\frac{\mathcal R_i}{M_X}
\ge\alpha\sqrt{z_i}+\frac\beta{\sqrt{z_i}}-o(1).
\tag{EDH3}
$$

Indeed eventually $h_m\ge(d/4)X^{-\eta}$,
$\log B_i/\log X\ge\tau/2$ and
$s_{B_i}D_{t_i}(B_i)=(1+o(1))t_i/\sqrt{B_i}$; after subtracting the
capacity term the latter coefficient is at least $(1-aC_0)/2$.
The fixed capacity allowance divided by $M_X$ tends to zero. All errors
are uniform over original labels and ties.

A bounded normalized residual is therefore in a fixed compact positive
range of $B_i/X$. On that range reuse JM5--JM6's localized capacity
and $\log B_i/\log X\to1$. The same AM--GM argument gives
$\mathcal R_i/M_X\ge R_\eta\sqrt{t_i/\ell_X}-o(1)$ there.
Any violating sequence would have bounded residual, so EDH3 localizes it
and proves this estimate uniformly on the whole original family.
In particular $G_a(B_i)\ge\mathcal R_i>0$ eventually.

The full-window facts $L_X\sim\ell_X$, $t_0\ge\ell_X$ and
$t_m\le2\ell_X$ imply $t_0/\ell_X\to1$, $t_m/\ell_X\to2$.
The paid label mesh gives the ordinary scalar left-sum limit

$$
\frac1{L_X}\sum_{i<m}\delta_i\sqrt{t_i/\ell_X}
\longrightarrow c_{\rm av}:=\frac23(2\sqrt2-1).
$$

Set $R_{\rm stat}=c_{\rm av}R_\eta$. This static averaging alone does
not account for the additional height in EDH2.

### The same ordered trajectory supplies a positive dynamic contribution

Choose fixed constants

$$
\begin{gathered}
K=2R_{\rm stat},\qquad
r=\min\{1/2,(\beta/(4K))^2\},\qquad
R=\max\{2,(4K/\alpha)^2\},\\
g_{\rm env}=\frac{d\sqrt r}{64R}>0,\qquad
\delta_{\rm env}=\frac12\min\{R_{\rm stat},g_{\rm env}\}>0.
\end{gathered}
\tag{EDH4}
$$

The fixed $R$ here is a compact-localization constant, not a replacement
for the original source ceiling $R_X$. If
$\mathcal G_{X,\mathcal T}/(M_XL_X)\le K$, EDH3 bounds the residual
below by $2KM_X$ outside $rX\le B_i\le RX$ beyond a common start.
Positivity of every original response then implies that tags inside this
range carry at least $L_X/2$ of the outgoing weight.

By N2's ordering for every choice of ties these tags form a consecutive
block $k,\ldots,l$. On the open interval $(t_k,t_l)$ every real active
core lies between the two tagged cores, hence in $[rX,RX]$. This suffices
almost everywhere for the integral; no constraint on other tied cores
at either endpoint is asserted. Dropping only the last outgoing
good interval leaves length
$T_{\rm good}=t_l-t_k\ge L_X/2-\varepsilon_X^{\rm lab}$.
The case $k=l$ is impossible eventually by this inequality and the mesh.
For $k\le i<l$, EDH1 consequently gives
$\Delta V(t_i)\ge(t_l-t_i)\lambda(RX+t_m)$.
The exact finite triangular-sum identity now yields

$$
\begin{aligned}
\sum_{i<m}\delta_i s_{B_i}\Delta V(t_i)
&\ge\sqrt{rX}\log(rX)\lambda(RX+t_m)
 \sum_{i=k}^{l-1}\delta_i(t_l-t_i)\\
&\ge\left[\frac{\sqrt r}{R\sqrt X}+o(X^{-1/2})\right]
\frac{T_{\rm good}^2}{2}.
\end{aligned}
$$

Since $L_X/(M_X\sqrt X)\to d/8$, this proves the additional estimate

$$
\boxed{
\frac1{M_XL_X}\sum_{i<m}\delta_i s_{B_i}\Delta V(t_i)
\ge g_{\rm env}-o(1)
\quad\text{whenever }\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}\le K.}
\tag{EDH5}
$$

Both factors in this ordered pair estimate belong to the same actual
envelope. There is no global assumption $B_i\asymp X$, independent
selection of clocks or new real-parameter capacity estimate. Only a
nonnegative part of the changing height was bounded below; the complete
future and all original terms remain in $G_a$.

Combining EDH5 with the uniform residual lower sum, and including the
alternative $\mathcal G_{X,\mathcal T}/(M_XL_X)>K$, gives

$$
\boxed{
\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge R_{\rm stat}+\min\{R_{\rm stat},g_{\rm env}\}
=R_{\rm stat}+2\delta_{\rm env}>R_{\rm stat}>R_\eta.}
\tag{EDH6}
$$

The lower limit is uniform over all original qualifying full windows and
tie assignments. HC2 and CQ5 have $o(M_XL_X)$ errors, so beyond one
common source start the same eventual lower bound
$(R_{\rm stat}+\delta_{\rm env})M_XL_X$ holds for each original
compensated sum, every admissible-height head and $\mathcal J_X$.
The strict extra gain therefore comes from the actual changing envelope,
beyond the complete static averaged margin.

BV1--BV3 bound variation of the source price $\lambda(A)$; EDH5 bounds
the integrated envelope height in the own-core pressure. These accounts
share a source and are not independent copies of a reserve. No credit is
spent again here. The full same-source boundary-minus-one-use-credit
expression still needs its strict upper below an available lower margin
on a common cofinal family. No favorable windows, real-parameter CR43
extension, WRC scope extension, strict all-integer Robin inequality or RH
proof follows.

## A published reverse Opial inequality gives an explicit full-source margin

Keep EDH1--EDH6's entire original conditional source, every originally
fixed $1-\Theta<\eta<1/2$, including allowed $\Theta=1$, every full
window and maximizing tie, and the original mesh and coarse ceiling.
Put $b=1-aQ_\eta\in(0,1)$. The analytic supplier below is an existing
published theorem. The additional project content is its full-source
interface, which permits clocks outside every fixed compact scale and
uses capacity only at original prime labels. This is a paper application,
without a new generic inequality, literature-priority claim or Lean/kernel
verification.

### Import the existing inequality with its actual parameters

P. R. Beesack and K. M. Das, *Extensions of Opial's inequality*,
Pacific Journal of Mathematics **26**(2) (1968), 215--232,
[primary publisher PDF](https://msp.org/pjm/1968/26-2/pjm-v26-n2-p02-s.pdf),
Theorem 3, printed pp.222--223, gives the lower inequality (22); its
constant $K_1$ is defined by (7), printed p.216. Take their exponents
$p=1$, $q=-2$, weights $r(z)=z^2$, $s(z)=1$, interval $[0,h]$ and
$y(z)=\int_0^z f(v)\,dv$. For measurable $0<c\le f\le C<\infty$,
the primitive is absolutely continuous, its derivative is positive
almost everywhere, and all required weight and negative-power integrals
are finite. Formula (7) gives $K_1=4(4h)^{-1}=1/h$. Direct application,
without reproving that theorem, therefore supplies

$$
\int_0^h\frac{\int_0^z f(v)\,dv}{f(z)^2}\,dz
\ge\frac1h\int_0^h\frac{z^2}{f(z)}\,dz.
\tag{OSP1}
$$

The cited theorem does not itself supply a statement about original
prime tags, source-selected cores or escaping clock scales.

### Prefix and suffix moments localize the interior of the actual source

It suffices to consider any cofinal sequence of original windows and tie
assignments with $\mathcal G_{X,\mathcal T}/(M_XL_X)\le K$ for some
fixed finite $K$. Any sequence violating a proposed fixed lower margin
would have this property. Define

$$
x_i=t_i/\ell_X,\quad h_i=\delta_i/\ell_X,\quad
u_i=\sqrt{B_i/X},\quad u_X(x)=\sqrt{\mathcal B_X(\ell_Xx)/X},
\qquad P_X^\pm=\sum_{i<m}h_i u_i^{\pm1}.
$$

EDH3 and $G_a(B_i)\ge\mathcal R_i$ give
$\alpha P_X^++\beta P_X^-\le(K+o(1))L_X/\ell_X$.
Thus both moments are bounded by one fixed $C_K$. N2 orders all active
cores at distinct parameters, including arbitrary original tie tags.
For a real parameter $x$, preceding tags have $u_i\le u_X(x)$, while
strictly later tags have $u_i\ge u_X(x)$. Their actual outgoing weights
therefore imply

$$
\frac{x-t_0/\ell_X}{P_X^-}
\le u_X(x)\le
\frac{P_X^+}{t_m/\ell_X-x-\varepsilon_X^{\rm lab}/\ell_X}.
\tag{OSP2}
$$

The upper inequality is used only when its denominator is positive.
The same comparisons hold for every other active choice at that real
parameter; they use tags at strictly different parameters. Fix
$0<\theta<1/2$, and put
$a_\theta=1+\theta$, $b_\theta=2-\theta$,
$I_\theta=[a_\theta,b_\theta]$ and $h_\theta=1-2\theta$.
Because the original endpoints tend to 1 and 2 after normalization,
OSP2 gives $0<c_{K,\theta}\le u_X\le C_{K,\theta}<\infty$
on this entire interior interval, uniformly in every active tie.
This is a consequence of the bounded-response sequence, not a global
assumption $B\asymp X$ or a change to the original source ceiling.

### Pay the source-to-integral interface before using the theorem

Only at original labels $x_i\in I_\theta$, reuse EDH2 and JM5--JM6's
localized capacity suppliers, with all their strict cuts. They give

$$
\frac{\mathcal R_i}{M_X}
\ge\frac d2u_i+\frac d8\frac{b x_i}{u_i}-o(1).
$$

For the changing height, EDH1's nonnegative integral may be restricted
to $[t_i,\ell_Xb_\theta]$. On this compact range,
$\log B/\log X\to1$ and $A/B\to1$ uniformly. Here
$\ell_X/X\to0$ because the original fixed $\eta>0$, and
$\ell_X/(M_X\sqrt X)=d/8$. Consequently

$$
\frac{s_{B_i}\Delta V(t_i)}{M_X}
\ge\frac d8u_i\int_{x_i}^{b_\theta}u_X(v)^{-2}\,dv-o(1).
\tag{OSP3}
$$

No capacity estimate has been used at an unsampled real parameter.
To integrate these original tagged bounds, reuse CQ2's published
arbitrary-partition bounded-variation supplier with the new readouts.
The monotone function $u_X$ and its reciprocal have uniformly bounded
variation on $I_\theta$. The function
$F_X(x)=\int_x^{b_\theta}u_X(v)^{-2}\,dv$ is uniformly bounded and
Lipschitz there. The product variation bound therefore controls
$u_XF_X$ and $x/u_X$ by constants depending only on $K,\theta$ and
fixed source parameters. Inserting any original tagged $u_i$ between
its one-sided monotone limits preserves these variation bounds; the
combined readout itself need not be monotone. Both boundary fragments
cost $O(\varepsilon_X^{\rm lab}/\ell_X)$, and the interior quadrature
error tends to zero uniformly in all ties.

All original responses are positive by EDH3 and its compact refinement.
Dropping outside tags for this lower comparison and using
$L_X/\ell_X\to1$ thus gives

$$
\begin{aligned}
\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge{}&\frac d2\int_{I_\theta}u_X(x)\,dx
+\frac d8b\int_{I_\theta}\frac{x}{u_X(x)}\,dx\\
&+\frac d8\int_{a_\theta\le r<v\le b_\theta}
\frac{u_X(r)}{u_X(v)^2}\,dr\,dv-o(1).
\end{aligned}
\tag{OSP4}
$$

This is an auxiliary interior integral cutoff. The final target still
uses the full original window, label list and outgoing weights. The
complete future in $G_a$ remains; only the positive envelope-height
integral and already positive outside responses were restricted.
No pointwise sign for the future arithmetic error is asserted.

### Apply the supplier and then remove the analytic cutoff

Apply OSP1 to $f(z)=u_X(a_\theta+z)$ on $[0,h_\theta]$.
OSP2 supplies all its function hypotheses, without taking a limit of
$u_X$. Its right side is
$h_\theta^{-1}\int_{I_\theta}(x-a_\theta)^2/u_X(x)\,dx$.
The same pointwise AM--GM inequality used in JM then gives from OSP4

$$
\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge\frac d2\int_{1+\theta}^{2-\theta}
\sqrt{b x+\frac{(x-1-\theta)^2}{1-2\theta}}\,dx-o(1).
$$

First take the source lower limit with $\theta$ fixed, and then let
$\theta\downarrow0$. The displayed scalar integrands are bounded for
small $\theta$ and converge almost everywhere. Bounded convergence
therefore proves the explicit full-source margin

$$
\boxed{
R_{\rm Op}:=\frac d2\int_1^2\sqrt{b x+(x-1)^2}\,dx,\qquad
\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}\ge R_{\rm Op}.}
\tag{OSP5}
$$

The result is uniform on all original full windows and tie assignments:
any violating cofinal sequence would be a bounded-response sequence to
which the argument applies. HC2 and CQ5 give the same lower limit for
every original admissible-height head and $\mathcal J_X$, with an
arbitrarily small fixed loss at the eventual-bound level.

Rationalizing the scalar square-root difference and integrating
$(x-1)^2$ gives the explicit further estimate

$$
\boxed{
R_{\rm Op}\ge R_{\rm stat}
+\frac{d}{6(\sqrt{2b+1}+\sqrt{2b})}>R_{\rm stat}.}
\tag{OSP6}
$$

For the original $0<b<1$, the displayed increment exceeds $d/24$,
whereas EDH4 gives $g_{\rm env}\le d/(128\sqrt2)<d/24$.
OSP5 therefore improves EDH6 without its auxiliary $C_0,r,R$ constants
in the final margin. These estimates use the full positive functional
without requiring an optimizing arithmetic source. The published inequality supplies
the analytic input; OSP2--OSP5 supply its source-specific application.
Neither supplies a second credit, a full-real capacity extension or the
missing strict upper of the complete same-source boundary-minus-credit
expression. That upper, strict all-integer Robin and RH remain unproved.


## The same-source response admits a larger joint variational margin

Keep OSP1--OSP6's entire original conditional RH-failure source, all
fixed parameters $1-\Theta<\eta<1/2$, including allowed $\Theta=1$,
all original full windows and maximizing ties, the complete future,
original mesh and coarse ceiling. Keep the original one-use $a$ and
$b=1-aQ_\eta\in(0,1)$. Reuse OSP4's existing actual-source interface and the classical
convex supporting inequality. The resulting full-functional analytic
infimum supplies a larger source margin. This is a paper derivation;
no literature-priority or Lean/kernel verification is claimed.

### A scalar constant for the complete positive functional

Define

$$
D_b(v)=2b+3(1-b)v-6v^2,\qquad
\nu_b=\frac{3(1-b)+\sqrt{9(1-b)^2+48b}}{12},
$$

and, on $0\le v<\nu_b$,

$$
\Phi_b(v)=\int_0^v\frac{2b+6s}{D_b(s)}\,ds.
$$

This is strictly increasing, starts at zero and diverges at $\nu_b$.
Let $v_b$ be its unique solution of $\Phi_b(v_b)=\log2$, and put

$$
\mathcal C_b=8v_b^2(b+2v_b),\qquad
R_{\rm joint}(b)=\frac d2\sqrt{\mathcal C_b}.
\tag{JVM1}
$$

For a measurable $u$ bounded above and away from zero on $[1,2]$, set

$$
A=\int_1^2u(x)dx,\qquad U(x)=\int_1^x u(r)dr,
$$

$$
\mathcal D_b[u]=b\int_1^2\frac{x}{u(x)}dx
                  +\int_1^2\frac{U(x)}{u(x)^2}dx.
$$

The analytic value is

$$
\inf_u A\mathcal D_b[u]=\mathcal C_b,\qquad
\inf_u\frac d8\bigl(4A+\mathcal D_b[u]\bigr)
       =R_{\rm joint}(b).
\tag{JVM2}
$$

The infima are attained by smooth positive increasing functions; this
is an assertion about the analytic class, not arithmetic attainability.

### Convex sufficient comparison for the actual functional

By scaling $u$ it suffices to minimize $\mathcal D_b$ subject to $A=1$.
Use $y=\sqrt{U(x)}\in[0,1]$, write its inverse as $x=x(y)$ and set
$z(y)=x(y)^{3/2}$. Change of variables gives exactly

$$
\mathcal D_b[u]=\int_0^1\mathscr L_b(y,z,z')dy,\qquad
\mathscr L_b(y,z,p)=\frac{2b}{9y}p^2+\frac2{27}\frac{p^3}{z},
\quad z(0)=1,\ z(1)=2\sqrt2.
\tag{JVM3}
$$

The integrand is convex in $(z,p)$ for $z>0,p\ge0$. For $p>0$,
the Hessian of $p^3/z$ has entries
$2p^3/z^3$, $-3p^2/z^2$, $6p/z$ and determinant $3p^4/z^4>0$;
the first term is convex in $p$ as well. For global sufficiency, apply
R. T. Rockafellar, *Conjugate convex functions in optimal control and
the calculus of variations*, Journal of Mathematical Analysis and
Applications **32** (1970), 174--222,
[author-hosted primary paper](https://sites.math.washington.edu/~rtr/papers/rtr034-ConjConFnsOptimalControl.pdf),
Corollary 1, printed p.210. Its basic assumptions (A)--(D) are on
pp.179--180; extremality is (9.3) and (9.5), printed p.208.

Here extend $\mathscr L_b$ by $+\infty$ outside
$1\le z\le2\sqrt2$, $p\ge0$. At $y=0$ use the indicator of
$[1,2\sqrt2]\times\{0\}$. The endpoint function is the indicator
of $(z(0),z(1))=(1,2\sqrt2)$. These are proper lower semicontinuous
convex data. The integrand is Borel and hence Lebesgue-normal; its
nonnegativity supplies the zero affine minorant in (C), and the
constant measurable selection $(z,p)=(1,0)$ with zero value supplies
(D). Thus the singular $1/y$ coefficient satisfies the published
hypotheses. Only the classical global sufficiency statement is
imported; the following curve and its value are computed for JVM3.

Construct $v(x)=\Phi_b^{-1}(\log x)$ for $1\le x\le2$. Let
$w(x)>0$ solve

$$
\frac{w'(x)}{w(x)}=\frac{b+3}{x(2b+6v(x))},
\qquad\int_1^2 w(x)dx=1.
\tag{JVM4}
$$

Its normalization is possible because the differential equation is
linear for $\log w$ with a finite coefficient. It is smooth and
increasing. Direct differentiation, using
$xv'=D_b(v)/(2b+6v)$, gives

$$
W(x):=\int_1^xw(r)dr=xw(x)v(x),\qquad
w'=\frac{(b+3)w^2}{2bxw+6W}.
$$

In particular $w(2)=1/(2v_b)$. If
$P=-bx/w^2-2W/w^3$, the same equation gives $P'=1/w^2$, which
is the Euler equation for $bx/W'+W/(W')^2$.

For the corresponding $z_*$ in JVM3, put
$m=\partial_p\mathscr L_b(y,z_*,z_*')$. Differentiation gives
$m'=\partial_z\mathscr L_b=-2(z_*')^3/(27z_*^2)$.
Near $y=0$, $z_*(y)=1+O(y^2)$, $z_*'=O(y)$ and
$m(y)\to4b/(3w(1))$. Thus $m$ extends to an absolutely continuous
coextremal on $[0,1]$. The constructed curve lies in the interior of
the state and positive-velocity constraints almost everywhere, so
these derivatives give the published subgradient condition (9.3).
The fixed endpoint function imposes no further restriction in (9.5).
Rockafellar's Corollary 1 therefore gives global minimality among the
feasible absolutely continuous curves.

For every measurable bounded positive $u$ above, the inverse map is
Lipschitz, with $z(y)=1+O(y^2)$ near zero, and belongs to that feasible
class. This verifies the comparison on the entire stated analytic
class. The constructed equality profile $w$ has no zero or singular
endpoint. No general existence or dual-attainment theorem is needed.

Finally $(WP)'=-bx/w-W/w^2$. Thus

$$
\mathcal D_b[w]=-[WP]_1^2
 =\frac{2b}{w(2)^2}+\frac2{w(2)^3}
 =8v_b^2(b+2v_b)=\mathcal C_b.
$$

This proves the first assertion of JVM2. For arbitrary $A$, scaling
gives $A\mathcal D_b[u]\ge\mathcal C_b$; minimizing
$4A+\mathcal C_b/A$ proves the second. Its optimizer is
$u_*=(\sqrt{\mathcal C_b}/2)w$.

### Strict gain over the already retained Opial margin

The known Beesack--Das application OSP1 and pointwise AM--GM imply
$R_{\rm joint}\ge R_{\rm Op}$, with the latter defined in OSP5.
If equality held, apply those two inequalities to $u_*$. The
pointwise nonnegative AM--GM gap would have integral zero, forcing

$$
u_*(x)=\frac12\sqrt{bx+(x-1)^2}\quad(1\le x\le2).
$$

This profile has logarithmic derivative $1/2$ at $x=1$.
JVM4 instead gives $u_*'(1)/u_*(1)=(b+3)/(2b)>1/2$.
Both profiles are smooth, so they cannot agree almost everywhere.
Consequently, for every fixed original $0<b<1$,

$$
\boxed{R_{\rm joint}(b)>R_{\rm Op}(b).}
\tag{JVM5}
$$

No numerical approximation to $v_b$ or uniform positive gain as
$b\downarrow0$ is asserted.

### Consume the constant on the original full source

Use OSP4 without changing its proof. On its fixed interior interval
$[a_\theta,b_\theta]=[1+\theta,2-\theta]$ of length
$h=1-2\theta$, substitute $x=a_\theta+h(z-1)$ and
$u_X(x)=\sqrt h\,\widetilde u(z)$, $1\le z\le2$.
The source clock remains on its existing compact interior range,
so JVM2's analytic hypotheses hold. Since $x=hz+3\theta\ge hz$,
the right side of OSP4 is at least

$$
h^{3/2}\frac d8\left[4\int_1^2\widetilde u
  +b\int_1^2\frac z{\widetilde u(z)}dz
  +\int_{1\le r<v\le2}
       \frac{\widetilde u(r)}{\widetilde u(v)^2}drdv\right]-o(1)
\ge h^{3/2}R_{\rm joint}(b)-o(1).
$$

Take the source lower limit at fixed $\theta$, then
$\theta\downarrow0$. Exactly the existing bounded-response
contradiction in OSP2--OSP5 therefore yields

$$
\boxed{\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge R_{\rm joint}(b)>R_{\rm Op}(b).}
\tag{JVM6}
$$

The bound is uniform over the original windows and tie assignments;
HC2 and CQ5 give the same margin for every original admissible-height
head and $\mathcal J_X$. The analytic infimum is not an assertion
that any prime-selected source attains it. No real-parameter capacity
extension, global clock bound, second compensation credit or pointwise
future-error sign is introduced. The independent same-source strict
upper, strict Robin for every integer above 5040 and RH remain open.


## A cited density theorem extends the original high-frequency range

Reuse Mark Lewko, *Zero-density estimates from an improved large-values
bound*, at pinned source
[`ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0`](https://github.com/mrklwk/zeta-density-39-over-17-lean/tree/ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0).
The production theorem
[`GuthMaynard.Improvement.global_density_uniform`](https://github.com/mrklwk/zeta-density-39-over-17-lean/blob/ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0/lean/GuthMaynard/Improvement/GlobalDensity.lean)
and its literal actual-zero formulation
[`GuthMaynardStatement.global_uniform`](https://github.com/mrklwk/zeta-density-39-over-17-lean/blob/ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0/lean/Solution.lean)
supply the following external input:

$$
\forall\epsilon>0\ \exists C_\epsilon>0\
\forall\sigma\in[1/2,1]\ \forall T\ge2,\qquad
N(\sigma,T)\le C_\epsilon
 T^{(39/17)(1-\sigma)+\epsilon}.
\tag{LDS1}
$$

Here the finite set consists of actual `riemannZeta` zeros in
$0<\operatorname{Re}\rho<1$, with
$\operatorname{Re}\rho\ge\sigma$ and $|\operatorname{Im}\rho|\le T$,
counted with `analyticOrderNatAt` multiplicities. This bounds the existing
positive-ordinate count as well. The endpoint's proof has no additional
analytic hypothesis. It is cited from an unrefereed proof repository:
the pinned compatibility migration's closure checks are source-reported,
not kernel replay by this project. Earlier-version receipts do not certify
that migration. This application takes LDS1 as a literature input; it is
neither a new density theorem nor a local Lean certification of that input.

With this cited supplier, keep FHA1--FHA5's original conditional source,
all full windows, maximizing ties, actual coefficients and multiplicities,
positive outgoing weights and legal upper heights. Replace only FHA1's
additional restriction by

$$
\boxed{1-\Theta<\eta<
 \min\!\left\{\frac12,
 \frac{2-\min\{\Theta,9/13\}}3\right\}.}
\tag{LDS2}
$$

To apply the existing proof directly, let $D_0$ denote FHA2's continuous
Ingham--Guth--Maynard exponent and set
$D_*(\sigma)=\min\{D_0(\sigma),(39/17)(1-\sigma)\}$.
Its normalized coefficient, for $1/2\le\sigma<1$, is

$$
\frac{D_*(\sigma)}{1-\sigma}=
\begin{cases}
3/(2-\sigma),&\sigma\le9/13,\\
39/17,&9/13\le\sigma\le46/65,\\
15/(3+5\sigma),&\sigma\ge46/65.
\end{cases}
\tag{LDS3}
$$

The joins agree. Its maximum over $1/2\le\sigma\le\Theta$, with
$\sigma<1$, is $3/(2-\min\{\Theta,9/13\})$. On the same compact
middle range $[u,v]$, where $u=1-\eta>1/2$ and
$v=\min\{\Theta,\sigma_\circ\}<1$, one has $0<D_*<1$ and, with
$E_*=\sigma-1+D_*/2$,

$$
\mu D_*(\sigma)-E_*(\sigma)
=1-\sigma-\eta D_*(\sigma)>0,\qquad \mu=1/2-\eta>0.
$$

Thus the strict compact gap in FHA2 holds with $D_*,E_*$. At each fixed
bin endpoint use whichever cited estimate supplies the minimum; include
$9/13$ and $46/65$ as endpoints when present. The existing finite-bin
choice absorbs the positive density loss. Apply FHA3--FHA5 without
changing their proof, including both $B\le X$ and $B>X$ branches and the
latter's actual source-height account. They give the same
$\mathcal R_X^{\rm high}/\mathcal G_X\to0$ and remaining-head margin
on LDS2. The common polynomial-height raw-head consumer following FHA5
uses that same gap and its existing near-one estimate, so it transfers
to LDS2 as well. No supplied exponent or height assignment is reselected.

For $\Theta\ge7/10$, including $\Theta=1$, the additional original
parameter class is $13/30\le\eta<17/39$. Its upper endpoint increases
by $1/390$. This is a consumed application of the cited density theorem.
WRC's additional short-interval input is supplied in the application
below. FCT's full-range uncompensated future account is already available. No uniformity as $\eta$ approaches the new endpoint,
signed remaining-head upper, full original-range compensation estimate,
strict Robin for every integer above 5040, or RH follows.


## The same density inputs extend the complete compensated clock transport

Keep LDS2's original conditional RH-failure source and WRC's original
$0<a<5\kappa/8$, complete response $G_a$, full windows, maximizing ties,
positive outgoing weights and endpoint conventions. Write

$$
c_\Theta=\frac3{2-\min\{\Theta,9/13\}},\qquad
r_\Theta=1-\frac1{c_\Theta}
=\frac{1+\min\{\Theta,9/13\}}3.
\tag{DST1}
$$

The following is a consumed paper application of the cited density
inputs and [Guth--Maynard, arXiv:2405.20552v2, Section 13.2](https://arxiv.org/html/2405.20552v2#S13.SS2).
It supplies WRC4's short-interval input on LDS2; it does not reprove a
general density theorem, prime-counting theorem or transport theorem.

### Supply a uniform proportional-loss input to the published proof

For every fixed $\delta>0$, the existing inputs imply

$$
N(\sigma,T)\ll_{\Theta,\delta}
T^{(c_\Theta+\delta)(1-\sigma)}\log^{15}T
\qquad(1/2\le\sigma\le1,\ T\ge51).
\tag{DST2}
$$

For $\Theta\ge9/13$, put $\sigma_0=9999/10000$ and take
$\epsilon=\delta(1-\sigma_0)$ in LDS1. On
$1/2\le\sigma\le\sigma_0$ this gives
$\epsilon\le\delta(1-\sigma)$. On $\sigma_0\le\sigma\le1$,
NE1 gives $N(\sigma,T)\ll T^{1-\sigma}\log^{15}T$ because
$58.05\sqrt{1-\sigma}\le0.5805<1$. Thus the fixed LDS1 loss is
not silently made proportional as $\sigma\uparrow1$: Ford's separately
owned uniform bound supplies that part.

For $1/2<\Theta<9/13$, use the already cited fixed-real-part Ingham
bound on a finite grid in $[1/2,\Theta]$. Choose one
$\epsilon=\delta(1-\Theta)/4$ and maximum grid width
$\omega\le\delta(1-\Theta)/(4c_\Theta)$. At a left gridpoint
$\sigma_j\le\sigma\le\sigma_j+\omega$, monotonicity of the count and
$3/(2-\sigma_j)\le c_\Theta$ give

$$
N(\sigma,T)\le N(\sigma_j,T)
\ll_j T^{c_\Theta(1-\sigma_j)+\epsilon}
\le T^{(c_\Theta+\delta)(1-\sigma)}.
$$

Only finitely many fixed constants occur. For $\sigma>\Theta$ the
actual count is zero by the definition of $\Theta$. This proves DST2
without a moving-$\sigma$ uniformity assumption or a zero attaining
$\Theta$. The original source has $\Theta>1/2$.

### Consume the variable-length short-interval consequence

In the cited Section 13.2 proof, fix
$r_\Theta<r<99/100$ and choose $\delta>0$ so that
$c(1-r)<1$, where $c=c_\Theta+\delta$. For
$x^r\le h\le x^{99/100}$ its same truncation

$$
T=(x/h)\exp\bigl(2(\log x)^{1/4}\bigr)
$$

has $T^c/x\le x^{-\kappa_r}$ eventually, for a fixed
$\kappa_r>0$. Apply that proof with DST2 in place of its (13.3).
The same explicit formula, total zero count in the left half and global
Vinogradov--Korobov cap for zeros below this $T$ apply. The latter cap
$1-\sigma\gg(\log T)^{-5/7}$ yields decay on the scale
$\exp[-C_r(\log x)^{2/7}]$, which absorbs its fixed logarithmic
factors and the stated $(\log x)^{1/4}$ loss. Bounded-height zeros
are absorbed into the fixed start. Remove proper prime powers from the
Mangoldt sum, with allowance $O(\sqrt x\log^2x)$, negligible since
$r>r_\Theta>1/2$. With the original right-continuous convention this
supplies, uniformly in the full indicated length range,

$$
\theta_1(x+h)-\theta_1(x)
=h\left(1+O_{\Theta,r}\!\left(e^{-(\log x)^{1/4}}\right)\right),
\qquad x^r\le h\le x^{99/100}.
\tag{DST3}
$$

This is the Chebyshev consequence of the Mangoldt proof itself; no
unaccounted loss is introduced by only multiplying a prime-counting
error by $\log x$. The cap is the global zero-free statement at the
new truncation $T$, not NE3's specialized original-mask height.

### Pay WRC4 and reuse the complete transport

LDS2 permits a single fixed
$r_\Theta<r<\min\{1-\eta,99/100\}$. For each fixed finite $R>1$
and every original core $B\le RX$, the unchanged floor gives

$$
\frac{t}{B^r}\ge\frac{d}{8R^r}
 X^{1-\eta-r}\log X\longrightarrow\infty.
$$

Together with the original uniform $t/B\to0$, DST3 supplies SI2's
variable blocks. Its same disjoint covering and full endpoint correction
$K-\theta_1=O(\sqrt x)$ therefore give WRC4 for this fixed $R$.
For every retained $B>RX$, WRC5's source-capacity and positive-height
bound remains $C_4/R+C_5/M$ without any short-interval input or global
clock ceiling. First choose $R$, then the common source start. WRC2--WRC3
and WRC6--WRC7 now apply unchanged on the entire LDS2 region:

$$
\boxed{
\sup_{\text{original labels and ties}}
 \frac{|G_a(A)-G_a(B)|}{G_a(B)}\longrightarrow0,
\qquad
\frac{\mathcal G_X^A}{\mathcal G_X}\longrightarrow1,
\qquad
\frac{\displaystyle\int_{D_X}G_a(v)\,dv}{\mathcal G_X}
 \longrightarrow1.}
\tag{DST4}
$$

The complete future response and original compensation are both
retained. LDS's common raw-head consumer and WRC7 give the same relative
common-head comparison on this range. For $\Theta\ge9/13$, including
$\Theta=1$, the upper bound is $\eta<17/39$; for
$1/2<\Theta<9/13$, it is $\eta<(2-\Theta)/3$, always retaining
$1-\Theta<\eta<1/2$. The cited unrefereed LDS1 input is needed for the
former extension; the latter uses the classical Ingham input.

Constants and starts may depend on the fixed $\Theta$, $\eta$ and $r$.
No uniformity at the boundary of LDS2, absolute $o(M)$ recentering error,
normalized-response ceiling, second compensation credit or signed upper
on the selected set follows. This application has no host Lean
verification; full original-range compensation, strict Robin for every
integer above 5040 and RH remain unproved.


## The actual total-clock pressure supplies a joint margin without capacity loss

Keep the complete original conditional RH-failure source, every fixed
$1-\Theta<\eta<1/2$, all full windows, outgoing weights, maximizing ties
and trace conventions. Keep the original positive $a<1$ unchanged.
Reuse APC2's all-real pressure identity, EDH1's envelope descent,
AO5's complete-response variation and JVM1--JVM4's analytic infimum.
The additional consumer is the full compensated response at the actual
total clock, before transporting any estimate back to the own-core clock.
There is no new generic variational theorem, prime-counting input,
literature-priority claim or Lean verification.

### Use the exact total-clock lag before any capacity estimate

Write $A(t)=\mathcal A_X(t)$, $h_m=V_X(t_m)-\gamma$ and
$\Delta V(t)=V_X(t)-V_X(t_m)$. APC1, APC2 and EDH1 give at every real
active clock, including every active tie,

$$
\begin{aligned}
G_a(A(t))={}&s_{A(t)}
 \bigl[h_m+\Delta V(t)+R_{\rm pp}(A(t))\bigr]
 +(1-a)\frac{t}{\sqrt{A(t)}}
 -a\frac{Q(A(t))}{\sqrt{A(t)}},\\
\Delta V(t)={}&\int_t^{t_m}\lambda(A(v))\,dv,\qquad
h_m\ge(d/2)X^{-\eta}-c_m.
\end{aligned}
\tag{TJV1}
$$

Here $c_m\le e^{-\ell_X}$, $R_{\rm pp}\ge0$ eventually and
$|Q(x)|/\sqrt x\le H_Q$. The complete future and original compensation
remain. In particular the total-clock lag coefficient is $1-a$;
no estimate of $B-K(B)$ has entered this identity.

Put $v_i=\sqrt{A_i/X}$ and
$\mathcal S_i=G_a(A_i)-s_{A_i}\Delta V(t_i)$. The same coarse
coercivity calculation as EDH3 gives

$$
\frac{\mathcal S_i}{M_X}
\ge\frac{d(1-\eta)}8v_i+
       \frac{d(1-a)}{16v_i}-o(1).
$$

Indeed $A_i\ge\ell_X$ implies
$\log A_i/\log X\ge(1-\eta)/2$ eventually; use
$h_m\ge(d/4)X^{-\eta}$ and the original $t_i\ge\ell_X$.
The bounded stock allowance divided by $M_X$ tends to zero.
Thus both $\mathcal S_i$ and $G_a(A_i)$ are uniformly positive
eventually. This proof also applies to every real active clock.

### Reuse the full functional with the actual total-clock trajectory

Consider any cofinal sequence on which
$\mathcal G_X^A/(M_XL_X)$ is bounded. With
$x_i=t_i/\ell_X$, $h_i=\delta_i/\ell_X$ and
$v_X(x)=\sqrt{A(\ell_Xx)/X}$, the preceding residual bound controls
both tagged moments $\sum h_i v_i$ and $\sum h_i/v_i$.
N2's all-choice ordering applies to $A$ as well as $B$. OSP2's same
prefix/suffix argument therefore bounds $v_X$ above and away from zero
on every fixed $I_\theta=[1+\theta,2-\theta]$, uniformly in every tie.
This uses no global bound on $A/X$ or normalized response.

On this interior range $\log A/\log X\to1$. TJV1 gives the tagged
static terms
$(d/2)v_i+(d/8)(1-a)x_i/v_i-o(1)$, while its retained envelope integral
gives exactly OSP3 with $s_A,v_X$ in place of $s_B,u_X$.
Use the same bounded-variation product bounds and original mesh as
OSP3--OSP4, retaining every outgoing weight. Positivity permits dropping
only outside tags for this lower comparison. Consequently

$$
\begin{aligned}
\frac{\mathcal G_X^A}{M_XL_X}\ge{}&
 \frac d2\int_{I_\theta}v_X(x)\,dx
 +\frac d8(1-a)\int_{I_\theta}\frac{x}{v_X(x)}\,dx\\
&+\frac d8\int_{1+\theta\le r<z\le2-\theta}
       \frac{v_X(r)}{v_X(z)^2}\,dr\,dz-o(1).
\end{aligned}
$$

Apply JVM2 and JVM6's existing interval rescaling, first fixing
$\theta$ and then taking $\theta\downarrow0$. Any sequence violating
the resulting lower bound would be a bounded-response sequence, so the
argument covers the whole original family. AO5 and the same tagged
monotone-selector quadrature give
$\mathcal I_X^A-\mathcal G_X^A=o(1)$ throughout the original range;
this absolute quadrature statement needs no WRC6 comparison with $B$.
It follows that

$$
\boxed{\liminf\frac{\mathcal G_X^A}{M_XL_X}
=\liminf\frac{\mathcal I_X^A}{M_XL_X}
\ge R_{\rm joint}(1-a).}
\tag{TJV2}
$$

All lower limits are uniform over the original full windows and ties.
This strengthens AO4's scalar margin with the complete changing height,
without a short-interval hypothesis.

### Consume the pure-future and original-core comparisons on their own ranges

For the already existing uncompensated $\mathsf H$, APC2's same exact
account has lag coefficient $1$ and no local stock subtraction. The
preceding argument applies to it with $b=1$. Use JVM1's same formulas to
define $R_{\rm joint}(1)$: here $D_1(v)=2-6v^2$ and
$\nu_1=1/\sqrt3$. The positivity, logarithmic divergence, convex
integrand and smooth extremal in JVM3--JVM4 all hold at this endpoint,
so their same sufficient comparison and value apply. This verifies the
parameter interface; it introduces no new variational problem or
optimizing arithmetic source. FCT3--FCT5 then consume the margin on the
entire original range:

$$
\boxed{\liminf\frac{\mathcal P_X^H}{M_XL_X}
=\liminf\frac{\mathcal H_X^B}{M_XL_X}
=\liminf\frac{\mathcal I_X^H}{M_XL_X}
\ge R_{\rm joint}(1)>\frac d2.}
\tag{TJV3}
$$

The displayed lower limits may be infinite. Their equality follows
from the positive source-relative comparisons already proved in FCT;
it does not assert absolute $o(M_XL_X)$ differences.

On LDS2, DST4 transports TJV2 back to the original compensated response.
HC2 and CQ5 retain every original admissible-height head and the actual
continuous core account. Thus on that range

$$
\boxed{\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge R_{\rm joint}(1-a),}
\tag{TJV4}
$$

with the same lower margin for every original admissible-height head
and $\mathcal J_X$. The upper branch of this transport takes the
unrefereed LDS1 theorem as its cited input, exactly as in DST; TJV2--TJV3
themselves need no additional density input.

For $0<b_1<b_2\le1$, insert JVM2's positive optimizer for $b_2$ in the
$b_1$ comparison. Its extra term is
$(d/8)(b_2-b_1)\int_1^2x/u(x)\,dx>0$, so
$R_{\rm joint}(b_2)>R_{\rm joint}(b_1)$. Therefore TJV4 strictly raises
JVM6's margin wherever $Q_\eta>1$ in LDS2. Likewise
$R_{\rm joint}(1)>R_{\rm joint}(1-a)$, and the same comparison with
OSP5 at $b=1$ gives $R_{\rm joint}(1)>d/2$.

The original $a$ and its one-use credit have not been changed or spent
again. TJV3 concerns the original pure-future head; TJV4 concerns the
original compensated head only on its paid transport range. No fixed
clock-ratio ceiling, extra source, favorable window, or arithmetic
attainment is asserted. The selected signed upper, strict Robin for
every integer above 5040 and RH remain unproved.

## The original witness comparator raises the full response margin

Keep the same original witness, fixed $d,\eta$, window, ceiling, all prime labels, weights and maximizing ties as in TJV. No new density or arithmetic sign input is used.

Let $m$ be the original witness, $\log m=X$, $F(m)\ge\gamma+dX^{-\eta}$, and let $m_0=\operatorname{lcm}(5040,m)$ with $d_0=\log(m_0/m)\in[0,\log5040]$. Reuse N1.1's literal legal comparator $p m_0$, including when $p\mid m_0$. For each original label $p$, $t=\log p$, N1.1 and nonnegative Euler increments give

$$
F(N_p)\ge\gamma+dX^{-\eta}-[f(X+d_0+t)-f(X)].
$$

Since $V_X(t)=F(N_p)-c_p$ and $c_p\le e^{-\ell_X}$, in particular at the original last label

$$
h_m=V_X(t_m)-\gamma\ge dX^{-\eta}-\frac{d_0+t_m}{X\log X}-e^{-\ell_X}
\ge(3d/4-\epsilon_X)X^{-\eta},\qquad\epsilon_X\to0.
\tag{WPH1}
$$

Here the decreasing derivative $f'=\lambda$ gives the first displayed cost bound, $t_m\le2\ell_X=(d/4)X^{1-\eta}\log X$, and $X^\eta/(X\log X)\to0$. This does not assume that $m_0$ belongs to the finite core domain or that $p$ is absent from it. The original full-domain maximization supplies the comparison. The original ceiling $R_X$ is unchanged.

Consume this stronger terminal height in the exact EDH2/TJV1 pressure identities. The old coarse coercivity and compact interior localization remain valid. On each fixed localized interior, the normalized static height term is now $(3d/4)v_X-o(1)$ instead of $(d/2)v_X-o(1)$; all other terms and the complete envelope-descent integral remain unchanged.

For the existing JVM notation $A=\int_1^2u$, the already proved identity $\inf_u A\mathcal D_b[u]=\mathcal C_b$, together with its attained scaling family, directly yields

$$
\inf_u\frac d8[6A+\mathcal D_b[u]]
=\frac d4\sqrt{6\mathcal C_b}
=\sqrt{3/2}\,R_{\rm joint}(b).
\tag{WPH2}
$$

This is reuse of JVM2's homogeneity, not a new generic variational theorem. In the existing interior substitution $x=hz+3\theta$, $u_X(x)=\sqrt h\,\widetilde u(z)$, the changed first term and both retained terms have the same lower factor $h^{3/2}$; $x\ge hz$ pays the lag term as before. First take the original source lower limit at fixed $\theta$ and then $\theta\downarrow0$. The bounded-response contradiction and all-tie quadrature are exactly those of OSP/TJV; the $\epsilon_X$ loss is $o(1)$ on this fixed compact interior.

Thus throughout the full original range $1-\Theta<\eta<1/2$, TJV2 and TJV3 improve to

$$
\liminf\frac{\mathcal G_X^A}{M_XL_X}
=\liminf\frac{\mathcal I_X^A}{M_XL_X}
\ge\sqrt{3/2}\,R_{\rm joint}(1-a),
\tag{WPH3}
$$

$$
\liminf\frac{\mathcal P_X^H}{M_XL_X}
=\liminf\frac{\mathcal H_X^B}{M_XL_X}
=\liminf\frac{\mathcal I_X^H}{M_XL_X}
\ge\sqrt{3/2}\,R_{\rm joint}(1).
\tag{WPH4}
$$

On the same full original range, EDH2/OSP4/JVM6 give for the original own-core compensated source

$$
\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge\sqrt{3/2}\,R_{\rm joint}(1-aQ_\eta).
\tag{WPH5}
$$

The same bound holds for the original admissible-height heads and $\mathcal J_X$ by the already paid HC2/CQ5 comparison. Only on LDS2 does DST4 additionally improve this to

$$
\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge\sqrt{3/2}\,R_{\rm joint}(1-a),
\tag{WPH6}
$$

with the same admissible-height and integral consequences. WPH5 retains the original positive $1-aQ_\eta$ and the existing count suppliers' strict cuts. WPH6 retains DST's explicitly attributed unrefereed density input on its upper branch; WPH3--WPH4 use no such input.

All limits remain uniform over the original full windows and ties. This is a fixed-parameter quantitative strengthening for the same $d,\ell_X,M_X$; it does not obtain the gain by renaming the witness constant and thereby changing the original source. No compensation is spent twice, no source clock or future horizon is replaced, and the analytic minimizer is not asserted to be arithmetically attainable. The actual same-source boundary-minus-credit upper, strict Robin above 5040 and RH remain unresolved. No Lean/kernel verification or literature-priority claim is made.
