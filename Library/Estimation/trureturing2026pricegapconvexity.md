---
bibkey: trureturing2026pricegapconvexity
authors: trureturing research synthesis
year: 2026
title: Actual price-gap moments and the complete selected-source response
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md
claim: Under the supplied original source-window hypotheses, actual envelope gaps have zero mass and price moments and a convex-order constraint. The original discrete prime response splits into exterior stock flux minus selected occupancy, gap costs and the complete Q term. The favorable exterior lower estimate remains unproved.
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
