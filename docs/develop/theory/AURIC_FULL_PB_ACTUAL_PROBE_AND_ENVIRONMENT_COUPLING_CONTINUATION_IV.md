# Full PB actual probes and environment coupling, continuation IV

This volume continues [II](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION_II.md)
and [III](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION_III.md).
References such as II (37.9) and III (58.2) retain their original meanings.
The source environments, probes, positive functionals and parameter intersection
are those of II (37.2)–(37.7) and III (58.39).
The volume is append-only; additions begin after its final append anchor.

## 63. Approximate moments for arbitrary finite tests and the quadratic endpoint rate

**Theorem 63.1 (the full-model endpoint rate).** There is $h_{\rm rate}>0$
with the following property. Fix $h$ satisfying the entire original small-parameter
intersection in III (58.39), $h\le10^{-3}$ and
$0<h<\min(h_{\rm rate},h_{\rm reg})$.
There are finite $C(h)>0$ and $\Lambda(h)>0$, common to both sources and both
orientations, such that for every finite real $\lambda\ge\Lambda(h)$,

$$
K_r(h)-\frac{C(h)}{\lambda^2}
\le\kappa_{(r,h)}(\lambda)<K_r(h),\qquad r\in\{+1,-1\}.
\tag{63.1}
$$

In particular $|\kappa_{(r,h)}(\lambda)-K_r(h)|\le C(h)/\lambda^2$.
Here $\kappa$ is exactly the endpoint of the complete pass set in III Theorem 62.4,
on $0\le k<b(h,\lambda)$, where

$$
b(h,\lambda)=\frac{h\lambda^2}{\sqrt{3(\lambda^2+3/2)}}.
\tag{63.2}
$$

The pass condition retains strict full P2 and both orientations of PB for every
finite Hermitian $X\oplus0_3$, and every positive complex-linear functional on
the whole $M_5(\mathbb C)$, including mixed and environment blocks and every
positive finite mass. The environment of each source is its own II (37.2), with
$a_r=(1/\sqrt2,r)^{\mathsf T}$, $C=\operatorname{diag}(1,2)$,
$T_A=\operatorname{diag}(1,-2)$ and $H_h=2C+hJ_A$.
The cutoff is at least the common cutoff of III Theorem 62.4.
The constants may depend on fixed $h$; no uniform-in-$h$ rate is asserted.

**Proof.** The new estimate is the lower bound in (63.1).
Write $t=\lambda^{-2}$, fix a source $r$, and initially use orientation $i$.
Set $K=K_r(h)$, $a=a_r$, $m=\|a\|^2=3/2$, $H=H_h$ and $B=H+C$.
All norms on real constraint vectors below are Euclidean.

### 63.1 Localization of possible violations

Take $h_{\rm rate}$ sufficiently small that III Theorem 58.2 and its conclusions
about all global minimizing contacts hold, as well as the previously established
critical finite-failure result cited in §63.6. This only decreases the common
positive small-parameter radius; all conditions of III (58.39) remain imposed.

The entire set of minimizing contacts at this fixed $h$ is compact by
II Theorem 41.4 and III Theorem 58.2. Each has
$\epsilon=-1$, $\ell=x+iy\in\operatorname{int}\mathcal B$ and $\zeta>0$,
where $\mathcal B=[1/100,1]\times[103/100,600]$ is III (58.1).
Its visible columns and actor action are bounded. Choose a neighborhood $\mathcal U$
of this whole set with compact closure in the visible variables, such that

$$
\epsilon=-1,\quad \ell\in\mathcal B,\quad
0<\delta\le\zeta\le Z_1,
\quad 0<\alpha_*\le\alpha_\pm\le\alpha^*<\infty
\quad\hbox{on }\overline{\mathcal U}.
\tag{63.3}
$$

The strict weight bounds follow from $\nu=0$, $y>1$ at every such contact.
The neighborhood also bounds $p,q,a_{\rm act},U,t_{\rm req}$ and $\nu$;
$U$ here is the auxiliary actor column in II (37.9), not an independent variable.
No bound on the original domain of $X$ or its variational parameters is imposed.

There are $\eta_0>0$ and $\Lambda_0<\infty$ such that every negative reduced
test with $|k-K|\le\eta_0$ and $\lambda\ge\Lambda_0$ belongs to $\mathcal U$.
Otherwise choose negative tests outside $\mathcal U$ with
$|k_n-K|\le1/n$ and $\lambda_n\ge n$.
II Theorem 37.5, uniformly for bounded $k$ as in III Lemma 62.2, gives a
subsequence converging to a full contact $c$ with $J_K(c)\le0$.
II Theorem 41.5 and the definition of $K$ give $J_K\ge0$ on every contact.
Since $\eta(c)\ne0$ by II Lemma 37.4, equality forces
$\epsilon\zeta(c)<0$ and $\mathscr R(c)=K$.
Thus $c$ is one of the minimizing contacts contained in $\mathcal U$, a contradiction.
The same extraction applies to reduced tests because II (37.13) realizes each of
them on the original environment with $e_0=0$.
Decrease $\eta_0$ so that $|k|\le K+1$ in this assertion.

It therefore suffices to exclude negative tests in this fixed neighborhood at
$k=K-D_r(h)t$, once $D_r(h)$ is chosen and $\lambda$ is sufficiently large.
All constants in the next three subsections depend only on this neighborhood
and fixed $h,r$.

### 63.2 Exact finite-test residual identities

Use the actual finite residuals $\mathsf P,\mathsf Q,\nu,U,v$ and $t_{\rm req}$
of II (37.8)–(37.9), with $\rho=kt$; none is set to zero.
Put

$$
\begin{gathered}
D=t_{\rm req},\qquad
\eta=\frac{a^*D}{m},\qquad D_\perp=D-\eta a,\\
E^2=\|\mathsf P\|^2+\|\mathsf Q\|^2+|\nu|^2+\|D_\perp\|^2,\\
Q_e=\mathsf Q-ktT_Au-\nu U/2,\qquad
\Delta a=-iC^{-1}Q_e,\\
\Delta q=-\frac{2i}{\ell}(\mathsf P+\nu p)
            +(I_2+2\ell^{-1}C^{-1})Q_e.
\end{gathered}
\tag{63.4}
$$

Solving $Q_e=iCv-\ell p$ and then
$\mathsf P=v-\nu p+\ell U/2$, using $U=iq+BCu+Cv$, gives the exact identities

$$
\begin{aligned}
a_{\rm act}&=i(I_2-\ell C^{-1})p+\Delta a,\\
q&=(\ell I_2+2C^{-1})p+iBCu+\Delta q.
\end{aligned}
\tag{63.5}
$$

In particular the $kt$ term and both occurrences of $\nu$ are retained in
the error columns. Their norms satisfy
$\|Q_e\|+\|\Delta a\|+\|\Delta q\|\le L_0(E+t)$ on $\mathcal U$:
this follows directly from (63.4), bounded $p,U,k$, and $|\ell|\ge103/100$.

Here are all the errors in the four real Hermitian graph conditions.
Write $w_u=\overline u_1u_2$ and define the following quantities;
$d_0,d_1$ are complex and all the other quantities in (63.6) are real:

$$
\begin{gathered}
\beta=3|u_1|^2+12|u_2|^2+3h\operatorname{Re}w_u,\\
\gamma=3|u_1|^2+24|u_2|^2+4h\operatorname{Re}w_u,\qquad
j=h\operatorname{Im}w_u,\\
Z_*=-3|u_1|^2+12|u_2|^2-h\operatorname{Re}w_u=2\gamma-3\beta,\\
d_0=u^*\Delta q,\qquad d_1=(Cu)^*\Delta q,\\
\Delta m=-\frac{\operatorname{Im}d_0}{y},\qquad
\Delta n=\frac{(x+3)\Delta m+\operatorname{Re}d_0}{2},\\
\Delta\alpha=2\Delta m-\Delta n,\qquad
\Delta\chi=\Delta n-\Delta m,\qquad
\Delta\kappa=\frac{y\Delta n+\operatorname{Im}d_1}{x},\\
\alpha=\frac{(x-1)\beta/y+j}{2},\qquad
\chi=-\frac{(x+1)\beta/y+j}{2},\qquad
\kappa=\frac{Z_*-x\beta-yj}{2x}.
\end{gathered}
\tag{63.6}
$$

To verify these formulas, put $m_p=u^*p\in\mathbb R$ and $n_p=u^*Cp$.
The exact graph identities $u^*q=p^*Cu$ and $\operatorname{Im}((Cu)^*q)=0$
give, after (63.5),

$$
\begin{gathered}
(\ell+3)m_p-2\operatorname{Re}n_p+i\beta-j+d_0=0,\\
\operatorname{Im}(\ell n_p)+\gamma+\operatorname{Im}d_1=0.
\end{gathered}
\tag{63.7}
$$

Their imaginary, real, and remaining imaginary parts give respectively

$$
\begin{aligned}
m_p&=-\beta/y+\Delta m,\\
\operatorname{Re}n_p&=-((x+3)\beta/y+j)/2+\Delta n,\\
\operatorname{Im}n_p&=-\kappa-\Delta\kappa.
\end{aligned}
\tag{63.8}
$$

Since $\overline u_1p_1=2m_p-n_p$ and
$\overline u_2p_2=n_p-m_p$, this proves

$$
\begin{aligned}
\overline u_1p_1&=\alpha+\Delta\alpha+i(\kappa+\Delta\kappa),\\
\overline u_2p_2&=\chi+\Delta\chi-i(\kappa+\Delta\kappa).
\end{aligned}
\tag{63.9}
$$

No actor coordinate was divided out. The errors in (63.6) are bounded by
$L_1\|\Delta q\|$, since $x\ge1/100$ and $y\ge103/100$ on $\mathcal B$.
There is also an exact off-contact correction to II (41.6):

$$
\begin{aligned}
\zeta&=Z_*+\Delta\zeta,\\
\Delta\zeta&=-3\operatorname{Im}d_0+2\operatorname{Im}d_1
 +\operatorname{Re}(iQ_e^*C^{-1}T_Au).
\end{aligned}
\tag{63.10}
$$

Indeed $v=-i\ell C^{-1}p-iC^{-1}Q_e$ and $C^{-1}T_A=3I_2-2C$ give
$\zeta=\operatorname{Re}(i\overline\ell(3m_p-2\overline n_p))
+\operatorname{Re}(iQ_e^*C^{-1}T_Au)$.
Using (63.7), the first term is $3ym_p+2\gamma+2\operatorname{Im}d_1$,
which is (63.10). In particular
$|\Delta\zeta|\le7\|\Delta q\|+\|Q_e\|$.

### 63.3 The five approximate moment constraints

Form the actual positive semidefinite matrix

$$
z=\frac{(u_1,ru_2,\eta)^{\mathsf T}}{\sqrt\zeta},\qquad Y=zz^*.
\tag{63.11}
$$

This matrix need not be feasible for III (58.2). Its five errors are as follows;
$Z,R_1,R_2,\mathcal A_{\ell,rh},b_0$ have exactly their III (58.2) meanings:

$$
\begin{aligned}
Z(Y)-1={}&-\Delta\zeta/\zeta,\\
R_1(Y)={}&\frac{\sqrt2}{\zeta}
 \left[i(1-\ell)(\Delta\alpha+i\Delta\kappa)
 +\overline u_1\Delta a_1
 +\frac{\omega\nu}{2}|u_1|^2-\overline u_1(D_\perp)_1\right],\\
R_2(Y)={}&\frac{1}{\zeta}
 \left[i(1-\ell/2)(\Delta\chi-i\Delta\kappa)
 +\overline u_2\Delta a_2
 +2\omega\nu|u_2|^2-\overline u_2(D_\perp)_2\right].
\end{aligned}
\tag{63.12}
$$

The real and imaginary parts of the last two lines, together with the first
line, are the required five real residuals. For verification use

$$
D=i(I_2-\ell C^{-1})p+\Delta a-Hu+\ell C^2u/2+\omega\nu C^2u/2
=\eta a_r+D_\perp.
\tag{63.13}
$$

Multiply its first coordinate by $\overline u_1$ and its second by
$\overline u_2$, and substitute (63.9).
The terms without $\Delta\alpha,\Delta\chi,\Delta\kappa,\Delta a,\omega\nu$
are exactly $M_1/\sqrt2$ and $M_2$ of III (58.2), evaluated on
$(u_1,ru_2,\eta)(u_1,ru_2,\eta)^*$.
Here $g=rh$, $w=r\overline u_1u_2$, so the source terms are
$-gw=-h\overline u_1u_2$ and $-g\overline w=-h\overline u_2u_1$.
The source equations supply $\eta\overline u_1/\sqrt2$ and
$r\eta\overline u_2$, respectively. Dividing by $\zeta$ proves (63.12).
Its first line follows from $Z(Y)=Z_*/\zeta$ and (63.10).
Thus both complex source equations, including transverse demand, survive.

Since $|\omega|<1$, (63.3)–(63.12) imply the quantitative bound

$$
\|\mathcal A_{\ell,rh}(Y)-b_0\|\le L_2(E+t).
\tag{63.14}
$$

This is an estimate for the matrix of the same finite test, not a declaration
of exact feasibility or a correction to a minimizing contact.

### 63.4 Uniformly bounded duals on the price rectangle

For fixed $g=rh$, III (58.7) gives an attained optimal dual vector $d$ at every
$\ell\in\mathcal B$. These vectors can be chosen with a common finite norm bound;
in fact every optimal dual vector has such a bound.
To see this, take the explicit matrix $Y^{\rm sf}_{\ell,g}$ in III (58.33)
with $e=|M_1|^2+3|M_2|^2+1$.
It is continuous in $\ell$, strictly positive definite and feasible.
Compactness of $\mathcal B$ gives

$$
Y^{\rm sf}_{\ell,g}\succeq\sigma I_3,\qquad
\langle C_y,Y^{\rm sf}_{\ell,g}\rangle\le V
\tag{63.15}
$$

with $\sigma>0$ and finite $V$. For an optimal dual put
$S=C_y-\mathcal A_{\ell,g}^*d\succeq0$.
Since $d_0=v(\ell,g)\ge0$,

$$
\sigma\operatorname{tr}S
\le\langle S,Y^{\rm sf}_{\ell,g}\rangle
=\langle C_y,Y^{\rm sf}_{\ell,g}\rangle-v(\ell,g)\le V.
\tag{63.16}
$$

Consequently $S$ and $\mathcal A_{\ell,g}^*d=C_y-S$ are uniformly bounded.
The map $\mathcal A_{\ell,g}^*$ is injective: varying only $Y_{31},Y_{32}$
in the real pairing first forces $d_1=d_2=d_3=d_4=0$; the remaining constraint
$Z=-3Y_{11}+12Y_{22}-g\operatorname{Re}Y_{21}$ is nonzero and forces $d_0=0$.
Continuity and compactness therefore give
$\|\mathcal A_{\ell,g}^*d\|\ge\mu\|d\|$ for a common $\mu>0$.
This proves $\|d\|\le M$ uniformly, without requiring a continuous choice of dual.

Pair this dual with the possibly infeasible PSD matrix (63.11).
Weak duality in its exact residual form and III (58.5) give

$$
\begin{aligned}
c_yY_{33}
&=\langle S,Y\rangle+d\cdot\mathcal A_{\ell,g}(Y)\\
&\ge v(\ell,g)-M\|\mathcal A_{\ell,g}(Y)-b_0\|\\
&\ge K-ML_2(E+t).
\end{aligned}
\tag{63.17}
$$

Since $4c_y=s(y)=2y/(y^2-1)$, multiplying by $4\zeta$ yields

$$
s(y)|\eta|^2\ge4\zeta K-L_3(E+t).
\tag{63.18}
$$

### 63.5 Retaining the finite positive penalties

Let $b_\nu=\operatorname{Im}\nu$. The exact weights of II (37.8), on the
localized $\epsilon=-1$ domain, satisfy

$$
\begin{gathered}
\alpha_\pm=y\pm(1+b_\nu),\qquad
s_\alpha=\frac{2y}{y^2-(1+b_\nu)^2},\qquad
\omega=-\frac{1+b_\nu}{y},\\
s_\alpha-s(y)=
\frac{2y(2b_\nu+b_\nu^2)}
 {[y^2-(1+b_\nu)^2](y^2-1)}.
\end{gathered}
\tag{63.19}
$$

Thus $|s_\alpha-s(y)|\le L_4|\nu|$ on $\mathcal U$.
The source-parallel resolvent coefficient in II (37.36) is exactly
$m/(m+t)$ after multiplication by $\lambda^2$.
II (37.12) consequently reads, with no expansion of a positive square,

$$
\begin{aligned}
F:=\lambda^2\mathcal D^{\rm red}_\lambda
={}&\frac1t\left[
 \sum_{d=\pm1}\alpha_d^{-1}\|\mathsf P+d\mathsf Q\|^2
 +s_\alpha\|D_\perp\|^2
 +\frac{|\nu|^2}{2y}\|C^2u\|^2\right]\\
&+s_\alpha\frac{m}{m+t}|\eta|^2-4k\zeta.
\end{aligned}
\tag{63.20}
$$

By (63.3), $\|C^2u\|\ge1$, and
$\|\mathsf P+\mathsf Q\|^2+\|\mathsf P-\mathsf Q\|^2
=2(\|\mathsf P\|^2+\|\mathsf Q\|^2)$,
the bracket is at least $cE^2$ for some $c>0$.
The boundedness of $\eta,s_\alpha$ and (63.19) give

$$
s_\alpha\frac{m}{m+t}|\eta|^2
=s(y)|\eta|^2+(s_\alpha-s(y))|\eta|^2
  -s_\alpha\frac{t}{m+t}|\eta|^2
\ge s(y)|\eta|^2-L_5E-B_0t.
\tag{63.21}
$$

All the effects of nonzero $\nu$, changing weights, nonzero $\rho=kt$ and
transverse demand have now appeared explicitly in (63.4), (63.12),
(63.19)–(63.21). Combining (63.18)–(63.21), for $k\le K$, gives

$$
\begin{aligned}
F&\ge4\zeta(K-k)+\frac{cE^2}{t}-LE-B_1t\\
&\ge4\delta(K-k)-\left(B_1+\frac{L^2}{4c}\right)t.
\end{aligned}
\tag{63.22}
$$

Here $L,B_1$ are finite nonnegative scalar constants.
The last step completes the square in $E$; its positive quadratic term was
retained until this step. Choose

$$
D_r(h)>\frac{B_1+L^2/(4c)}{4\delta}.
\tag{63.23}
$$

At $k=K-D_r(h)t$, (63.22) is strictly positive.
For sufficiently large $\lambda$ this $k$ is positive and satisfies
$|k-K|\le\eta_0$. A negative reduced test would then localize to $\mathcal U$
by §63.1, where (63.22) contradicts negativity.
Therefore every reduced finite test is nonnegative at this moving $k$.

### 63.6 Original domain, the endpoint, and sources

II (37.12) restores the nonnegative term $s_\alpha\|e_0\|^2$, so every original
normalized finite test is also nonnegative. II (37.7) then gives vector PB.
The variational identity used there includes Gram degeneracy and does not
require its infimum to be attained. II (37.45) removes actor normalization;
II (37.46) handles actor-zero vectors. The spectral sum and real Gram
superadditivity in II (37.47) give PB for every positive functional on the
whole algebra. In particular singular densities, mixed/environment blocks,
arbitrarily small actor mass and every positive finite total mass remain included.

II (39.32), with the conventions of III (46.3), transports the argument to
orientation $-i$ on the same source. It preserves $r$ and the adapted $x,y$
coordinates. There are only two sources and two orientations, so constants
and cutoffs can be enlarged to be common.

For fixed $h>0$, $b(h,\lambda)\to\infty$.
Increase the cutoff so that both inward prices $K_r(h)-D_r(h)/\lambda^2$ are
positive and below $b(h,\lambda)$. By II (39.7), this is the complete original
strict P2 condition, not a single-vector surrogate.
Taking also the common cutoff in III Theorem 62.4 proves

$$
\kappa_{(r,h)}(\lambda)\ge K_r(h)-D_r(h)/\lambda^2.
\tag{63.24}
$$

For the other inequality reuse the existing
[critical finite-failure calculation](https://github.com/the-omega-institute/trureturing/issues/29504#issuecomment-6819069391).
It supplies failure at $k=K_r(h)$ for both orientations, with strict full P2,
on its original small-$h$ radius and with its stated cutoff
$\max(2,1+\sqrt6K_r(h)/h)$.
Keep that radius in $h_{\rm rate}$ and include both such cutoffs in $\Lambda(h)$.
Its proof and finite witness construction are not new results here.
Since III Theorem 62.4 identifies the entire pass set as $[0,\kappa]$,
this failure implies $\kappa_{(r,h)}(\lambda)<K_r(h)$.
Taking $C(h)=\max_r D_r(h)>0$ proves (63.1).
Every cutoff is finite at fixed $h$, and every assertion holds on the full real
tail of $\lambda$. No monotonicity in $\lambda$, finite-PB minimizer, isolated
contact set, unique root, quadratic growth or additional regularity was used. $\square$

### 63.7 Mathematical sources and limits

The defining source for II §§37–43 and III §§50–62 is revision
`65680da08471f736d5489291f52a85a1168e3c70`:
[II](https://github.com/the-omega-institute/trureturing/blob/65680da08471f736d5489291f52a85a1168e3c70/docs/develop/theory/AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION_II.md)
and
[III](https://github.com/the-omega-institute/trureturing/blob/65680da08471f736d5489291f52a85a1168e3c70/docs/develop/theory/AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION_III.md).
The critical upper-side calculation is the separately cited existing result.
The model-specific addition is the finite-test residual transport (63.4)–(63.14)
and its all-test quantitative lower comparison (63.22)–(63.24), classified
as `repo-derived`. The compactness, exact environment elimination, contact SDP,
Slater matrices, interval theorem and critical upper side are reused.
Uniform boundedness of duals here follows directly from those Slater matrices,
finite-dimensional compactness and injectivity; no general perturbation theorem
or new regularity premise is needed.

The literature search for the endpoint-rate problem is bounded rather than
exhaustive; no literature-priority claim is made. The theorem gives neither
effective numerical constants nor a uniform-in-$h$ cutoff, and does not decide
the separate comparison of the two limiting thresholds. It concerns the stated
finite matrix model, without a physical realization claim.

## 追加锚（本行以下为增补区）
