# Same-source attractive boundary response: phase-aligned original-domain gluing

## 31. Phase-aligned gluing in the original physical operator domain

**Definition 31.1 (unchanged original source, form and natural domains).**
Use precisely Definition 18.1 of
[Same-source native attractive boundary response](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
with its analytic suppliers and normalizations at revision
[d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md).
The conditional interfaces from Sections 24, 26 and 30 of
[the complete Green marginal continuation](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md)
are used as stated at revision
[0564383e90de0a8b3a12e6e7628d9aef9218a848](https://github.com/the-omega-institute/trureturing/blob/0564383e90de0a8b3a12e6e7628d9aef9218a848/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md).
In particular, the analytic hypotheses are the original-field heat
formulas and locally uniform off-pole convergence of Theorem 10.2,
the full complex polar identity (12.12)--(12.13), the closed natural
angular form and compact embedding supplied by V, Theorem 10.2,
the natural-core approximation (13.6)--(13.8), the complete-field
scaling (14.9), and the original closed form, compact smooth core
and local estimates (15.9)--(15.12). Suppliers C and V have exactly
the statements fixed in original Definition 1.1 at revision
5cec4fa83ae7bbb4e787c42606525db4cd11ed48. No additional analytic
hypothesis is imposed below.

For clarity, the complete source and parent generator are

$$
\begin{aligned}
U_k&=\partial_{x_k}-\tfrac12y_k\partial_z,
&V_k&=\partial_{y_k}+\tfrac12x_k\partial_z,
&Z&=\partial_z,\\
L_{n,\epsilon}&=-\sum_{k=1}^n(U_k^2+V_k^2)-\epsilon^2Z^2,\\
M_{n,\epsilon}(x,y,z)
 &=\int_0^\infty\int_{\mathbb R^{2n-2}}
       (e^{-tL_{n,\epsilon}}\delta_0)(x,y,W,z)\,dW\,dt.
\end{aligned}
\tag{31.1}
$$

The heat column is the original compact-smooth Friedrichs heat
column with identity unit source, raw Lebesgue measures, horizontal
covariance $2$ and central covariance $2\epsilon^2$. Both integrals
in (31.1) are complete and unweighted. Fix $\epsilon=1$, retaining
the original fields and units. On retained $\mathbb R^3$ put

$$
\begin{aligned}
P&=M_{n,1},&d\xi&=dx\,dy\,dz,\\
U&=\partial_x-\tfrac y2\partial_z,
&V&=\partial_y+\tfrac x2\partial_z,
&\mathcal X&=\{U,V,Z\},\\
\mathcal H_1
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^{\,\|\cdot\|_{\rm free}},
&\|u\|_{\rm free}^2
 &=\|u\|_2^2+\sum_{X\in\mathcal X}\|Xu\|_2^2,\\
q(u,v)&=\sum_{X\in\mathcal X}\langle Xu,Xv\rangle
                   -g\int_{\mathbb R^3}Pu\overline v\,d\xi,
&D(q)&=\mathcal H_1,\qquad \mathscr A=A_{n,1,g}.
\end{aligned}
\tag{31.2}
$$

All inner products are linear in the first argument. The operator
$\mathscr A$ is the full complex Friedrichs realization of $q$,
including the original pole. In particular its domain is

$$
D(\mathscr A)=\{u\in\mathcal H_1:
 \text{there is }a\in L^2(d\xi)\text{ with }
 q(u,v)=\langle a,v\rangle\text{ for every }v\in\mathcal H_1\},
\qquad \mathscr Au=a.
\tag{31.3}
$$

Original (15.11)--(15.12) give an infinitesimal form bound, so a
sufficiently shifted $q$ norm is equivalent to the free norm and
$C_c^\infty(\mathbb R^3;\mathbb C)$ remains a form core. The space
$\mathcal H_1$ is not replaced by a global isotropic Sobolev space.

Use the actual gauge coordinates

$$
\begin{aligned}
R&=((x^2+y^2)^2+16z^2)^{1/4},&\ell&=\log R,
&\delta_r(x,y,z)&=(rx,ry,r^2z),\\
\omega(a,\varphi)&=(\sqrt{\cos a}\cos\varphi,
 \sqrt{\cos a}\sin\varphi,\sin a/4),
&d\xi&=\tfrac14e^{4\ell}\,d\ell\,da\,d\varphi,\\
J&=(-\pi/2,\pi/2),&c(a)&=\cos a,\\
\mathcal H_c&=\{v\in L^2(J,da):v\in AC_{\rm loc}(J),
                                  \ \sqrt c\,v'\in L^2(J,da)\},\\
A[v]&=\int_J(4c|v'|^2+c|v|^2)\,da,
&C[v]&=\int_Jc|v|^2\,da,
&\|v\|_{\mathcal H_c}^2&=A[v]+\|v\|_{L^2(da)}^2.
\end{aligned}
\tag{31.4}
$$

There are no imposed angular endpoint values. Explicitly the original
angular coefficients and threshold are

$$
\begin{aligned}
I_n&=\int_0^{\pi/2}\sin^{n-2}t\,dt,
&q_n(a)&=\frac1{I_n}\int_0^1
             \frac{v^{n-2}}{\sqrt{1-v^2\sin^2a}}\,dv,\\
Q_n[v]&=\int_Jq_n|v|^2\,da,
&\mu_n&=\inf_{0\ne v\in\mathcal H_c}\frac{A[v]}{Q_n[v]},
&\lambda_n&=2\pi\mu_n.
\end{aligned}
$$

The original natural pencil $H_{n,g}(\sigma,m)$ is the operator
on complex $L^2(J,da)$ associated with

$$
h_{n,g}(\sigma,m)[v]
 =A[v]+\int_J c(a)(\sigma+m\tan a)^2|v|^2\,da
                                  -\frac{g}{2\pi}Q_n[v],
\qquad \sigma\in\mathbb R,\quad m\in\mathbb Z.
$$

The coefficient is the original all-integer-mode phase integral

$$
L=L_{n,g}=\frac1{4\pi}\sum_{m\in\mathbb Z}
 \int_{\mathbb R}\dim_{\mathbb C}\operatorname{Ran}
 \mathbf1_{(-\infty,0)}(H_{n,g}(\sigma,m))\,d\sigma.
\tag{31.5}
$$

Its domains remain $D_0=\mathcal H_c$ and
$D_m=\mathcal H_c\cap L^2(J,\sin^2a/c\,da)$ for $m\ne0$.
For an axisymmetric $f$ use the actual gauge

$$
w_f(\ell,a)=\sqrt{2\pi}\,e^\ell
             f(\delta_{e^\ell}\omega(a,\varphi)),\qquad
4\|f\|_2^2=\int e^{2\ell}\|w_f(\ell)\|_{L^2(J,da)}^2\,d\ell.
\tag{31.6}
$$

The same identity holds on gauge strips. Its angular mass is
unweighted $da$, not the auxiliary $c\,da$ mass. Original (14.9),
(15.7), and (25.2), (26.6) of the continuation give, throughout a
sufficiently remote exterior,

$$
P(\delta_{e^\ell}\omega(a,\varphi))
 =e^{-2\ell}\left(\frac{q_n(a)}{2\pi}+B_n(\ell,a)\right),
\qquad \|B_n(\ell,\cdot)\|_\infty\le C e^{-2\ell},
\qquad |P|\le C e^{-2\ell}.
\tag{31.7}
$$

The bounds include the entire angular interval and the complete
source, including the central contribution.

**Definition 31.2 (the supplied core and physical exterior family).**
For every integer $n\ge2$ and every fixed
$g\in(\lambda_n,g_n^{\rm iso})$, use the entire isolation interval
of Lemma 24.2. Proposition 24.3 and (26.5) supply
$s=2\pi L>0$ and a real positive even $\psi\in\mathcal H_c$ with
$C[\psi]=1$ and

$$
\left(A-\frac{g}{2\pi}Q_n\right)(\psi,v)
             =-s^2C(\psi,v)\qquad(v\in\mathcal H_c).
$$

Here forms are polarized linearly in their first argument. These
are derived parameters, not added restrictions on $n,g$. All
constants below may depend on the fixed pair $n,g$.

Theorem 26.2 supplies a real axisymmetric $z$-even $f_0$, defined
on all of $\mathbb R^3$, and $b\in\mathbb C\setminus\{0\}$.
For every $\eta\in C_c^\infty(\mathbb R^3)$ one has
$\eta f_0\in\mathcal H_1$, and
$q(f_0,\phi)=0$ for every original complex compact smooth test
$\phi$, including tests through the pole. With continuous slice
representatives and $w_0=w_{f_0}$,

$$
\begin{aligned}
\|w_0(\ell)-2\operatorname{Re}(be^{is\ell})\psi\|_{\mathcal H_c}
 &\longrightarrow0,\\
\|\partial_\ell w_0(\ell)
       -2\operatorname{Re}(isbe^{is\ell})\psi\|_{L^2(c\,da)}
 &\longrightarrow0\qquad(\ell\longrightarrow\infty).
\end{aligned}
\tag{31.8}
$$

This is a global local-form solution; neither global $L^2$
membership nor membership in $D(\mathscr A)$ is presumed for $f_0$.

Write $F_E$ for the single exterior family furnished by Theorem
30.6. There are fixed $R_0>1$, $E_0\in(0,1)$ and $\beta\in\mathbb C$
with $|\beta|=1$ such that for every $0<E<E_0$, $F_E$ is real,
axisymmetric and $z$-even on $\Omega_{R_0}=\{R>R_0\}$. Every compact
smooth exterior multiplier of $F_E$ belongs to $\mathcal H_1$, and

$$
q(F_E,\phi)+E\langle F_E,\phi\rangle=0
\quad\bigl(\phi\in C_c^\infty(\Omega_{R_0};\mathbb C)\bigr).
\tag{31.9}
$$

The test class includes all nonaxisymmetric complex tests. For every
$R_0<r_1<r_2<\infty$ and every smooth real radial $\eta$, with
$0\le\eta\le1$, $\eta=0$ on $R\le r_1$ and $\eta=1$ on $R\ge r_2$,
the physical tail $\eta F_E$ belongs to $\mathcal H_1$, with zero
extension inward. This includes the physical $L^2$ mass and all
three original field energies.

Set $w_E=w_{F_E}$ and $T_E=\tfrac12\log(1/E)$. The value and
derivative slice representatives satisfy, with the same $\beta$
for every sufficiently small $E$,

$$
\begin{aligned}
\mathfrak r_E(\ell)
 &=\|w_E(\ell)-2\operatorname{Re}(\beta e^{is(\ell-T_E)})\psi
                                                   \|_{\mathcal H_c}\\
 &\quad+\|\partial_\ell w_E(\ell)
       -2\operatorname{Re}(is\beta e^{is(\ell-T_E)})\psi\|_{L^2(c\,da)},\\
\lim_{K\to\infty}\limsup_{E\downarrow0}
          \sup_{K\le\ell\le T_E-K}\mathfrak r_E(\ell)&=0.
\end{aligned}
\tag{31.10}
$$

Here $K>\log R_0$ and the inner limit uses $T_E>2K$.
Equivalently, for each $\varepsilon>0$ there is $K_0$ such that for
every fixed $K\ge K_0$ there is $E_K>0$ for which every
$0<E<E_K$ and every $\ell\in[K,T_E-K]$ have
$\mathfrak r_E(\ell)<\varepsilon$. No continuity in $E$ is required.
All higher even components of $f_0$ and $F_E$ are retained.
Neither solution is replaced by its $\psi$ component. Every kernel
or zero-energy resonance allowed by the original hypotheses remains
allowed, with no exceptional coupling or energy removed.

**Definition 31.3 (all-level phase alignment and the glued vectors).**
Fix any arguments $\theta_b,\theta_\beta\in\mathbb R$ with
$b=|b|e^{i\theta_b}$ and $\beta=e^{i\theta_\beta}$. For integers $j$ put

$$
\begin{aligned}
T_j&=\frac{\theta_\beta-\theta_b+\pi j}{s},
&E_j&=e^{-2T_j}=D_{\rm align}e^{-j/L},\\
D_{\rm align}&=\exp\left(-\frac{2(\theta_\beta-\theta_b)}s\right)>0,
&c_j&=(-1)^j|b|.
\end{aligned}
\tag{31.11}
$$

Thus $T_j\to\infty$ and $E_j<E_0$ for every sufficiently large
integer $j$. Fix any real $\chi\in C^\infty(\mathbb R)$ with
$0\le\chi\le1$, $\chi(t)=1$ for $t\le0$ and $\chi(t)=0$ for
$t\ge1$. For any real sequence $M_j$ satisfying

$$
M_j\longrightarrow\infty,\qquad T_j-M_j\longrightarrow\infty,
\tag{31.12}
$$

define $\chi_j(\xi)=\chi(\ell(\xi)-M_j)$ away from the pole and
continue it as $1$ near the pole. On the exterior overlap put

$$
\begin{aligned}
d_j&=f_0-c_jF_{E_j},\\
h_j&=\chi_jf_0+(1-\chi_j)c_jF_{E_j},\\
\Delta_j&=\sup_{M_j-1\le\ell\le M_j+2}
              \|w_0(\ell)-c_jw_{E_j}(\ell)\|_{L^2(J,da)}.
\end{aligned}
\tag{31.13}
$$

The outer summand in $h_j$ is extended by zero inward; it is
well-defined for every sufficiently large $j$. The constant
$D_{\rm align}$ specifies equality of leading-wave phases only.

**Theorem 31.4 (original-domain gluing and quantitative physical residual).**
Under exactly Definitions 31.1--31.2, for every integer $n\ge2$,
every fixed $g\in(\lambda_n,g_n^{\rm iso})$, every fixed choice in
Definition 31.3 and every sequence satisfying (31.12), one has
$\Delta_j\to0$. For every sufficiently large integer $j$,
$h_j$ is a nonzero member of the full original complex
$D(\mathscr A)$, and there are constants $c_*,C_*>0$, independent
of $j$, such that

$$
\|h_j\|_{L^2(d\xi)}\ge c_*e^{T_j}=c_*E_j^{-1/2}.
\tag{31.14}
$$

In the original $L^2(d\xi)$ space the exact identity is

$$
(\mathscr A+E_j)h_j
 =E_j\chi_jf_0
 -2\sum_{X\in\mathcal X}(X\chi_j)(Xd_j)
 -\sum_{X\in\mathcal X}(X^2\chi_j)d_j.
\tag{31.15}
$$

Both commutator sums are supported on $M_j\le\ell\le M_j+1$.
Moreover,

$$
\frac{\|(\mathscr A+E_j)h_j\|_{L^2(d\xi)}}
     {E_j\|h_j\|_{L^2(d\xi)}}
 \le C_*\left(e^{M_j-T_j}+e^{T_j-M_j}\Delta_j\right).
\tag{31.16}
$$

The constants and the first usable index may depend on fixed
$n,g$ and the fixed choices. No parameter-uniform estimate,
projection eliminating higher even components, kernel exclusion or
extra angular endpoint condition is asserted.

Proof. The exact phase computation is

$$
c_j\beta e^{-isT_j}
 =(-1)^j|b|e^{i\theta_\beta}
       e^{-i(\theta_\beta-\theta_b+\pi j)}=b.
\tag{31.17}
$$

Consequently the leading waves in (31.8) and $c_j$ times (31.10)
agree at every $\ell$. To use the double limit with a moving
strip, fix an error tolerance and choose a fixed sufficiently large
$K$ in (31.10). By (31.12), for every sufficiently large $j$,

$$
[M_j-1,M_j+2]\subset[K,T_j-K].
\tag{31.18}
$$

The wall error is then small for every sufficiently large $j$,
since $E_j\downarrow0$. The core value error is uniformly small
on the same strip by (31.8). The norm $\mathcal H_c$ controls
$L^2(da)$ and $|c_j|=|b|$, so the triangle inequality proves
$\Delta_j\to0$. This uses every sufficiently large integer, without
an energy subsequence or an energy-continuity premise.

For the domain assertion, $\chi_j$ is a compact smooth Cartesian
multiplier of $f_0$. Indeed $R$ and $\ell$ are smooth off the
pole, including the physical axis points with $z\ne0$, and the
cutoff is constant near the pole. Thus $\chi_jf_0\in\mathcal H_1$
by (31.8)'s local-form premise. The other summand is exactly an
allowed physical outer cutoff in Definition 31.2, with
$r_1=e^{M_j}>R_0$ and $r_2=e^{M_j+1}$. Hence
$h_j\in\mathcal H_1$, including its inward zero extension and its
full physical tail.

The fields $U,V,Z$ are divergence-free with respect to $d\xi$.
Their product rules in the local weak equations (31.8)--(31.9)
give (31.15) against every compact smooth complex Cartesian test.
The signs follow from the differential expression
$-\sum_{X\in\mathcal X}X^2-gP$; the potential commutes with the
cutoff. The term $E_j\chi_jf_0$ is in $L^2$ by local-form
membership. The remaining coefficients are smooth and supported
on a compact annulus away from the pole, where $d_j$ and all
$Xd_j$ are locally $L^2$. Thus the right side of (31.15) is an
actual $L^2(d\xi)$ vector, denoted by $r_j$.

The compact-test identity says
$q(h_j,v)=\langle r_j-E_jh_j,v\rangle$ on the original compact
smooth core. Continuity of $q$ on $\mathcal H_1$ and density of
that core in the shifted form norm extend it to every
$v\in\mathcal H_1$. The representation characterization (31.3)
therefore yields $h_j\in D(\mathscr A)$ and (31.15) as an $L^2$
identity. This argument does not require $Pf_0\in L^2$, or
operator-domain membership of either uncut solution.

For the residual estimate, temporarily suppress the index $j$ and
write $T,E,M,d,h,\Delta$ for the corresponding quantities. Let
$\chi_M=\chi(\ell-M)$ and choose a fixed smooth real profile
$\zeta_M$ equal to $1$ on $[M,M+1]$ and supported within
$(M-1,M+2)$ in the $\ell$ variable. Homogeneity on the compact
unit gauge sphere and smoothness away from the pole give, for
large $M$,

$$
\begin{aligned}
|U\chi_M|+|V\chi_M|&\le C e^{-M},
&|Z\chi_M|&\le C e^{-2M},\\
\sum_{X\in\mathcal X}|X^2\chi_M|&\le C e^{-2M},
&\sum_{X\in\mathcal X}|X\zeta_M|^2&\le C e^{-2M}.
\end{aligned}
\tag{31.19}
$$

In fact $U,V$ have dilation degree $1$ and $Z$ degree $2$;
the $Z^2$ term is bounded by $Ce^{-4M}$ and is included in the
sum displayed above. These are physical Cartesian derivative
bounds, with no angular endpoint integration by parts.

On $S_M^+=\{M-1<\ell<M+2\}$ the weak equations imply
$(\mathscr A+E)d=Ef_0$. Use $\zeta_M^2d$ as an energy test and
take real parts. Local free approximation justifies this compactly
supported test in the local form equation. In the kinetic term,

$$
\operatorname{Re}\langle Xd,X(\zeta_M^2d)\rangle
 =\|\zeta_MXd\|_2^2
   +2\operatorname{Re}\langle \zeta_MXd,(X\zeta_M)d\rangle.
\tag{31.20}
$$

Absorb the cross terms by the elementary quadratic inequality,
drop the nonnegative $E\|\zeta_Md\|_2^2$, and use (31.7) and
(31.19). This is the usual Caccioppoli energy argument, here with
all three original fields and the full source. It yields

$$
\sum_{X\in\mathcal X}\|\zeta_MXd\|_2^2
 \le C\left(e^{-2M}\|d\|_{L^2(S_M^+)}^2
       +E\|f_0\|_{L^2(S_M^+)}\|d\|_{L^2(S_M^+)}\right).
\tag{31.21}
$$

The exact unweighted mass identity (31.6) and the definition of
$\Delta$ give

$$
\|d\|_{L^2(S_M^+)}\le C e^M\Delta,\qquad
\|f_0\|_{L^2(S_M^+)}\le C e^M.
\tag{31.22}
$$

For the second inequality the core trace in (31.8) is bounded in
$L^2(da)$ on the remote exterior. The same bound integrated over
all $\ell\le M+1$, together with local $L^2$ membership on the
finite inner compact region through the pole, proves

$$
\|\chi_Mf_0\|_2\le C e^M,\qquad
\sum_{X\in\mathcal X}\|\zeta_MXd\|_2^2
                \le C(\Delta^2+Ee^{2M}\Delta).
\tag{31.23}
$$

In particular, the forcing term in (31.21) contributes its square
root to the commutator estimate. Combining (31.15), (31.19),
(31.22) and (31.23) gives

$$
\begin{aligned}
\|(\mathscr A+E)h\|_2
 &\le C\left(Ee^M+e^{-M}(\Delta^2+Ee^{2M}\Delta)^{1/2}
                         +e^{-M}\Delta\right)\\
 &\le C\left(Ee^M+e^{-M}\Delta+\sqrt E\sqrt\Delta\right).
\end{aligned}
\tag{31.24}
$$

No estimate on the derivative trace in (31.8) or (31.10) has
been needed for this energy bound.

It remains to bound the physical norm from below. Put
$p=\pi/s$ and $m_\psi=\|\psi\|_{L^2(da)}^2>0$. Choose a fixed
sufficiently large $K>\log R_0$ so that for every sufficiently
small $E$ the value error in (31.10), measured in $L^2(da)$, is
uniformly at most $\eta$ on $[K,T_E-K]$, with
$\eta^2<m_\psi/2$. For small enough $E$, the strip
$I_E=[T_E-K-p,T_E-K]$ lies in that overlap. Since
$|\beta|=1$, one full period of the squared leading wave gives

$$
\int_{I_E}\|2\operatorname{Re}(\beta e^{is(\ell-T_E)})\psi
                                  \|_{L^2(da)}^2\,d\ell
 =2m_\psi p.
\tag{31.25}
$$

The inequality $\|u+v\|^2\ge\tfrac12\|u\|^2-\|v\|^2$
therefore implies

$$
\int_{I_E}\|w_E(\ell)\|_{L^2(da)}^2\,d\ell
 \ge m_\psi p-\eta^2p>\tfrac12m_\psi p.
\tag{31.26}
$$

For $E=E_j$, (31.12) makes $h_j=c_jF_{E_j}$ on this entire
strip for every sufficiently large $j$. By (31.6),

$$
4\|h_j\|_2^2
 \ge |b|^2 e^{2(T_j-K-p)}\tfrac12m_\psi p
 \ge c e^{2T_j}.
\tag{31.27}
$$

This proves (31.14) and nonzero membership at every sufficiently
large level, with the original unweighted angular mass.

Finally divide (31.24) by $E\|h\|_2\ge cE e^T$, using
$E=e^{-2T}$. The resulting upper bound is

$$
C\left(e^{M-T}+e^{T-M}\Delta+\sqrt\Delta\right).
\tag{31.28}
$$

The elementary arithmetic-geometric mean inequality gives
$2\sqrt\Delta\le e^{M-T}+e^{T-M}\Delta$, proving (31.16).

This source-specific deduction uses the original conditional
interfaces stated above. The product rule, compact energy test
and quadratic absorption are standard calculus and weak-equation
arguments, as in Evans, *Partial Differential Equations*, second
edition, Chapters 5--6; the form-domain-to-operator-domain step is
the classical first representation theorem, as in Kato,
*Perturbation Theory for Linear Operators*, second edition,
Chapter VI, Section 2. They are intermediate arguments for this
original-source gluing construction. No zero-energy inverse,
kernel-removing projection or resonance exclusion is used.
$\square$

## 32. All-level residual estimates and the remaining matching rate

**Corollary 32.1 (weaker all-level physical residual).**
Under exactly the hypotheses and full parameter range of Theorem
31.4, fix any $\theta\in(0,1)$ and set $M_j=\theta T_j$ in
Definition 31.3. For every sufficiently large integer $j$ the
vector $h_j$ is nonzero and belongs to the exact original complex
$D(\mathscr A)$, and

$$
\frac{\|(\mathscr A+E_j)h_j\|_2}{\|h_j\|_2}
                 =o\left(E_j^{(1+\theta)/2}\right).
\tag{32.1}
$$

In particular $\theta=1/2$ gives $o(E_j^{3/4})$.

Proof. Both conditions in (31.12) hold. Multiply (31.16) by
$E_j=e^{-2T_j}$ and divide by
$E_j^{(1+\theta)/2}=e^{-(1+\theta)T_j}$. The quotient is bounded by

$$
C\left(e^{-2(1-\theta)T_j}+\Delta_j\right)\longrightarrow0.
\tag{32.2}
$$

The domain, nonzero and all-level assertions are those of Theorem
31.4, without an additional choice of subsequence. $\square$

**Problem 32.2 (relative matching and the full original spectral phase).**
For the particular vectors in Theorem 31.4 a sufficient further
rate is

$$
\Delta_j=o(e^{M_j-T_j}),\qquad
M_j\to\infty,\qquad T_j-M_j\to\infty.
\tag{32.3}
$$

It would make the right side of (31.16) tend to zero. The trace
convergences (31.8) and (31.10) give $\Delta_j\to0$, but no rate
(32.3) is established here. In particular they do not control
$e^{T_j-M_j}\Delta_j$. Failure to obtain this rate from an upper
bound is not a lower bound on attainable residuals and does not
exclude a different matching construction.

The exponent $(1+\theta)/2$ in (32.1) is strictly below $1$.
Thus (32.1) does not establish relative $o(E_j)$ error. Although
the spectral theorem bounds
$\operatorname{dist}(-E_j,\operatorname{spec}\mathscr A)$ by the
left side of (32.1), the resulting scale need not be smaller than
$E_j$ and can include zero. It does not locate a negative
eigenvalue at relative distance $o(E_j)$.

Application 24.6, with its actual antecedent (24.18), remains the
conditional supplier for all original negative eigenvalues and
complex multiplicities, including a fixed indexing shift. That
antecedent requires nonzero original-domain vectors with relative
$o(E_j)$ residual at every sufficiently large geometric level;
Corollary 32.1 does not supply it. The real reducing-sector
construction above is checked in the full complex domain, but
it supplies no additional simplicity or exhaustion assertion.

The number $D_{\rm align}$ in (31.11) aligns only the supplied
leading waves. It has not been identified with an original
spectral-phase constant. For all original negative eigenvalues
$-\varepsilon_j$, ordered with their original complex
multiplicities, the existence of a finite limit

$$
\lim_{j\to\infty}
 \left(\tfrac12\log(1/\varepsilon_j)-\frac{j}{2L_{n,g}}\right)
 \in\mathbb R
\tag{32.4}
$$

throughout the entire isolation interval remains undetermined by
these gluing and residual conclusions. The unresolved quantitative
bridge is relative original-domain matching at all sufficiently
large levels, or another exact original-family all-eigenvalue
quantization argument, with the original natural endpoints,
physical mass, all higher even components and every permitted
kernel or zero-energy resonance retained.

## 追加锚（本行以下为增补区）
