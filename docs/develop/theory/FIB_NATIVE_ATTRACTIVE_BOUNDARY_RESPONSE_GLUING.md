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

## 33. 固定内截断残差的物理尾部矩与扇区余核展开

**定义 33.1（原参数、扇区与加权余核）。** 沿用定义 31.1--31.2 的全部原始条件：每个整数 $n\ge2$，整个隔离区间内的每个固定 $g\in(\lambda_n,g_n^{\rm iso})$，以及原定义 18.1 的解析供应者。单位恒等源、完整时间积分、完整无权边缘、raw Lebesgue 物理质量、covariance-$2$ 时钟、$\epsilon=1$、原场 $U,V,Z$ 与单位均保持不变。$\mathscr A$ 仍是包含极点的完整复 Friedrichs 算子，$D(\mathscr A)$ 仍由 (31.3) 定义；自然角端点不附加迹条件。以下常数、权重与起始指标可以依赖固定 $n,g$，不要求参数一致性，也不排除任何原条件允许的核或零能共振。

记 $G$ 为[完整 Green 边缘续篇](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md)。令 $\mathcal S$ 为 $G$ 第 26 节所用的复轴对称、$z$ 偶对称扇区，即绕物理 $z$ 轴旋转不变且在 $z\mapsto-z$ 下不变的函数或局部分布。下面的 $H_{\pm d}$、$K$ 与 $Z$ 全部在此扇区内定义；它们不是全算子全部角模的核或余核。

具体沿用 $G$ (26.8)--(26.10) 的完成空间。固定其中足够大的 $L_*$，取 $\chi_0$ 在 $\ell\le L_*+1$ 为一、在 $\ell\ge L_*+2$ 为零，并在极点附近恒为一。$H^{(0)}$ 是紧支撑原光滑 $\mathcal S$ 元在下列范数中的完成：

$$
\begin{aligned}
\|f\|_{H^{(0)}}^2
 &=\|\chi_0f\|_{\rm free}^2
   +\int_{L_*}^{\infty}\mathcal E[w_f](\ell)\,d\ell,\\
\mathcal E[w]&=C[w_\ell]+A[w]+e^{-2\ell}\|Dw\|_{L^2(da)}^2,
& D&=2\sin a\,(\partial_\ell-1)+4c\partial_a,\\
H_\sigma&=\{f\in\mathcal S:e^{\sigma\rho}f\in H^{(0)}\},
&\|f\|_{H_\sigma}&=\|e^{\sigma\rho}f\|_{H^{(0)}},
\qquad \rho=(\ell-L_*)_+.
\end{aligned}
\tag{33.1}
$$

$\rho$ 在内区延拓为零。这里 $H_\sigma$ 是 $G$ 的加权空间记号，须与原物理自由闭包 $\mathcal H_1$ 区分。选择 $d>0$，小于 $G$ 第 26、30 节及 wall 所允许的权重，并使 $d<1/2$；这是固定参数后的权重选择，不缩小隔离区间。取连续反对偶，定义

$$
\begin{aligned}
P_d &:H_d\longrightarrow(H_{-d})^*,
& (P_df)(z)&=4q(f,z),\\
K&=\ker P_d,
&Z&=\{z\in H_{-d}:q(f,z)=0\ \text{对每个 }f\in H_d\}.
\end{aligned}
\tag{33.2}
$$

$G$ (26.23)--(26.29) 给出 $\operatorname{ind}_{\mathbb C}P_d=-1$、$K\subset Z$、$\dim_{\mathbb C}Z=\dim_{\mathbb C}K+1$。取同一全局实解 $f_0$ 与非零系数 $b$，则

$$
\begin{aligned}
G_\zeta(t)&=(\zeta e^{ist}+\overline\zeta e^{-ist})\psi,
&s&=2\pi L_{n,g},\qquad C[\psi]=1,\\
w_0(\ell)&=G_b(\ell)+r_0(\ell),
&\int_{b_0}^{\infty}e^{2d\ell}\|r_0(\ell)\|_{L^2(da)}^2\,d\ell&<\infty,\\
Z&=K\oplus\mathbb C f_0.
\end{aligned}
\tag{33.3}
$$

$b_0$ 是足够大的固定对数半径，与 $b$ 不同。加权余项是 $G$ (26.26)、(26.29)、(26.35) 的同一余项；非零站波不属于 $H_d$，故 $f_0\notin K$，维数公式给出直和。不能只用 (31.8) 的定性迹极限代替此加权信息。有限维 $Z$ 上可用范数 $\|v+af_0\|_Z=\|v\|_{H_d}+|a|$。

**定义 33.2（同一外解、物理质量与固定截断）。** 对每个充分小的 $E>0$，令 $T=\frac12\log(1/E)$、$x=\ell-T$。始终取 $G$ (30.14)、(30.19) 的同一外解 $F_E$ 与第 28 节的完整耦合 wall $W$：

$$
\begin{aligned}
w_E(T+x)&=W(x)+r_T(x),
&r_T&=\sigma^{-1}Y_T,\qquad \|Y_T\|_{X_T}\le C e^{-dT},\\
\sigma(x)&=e^{dx}\quad(x\le-2),
&\sigma(x)&=1\quad(x\ge2),\\
\|Y\|_{X_T}^2
 &=\int_{\mathbb R}\{C[Y_x]+A[Y]+t_T\|DY\|_2^2
                                      +e^{2x}\|Y\|_2^2\}\,dx.
\end{aligned}
\tag{33.4}
$$

这里 $t_T$ 与 $X_T$ 是 $G$ (30.1)--(30.2) 的原对象，$D$ 以 $x$ 代替 $\ell$。$W$ 的左端系数为同一 $\beta$，$|\beta|=1$。$W$、$F_E$ 及 $f_0$ 的全部高阶偶角分量均保留。原内积第一变量线性，精确物理配对为

$$
4\langle f,h\rangle_{L^2(d\xi)}
 =\int e^{2\ell}\langle w_f(\ell),w_h(\ell)\rangle_{L^2(da)}\,d\ell.
\tag{33.5}
$$

此式也用于下述绝对收敛的广义质量配对；$C$ 角配对只用于微分能量，不能替代 (33.5) 的无权 $da$ 质量或其 $1/4$ 因子。

固定原 Cartesian 光滑径向截断 $\eta$，满足 $0\le\eta\le1$、$\eta=0$ 于 $R\le r_1$、$\eta=1$ 于 $R\ge r_2$，其中 $R_0<r_1<r_2<\infty$。向内零延拓并定义

$$
\begin{aligned}
U_E&=\eta F_E,\\
C_E&=-2\sum_{X\in\mathcal X}(X\eta)(XF_E)
                  -\sum_{X\in\mathcal X}(X^2\eta)F_E.
\end{aligned}
\tag{33.6}
$$

$C_E$ 是固定紧环带上的实际 $L^2(d\xi)$ 函数。

**定理 33.3（源特定物理尾部矩与完整扇区余核展开）。** 在定义 33.1--33.2 的条件下，对每个充分小的 $E$，有

$$
U_E\in D(\mathscr A)\cap H_d,\qquad
(\mathscr A+E)U_E=C_E,\qquad E\|U_E\|_2^2\le C.
\tag{33.7}
$$

存在固定 $\alpha,a>0$，令 $r_E=e^{T+a}$，则

$$
E\int_{R\ge2r_E}
 e^{2\alpha\sqrt E(R-2r_E)}|F_E|^2\,d\xi\le C.
\tag{33.8}
$$

相应指数加权的三个原场能量也有限。更具体地，存在固定 $\alpha_1,a_1>0$，使下列界对全部充分小 $E$ 一致成立：

$$
\begin{aligned}
\int_{x\ge a_1}e^{2x}e^{2\alpha_1e^x}
 \bigl(\|w_E(T+x)\|_2^2+\|W(x)\|_2^2\bigr)\,dx&\le C,\\
\int_{b_0-T}^{\infty}e^{(4-2d)x}\|w_E(T+x)\|_2^2\,dx&\le C.
\end{aligned}
\tag{33.9}
$$

对每个 $z\in Z$，物理质量配对绝对收敛，且

$$
\langle C_E,z\rangle=E\langle U_E,z\rangle.
\tag{33.10}
$$

对整个 $K$ 的 $H_d$ 单位球一致地，以及对任意固定 $0<d'<d$，有

$$
\begin{aligned}
|\langle C_E,v\rangle|&\le C e^{-dT}\|v\|_{H_d}
                                           &&(v\in K),\\
\langle C_E,f_0\rangle
 &=-s\operatorname{Im}(\overline\beta b e^{isT})+O(e^{-d'T}).
\end{aligned}
\tag{33.11}
$$

第一式包括不属于物理 $L^2$ 的所有允许零能共振。严格采用 (31.11) 的固定 $D_{\rm align}$ 与 $E_j=D_{\rm align}e^{-j/L_{n,g}}$，则对每个充分大的整数 $j$，

$$
\begin{aligned}
|\langle C_{E_j},f_0\rangle|&=O(E_j^{d'/2}),\\
\sup_{v\in K,\ \|v\|_{H_d}\le1}|\langle C_{E_j},v\rangle|
 &=O(E_j^{d/2}),\\
\|\langle C_{E_j},\cdot\rangle|_Z\|_{Z^*}&=O(E_j^{d'/2}).
\end{aligned}
\tag{33.12}
$$

这是对整个扇区余核的对偶配对展开，不是物理 $L^2$ 正交投影，也不包含全算子余核的穷尽断言。

证明。先使用 (33.4) 控制原物理质量。在左半线，$A$ 控制无权角 $L^2$，且 $1-d>0$，所以

$$
\int_{b_0-T}^{-2}e^{2x}\|r_T\|_2^2\,dx
 =\int_{b_0-T}^{-2}e^{2(1-d)x}\|Y_T\|_2^2\,dx
 \le C e^{-2dT}.
$$

右侧 $\sigma^{-1}$ 有界，$X_T$ 又包含 $e^{2x}$ 质量，故合得

$$
\int_{b_0-T}^{\infty}e^{2x}\|r_T\|_2^2\,dx\le C e^{-2dT}.
\tag{33.13}
$$

$G$ (28.4) 给出 $W$ 左端有界，(28.5) 给出右端物理质量可积。由 (33.5) 得 $E\|U_E\|_2^2\le C$；固定内截断的有限过渡环带也满足此界，因为 $G$ (30.14) 在每个固定 $\ell$ 环带给出一致有界的值迹。

接着直接在原 Cartesian 弱方程中作截断指数能量试验。原尾界 $P\le C_PR^{-2}$，原 gauge 在 $R\ge1$ 上满足 $\sum_{X\in\mathcal X}|XR|^2\le C_R$；后者由原场、光滑性及齐次度给出，不对角端点分部积分。选固定 $a$ 足够大，使 $R\ge r_E=e^{T+a}$ 时 $gP\le E/4$。取 $\chi_E$ 在 $R\le r_E$ 为零、$R\ge2r_E$ 为一，且 $\sum|X\chi_E|^2\le CE$。令

$$
\phi_N=\min\{\alpha\sqrt E(R-2r_E)_+,N\},
\qquad \sum_{X\in\mathcal X}|X\phi_N|^2\le E/8,
\tag{33.14}
$$

其中固定 $\alpha>0$ 足够小。$\phi_N$ 在 $\chi_E$ 的过渡支撑上恒为零。以 $\chi_E^2e^{2\phi_N}F_E$ 测试原弱方程，取实部并展开原场乘法规则，得到

$$
\begin{aligned}
&\sum_{X\in\mathcal X}\|X(e^{\phi_N}\chi_EF_E)\|_2^2\\
&\quad+\int\left(E-gP-\sum_{X\in\mathcal X}|X\phi_N|^2\right)
                         e^{2\phi_N}\chi_E^2|F_E|^2\,d\xi\\
&=\int e^{2\phi_N}\sum_{X\in\mathcal X}|X\chi_E|^2|F_E|^2\,d\xi
 \le C.
\end{aligned}
\tag{33.15}
$$

右端由刚证的一致 $E$ 质量界控制。对固定 $N$，权重及其原场导数有界；$G$ 第 30 节给出实际外尾的自由域成员身份，原 form core 的稠密性允许先作紧截断再通过极限使用该测试。局部 Lipschitz 权重由光滑逼近处理，不增加极点或角端点条件。左端势项与梯度损失分别由 $E/4$、$E/8$ 吸收。令 $N\to\infty$，以单调收敛和弱下半连续性得到 (33.8)，乘法规则同时给出相应指数加权原场能量。这是 Agmon 截断权重方法在原方程上的具体应用；方法参见 Agmon，*Lectures on Exponential Decay of Solutions of Second-Order Elliptic Equations*，DOI [10.1515/9781400853076](https://doi.org/10.1515/9781400853076)，这里的原场与质量估计由 (33.13)--(33.15) 给出。

这些界控制任意固定多项式尾权，故 $U_E\in H_d$。另一方面，$U_E\in\mathcal H_1$ 已由第 30 节的同一物理尾部结论给出。(33.6) 的原场乘法规则产生紧环带 $L^2$ 右端；原紧光滑 core 上有 $q(U_E,\phi)=\langle C_E-EU_E,\phi\rangle$，再由原 form 连续性和 core 稠密性延拓至整个 $\mathcal H_1$。(31.3) 因而给出 (33.7) 的原算子域身份，无须假设 $PF_E\in L^2$。这与定理 31.4 使用同一表示定理步骤；该标准中间步骤见 Kato，*Perturbation Theory for Linear Operators*，Chapter VI，Section 2。

对比较 wall $W$，在其实际 $p_*$ 方程上作同样的右侧能量试验，取

$$
\phi_N(x)=\min\{\alpha(e^x-e^{a+1})_+,N\}.
$$

在固定充分大的 $x\ge a$ 上，$e^{2x}$ 无权质量吸收 $kQ_n$ 和梯度损失，且
$C[\phi_N'W]\le\alpha^2e^{2x}\|W\|_2^2$，$A$ 的正项保留。(28.5) 提供初始尾部可积性。令截断趋于无穷，得到 $W$ 的对应指数质量界。将 (33.8) 换到 $x$ 坐标并与此合并，缩小固定指数常数即可得 (33.9) 第一式。

再证尾部矩 (33.9) 第二式。左侧 $W$ 有界，而 $r_T$ 的权重为

$$
e^{(4-2d)x}\|r_T\|_2^2=e^{(4-4d)x}\|Y_T\|_2^2
\qquad(x\le-2).
$$

因 $d<1/2$，此系数在左半线有界；$A[Y_T]$ 控制其角质量。右侧的任意固定幂由 (33.9) 第一式控制。这同时说明所有下述物理配对的尾部收敛性。

对任意 $v\in K$，加权空间定义及 $A\ge\lambda_0\|\cdot\|_2^2$ 给出

$$
\int_{b_0}^{\infty}e^{2d\ell}\|w_v(\ell)\|_2^2\,d\ell
 \le C\|v\|_{H_d}^2.
$$

以 (33.5)、Cauchy--Schwarz 不等式和刚证的尾部矩估计，得到

$$
\begin{aligned}
E|\langle U_E,v\rangle|
 &\le C\|v\|_{H_d}
   \left(E^2\int_{b_0}^{\infty}
      e^{(4-2d)\ell}\|w_E(\ell)\|_2^2\,d\ell\right)^{1/2}
       +O(E)\|v\|_{H_d}\\
 &\le C e^{-dT}\|v\|_{H_d}.
\end{aligned}
\tag{33.16}
$$

最后一步的缩放因子是 $E e^{(2-d)T}=e^{-dT}$；固定有限环带项为 $O(E)\|v\|_{H_d}$，可吸收。此估计使用整个 $K$，不以辅助 $C$ 正交性删掉原物理交叉质量。

由 $U_E\in H_d$ 和 $Z$ 的定义，$q(U_E,z)=0$。将 (33.7) 的弱等式用截断的 $z$ 测试，再移去远端截断。指数原场尾界、$z\in H_{-d}$ 和原加权 form 连续性保证极限合法；质量配对绝对收敛。因此得到 (33.10)，与 (33.16) 合得 (33.11) 第一式。这一配对过程不要求 $z$ 或 $v$ 属于物理 $L^2$。

为计算剩余标量分量，先在比较 wall 上取任意 $\zeta\in\mathbb C$，定义弱通量

$$
\mathcal F_\zeta(x)=C(W,G_\zeta')-C(W',G_\zeta).
$$

$G_\zeta$ 解无质量的齐次柱面方程。$p_*$ 方程和 $h(\psi,u)=-s^2C(\psi,u)$ 的弱本征式给出

$$
\mathcal F_\zeta'(x)
 =-e^{2x}\langle W(x),G_\zeta(x)\rangle_{L^2(da)}.
\tag{33.17}
$$

指数质量界及右端能量给出一个趋向 $+\infty$ 的序列，其上 $\mathcal F_\zeta\to0$；(33.17) 右端绝对可积，所以整个右端通量极限为零。由 $G$ (28.4) 的两个强迹和 $C[\psi]=1$，左端为

$$
\mathcal F_\zeta(-\infty)
 =C(G_\beta,G_\zeta')-C(G_\beta',G_\zeta)
 =-4s\operatorname{Im}(\overline\beta\zeta).
$$

积分 (33.17)，得

$$
\int_{\mathbb R}e^{2x}
       \langle W(x),G_\zeta(x)\rangle_{L^2(da)}\,dx
 =-4s\operatorname{Im}(\overline\beta\zeta).
\tag{33.18}
$$

此处仅以 $\psi$ 的弱本征式处理 $h$ 配对，没有把 $W$ 投影为标量；$e^{2x}$ 质量始终使用无权 $da$，包含所有更高偶角分量的质量贡献。

回到原物理配对，令 $\zeta_T=be^{isT}$。由 (33.3)，
$w_0(T+x)=G_{\zeta_T}(x)+r_0(T+x)$。尾部矩与 $r_0$ 的加权可积性，按 (33.16) 的 Cauchy--Schwarz 估计，给出 $r_0$ 项 $O(e^{-dT})$。对 $r_T$ 项，固定 $0<d'<d$，以 $R_T=(d-d')T$ 分割：在 $x\le R_T$ 上，(33.13) 和 $G_{\zeta_T}$ 的一致有界性给出

$$
\left|\int_{b_0-T}^{R_T}e^{2x}
             \langle r_T,G_{\zeta_T}\rangle\,dx\right|
 \le C e^{R_T}e^{-dT}=C e^{-d'T}.
$$

在 $x\ge R_T$ 上，用 (33.9) 第一式及 Cauchy--Schwarz，误差至多

$$
C(1+e^{R_T})^{1/2}e^{-\alpha_1e^{R_T}}
 =O(e^{-d'T}).
$$

省略的左端 $x<b_0-T$ 及固定 $\eta$ 过渡区均为 $O(e^{-2T})$。因此，包含精确物理因子，

$$
E\langle U_E,f_0\rangle
 =\frac14\int_{\mathbb R}e^{2x}
            \langle W(x),G_{\zeta_T}(x)\rangle_{L^2(da)}\,dx
       +O(e^{-d'T}).
\tag{33.19}
$$

这些估计逐项控制余项及极限；不需关于 $E$ 的连续性，也没有选能量子列。将 (33.18) 代入 (33.19)，并用 (33.10)，恰得 (33.11) 的负号和系数 $-s$。

最后，(31.11) 对每个充分大 $j$ 都精确给出

$$
be^{isT_j}=c_j\beta,\qquad c_j=(-1)^j|b|\in\mathbb R.
$$

所以正弦主项逐层为零，得到 (33.12) 前两式；由 $Z=K\oplus\mathbb C f_0$ 和所定义的有限维范数得到第三式。整个计算只确定同一实际残差在扇区余核上的限制。$\square$

**问题 33.4（原补空间校正的实际相容方程）。** 对欲求的原校正

$$
(\mathscr A+E)v_E=-C_E+\rho_E,
\tag{33.20}
$$

若 $v_E$ 具有上述配对所需的原域与尾部，则其 $Z$ 相容式为

$$
E\langle v_E,z\rangle
 =-\langle C_E,z\rangle+\langle\rho_E,z\rangle
\qquad(z\in Z).
\tag{33.21}
$$

定理 33.3 计算的正是这个实际右端中的 $C_E$ 项。它没有给出 (33.20) 的补空间校正、原 $\mathscr A+E$ 的统一补空间逆，或允许核与共振的能量依赖物理质量矩阵控制。原物理质量在 $H_d\to(H_{-d})^*$ 尺度上不能被当作有界小扰动；有限维右端趋零不能代替原图范数估计。$G$ (30.10) 的辅助 wall 右逆与第 26 节的零能 Fredholm 广义逆，均不能直接充当这里尚缺的统一逆。

特别地，(33.12) 不给出 $\|C_{E_j}\|_2=o(E_j\|U_{E_j}\|_2)$，也不提供 (31.16) 所需的 $e^{T_j-M_j}\Delta_j$ 控制。(32.3) 仍只是既有 gluing 构造的充分条件，不是原目标的必要条件。仍须在每个 $n\ge2$、整个隔离区间内的每个固定 $g$ 上，以固定 $D>0$ 和每个充分大的整数 $j$，构造非零原 $D(\mathscr A)$ 向量，使

$$
E_j=De^{-j/L_{n,g}},\qquad
\frac{\|(\mathscr A+E_j)u_j\|_2}{E_j\|u_j\|_2}\longrightarrow0,
\tag{33.22}
$$

或给出满足同一原全谱目标的其他量化论证。$D_{\rm align}$ 在本节只保证 (33.12) 的全层配对消去，未被识别为原谱相位常数。定理 31.4 与条件应用 24.6 保持各自原用途；本节不增加负谱穷尽、简单性或全算子余核结论，亦不以补空间路线的未解问题反驳原谱目标。

## 追加锚（本行以下为增补区）

## 34. 原自然角慢尾、物理零模与截断质量矩阵

**定义 34.1（原算子、自然角谱与同一加权核）。** 沿用定义 31.1--31.2、33.1--33.2 的全部条件和对象。具体地，原定义 18.1 取自修订 [d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md)，其定义 1.1 所固定的解析供应者 C、V 取自修订 5cec4fa83ae7bbb4e787c42606525db4cd11ed48；V 的自然角域、紧嵌入与原场归一化见该修订的[第 10 节](https://github.com/the-omega-institute/trureturing/blob/5cec4fa83ae7bbb4e787c42606525db4cd11ed48/docs/develop/theory/FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)。$G$ 第 24--26、28、30 节以及本卷第 31、33 节的解析结论按修订 [47176ca9b3af67894cfd4856beeb929c82fa63fa](https://github.com/the-omega-institute/trureturing/blob/47176ca9b3af67894cfd4856beeb929c82fa63fa/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md) 中的原陈述使用。

固定任意整数 $n\ge2$ 和整个原隔离区间中的任意固定 $g\in(\lambda_n,g_n^{\rm iso})$。区间非空和 $L=L_{n,g}>0$ 是 $G$ 引理 24.2、命题 24.3 的结论。原恒等单位源、完整时间积分、完整无权边缘、raw Lebesgue 测度 $d\xi=dx\,dy\,dz$、covariance-$2$ 热时钟、$\epsilon=1$、原场 $U,V,Z$ 和单位均与 (31.1)--(31.2) 相同。$\mathscr A=A_{n,1,g}$ 是包含极点的完整复 Friedrichs 算子，其自由闭包为原 $\mathcal H_1$，算子域由 (31.3) 给出。本节只在实际复轴对称、$z$ 偶对称约化扇区 $\mathcal S$ 中分类零能解；原全算子及其全部整数角模不作改变，不附加角端点迹条件，不排除原条件允许的任何核或零能共振。

记 $J=(-\pi/2,\pi/2)$、$c(a)=\cos a$、$k=g/(2\pi)$，沿用 (31.4) 的自然角域

$$
\mathcal H_c=\{b\in L^2(J,da):b\in AC_{\rm loc}(J),\ \sqrt c\,b'\in L^2(J,da)\},
$$

以及原角形式

$$
\begin{aligned}
A[b]&=\int_J(4c|b'|^2+c|b|^2)\,da,
&C[b]&=\int_Jc|b|^2\,da,\\
h&=A-kQ_n,
&Q_n[b]&=\int_Jq_n|b|^2\,da,\\
q_n(a)&=\frac1{I_n}\int_0^1
       \frac{u^{n-2}}{\sqrt{1-u^2\sin^2a}}\,du,
&I_n&=\int_0^{\pi/2}\sin^{n-2}t\,dt.
\end{aligned}
$$

内积及形式的极化均取第一变量线性。令 $\mathsf K_g$ 为偶子空间上 $h$ 在 $L^2(J,c\,da)$ 中的自然自伴表示。$G$ 命题 24.3 给出其紧预解式、唯一单负本征值 $-s^2$、无零本征值以及与零有正距离的正谱，其中 $s=2\pi L$。负本征向量记为 $\psi$，取 $C[\psi]=1$；每个正本征值写为 $\nu^2$，$\nu>0$，相应有限维复偶自然本征空间记为 $E_\nu$。不同本征空间在 $C$ 中正交，在物理角配对 $L^2(da)$ 中不必正交。

始终使用 (31.4)、(31.6) 的原规范坐标 $R=((x^2+y^2)^2+16z^2)^{1/4}$、$\ell=\log R$ 和 $w_f$。精确物理质量配对为

$$
4\langle f,u\rangle_{L^2(d\xi)}
 =\int e^{2\ell}\langle w_f(\ell),w_u(\ell)\rangle_{L^2(da)}\,d\ell.
\tag{34.1}
$$

在充分远的外部，原零能弱方程由 $G$ (25.7)--(25.10) 写成

$$
\begin{aligned}
p(w,z)&=\int\bigl\{C(w',z')+h(w,z)
       +t\langle Dw,Dz\rangle_{L^2(da)}
       -g\langle B_nw,z\rangle_{L^2(da)}\bigr\}\,d\ell=0,\\
t&=e^{-2\ell},\qquad
D=\upsilon(a)(\partial_\ell-1)+4c\partial_a,
\qquad \upsilon(a)=2\sin a,\\
\|B_n(\ell,\cdot)\|_\infty&\le C e^{-2\ell}.
\end{aligned}
\tag{34.2}
$$

这里 $B_n$ 是 (31.7) 中完整原 Green 边缘的误差；$D$ 项与 $B_n$ 项均用无权 $da$ 配对，中央场耦合全部保留。

辅助加权空间 $H_\sigma$ 仍严格取 (33.1) 与 $G$ (26.8)--(26.10) 的完成空间：内区为原自由范数，外部图能量为
$\int\{C[w']+A[w]+t\|Dw\|_2^2\}\,d\ell$，权重为 $e^{\sigma\rho}$，$\rho=(\ell-L_*)_+$。取原构造允许的固定小权重 $d>0$，并取 $d<1/2$ 且小于最小正角指数。后一选择与原高角强制估计及小权重条件相容；这些辅助选择不限制 $n,g$。定义

$$
K=\ker\bigl(P_d:H_d\longrightarrow(H_{-d})^*\bigr),
\qquad (P_df)(z)=4q(f,z),
\qquad N=\ker\mathscr A\cap\mathcal S.
$$

这是 (33.2) 的同一 $K$。由 $G$ (26.23)--(26.24)，$K$ 有限维；由 $G$ (26.8)--(26.10) 及第 26 节证明第 (9) 步的平均论证，其中元素均为包含原极点的全局局部自由形式解，并对全部原复紧光滑测试成立。记 $H_1^{\rm aux}$ 为辅助指数等于一的空间，始终与原自由闭包 $\mathcal H_1$ 区分。

**定理 34.2（完整慢尾、原域零模与球质量）。** 在定义 34.1 的条件下，令

$$
\Sigma=\{\nu\in(0,1]:\nu^2\in\sigma(\mathsf K_g)\},
$$

并令 $\nu_+$ 为严格大于一的最小正谱平方根。$\Sigma$ 有限且允许为空。固定一次

$$
1<\delta<\min(1+d,\nu_+).
\tag{34.3}
$$

则存在唯一复线性映射 $\mathsf A_\nu:K\to E_\nu$，使每个 $v\in K$ 在远端满足

$$
w_v(\ell)=\sum_{\nu\in\Sigma}e^{-\nu\ell}\mathsf A_\nu(v)+r_v(\ell),
\tag{34.4}
$$

且余项具有完整中央图控制

$$
\int e^{2\delta\ell}
 \bigl\{C[r_v']+A[r_v]+t\|Dr_v\|_{L^2(da)}^2\bigr\}\,d\ell<\infty.
\tag{34.5}
$$

各系数的范数和 (34.5) 的平方根均由 $C\|v\|_{H_d}$ 控制。显式抽出有限个慢分量后，其余全部高阶偶角分量仍在 $r_v$ 的完整图范数中。

更具体地，对任意 $C$ 单位本征向量 $\phi\in E_\nu$，置

$$
\begin{aligned}
a(\ell)&=C(w_v(\ell),\phi),
&p_\phi&=\upsilon\phi,
&r_\phi&=4c\phi'-\upsilon\phi,\\
f_1(\ell)&=-t\langle Dw_v,p_\phi\rangle_{L^2(da)},\\
f_0(\ell)&=-t\langle Dw_v,r_\phi\rangle_{L^2(da)}
                  +g\langle B_nw_v,\phi\rangle_{L^2(da)},
&y&=a'-f_1.
\end{aligned}
$$

用 $a,y$ 的连续 $H^1_{\rm loc}$ 代表，在任意充分大的 Lebesgue 点 $b$ 有

$$
C(\mathsf A_\nu(v),\phi)
 =\frac12e^{\nu b}\left(a(b)-\frac{y(b)}\nu\right)
  +\frac12\int_b^\infty e^{\nu u}
                  \left(f_1(u)+\frac{f_0(u)}\nu\right)\,du.
\tag{34.6}
$$

积分绝对收敛，右端与 $b$ 无关。在 $E_\nu$ 中取 $C$ 正交基即确定整个 $\mathsf A_\nu(v)$；公式包含原完整中央场和源项的 强迫项。

此外，原域零模恰满足

$$
N=K\cap L^2(d\xi)=K\cap H_1^{\rm aux}
 =\ker\left(\mathsf A:K\longrightarrow\bigoplus_{\nu\in\Sigma}E_\nu\right),
\qquad \mathsf A=(\mathsf A_\nu)_{\nu\in\Sigma}.
\tag{34.7}
$$

因而 $\dim_{\mathbb C}N\le\dim_{\mathbb C}K$，$K/N$ 注入所示有限自然角空间。这里不要求系数映射满射，不要求 $K$、$N$、$\Sigma$ 或任何系数非零。

若 $v\in K\setminus N$，令 $\nu=\nu(v)$ 是 $\mathsf A_\nu(v)\ne0$ 的最小指数，则尖锐物理球质量满足

$$
\begin{aligned}
\int_{R\le e^T}|v|^2\,d\xi
 &\sim\frac{\|\mathsf A_\nu(v)\|_{L^2(da)}^2}{4(2-2\nu)}
                          e^{(2-2\nu)T}&& (\nu<1),\\
\int_{R\le e^T}|v|^2\,d\xi
 &\sim\frac14\|\mathsf A_1(v)\|_{L^2(da)}^2T&& (\nu=1).
\end{aligned}
\tag{34.8}
$$

证明。先证明完整图能量中的展开。有限自然谱投影在该图空间上有界。对固定 $\phi\in\mathcal H_c$，由 $|\upsilon|\le2$、$c^2\le c$，有 $p_\phi,r_\phi\in L^2(da)$，且

$$
D(b\phi)=p_\phi b'+r_\phi b.
$$

投影系数的一阶 Sobolev 范数由 $C[w']$ 与 $A[w]$ 控制；上式同时控制其中央图项。因此减去有限投影保留整个高角图项。

以 $b(\ell)\phi(a)$ 测试 (34.2)，使用自然弱本征式，不对角端点另作分部积分，得到

$$
-a''+\nu^2a=f_0-f_1',
\qquad a'=y+f_1,\qquad y'=\nu^2a-f_0.
\tag{34.9}
$$

由 $v\in H_d$ 得

$$
\int e^{2(d+1)\ell}(|f_0|^2+|f_1|^2)\,d\ell
 \le C\|v\|_{H_d}^2.
\tag{34.10}
$$

确实，中央项恰有

$$
\bigl(e^{(d+1)\ell}t\|Dw\|_2\bigr)^2
 =e^{2d\ell}t\|Dw\|_2^2;
$$

源误差 $B_n$ 还带有 $e^{-2\ell}$，其估计多出一阶衰减。这只使用实际中央图范数中的一个权重单位增益。

令

$$
c_-(\ell)=\frac12e^{\nu\ell}(a-y/\nu),
\qquad c_+(\ell)=\frac12e^{-\nu\ell}(a+y/\nu).
$$

由 (34.9)，

$$
c_-'=\frac12e^{\nu\ell}(f_1+f_0/\nu),
\qquad c_+'=\frac12e^{-\nu\ell}(f_1-f_0/\nu).
$$

因 $\nu\le1<d+1$，第一个导数在右半线上可积，故 $c_-$ 有极限，且积分导数即得 (34.6)。$a\in H^1_d$ 排除 $e^{\nu\ell}$ 增长解，故 $c_+(\infty)=0$。于是

$$
\begin{aligned}
c_-(\ell)-c_-(\infty)
 &=-\frac12\int_\ell^\infty e^{\nu u}(f_1(u)+f_0(u)/\nu)\,du,\\
c_+(\ell)
 &=-\frac12\int_\ell^\infty e^{-\nu u}(f_1(u)-f_0(u)/\nu)\,du.
\end{aligned}
$$

Cauchy--Schwarz 不等式或半线指数卷积的 Young 不等式表明，$a-e^{-\nu\ell}c_-(\infty)$ 及其一阶导数具有 (34.3) 的 $\delta$ 加权 $L^2$ 控制；此时 $\delta>\nu$，尾积分的卷积核以 $\delta-\nu>0$ 衰减。端点值取 $y$ 的一阶方程所给的 $H^1_{\rm loc}$ 代表，公式不依赖所取点。

对负角向量 $\psi$ 的系数，(34.9) 中 $\nu^2$ 改为 $-s^2$。相应常矩阵的指数有界，而 $a,y$ 的正权 $d$ 可积性排除两个振荡齐次解，故

$$
\begin{pmatrix}a\\y\end{pmatrix}(\ell)
 =-\int_\ell^\infty e^{M(\ell-u)}
             \begin{pmatrix}f_1(u)\\-f_0(u)\end{pmatrix}\,du,
\qquad M=\begin{pmatrix}0&1\\-s^2&0\end{pmatrix}.
$$

这给出任意 $\delta<d+1$ 的加权 $H^1$ 控制，负角通道不留下振荡慢尾系数。

令 $V_>$ 为与 $\psi$ 和所有 $E_\nu$（$\nu\le1$）均 $C$ 正交的高角空间。其上

$$
h\ge\nu_+^2C,\qquad h\ge\kappa_>A,\qquad \kappa_>>0.
$$

第二式由 $G$ (24.9) 的 $h+\beta C\ge\alpha A$ 与第一式组合得到。对 $\tau=d$ 或 $\delta$，

$$
h-\tau^2C\ge(1-\tau^2/\nu_+^2)h\ge\kappa_\tau A.
$$

在充分大的固定外部半线 $\ell\ge b$，将限制于 $V_>$ 的完整 $p$ 作相反 $\tau$ 权重共轭，其实对角为

$$
\int_b^\infty\bigl\{C[z']+h[z]-\tau^2C[z]
 +t\|Dz\|_2^2-\tau^2t\|\upsilon z\|_2^2
 -g\langle B_nz,z\rangle_{L^2(da)}\bigr\}\,d\ell.
$$

末两项的绝对值至多为 $Ce^{-2b}\int_b^\infty A[z],d\ell$，增大固定 $b$ 即可吸收。Riesz 表示及伴随的强制形式论证给出这个高块在半线零左迹图完成空间上的唯一有界逆，分别适用于 $\tau=d,\delta$。这里的零左迹仅用于径向截断后的未知量。

令 $w_{\rm low}$ 为已得到的有限低投影，$v_>=w_v-w_{\rm low}$。取远端径向 $\eta$，在半线左端为零、远处为一，考察 $\eta v_>$ 的高块方程。右端是固定过渡带的实际交换子以及 $w_{\rm low}$ 的中央场、源项交叉 强迫项。每个正低标量为 $e^{-\nu\ell}$ 常系数加 $H^1_\delta$ 余项，且所有正 $\nu>d$，所以

$$
\int e^{2\delta\ell}t\|Dw_{\rm low}\|_2^2\,d\ell<\infty,
\qquad
\int e^{2\delta\ell}\|B_nw_{\rm low}\|_2^2\,d\ell<\infty.
$$

第一式对显式慢项使用 $\delta<1+d<1+\nu$，对加权余项使用 $t$ 有界；$\psi$ 系数使用刚证的加权 $\delta$ 控制。故右端是高块 $\delta$ 图对偶中的有界泛函。固定过渡带项由原局部图能量控制。高块 $\delta$ 逆产生的解也属于 $d$ 空间，而原 $\eta v_>$ 是同一个 $d$ 方程的解；$d$ 零左迹空间中的唯一性使两者相等。这证明高块的 (34.5)，与低标量余项相加即得 (34.4)--(34.5)。全部构造都是有界线性操作；不同指数的独立性及 $\delta>1\ge\nu$ 给出唯一性。这里使用的是完整高角半线强制形式逆，不是原整体低能补空间逆。

再证明物理质量及原域对应。由 (34.1)、(34.5)、$\delta>1$ 以及 $A\ge\lambda_0\|\cdot\|_{L^2(da)}^2$，余项具有有限原物理 $L^2$ 质量。若最小非零指数为 $\nu<1$，其球质量首项按 (34.1) 积分恰为 (34.8) 第一式；其余有限显式项指数更快，均为低阶。余项与首项的物理 Cauchy--Schwarz 交叉界为 $O(e^{(1-\nu)T})$，也为低阶。若只有 $\nu=1$，首项为 $T\|\mathsf A_1(v)\|_2^2/4$，余项交叉为 $O(\sqrt T)$。故 (34.8) 成立，并有 $K\cap L^2=\ker\mathsf A$。整个计算用无权 $da$，未用 $C$ 正交性删去物理交叉项。

对 $v\in K\cap L^2$，$H_d$ 控制外部全部原场 $U,V,Z$ 能量，定义中的内区范数控制原紧内区。原正极坐标恒等式与径向远端截断将其转回原自由闭包：截断损失由 $|\nabla_{\mathcal X}\chi_R|\le C/R$ 及物理 $L^2$ 尾部控制，趋于零；紧支撑局部自由形式元由原光滑核稠密性逼近。因此 $v\in\mathcal H_1$。全局零能弱方程先对所有复紧光滑测试成立，再由原形式连续性及核稠密性延拓至全部 $\mathcal H_1$。(31.3) 给出 $v\in D(\mathscr A)$、$\mathscr Av=0$，不要求 $Pv\in L^2$。

反向取 $z\in N$。记原水平能量加中央能量为 $T_1[z]=\sum_{X\in\{U,V,Z\}}\|Xz\|_2^2$，势能为 $W[z]=\int P|z|^2\,d\xi$。原无穷小形式界与 $q[z]=0$ 给出 $T_1[z]+W[z]\le C\|z\|_2^2$。取平滑正函数 $a_0$，在内区有界、远端等于 $R$；令 $a_m=\min(a_0,m)$，折点用光滑逼近处理。原场直接给出

$$
(UR)^2+(VR)^2=c,
\qquad (ZR)^2=\frac{4\sin^2a}{R^2},
\qquad \Gamma(R)=\sum_{X\in\{U,V,Z\}}|XR|^2
                  =c+\frac{4\sin^2a}{R^2}.
\tag{34.11}
$$

故 $\Gamma(a_m)$ 在全空间一致有界，$a_m^2z$ 是合法原形式测试。由原乘法规则及 $q(z,a_m^2z)=0$，精确 IMS 等式为

$$
T_1[a_mz]
 =g\int P a_m^2|z|^2\,d\xi
    +\int\Gamma(a_m)|z|^2\,d\xi
 \le C\|z\|_2^2.
\tag{34.12}
$$

外区势项使用原 $P\le C/R^2$，内区使用刚得的 $W[z]$ 界。局部弱极限及下半连续性给出 $X(a_0z)\in L^2$，范数至多为 $C\|z\|_2$。在外部 $w_{a_0z}=e^\ell w_z$，其无权柱面 $L^2$ 范数正由 (34.1) 的物理质量控制。对 $a_0z$ 再作径向远端截断，(34.11) 使梯度损失由 $z$ 的物理 $L^2$ 尾部控制并趋零；原正极坐标恒等式遂给出 $e^\ell w_z$ 的完整外部图能量有限，内区仍为原自由域。因此

$$
z\in H_1^{\rm aux},\qquad
\|z\|_{H_1^{\rm aux}}\le C\|z\|_{L^2(d\xi)}.
\tag{34.13}
$$

$H_1^{\rm aux}\subset H_d$，原弱方程与相反权重空间的稠密性给出 $P_dz=0$，故 $z\in K$。另一方面，$A\ge\lambda_0\|\cdot\|_{L^2(da)}^2$ 给出 $H_1^{\rm aux}\subset L^2(d\xi)$。结合前述包含即得 (34.7)。原自然角光滑核、包含极点的原自由形式核以及全测试恢复贯穿上述域对应，没有增添端点值或 $Pz\in L^2$ 条件。

本定理中的常系数变参数、半线卷积与强制形式论证是经典方法；Hilbert 空间的 Riesz 及伴随论证参见 Folland，*Real Analysis*，Chapter 5，闭形式表示与原算子域刻画参见 Kato，*Perturbation Theory for Linear Operators*，Chapter VI，Section 2。它们在这里用于原完整 强迫项 的 (34.6)、图增益 (34.10)、高角权重吸收以及原域与物理质量的具体对应。$\square$

**定理 34.3（完整加权核的原域截断与物理 Gram）。** 在定义 34.1 的条件下，固定实光滑函数 $\chi:[0,\infty)\to[0,1]$，在 $[0,1]$ 上为一、在 $[2,\infty)$ 上为零，定义

$$
V_T(v)=\chi(e^{-T}R)v,\qquad
M_T(v,u)=\langle V_T(v),V_T(u)\rangle_{L^2(d\xi)}.
\tag{34.14}
$$

每个 $v\in K$ 均有 $V_T(v)\in D(\mathscr A)$，并有原 $L^2$ 中的精确等式

$$
\mathscr AV_T(v)
 =-2\sum_{X\in\mathcal X}(X\chi_T)(Xv)
       -\sum_{X\in\mathcal X}(X^2\chi_T)v,
\qquad \chi_T=\chi(e^{-T}R).
\tag{34.15}
$$

在复商空间 $K/N$ 中取依最小非零指数适配的基，代表元记为 $r_i$，即
$\nu_i$ 是 $r_i$ 的最小非零指数，$a_i=\mathsf A_{\nu_i}(r_i)\ne0$，同一 $\nu_i$ 下的首系数线性独立。再取 $N$ 的任意基 $z_\alpha$。令

$$
S_i(T)=
\begin{cases}
e^{(1-\nu_i)T},&\nu_i<1,\\
\sqrt T,&\nu_i=1,
\end{cases}
\qquad S_\alpha(T)=1.
$$

用相应因子同时除 $M_T$ 在基 $(z_\alpha,r_i)$ 中的行、列，所得矩阵收敛到真零、幂共振、临界对数三个对角块：

$$
\begin{aligned}
G_{N,\alpha\beta}
 &=\langle z_\alpha,z_\beta\rangle_{L^2(d\xi)},\\
G_{{\rm pow},ij}
 &=\frac14\langle a_i,a_j\rangle_{L^2(da)}
       \int_0^2\chi(r)^2r^{1-\nu_i-\nu_j}\,dr
                                  &&(\nu_i,\nu_j<1),\\
G_{{\rm log},ij}
 &=\frac14\langle a_i,a_j\rangle_{L^2(da)}
                                  &&(\nu_i=\nu_j=1).
\end{aligned}
\tag{34.16}
$$

不同块之间的极限交叉项为零，每个非空极限块正定。$K/N=0$ 时共振块为空，$N=0$ 时真零块为空；所有块均允许为空。幂块保留不同自然本征空间之间的全部物理 $da$ 交叉项。

证明。$\chi_T$ 在极点附近恒为一，是原 笛卡尔 光滑紧支撑乘子。$v$ 的局部自由形式身份给出 $V_T(v)\in\mathcal H_1$。对原全测试弱方程使用乘法规则，得到 (34.15)；右端只含紧环带上的一阶原场导数和光滑乘子导数，是实际 $L^2(d\xi)$ 函数。原形式核稠密性与 (31.3) 给出算子域身份。极点闭包保持原样，无须 $Pv\in L^2$。

由 (34.7)，有限系数映射的共同核恰为 $N$。按 $\Sigma$ 的递增次序逐层取系数核过滤，并在连续商层选基，即得所述适配基；同一层的首系数线性独立。这只用有限维消元，不要求任一系数映射满射。

把 (34.4) 代入 (34.14)，在远端令 $r=e^{\ell-T}$。幂块的首项经 (34.1) 换元，恰为 (34.16) 所列积分与 $1/4$ 因子；更快系数在规定的归一化下趋零。临界块由 $\int^T d\ell=T+O(1)$ 得到。幂与临界项的交叉为 $O(e^{(1-\nu_i)T})$，除以 $e^{(1-\nu_i)T}\sqrt T$ 后趋零。余项有有限物理 $L^2$ 质量，归一化后趋零，其交叉项亦由 Cauchy--Schwarz 不等式趋零。

归一化共振向量在每个固定紧集趋零，在全局物理 $L^2$ 中有界，故弱趋零；这使它与每个真零模的交叉趋零。真零块本身由支配收敛得到 $G_N$。因此所有块间交叉极限均为零。

$G_{\rm pow}$ 是函数族

$$
r\longmapsto\chi(r)r^{-\nu_i}a_i
\quad\text{在 }L^2\bigl((0,2),r\,dr;L^2(J,da)\bigr)\text{ 中的 Gram 矩阵除以 }4.
$$

不同幂的独立性和同一指数首系数的独立性使该族线性独立，故每个非空幂块正定。临界块由同层首系数独立性正定，真零块由物理零模基的独立性正定。这里没有借用 $C$ 正交性删除物理交叉项。有限维过滤、Gram 与正定性的步骤是经典线性代数方法，所用原域向量及质量尺度由定理 34.2 和 (34.15) 给出。

在自然尺度 $E=e^{-2T}$ 下，幂共振的因子为 $S_i(E)=E^{-(1-\nu_i)/2}$，临界因子为 $\sqrt{\log(1/E)/2}$。所得是零能解实际截断的质量 Gram 及其归一化渐近可逆块；它不是未知低能校正的能量依赖有效矩阵或其逆。$\square$

**定理 34.4（同一外解的真零模投影与精确主质量）。** 使用定义 33.2 的同一 $U_E=\eta F_E$、紧环带残差 $C_E$ 和完整耦合势墙 $W$。令 $\Pi_N$ 为 $N$ 的物理 $L^2(d\xi)$ 正交投影，置

$$
U_E^\perp=U_E-\Pi_NU_E,\qquad
C_E^\perp=(I-\Pi_N)C_E.
$$

则对每个充分小的 $E>0$，

$$
\begin{aligned}
U_E^\perp&\in D(\mathscr A)\cap N^\perp,\\
(\mathscr A+E)U_E^\perp&=C_E^\perp,\\
\Pi_N C_E&=E\Pi_NU_E,\\
\|\Pi_NU_E\|_2&=o(E^{-1/2}).
\end{aligned}
\tag{34.17}
$$

并且有严格正的精确主质量

$$
\begin{aligned}
m_W&=\frac14\int_{\mathbb R}e^{2x}\|W(x)\|_{L^2(da)}^2\,dx
                              \in(0,\infty),\\
E\|U_E^\perp\|_2^2&\longrightarrow m_W,
\qquad E\|U_E\|_2^2\longrightarrow m_W.
\end{aligned}
\tag{34.18}
$$

特别地，$U_E^\perp$ 对每个充分小的 $E$ 都非零。原全物理零核的正交投影作用在这个特定 $U_E$ 上，也等于 $\Pi_NU_E$。

证明。(33.13) 给出同一余项的物理加权质量

$$
\int_{b_0-T}^{\infty}e^{2x}\|r_T(x)\|_2^2\,dx=O(e^{-2dT}),
\qquad T=\tfrac12\log(1/E).
$$

$G$ (28.4)--(28.5) 给出 $W$ 左端有界、右端物理质量可积。固定内截断 $\eta$ 所遗漏的 $W$ 左尾质量趋零，故 (34.1) 给出 $E\|U_E\|_2^2\to m_W$。$W$ 的非零左端站波系数保证 $m_W>0$。

由 $G$ (30.14) 的固定 $\ell$ 环带值迹界及 $U_E$ 的内部零延拓，$U_E$ 在每个固定紧集上的物理 $L^2$ 范数一致有界。因此 $\sqrt E U_E$ 局部强趋零、全局有界，在原 $L^2$ 中弱趋零。由 (34.7)，$N$ 有限维，于是 $\sqrt E\Pi_NU_E\to0$。

$N$ 中每个向量均在真实 $D(\mathscr A)$ 中且被 $\mathscr A$ 消去；有限维投影因而保持原算子域。由 (33.7) 及原自伴性，对任意 $z\in N$ 有

$$
\langle C_E,z\rangle=E\langle U_E,z\rangle.
$$

减去投影即得 (34.17)，Pythagoras 等式与该小量界给出 (34.18)。$\mathcal S$ 是原算子的实际约化扇区，而 $U_E\in\mathcal S$，故扇区外的物理零模与它正交；其全物理零核投影正是 $\Pi_NU_E$。这不需要把全算子零核或余核由 $K$ 穷尽。上述正交投影、弱收敛的有限维投影和 Pythagoras 步骤是经典方法，实际原域零模的识别和该特定外解的主质量由 (34.7)、(34.13)、(33.13) 提供。$\square$

定理 34.2--34.4 只建立原扇区零能加权核、物理零模、截断质量和同一外解投影之间的关系。$\nu^2$ 及 $E_\nu$ 必须来自原 $q_n$ 与原自然端点，不以比较角谱替代；$\nu=1$ 的临界情形全部保留。Guillarmou--Hassell，*Resolvent at low energy and Riesz transform for Schrödinger operators on asymptotically conic manifolds. II*，Ann. Inst. Fourier 59(4)，1553--1610，DOI [10.5802/aif.2471](https://doi.org/10.5802/aif.2471)，第 1 节讨论的零模、慢尾与临界对数仅属相关方法：其光滑散射度量 与 $V=O(x^l)$、$l\ge3$ 的条件尚未与这里的自然退化角端点、各向异性原场、吸引 $R^{-2}$ 主势及原域建立对应，故不作为上述定理的预解式供应者。

对 (33.20)--(33.22) 的原问题，仍需构造实际低能补空间校正

$$
(\mathscr A+E)v_E=-C_E+\rho_E,
$$

或给出满足同一原目标的其他论证，并控制全部允许幂与对数共振的能量依赖有效矩阵、其逆及误差放大，以及最终原域重构的非零物理质量和相对残差。零能展开 (34.4) 与截断 Gram (34.16) 不提供这个低能方程的双侧参数逆，不能把 (33.12) 的对偶小量乘以未建立的有界逆。真零模投影不消除 $K/N$ 的非物理 $L^2$ 共振，也不证明 $C_E^\perp$ 的原相对残差趋零。

原目标仍要求对每个 $n\ge2$、整个隔离区间中的每个固定 $g$，以一个固定 $D>0$，对每个充分大的整数 $j$ 在 $E_j=De^{-j/L_{n,g}}$ 上得到非零原域重构，满足

$$
\frac{\|\rho_{E_j}\|_{L^2(d\xi)}}
 {E_j\|U_{E_j}+v_{E_j}\|_{L^2(d\xi)}}\longrightarrow0.
$$

这些要求不附加区间收缩、泛型性、共振排除、能量子列、标量约化或更强尾部条件。条件应用 24.6 保持原有作用，其他满足同一原全谱目标的路线仍然允许；上述结果既未证明也未反驳原目标 C，不增加全算子核、余核或负谱穷尽断言。

## 追加锚（本行以下为增补区）
## 35. 实际慢共振输入、有限相容修正与修正后的物理质量

**定义 35.1（原对象、物理配对与供应关系）。** 固定任意整数 $n\ge2$，以及整个原自然隔离区间中的任意固定 $g\in(\lambda_n,g_n^{\rm iso})$；不要求 $n,g$ 一致性。解析条件恰为原定义 18.1（修订 [d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md)），其定义 1.1 的供应者 C、V 固定于 5cec4fa83ae7bbb4e787c42606525db4cd11ed48。沿用定义 31.1--31.2、33.1--33.2、34.1 及其原条件下的结论；本节所用本卷第 31、33、34 节及 $G$ 第 24、26、28、30 节的文本固定于 [c4e346266d26ad884d034fd81e94f269df61a965](https://github.com/the-omega-institute/trureturing/blob/c4e346266d26ad884d034fd81e94f269df61a965/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GLUING.md)。

具体地，原父算子与完整源仍为

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
$$

$\delta_0$ 是恒等单位源，水平热时钟 covariance 为 $2$，中央 covariance 为 $2\epsilon^2$；时间积分和遗漏坐标边缘完整且无权。固定 $\epsilon=1$，保留原场与单位，置 $P=M_{n,1}$、$d\xi=dx\,dy\,dz$。在保留的三维空间中，$U=\partial_x-(y/2)\partial_z$、$V=\partial_y+(x/2)\partial_z$。原自由闭包和形式为

$$
\begin{aligned}
\mathcal H_1
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^{\,\|\cdot\|_{\rm free}},
&\|u\|_{\rm free}^2&=\|u\|_2^2+
             \sum_{X\in\{U,V,Z\}}\|Xu\|_2^2,\\
q(u,v)&=\sum_{X\in\{U,V,Z\}}\langle Xu,Xv\rangle
          -g\int P u\overline v\,d\xi,
&D(q)&=\mathcal H_1.
\end{aligned}
$$

所有内积第一变量线性。$\mathscr A=A_{n,1,g}$ 是此下半有界形式的完整复 Friedrichs 算子，包含原极点；其域恰为 (31.3)：$u\in\mathcal H_1$ 且存在 $a\in L^2(d\xi)$，使 $q(u,v)=\langle a,v\rangle$ 对全部 $v\in\mathcal H_1$ 成立，此时 $\mathscr Au=a$。不以穿孔闭包或各向同性 Sobolev 域替换它。

取原坐标

$$
\begin{aligned}
R&=((x^2+y^2)^2+16z^2)^{1/4},&\ell&=\log R,
&J&=(-\pi/2,\pi/2),&c&=\cos a,\\
\omega(a,\varphi)&=(\sqrt c\cos\varphi,\sqrt c\sin\varphi,\sin a/4),
&d\xi&=\tfrac14 e^{4\ell}\,d\ell\,da\,d\varphi,\\
\delta_r(x,y,z)&=(rx,ry,r^2z),
&w_f(\ell,a)&=\sqrt{2\pi}\,e^\ell
 f(\delta_{e^\ell}\omega(a,\varphi)).
\end{aligned}
$$

最后一式用于轴对称 $f$，其精确物理配对为

$$
4\langle f,h\rangle_{L^2(d\xi)}
 =\int e^{2\ell}\langle w_f(\ell),w_h(\ell)\rangle_{L^2(J,da)}\,d\ell.
\tag{35.1}
$$

原自然角域为

$$
\mathcal H_c=\{b\in L^2(J,da):b\in AC_{\rm loc}(J),\
                         \sqrt c\,b'\in L^2(J,da)\},
$$

没有额外端点迹条件。沿用角形式

$$
\begin{aligned}
A[b]&=\int_J(4c|b'|^2+c|b|^2)\,da,
&C[b]&=\int_Jc|b|^2\,da,\\
I_n&=\int_0^{\pi/2}\sin^{n-2}t\,dt,
&q_n(a)&=I_n^{-1}\int_0^1
       u^{n-2}(1-u^2\sin^2a)^{-1/2}\,du,\\
Q_n[b]&=\int_Jq_n|b|^2\,da,
&h&=A-\frac{g}{2\pi}Q_n.
\end{aligned}
$$

$H_{n,g}(\sigma,m)$ 是 $h[b]+\int c(\sigma+m\tan a)^2|b|^2\,da$ 的原自然复自伴表示。$m$ 遍历全部整数；$m=0$ 的域为 $\mathcal H_c$，$m\ne0$ 时另要求 $\int(\sin^2a/c)|b|^2\,da<\infty$。保留原复重数和全部角模定义

$$
L=L_{n,g}=\frac1{4\pi}\sum_{m\in\mathbb Z}\int_{\mathbb R}
       \operatorname{rank}_{\mathbb C}
       \mathbf1_{(-\infty,0)}(H_{n,g}(\sigma,m))\,d\sigma.
$$

$g_n^{\rm iso}>\lambda_n$、$L>0$ 以及 $s=2\pi L>0$ 由 $G$ 的引理 24.2、命题 24.3 推出，不是新增假设。

下面的 $K,N,Z$ 仅定义在实际约化扇区 $\mathcal S$，即完整复轴对称、$z$ 偶扇区；不删除原算子的其他角模。$\mathsf K_g$ 是 $h$ 在偶 $L^2(J,c\,da)$ 中的自然表示，其唯一负本征值为 $-s^2$，相应 $\psi$ 实、正、偶且 $C[\psi]=1$；正本征值记作 $\nu^2$，相应自然复偶本征空间为 $E_\nu$。物理角质量仍是无权 $da$。

加权空间取 (33.1) 的同一完成空间：内区范数为原自由范数，外部图能量为

$$
\int\{C[w_\ell]+A[w]+e^{-2\ell}\|Dw\|_{L^2(da)}^2\}\,d\ell,
\qquad D=2\sin a\,(\partial_\ell-1)+4c\partial_a.
$$

$H_\sigma$ 由 $e^{\sigma\rho}$、$\rho=(\ell-L_*)_+$ 共轭定义。选择原供应者允许的固定小 $d>0$，使 $d<1/2$ 且小于最小正角指数。令

$$
\begin{aligned}
P_d &:H_d\longrightarrow(H_{-d})^*,&(P_df)(z)&=4q(f,z),\\
K&=\ker P_d,&N&=\ker\mathscr A\cap\mathcal S,\\
Z&=\{z\in H_{-d}:q(f,z)=0\ \text{对每个 }f\in H_d\}.
\end{aligned}
$$

这里反对偶及原自由闭包 $\mathcal H_1$ 的含义均与定义 33.1 相同；辅助指数一空间不被识别为 $\mathcal H_1$。直接复用 (33.3) 与定理 34.2：$K$ 有限维，$Z=K\oplus\mathbb C f_0$，$f_0$ 是原全局局部自由形式零能解，存在 $b\ne0$ 使

$$
w_{f_0}(\ell)=(be^{is\ell}+\overline b e^{-is\ell})\psi+r_0(\ell),
\qquad
\int_{b_*}^{\infty}e^{2d\ell}\|r_0(\ell)\|_{L^2(da)}^2\,d\ell<\infty.
\tag{35.2}
$$

$b_*$ 为固定充分大对数半径。令 $\Sigma=\{\nu\in(0,1]:\nu^2\in\sigma(\mathsf K_g)\}$，允许为空。唯一复线性系数映射 $\mathsf A_\nu:K\to E_\nu$ 满足

$$
w_v(\ell)=\sum_{\nu\in\Sigma}e^{-\nu\ell}\mathsf A_\nu(v)+r_v(\ell),
\tag{35.3}
$$

其中余项具有 (34.5) 的完整 $\delta$ 加权图界，固定 $\delta>1$ 满足 (34.3)。余项映射有界，包含原中央场和全部高阶偶角分量；$N=\ker(\mathsf A_\nu)_\nu=K\cap L^2(d\xi)$。不要求系数映射满射，其像和各系数均允许为零。这些均为定理 34.2 的供应结论。

取定义 33.2 的同一原外解 $F_E$、固定内截断 $\eta$，以及 $U_E=\eta F_E$、$C_E=(\mathscr A+E)U_E$。对每个充分小的 $E>0$，$U_E\in D(\mathscr A)$，$C_E$ 是固定紧环带上的实际 $L^2$ 函数。令 $T=\tfrac12\log(1/E)$、$x=\ell-T$。完整耦合 wall 的同一实解 $W$ 满足

$$
W(x)=(\beta e^{isx}+\overline\beta e^{-isx})\psi
                 +O_{\mathcal H_c}(e^{d_0x})\quad(x\to-\infty),
\qquad |\beta|=1.
$$

(33.4) 给出 $w_{F_E}(T+x)=W(x)+r_T(x)$、$r_T=\sigma^{-1}Y_T$、$\|Y_T\|_{X_T}\le Ce^{-dT}$，其中 $\sigma=e^{dx}$ 于左端、右端为一；$X_T$ 范数含 $\int A[Y_T]$ 和 $\int e^{2x}\|Y_T\|_{L^2(da)}^2\,dx$。右端原外解与 $W$ 保有 (33.9) 的一致指数物理质量界。直接复用 (33.10)--(33.11)、(34.18) 及定理 34.4 证明中的弱收敛：

$$
\begin{aligned}
\langle C_E,v\rangle&=E\langle U_E,v\rangle&& (v\in K),\\
\langle C_E,f_0\rangle
 &=-s\operatorname{Im}(\overline\beta b e^{isT})+o(1),
\end{aligned}
\tag{35.4}
$$

$$
m_W=\frac14\int e^{2x}\|W(x)\|_{L^2(da)}^2\,dx\in(0,\infty),
\qquad E\|U_E\|_2^2\longrightarrow m_W,
\qquad \sqrt E\,U_E\rightharpoonup0\ \text{于 }L^2(d\xi).
\tag{35.5}
$$

所有配对均使用原物理测度。这里的 $Z$ 不被断言为全算子余核。

**命题 35.2（完整 wall 给出的实际慢共振输入）。** 对每个 $\nu\in\Sigma$ 及 $\alpha\in E_\nu$，定义反线性泛函

$$
J_\nu(\alpha)=\frac14\int_{\mathbb R}e^{(2-\nu)x}
                 \langle W(x),\alpha\rangle_{L^2(da)}\,dx.
\tag{35.6}
$$

积分绝对收敛。令 $K_{\ge\nu}=\{v\in K:\mathsf A_\mu(v)=0\ \text{当 }\mu<\nu\}$。在 $K_{\ge\nu}$ 的 $H_d$ 单位球上一致地，有

$$
E^{-\nu/2}\langle C_E,v\rangle
       \longrightarrow J_\nu(\mathsf A_\nu(v))\qquad(E\downarrow0).
\tag{35.7}
$$

在 $N$ 的 $H_d$ 单位球上一致地，$E^{-1/2}\langle C_E,z\rangle\to0$。若 (35.7) 右端为零，结论仅为相应 little-o，不断言系数非零。

证明。左端 $W$ 在 $\mathcal H_c$ 中有界，$2-\nu\ge1$，故 (35.6) 的左半线绝对可积；右端由 (33.9) 的指数质量界和 Cauchy--Schwarz 不等式可积。

先对每个 $\nu\in\Sigma$ 证明实际向量矩收敛：

$$
\int e^{(2-\nu)x}w_{U_E}(T+x)\,dx
       \longrightarrow\int e^{(2-\nu)x}W(x)\,dx
                 \quad\text{于 }L^2(J,da).
\tag{35.8}
$$

在 $x\le-2$，$\|Y_T\|_{X_T}$ 的 $A$ 部分控制无权角 $L^2$ 范数，且

$$
\begin{aligned}
&\int_{b_*-T}^{-2}e^{(2-\nu)x}\|r_T(x)\|_{L^2(da)}\,dx\\
&\quad\le\left(\int_{-\infty}^{-2}e^{2(2-\nu-d)x}\,dx\right)^{1/2}
             \|Y_T\|_{L^2(dx\,da)}
 \le Ce^{-dT}.
\end{aligned}
$$

这里 $2-\nu-d>0$。固定有限 $x$ 区间的误差同样趋零。右端 $x\ge R$ 的向量矩尾由外解与 $W$ 的一致指数质量界控制为随 $R\to\infty$ 趋零的函数，且对 $E$ 一致；先固定 $R$，再令 $E\downarrow0$，最后令 $R\to\infty$，得到 (35.8)。固定内截断 $\eta$ 与原外解起点遗漏的 $W$ 左尾亦趋零，没有取能量子列。

取固定外部光滑截断 $\zeta$，在充分远端为一。由 (35.3) 和 $\delta>1$，可写

$$
v=\sum_{\mu\in\Sigma}v_\mu^{\rm model}+R_v,
\qquad
w_{v_\mu^{\rm model}}(\ell)
 =\zeta(\ell)e^{-\mu\ell}\mathsf A_\mu(v),
\qquad R_v\in L^2(d\xi).
$$

映射 $v\mapsto R_v$ 在有限维 $K$ 上有界；内区由局部自由形式身份保证 $L^2$。利用 (35.5) 的弱收敛与有限维一致性，余项配对为

$$
E\langle U_E,R_v\rangle
 =\sqrt E\,\langle\sqrt E\,U_E,R_v\rangle
 =o(\sqrt E)\|v\|_{H_d}.
\tag{35.9}
$$

由 (35.1)，慢尾模型的贡献除以 $e^{-\mu T}$ 后，恰为 (35.8) 与 $\mathsf A_\mu(v)$ 的角配对再除以 $4$，外加固定 $\zeta$ 过渡区的 $o(1)$，故该贡献为

$$
e^{-\mu T}\{J_\mu(\mathsf A_\mu(v))+o(1)\|v\|_{H_d}\}.
$$

对 $v\in K_{\ge\nu}$，$\mu<\nu$ 的各项为零，$\mu>\nu$ 的各项除以 $e^{-\nu T}$ 后趋零；(35.9) 除以 $e^{-\nu T}$ 也趋零。临界 $\nu=1$ 使用 (35.9) 的 little-o。有限维一致性给出 (35.7)；对 $N$，所有慢系数为零，直接使用 (35.9)。$\square$

命题 35.2 确定了 (33.20)--(33.21) 的实际 $C_E$ 慢共振系数，不以正能量逆估计为前提，也未用 $C$ 正交性删除物理质量交叉项。

**定义 35.3（有限物理质量相容矩阵与显式修正）。** 选 $0<a<b_c<\infty$ 和 $\theta\in C^\infty([0,\infty);[0,1])$，使 $\theta=1$ 于 $[0,a]$、$\theta=0$ 于 $[b_c,\infty)$；令 $\chi=\theta^2$。取 $b_c$ 充分小，使

$$
\frac14\int_{x>\log b_c}e^{2x}\|W(x)\|_{L^2(da)}^2\,dx
                                      >m_W/2.
\tag{35.10}
$$

因 $m_W>0$ 且左端质量可积，总能如此选择。选择可依赖固定 $n,g$，不改变其允许区间。记 $\theta_T=\theta(e^{-T}R)$、$\chi_T=\chi(e^{-T}R)$。

选 $K$ 的实适配基 $(z_\alpha,r_i)$：$z_\alpha$ 为 $N$ 的实基；$r_i$ 为 $K/N$ 依最小非零指数 $\nu_i$ 的适配基代表，$\alpha_i=\mathsf A_{\nu_i}(r_i)\ne0$，同指数首系数独立。原系数和空间在复共轭下不变，故这些实基的复线性包恰为原完整复 $K$，不缩小复重数。所有相关指标集合及各块均允许为空，实际系数像允许为零。

用 $v_i$ 统一表示该基，并设

$$
\kappa_\alpha(E)=\sqrt E\quad(z_\alpha\in N),
\qquad
\kappa_i(E)=
\begin{cases}
E^{\nu_i/2},&\nu_i<1,\\
\sqrt{ET},&\nu_i=1.
\end{cases}
$$

定义

$$
\begin{aligned}
\Gamma_{ij}(E)&=E\langle\theta_Tv_i,\theta_Tv_j\rangle
               =E\langle\chi_Tv_i,v_j\rangle,\\
M_{ij}(E)&=\Gamma_{ij}(E)/(\kappa_i\kappa_j).
\end{aligned}
\tag{35.11}
$$

直接复用定理 34.3 的物理 Gram 结论，将其固定截断取为 $\theta$ 并作常数径向缩放，得到

$$
\begin{aligned}
M(E)&\longrightarrow
 \operatorname{diag}(G_N,G_{\rm pow},G_{\rm log})=:G,\\
G_{N,\alpha\beta}&=\langle z_\alpha,z_\beta\rangle_{L^2(d\xi)},\\
G_{{\rm pow},ij}
 &=\tfrac14\langle\alpha_i,\alpha_j\rangle_{L^2(da)}
       \int_0^{b_c}\theta(r)^2r^{1-\nu_i-\nu_j}\,dr
                    &&(\nu_i,\nu_j<1),\\
G_{{\rm log},ij}&=\tfrac14\langle\alpha_i,\alpha_j\rangle_{L^2(da)}
                    &&(\nu_i=\nu_j=1).
\end{aligned}
\tag{35.12}
$$

每个非空块正定，跨块极限为零；幂块保留不同指数之间的全部无权 $da$ 交叉项。该结论由既有定理直接提供。$\Gamma(E)$ 只是明确写出的有限物理质量相容矩阵，不是 $\mathscr A+E$ 的补空间压缩或 Schur 补。

定义实向量 $B_j(E)=\langle C_E,v_j\rangle/\kappa_j$。命题 35.2 给出

$$
B(E)\longrightarrow
 B_*=(0,(J_{\nu_i}(\alpha_i))_{\nu_i<1},0).
\tag{35.13}
$$

由 (35.12)，$M(E)$ 对每个充分小 $E$ 正定可逆。置

$$
d(E)=-M(E)^{-1}B(E),
\qquad
h_E=\sum_i d_i(E)\kappa_i(E)^{-1}\chi_Tv_i.
\tag{35.14}
$$

$K=0$ 时为空和 $h_E=0$；零维逆均采用唯一空映射。

**命题 35.4（原完整复 $K$ 的实际有限相容修正）。** 定义 35.3 的构造对每个充分小 $E$ 满足

$$
h_E\in D(\mathscr A),\qquad
\|h_E\|_2=O(E^{-1/2}),\qquad
E\langle h_E,v\rangle=-\langle C_E,v\rangle\quad(v\in K).
\tag{35.15}
$$

$h_E$ 紧支撑。令 $R_E=(\mathscr A+E)(U_E+h_E)$，则 $R_E$ 是紧支撑的实际 $L^2$ 函数，且

$$
\langle R_E,v\rangle=0\qquad(v\in K).
\tag{35.16}
$$

归一化系数的精确极限为

$$
d(E)\longrightarrow d_*=(0,-G_{\rm pow}^{-1}J_{\rm pow},0),
\qquad J_{\rm pow}=(J_{\nu_i}(\alpha_i))_{\nu_i<1}.
\tag{35.17}
$$

非空真零、幂、临界块的对角反演尺度分别为 $E^{-1}$、$E^{-\nu_i}$、$(ET)^{-1}$；混合幂由整个 $G_{\rm pow}$ 控制，不能逐指数丢弃物理交叉项。

证明。定理 34.3 的原场乘法与表示定理结论给出每个 $\chi_Tv_i\in D(\mathscr A)$；$\chi$ 在极点附近恒为一，故不改变原极点闭包。有限和给出 $h_E\in D(\mathscr A)$。矩阵恒等式为

$$
\Gamma=\operatorname{diag}(\kappa)M\operatorname{diag}(\kappa).
$$

实基使这些矩阵实对称，(35.14) 因而给出

$$
E\langle h_E,v_j\rangle/\kappa_j
       =\sum_i d_iM_{ij}=-B_j.
$$

按第二变量的复反线性延拓，方程对原完整复 $K$ 成立。反演尺度来自此加权矩阵恒等式及有限维逆的连续性，不是原预解式界；(35.12)--(35.13) 亦直接给出 (35.17)。

对 $\chi_Tv_i$ 的质量再次应用定理 34.3，此时其截断取为 $\chi$，得到这些向量除以 $\kappa_i$ 后的物理 Gram 乘 $E$ 有界。$d(E)$ 有界，故 $\|h_E\|_2=O(E^{-1/2})$。

每个 $v\in K$ 是原全测试局部形式零能解。$h_E$ 是紧支撑原自由形式向量，可由原紧光滑 core 在固定更大紧集上逼近，故 $q(h_E,v)=0$。其原算子像由 (34.15) 的环带乘法公式给出，是紧支撑 $L^2$ 函数，于是 $\langle\mathscr Ah_E,v\rangle=0$。结合 (35.4)、(35.15)，

$$
\langle R_E,v\rangle
 =\langle C_E,v\rangle+\langle\mathscr Ah_E,v\rangle
                            +E\langle h_E,v\rangle=0.
$$

$C_E$、$h_E$、$\mathscr Ah_E$ 均紧支撑，所写残差配对均为普通局部物理 $L^2$ 配对。$\square$

(35.15) 针对真实右端给出有限相容修正，不是假定未知解存在；它未给出 $\|R_E\|_2=o(\sqrt E)$。

**命题 35.5（修正的正物理主质量与剩余标量相位）。** 在定义 35.3 下，令

$$
H(x)=\sum_{\nu_i<1}d_{i,*}\chi(e^x)e^{-\nu_i x}\alpha_i
       \quad\text{于 }L^2(\mathbb R,e^{2x}dx;L^2(J,da)).
\tag{35.18}
$$

幂块为空时 $H=0$。置

$$
J_H=\frac12\int_{\mathbb R}e^{(2+is)x}
                       \langle H(x),\psi\rangle_{L^2(da)}\,dx,
\qquad \Lambda=is\overline\beta+J_H.
\tag{35.19}
$$

$H$ 实，支撑于 $x\le\log b_c$，且各指数 $\nu_i<1$，所以这些积分绝对收敛。令 $u_E=U_E+h_E$。对每个充分小 $E$，$u_E\in D(\mathscr A)$，并有

$$
E\|u_E\|_2^2\longrightarrow
 m_{\rm corr}=\frac14\int e^{2x}
          \|W(x)+H(x)\|_{L^2(da)}^2\,dx>m_W/2,
\tag{35.20}
$$

$$
\langle R_E,f_0\rangle=\operatorname{Re}(b\Lambda e^{isT})+o(1).
\tag{35.21}
$$

若 $\Lambda\ne0$，取任意 $\arg(b\Lambda)$，令

$$
T_*=(\pi/2-\arg(b\Lambda))/s,
\qquad D_{\rm comp}=e^{-2T_*}.
$$

若 $\Lambda=0$，任取固定 $D_{\rm comp}>0$。两种情形下，$E_j=D_{\rm comp}e^{-j/L}$ 对每个充分大整数 $j$ 都给出非零原域向量 $u_{E_j}$，满足 (35.16) 以及

$$
\langle R_{E_j},f_0\rangle\longrightarrow0,
\qquad
\|\langle R_{E_j},\cdot\rangle|_Z\|_{Z^*}\longrightarrow0.
\tag{35.22}
$$

$Z$ 上使用定义 33.1 的有限维范数。$D_{\rm comp}$ 仅为此有限相容构造的标量相位常数，未被识别为 (33.22) 所需的最终谱相位常数。

证明。由 (33.13)、固定内截断以及 $W$ 左端质量可积，

$$
w_{U_E}(T+\cdot)\longrightarrow W
                   \quad\text{于 }L^2(e^{2x}dx\,da).
\tag{35.23}
$$

对 $\nu_i<1$，(35.3)、(35.1) 给出

$$
w_{\kappa_i^{-1}\chi_Tr_i}(T+\cdot)
       \longrightarrow\chi(e^x)e^{-\nu_i x}\alpha_i
                   \quad\text{于同一加权 }L^2\text{ 空间}.
\tag{35.24}
$$

具体地，$\mu>\nu_i$ 且 $\mu<1$ 的高慢项带有额外因子 $e^{-(\mu-\nu_i)T}$；$\mu=1$ 的临界项至多多出 $\sqrt T$，仍由 $e^{-(1-\nu_i)T}$ 消去。物理 $L^2$ 余项的相应范数由 $Ce^{-(1-\nu_i)T}$ 控制而趋零，固定内区亦然。所处理高项是真实原向量中的项，未通过删除高项更换原算子。

真零和临界归一化向量在此加权物理范数中有界，其系数由 (35.17) 满足 $d_i(E)\to0$，故总贡献趋零。由 (35.17)、(35.23)--(35.24)，

$$
w_{u_E}(T+\cdot)\longrightarrow W+H
                           \quad\text{于 }L^2(e^{2x}dx\,da).
$$

(35.1) 给出 (35.20) 的极限。$H$ 在 $x>\log b_c$ 为零，故 (35.10) 给出 $m_{\rm corr}>m_W/2$，并证明 $u_E$ 对每个充分小 $E$ 非零；不需排除允许共振或假定任何块非空。

$h_E$ 紧支撑，原 $f_0$ 的全测试零能方程给出 $q(h_E,f_0)=0$，故

$$
\langle R_E,f_0\rangle
       =\langle C_E,f_0\rangle+E\langle h_E,f_0\rangle.
\tag{35.25}
$$

在 $x\le\log b_c$ 上，(35.2) 的移位余项在 $e^{2x}$ 物理范数中趋零：外部余项的平方积分至多为 $Ce^{-2dT}$，固定内区至多为 $Ce^{-2T}$。该区域内的站波 $G_{be^{isT}}(x)$ 的同一范数一致有界。因此 (35.24) 和消失的真零、临界贡献可用于 (35.25) 的质量配对，得到

$$
\begin{aligned}
E\langle h_E,f_0\rangle
 &=\frac14\int e^{2x}\Big\langle H(x),
       (be^{is(T+x)}+\overline b e^{-is(T+x)})\psi
                         \Big\rangle_{L^2(da)}\,dx+o(1)\\
 &=\operatorname{Re}(be^{isT}J_H)+o(1).
\end{aligned}
$$

结合 (35.4) 以及 $-s\operatorname{Im}z=\operatorname{Re}(isz)$，恰得 (35.21)。若 $\Lambda\ne0$，$T_j=T_*+\pi j/s$ 使 $\operatorname{Re}(b\Lambda e^{isT_j})=0$。因 $s=2\pi L$，$e^{-2T_j}=D_{\rm comp}e^{-j/L}$；若 $\Lambda=0$，(35.21) 对任意趋零 $E$ 均为 $o(1)$。$K$ 配对已由 (35.16) 精确消去，$Z=K\oplus\mathbb C f_0$ 且有限维，故得 (35.22)。$\square$

**注记 35.6（实际消费者与未得出的全残差结论）。** 命题 35.2、35.4、35.5 共同服务问题 33.4 的 (33.20)--(33.22)，特别是 (33.21) 的实际 $K$ 相容数据：命题 35.2 给出实际 $C_E$ 对每个实际慢共振首系数的能量尺度及完整 wall 系数；命题 35.4 以紧支撑原域向量消掉全部 $K$ 相容数据并给出其物理放大；命题 35.5 给出修正后的非零主质量及剩余 $f_0$ 相位。$\Gamma(E)$ 的非空块正定性直接来自定理 34.3。

所构造的是有限相容修正；尚无

$$
(\mathscr A+E)h_E=-C_E+\rho_E,
\qquad \|\rho_E\|_2=o(\sqrt E)
$$

的范数结论。实际残差为 $R_E=C_E+(\mathscr A+E)h_E$，固定内环带上的 $C_E$ 不会仅因有限相容方程而得到小范数估计。这里没有消去原补空间后的有效 Schur 矩阵估计，也未控制该消元的误差放大；未来补空间修正若改变右端，仍须在同一原物理尺度重新处理相容数据，不能直接沿用本 $\Gamma(E)$ 为最终有效矩阵。

原目标 (33.22) 仍要求：对每个整数 $n\ge2$、整个原隔离区间的每个固定 $g$，以某个固定 $D>0$，在每个充分大整数层级 $E_j=De^{-j/L}$ 构造非零原域向量，满足

$$
\frac{\|(\mathscr A+E_j)u_j\|_{L^2(d\xi)}}
 {E_j\|u_j\|_{L^2(d\xi)}}\longrightarrow0.
$$

(35.20)、(35.22) 未给出该全物理 $L^2$ 残差结论；对已构造且质量为 $E^{-1/2}$ 阶的向量，仍缺 $\|R_E\|_2=o(\sqrt E)$。有限 $K$ 精确消去和 $Z^*$ 小量既不证明也不反驳原目标。定理 31.4 保持原域与残差用途；(31.16)、(32.3) 仅是其特定构造的充分条件，不是原目标必要条件。条件应用 24.6，尤其其 (24.18)，保持原条件角色，未由上述配对小量支付其前件。

这里没有缩小原隔离区间、选取能量子列、排除核或共振、假定标量约化、加强源尾部或替换自然端点，也不增加负谱穷尽、简单性或全算子余核义务；满足同一原目标的其他路线仍然允许。$\Sigma,K,N$ 及各块允许为空，实际系数像以及 $J,H,\Lambda$ 允许为零。结论限于所述原模型的条件数学分析，不涉及物理实现。命题 35.2、35.4、35.5 是对既有原模型结果的具体综合推导；有限维正定矩阵反演、弱收敛的有限维一致性、Cauchy--Schwarz 不等式及移位质量积分均为其中复用的经典方法，不单列为新结果，也不作全局文献优先权判断。

**数学引文 35.7（版本、参数对应与适用界限）。**

1. [原边界响应卷](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md)，修订 d6d829c43b0ed4f127a09666bc40088b6f440b94，定义 18.1 及定义 1.1 的解析供应者固定。
2. [本卷第 31、33、34 节](https://github.com/the-omega-institute/trureturing/blob/c4e346266d26ad884d034fd81e94f269df61a965/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GLUING.md)，修订 c4e346266d26ad884d034fd81e94f269df61a965；本节直接复用其慢尾、原域截断、Gram、物理零模和 wall 质量结论。
3. [完整 Green 边缘续篇](https://github.com/the-omega-institute/trureturing/blob/c4e346266d26ad884d034fd81e94f269df61a965/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md)，同一修订，第 24、26、28、30 节；条件结论按本卷原接口使用。
4. [变量系数 Green 稳定性卷](https://github.com/the-omega-institute/trureturing/blob/5cec4fa83ae7bbb4e787c42606525db4cd11ed48/docs/develop/theory/FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)，修订 5cec4fa83ae7bbb4e787c42606525db4cd11ed48，第 10 节；供应原自然角闭域、坐标与测度规范。
5. Colin Guillarmou and Andrew Hassell, *Resolvent at low energy and Riesz transform for Schrödinger operators on asymptotically conic manifolds. II*, Ann. Inst. Fourier 59(4), 1553--1610 (2009)，DOI [10.5802/aif.2471](https://doi.org/10.5802/aif.2471)，[PDF](https://aif.centre-mersenne.org/item/10.5802/aif.2471.pdf) 页 1--5（封面、印刷页 1553--1556），第 1 节。其光滑 scattering metric、$V=O(x^l)$（$l\ge3$）及物理空间 $L^2(M,dg)$ 是具体适用条件。原 $E$ 对应其 $k^2$、原 $R$ 对应 $1/x$ 仅对应能量量纲；原非零 $-gq_n/(2\pi)R^{-2}$ 主势不满足其三阶消失条件，原自然退化角域与完整各向异性场的度量、域对应亦未建立。因缺完整假设、域和测度对应，这里的证明不调用其预解式定理，该文不是原目标的现成逆供应者。
6. 钉版 mathlib [56a005855ea17e0b0958f73ec801ae140b0a1679 的 FredholmAlternative](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean) 中，有界紧算子非零谱值的 Fredholm 二择一不提供本原非有界 $\mathscr A$ 的低能有权参数逆；本仓 `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.lean` 的正矩阵行列式极限定理亦不提供该逆。这两项与原问题的上述界限不构成对本节结论的形式化认证。

## 追加锚（本行以下为增补区）
