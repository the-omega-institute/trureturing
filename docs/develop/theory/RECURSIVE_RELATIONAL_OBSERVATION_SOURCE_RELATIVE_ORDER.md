# Original-source relative order

## 1. The original endpoint, trace and numerical inputs

**Definition 1.1 (analytic suppliers and the unchanged source).** Write
[D] for [Full-source recovery and finite native phase covers](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md),
[E] for [the endpoint appendix](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md),
and [S] for [Appendix II](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md).
Retain the hypotheses and conclusions of [E, §§109–112],
[S, §§115–117, 130–133] and [D, §§10–12]. In particular the source is

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad e=(0,0,0,0),\\
pp'=(x+x',y+y',z+z',w+w'+xy'),\qquad
d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\quad L\Gamma=\delta_e,\\
S_{\min}=(aL-\eta\partial_w^2-16\sqrt{a\eta}\,\Gamma)
 \big|_{C_c^\infty(G\setminus\{e\};\mathbb C)},\qquad a,\eta>0.
\end{gathered}
\tag{SRO.1}
$$

The Green field has its original unit-source normalization and satisfies
the bound $\Gamma\le32\varrho^{-3}$ of [D, §10], where
$\varrho^4=|(x,y,z)|^4+(w-xy/2)^2$. The actual zero vector and endpoint are

$$
\begin{gathered}
C(w_*)=1,\qquad h=w_*/\|w_*\|_2,\qquad
c_h=C(h)=\|w_*\|_2^{-1}>0,\qquad \rho=A(h)/c_h\in\mathbb R,\\
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\qquad
H=H_{\rm end}\ge0,\qquad \ker H=\mathbb Ch,\\
D(F)=\{u\in D(S_{\min}^*):C(u)=0\},\qquad H\ne F,\\
m=h^2\mu,\quad m(G)=1,\quad J_hu=hu,\quad
K=J_h^{-1}HJ_h,\quad T_t=e^{-tK},\quad v_t=hg_t.
\end{gathered}
\tag{SRO.2}
$$

All operator domains are the entire complex domains. Raw inner products
are antilinear in the first slot. The legitimate nonpolar source trace
on the full form $\mathscr V=\mathscr V_0\dotplus\mathbb C1$ obeys

$$
\operatorname{tr}u=C(hu)/c_h\quad(u\in D(K)),\qquad
s_t:=\operatorname{tr}g_t=\|v_{t/2}\|_2^2.
\tag{SRO.3}
$$

These are [S, (115.20), (116.3)] and [D, (12.29)]. The vector $h$ is real,
smooth and strictly positive off $e$; no finite value $h(e)$ is assigned.
The function $g_t$ off $e$ means the smooth representative $v_t/h$.
Its almost-everywhere class is independent of permitted Borel repairs.

**Definition 1.2 (names and source coordinates).** The inputs are total
rational interval names of the original finite positive $a,\eta,d$.
A scalar name gives certified intervals of arbitrarily small width.
The services constructed in [D, §§11–12] are available with their exact
source/domain correspondences: raw global $L^2$ names of $w_*,h$, the
constant/logarithmic graph pairs $(\gamma_c,\ell_c)$ and
$(\gamma_l,\ell_l)$, the endpoint $\rho$, and the full resolvent and
heat/source names. A raw name consists of finite rational complex box
steps in the original coordinates with certified global norm errors.
In particular raw norms and pairings have scalar names. No pointwise
heat evaluator, spatial modulus, supremum or Harnack constant is input.

Use the unitary chart and cylinder of [D, (11.2)–(11.6)]:

$$
\begin{gathered}
\kappa=\sqrt{\eta/a},\quad Z=(\xi,u)=(x,y,z,u),\quad
\Phi_\kappa(Z)=(x,y,z,\kappa u+xy/2),\\
f_v(Z)=\sqrt\kappa\,v(\Phi_\kappa Z),\quad
R=|Z|,\quad \tau=-\log R,\quad H_v(\tau,\omega)=R f_v(R\omega),\\
\|v\|_2^2=\int_{\mathbb R}e^{-2\tau}
                 \|H_v(\tau)\|_{L^2(S^3)}^2d\tau.
\end{gathered}
\tag{SRO.4}
$$

The Jacobian of $\Phi_\kappa$ is $\kappa$. The time of the original
evolution is denoted by $t$, distinct from $u$ and $\tau$.
The positive angular vector, its ordinary surface normalization and the
comparison operator are exactly

$$
\begin{gathered}
N_0=2\pi/\sqrt3,\qquad
e_0(\sin\vartheta\,\Omega,\cos\vartheta)
 =\frac{2\min(\vartheta,\pi-\vartheta)}{\pi N_0\sin\vartheta},\\
b[v]=\|\nabla_Sv\|_2^2+\|v\|_2^2
             -\frac4\pi\|v|_{\{u=0\}\cap S^3}\|_2^2,
\quad P_0=-\partial_\tau^2+B,\\
X=\{J:e^{\tau/8}J\in H^1(\mathbb R\times S^3)\},\qquad
Y=\{Q:e^{\tau/8}Q\in H^{-1}(\mathbb R\times S^3)\}.
\end{gathered}
\tag{SRO.5}
$$

Here $B$ is the form operator of $b$, $Be_0=0$, $\|e_0\|_2=1$,
$\|e_0\|_{H^1}^2=12/\pi^2$, and $B\ge2$ on $e_0^\perp$.
This last gap is not a gap for $H$ or $F$.

Let $q$ be the polynomial cutoff of [D, §11]: it is zero on
$(-\infty,0]$, equals $6v^5-15v^4+10v^3$ on $[0,1]$, and is one on
$[1,\infty)$. Thus $|q'|\le2$, $|q''|\le6$. Retain exactly the computed
$C_E,T,\bar q,E_T,D_c,D_l,Z_c,Z_l$ of [D, (11.4)–(11.8), (11.14)]:

$$
\begin{gathered}
T\ge4,\quad 256C_Ee^{-T/4}\le\bar q<1/2,\quad
\|P_0^{-1}\|_{Y\to X}\le256,\quad
\|E_T\|_{X\to Y}\le C_Ee^{-T/4},\\
\|(P_0+E_T)^{-1}\|_{Y\to X}\le\frac{256}{1-\bar q},\qquad
\chi(\tau)=q(\tau-T-2),\\
(A,C)(\gamma_c)=(1,0),\quad
(A,C)(\gamma_l)=(0,1),\quad S_{\min}^*\gamma_j=\ell_j,\\
H_{\gamma_c}=\chi(e_0+Z_c),\quad
H_{\gamma_l}=\chi(\tau e_0+Z_l),\quad
\|Z_j\|_X\le\frac{256D_j}{1-\bar q}\quad(j=c,l).
\end{gathered}
\tag{SRO.6}
$$

On $\tau>T+1$, $P_0+E_T$ is the actual cylinder expression, not a
replacement differential equation. The maps $A,C$ in (SRO.2) are exactly
those of [E, (112.2)–(112.3)]. In particular they are complex linear.

## 2. A computed graph estimate reaching the entire source tail

**Theorem 2.1 (zero-coefficient graph control at a fixed computed level).**
The coefficient names compute a finite positive rational $C_0$ such that
every exact complex maximal pair $u\in D(S_{\min}^*)$,
$f=S_{\min}^*u$, with $A(u)=C(u)=0$, satisfies

$$
\|\chi H_u\|_X\le C_0(\|u\|_2+\|f\|_2),\qquad
\|H_u(\tau)\|_2\le C_0(\|u\|_2+\|f\|_2)e^{-\tau/8}
\quad(\tau\ge T+3).
\tag{SRO.7}
$$

The second assertion is the continuous $L^2(S^3)$ slice assertion;
it makes no pointwise angular assertion for an arbitrary maximal vector.
The level $T$ is the same constructed level as in (SRO.6).

Proof. Choose rational brackets $a_->0$ and
$0<\kappa_-\le\kappa\le\kappa_+$ with $a_-\le a$. Such brackets are
found by interval refinement and the strict positivity of the inputs.
Choose rational $E>e^{T+4}$ and $E_3>e^{3(T+4)}$, and set

$$
\begin{gathered}
\Lambda=4(1+\kappa_-^{-2}),\qquad
V_0=2^{12}(1+\kappa_++\kappa_-^{-2})E_3,\qquad D_0=4E,\\
C_\nabla=4+4\Lambda^2D_0+4\Lambda(1+V_0)+4\Lambda/a_-,\qquad
C_I=3E+2C_\nabla,\\
C_0=\frac{256}{1-\bar q}
       \left(a_-^{-1}+32\Lambda E C_I\right).
\end{gathered}
\tag{SRO.8}
$$

All these choices are finite rational arithmetic after elementary outward
enclosure of the exponentials. Large constants cause no logical change.

In the unitary coordinates the original equation divided by $a$ is

$$
-\operatorname{div}(A_\kappa(Z)\nabla f_u)
       -16\kappa\Gamma(\Phi_\kappa Z)f_u=a^{-1}f_f,
\tag{SRO.9}
$$

where the principal quadratic form is

$$
|p_1-yv/(2\kappa)|^2+|p_2+xv/(2\kappa)|^2+|p_3|^2+|v|^2.
\tag{SRO.10}
$$

The triangular shear and its inverse have squared norm at most
$\Lambda$ for $R\le1$, hence $\Lambda^{-1}I\le A_\kappa\le\Lambda I$.
For $R\le1$,

$$
\varrho(\Phi_\kappa Z)^4=|\xi|^4+\kappa^2u^2
 \ge\tfrac12\min(1,\kappa^2)R^4.
\tag{SRO.11}
$$

Indeed $u^2\ge u^4$ and
$|\xi|^4+u^4\ge(|\xi|^2+u^2)^2/2$. On
$T+1\le\tau\le T+4$, the original Green bound therefore gives
$16\kappa\Gamma(\Phi_\kappa Z)\le V_0$. For example the smaller bound
$1024(\kappa+\kappa^{-1})e^{3(T+4)}$ suffices, and is dominated by
the displayed $V_0$.

Put $I=[T+2,T+3]$ and
$\zeta(\tau)=q(\tau-T-1)(1-q(\tau-T-3))$. It is one on $I$,
supported in $[T+1,T+4]$, and $|\nabla_Z\zeta|\le D_0$.
The local regularity of [E, §112], matched to Shubin's Lemma 5.1,
gives $f_u\in H^2_{\rm loc}$ on this punctured collar. Test (SRO.9)
against $\zeta^2\overline{f_u}$ and take real parts. For
$U=\|u\|_2$, $F_u=\|f\|_2$, ellipticity and Young's inequality give

$$
\|\nabla f_u\|_{L^2(\{Z:-\log|Z|\in I\})}^2
 \le (2\Lambda V_0+4\Lambda^4D_0^2)U^2
            +(2\Lambda/a_-)UF_u.
\tag{SRO.12}
$$

The norm here is the ordinary $Z$-coordinate gradient norm on
$\{\tau\in I\}$. To obtain (SRO.12), bound the cross
term by half of $\Lambda^{-1}\int\zeta^2|\nabla f_u|^2$ plus
$2\Lambda^3D_0^2U^2$, and move that half to the left. The unitary factor
in (SRO.4) identifies the remaining $L^2$ norms with $U,F_u$.
The definition of $C_\nabla$ bounds the square root of the right side
by $C_\nabla(U+F_u)$; use
$UF_u\le(U+F_u)^2/4$ and $\sqrt x\le1+x$ for $x\ge0$.
No separate uncut source kinetic or potential integral is taken.

The exact polar derivative identities are

$$
\partial_\tau H_u=-R f_u-R^2\partial_Rf_u,\qquad
\nabla_SH_u=R^2\nabla_{\rm tan}f_u,\qquad
dZ=R^4d\tau d\omega.
\tag{SRO.13}
$$

They imply

$$
\|H_u\|_{H^1(I\times S^3)}
 \le3e^{T+3}U+2\|\nabla f_u\|_{L^2(\{\tau\in I\})}
 \le C_I(U+F_u).
\tag{SRO.14}
$$

Now $J=\chi H_u$ belongs to $X$. This uses precisely the qualitative
maximal-domain expansion [E, (112.2)] and $A=C=0$. If that expansion is
first stated beyond a larger unspecified level, local $H^1$ regularity
fills the finite intervening collar. This establishes membership without
using that level or its remainder norm as numerical data.

Write $P$ for the actual cylinder expression. The distributional equation
is exactly

$$
(P_0+E_T)J=[P,\chi]H_u+
                       a^{-1}\chi e^{-2\tau}H_f.
\tag{SRO.15}
$$

The factor is $a^{-1}R^3f_f=a^{-1}e^{-2\tau}H_f$, as in
[E, (112.9)–(112.10)]. Both $\chi$ and its derivatives are supported
where the cutoff defining $E_T$ is identically one.

Here is a bound for the commutator not requiring derivatives of a finite
name. For cylinder functions write
$\mathcal DH=\nabla_SH-\omega(H+\partial_\tau H)$. The exact kinetic
form is $\int\overline{\mathcal D\phi}\cdot A_\kappa\mathcal DH$,
and $\|\mathcal DH\|_2\le\sqrt2\|H\|_{H^1}$. The potential
commutes with $\chi$. Since
$\mathcal D(\chi H)=\chi\mathcal DH-\omega\chi'H$, the remaining
commutator pairing is

$$
-\int_I\chi'H_u\overline{\mathcal D\phi}\cdot A_\kappa\omega
 +\int_I\chi'\overline\phi\,\omega\cdot A_\kappa\mathcal DH_u.
\tag{SRO.16}
$$

Cauchy–Schwarz bounds its absolute value by
$6\Lambda\|H_u\|_{H^1(I\times S^3)}\|\phi\|_{H^1}$.
To compute its $Y$ norm, multiply the distribution by $e^{\tau/8}$,
equivalently replace the test by $e^{\tau/8}\phi$. On $I$ this
multiplier has $H^1$ norm at most $2e^{(T+3)/8}\le2E$.
Thus the commutator's $Y$ norm is at most
$32\Lambda E C_I(U+F_u)$.
For the forcing term, $H^{-1}$ is bounded by $L^2$, and

$$
\int\chi^2e^{-15\tau/4}\|H_f(\tau)\|_2^2d\tau
 \le\int e^{-2\tau}\|H_f(\tau)\|_2^2d\tau=F_u^2,
\tag{SRO.17}
$$

since its support has $\tau\ge T+2>0$. Its $Y$ norm is therefore at
most $a_-^{-1}F_u$. Apply the inverse estimate (SRO.6) to (SRO.15).
This proves the first inequality of (SRO.7) with (SRO.8).

Finally for a Hilbert-valued $W\in H^1(\mathbb R;L^2(S^3))$,
integration of $(\|W\|_2^2)'$ from a sequence tending to infinity on
which $\|W\|_2\to0$ gives
$\sup_\tau\|W(\tau)\|_2^2\le2\|W\|_2\|W'\|_2\le\|W\|_{H^1}^2$.
Use $W=e^{\tau/8}J$ and $\chi=1$ on $\tau\ge T+3$.
The local regularity and this continuous Hilbert-valued representative
agree on every such slice. This proves (SRO.7). $\square$

**Definition 2.2 (a computed remainder bound for the actual normalized zero state).**
Obtain positive rational brackets $c_-\le c_h\le c_+$ and a rational
$R_\rho\ge|\rho|$ from [D, §11], with $c_->0$. Put $A_+=R_\rho c_+$.
Choose rational upper bounds $G_j\ge\|\gamma_j\|_2$,
$L_j\ge\|\ell_j\|_2$ and
$N_j\ge256D_j/(1-\bar q)$ for $j=c,l$ using their supplied names.
Set

$$
\begin{gathered}
Y_h=1+A_+G_c+c_+G_l,\qquad F_h=A_+L_c+c_+L_l,\\
B_h=C_0(Y_h+F_h)+A_+N_c+c_+N_l.
\end{gathered}
\tag{SRO.18}
$$

For later use this is a certified bound for a whole-cylinder $X$ vector
whose restriction to $\tau\ge T+3$ is
$Z_h=H_h-c_h(\rho+\tau)e_0$. Indeed
$y=h-A(h)\gamma_c-c_h\gamma_l$ has $A(y)=C(y)=0$, norm at most $Y_h$
and maximal image norm at most $F_h$. Theorem 2.1 and (SRO.6) show that
$\chi H_y+A(h)Z_c+c_hZ_l$ is the required $X$ vector. In particular

$$
\|Z_h(\tau)\|_2\le B_he^{-\tau/8}\quad(\tau\ge T+3).
\tag{SRO.19}
$$

All cancellations are in the original complex coefficient maps.
No evolution by the auxiliary endpoint $F$ is used here.

## 3. A numerical all-angle floor for the actual source denominator

**Theorem 3.1 (a computed positive source floor).** The original
coefficient names compute a positive rational $L_h$ and an integer
$\tau_0\ge\max(T+4,1)$ such that

$$
R f_h(R\omega)\ge L_h\log(1/R)
\quad(0<R\le e^{-\tau_0},\ \omega\in S^3).
\tag{SRO.20}
$$

They require no numerical Harnack constant or assumed all-angle source
comparison. One possible output is $L_h=c_-/256$ with the terminating
search specified below.

Proof. The mature intermediate method is ordinary parabolic power
iteration on a fixed annulus; all constants needed here can be bounded
explicitly from the original potential. Take
$D=\{y\in\mathbb R^4:3/4<|y|<5/4\}$ and $0<r\le1$.
In the notation of [S, (130.3), (130.11)–(130.19)], put

$$
W_r(X,u)=r^2\Gamma(rX_1,rX_2,rX_3,
                         \kappa ru+r^2X_1X_2/2),\qquad V_r=16\kappa W_r.
\tag{SRO.21}
$$

The principal matrix $A_r$ is (SRO.10) with $(x,y)$ replaced by
$(rX_1,rX_2)$. On $D$ its ellipticity bounds are
$\Lambda^{-1}I\le A_r\le\Lambda I$, with the same rational $\Lambda$
as in (SRO.8). The potential in this proof is nonnegative; the operator
is $-\operatorname{div}(A_r\nabla)-V_r$. This fixes the sign independently
of conventions for a signed Schrödinger potential.

Extend $V_r|_D$ by zero outside $D$, writing $\widetilde V_r$.
The exact raw-Haar marginal is

$$
\int_\mathbb R W_r(X,u)du=\frac1{4\pi\kappa|X|}.
\tag{SRO.22}
$$

It follows from $dw=\kappa r\,du$ and the original unit-source marginal
$\int\Gamma(rX,w)dw=1/(4\pi r|X|)$; the full spatial Jacobian is
$\kappa r^4$. Thus [S, (130.6), (130.17)–(130.19)] give

$$
\begin{gathered}
\int\widetilde V_r\le25/2<13,\\
\sup_z\int_{|z-y|<s}\frac{\widetilde V_r(y)}{|z-y|^2}dy
 \le128s+(K_{\rm St}+3200)s^2,\\
K_{\rm St}=16\pi^2\,32\,\kappa^{-1/2}
                         (\sqrt3/8)^{-3/2}.
\end{gathered}
\tag{SRO.23}
$$

This statement covers every center, including centers outside $D$.
For $0<s\le1/4$ a rational sufficient bound is

$$
\sup_z\int_{|z-y|<s}\frac{\widetilde V_r(y)}{|z-y|^2}dy\le Ws,
\qquad W=2^{24}(1+\kappa_-^{-1})\ge1.
\tag{SRO.24}
$$

For example $\pi<4$, $\sqrt3/8>1/8$, and
$\kappa^{-1/2}\le1+\kappa_-^{-1}$ give
$K_{\rm St}<2^{18}(1+\kappa_-^{-1})$; substitution into (SRO.23)
proves (SRO.24). No derivative of the concentrating potential is bounded.

We detail a numerical form bound used by the power test. For any
$0<\delta\le1$ the ordinary four-dimensional Bessel kernel obeys

$$
G_b(x)=\int_0^\infty(4\pi t)^{-2}e^{-bt-|x|^2/(4t)}dt
 \le\frac{e^{-\sqrt b|x|/2}}{2\pi^2|x|^2}.
\tag{SRO.25}
$$

Split the exponent into $bt+|x|^2/(8t)$ and $|x|^2/(8t)$;
the first is at least $\sqrt b|x|/2$, and the remaining integral is
$8/|x|^2$. Set
$s=\delta/(4W)$ and $b=2^{20}W^4\delta^{-4}$.
The convolution $G_b*\widetilde V_r$ over $|x-y|<s$ is less than
$\delta/4$ by (SRO.24). On the complement its supremum is at most

$$
13s^{-2}e^{-\sqrt b s/2}
=208W^2\delta^{-2}e^{-128W/\delta}
\le\frac{1248}{128^3}\frac\delta W<\delta/4,
\tag{SRO.26}
$$

using $e^{-x}\le6x^{-3}$. Schur's test with weight
$\sqrt{\widetilde V_r}$ bounds
$\sqrt{\widetilde V_r}(-\Delta+b)^{-1}\sqrt{\widetilde V_r}$
by $\delta$ in $L^2$ operator norm. Apply this to bounded truncations
and pass by monotone convergence if a weight vanishes or is unbounded.
Equivalently, by the $BB^*$ identity, for all compactly supported
$f\in H^1(\mathbb R^4)$,

$$
\int\widetilde V_r|f|^2
 \le\delta\int|\nabla f|^2+
             2^{20}W^4\delta^{-3}\int|f|^2.
\tag{SRO.27}
$$

All constants are uniform in $r$ and were obtained from the actual
source potential, rather than its thin-layer limit.

Here are sufficient numerical constants for local iteration:

$$
A_0=2^{60}W^4(1+\Lambda)^5,\qquad C_{\rm loc}=2^{40}A_0^2.
\tag{SRO.28}
$$

For every $y_0\in S^3$ the ball $B(y_0,1/8)$ lies in $D$.
A nonnegative smooth local subsolution of
$U_\theta-\operatorname{div}(A_r\nabla U)-V_rU\le0$ on
$B(y_0,1/8)\times(-1,0)$ satisfies

$$
\operatorname{ess\,sup}_{B(y_0,1/16)\times(-1/2,0)}U
 \le C_{\rm loc}
       \|U\|_{L^2(B(y_0,1/8)\times(-1,0))}.
\tag{SRO.29}
$$

To check this constant, the ordinary compact-support Sobolev inequality
$\|f\|_4^2\le64\int|\nabla f|^2$ suffices. The coordinate-line
$W^{1,1}$ inequality in dimension four gives
$\|F\|_{4/3}\le\sum_i\|\partial_iF\|_1\le2\|\nabla F\|_1$.
Apply it to $F=|f|^3$ and then Cauchy–Schwarz to get
$\|f\|_4\le6\|\nabla f\|_2$; smooth density gives the asserted safe
constant $64$. This is the usual Gagliardo–Nirenberg–Sobolev intermediate.

For $p\ge2$ write $z=U^{p/2}$, $f=\eta z$ and
$Y=\int\eta^2z^2$. The power test, with the cross term estimated in
the $A_r$ metric by $4ab\le a^2+4b^2$, gives

$$
\frac{dY}{d\theta}+\frac1{2\Lambda}\int|\nabla f|^2
 \le\int(2|\eta_\theta|+8\Lambda|\nabla\eta|^2)z^2
                                  +p\int V_rf^2.
\tag{SRO.30}
$$

Indeed before converting from $\eta\nabla z$ to $\nabla f$ the
gradient coefficient is at least one in the $A_r$ metric, since
$4(p-1)/p\ge2$. The conversion costs at most
$\Lambda\int|\nabla\eta|^2z^2$ in addition to the cross-term cost
$4\Lambda\int|\nabla\eta|^2z^2$; $8\Lambda$ dominates their sum.
Use (SRO.27) with $\delta=(4\Lambda p)^{-1}$ to obtain

$$
\frac{dY}{d\theta}+\frac1{4\Lambda}\int|\nabla f|^2
 \le\int\left(2|\eta_\theta|+8\Lambda|\nabla\eta|^2
                  +2^{26}W^4\Lambda^3p^4\right)z^2.
\tag{SRO.31}
$$

Thus the $p$-dependent potential term has been absorbed with its
explicit $p^4$ cost. The calculation for $U+\epsilon$ follows from
the same subsolution inequality, since $V_r\ge0$; let
$\epsilon\downarrow0$. For positive parts of smooth solutions use smooth
convex truncations first. All tests are supported inside the punctured
annulus, where the actual coefficients and orbits are smooth.

For completeness take $p_j=2(3/2)^j$, spatial radii
$r_j=1/16+2^{-j}/16$ around $y_0$, and backward lengths
$\theta_j=1/2+2^{-j}/2$. Product cutoffs for successive cylinders can
have $|\nabla\eta_j|^2\le2^{12}4^j$ and
$|\partial_\theta\eta_j|\le8\,2^j$, be one on the next cylinder,
and vanish at the earlier time. Integration of (SRO.31) gives

$$
\sup_\theta\int f_j^2+\iint|\nabla f_j|^2
 \le H_j\iint_{Q_j}U^{p_j},\qquad H_j=A_0p_j^4\,4^j.
\tag{SRO.32}
$$

Here $(1+4\Lambda)$ times the sum of the three coefficients in
(SRO.31) is bounded by $H_j$: $p_j\ge2$, $W,\Lambda\ge1$ and
the displayed $A_0$ dominate each coefficient and their sum.
Space-time Hölder and the Sobolev inequality give

$$
\iint |f_j|^3\le64
 \left(\sup_\theta\int f_j^2+\iint|\nabla f_j|^2\right)^{3/2},
\quad
\|U\|_{p_{j+1},Q_{j+1}}
 \le64^{1/p_{j+1}}H_j^{1/p_j}\|U\|_{p_j,Q_j}.
\tag{SRO.33}
$$

The sums $\sum1/p_j=3/2$, $\sum j/p_j=3$ and
$\sum1/p_{j+1}=1$ bound the product by

$$
64\,2^6(3/2)^{12}4^3A_0^{3/2}
=34012224A_0^{3/2}<2^{26}A_0^{3/2}\le C_{\rm loc}.
\tag{SRO.34}
$$

This proves (SRO.29). For the actual smooth positive-time orbits it also
holds at $\theta=0$ by continuity from negative times. A stationary
subsolution is included by making it constant in $\theta$; its
space-time $L^2$ norm on an interval of length one is its spatial norm.
For a real solution, its absolute value is a subsolution by the convex
Kato calculation: for $\phi_\epsilon(u)=\sqrt{u^2+\epsilon^2}$ the
potential residual is $V_r(\phi_\epsilon'(u)u-\phi_\epsilon(u))\le0$
and the gradient residual is nonpositive. Positive parts obey the same
limit inequality. This records the precise sign used below.

We now apply this quantified intermediate to the original $h$.
For $\tau\ge T+4$, $r=e^{-\tau}$ and $y=l\omega\in D$,

$$
r f_h(ry)=l^{-1}c_h(\rho+\tau-\log l)e_0(\omega)
                            +l^{-1}Z_h(\tau-\log l,\omega).
\tag{SRO.35}
$$

Polar integration of (SRO.19) gives

$$
\|l^{-1}Z_h(\tau-\log l,\omega)\|_{L^2(D)}
 \le B_he^{-\tau/8}
          \left(\int_{3/4}^{5/4}l^{5/4}dl\right)^{1/2}
 \le2B_he^{-\tau/8}.
\tag{SRO.36}
$$

The angular profile satisfies $e_0\ge\sqrt3/\pi^2>1/16$.
If $\tau\ge2(R_\rho+1)$, then $|\log l|<1$ and the affine term
in (SRO.35) is at least $c_-\tau/40$ everywhere on $D$.
Put $k=c_-\tau/128$. The positive part
$w_{r,k}=(k-r f_h(r\,\cdot))_+$ has $L^2(D)$ norm at most
$2B_he^{-\tau/8}$. Crucially it is a stationary subsolution for
the same operator: before truncation,

$$
[-\operatorname{div}(A_r\nabla)-V_r](k-r f_h(r\,\cdot))
=-V_rk\le0.
\tag{SRO.37}
$$

This compares with a constant, not with an equation falsely assigned to
the nonsmooth angular model. Apply (SRO.29) centered at every
$\omega\in S^3$ and bound its local norm by the full $D$ norm.
Choose an integer

$$
\tau_0\ge\max(T+4,1,2(R_\rho+1)),\qquad
2C_{\rm loc}B_he^{-\tau_0/8}<c_-\tau_0/256.
\tag{SRO.38}
$$

The strict inequality can be certified by an upper exponential enclosure
of error at most $2^{-n}$ at the candidate integer $n$.
Testing successive sufficiently large integers terminates because
$(e^{-n/8}+2^{-n})/n\to0$. The same inequality holds for every
$\tau\ge\tau_0$, since $e^{-\tau/8}/\tau$ decreases.
Then $w_{r,k}(\omega)<c_-\tau/256=k/2$, so
$r f_h(r\omega)\ge c_-\tau/256$. This proves (SRO.20) with
$L_h=c_-/256$, uniformly over every radius and angle. $\square$

## 4. Relative source order at the original deterministic time

**Theorem 4.1 (a coefficient-computed uniform relative remainder).**
From the original $a,\eta,d$ names alone and the services of Definition
1.2 one computes positive rationals $r_*,D_1,D_2$ such that the actual
smooth punctured representative satisfies

$$
\left|g_d(\Phi_\kappa(R\omega))-s_d\right|
 \le D_1R^2+D_2\frac{R^{1/8}}{\log(1/R)}
\quad(0<R\le r_*,\ \omega\in S^3).
\tag{SRO.39}
$$

The scalar $s_d=\operatorname{tr}g_d$ already has its exact name from
(SRO.3). This is an all-angle estimate on the entire shrinking source
neighborhood, stronger than an angular or ball mean-square estimate.
It does not assert a global maximum at $e$.

Proof. By [D, (12.4)–(12.8)], compute

$$
\begin{gathered}
n=h-(F+1)^{-1}h,\qquad D=\langle h,n\rangle=d_1>0,\qquad z=n/D,\\
v_t=(H+1)e^{-tH}z,\qquad \|z\|_2\le1/\ell
\quad\hbox{for a computed rational }0<\ell<D.
\end{gathered}
\tag{SRO.40}
$$

The symbol $z$ here is a raw Hilbert vector, not the third group
coordinate. Refinement to $\ell>0$ terminates by the supplied strict
positivity. This rank-one/source identity is for the full $A=\rho C$
endpoint; the occurrence of a Friedrichs resolvent in its construction
does not change that endpoint.

Choose rational $0<d_-\le d$, put $t_0=d_-/4$, and define rational
bounds

$$
Q=\frac{1+t_0^{-1}}\ell,\qquad
J=\frac{t_0^{-1}+4t_0^{-2}}\ell,\qquad
S=Q^2,\qquad L_s=QJ.
\tag{SRO.41}
$$

Nonnegative spectral calculus gives $\|v_t\|_2\le Q$ and
$\|Hv_t\|_2\le J$ for every $t\ge t_0$: use
$\sup_{\lambda\ge0}\lambda^j e^{-t\lambda}\le(j/t_0)^j$ for
$j=1,2$. Smoothing also puts these exact vectors in every $D(H^j)$.
For $d/2\le t\le d$, both $t$ and $t/2$ are at least $t_0$.
Hence $0\le s_t=\|v_{t/2}\|_2^2\le S$ and

$$
s_t'=-\langle v_{t/2},Hv_{t/2}\rangle,\qquad
|s_t'|\le L_s.
\tag{SRO.42}
$$

This differentiates positive-time Hilbert vectors. The factor $1/2$
from the time argument cancels the factor $2$ from the squared norm;
no numerical source derivative or pointwise evaluation is assumed.

Set $y_t=v_t-s_t h$. Since $g_t\in D(K)$, the exact full-domain
trace correspondence gives

$$
C(v_t)=c_hs_t,\qquad A(v_t)=\rho c_hs_t,\qquad
A(y_t)=C(y_t)=0,\qquad S_{\min}^*y_t=Hv_t.
\tag{SRO.43}
$$

Thus Theorem 2.1 gives, simultaneously throughout this time interval,

$$
\|\chi H_{y_t}\|_X\le B_0:=C_0(Q+S+J),\qquad
\|H_{y_t}(\nu)\|_2\le B_0e^{-\nu/8}\quad(\nu\ge T+3).
\tag{SRO.44}
$$

This cancellation uses both coefficients of the actual full endpoint.
It is not a statement that $v_t$ itself has Friedrichs boundary data.

Fix $\alpha=s_d$ and $u_t=v_t-\alpha h$. It is an actual heat orbit
difference because $Hh=0$. Its cylinder expansion, using (SRO.19), is

$$
H_{u_t}=(s_t-\alpha)c_h(\rho+\nu)e_0+Z_t,
\qquad \|Z_t(\nu)\|_2\le B_u e^{-\nu/8},\qquad
B_u=B_0+2SB_h.
\tag{SRO.45}
$$

Indeed $u_t=y_t+(s_t-\alpha)h$, $|s_t-\alpha|\le2S$, and
the two remainders in this decomposition satisfy (SRO.44), (SRO.19).
The bound is uniform in $t\in[d/2,d]$ and $\nu\ge T+3$.

Choose a positive rational

$$
r_*<\min(e^{-\tau_0},\sqrt{a_-d_-/2},1/2).
\tag{SRO.46}
$$

The positive right side has a total interval name, so successive positive
dyadics and interval refinements give such an $r_*$. For $0<r\le r_*$,
put $\tau=\log(1/r)$ and use the proof coordinates

$$
\theta=\frac{a(t-d)}{r^2}\in[-1,0],\qquad
t=d+\frac{r^2}{a}\theta,\qquad
U_r(\theta,y)=r f_{u_t}(ry).
\tag{SRO.47}
$$

Condition (SRO.46) ensures $t\ge d/2>0$. The scaled equation of the
actual original orbit is exactly

$$
\partial_\theta U_r-\operatorname{div}(A_r\nabla U_r)-V_rU_r=0
\quad\hbox{on }(-1,0)\times D.
\tag{SRO.48}
$$

To check the forcing and clock factors, the unscaled chart equation is
$\partial_t f=a\operatorname{div}(A_\kappa\nabla f)
                 +16a\kappa\Gamma(\Phi_\kappa Z)f$.
The derivative of (SRO.47) is $r^3/a$ times this equation, so its
potential coefficient is exactly $16\kappa r^2\Gamma(\Phi_\kappa(ry))$.
This is (SRO.21), not an additional source or a change of physical time.

For $y=l\omega\in D$, (SRO.45) reads

$$
U_r(\theta,l\omega)
 =l^{-1}(s_t-\alpha)c_h(\rho+\tau-\log l)e_0(\omega)
                        +l^{-1}Z_t(\tau-\log l,\omega).
\tag{SRO.49}
$$

Since $\tau\ge\tau_0\ge2(R_\rho+1)$ and $\|e_0\|_2=1$,
the $L^2(D)$ norm of $l^{-1}(\rho+\tau-\log l)e_0$ is at most
$4\tau$. The remainder has norm at most $2B_ur^{1/8}$ by exactly
the polar integration in (SRO.36). Also (SRO.42), in the original clock,
gives $|s_t-\alpha|\le L_s r^2/a_-$. Therefore, uniformly over the
entire interval of length one in $\theta$,

$$
\|U_r\|_{L^2((-1,0)\times D)}
 \le\frac{4c_+L_s}{a_-}r^2\tau+2B_ur^{1/8}.
\tag{SRO.50}
$$

The actual heat orbit is smooth on these compact punctured cylinders:
spectral smoothing gives all powers of $H$, and repeated local elliptic
regularity for the original smooth coefficients gives the spatial and
positive-time representatives. Apply (SRO.29) to $|U_r|$ in the ball
centered at each $\omega$. Continuity reaches its time endpoint $0$.
Use the denominator floor (SRO.20) to divide at that same point:

$$
\begin{aligned}
\left|g_d(\Phi_\kappa(r\omega))-\alpha\right|
 &=\frac{|r f_{v_d-\alpha h}(r\omega)|}{r f_h(r\omega)}\\
 &\le\frac{4C_{\rm loc}c_+L_s}{a_-L_h}r^2
       +\frac{2C_{\rm loc}B_u}{L_h}\frac{r^{1/8}}\tau.
\end{aligned}
\tag{SRO.51}
$$

The factors $\sqrt\kappa$ and $r$ cancel in this ratio. The source
normalization remains $C(w_*)=1$ and $m=h^2\mu$ throughout.
Take the rational constants
$D_1=4C_{\rm loc}c_+L_s/(a_-L_h)$ and
$D_2=2C_{\rm loc}B_u/L_h$, increasing either by a positive rational
if needed. Formula (SRO.51) proves (SRO.39). $\square$

## 5. Finite upper certificates on shrinking original neighborhoods

**Theorem 5.1 (sound acceptance and local cofinality at the source trace).**
For every positive rational $\epsilon$, the original names compute a
positive rational $\delta$ and rational $U$ with

$$
s_d\le U<s_d+\epsilon,\qquad
g_d\le U\quad m\hbox{-a.e. on }[-\delta,\delta]^4.
\tag{SRO.52}
$$

Equivalently $v_d\le Uh$ $\mu$-almost everywhere on this original
coordinate box. More generally, for every rational $U>s_d$, a fair
finite-certificate search accepts that conclusion on some positive
source neighborhood. This is local cofinality at $s_d$, not global
cofinality at $N_d=\|g_d\|_\infty$.

Proof. First compute the bounds in (SRO.6), (SRO.8), (SRO.18),
(SRO.24), (SRO.28), (SRO.38), (SRO.41), (SRO.44)–(SRO.46) and
(SRO.51), with their strict outward enclosures. A finite packet contains
the relevant name queries and certified errors, the positive rational
brackets, the integers $T,\tau_0$, and these rational bounds. Theorems
2.1, 3.1 and 4.1 show that every packet satisfying those finite
inequalities certifies the corresponding mathematical bounds. Its
acceptance presumes the total input names and analytic hypotheses of
Definition 1.1; it is not a test of arbitrary proposed input functions.

The named $v_{d/2}$ computes $s_d=\|v_{d/2}\|_2^2$. If $V$ has raw
norm error $e_v$ and $\|v_{d/2}\|_2\le Q$, the scalar error before
finite norm rounding is at most $(2Q+e_v)e_v$. Thus a finite query and
rounding budget gives a rational upper enclosure
$s_d\le A<s_d+\epsilon/4$. One can ensure its excess is strictly
positive by increasing the upper endpoint within this budget.

Search integers $k$ with $r=2^{-8k}<r_*$ and

$$
D_1\,2^{-16k}+D_2\,2^{-k}<\epsilon/4.
\tag{SRO.53}
$$

These are decidable rational comparisons, and a sufficiently large $k$
passes. Since $\log(1/R)\ge1$ for $R\le r_*$, (SRO.39) implies
$|g_d-s_d|<\epsilon/4$ at every smooth punctured point with $R\le r$.
Choose a positive rational dyadic $\delta$ satisfying

$$
3\delta^2+\frac{(\delta+\delta^2/2)^2}{\kappa_-^2}<r^2.
\tag{SRO.54}
$$

This is again a rational strict search with termination as
$\delta\downarrow0$. For a point in the original box,
$|w-xy/2|\le\delta+\delta^2/2$; hence (SRO.54) implies
$|\Phi_\kappa^{-1}p|<r$. Return $U=A+\epsilon/2$.
Then $s_d\le U<s_d+3\epsilon/4$ and the order inequality follows.
The box contains an open neighborhood of the original $e$.

For the general rational conclusion $U>s_d$, dovetail integers $k$,
upper trace enclosures $A_n$ of errors tending to zero, and rational
boxes satisfying (SRO.54). Accept exactly when $2^{-8k}<r_*$ and

$$
A_n+D_1\,2^{-16k}+D_2\,2^{-k}<U.
\tag{SRO.55}
$$

Each test is finite. Soundness follows from (SRO.39).
The strict gap $U-s_d>0$ allows both the trace enclosure error and the
radius error to be less than one third of that gap, so fair search
eventually accepts. No equality test for $U=s_d$ is required.

The estimate covers every $0<R\le r$ and every angle, not a sampled
sphere or an annulus omitting a smaller source region. The value at $e$
in the full-form quasi-continuous representative is $s_d$, by (SRO.3).
The smooth quotient converges uniformly to this same value by (SRO.39).
Nevertheless an arbitrary permitted Borel repair need not take this
point value. Since $m$ and $\mu$ have the same null sets and neither has
an atom at $e$, (SRO.52) holds for every such repair as an a.e. statement.
No capacity-zero exception at the nonpolar source is asserted.

All searches use finite rational inequalities and elementary real
enclosures, supplemented by the already constructed global names.
The numerical lower brackets for $a,\kappa,c_h,d,D$ terminate by their
proved strict positivity. The cylinder contraction search is the one
in [D, §11]. The only additional integer/exponential search is
(SRO.38), whose termination was proved there. These facts, followed by
(SRO.53)–(SRO.54), give a total finite-precision construction for each
$\epsilon$. No parameter-uniform or practical resource bound is
asserted. $\square$

## 6. Relation to sharp calibration and other recovery routes

**Definition 6.1 (the unchanged global consumer).** Retain exactly

$$
\begin{gathered}
N_d=\|g_d\|_{L^\infty(m)},\qquad M=1+N_d,\qquad c=1/(4M),\\
P=T_d,\qquad f_3=cg_d,\qquad f_B=1/4,\qquad
f_0=f_1=(3/4-f_3)/2,\qquad\mathcal L=\{0,1,3,B\}.
\end{gathered}
\tag{SRO.56}
$$

The process starts at $e$, its first passive read is at $2d$ and every
following gap is $d$. Read noise is fresh conditionally on the same
undisturbed path. The coefficient names are mathematical model inputs,
not passive records or added coordinate observations.

The exact global upper problem is [D, (12.31)]: finite sound certificates
$v_d\le Uh$ on all $G$, cofinal at $N_d$. Theorem 5.1 pays the source
factor of a possible regional construction. Indeed $s_d\le N_d$ by
[D, Proposition 12.7], so every $U>N_d$ eventually passes the source
test (SRO.55). It still requires independently constructed numerical
order certificates on the remaining punctured compact region and at
infinity, with overlapping coverage of their interfaces. The result
does not construct those regional producers or their global assembly.

[D, Theorem 14.2] already gives a computed Gaussian raw $L^2$ tail for
$v_t$. [D, Theorem 14.3 and Corollary 14.4] give qualitative exterior
order decay and compact localization. Their pointwise constants and
exterior radius are not supplied as numerical names. They remain within
that exact scope here. A raw norm tail or a small positive defect norm
cannot certify zero measure of an exceedance region.

Direct source maximality, if proved for this very family, would give the
more economical identity $N_d=s_d$. Formula (SRO.39) is compatible with
an off-source maximum and proves no such identity. A global
order/supersolution argument or a sharp bound for the trace functional
$u\mapsto\operatorname{tr}(T_du)$ on the $L^1(m)$ unit ball would also
serve the consumer; a bound on an $L^2(m)$ unit ball alone does not.
The positive simple-resolvent obstruction in [D, §13] retains its stated
comparison class and does not preclude these other routes.

Thus the source-relative relation here is a computable approach of a
spatial germ to its actual boundary trace at a specified continuation
time. It identifies that trace with the already computed source norm
memory $\|v_{d/2}\|_2^2$ and gives the quantitative local order needed
to use that relation. It is not an exact global normalization, original
word evaluator, finite-record confidence rule or a complete recovery of
space, time, boundary and memory. Replacing $M$ by any loose proof
constant changes (SRO.56) and is not licensed by these results.

## 7. Mathematical antecedents and the precise additional relation

**Definition 7.1 (source correspondence and literature scope).** The
source-specific statements (SRO.7), (SRO.20), (SRO.39) and (SRO.52)
are `repo-derived` ordinary mathematical deductions conditional on
Definition 1.1. Their quantitative graph/annular composition is the
additional relation; generic Sobolev, Bessel form bounds, spectral
smoothing and power iteration are mature intermediate tools.

| Mathematical source | Correspondence and exact scope |
| --- | --- |
| [D, §§10–12](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md) | Original unit Green bound, actual graph names and their weighted remainder norms, full-resolvent/source formula, numerical $h,\rho,c_h,D$, deterministic-time $v_t$ and $s_t$. These are reused, not reconstructed as a new source. |
| [E, §§109–112](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md) | Entire complex maximal expansion, Green pairing, original selector and forcing factor $a^{-1}R^3f_f$. Qualitative membership supplies the legal domain for the fixed-level numerical inverse, not a numerical remainder size. |
| [S, §§115–117, 130–133](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md) | Positive normalized $h$, full conservative form, actual nonpolar trace and source-start law. The exact annular marginal and Stummel modulus of §130 supply (SRO.23); its existential Harnack constant is not an input. No auxiliary extended weight replaces $m$. |
| M. Shubin, [Essential self-adjointness for semi-bounded magnetic Schrödinger operators on non-compact manifolds](https://arxiv.org/html/math/0007019v1), Lemma 5.1 and (5.3) | Inhomogeneous local regularity and cutoff identity on punctured collars, with zero magnetic form, the actual smooth elliptic symbol and raw smooth measure. Its complete-manifold essential self-adjointness theorem is not applied across $e$. |
| D. G. Aronson, [Harnack, Hölder, Gauss and Widder: Serrin's parabolic legacy](https://arxiv.org/html/1611.09417v1), weak equation and fundamental power inequality (7), and [Non-negative solutions of linear parabolic equations](https://www.numdam.org/item/ASNSP_1968_3_22_4_607_0.pdf), Ann. Scuola Norm. Sup. Pisa 22 (1968), 607–694, Theorem B | Established local power-test and iteration method. The equation here has time coefficient one only in the unitary raw annular chart and proof time (SRO.47). No unspecified structural constant or weighted-time theorem is imported; (SRO.25)–(SRO.34) provide the finite bounds used here. |
| [D, §14](RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md) | Computed norm tail and qualitative exterior/compact results, with their explicit numerical boundary unchanged. They do not provide a numerical all-source order modulus. |

The existing D5 `DysonPhillipsPerturbation` result, including its private
`Input` and `native` bridge, assumes an already supplied strongly
continuous semigroup and a bounded perturbation. It does not construct
this singular endpoint, source trace or order bound. D5
`SchwartzCutoffGraph.scaled_cutoff_graph` concerns Schwartz differential
cutoffs and does not supply the maximal source-tail estimate.
Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Analysis/FunctionalSpaces/SobolevInequality`, supplies the mature
Gagliardo–Nirenberg–Sobolev method, including
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`. Its ordinary Euclidean
hypotheses are used only inside the annular argument. None of these
formal declarations is asserted to verify the new original-source
composition.

A. Burchard and Á. D. Martínez,
[On monotonicity of heat kernels: a new example and counterexamples](https://arxiv.org/html/2502.08212v1),
Theorem 2.2, concerns compact smooth manifolds with a simple first
positive eigenvalue. It is not a counterexample in (SRO.1)–(SRO.2).
Neither that reference nor a failure to find a sharp source-maximum
theorem implies noncomputability or impossibility for the present family.
No worldwide priority or new kernel-verification assertion is made.

## 追加锚（本行以下为增补区）

## 8. Finite certificates on an arbitrary punctured rational compact region

**Definition 8.1 (the regional problem and its inputs).** Retain Definitions
1.1–1.2 in full, including the original unit-source Green field, selector,
positive normalized $h$, measure $m=h^2\mu$, entire complex endpoint
$A=\rho C$, and the distinction $H\ne F$. Write $\mathcal K$ for a
spatial region, to distinguish it from the operator $K=J_h^{-1}HJ_h$.
The region is specified as a finite union of nondegenerate closed boxes
with rational endpoints in the original $(x,y,z,w)$ coordinates, and
$e\notin\mathcal K$. The empty union is allowed. Put

$$
G_{\mathcal K}=\sup_{p\in\mathcal K}\frac{v_d(p)}{h(p)}
\quad(\mathcal K\ne\varnothing),
\tag{SRO.57}
$$

where the quotient is its smooth punctured representative. It is finite
by the admitted punctured regularity and strict positivity of $h$.
Neither $G_{\mathcal K}$ nor a compact minimum or modulus is an input.
The numerical access is exactly that of Definition 1.2: total interval
names for the original finite positive $a,\eta,d$, and the already
constructed raw $L^2(\mu)$ resolvent, zero-state and source services of
[D, §§11–12]. In particular a query at any positive time with a name
returns a finite rational complex box step approximating the actual
$v_t$, with a certified global norm error. Acceptance below is relative
to legitimate replies from those services, just as in Theorem 5.1;
it does not authenticate an arbitrary proposed name.

**Theorem 8.2 (sound and strictly cofinal punctured-compact packets).**
For every input of Definition 8.1 and every rational $U$, there is a
uniformly described search through finite rational packets such that:

1. Each individual acceptance test terminates after finitely many
   legitimate name answers and finite rational operations.
2. Every accepted packet proves $v_d\le Uh$ $\mu$-almost everywhere on
   $\mathcal K$. For nonempty $\mathcal K$, the construction actually
   proves $v_d<Uh$ everywhere there in the smooth representatives.
3. If $\mathcal K\ne\varnothing$ and $U>G_{\mathcal K}$, fair search
   eventually accepts. The empty union has an immediate certificate.

No termination at equality, common positive gap, or parameter-uniform
time bound is asserted. The packets use no pointwise heat evaluator,
spatial modulus, numerical Harnack constant, positive anchor, or
numerical compact minimum. Every additional numerical bound needed by
the test is extracted below from the original names. The proof is given
in §§9–11; its method is to certify a small *shifted* positive-part
defect on a slightly larger space-time cylinder. The shift and a
computed local estimate turn smallness into exact order.

This is the punctured-compact factor named in §6 for the original
[D, Definition 12.8, (12.31)]. It does not replace or reprove Theorem 5.1,
and does not supply an exterior certificate or global assembly.

## 9. Rational local geometry and the original-source time bound

**Lemma 9.1 (explicit bounds from a punctured rational cube).** Refine the
coefficient names to rational brackets
$0<a_-\le a\le a_+$ and $0<\eta_-\le\eta\le\eta_+$.
Let

$$
B=c+[-r,r]^4,\qquad I=c+[-r/2,r/2]^4,
\qquad c\in\mathbb Q^4,\quad r\in\mathbb Q_{>0},\quad e\notin B.
\tag{SRO.58}
$$

Choose a coordinate $j$ with $b=|c_j|-r>0$, and put

$$
\begin{gathered}
X_B=|c_x|+r,\qquad
q_B=\begin{cases}
b^{-4},&j=x,y,\text{ or }z,\\
25/(16b^2),&j=w,
\end{cases}\\
\lambda_B^0=\frac{\min(a_-,\eta_-)}{2(1+X_B^2)},\qquad
\Lambda_B^0=2(a_++\eta_+)(1+X_B^2),\qquad
\nu_B^0=512(a_++\eta_+)(1+q_B).
\end{gathered}
\tag{SRO.59}
$$

These are finite positive rationals. In the original coordinates the
principal matrix $\mathsf A$ and potential $V$ satisfy on $B$

$$
\begin{gathered}
q^{\mathsf T}\mathsf A(p)q
 =a\big(q_x^2+(q_y+xq_w)^2+q_z^2\big)+\eta q_w^2,\qquad
V(p)=16\sqrt{a\eta}\,\Gamma(p),\\
\lambda_B^0\mathbf1\le\mathsf A(p)\le\Lambda_B^0\mathbf1,
\qquad 0<V(p)\le\nu_B^0.
\end{gathered}
\tag{SRO.60}
$$

Proof. The original fields have zero Haar divergence, so their quadratic
form gives precisely $-\operatorname{div}(\mathsf A\nabla)-V$ off $e$.
The shear $q\mapsto(q_x,q_y+xq_w,q_z,q_w)$ and its inverse have squared
operator norms at most $2(1+X_B^2)$. Applying the coefficient brackets
proves both matrix inequalities.

If $j$ is a noncentral coordinate, $\varrho^4\ge b^4$. If $j=w$, write
$s=w-xy/2$ and use

$$
|w|\le |s|+|xy|/2
 \le\varrho^2+|(x,y,z)|^2/4\le5\varrho^2/4.
\tag{SRO.61}
$$

Thus $\varrho^{-4}\le q_B$ in both cases. The elementary inequality
$\varrho^{-3}\le1+\varrho^{-4}$ and the original bound
$\Gamma\le32\varrho^{-3}$ give (SRO.60), since
$\sqrt{a\eta}\le a_++\eta_+$. A closed coordinate cube avoids zero
exactly when at least one coordinate has $|c_j|>r$, so the separation
choice is a finite rational test. No Green-field evaluation or
coefficient derivative is required. $\square$

**Definition 9.2 (finite coverage evidence).** A geometric packet has
finitely many pairs $(B_i,I_i)$ of the form (SRO.58), each avoiding $e$.
For every specified constituent box of $\mathcal K$, include a finite
rational grid partition of that box. Its coordinate breakpoint lists
start and end at the given endpoints, are strictly increasing, and each
closed grid cell must be contained in some $I_i$. Containment is checked
by its eight endpoint inequalities in dimension four. These finite
checks imply $\mathcal K\subseteq\bigcup_i I_i$, including all faces.
They require no decision about membership in a named real set.

Such evidence exists whenever the interiors of the $I_i$ cover
$\mathcal K$: the finite open cover of each compact constituent box
has a positive Lebesgue number, so a sufficiently fine rational grid
has every cell inside one of those interiors. This fact establishes
completeness of the finite language; a Lebesgue number is not requested
by the search. Small rational cubes whose half-size interiors cover
any prescribed point can be chosen inside any open neighborhood of
that point. Compactness therefore gives a finite such cover inside
any punctured open neighborhood of $\mathcal K$.

**Lemma 9.3 (a numerical time-interpolation bound for this source).**
Use the existing scalar name of $D$ in (SRO.40) to find a rational
$0<\ell<D$, and the original clock name to find $0<d_-\le d$.
Set

$$
t_0=d_-/4,\qquad
J=\frac{t_0^{-1}+4t_0^{-2}}{\ell}.
\tag{SRO.62}
$$

For $s,t\ge t_0$, the actual full-endpoint source vectors obey

$$
\|v_t-v_s\|_{L^2(\mu)}\le J|t-s|.
\tag{SRO.63}
$$

Proof. Reuse (SRO.40)–(SRO.41), not a new source construction:
$v_t=(H+1)e^{-tH}z$ and $\|Hv_t\|_2\le J$ for $t\ge t_0$.
Positive-time Hilbert differentiability gives
$\partial_t v_t=-Hv_t$; integration proves (SRO.63).
The searches for the positive lower brackets terminate because the
named $D,d$ are strictly positive. The spectral bound uses the
nonnegative full $H$; the auxiliary $(F+1)^{-1}$ in $z$ does not
substitute an $F$ heat orbit. $\square$

## 10. A numerical cylinder estimate and the shifted defect

**Lemma 10.1 (an explicit four-dimensional cylinder constant).** On
$Q=(-1,1)^4\times(-1,0)$ let $Z\ge0$ be a smooth subsolution of

$$
\partial_\theta Z-\operatorname{div}(\mathsf B\nabla Z)-WZ\le0,
\quad \lambda\mathbf1\le\mathsf B\le\Lambda\mathbf1,
\quad 0\le W\le\nu,
\tag{SRO.64}
$$

where $\mathsf B$ is symmetric, $\lambda>0$, and the coefficients are
smooth locally. Put

$$
L=1+\lambda^{-1}+\Lambda+\nu,\qquad C=2^{42}L^3.
\tag{SRO.65}
$$

Then

$$
\operatorname{ess\,sup}_{(-1/2,1/2)^4\times(-1/2,0)}Z
 \le C\|Z\|_{L^2(Q)}.
\tag{SRO.66}
$$

The same estimate holds for locally uniform, $L^2(Q)$ convergent limits
of such subsolutions. If the limit is continuous on the closed smaller
spatial cube at time zero, (SRO.66) holds there too. The constant
depends only on the displayed bounds, not on coefficient derivatives.

Proof. This is a power-iteration intermediate with all numerical costs
specified. For $p\ge2$, write $z=Z^{p/2}$, $f=\chi z$ and
$Y=\int\chi^2z^2$, with $0\le\chi\le1$ compactly supported in space
and vanishing at the earlier time. The test $p\chi^2Z^{p-1}$ gives

$$
\frac{dY}{d\theta}+\frac\lambda2\int|\nabla f|^2
 \le\int\big(2|\chi_\theta|+8\Lambda|\nabla\chi|^2+p\nu\big)Z^p.
\tag{SRO.67}
$$

Indeed the initial diffusion coefficient is $4(p-1)/p\ge2$ in
the $\mathsf B$ metric. Estimate its cross term by
$4ab\le a^2+4b^2$, leaving at least one copy of
$\chi^2|\nabla z|_{\mathsf B}^2$. The inequality
$|\nabla(\chi z)|_{\mathsf B}^2
 \le2\chi^2|\nabla z|_{\mathsf B}^2+2z^2|\nabla\chi|_{\mathsf B}^2$
then costs at most a further $\Lambda|\nabla\chi|^2z^2$.
The displayed $8\Lambda$ bounds the resulting $5\Lambda$.
The time term uses $|2\chi\chi_\theta|\le2|\chi_\theta|$.
One can first use $Z+\epsilon>0$: its operator residual is no larger
than that of $Z$, because $W\ge0$. Letting $\epsilon\downarrow0$
justifies the power test at zeros.

Take

$$
\begin{gathered}
p_j=2(3/2)^j,\qquad R_j=S_j=1/2+2^{-j-1},\\
Q_j=(-R_j,R_j)^4\times(-S_j,0).
\end{gathered}
\tag{SRO.68}
$$

Product cutoffs supported in $Q_j$, equal to one on $Q_{j+1}$, can
have $|\nabla\chi_j|^2\le2^{10}4^j$ and
$|\partial_\theta\chi_j|\le2^6 4^j$. For example each coordinate
transition has width $2^{-j-2}$ and slope at most twice its reciprocal;
the time transition has the same width. Piecewise smooth cutoffs are
valid by approximation. The right-hand coefficient of (SRO.67) is at
most $2^{14}Lp_j4^j$. Integrating from the earlier zero-cutoff time,
and using $1+2/\lambda\le3L$, gives

$$
\sup_\theta\int f_j^2+\iint|\nabla f_j|^2
 \le H_j\iint_{Q_j} Z^{p_j},\qquad
H_j=2^{16}L^2p_j4^j.
\tag{SRO.69}
$$

Reuse the ordinary compact-support Sobolev inequality
$\|f\|_4^2\le64\int|\nabla f|^2$ established in the proof of
Theorem 3.1. Spatial Hölder followed by time integration yields

$$
\begin{gathered}
\iint|f_j|^3
 \le64\left(\sup_\theta\int f_j^2+\iint|\nabla f_j|^2\right)^{3/2},\\
\|Z\|_{p_{j+1},Q_{j+1}}
 \le64^{1/p_{j+1}}H_j^{1/p_j}\|Z\|_{p_j,Q_j}.
\end{gathered}
\tag{SRO.70}
$$

Here all norms and integrals are ordinary unweighted Euclidean ones.
The sums $\sum_j1/p_j=3/2$, $\sum_jj/p_j=3$ and
$\sum_j1/p_{j+1}=1$ bound the infinite product by

$$
64\,2^{24}L^3\,2^{3/2}(3/2)^3\,4^3<2^{40}L^3<C.
\tag{SRO.71}
$$

For the strict inequality it suffices to use $2^{3/2}<4$ and
$(3/2)^3<4$. On the intersection cylinder the uniform bounds for
$p_j\to\infty$ imply the essential-supremum bound: any positive-measure
set exceeding it would contradict those bounds as $j\to\infty$.
Limits of subsolutions preserve (SRO.66) by the stated convergence.
Continuity and approach from the interior reach the closed spatial cube
and final time. This proves the lemma without importing an unspecified
local boundedness or Harnack constant. $\square$

**Lemma 10.2 (the actual shifted positive part is admissible).** On any
punctured positive-time cylinder, set $u_t=v_t-Uh$ for a fixed real $U$.
For every constant $k>0$, $(u_t+k)_+$ is a continuous subsolution to
which Lemma 10.1 applies after scaling, with the actual principal
matrix and the actual positive $V$.

Proof. The source-specific equations, already used in Theorem 4.1
and [D, §14], are

$$
\operatorname{div}(\mathsf A\nabla h)+Vh=0,\qquad
\partial_t v_t=\operatorname{div}(\mathsf A\nabla v_t)+Vv_t.
\tag{SRO.72}
$$

They hold in smooth representatives on every such cylinder. For
$\mathcal P=\partial_t-\operatorname{div}(\mathsf A\nabla)-V$,
one has $\mathcal Pu=0$ and $\mathcal P(u+k)=-Vk\le0$.
To justify the truncation, use
$\phi_\epsilon(s)=(s+\sqrt{s^2+\epsilon^2})/2$.
Its first derivative is nonnegative, its second derivative is
nonnegative, and
$s\phi_\epsilon'(s)-\phi_\epsilon(s)
 =-\epsilon^2/(2\sqrt{s^2+\epsilon^2})\le0$. Consequently

$$
\mathcal P\phi_\epsilon(u+k)
 =-Vk\phi_\epsilon'(u+k)
   +V\big((u+k)\phi_\epsilon'(u+k)-\phi_\epsilon(u+k)\big)
   -\phi_\epsilon''(u+k)|\nabla u|_{\mathsf A}^2\le0.
\tag{SRO.73}
$$

The smooth nonnegative approximations converge uniformly to $(u+k)_+$,
and in $L^2$ on each bounded cylinder. Lemma 10.1 therefore applies.
The sign $-V$ in the original raw operator is essential to this
particular constant-shift test. No boundary condition on a cube is
imposed, and no killed heat solution is introduced. $\square$

## 11. The finite acceptance rule, soundness and terminating strict-slack search

**Definition 11.1 (the rational packet and its test).** For nonempty
$\mathcal K$, start with the terminating bracket extractions in §9.
A candidate packet contains the finite geometric evidence of
Definition 9.2, rational $k>0$ and $0<\tau<d_-/2$, positive integers
$N_i$, and finitely many precision requests and their legitimate raw
name replies. For each cube set

$$
\begin{gathered}
\lambda_i=(\tau/r_i^2)\lambda_{B_i}^0,\qquad
\Lambda_i=(\tau/r_i^2)\Lambda_{B_i}^0,\qquad
\nu_i=\tau\nu_{B_i}^0,\\
L_i=1+\lambda_i^{-1}+\Lambda_i+\nu_i,\qquad
C_i=2^{42}L_i^3,\\
t_{ij}=d-\tau+j\tau/N_i\quad(0\le j<N_i).
\end{gathered}
\tag{SRO.74}
$$

All constants in the first two lines are rational. Each $t_{ij}$ has
a total interval name computed from the same original $d$ name and
is at least $d-\tau>d/2>t_0$. Request finite raw box steps
$\widehat h,\widehat v_{ij}$ with certified global errors
$e_h,e_{ij}$, respectively, and put

$$
\begin{gathered}
\delta_i=\max_{0\le j<N_i}(e_{ij}+|U|e_h),\\
P_{ij}=1_{B_i}
 \big(\operatorname{Re}\widehat v_{ij}
           -U\operatorname{Re}\widehat h+k\big)_+,\\
F_i=\frac1{N_ir_i^4}\sum_{j=0}^{N_i-1}\int_{B_i}P_{ij}^2\,d\mu.
\end{gathered}
\tag{SRO.75}
$$

The constant $k$ is included on *all* of $B_i$, including the portion
outside both finite approximant supports. This is a rational box-step
calculation on a finite common partition, so $F_i$ is an exactly
computable nonnegative rational. Obtain a rational upper square-root
enclosure $b_i\ge\sqrt{F_i}$, and define

$$
E_i=b_i+\frac{\delta_i+J\tau/N_i}{r_i^2}.
\tag{SRO.76}
$$

An enclosure with arbitrarily small excess requires only finite rational
arithmetic: start with $[0,1+F_i]$, bisect by comparing the square of
its midpoint to $F_i$, and stop when the interval width is at most a
requested positive rational. The upper endpoint is $b_i$; the squared
endpoint inequalities are a finite certificate.

Accept exactly when the finite rational geometry and positive-bracket
conditions hold and

$$
C_iE_i<k\qquad\text{for every }i.
\tag{SRO.77}
$$

The packets range over rational centers, radii, grids, $k,\tau$,
integers $N_i$, requested name precisions and square-root enclosure
widths. After the initial bracket extractions, enumerate these finite
data fairly. Reject geometrically invalid candidates before querying
their source names. Every valid candidate has finitely many positive
named times, hence finitely many terminating calls to the original
services. No candidate waits for a test of an unknown real equality.
One may use the same $\widehat h$ throughout a packet.

**Proposition 11.2 (soundness with the exact Haar and clock factors).**
Every accepted packet of Definition 11.1 has the conclusions in
Theorem 8.2(2).

Proof. Work with $u_t=v_t-Uh$. For cube $i$, use only the proof
coordinates

$$
p=c_i+r_i y,\qquad t=d+\tau\theta,\qquad
Z_i(\theta,y)=(u_{d+\tau\theta}(c_i+r_i y)+k)_+.
\tag{SRO.78}
$$

Their domain is $(-1,1)^4\times(-1,0)$. The principal matrix is
$(\tau/r_i^2)\mathsf A(c_i+r_i y)$ and the potential is
$\tau V(c_i+r_i y)$, so (SRO.60) supplies exactly the constants
(SRO.74) in Lemma 10.1. The physical/source time is still $t$ with
the original units; $\theta$ is only a proof variable. The measure
factors are $d\mu=r_i^4dy$ and $dt=\tau d\theta$.

On the $j$th time bin
$[-1+j/N_i,-1+(j+1)/N_i)$, compare $Z_i$ with
$P_{ij}(c_i+r_i y)$. Real projection and positive part are contractions,
so at $t_{ij}$ their $L^2(B_i,d\mu)$ difference is at most
$e_{ij}+|U|e_h\le\delta_i$. At any later time in that bin,
(SRO.63) increases this bound by at most $J\tau/N_i$; the stationary
$h$ makes no time-interpolation contribution. After the spatial scaling,
the bound is $(\delta_i+J\tau/N_i)/r_i^2$. The normalized time interval
has length one. Thus Minkowski's inequality in space-time gives

$$
\begin{aligned}
\|Z_i\|_{L^2((-1,1)^4\times(-1,0))}
 &\le\left(\frac1{N_ir_i^4}
       \sum_j\int_{B_i}P_{ij}^2\,d\mu\right)^{1/2}
       +\frac{\delta_i+J\tau/N_i}{r_i^2}\\
 &\le E_i.
\end{aligned}
\tag{SRO.79}
$$

There is no unaccounted time Jacobian: averaging the physical interval
of length $\tau$ contributes $1/N_i$ per bin in $\theta$.
The shift is used only on the finite cube, so it need not be a global
$L^2$ vector.

Lemma 10.2 supplies the subsolution. Lemma 10.1, and continuity up to
the final time and the smaller spatial cube, now yield

$$
(v_d-Uh+k)_+(p)\le C_iE_i<k\quad(p\in I_i),\qquad
v_d(p)-Uh(p)\le C_iE_i-k<0.
\tag{SRO.80}
$$

Finite coverage proves the strict smooth-representative conclusion
on $\mathcal K$. The raw a.e. inequality follows. Since $h>0$ a.e.,
$m$ and $\mu$ have the same null sets; all permitted Borel repairs
preserve it. The source vector and $h$ were selected by the same full
endpoint before restricting to the local cylinders. No value of $h(e)$,
no arbitrary value assigned to $g_d(e)$, and no endpoint replacement
enters the proof. $\square$

**Proposition 11.3 (strict-slack completeness and finite extraction).**
If $U>G_{\mathcal K}$, the fair search in Definition 11.1 accepts
after finitely many name answers and finite rational operations.

Proof. On $\mathcal K$ the smooth function $Uh-v_d$ is strictly
positive, because $h>0$ and $U>v_d/h$ at every point. Compactness and
joint positive-time punctured continuity imply the existence of a
rational $k>0$, a bounded open neighborhood $O$ of $\mathcal K$ with
$e\notin\overline O$, and $\tau_*>0$ such that

$$
v_t(p)-Uh(p)\le-2k
\quad(p\in\overline O,\ d-\tau_*\le t\le d),
\qquad d-\tau_*>0.
\tag{SRO.81}
$$

For example first choose $k$ small enough that the margin on the compact
set is greater than $4k$, and then take a smaller compact collar and
time interval within that strict inequality. This is an existence
argument for a successful candidate; no value of that margin, collar,
continuity modulus or compact minimum is computed, queried, or used
in acceptance or soundness.

Choose finitely many rational $B_i\subset O$ whose half-size interiors
cover $\mathcal K$, and the rational grid evidence of Definition 9.2.
Choose a rational $0<\tau<\min(\tau_*,d_-/2)$. Fix this finite geometry,
$k$ and $\tau$. All resulting $C_i$ are explicit finite rationals.
On each entire outer cylinder the exact positive part
$(v_t-Uh+k)_+$ vanishes. At every sampled time, contraction therefore
implies $\|P_{ij}\|_{L^2(B_i)}\le\delta_i$, whence

$$
\sqrt{F_i}\le\delta_i/r_i^2,\qquad
E_i\le\frac{2\delta_i}{r_i^2}+\zeta_i
                 +\frac{J\tau}{N_ir_i^2},
\tag{SRO.82}
$$

if the square-root enclosure width is at most $\zeta_i>0$.
First choose $N_i$ so large that
$C_iJ\tau/(N_ir_i^2)<k/3$. Next request sufficiently small raw name
errors that $2C_i\delta_i/r_i^2<k/3$, and sufficiently small rational
$\zeta_i$ that $C_i\zeta_i<k/3$. There are finitely many cubes and
sample times; totality of the services gives all these replies after
finitely many queries. The rational bisections terminate. Equations
(SRO.82) then imply every test (SRO.77).

The rational geometry, shift, backward time, sample counts and precision
requests just chosen occur in the fair enumeration. Every preceding
candidate has a finite test, and the initial coefficient, $D$ and clock
bracket searches terminate by strict positivity. Thus a successful
packet is reached in finite time relative to the admitted total names.
This argument provides termination for each strict-slack input without
requiring a computable index for the successful geometry or a uniform
bound on the cost of a name reply. Together with Proposition 11.2 and
the empty-region convention it proves Theorem 8.2. $\square$

## 12. Numerical suppliers, attribution and the remaining global boundary

**Definition 12.1 (the precise additional relation and its source account).**
Theorem 8.2 and its construction are `repo-derived` ordinary paper
mathematics conditional on the unchanged analytic suppliers of
Definition 1.1. The source-specific increment is the sound shifted
defect test (SRO.75)–(SRO.80), its finite extraction from the actual
source names, and strict-slack termination on every specified
punctured rational compact union. The power method itself is a mature
intermediate, not a claim of new generic parabolic regularity.

| Required item | Supplier and exact use |
| --- | --- |
| Actual $h,H,F,D,z,v_t$ and finite box-step names | [D, §§11–12], especially Theorems 12.2–12.4 and (12.4)–(12.8), reused through Definitions 1.1–1.2 and (SRO.40). The source-start law is the deterministic-time full-$H$ law. |
| Punctured local equations and joint smoothness | The admitted local regularity and positive-time spectral smoothing, already applied in Theorem 4.1 and [D, §14]. They apply only away from $e$; qualitative continuity is used for completeness, not as a numerical service. |
| Rational ellipticity and bounded positive potential on every candidate cube | Lemma 9.1, derived from the original shear, positive coefficient brackets, rational separation from $e$, and $\Gamma\le32\varrho^{-3}$. |
| Numerical time interpolation | (SRO.40)–(SRO.41) and Lemma 9.3, with the extracted $\ell,d_-$; no time derivative evaluator is requested. |
| Numerical local $L^2$ to supremum constant | Lemma 10.1, including every cutoff, energy, Sobolev and product bound; $C_i$ is a rational expression in the displayed local bounds. |
| Finite defect enclosure and square-root bounds | Rational common box partitions, certified global raw errors, (SRO.63), and rational bisection; the exact scaling factors are in (SRO.79). |
| Positive denominator in the completeness proof | The existing strict positivity of the original $h$ on the punctured region. Neither a numerical floor nor a positive anchor is extracted or used by acceptance. |
| Source neighborhood | Theorems 4.1–5.1 are reused as their existing regional service; their trace-cofinal construction is not a new deliverable here. |

The local power-test antecedent is D. G. Aronson,
[*Harnack, Hölder, Gauss and Widder: Serrin's Parabolic Legacy*,
arXiv:1611.09417v1](https://arxiv.org/html/1611.09417v1), specifically
the weak formulation (6), fundamental power inequality referred to as
(7), and the discussion headed “LOCAL BOUNDEDNESS”. Its equation has
time coefficient one and divergence-form principal part; the present
local specialization has a uniformly elliptic matrix and bounded
zeroth-order term $WZ$. These satisfy the local structural requirements.
The pinned primary text supplies the method and attribution, not a
numerical value for its unspecified structural constants. Lemma 10.1
derives the actual constant needed here. No Gaussian or Harnack theorem
from that text is applied across the original singular source.

The punctured regularity antecedent already cited in §7 and [D] is
M. Shubin, [*Essential self-adjointness for semi-bounded magnetic
Schrödinger operators on non-compact manifolds*,
arXiv:math/0007019v1](https://arxiv.org/html/math/0007019v1), Lemma 5.1
and the local cutoff identity (5.3). The lemma assumes a locally
Lipschitz magnetic one-form and locally bounded scalar potential and
gives $W^{2,2}_{\rm loc}$ for maximal-domain vectors. The correspondence
here uses zero magnetic form, the actual smooth elliptic symbol and
smooth measure on punctured compact sets; repeated local regularity
is the existing smoothness supplier, not a new numerical estimate.
The complete-manifold essential-self-adjointness theorem is not used
to select or identify the endpoint at $e$. Both cited versioned primary
texts' relevant passages are the literature scope; no broader priority
or exhaustive literature-search assertion is made.

**Proposition 12.2 (regional scope and unresolved interfaces).** The new
packets supply the punctured-compact order producer left unpaid in §6.
They do not supply the exterior producer or the global cofinal
enumeration of [D, (12.31)]. In particular the following remain distinct:
the exterior numerical extraction identified in [D, §14], coverage
and compatibility of all regional interfaces, exact global $N_d$ and
$M=1+N_d$, and the optional source-maximum identity $N_d=s_d$.

Proof. Every accepted conclusion above has the finite specified region
$\mathcal K$ as its domain. Neither its geometry nor its proof includes
an unbounded region or a source-containing neighborhood. The existing
source service is Theorem 5.1; a remaining exterior service and a proof
that the selected regions cover all of $G$ are still needed for that
regional route. The qualitative exterior results and computed norm tail
of [D, §14] keep their stated numerical boundary. No global order
conclusion follows from the present finite-domain theorem alone.
$\square$

The original first read at $2d$, all gaps $d$, selector, emissions
(SRO.56), full source trace and allowed Borel repairs are unchanged.
The already supplied finite-observation consumers in the original-word
geometry volume, §§9–11, retain their capacity, confidence and finite-task
contracts and acquire no prerequisite involving exact $N_d$ from this
paper. This construction is a model-side computation from the admitted
names, not a new passive observation, physical operation, stationary
preparation, actual instrument, re-entry, joint/reference supplier,
autonomous factor, or complete quantum-origin result. The conclusions
are paper deductions; no Lean verification is asserted.

## 追加锚（本行以下为增补区）

## 13. A source-connected numerical denominator on the original group

**Definition 13.1 (fixed source and rational brackets).** Throughout
§§13–17 retain exactly Definitions 1.1–1.2 and 6.1. Thus the quantifiers
are every original finite $a,\eta,d>0$ with their original analytic
suppliers and total names. The Green field has $L\Gamma=\delta_e$,
$C(w_*)=1$, $h=w_*/\|w_*\|_2$, $m=h^2\mu$, and the entire complex
conservative endpoint is $D(H)=\{A=\rho C\}$, distinct from $F$.
The source vector is the actual $v_t=hg_t$ started at $e$, with the
full-form nonpolar trace (SRO.3). An auxiliary coordinate ball or
cylinder below is a region of proof for these same objects.

Use Theorem 3.1 to obtain its rational $L_h>0$ and integer $\tau_0$.
Refine the existing interval names to positive rational brackets

$$
\begin{gathered}
a_-\le a\le a_+,\qquad \eta_-\le\eta\le\eta_+,\qquad
\kappa_-\le\kappa=\sqrt{\eta/a}\le\kappa_+,\\
d_-\le d\le d_+,\qquad 0<D_-\le D,\qquad
D=\langle h,h-(F+1)^{-1}h\rangle .
\end{gathered}
\tag{SRO.83}
$$

The last scalar is exactly (SRO.40) and [D, (14.3)], not a differential
operator. Write $\mathbb B_r$ for the ordinary open Euclidean ball of
radius $r$ in the original four coordinates. Define the positive
rational numbers and positive integer

$$
\begin{gathered}
M_0=1+2/\kappa_-,\qquad
r_0=\min\left(\frac1{64},\frac{4^{-\tau_0}}{2M_0}\right),\qquad
m_0=\frac{L_h}{1+\kappa_+},\\
\lambda_-=\frac{\min(a_-,\eta_-)}3,\qquad
\Lambda_+=3\max(a_+,\eta_+),\qquad
k=\max\left(1,\left\lceil4\Lambda_+/\lambda_-\right\rceil\right),\\
c_*=m_0\,2^{-7(k+1)},\qquad C_*=\frac{32(k+1)}{r_0}.
\end{gathered}
\tag{SRO.84}
$$

No value of $h(e)$ is introduced by these definitions.

**Theorem 13.2 (a rational exponential floor for this normalized
zero state).** The constants in (SRO.84) satisfy

$$
h(p)\ge m_0\quad(0<|p|\le r_0),\qquad
h(p)\ge c_*\exp(-C_*\varrho(p))\quad(p\ne e).
\tag{SRO.85}
$$

They are extracted from the original names and the existing source
floor, without a numerical Harnack constant or compact minimum.

Proof. For $0<|p|\le r_0$, with $p=(x,y,z,w)$, set
$s=w-xy/2$ and $R_0=|\Phi_\kappa^{-1}p|$. Since
$|xy|/2\le r_0^2/4$,

$$
0<R_0\le |(x,y,z)|+|s|/\kappa
 <(1+2/\kappa_-)r_0
 \le4^{-\tau_0}/2<e^{-\tau_0}.
\tag{SRO.86}
$$

Here $\tau_0\ge1$. By (SRO.4) and (SRO.20),

$$
h(p)\ge\frac{L_h\log(1/R_0)}{\sqrt\kappa\,R_0}
 \ge\frac{L_h}{1+\kappa_+}=m_0.
\tag{SRO.87}
$$

The factor $\sqrt\kappa$ is the unitary normalization in (SRO.4).
The inequality uses $R_0<1$, $\log(1/R_0)\ge1$ and
$\sqrt\kappa\le1+\kappa_+$.

For propagation, use the left chart $q=pu$. Its Haar Jacobian is one,
and the fields pull back to
$\partial_{u_x},\partial_{u_y}+u_x\partial_{u_w},\partial_{u_z}$.
Denote the principal differential operator by
$\mathcal D=-P$, with $P$ as in [D, (14.1)]. Thus

$$
\begin{gathered}
\mathcal D=\operatorname{div}(\mathsf A(u)\nabla),\qquad
\mathsf A(u)=
\begin{pmatrix}
a&0&0&0\\
0&a&0&au_x\\
0&0&a&0\\
0&au_x&0&\eta+au_x^2
\end{pmatrix},\\
\lambda_-\mathbf1\le\mathsf A(u)\le\Lambda_+\mathbf1
\quad(|u|\le1/4),\qquad
\sum_i\partial_{u_i}\mathsf A_{ij}=0\quad\text{for every }j .
\end{gathered}
\tag{SRO.88}
$$

The matrix bounds are the original left-chart bounds [D, (14.13)].
For the last identity, the variable off-diagonal entries occur in rows
$y,w$, while their only variable is $u_x$; the other variable entry is
in row $w$. Consequently no coefficient-derivative term enters
$\mathcal D f=\sum_{ij}\mathsf A_{ij}\partial_{ij}f$.
In particular

$$
\begin{aligned}
\mathcal D(|u|^{-k})
 &=k|u|^{-k-4}\big((k+2)u^{\mathsf T}\mathsf A(u)u
                         -|u|^2\operatorname{tr}\mathsf A(u)\big)\\
 &\ge k|u|^{-k-2}\big((k+2)\lambda_--4\Lambda_+\big)\ge0
 \quad(0<|u|\le4r_0).
\end{aligned}
\tag{SRO.89}
$$

Here $4r_0\le1/16$. At every punctured point the actual equation
(SRO.72) gives $\mathcal D h=-Vh\le0$, since
$V=16\sqrt{a\eta}\Gamma>0$.

Suppose an inductive floor $h\ge m_j$ holds on
$p\overline{\mathbb B}_{r_0}\setminus\{e\}$, with
$0<m_j\le m_0$. On $r_0<|u|<4r_0$ put

$$
b_j(u)=m_j\,
 \frac{|u|^{-k}-(4r_0)^{-k}}{r_0^{-k}-(4r_0)^{-k}}.
\tag{SRO.90}
$$

It has inner value $m_j$, outer value zero, lies between zero and
$m_j$, and satisfies $\mathcal D b_j\ge0$. On the punctured inner
sphere the floor follows also by continuity from the ball;
on the outer sphere positivity of $h$ suffices.

The comparison remains valid when the annulus meets the original
source. Indeed $w_j=(b_j-h(pu))_+$ vanishes wherever
$pu\in\mathbb B_{r_0}$, by (SRO.87) and $b_j\le m_j\le m_0$.
If $p^{-1}e$ lies in the closed annulus, this gives an open neighborhood
of that point on which $w_j$ is zero. Away from that neighborhood the
original $h$ is smooth. Extend $w_j$ by zero there. The boundary
inequalities and the Lipschitz positive-part operation then put
$w_j\in H^1_0(\{r_0<|u|<4r_0\})$.
Thus this test is supported away from the source, even when the
source is on a boundary sphere. The punctured weak inequality gives

$$
0\le\langle\mathcal D(b_j-h(p\,\cdot)),w_j\rangle
 =-\int \nabla w_j^{\mathsf T}\mathsf A\nabla w_j
 \le-\lambda_-\int|\nabla w_j|^2 .
\tag{SRO.91}
$$

Approximation by compact smooth tests, with a cutoff on the
neighborhood where $w_j=0$, justifies the equality for this $H^1_0$
test. Coercivity and its zero trace imply $w_j=0$.
No Sobolev membership, differential equation or boundary condition for
$h$ across $e$ is used. The test concerns the raw principal operator,
not a new realization of the full endpoint.

On the annulus with $|u|\le2r_0$, the barrier is at least
$\theta m_j$, where

$$
\theta=\frac{2^{-k}-4^{-k}}{1-4^{-k}}=\frac1{2^k+1}.
\tag{SRO.92}
$$

The old floor on the inner ball and punctured continuity therefore
give $h\ge\theta m_j$ on
$p\overline{\mathbb B}_{2r_0}\setminus\{e\}$.
If $q=pv$, $|v|\le r_0/4$, then for $|u|\le r_0$ the original product
satisfies

$$
|vu|\le |v|+|u|+|v_xu_y|
 \le5r_0/4+r_0^2/4<2r_0.
\tag{SRO.93}
$$

Hence an entire ball floor at $p$ supplies an entire ball floor
$\theta m_j$ at $q$. This permits the next comparison with the same
inner-boundary data, rather than only a floor at the center.

For $p\ne e$, the original horizontal construction [D, (14.15)]
joins $e$ to $p$ by at most seven segments of the fields
$X_1,X_2,X_3$: first the $x,y,z$ displacements, then a four-side
commutator rectangle of signed central area $w-xy$. Its length obeys

$$
\ell\le |x|+|y|+|z|+4\sqrt{|w-xy|}<8\varrho(p),
\qquad |w-xy|\le5\varrho(p)^2/4 .
\tag{SRO.94}
$$

For example $|x|+|y|+|z|\le\sqrt3\,\varrho(p)$, and
$\sqrt3+2\sqrt5<8$. Subdivision into segments of length at most
$r_0/4$ gives a number of links

$$
N\le4\ell/r_0+7\le32\varrho(p)/r_0+7 .
\tag{SRO.95}
$$

A link along any of these three fields has left increment of ordinary
Euclidean norm equal to its length. Start with the floor on
$\overline{\mathbb B}_{r_0}\setminus\{e\}$ and apply (SRO.93) at every
link. Intermediate balls and path points may meet $e$; (SRO.91)
already includes that case. The endpoint has $h(p)\ge m_0\theta^N$.
Since $\theta\ge2^{-(k+1)}$ and $\log2<1$, (SRO.95) implies the second
inequality in (SRO.85) with precisely $c_*,C_*$ from (SRO.84).
The expressions $c_*,C_*$ require only rational arithmetic and integer
powers; the exponential is used only to express the lower bound. $\square$

## 14. A numerical numerator estimate with the original time

**Definition 14.1 (rational exterior constants).** Use the brackets and
$\lambda_-,\Lambda_+$ of (SRO.83)–(SRO.84). Choose a positive rational
$\beta$ with $\beta^2\ge a_++\eta_+/4$, and define

$$
\begin{gathered}
\tau=\min(d_-/4,1)>0,\qquad V_+=256(a_++\eta_+),\\
L_* =1+(32\tau\lambda_-)^{-1}
                    +32\tau\Lambda_++2\tau V_+,\\
A_*=2^{42}L_*^3(1+128/\tau),\\
L_+=1+\frac3{16a_-}+\frac{25}{256\eta_-},\qquad
b_*=1+\beta L_+,\\
K_*=\frac{4A_*}{c_*}(1+d_+)
                 \left(1+\frac{\tau}{d_-D_-}\right),\qquad
T_*=32d_+\beta^2,\\
s_*=\max(8,2b_*,b_*+\beta,32d_+\beta^2C_*).
\end{gathered}
\tag{SRO.96}
$$

In particular $\tau$ is a rational proof-cylinder length in the
original time units; it may be smaller than $\min(d/4,1)$.
The symbol $D_-$ brackets the named scalar $D$, whereas
$\mathcal D$ remains the operator of (SRO.88).

**Theorem 14.2 (a computed exterior ratio estimate for the actual
source vector).** For every $p$ with $\varrho(p)\ge s_*$,

$$
0\le\frac{v_d(p)}{h(p)}
 \le K_*\exp\left(-\frac{\varrho(p)^2}{T_*}\right).
\tag{SRO.97}
$$

The estimate uses the original $v_t$, its existing Gaussian norm tail,
and the numerical local estimate of Lemma 10.1.

Proof. Put $Q=(-1/4,1/4)^4$. If $\varrho(p)\ge8$, the original
gauge inequality in [D, §14] gives
$\varrho(pu)\ge\varrho(p)/2-\varrho(u)\ge1$ for $u\in Q$.
Thus the whole left chart is punctured and
$V(pu)\le512\sqrt{a\eta}\le V_+$. For $y\in(-1,1)^4$ and
$-1<\theta<0$ define

$$
Z(\theta,y)=v_{d+2\tau\theta}(p(y/4)).
\tag{SRO.98}
$$

It is smooth and nonnegative, using exactly the positive-time
full-endpoint smoothing in [D, §14]. Its equation (SRO.64) has

$$
\mathsf B(y)=32\tau\mathsf A(y/4),\qquad
W(\theta,y)=2\tau V(p(y/4)),\qquad
(\lambda,\Lambda,\nu)
 =(32\tau\lambda_-,32\tau\Lambda_+,2\tau V_+).
\tag{SRO.99}
$$

The factors are $16$ from the spatial dilation and $2\tau$ from time.
Lemma 10.1 reaches $(\theta,y)=(0,0)$ by continuity.
Left translation preserves Haar measure; spatial dilation contributes
$4^{-4}$ and time contributes $2\tau$. Consequently

$$
\begin{aligned}
v_d(p)
 &\le2^{42}L_*^3\sqrt{128/\tau}
       \left(\int_{d-2\tau}^{d}\int_{pQ}|v_t|^2\,d\mu\,dt\right)^{1/2}\\
 &\le A_*\left(\int_{d-2\tau}^{d}
                         \int_{pQ}|v_t|^2\,d\mu\,dt\right)^{1/2}.
\end{aligned}
\tag{SRO.100}
$$

The second step uses $\sqrt x\le1+x$. This supplies a rational value
for the local numerator constant in [D, (14.17)] from the already
proved Lemma 10.1. Also $d-2\tau\ge d/2>0$, so the entire cylinder
uses the original positive-time source orbit.

Use the original intrinsic distance $d_A$ and $\psi$ of
[D, Definition 14.1]. The straight coordinate path to $u\in Q$ has

$$
d_A(e,u)\le
 \sqrt{\frac3{16a}+\frac{25}{256\eta}}\le L_+.
\tag{SRO.101}
$$

This is [D, (14.18)] with a rational upper enclosure.
The function $\psi=((1+\varrho^4)^{1/4}-1)/\beta$ is
$1$-Lipschitz in $d_A$. If $s=\varrho(p)$, set

$$
r_s=\frac{s-b_*}{\beta}.
\tag{SRO.102}
$$

For $r_s>0$ and every $u\in Q$,
$\psi(pu)\ge\psi(p)-L_+\ge r_s$. Apply
[D, Theorem 14.2, (14.5)] with this $r_s$.
For $d-2\tau\le t\le d$, its time factors give

$$
\|1_{pQ}v_t\|_2
 \le\frac{2\sqrt2(1+d/r_s)}{\sqrt{\pi dD}}
                          e^{-r_s^2/(4d)}.
\tag{SRO.103}
$$

Indeed $t\ge d/2$, $t\le d$, and the negative Gaussian exponent is
largest at $t=d$. Integrating the square over the interval of length
$2\tau$ in (SRO.100), and dividing by the same normalized $h$ in
(SRO.85), yields

$$
\frac{v_d(p)}{h(p)}
 \le \frac{4A_*}{c_*}\sqrt{\frac{\tau}{\pi dD}}\,
       (1+d/r_s)\exp\left(C_*s-\frac{r_s^2}{4d}\right).
\tag{SRO.104}
$$

For $s\ge s_*$ the following inequalities hold:

$$
\begin{gathered}
r_s\ge s/(2\beta),\qquad r_s\ge1,\\
C_*s-\frac{r_s^2}{4d}
 \le C_*s-\frac{s^2}{16d_+\beta^2}
 \le-\frac{s^2}{32d_+\beta^2},\\
1+d/r_s\le1+d_+,\qquad
\sqrt{\frac{\tau}{\pi dD}}
 \le1+\frac{\tau}{d_-D_-}.
\end{gathered}
\tag{SRO.105}
$$

The four lower requirements in $s_*$ respectively ensure a punctured
chart, the first bound for $r_s$, its lower bound one, and absorption
of the linear exponent by half the quadratic exponent.
Equations (SRO.104)–(SRO.105) prove (SRO.97).
The appearance of $F$ in the named scalar $D$ has not introduced an
$F$ heat vector, killed source, or off-source initial delta. $\square$

## 15. A finite rational exterior half-threshold packet

**Definition 15.1 (the exterior packet).** An exterior packet consists
of the legitimate finite name replies and brackets (SRO.83), the
existing source-floor output $(L_h,\tau_0)$ with its finite
inequalities from Theorem 3.1, the rational quantities (SRO.84),
(SRO.96), an integer $n$, and a rational $R$ satisfying

$$
n\ge\max(s_*,1+2T_*K_*),\qquad n\ge1,\qquad
R=\max(n,5n^2/4).
\tag{SRO.106}
$$

All comparisons and integer powers here are finite rational tests.
The source-floor and name replies have their stipulated legitimate
meaning, as in Theorems 5.1 and 8.2. This does not test whether arbitrary
proposed functions satisfy the analytic suppliers.

**Theorem 15.2 (soundness, finite extraction and termination for every
original positive triple).** From exactly the analytic and total-name
suppliers of Definitions 1.1–1.2, for every original finite
$a,\eta,d>0$ one obtains a finite packet of Definition 15.1.
Every accepted packet proves, for the same actual source vector,

$$
v_d(p)<\frac12h(p)\quad
       (p\notin[-R,R]^4),\qquad R\in\mathbb Q_{>0}.
\tag{SRO.107}
$$

In particular the weak order $v_d\le h/2$ holds there $\mu$-almost
everywhere, or equivalently $g_d\le1/2$ there $m$-almost everywhere,
for every permitted Borel repair.

Proof. For $s\ge n$, put $y=2T_*K_*>0$. Since $n\ge1+y$,
$n^2\ge y$, and hence $s^2/T_*\ge2K_*$. The elementary inequality
$e^x\ge1+x$ for $x\ge0$ and (SRO.97) imply

$$
\frac{v_d(p)}{h(p)}
 \le\frac{K_*}{1+\varrho(p)^2/T_*}
 \le\frac{K_*}{1+2K_*}<\frac12
 \quad(\varrho(p)\ge n).
\tag{SRO.108}
$$

If $\varrho(p)\le n$, then in the original coordinates

$$
|x|,|y|,|z|\le n,\qquad
|w|\le|w-xy/2|+|xy|/2\le5n^2/4 .
\tag{SRO.109}
$$

Thus that gauge ball is contained in $[-R,R]^4$, proving (SRO.107).
All its exterior points are away from $e$, so the pointwise assertion
uses only the smooth representatives. Equivalence of the two a.e.
orders follows from $h>0$ a.e. and equivalence of the null sets of
$m$ and $\mu$.

For extraction, interval refinement terminates at finite positive
lower and finite upper rational brackets for $a,\eta,\kappa,d$.
The name of $D>0$ is already supplied by (SRO.40), so refinement also
finds $D_->0$. Theorem 3.1 supplies $L_h,\tau_0$ by its terminating
construction, retaining the original selector and normalization.
One may find $\beta$ by increasing positive integers until
$\beta^2\ge a_++\eta_+/4$. All remaining quantities in (SRO.84),
(SRO.96) are positive finite rational expressions with nonzero
denominators. The integer $k$, then an integer $n$ satisfying
(SRO.106), and finally $R$ require only finite rational arithmetic,
integer powers and ceilings. No exponential need be numerically
evaluated: it appears only in the proof (SRO.108).
These observations prove finite termination separately for each
original triple, without a parameter-uniform size or time bound.

The barrier comparisons require only the already supplied punctured
equation and the whole-ball source floor. The numerator requires only
Lemma 10.1 and the existing full-source Gaussian norm tail. Thus no
pointwise evaluator, numerical compact minimum, Harnack constant or
additional physical supplier is an input to this extraction. $\square$

## 16. Same-source regional assembly for the original global upper cut

**Definition 16.1 (a finite global packet with one conclusion).**
Fix one original input triple and all its services in Definitions
1.1–1.2. Compute one exterior packet of Definition 15.1, with radius
$R$. For a rational target $U>1$, a global packet consists of:

1. A source packet accepted by the general test (SRO.55) of Theorem
   5.1 at this very target $U$, with positive rational source-box
   radius $\delta_0$.
2. The rational radius $\delta=\min(\delta_0,R/2)>0$ and the eight
   rational closed boxes

$$
\begin{gathered}
B_j^+=[-R,R]^{j-1}\times[\delta/2,R]\times[-R,R]^{4-j},\\
B_j^-=[-R,R]^{j-1}\times[-R,-\delta/2]\times[-R,R]^{4-j}
       \quad(1\le j\le4),\\
\mathcal K(R,\delta)=\bigcup_{j=1}^4(B_j^+\cup B_j^-).
\end{gathered}
\tag{SRO.110}
$$

3. A punctured-compact packet of Definition 11.1 for precisely
   $\mathcal K(R,\delta)$, accepted at precisely the same $U$.

The exterior component has target $U$ by combining (SRO.107) with
the finite rational comparison $1/2<U$. Thus all three regional
conclusions in a global packet have exactly the same target $U$.

All regional name requests refer to the one fixed input triple and
its original $h,H,v_t,d$ services. Regional packets may request
different precisions and use different proof cylinders. They do not
select different zero states, normalizations, endpoints, clocks or
source starts. Acceptance checks these references, the finite rational
geometry (SRO.110), $U>1$, the exterior packet, and the two existing
finite regional acceptance rules. It does not decide equality between
functions supplied by independently chosen names.

**Theorem 16.2 (reliable finite global certificates and fair
strict-slack cofinality).** Under exactly Definitions 1.1–1.2 the
packets of Definition 16.1 have the following properties.

1. Each individual acceptance test is finite, relative to the
   stipulated total names.
2. Every accepted packet proves $v_d\le Uh$ $\mu$-almost everywhere
   on all $G$, for the original full endpoint and normalization.
3. For every rational $U>N_d$, where $N_d$ is exactly (SRO.56), a
   fair search through these finite packets eventually accepts a
   packet with conclusion $U$.
4. Fair enumeration over the rational targets and finite packet data
   therefore yields rational conclusions $U_j$ satisfying

$$
v_d\le U_jh\quad\mu\text{-a.e. on all }G,\qquad
\inf_j U_j=N_d .
\tag{SRO.111}
$$

This is the certificate obligation [D, (12.31)], without assuming a
source-maximum identity or a numerical name for $N_d$.

Proof. The fact $N_d\ge1$ is the original mass-one conclusion of
[D, Proposition 12.7 and Corollary 14.4], with exactly the present
$m,h,g_d$. Explicitly the conservative full source law has
$\int g_d\,dm=\operatorname{tr}(T_d1)=1$ and $m(G)=1$.
Thus every $U>N_d$ already satisfies the rational restriction $U>1$.
This restriction adds no hypothesis to the source class.
The same Proposition 12.7, with its full-form trace correspondence,
gives

$$
s_d=\operatorname{tr}g_d=\|v_{d/2}\|_2^2\le N_d<\infty .
\tag{SRO.112}
$$

These are the existing facts needed to match the two regional
thresholds with the global target.

Each box in (SRO.110) is nondegenerate, rational and avoids $e$:
indeed $0<\delta\le R/2$, and one coordinate has absolute value at
least $\delta/2$. Their union is exactly

$$
\mathcal K(R,\delta)
 =\{p\in[-R,R]^4:\|p\|_\infty\ge\delta/2\}.
\tag{SRO.113}
$$

Consequently

$$
G=[-\delta,\delta]^4\cup\mathcal K(R,\delta)
                          \cup\big(G\setminus[-R,R]^4\big).
\tag{SRO.114}
$$

The source box and compact union overlap on
$\delta/2\le\|p\|_\infty\le\delta$ inside the outer box.
The compact union includes every outer face
$\|p\|_\infty=R$; the exterior region begins beyond those faces.
All inner faces in (SRO.110) are also included. Thus this is a finite
cover including the source and all interfaces.

An accepted source packet proves order on
$[-\delta_0,\delta_0]^4$, and hence on the smaller source box.
Its same trace enclosure in (SRO.55) also gives $s_d<U$.
An accepted compact packet proves order on every constituent box of
(SRO.110), with its own finite closed-cell coverage from Definition
9.2. The exterior packet proves order with $1/2<U$ on the third
region. The finite union of the regional null exceptions is null.
This proves the global order in part 2.

For the nonpolar source point the trace assertion is the one in the
source packet, using the full quasi-continuous form representative.
No assignment of a value to $h(e)$ or arbitrary Borel representative
is substituted for that assertion. For the global a.e. inequality the
source has zero $\mu$ and $m$ mass, but it is retained in the process,
form domain and trace. On all punctured interfaces the fields are
literally the same smooth $h,v_d$, not independently patched
solutions. Their proofs on overlapping sets therefore require no
extra boundary or matching supplier.

Finiteness of an individual test follows as well. After the single
terminating exterior extraction, it involves finitely many source
name replies, rational comparisons in (SRO.55), the rational box
construction, and the finite compact test (SRO.77). Invalid geometry
or unequal rational targets is rejected before any unnecessary name
request. Every requested time and coefficient query belongs to the
same stipulated total services. Acceptance is relative to their
legitimate replies, just as for the two reused regional tests.

For cofinality, fix a rational $U>N_d$. Since $s_d\le N_d$, the fair
source search of Theorem 5.1 has some successful finite packet at
$U$. Choose any such packet. Its $\delta_0$ determines $\delta$ and
the particular finite $\mathcal K(R,\delta)$ above.

The smooth punctured representative of $g_d$ satisfies
$g_d(p)\le N_d$ at every $p\ne e$. To see this from the essential
bound, if $g_d(p)>N_d$ at one punctured point, continuity gives a
punctured open ball on which $g_d>q>N_d$. Strict positivity of $h$
there makes its $m$ measure positive, contrary to the definition of
$N_d$. This uses no numerical point value or compact minimum.
It follows that

$$
G_{\mathcal K(R,\delta)}
   =\sup_{p\in\mathcal K(R,\delta)}g_d(p)\le N_d<U .
\tag{SRO.115}
$$

Theorem 8.2 therefore gives a successful finite compact packet at
this same $U$ on precisely that region. The exterior packet is already
available, independently of $U$; its fixed half threshold is enough
because $U>N_d\ge1$. No exterior service with arbitrary requested
accuracy is assumed.

For an explicit fair organization, first extract the exterior packet.
For a fixed target $U$, enumerate all finite source-candidate data of
(SRO.55) together with finite compact-candidate data of Definition
11.1. Each source candidate determines the rational region (SRO.110);
perform its finite source test and, on success, the finite compact
test for that region. The successful pair just proved exists in this
language, and every earlier candidate test terminates. Hence this
search eventually accepts for every $U>N_d$, without testing
$U=N_d$ or knowing the size of its positive gap.

For global enumeration, enumerate finite tuples containing a rational
$U>1$ and both candidate packets fairly. Equivalently dovetail the
finite tests over the rational targets; do not wait for an unsuccessful
target's entire search to terminate. Each test makes only finitely
many calls to total names. Every successful finite tuple is eventually
tested. The preceding completeness proof shows in particular that
every rational $U>N_d$ appears as an accepted conclusion.
Soundness implies every accepted $U\ge N_d$, so their infimum is
$N_d$. There are accepted conclusions because $N_d<\infty$ and
rationals exist above it. This proves all four assertions. $\square$

## 17. Exact source correspondences and the unchanged calibration consumer

**Definition 17.1 (mathematical antecedents of the additional
relations).** The source-specific deductions (SRO.85), (SRO.97),
(SRO.107) and (SRO.111) are repo-derived conditional on Definitions
1.1–1.2. Their mathematical inputs and uses are exactly:

| Input or intermediate | Correspondence and scope |
| --- | --- |
| Original selector, unit Green field, normalized zero state and full complex endpoint | (SRO.1)–(SRO.4), [D, §§11–12], [E, §§109–112], [S, §§115–117, 130–133]. The same $A=\rho C$ and $C(w_*)=1$ determine the denominator throughout; $H$ is never replaced by $F$. |
| Numerical all-angle source floor | Theorem 3.1 supplies $L_h,\tau_0$. Equations (SRO.86)–(SRO.87) retain its $\sqrt\kappa$ factor when converting to a whole original-coordinate ball. |
| Propagated denominator | The explicit original left-chart matrix, the attractive sign $\mathcal D h=-Vh\le0$, the radial Hessian calculation and the positive-part energy comparison (SRO.88)–(SRO.95). This is a source-specific floor propagated from a supplied whole ball, rather than a general Harnack theorem. |
| Numerical local numerator | Lemma 10.1 with exactly (SRO.98)–(SRO.100). The proof time is $\theta$, the original evolution time is $t=d+2\tau\theta$, and the raw Jacobian is $\tau/128$. |
| Source-vector tail and named $D$ | [D, Theorem 14.2, (14.3)–(14.5)], with $\beta^2\ge a+\eta/4$. Its full-form trace and original source vector are used in (SRO.103). |
| Source-neighborhood order | Theorem 5.1, specifically the finite test (SRO.55) with the target $U$ of the global packet. |
| Punctured-compact order | Theorem 8.2 and Definition 11.1, on the eight rational boxes (SRO.110), at that identical $U$. |
| Thresholds for strict-slack assembly | The existing original mass-one and trace bounds [D, Proposition 12.7 and Corollary 14.4] give $1\le N_d$ and $s_d\le N_d$ for this same source. |
| Global geometry and compatibility | The rational equalities (SRO.113)–(SRO.114) include all faces. Every regional inequality concerns the fixed $h,v_d,d$; there is no regional rescaling of their normalization or choice of another endpoint. |

The weak comparison in (SRO.91) is the classical positive-part energy
method for a symmetric uniformly elliptic divergence operator with
zero boundary test. Its full calculation is included because the
annulus can meet the original source; only the test, not $h$, is
extended through that point. Radial barriers, finite path subdivision
and elementary rational majorants are mature intermediates.

The local power-iteration antecedent remains D. G. Aronson,
[*Harnack, Hölder, Gauss and Widder: Serrin's Parabolic Legacy*,
arXiv:1611.09417v1](https://arxiv.org/html/1611.09417v1), weak formulation
(6), fundamental power inequality (7), and “LOCAL BOUNDEDNESS”.
Its divergence-form equation has time coefficient one; the raw
proof cylinder (SRO.98) has exactly that coefficient and the bounded
potential (SRO.99). The primary text gives the iteration method;
the numerical value used here is the already proved Lemma 10.1,
not an unspecified structural constant from the reference.
The finite-wave and transmutation antecedents for the reused norm
tail remain [D, Definition 14.5], T. Coulhon and A. Sikora,
[*Gaussian heat kernel upper bounds via Phragmén–Lindelöf theorem*,
arXiv:math/0609429v1](https://arxiv.org/html/math/0609429v1),
Theorem 3.4 and (3.8). No additional heat-kernel or Harnack theorem
is required in (SRO.85)–(SRO.111).

**Definition 17.2 (the precise consumer and full retained domain).**
The global upper enumeration of Theorem 16.2 is exactly the upper
side of [D, Definition 12.8]. Applying that existing implication
together with its existing lower enumeration in Proposition 12.7
gives a scalar interval name of the same $N_d$. Thus the calibration
remains literally $M=1+N_d$, $c=1/(4M)$ and all emissions (SRO.56);
an exterior or intermediate proof majorant never replaces $M$.
This is a use of those implications, not a new finite-word or
finite-energy theorem.

All original finite positive triples remain in the conditional
domain. The original source space $\Omega$, including its source
point, every input preparation, event including zero, failure,
rejection, stop,
alarm, destruction and return, every record and history, every
reference and joint object, control and clock, and every legal future,
keeps its original domain and interpretation. In particular the
source start is at $e$, the first passive read is at $2d$, all
subsequent gaps are $d$, and read noise is the original conditionally
fresh noise on the same undisturbed path. Auxiliary balls, paths,
cylinders and regional covers only prove deterministic field
inequalities; they do not select a subfamily of histories, alter
units, add a physical supplier, or modify any emission or operation.
The optional identity $N_d=s_d$ is not a premise or conclusion of
the global-certificate construction.

## 追加锚（本行以下为增补区）
