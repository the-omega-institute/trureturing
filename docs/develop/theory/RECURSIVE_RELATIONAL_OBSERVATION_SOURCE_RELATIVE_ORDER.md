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
$W_r=(k-r f_h(r\,\cdot))_+$ has $L^2(D)$ norm at most
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
Then $W_r(\omega)<c_-\tau/256=k/2$, so
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
| D. G. Aronson, [Harnack, Hölder, Gauss and Widder: Serrin's parabolic legacy](https://arxiv.org/html/1611.09417v1), weak equation and fundamental power inequality (7), and D. G. Aronson, Non-negative solutions of linear parabolic equations, Ann. Scuola Norm. Sup. Pisa 22 (1968), 607–694 | Established local power-test and iteration method. The equation here has time coefficient one only in the unitary raw annular chart and proof time (SRO.47). No unspecified structural constant or weighted-time theorem is imported; (SRO.25)–(SRO.34) provide the finite bounds used here. |
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
