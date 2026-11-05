# Four-path full-record recovery: first selected determinant zero and relaxed quartic

## 49. First selected determinant zero, population relaxation and the original local phase consequence

Use the original normalized effects, ordinary transpose and shared feedback of
the [source volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md),
Definitions 1.1, 11.1 and 23.1. Section numbers 24--39 refer to
[Continuation I](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md);
40--47 refer to
[Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md).
The global minimizing-set result cited as Theorem 48.5 is in
[Continuation III](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_III.md).
The numbered statements and identities 49 in this volume are distinct
from the source-correspondence Section 49 of Continuation III.
The domain is still
$\mathcal K=\operatorname{Dens}_2\times U(4)$, with
$f=g-\kappa\rho$ and

$$
\rho=\min\{\rho_+,\rho_-\},\qquad
\rho_\sigma=\|E-E_\sigma\|_{\mathrm F}^2+
 \min_{|\lambda|=1}\|U-\lambda U_\sigma\|_{\mathrm F}^2.
\tag{49.1}
$$

The scalar acts on the entire feedback. The two orientations below are
distinct from the two optimizer signs in (49.1). All amplitude and trace
data always belong to the same actual feedback. Put

$$
h=1/\sqrt2,\quad c=\cos(\pi/8),\quad s=\sin(\pi/8),\quad
d=2(h+c),\quad e=2(h+s),\quad \gamma=c-h>0.
\tag{49.2}
$$

The comparator $N(\xi)=N_{\mathrm{geo}}(\xi)$ and
$V(\xi)=N(\xi)+\kappa\xi$ are the **selected positive geometric** values
of Theorem 37.5 and (41.1). They are not definitions of the unrestricted
global minimum $m(\xi)$.

### 49.1. Statement and normalization

For $0<\xi<4$ use the existing unique interior scalar selector:

$$
t=\xi/2,\quad \delta=\delta_\circ(t),\quad
x=1-\delta/2,\quad y=\sqrt{1-x^2},\quad q=t-\delta,\quad p=1-q.
\tag{49.3}
$$

All four of $x,y,p,q$ lie in $(0,1)$. Define, exactly as in (36.43),

$$
\begin{aligned}
L_a&=\frac{hx^2}{1+x}
 \left(\frac{\gamma\sqrt p}{hx+c}+\frac{\sqrt q}{y}\right),\\
L_b&=\gamma\sqrt p+\frac{(h^2x-s^2)\sqrt q}{hy},\\
D_{\mathrm{sel}}(\xi)&=L_aL_b-s^2q.
\end{aligned}
\tag{49.4}
$$

Thus $D_{\mathrm{sel}}(\xi)=\mathscr D(x,p)$ in (36.43), or
$\mathfrak D_+(x,q)$ in (46.13); the population arguments in those
two notations differ.

**Theorem 49.1 (unique first zero and relaxed quartic classification).**
There is exactly one zero $\xi_*$ of $D_{\mathrm{sel}}$ on $(0,4)$.
It satisfies

$$
\frac{59}{25}<\xi_*<\frac{61}{25}<\frac{13}{4},\qquad
D_{\mathrm{sel}}'(\xi_*)<0.
\tag{49.5}
$$

The determinant is positive on $(0,\xi_*)$ and negative on
$(\xi_*,4)$. At this zero, minimize over effects at the same actual
feedback and original level, and then eliminate the stable population
and transverse phase coordinates in the complete phase chart (43.2).
With its coordinate $b$ retained as amplitude, the resulting objective is

$$
\Phi_{\mathrm{red}}(b)
 =N(\xi_*)+C_{\mathrm{eff}}b^4+O(b^6),\qquad
C_{\mathrm{eff}}>\frac{28}{25}>0.
\tag{49.6}
$$

The exact coefficient is (49.28) below, at the algebraic root specified
in (49.18). The normalization is $b$ in (43.2), with tangent
$(\dot\delta,\dot a,\dot b)=(0,\eta,1)$; it is not a unit length
eigenvector normalization. For a rescaling $b=\lambda\widetilde b$
the coefficient becomes $\lambda^4C_{\mathrm{eff}}$.

At $\xi_*$ each selected orbit is a strict isolated local minimum on
the **phase feedback** part of its original level, including every
normalized positive effect at those feedbacks. A quadratic stable
bound and a quartic null-direction bound are given in (49.41).
For levels sufficiently close to and strictly above $\xi_*$, each
selected orientation has two nearby strict local phase minimum branches
whose values are strictly smaller than $N(\xi)$. These are actual
same-original-level competitors. They are not asserted to be global
minimizers. The proof and the all-effect domain are given below.

### 49.2. Monotonicity of the actual scalar selector

For independent $0<\delta<2$ and $0<q<1$, put

$$
\begin{aligned}
\mathscr L(\delta,q)&=d^2(1-q)+e^2q
 -(u\sqrt{1-q}+v\sqrt q)^2,\\
u&=2R,\quad R=c+hx,\quad v=2hy,\quad
x=1-\delta/2,\quad y=\sqrt{1-x^2},\\
\mathcal H(t,\delta)&=\mathscr L(\delta,t-\delta)-2\kappa t.
\end{aligned}
\tag{49.7}
$$

Theorem 37.5 selects the unique interior minimum of $\mathcal H$ on
$J(t)=[\max\{0,t-1\},t]$, for $0<t\le2$.
Theorem 41.2 supplies, at every selected point,

$$
\mathscr L_\delta=\mathscr L_q>0,\qquad q<y^2.
\tag{49.8}
$$

The following derivative signs are needed along that actual selector;
they are not assumed throughout the independent $(\delta,q)$ rectangle.
Write

$$
r=\sqrt{q/p},\quad D_0=d^2-e^2=4h+8s,\quad
A_0=u^2-v^2-D_0,\quad C_1=(Rx-hy^2)/y.
$$

Direct differentiation at fixed values of the other independent variable
gives

$$
\begin{aligned}
\mathscr L_q&=A_0+uv(r-r^{-1}),\\
\mathscr L_{\delta q}
 &=2h[-2(R+hx)+C_1(r-r^{-1})],\\
\mathscr L_{\delta\delta}
 &=p(r^2-1+2rM_1),\qquad
 M_1=\frac{xy^2+hR}{y^3},\\
\mathscr L_{qq}&=\frac{uv}{2(pq)^{3/2}}>0.
\end{aligned}
\tag{49.9}
$$

To prove $\mathscr L_{\delta q}<0$, first suppose $C_1\le0$.
The numerator $cx+2hx^2-h$ of $C_1$ is strictly increasing and is
$(c-h)/2>0$ at $x=1/2$, so $x<1/2$. Also

$$
A_0/4=x^2+2hcx-h/2-2s
$$

is increasing and at $1/2$ equals $1/4-h/2+(h-1)s<0$.
Hence $A_0<0$. Since $\mathscr L_q>0$, the first line of (49.9)
forces $r>1$, so $C_1(r-r^{-1})\le0$. If $C_1>0$ and $r\le1$,
the same conclusion is immediate. In the remaining case $C_1>0,r>1$,
(49.8) gives $r<y/x$ and $x<y$. Therefore

$$
C_1(r-r^{-1})
 <\frac{(Rx-hy^2)(y^2-x^2)}{xy^2}
 <R\frac{y^2-x^2}{y^2}<R.
$$

The second line of (49.9) is strictly negative in every case.

For $\mathscr L_{\delta\delta}>0$, put $K_0=D_0/4=h+2s$.
The exact identity

$$
2M_1-\frac{A_0}{uv}
 =\frac{(Rx+hy^2)^2+K_0y^2}{Rh\,y^3}>0
\tag{49.10}
$$

uses $x^2+y^2=1$ and $2h^2=1$.
The inequality $\mathscr L_q>0$ implies
$r^2-1>-A_0r/(uv)$, so the third line of (49.9) and (49.10)
give $\mathscr L_{\delta\delta}>0$.

Thus at every selected point

$$
H_t:=\mathcal H_{\delta\delta}
 =\mathscr L_{\delta\delta}-2\mathscr L_{\delta q}
      +\mathscr L_{qq}>0.
$$

The scalar implicit function theorem, with uniqueness from Theorem 37.5,
identifies the selector locally as an analytic function. Differentiating
$\mathscr L_\delta-\mathscr L_q=0$ along $q=t-\delta$ gives

$$
\delta_\circ'(t)=\frac{\mathscr L_{qq}-\mathscr L_{\delta q}}{H_t}>0,
\qquad
q'(t)=\frac{\mathscr L_{\delta\delta}-\mathscr L_{\delta q}}{H_t}>0.
\tag{49.11}
$$

In particular $x'(t)<0$ and $r'(t)>0$ on the whole selected curve
$0<t<2$.

### 49.3. Firstness and simple crossing

Use the coefficients of (36.45):

$$
a_0=\frac{h\gamma x^2}{(1+x)(hx+c)},\quad
a_1=\frac{hx^2}{(1+x)y},\quad
b_1=\frac{h^2x-s^2}{hy}.
$$

Then

$$
\frac{D}{p}=G(x,r):=(a_0+a_1r)(\gamma+b_1r)-s^2r^2.
\tag{49.12}
$$

All three coefficients $a_0,a_1,b_1$ are strictly increasing in $x$.
For $a_0$ its logarithmic derivative is
$2/x-1/(1+x)-h/(hx+c)>0$; for $a_1$ it is
$2/x-1/(1+x)+x/y^2>0$; and
$b_1'=(h^2-s^2x)/(hy^3)>0$.

Theorem 36.5 supplies the unique $x_\dagger\in(0,1)$ satisfying
$(h^2+s^2)x_\dagger^3-s^2(1+x_\dagger)=0$.
For $x\ge x_\dagger$, $D>0$. For $x<x_\dagger$, (49.12)
has positive constant term and negative quadratic coefficient, hence
exactly one positive root $r_*(x)$, and is negative precisely above
that root. At the root,

$$
\gamma+b_1r_*=
 \frac{s^2r_*^2}{a_0+a_1r_*}>0.
$$

Consequently $G_x>0$ there. Also $G_r<0$ at the positive root
of this downward quadratic. It follows that $r_*'(x)>0$.
By (49.11), once $x<x_\dagger$ the difference
$r(t)-r_*(x(t))$ is strictly increasing. Before that region the
determinant is strictly positive. This proves that the selected
determinant has at most one zero, without a numerical root search.
For small $t>0$, $0<\delta<t$ implies $x\to1$, so it starts positive.
Existence and a rational bracket are proved in the next subsection.
At any zero, since $D=pG$,

$$
\frac{dD_{\mathrm{sel}}(2t)}{dt}
 =p(G_xx'(t)+G_rr'(t))<0.
\tag{49.13}
$$

Thus the unique zero is simple, with exactly the sign pattern in
Theorem 49.1. This differentiates along the selector; it is not the
fixed-$t$ derivative used for population relaxation below.

### 49.4. Exact algebraic root and rational isolation

Set

$$
\omega=c/h=\sqrt{1+h},\quad v_0=s^2/h^2=1-h,\quad
k=\omega-1,\quad \ell=1-x^2,\quad z=\sqrt{q/p}/y,\quad
\mathsf H=h+4s.
$$

Thus $q=z^2\ell/(1+z^2\ell)$ and $p=1/(1+z^2\ell)$.
Define the two polynomials

$$
\begin{aligned}
\mathcal F(x,z)={}&x+\omega
 +[\mathsf H+\omega+(1-2\omega)x-2x^2]z\\
 &+[1-2x^2-\omega x]z^2
 +\ell[\mathsf H-(1+2\omega)x-2x^2]z^3
 -(x+\omega)\ell^2z^4,\\
\mathcal P(x,z)={}&k^2x^2+kx^2(2x+\omega-v_0)z\\
 &+(x+\omega)[(1+v_0)x^3-v_0(1+x)]z^2.
\end{aligned}
\tag{49.14}
$$

Substitution in (49.7) and (49.4) gives the exact unsquared identities

$$
\mathcal F=\frac{z(1+z^2\ell)}{4h^2}
    (\mathscr L_\delta-\mathscr L_q),\qquad
\mathcal P=\frac{(1+x)(x+\omega)}{h^2p}D.
\tag{49.15}
$$

Every multiplier is positive for $0<x<1,z>0$. In the first identity
$D_0/(4h^2)=\mathsf H+h=\mathsf H+\omega^2-1$.
There is no squaring or unspecified radical branch.

Here is a rational certificate on
$\mathcal R=[16/25,13/20]\times[32/25,13/10]$.
Positive square comparisons using (49.2) give

$$
\begin{gathered}
7071/10000<h<7072/10000,\qquad
1913/5000<s<3827/10000,\\
\omega_-:=2613/2000<\omega<6533/5000=:\omega_+,\\
\mathsf H_-:=179/80<\mathsf H<1119/500=:\mathsf H_+,\\
v_-:=183/625<v_0<2929/10000=:v_+.
\end{gathered}
\tag{49.16}
$$

On $\mathcal R$, $\mathcal F_{\mathsf H}=z+\ell z^3>0$, whereas
$\mathcal F_\omega=1+(1-2x)z-xz^2-2x\ell z^3-\ell^2z^4<0$:
indeed $x>1/2$ and $xz^2>1$.
Writing $\mathcal F=x+\omega+\sum_{i=1}^4B_i z^i$, direct bounds are

| Coefficient derivative | Rational upper bound on $\mathcal R$ |
| --- | --- |
| $B_1'=1-2\omega-4x$ | $-4173/1000<-4$ |
| $B_2'=-4x-\omega$ | $-7733/2000<-19/5$ |
| $B_3'=-2\mathsf Hx+3(1+2\omega)x^2-(1+2\omega)-4x+8x^3$ | $-2345219/1000000<-2$ |
| $B_4'=\ell(5x^2+4\omega x-1)$ | $52086573/20000000<3$ |

For the third bound, $B_3'$ increases in $x,\omega$ and decreases in
$\mathsf H$ on this box: its $x$ derivative is
$-2\mathsf H+6(1+2\omega)x-4+24x^2>0$.
For the fourth, the $x$ derivative is
$-20x^3-12\omega x^2+12x+4\omega>0$ there, and the
$\omega$ derivative is positive. Endpoints give the displayed values.
Consequently

$$
\mathcal F_x<1-4(32/25)-(19/5)(32/25)^2
 -2(32/25)^3+3(13/10)^4=-1492981/250000<0.
$$

The following exact substitutions therefore bound the two horizontal
edges, uniformly in $x$:

$$
\begin{aligned}
\mathcal F(13/20,32/25;\mathsf H_-,\omega_+)
 &=\frac{27078966727}{1220703125000}>1/50,\\
\mathcal F(16/25,13/10;\mathsf H_+,\omega_-)
 &=-\frac{445536333653}{7812500000000}<-1/20.
\end{aligned}
\tag{49.17}
$$

Thus for every $x$ in the box there is a root in its $z$ interval.
Any such root is an actual selected point: define
$\delta=2(1-x)$, $q=z^2\ell/(1+z^2\ell)$ and $t=\delta+q$.
Then $0<t<2$, $\delta\in\operatorname{int}J(t)$ and (49.15)
is the original stationarity equation. Strict scalar convexity from
Theorem 37.5 identifies it with the selected minimum. There cannot be
two such $z$ at one $x$, since $x(t)$ is strictly decreasing by (49.11).
Equivalently the continuous strictly monotone selected $x(t)$ has a
continuous inverse throughout this $x$ interval.

To certify a determinant sign at each vertical edge, write
$E_v(x)=(1+v)x^3-v(1+x)$ and

$$
\begin{aligned}
\mathcal P^+&=(\omega_+-1)^2x^2
 +(\omega_+-1)x^2(2x+\omega_+-v_-)z
 +(x+\omega_-)E_{v_-}(x)z^2,\\
\mathcal P^-&=(\omega_--1)^2x^2
 +(\omega_--1)x^2(2x+\omega_--v_+)z
 +(x+\omega_+)E_{v_+}(x)z^2.
\end{aligned}
$$

Here $E_v<0$ on the box and decreases with $v$.
It follows term by term that $\mathcal P^-\le\mathcal P\le\mathcal P^+$.
The exact endpoint values are

$$
\mathcal P^+(16/25,32/25)
 =-\frac{33093929164}{762939453125}<-1/25,\qquad
\mathcal P^-(13/20,13/10)
 =\frac{207479065651}{40000000000000}>1/200.
$$

Each of these downward quadratics has positive constant and linear
terms, so its sign changes once on the positive $z$ axis. The first
value makes the determinant negative at the selected left edge for
all $z\ge32/25$; the second makes it positive at the selected right
edge for all $z\le13/10$. Continuity and the at-most-one-zero result
prove that

$$
\boxed{\mathcal F(x_*,z_*)=\mathcal P(x_*,z_*)=0,\quad
 16/25<x_*<13/20,\quad32/25<z_*<13/10}
\tag{49.18}
$$

has exactly one solution. Its level is exactly

$$
\xi_*=4(1-x_*)+
 \frac{2z_*^2(1-x_*^2)}{1+z_*^2(1-x_*^2)}.
\tag{49.19}
$$

One can also specify a single positive radical branch: on the $x$
interval in (49.18), set
$A=k^2x^2$, $B=kx^2(2x+\omega-v_0)$,
$C=-(x+\omega)E_{v_0}(x)>0$. Then
$z_D(x)=(B+\sqrt{B^2+4AC})/(2C)$, and $x_*$ is the unique
root of $\mathcal F(x,z_D(x))=0$ in that interval.

Finally the box gives

$$
\frac{14784}{15625}<z_*^2(1-x_*^2)<\frac{62361}{62500}<1,
\quad 12/25<q_*<1/2,\quad 7/10<\delta_*<18/25.
$$

The leftmost fraction exceeds $12/13$. Thus
$59/25<2(\delta_*+q_*)<61/25$, as claimed. This certificate
proves firstness, root correspondence and a strict crossing jointly;
an isolated numerical zero alone would establish none of those facts.

### 49.5. Exact original-level effect elimination and phase coordinates

Use (43.2), for either $\tau=\pm1$ and a single $|\lambda|=1$:

$$
\begin{aligned}
X&=-\cos b\cos a+\sqrt{(1+x)^2-\cos^2b\sin^2a},\quad
Y=\sqrt{1-X^2},\\
w_\tau&=(e^{ia}(X+\tau iY),e^{ia}(X-\tau iY),
                         e^{i\tau b},e^{-i\tau b}),\\
U&=\lambda\operatorname{diag}(w_\tau)U_+,\qquad x=1-\delta/2,\\
A&=2(1+x)=4-\delta,\\
P/\lambda&=2(hXe^{ia}+c\cos b),\qquad
Q/\lambda=2\tau(ihYe^{ia}-s\sin b),\\
B&=2|iYe^{ia}-\sin b|.
\end{aligned}
\tag{49.20}
$$

The radicals are the positive branches through $X=x_*,Y=y_*$.
Theorem 43.2 gives both the complete local chart and its analytic
inverse modulo exactly the original scalar. In particular no relative
phase direction has been omitted.

The selected feedback and level belong to the open set $\Omega$ in
(40.21). Its strict conditions are
$uv>0$, $0<q=t-\delta<1$, $q<J_+$, $t_-<0$, and positive arc
derivative greater than $49/180$. Here $u=|P|$, $v=|Q|$;
$J_+=(1+A-B)/2$ and $t_-=(\xi-8+2B)/2$ are the original
fixed-feedback arc data of (36.2). At the selected point, (49.18)
gives $x_*>16/25$ and $y_*<4/5$, hence

$$
J_+=\frac{3+2x_*-2y_*}{2}>\frac{67}{50}>1,
\qquad B=2y_*<8/5<2.
$$

Choose a product neighborhood of the selected feedback and level
contained in $\Omega$ with $J_+>1$, $B<2$ and $\xi<4$.
All these conditions are strict and common-scalar invariant.

It is important to distinguish the pure endpoint $q$ from the
population of a general effect. Write

$$
F_E=T^\dagger E^{\mathsf T}T=
 \begin{pmatrix}1-r&z_E\\\bar z_E&r\end{pmatrix},\qquad
\epsilon(E)=2[r(1-r)-|z_E|^2].
$$

The identities (41.3), at this actual $U$, give

$$
\begin{aligned}
\rho_+&=2\delta+2r-\epsilon(E),\\
\rho_-&=10-2r-2B-\epsilon(E),\\
\rho_--\rho_+&=2(1+A-B-2r)=4(J_+-r).
\end{aligned}
\tag{49.21}
$$

For every normalized positive effect, the same identities give
$\rho_-=8-2B+2[(1-r)^2+|z_E|^2]\ge8-2B>\xi$, since $t_-<0$.
Thus no effect can have negative branch equal to this prescribed $\xi$.
Every original effect with $\rho(E,U)=\xi=2t$ therefore has the
positive sign as its unique minimizing sign and satisfies exactly

$$
q=t-\delta=r-\epsilon(E)/2=r^2+|z_E|^2,\qquad
q\le r\le\min\{\sqrt q,J_+\}=\sqrt q.
\tag{49.22}
$$

Conversely, every $r\in[q,\sqrt q]$ and every coherence phase with
$|z_E|^2=q-r^2$ give a normalized positive effect at this same original
level: $F_E$ has trace one and determinant $r-q\ge0$, and
$0<r<1$. Its positive distance is $2t$, and its negative distance is
strictly larger. Thus (49.22) is the full feasible arc in both
directions, with no sign tie in this neighborhood. It retains the
zero-coherence endpoint $r=\sqrt q$ and every intermediate mixed
effect. Its impurity is $2(r-q)$; one must not set $r=q$ for mixed
effects.

By Theorem 40.4, or precisely (43.8)--(43.9), the unique minimizing
effect at this same $U$ and level is

$$
\widehat E=
 \left[T\begin{pmatrix}
 1-q&\sqrt{q(1-q)}\,\bar P Q/(uv)\\
 \sqrt{q(1-q)}\,P\bar Q/(uv)&q
 \end{pmatrix}T^\dagger\right]^{\mathsf T},
\qquad
f(E,U)\ge f(\widehat E,U)+\frac{49}{360}\epsilon(E).
\tag{49.23}
$$

For the full arc, put $\Delta_+=d^2-u^2$,
$b_+=e^2-v^2-\Delta_+$ and
$\varphi_q(r)=\Delta_++b_+r-2uv\sqrt{q-r^2}$.
The same-feedback identity (41.3) gives exactly

$$
f(E,U)-f(\widehat E,U)
 =\varphi_q(r)-\varphi_q(q)
   +2\bigl(uv|z_E|-\operatorname{Re}(Pz_E\bar Q)\bigr).
$$

The last summand is nonnegative. On $q\le r<\sqrt q$,
$\varphi_q'(r)\ge\varphi_q'(q)>49/180$ by (40.20)--(40.21);
continuity includes $r=\sqrt q$. This proves the impurity bound in
(49.23) over the full arc, including arbitrary coherence phases.
Equality with the minimizing value requires $r=q$ and the unique
aligning phase, since $uv\sqrt{q(1-q)}>0$.

The ordinary transpose is retained. The minimizing effect is positive,
trace one and rank one; $q<J_+$ makes its positive distance uniquely
minimizing. Its exact analytic objective is

$$
\Psi(t,\delta,a,b)=d^2p+e^2q
 -(\sqrt p\,|P|+\sqrt q\,|Q|)^2-2\kappa t,\qquad
q=t-\delta,\quad p=1-q.
\tag{49.24}
$$

All its moduli and roots are analytic in this neighborhood, since
$p,q,u,v>0$. At $a=b=0$ it is $\mathcal H(t,\delta)$.
The phase expansion (43.12), with $S_0=2\Gamma$, is

$$
\Psi=\mathcal H(t,\delta)
 +4\Gamma(L_aa^2+L_bb^2-2s\sqrt q\,ab)
 +O((|a|+|b|)^4).
\tag{49.25}
$$

The exact symmetry $(a,b)\mapsto(-a,-b)$ removes odd total
phase degrees. It follows either from the moduli in (49.20) or from
their squared expressions. All statements hold for both orientations,
with identical objective and the same common-scalar action.

### 49.6. The quartic before and after stable relaxation

In this subsection evaluate all scalar quantities at $t_*=\xi_*/2$
and its selected point unless a derivative variable is displayed. Put

$$
\begin{gathered}
L=1+x,\quad R=hx+c,\quad C=hy,\quad
\Gamma=\sqrt p\,R+\sqrt q\,C,\\
\eta=\frac{s\sqrt q}{L_a},\qquad
\mu=\frac12\left(\frac{h\gamma\sqrt p}{R}
                     +\frac{h\sqrt q}{y}\right),\qquad
j=\frac{x^2\eta^2}{L},\\
\mathcal E=\frac12\left[
 \frac{x+j}{x^2y^2}-1+\frac{(L+j)^2}{4Lj}\right],\\
r_2=-\frac{\gamma(R+hj)}{2R},\qquad
c_2=\frac{-h^2(x+j)+s^2+2hs(\sqrt L\,y/x)\sqrt j}{2C},\\
\mathcal M=2\mu j\mathcal E
       +\frac{\sqrt p}{2R}r_2^2+\frac{\sqrt q}{2C}c_2^2.
\end{gathered}
\tag{49.26}
$$

Here $j,\mu>0$; $L_a=2\mu x^2/L$ and $L_aL_b=s^2q$.
Define

$$
H_*=\left.\mathcal H_{\delta\delta}\right|_{(t_*,\delta_*)}>0,
\qquad
K_\delta=\frac{\left.\partial_\delta D\right|_t}{L_a}.
\tag{49.27}
$$

The exact population-relaxed coefficient is

$$
\boxed{C_{\mathrm{eff}}
 =8\Gamma\mathcal M-\frac{8\Gamma^2K_\delta^2}{H_*}.}
\tag{49.28}
$$

All terms in (49.28) are exact algebraic quantities specified by
(49.18) and positive radicals. The derivative in (49.27) is fixed
$t$, so that

$$
\left.\partial_\delta D\right|_t
 =-\tfrac12\partial_x\mathfrak D_+(x,q)
                    -\partial_q\mathfrak D_+(x,q).
\tag{49.29}
$$

It differs from (49.13); substituting the along-selector derivative
would give the wrong relaxation term.

For the fixed-population quartic, use the exact cone remainder
(46.18)--(46.24) on its positive row. Set
$B_c=\varepsilon$, $H_c=j\varepsilon$,
$A_c=(x+j)\varepsilon$, so the squared pair lengths are
$X_c=x^2+(x+j)\varepsilon$ and $Y_c=1-\varepsilon$.
They lie in the attained triangle for all sufficiently small
$\varepsilon>0$, since
$\Delta=4Lj\varepsilon-(L+j)^2\varepsilon^2>0$.
The first square and the determinant term of (46.19) vanish on this
ray: $\sqrt j=t_c/(2\mu)$, where $t_c=s\sqrt q\sqrt L/x$.
The coherent triangle factor is exactly

$$
F_c^2=\frac{Ly^2j}{x^2}\varepsilon^2
 \frac{[1-(x+j)\varepsilon/y^2]
       [1-(L+j)^2\varepsilon/(4Lj)]}
      {[1+(x+j)\varepsilon/x^2](1-\varepsilon)}.
\tag{49.30}
$$

Its positive square root is
$F_c=(\sqrt L\,y/x)\sqrt j\,\varepsilon
 -\mathcal E(\sqrt L\,y/x)\sqrt j\,\varepsilon^2
 +O(\varepsilon^3)$.
The half-recoveries in (46.21) have
$R_{\mathrm{var}}-R=r_2\varepsilon+O(\varepsilon^2)$ and
$C_{\mathrm{var}}-C=c_2\varepsilon+O(\varepsilon^2)$.
In (46.19) the coherent remainder coefficient is
$\sqrt q\,hs(\sqrt L\,y/x)\sqrt j\,\mathcal E/C
=2\mu j\mathcal E$. The last two terms give exactly the two
root squares in $\mathcal M$. Hence

$$
\Gamma-\Gamma_{\mathrm{var}}
 =\mathcal M\varepsilon^2+O(\varepsilon^3).
\tag{49.31}
$$

This cone ray is realized in the original chart, with
$B_c=\sin^2 b$ and the analytic branch

$$
\sin a=
 \frac{\sin b\sqrt{4Lj-(L+j)^2\sin^2b}}
 {2\sqrt{x^2+(x+j)\sin^2b}\cos b},\qquad
a=\eta b+O(b^3).
\tag{49.32}
$$

Indeed its trace equation gives
$\Delta=4X_cY_c\sin^2a$; choosing the sign of $a$ equal to
the sign of $b$ attains the crossed recovery, as also follows from
the cross term $2hsY\sin a\sin b$ in $|Q|^2/4$.
Thus both signs of $b$ use an actual whole feedback with the
correct coherent orientation. Since
$4(\Gamma^2-\Gamma_{\mathrm{var}}^2)
=8\Gamma\mathcal M\varepsilon^2+O(\varepsilon^3)$,

$$
\Psi(t_*,\delta_*,\eta b,b)-N(\xi_*)
 =8\Gamma\mathcal M b^4+O(b^6).
\tag{49.33}
$$

Replacing the analytic ray by its tangent line changes $a$ by
$O(b^3)$. The quadratic form is $L_a(a-\eta b)^2$ at the zero;
there are no cubic phase terms. This replacement changes the
objective only by $O(b^6)$, justifying (49.33).

To eliminate the remaining stable directions set
$u_\delta=\delta-\delta_*$, $u_a=a-\eta b$ and
$\mathscr F(u_\delta,u_a,b)=
\Psi(t_*,\delta_*+u_\delta,\eta b+u_a,b)-N(\xi_*)$.
Its stable Hessian is

$$
\nabla^2_{(u_\delta,u_a)}\mathscr F(0)
 =\operatorname{diag}(H_*,8\Gamma L_a)>0.
\tag{49.34}
$$

The scalar--phase entries vanish by (49.25). The analytic implicit
function theorem applied to the **stable gradient only** gives a
unique graph $u_\delta^*(b),u_a^*(b)$; it does not assert that its
nonzero points are full critical points. The symmetry
$\mathscr F(u_\delta,-u_a,-b)=\mathscr F(u_\delta,u_a,b)$
makes the first graph even and the second odd. Its first derivatives
vanish at zero by the null Hessian, so
$u_\delta^*(b)=O(b^2)$ and $u_a^*(b)=O(b^3)$.

For the fixed critical value of $\eta$, write
$Q(\delta)=L_a(\delta)\eta^2+L_b(\delta)
-2s\sqrt{q(\delta)}\eta$, with $q=t_*-\delta$.
At $\delta_*$,

$$
Q=0,\quad Q'=K_\delta
 =\eta^2L_{a,\delta}+L_{b,\delta}
                      +s\eta/\sqrt q.
\tag{49.35}
$$

For example this follows by differentiating
$L_b-s^2q/L_a=D/L_a$; the stationary minimizing value
of $a/b$ has zero first variation at the critical point.
The cubic population coupling is therefore
$4\Gamma K_\delta u_\delta b^2$.
Together with (49.33)--(49.34) this yields

$$
u_\delta^*(b)=-\frac{4\Gamma K_\delta}{H_*}b^2+O(b^4),\qquad
\mathscr F(u_\delta^*(b),u_a^*(b),b)
 =\left(8\Gamma\mathcal M-
 \frac{8\Gamma^2K_\delta^2}{H_*}\right)b^4+O(b^6).
\tag{49.36}
$$

There is no additional transverse phase correction at fourth order,
because its optimizing displacement starts at degree three. Effects
were eliminated exactly on their full feasible arc in (49.23).
These facts account for every stable direction in the reduced phase
problem. Fixed-population positivity alone would be insufficient:
$F(b,z)=z^2/2+2zb^2+b^4$ has fixed-$z=0$ coefficient $+1$,
but minimizing over $z$ gives $-b^4$.

### 49.7. Rational sign certificate for the relaxed coefficient

The root rectangle implies $12/25<p,q<13/25$. Half-angle identities
and positive square comparisons give the following convenient bounds:

$$
\begin{gathered}
7/10<h<71/100,\quad92/100<c<93/100,\quad
38/100<s<39/100,\quad21/100<\gamma<23/100,\\
3/4<y<4/5,\quad69/100<\sqrt p,\sqrt q<73/100,\\
4/3<R<7/5,\quad1/2<C<3/5,\quad5/4<\Gamma<3/2,\\
256/1025<x^2/(1+x)<169/660.
\end{gathered}
$$

Substitution into $L_a$ gives $1/6<L_a<1/5$. To expose the
margins, the lower bounding expression is

$$
\frac7{10}\frac{256}{1025}
 \left[\frac{(21/100)(69/100)}{7/5}
                  +\frac{69/100}{4/5}\right]
 =\frac16+\frac{8527}{3843750},
$$

whereas $1/5$ minus the upper bounding expression
$(71/100)(169/660)[(23/100)(73/100)/(4/3)+(73/100)/(3/4)]$
equals $1199911/7920000000>0$.
It follows that

$$
13/10<\eta<7/4,\qquad \mu>8/25,\qquad j>2/5.
$$

For $\mu$, use $\mu=L_a/[2x^2/(1+x)]$; the resulting lower
bound exceeds $8/25$ by $23/4225$. For $j$, the bound
$(256/1025)(13/10)^2$ exceeds $2/5$ by $566/25625$.
Since $(L+j)^2/(4Lj)\ge1$, $x^2y^2\le1/4$, and $x+j>1$,
one has $\mathcal E>2$. Consequently

$$
\mathcal M>64/125,\qquad 8\Gamma\mathcal M>128/25.
\tag{49.37}
$$

To bound the subtraction, use
$L_a=a_0\sqrt p+a_1\sqrt q$ and
$L_b=\gamma\sqrt p+b_1\sqrt q$. Direct bounds on the same rectangle are

$$
\begin{gathered}
0<a_0<1/30,\quad1/5<a_1<1/4,\quad
0<a_{0,x}<1/9,\quad0<a_{1,x}<1,\\
7/25<b_1<7/20,\qquad0<b_{1,x}<7/5.
\end{gathered}
$$

Here
$a_{0,x}=a_0(2/x-1/(1+x)-h/R)$,
$a_{1,x}=a_1(2/x-1/(1+x)+x/y^2)$, and
$b_{1,x}=(h^2-s^2x)/(hy^3)$.
For the last upper bound it is necessary to retain the numerator
subtraction: it is bounded by
$[1/2-(38/100)^2(16/25)]/[(7/10)(3/4)^3]<7/5$.

Fixed-$t$ differentiation gives

$$
\begin{aligned}
L_{a,\delta}&=-\tfrac12(a_{0,x}\sqrt p+a_{1,x}\sqrt q)
       +\frac{a_0}{2\sqrt p}-\frac{a_1}{2\sqrt q},\\
L_{b,\delta}&=\frac\gamma{2\sqrt p}
       -\tfrac12b_{1,x}\sqrt q-\frac{b_1}{2\sqrt q}.
\end{aligned}
$$

Both are negative: $a_0/\sqrt p<a_1/\sqrt q$, and
$\gamma/(2\sqrt p)<1/6<b_1/(2\sqrt q)$.
Their magnitudes obey

$$
-L_{a,\delta}<73/180+25/138<3/5,\qquad
-L_{b,\delta}<511/1000+35/138<4/5.
$$

Moreover $s\eta/\sqrt q=s^2/L_a\in(2/3,1)$.
Equation (49.35) now gives

$$
-2<-\frac{49}{16}\frac35-\frac45+\frac23
 <K_\delta<1,\qquad |K_\delta|<2.
\tag{49.38}
$$

For the scalar curvature let $S=2\Gamma$ at $a=b=0$, differentiating
at fixed $t$ as before. The exact expression is

$$
S_{\delta\delta}=-\frac h{\sqrt p}
 -\frac R{2p^{3/2}}-\frac{h\sqrt q}{2y^3}
 -\frac{hx}{y\sqrt q}-\frac{hy}{2q^{3/2}}.
$$

The five positive magnitudes exceed respectively
$9/10,7/4,9/20,3/4,13/20$, whose sum is $9/2$.
For example direct substitutions give margins
$43/730$, $71/11388$, $111/5120$, $5/292$ and $197/4745$
above those five lower bounds. Scalar stationarity gives
$S_\delta=D_0/(2S)$; since $D_0<6$ and $S>5/2$, this lies in
$(0,6/5)$. Thus

$$
H_*=-2(S_\delta^2+SS_{\delta\delta})
 >2[(5/2)(9/2)-36/25]=981/50>18.
$$

Combining this with (49.38),

$$
\frac{8\Gamma^2K_\delta^2}{H_*}
 <\frac{8(3/2)^2\,2^2}{18}=4,
\qquad
\boxed{C_{\mathrm{eff}}>128/25-4=28/25.}
\tag{49.39}
$$

This is a rational certificate for the full relaxed difference, not
just for its fixed-population positive summand.

### 49.8. Controlled analytic remainder and all-effect local isolation

The stable graph and its reduced objective are analytic. Uniqueness
and the symmetry in Section 49.6 make the latter even. On a sufficiently
small closed interval $[-r_0,r_0]$ inside that analytic neighborhood,
Taylor's theorem gives the actual bound

$$
|\Phi_{\mathrm{red}}(b)-N(\xi_*)-C_{\mathrm{eff}}b^4|
 \le M_6|b|^6,\quad
M_6=\frac1{6!}\max_{|b|\le r_0}|\Phi_{\mathrm{red}}^{(6)}(b)|<\infty.
\tag{49.40}
$$

Fix that $M_6$ and shrink the interval so $M_6r^2\le C_{\mathrm{eff}}/2$.
This supplies a controlled, existential analytic neighborhood; no
specific numerical radius is claimed. By (49.34) and continuity,
the stable Hessian is uniformly positive definite on a smaller product
neighborhood. Taylor's integral formula along each stable-variable
segment from its graph gives a constant $c_s>0$ with

$$
\begin{aligned}
f(E,U)-N(\xi_*)\ \ge{}&
c_s\left[(u_\delta-u_\delta^*(b))^2
                 +(u_a-u_a^*(b))^2\right]
 +\frac{C_{\mathrm{eff}}}{2}b^4
 +\frac{49}{360}\epsilon(E).
\end{aligned}
\tag{49.41}
$$

The quantifiers are: every phase feedback (49.20) in that neighborhood,
and **every** $E\in\operatorname{Dens}_2$ satisfying the original
constraint $\rho(E,U)=\xi_*$. Equation (49.22) is what allows (49.23)
to pass from the pure reduced calculation to this all-effect statement.
It includes mixed effects and all coherence phases, without assuming
that the actual population is the pure endpoint.

Equality $f=N(\xi_*)$ first forces $b=0$ and both stable displacements
zero. The unique fixed-feedback minimizer in (49.23) then forces
$E=\widehat E$; purity alone would not fix its coherence phase.
Conversely these selected pairs attain equality. The two scalar orbits
are distinct, since $y_*>0$ and the last two selected entries fix the
common scalar. Compactness of that scalar circle and completeness of
the chart give a full phase feedback neighborhood of their union.
With $d_U$ exactly as in (43.1), bounded chart derivatives and
$u_\delta^*=O(b^2),u_a^*=O(b^3)$ also imply, on a smaller neighborhood,

$$
f(E,U)-N(\xi_*)\ge c\,d_U(U,\xi_*)^4
                         +\frac{49}{360}\epsilon(E),\qquad c>0.
\tag{49.42}
$$

Indeed the fourth power of the total coordinate displacement is bounded
by a constant times the two stable squares plus $b^4$ on a bounded
small ball. The displacement $d_U$ is auxiliary; (49.1) is the
prescribed distance throughout.

For the pure constructed effect the exact branches satisfy

$$
\rho_+=2(q+\delta)=\xi_*,\qquad
\rho_--\rho_+=2(1+2p+2x-2y)>0
\quad\text{at }a=b=0.
\tag{49.43}
$$

For example the root bounds make the expression in parentheses larger
than $1+24/25+32/25-8/5>0$. By continuity it stays positive for
the nearby pure constructions. Throughout the chosen neighborhood,
(49.22) and $t_-<0$ make the positive sign uniquely minimizing for
every effect at the prescribed level, hence the actual branch statements
used in (49.21)--(49.23). Both original distance branches, not just
a formal positive-branch constraint, are accounted for.

### 49.9. The actual right-side branches

Perform the stable-gradient elimination with $t$ also a parameter,
centered on the analytic selected graph $\delta_\circ(t)$.
The stable block remains invertible in a product neighborhood of
$(t_*,b=0)$. Write its reduced objective as $\Phi(t,b)$.
Its evenness gives an analytic function of $t$ and $u=b^2$.
Eliminating the quadratic transverse phase exactly by the Schur
complement of (49.25) gives

$$
\begin{aligned}
\Phi(t,b)-N(2t)&=A(t)b^2+C(t)b^4+R(t,b),\\
A(t)&=\frac{4\Gamma(t)}{L_a(t)}D_{\mathrm{sel}}(2t),\qquad
C(t_*)=C_{\mathrm{eff}},\\
|R(t,b)|&\le M|b|^6,\qquad
|C(t)-C_{\mathrm{eff}}|\le M|t-t_*|
\end{aligned}
\tag{49.44}
$$

on a smaller closed product neighborhood, for some finite $M$.
Analyticity supplies the corresponding derivative bounds as well.
There is no scalar--phase quadratic cross term, so population
elimination does not alter $A(t)$. Equation (49.13) implies
$A(t_*)=0$ and $A'(t_*)<0$.

The remaining full stationary equation away from $b=0$ is
$A(t)+2C(t)u+O(u^2)=0$. Its derivative in $u$ at $(t_*,0)$
is $2C_{\mathrm{eff}}>0$. Applying the implicit function theorem
to this equation, with its analytic remainder, gives the unique
nearby root

$$
u(t)=-\frac{A(t)}{2C_{\mathrm{eff}}}+O((t-t_*)^2).
\tag{49.45}
$$

Choose $\varepsilon>0$ small enough that $t\in(t_*,t_*+\varepsilon)$
implies $t<2$, all reconstructed coordinates remain in the chart
and in $\Omega$, $u(t)>0$, and $C(t)>0$.
Then $b_\pm(t)=\pm\sqrt{u(t)}$ are two distinct branches near
each orientation. Along them the reduced second derivative is
$8C_{\mathrm{eff}}u(t)+O(u(t)^2+|t-t_*|u(t))>0$.
The stable Hessian stays positive, so these are strict local minima
on the phase level, also among all effects by (49.23). Their values obey

$$
\Phi(t,b_\pm(t))-N(2t)
 =-\frac{A(t)^2}{4C_{\mathrm{eff}}}+O(|t-t_*|^3)<0.
\tag{49.46}
$$

Each branch uses its own single feedback (49.20) and its unique effect
(49.23), with $q=t-\delta(t,b_\pm(t))$. Thus its original distance
is exactly $2t$, with the negative distance strictly larger. This
is a same-level comparison with $N(2t)$, not with a displaced level.
The two signs of $b$ give different phase feedbacks modulo the common
scalar by local injectivity of the chart. The two base orientations
remain disjoint on a smaller neighborhood.
For $t<t_*$ sufficiently close, (49.45) has $u(t)<0$, so no real
nonzero branch of this local stationary equation exists. This is a
local assertion only; it does not exclude separated stationary points.

### 49.10. Suppliers, consumer and remaining original boundary

The load-bearing suppliers are the original normalized-effect and
same-feedback identities (23.9)--(23.12), the attained selector and
strict convexity of Theorem 37.5, the selected inequalities (41.4),
the exact phase chart and Hessian (43.2)--(43.14), the strict
same-feedback all-effect neighborhood of Theorem 40.4, and the coherent
triangle identity and five-term remainder (46.18)--(46.24).
The selector is always the positive geometric one. No assertion that
$V$ or $N$ is globally minimizing is used as a premise. The present
root system, monotonicity argument, rational certificates and relaxed
quartic calculation are explicit finite-dimensional deductions from
those suppliers. The analytic steps apply the ordinary real analytic
implicit function theorem with the positive invertible stable block
displayed in (49.34), followed by Taylor's theorem. No additional
literature theorem about synchronization or bifurcation is a premise,
and no literature-exhaustiveness or priority claim is made.

The original-domain consumer is (49.41)--(49.46): all normalized positive
effects at nearby **phase** feedbacks are included on the exact original
level; the zero remains locally isolated, and immediate right levels
have strict original competitors in both selected orientations. On the
left, Theorem 43.3 and the now proved firstness give phase local
isolation at every selected level $0<\xi<\xi_*$. The quartic result
adds the endpoint, so phase local isolation holds through $\xi_*$.
For $\xi_*<\xi<4$, the negative determinant and Theorem 36.5 supply
strict original competitors at each selected level. This last statement
does not require these competitors to be global minimizers.

The full first-loss/equality problem remains unresolved. In particular
the phase local result does not exclude a separated phase contact at an
earlier level, locate $\alpha$ or $\beta$, prove their equality, or
establish a global geometric-equality prefix ending at $\xi_*$. Global
purity alone from Theorem 45.5 does not fill these gaps.

For global minimizers, Theorem 48.5 of Continuation III supplies the
stronger statement
$\mathcal A_\xi=\mathcal A_{\mathrm{ph,p},\xi}=\mathcal E_\xi(a_\xi)$
for $0<\xi\le13/4$: every actual global minimizer is pure phase, with
all common scalar representatives retained. By (49.5),
$\xi_*<61/25<13/4$, so this result applies at the selected zero and
throughout a sufficiently small two-sided level neighborhood of it.
Thus no additional nonphase global-minimizing lift classification or
variance-zero lift condition remains to be proved on this interval.
The phase endpoint value $a_\xi$ and the set
$\mathcal E_\xi(a_\xi)$ remain unevaluated. Their full-level ordering
against the selected $V(\xi)$, including both signs, every population
and all attained phase configurations, is still required; neither
$N(\xi)$ nor $V(\xi)$ is assumed globally optimal.

Global phase rigidity does not classify arbitrary $U(4)$ local minima,
and no extension of that global theorem beyond $13/4$ is used. In
particular it does not exclude earlier separated phase contact or
settle the first-loss and equality questions above. The local minima
proved here remain minima on the phase feedback part of the original
level, including all effects there. This article makes no unrestricted
unitary local-minimum classification, no global equality completion,
and no claim about an empirical quantum origin, state preparation,
reset, dynamics or physical realization. These are paper proofs and
algebraic certificates; no Lean, kernel or digestion status is asserted.

## 追加锚（本行以下为增补区）

## 51. Positive-prefix population cost, recovery gain and complete pure equality

The objects are those of Definitions 1.1, 11.1 and 23.1 in the
[source volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md).
The scalar selector is Theorem 37.5 of
[Continuation I](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md).
The transport, triangle and gain statements numbered 42, 46, 47 and 50 are in
[Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md).
Theorem 48.5 is in
[Continuation III](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_III.md).
Throughout, $\xi_*$ is exactly the unique selected determinant zero of
Theorem 49.1, and $V(\xi)$ is the selected positive geometric value, rather
than a definition of the unrestricted minimum.

### 51.1. Original objects and the full-prefix statement

**Definition 51.1 (positive row on the original level).** Put

$$
h=1/\sqrt2,\quad c=\cos(\pi/8),\quad s=\sin(\pi/8),\quad
k=c-h,\quad d=2(h+c),\quad e=2(h+s).
\tag{51.1}
$$

The matrix $T=(b_+\ b_-)$ is the fixed certificate basis of the source,
and not a new optimizer. Every normalized pure original effect has the form

$$
\beta=\begin{pmatrix}\sqrt{1-q}\\e^{i\phi}\sqrt q\end{pmatrix},\qquad
E=(T\beta\beta^\dagger T^\dagger)^{\mathsf T},\qquad 0\le q\le1.
\tag{51.2}
$$

The superscript $\mathsf T$ is ordinary transpose. For the one actual
$U\in U(4)$ define $w=\operatorname{diag}(UU_+^\dagger)$ and

$$
\begin{aligned}
A&=\left|\sum_{j=1}^4w_j\right|,
&B&=|w_1-w_2+i(w_3-w_4)|,\\
P&=h(w_1+w_2)+c(w_3+w_4),
&Q&=h(w_1-w_2)+is(w_3-w_4).
\end{aligned}
\tag{51.3}
$$

These are the same-feedback quantities in (23.2), (23.9)--(23.12):

$$
\begin{aligned}
\rho_+&=8+2q-2A,&\rho_-&=10-2q-2B,&
\rho&=\min\{\rho_+,\rho_-\},\\
g(E,U)&=d^2(1-q)+e^2q
 -|\sqrt{1-q}P+e^{i\phi}\sqrt q Q|^2.
\end{aligned}
\tag{51.4}
$$

The ambient domain remains $\operatorname{Dens}_2\times U(4)$.
A scalar representative always acts on the entire feedback; there is
no separate column scalar or independently attainable recovery optimum.
For $\rho_+=\rho=\xi$, the feasible population interval is
$0\le q\le\min\{1,\xi/2\}$. Write $q_\xi$ for the unique interior
positive geometric selector of Theorem 37.5 and put

$$
\begin{gathered}
x=1-\xi/4+q/2,\quad y=\sqrt{1-x^2},\quad L=1+x,\quad
R=hx+c,\quad u=\sqrt{1-q},\quad v=\sqrt q,\\
\Gamma_0=uR+hvy,\qquad
C_\xi(q)=d^2(1-q)+e^2q-4\Gamma_0^2.
\end{gathered}
\tag{51.5}
$$

Thus $V(\xi)=C_\xi(q_\xi)$ and $C'_\xi(q_\xi)=0$.
For $x<1$ define exactly the positive row of (46.13), (47.1) and (50.3):

$$
\begin{aligned}
\mu&=\tfrac12\left(\frac{hku}{R}+\frac{hv}{y}\right),&
\nu&=\tfrac12\left(ku+\frac{(x/2-s^2)v}{hy}\right),\\
Z&=\frac{s^2qL}{x^2},&
\omega&=\nu-\frac Z{4\mu}
 =\frac{L\mathfrak D_+(x,q)}{4\mu x^2},\\
\eta&=\max\{0,-\omega\},&
K&=\frac{k^2u}{8R}+\frac{2svL}{3\sqrt3\,x},\qquad
J=\frac{\eta^2}{4K}.
\end{aligned}
\tag{51.6}
$$

Here $K=C_{\mathrm{gain},+}$; it is distinct from $C_\xi$, the trace
modulus $B$, and the ambient domain. On this nonsingular domain
$x,\mu,K$ are positive, including at $q=0,1$. Write
$\Omega(\xi,q)=\omega(1-\xi/4+q/2,q)$ and use $K(\xi,q)$ for the
same substitution in $K$.

**Theorem 51.2 (full positive-prefix cost and original-pair comparison).**
For every $0<\xi\le\xi_*$ and every feasible population with $x<1$,

$$
\eta(\xi,q)^2\le K(\xi,q)(q-q_\xi)^2.
\tag{51.7}
$$

This is the full-domain population-cost/gain relation T. For every
normalized pure original $E$ and every single original $U\in U(4)$
with $\rho_+(E,U)=\rho(E,U)=\xi$,

$$
g(E,U)-V(\xi)\ge\frac{23}{300}(q-q_\xi)^2.
\tag{51.8}
$$

Both population endpoints, every effect phase, arbitrary original
unitaries and the level $\xi=\xi_*$ are included. Equality $g=V$ holds
exactly at the following two geometric orientations and all their common
scalar representatives:

$$
\begin{gathered}
x_\xi=1-\xi/4+q_\xi/2,\qquad y_\xi=\sqrt{1-x_\xi^2},\\
\beta_\tau=\begin{pmatrix}\sqrt{1-q_\xi}\\-\tau i\sqrt{q_\xi}\end{pmatrix},
\qquad E_\tau=(T\beta_\tau\beta_\tau^\dagger T^\dagger)^{\mathsf T},\\
U_{\tau,\lambda}=\lambda\operatorname{diag}
 (x_\xi+\tau iy_\xi,x_\xi-\tau iy_\xi,1,1)U_+,
\qquad \tau\in\{-1,1\},\quad |\lambda|=1.
\end{gathered}
\tag{51.9}
$$

The two orientations are distinct modulo the one common scalar. The
selected root also satisfies the refined rational isolation

$$
                 \frac{59}{25}<\xi_*<\frac{239}{100}.
\tag{51.10}
$$

### 51.2. Continuous rational inequalities and their cover

The inequalities used below are over complete closed rectangles in the
coordinates $(\xi,q)$. A singleton argument denotes a degenerate interval.
The expression $C'$ is the derivative of $C_\xi$ in $q$ at fixed $\xi$,
and $\Omega_q$ likewise differentiates at fixed $\xi$, not along the
selected curve.

| Certificate | Expression | Closed $\xi$ interval | Closed $q$ interval | Continuous inequality | $n_{96}$ | $n_{128}$ |
| --- | --- | --- | --- | --- | --- | --- |
| P1 | $C'_\xi(q)$ | $\{239/100\}$ | $\{489/1000\}$ | $C'_\xi(q)\le -1/100$ | 1 | 1 |
| P2 | $C'_\xi(q)$ | $\{239/100\}$ | $\{491/1000\}$ | $C'_\xi(q)\ge 1/50$ | 1 | 1 |
| P3 | $\Omega(\xi,q)$ | $\{239/100\}$ | $[489/1000,491/1000]$ | $\Omega(\xi,q)\le -1/2000$ | 9 | 9 |
| P4 | $C'_\xi(q)$ | $\{21/10\}$ | $\{2/5\}$ | $C'_\xi(q)\le -1$ | 1 | 1 |
| P5 | $C'_\xi(q)$ | $\{9/4\}$ | $\{47/100\}$ | $C'_\xi(q)\ge 2/25$ | 1 | 1 |
| P6 | $\Omega(\xi,q)$ | $\{21/10\}$ | $[0,13/20]$ | $\Omega(\xi,q)\ge 1/1000$ | 36 | 36 |
| P7 | $\Omega(\xi,q)$ | $\{239/100\}$ | $[0,1/20]$ | $\Omega(\xi,q)\ge 1/100$ | 5 | 5 |
| P8 | $\Omega(\xi,q)$ | $\{239/100\}$ | $[1/2,159/200]$ | $\Omega(\xi,q)\ge 1/1000$ | 11 | 11 |
| P9 | $\Omega(\xi,q)$ | $\{239/100\}$ | $[1/20,1/4]$ | $\Omega(\xi,q)\ge -11/200$ | 31 | 31 |
| P10 | $K(\xi,q)$ | $[21/10,239/100]$ | $[1/20,1/5]$ | $K(\xi,q)\ge 1/10$ | 11 | 11 |
| P11 | $K(\xi,q)$ | $[21/10,239/100]$ | $[1/5,1/4]$ | $K(\xi,q)\ge 17/100$ | 2 | 2 |
| P12 | $K(\xi,q)$ | $[21/10,239/100]$ | $[1/4,1/2]$ | $K(\xi,q)\ge 19/100$ | 12 | 12 |
| P13 | $\Omega_q(\xi,q)$ | $[21/10,9/4]$ | $[1/4,47/100]$ | $0\le \Omega_q(\xi,q)\le 43/100$ | 197 | 409 |
| P14 | $\Omega_q(\xi,q)$ | $[9/4,239/100]$ | $[1/4,1/2]$ | $0\le \Omega_q(\xi,q)\le 43/100$ | 312 | 705 |

The columns $n_{96},n_{128}$ describe finite closed covers for two
interval evaluations of the same inequalities. Their totals are $630$
and $1235$. Exact rational endpoints, partition leaves and enclosure
numerators are specified in the private
[certificate source](https://github.com/the-omega-institute/trureturing-experiments/tree/d44a8f1bffeb02403b8fc596168c755ea1a017e5/experiments/auric/four-path/positive-prefix-population-gain-6aeb0aa2fba56a3ea8c3ca9c).
The correspondence is, in table order, `root_selector_left`,
`root_selector_right`, `root_determinant_negative`, `selector_lower`,
`selector_upper_low_slab`, `early_nonnegative`,
`small_population_nonnegative`, `upper_population_nonnegative`,
`negative_part_bound`, `gain_small`, `gain_middle`, `gain_large`,
`slope_low_slab`, `slope_high_slab`.

Here is the exact arithmetic specification of these finite certificates.
For the first evaluation let $S=2^{96}$ and enclose every rational
endpoint between its outward-rounded multiples of $1/S$. Addition and
negation are exact on this grid. For a product, form the four endpoint
products and round the least downward and greatest upward. For a
zero-excluding interval $[a,b]$, enclose its reciprocal using $[1/b,1/a]$
with outward rounding. For a square, the lower endpoint is zero when
the argument contains zero, and otherwise the lesser squared endpoint;
the upper is the greater squared endpoint. For a square root with
lower radicand $a/S$, the lower root is
$\lfloor\sqrt{aS}\rfloor/S$; the upper endpoint is the corresponding
integer root at the upper radicand, increased by one grid step unless
its square is exact. Radicands are nonnegative and every inverted
interval excludes zero. Start with

$$
h=\sqrt{1/2},\qquad c=\sqrt{(1+h)/2},\qquad
s^2=(1-h)/2,\qquad s=\sqrt{s^2}.
\tag{51.11}
$$

Evaluate (51.5)--(51.6), using $h^2=1/2$ as $x/2$ in $\nu$ and the
literal expression $s^2qL/x^2$ in $Z$. Each elementary interval
operation preserves inclusion. Consequently the image of each closed
leaf encloses the expression on that whole leaf, rather than at sample
points.

For precision about the cover, start with the exact rational rectangle
of each row. At a bisection choose the coordinate with greatest current
width divided by its initial width, ignore zero-width coordinates and
break ties by choosing $\xi$ first. Bisect at its rational midpoint.
The two closed halves meet at the cut and cover the parent. Each leaf
can therefore be described by a finite binary word, with 0 and 1
selecting the lower and upper half, respectively; `e` denotes an unsplit
rectangle. The listed leaves lie in their original rectangle, have
disjoint relative interiors, and have total exact relative volume equal
to the rectangle. These properties also justify cover without trusting
the generation tree: a nonempty complement of their finite closed union
would contain a relatively open set of positive relative volume, a
contradiction. Degenerate point domains have exactly one leaf. Thus all
boundaries and shared faces belong to the cover.

For the second evaluation, all arithmetic between square roots is exact
rational arithmetic, with square roots enclosed outward on the
$2^{-128}$ grid. First-order interval jets applied to the original
expression in (51.6) give $\Omega_q$. This derivative construction is
independent of the hand derivative formulas below. Each original leaf
is either accepted at its threshold or bisected by the same coordinate
rule until its subleaves satisfy the threshold; bisection preserves the
closed cover. The second count in the table includes these refinements.
All decisions are integer or rational inequalities.

For explicit expression correspondence, the hand derivative identities
used for the first evaluation are

$$
\begin{gathered}
x_q=1/2,\quad y_q=-x/(2y),\quad u_q=-1/(2u),\quad
v_q=1/(2v),\quad R_q=h/2,\\
\mu_q=\frac12\left\{
 hk\left[-\frac1{2uR}-\frac{hu}{2R^2}\right]
 +h\left[\frac1{2vy}+\frac{vx}{2y^3}\right]\right\},\\
\nu_q=\frac12\left\{-\frac k{2u}
 +\frac{v/4+(x/2-s^2)/(2v)}{hy}
 +\frac{(x/2-s^2)vx}{2hy^3}\right\},\\
Z_q=s^2\left[\frac L{x^2}+\frac q{2x^2}-\frac{qL}{x^3}\right],\qquad
\Omega_q=\nu_q-\frac{Z_q}{4\mu}+\frac{Z\mu_q}{4\mu^2},\\
C'_\xi=-(4h+8s)-4\Gamma_0
 \left[hu-\frac Ru+\frac{hy}{v}-\frac{hxv}{y}\right].
\end{gathered}
\tag{51.12}
$$

Only $0<q<1$ and $y>0$ are used in these derivative rows. The
nonderivative rows may include $q=0$; no derivative containing $1/v$
is evaluated there. The table's lower and upper rational bounds,
together with the inclusion rules and complete covers, give the
continuous inequalities required in the proof.

### 51.3. Analytic screens and the selected root refinement

*Proof of Theorem 51.2.* First reuse the fixed-$q$ calculation (50.14).
For $q>0$ and $0<x<1$ it gives

$$
\nu_x=\frac{v(h^2-s^2x)}{2hy^3}>0,\qquad
\frac{\mu_x}{\mu}\ge-\frac hR,\qquad
\partial_x\log(Z/\mu)
 \le\frac1L-\frac2x+\frac hR
 <\frac1L-\frac1x<0.
\tag{51.13}
$$

Thus $\omega_x>0$. At $q=0$, instead use
$\omega=k/2>0$ directly, with no logarithm of zero. At fixed $q$,
decreasing $\xi$ increases $x$; consequently each one-level lower
bound for $\Omega$ propagates to smaller levels wherever $x<1$.

The screen from Theorem 36.5 and Corollary 46.7 is

$$
          \mathfrak D_+(x,q)>0\qquad(4/5\le x<1,\ 0\le q\le1).
\tag{51.14}
$$

To state its algebraic correspondence explicitly, for $q<1$ put
$r=\sqrt{q/(1-q)}$ and

$$
a_0=\frac{hkx^2}{LR},\qquad a_1=\frac{hx^2}{Ly},\qquad
b_1=\frac{h^2x-s^2}{hy}.
$$

Then $\mathfrak D_+/(1-q)=(a_0+a_1r)(k+b_1r)-s^2r^2$.
For $x\ge4/5$ its constant and linear coefficients are positive,
and its quadratic coefficient is $n(x)/(Ly^2)$, where

$$
n(x)=(h^2+s^2)x^3-s^2(1+x),\qquad
n(4/5)=\frac{32-161s^2}{125}>0.
$$

Here $s^2<3/20$ and $n'(x)>0$ on $[4/5,1)$.
The same quadratic coefficient gives positivity at $q=1$ directly.
This computation never evaluates a $y$ denominator at $x=1$.

Rows P1--P2 and the strict scalar convexity of Theorem 37.5 put
$q_{239/100}$ strictly between $489/1000$ and $491/1000$.
Row P3 therefore gives $\Omega(239/100,q_{239/100})<0$.
The multiplier between $\omega$ and $\mathfrak D_+$ in (51.6)
is positive, so $D_{\mathrm{sel}}(239/100)<0$.
The unique zero and sign pattern in Theorem 49.1 now imply
$\xi_*<239/100$. Its lower bound $59/25$ is unchanged, proving
(51.10). This refines the existing unique root without selecting a
new root or changing its algebraic definition.

Rows P4--P5, selector uniqueness and the strict increase of $q_\xi$
in (49.11) give

$$
\begin{aligned}
q_\xi&>2/5&& (\xi\ge21/10),\\
q_\xi&<47/100&& (\xi\le9/4).
\end{aligned}
\tag{51.15}
$$

Also $q_{\xi_*}<1/2$ by (49.18)--(49.19), so $q_\xi<1/2$
through the whole prefix. Theorem 49.1 and (51.6) give

$$
                  \Omega(\xi,q_\xi)\ge0\qquad(0<\xi\le\xi_*).
\tag{51.16}
$$

Use P6 and (51.13) for $q\le13/20$, $\xi\le21/10$.
For the remaining $q\ge13/20$ at those levels,
$x\ge1-(21/10)/4+(13/20)/2=4/5$, so (51.14) applies.
Hence $\eta=0$ at every feasible nonsingular slice with
$\xi\le21/10$. Similarly P7 gives $\eta=0$ for $q\le1/20$
through the prefix. Row P8 covers $1/2\le q\le159/200$;
for larger $q$, (51.10) gives
$x>1-(239/100)/4+(159/200)/2=4/5$.
Thus $\eta=0$ for every $q\ge1/2$ in the prefix as well.
In the lower level slab $\xi\le9/4$, the existing C2 bound in
Section 50 gives $\Omega(9/4,q)\ge1/10000$ for $q\ge3/8$;
with (51.13) it in particular screens every $q\ge47/100$.
Each sign propagation uses monotonicity on the same population,
rather than assuming that a sign at one level holds elsewhere.

### 51.4. The complete population-cost/gain relation T

The preceding screens prove (51.7) whenever $\xi\le21/10$,
$q\le1/20$, or $q\ge1/2$, because $\eta=0$.
Consider $21/10\le\xi\le\xi_*$ and $1/20\le q\le1/4$.
Rows P9 and (51.13) give $\eta\le11/200$.
For $1/20\le q\le1/5$, (51.15) gives $q_\xi-q>1/5$,
and P10 gives

$$
\eta^2\le\frac{121}{40000}<\frac1{250}
             <K(q-q_\xi)^2.
\tag{51.17}
$$

For $1/5\le q\le1/4$, one has $q_\xi-q>3/20$, and P11 gives

$$
\eta^2\le\frac{121}{40000}<\frac{153}{40000}
             <K(q-q_\xi)^2.
\tag{51.18}
$$

At any shared boundary these strict estimates can be weakened to
nonstrict ones without changing the conclusion.

It remains to treat $q\ge1/4$. In the slab $[21/10,9/4]$,
$q\ge47/100$ has already been screened; in the slab
$[9/4,\xi_*]$, $q\ge1/2$ has already been screened.
The selected population is strictly inside the corresponding upper
population boundary by (51.15) and $q_\xi<1/2$.
Rows P13--P14 give, on both remaining closed rectangles,

$$
                       0\le\Omega_q\le43/100.
\tag{51.19}
$$

If $q\ge q_\xi$, (51.16) and (51.19) imply $\Omega(\xi,q)\ge0$,
so $\eta=0$. If $q<q_\xi$ and $\Omega(\xi,q)<0$, integration on
the fixed-$\xi$ segment from $q$ to $q_\xi$ gives

$$
\eta=-\Omega(\xi,q)
 \le\Omega(\xi,q_\xi)-\Omega(\xi,q)
 \le\frac{43}{100}(q_\xi-q).
\tag{51.20}
$$

Row P12 now yields

$$
\eta^2\le\frac{1849}{10000}(q-q_\xi)^2
 \le K(q-q_\xi)^2,
\qquad K\ge\frac{19}{100}=\frac{1900}{10000}.
\tag{51.21}
$$

If $\Omega(\xi,q)\ge0$, the same conclusion is immediate.
These regions cover the entire feasible nonsingular domain with all
shared boundaries. At $q=q_\xi$, both sides of (51.7) vanish,
including $\xi=\xi_*$. This proves T without a local-neighborhood
restriction or a sampling argument.

### 51.5. Curvature and the same-original-pair consumer

For the numerical constant in (51.8), use the scalar expression itself,
rather than only the weaker curvature constant 4 in (50.11). Put

$$
F_0=4(1-q)R^2,\qquad F_1=4qh^2y^2.
\tag{51.22}
$$

On the same fixed-$\xi$ feasible population interval they are nonnegative
and concave, since

$$
F_0''=(1-q)-8hR<0,\qquad F_1''=-4x-q<0.
\tag{51.23}
$$

The nonnegative geometric mean is concave and nondecreasing in both
arguments. Its concave-composition rule therefore makes
$\sqrt{F_0F_1}$ concave on this interval; endpoint zeros are included
by continuity. This is the standard composition statement in
Boyd and Vandenberghe, *Convex Optimization*, Section 3.2.4,
Example 3.14, applied to these two functions of the same population.
As $4\Gamma_0^2=F_0+F_1+2\sqrt{F_0F_1}$, in the population interior

$$
\begin{aligned}
C_\xi''&\ge-F_0''-F_1''
 =8hc+8x+2q-1\\
 &=8hc+7-2\xi+6q>\frac{183}{25}.
\end{aligned}
\tag{51.24}
$$

Here $hc>13/20$ and the existing bound $\xi_*<61/25$ suffice;
the sharper (51.10) is not needed for this constant. The elementary
radical comparison $hc>13/20$ follows by squaring
$(hc)^2=(1+h)/4$ with $h>7/10$.
Integration from the interior stationary selector and continuity at
all population endpoints give

$$
C_\xi(q)-V(\xi)\ge\frac{183}{50}(q-q_\xi)^2.
\tag{51.25}
$$

The gain/transport consumer (47.9)--(47.13), applied to the given
original pair, gives

$$
g(E,U)\ge C_\xi(q)-8\Gamma_0J-4J^2.
\tag{51.26}
$$

It includes every effect phase and arbitrary actual $U$. Its two
recovery amplitudes come from the same attained triangle and the same
whole feedback. More explicitly, the same-effect, same-complex-trace
transport of Theorem 42.3 preserves $q,x,\xi$ and the active sign in
every positive-weight phase replacement; (42.16) adds a nonnegative
recovery variance to their weighted defects. It therefore strengthens,
rather than weakens, (51.26) for the original $U$. No estimate from
separate recovery optima or from different objects is substituted.

Cauchy--Schwarz yields

$$
\Gamma_0^2\le R^2+h^2y^2=h^2+c^2+2hcx
 \le(h+c)^2<(5/3)^2.
\tag{51.27}
$$

For the last elementary inequality, $h<71/100$ and $c<93/100$
give $h+c<41/25<5/3$. Put $\Delta q=q-q_\xi$.
By T, $J\le(\Delta q)^2/4$. Since $q,q_\xi\in[0,1]$,
$4J^2\le(\Delta q)^4/4\le(\Delta q)^2/4$.
Combining (51.25)--(51.27) therefore gives

$$
g(E,U)-V(\xi)
 \ge\left[\frac{183}{50}-\frac{10}{3}-\frac14\right](\Delta q)^2
 =\frac{23}{300}(\Delta q)^2.
\tag{51.28}
$$

For $x=1$, use the direct original endpoint (47.11):

$$
U=\lambda U_+,\qquad \rho=\rho_+=2q=\xi,\qquad
\rho_-=8+2(1-q)>\xi,\qquad
g=e^2q=C_\xi(q).
\tag{51.29}
$$

Thus (51.25) alone gives the stronger coefficient $183/50$ at this
endpoint. No $y$ denominator from (51.6) is evaluated. This includes
$\xi=2,q=1$; the other $q=0,1$ cases lie in the already treated
nonsingular domain. Hence all required population and trace endpoints
are included, with the full open lower level boundary $0<\xi$ preserved.

### 51.6. Equality on the original positive-active pure branch

If $g=V$, the strictly positive coefficient in (51.8) forces
$q=q_\xi$. At that population $D_{\mathrm{sel}}\ge0$, including its
zero at $\xi_*$. The selector has $0<q_\xi<1$ and
$0<x_\xi,y_\xi<1$. Theorem 46.4 and Corollary 46.5 therefore apply
and give exactly (51.9). In detail, the same-effect,
same-complex-trace positive-weight transport must attain equality
termwise and have zero recovery variance. The nonzero effect
coordinates select one orientation; the nonzero active complex trace
fixes the same scalar in every replacement. The averaged diagonal
then has four entries of modulus one, and the row norms of the
actual unitary force all off-diagonal entries to vanish. Thus no
additional nonphase original lifts occur.

The equality assertion of Theorem 46.4 is unchanged when the determinant
is zero, so no enlarged equality family appears at $\xi_*$.
The $q=0$ block-lift alternative of Corollary 46.5 cannot occur because
$q_\xi$ is interior. Conversely, Theorem 37.5 and its actual-distance
identity (37.23) show that every pair in (51.9) has
$\rho_+=\rho=\xi$ and $g=V$. This proves both directions and completes
the proof of Theorem 51.2. $\square$

### 51.7. Source correspondence and the remaining global comparison

The new deduction relative to the fixed suppliers is the entire
positive-prefix relation T, its same-original-pair quantitative consumer,
the complete positive-active pure equality through the selected zero,
and the refinement (51.10). The source correspondences are:

| Supplier | Mathematical role |
| --- | --- |
| Original Definitions 1.1, 11.1, 23.1 and (23.2), (23.9)--(23.12) | Original domain, ordinary transpose, one-feedback $P,Q$, both distance branches and one common scalar |
| I Theorem 37.5 and (37.20)--(37.23) | Unique positive geometric selector, stationarity, attained $V$ and true-distance scalar equality |
| II Theorem 42.3 and (42.15)--(42.20) | Same-effect, same-complex-trace transport, true sign separation and nonnegative variance |
| II Definition 46.1, Theorem 46.4, Corollaries 46.5 and 46.7 | Joint attainable triangle, determinant identity, complete actual nonnegative-slice equality and $x\ge4/5$ screen |
| II (47.1), (47.9)--(47.13) | Recovery-gain envelope, original pure-input consumer and direct $x=1$ endpoint |
| II (50.3), (50.6), (50.14)--(50.15) and C2 | Positive-row parameters, scalar derivative, fixed-population monotonicity and existing upper-population screen |
| III Theorem 48.5 | Global-minimizer purity and phase rigidity through $13/4$ |
| IV Theorem 49.1, (49.11)--(49.19) | Unique selected zero and its sign, increasing selector and $q_{\xi_*}<1/2$ |

The ordinary mathematical suppliers are pinned by the published source
snapshot `6b6539921bf3fde0f84f85fdda6c284b5891ae98`.
The original and Continuations I--III agree with their corresponding
suppliers at `2c54932b6f9a7eb9a838e5be71e91d97e10027be`;
Section 49 agrees with its source at
`e6854b4057168ac0ffbbbc0b3e4e1468203de0f1`.
The results above are repo-derived ordinary mathematics with exact
rational interval certificates; no literature-wide priority or physical
realization claim follows.

For the standard composition premise see
[Boyd--Vandenberghe, *Convex Optimization*, Section 3.2.4, Example 3.14](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
Other mature optimization results have different hypotheses:
[Bandeira--Boumal--Singer, arXiv:1411.3272v3, Lemma 4.3](https://arxiv.org/html/1411.3272v3)
requires a feasible unit-diagonal positive semidefinite $X$, a Hermitian
positive semidefinite slack $S$ annihilating $X$, and $S+C$ real diagonal;
its uniqueness criterion uses $\operatorname{rank}S=n-1$.
No such dual certificate is constructed here for the coupled trace and
population family.
[Soltanalian--Stoica, arXiv:1303.0152v1, Theorem 2](https://arxiv.org/html/1303.0152v1)
requires an actual unimodular vector in the top eigenspace of the unchanged
Hermitian objective, and supplies no joint prescribed-trace/effect/population
conclusion for these objects.
[Nie, arXiv:1206.0319v2, Theorem 1.1](https://arxiv.org/html/1206.0319v2)
requires an archimedean polynomial model and constraint qualification,
strict complementarity and second-order sufficiency at every global
minimizer. Those global hypotheses are not established here, and the
selected degenerate zero does not justify assuming an ordinary strict
second-order certificate. These three results are therefore not proof
premises of Theorem 51.2.

There is no earlier separated pure contact in the positive-active branch
on $0<\xi\le\xi_*$. A negative-active pure phase pair could still have
smaller value or an additional equality at the same original level.
The negative canonical and interior comparison, both-sign assembly,
global equality, earliest global contact, $\alpha,\beta$, their possible
coincidence, endpoint inclusion for the global first-loss statement and
immediate right-side global classification remain unresolved here.
Theorem 48.5 is used only for its existing global-minimizer reduction;
a pointwise estimate for arbitrary mixed inputs does not follow.
No extension beyond $\xi_*$ or beyond that theorem's $13/4$ range is
asserted. Section 49's local quartic and right-side branch results retain
their own local scope. No native resources, complete AURIC reconstruction,
or Lean/kernel validation are asserted by this ordinary mathematical
positive-branch theorem.

## 追加锚（本行以下为增补区）

## 52. Strict negative attained-triangle comparison on the original level

**Definition 52.1 (negative population and common triangle).** Retain the
original $\mathcal K=\operatorname{Dens}_2\times U(4)$, ordinary transpose,
$g$, $f=g-\kappa\rho$, $\rho=\min\{\rho_+,\rho_-\}$, and exactly one
common feedback scalar. The matrices $T$, $U_+$ and $U_-$ are the fixed
objects of source Section 23. The constants $h,s,c,d,e$ are (49.2), and in
this section put $k_-=h-s>0$. The selected value $V=N+\kappa\xi$ is
exactly Theorem 37.5 of Continuation I, not a definition of a global
minimum. For a pure effect use the negative population

$$
\beta=\begin{pmatrix}e^{i\phi}\sqrt q\\\sqrt p\end{pmatrix},\qquad
p=1-q,\qquad E=(T\beta\beta^\dagger T^\dagger)^{\mathsf T},\qquad
q=(T^\dagger E^{\mathsf T}T)_{11}.
\tag{52.1}
$$

Thus this $q$ is distinct from the positive population in (51.2).
At the negative-active true original level $\xi$ set

$$
x=1-\xi/4+q/2,\qquad y=\sqrt{1-x^2},\qquad L=1+x,
\qquad 0\le q\le\min\{1,\xi/2\}.
\tag{52.2}
$$

For $0<x<1$ use precisely the negative row $(s,h,c,h)$ of
Continuation II, Definition 46.1 and Lemma 46.2. Its actual common
triangle and nonnegative half-amplitudes are

$$
\begin{aligned}
\mathcal T_x&=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\},\\
Z&=\frac{L^2-X-Y}{2\sqrt{XY}},\qquad
F=\sqrt{(1-X)(1-Y)}\sqrt{1-Z^2},\\
R^2&=s^2X+h^2Y+sh(L^2-X-Y),\\
C^2&=c^2(1-X)+h^2(1-Y)+2chF,\qquad
\Gamma=\sqrt p\,R+\sqrt q\,C.
\end{aligned}
\tag{52.3}
$$

Both amplitudes belong to this one triangle point and one whole phase
feedback. In particular $X,Y\ge x^2>0$, and $-1\le Z\le1$ follows
from $|\sqrt X-\sqrt Y|\le1<L\le\sqrt X+\sqrt Y$.
For every coherence phase, the original recovery modulus is at most
$2\Gamma$ by Lemma 46.2, so its actual $g$ is at least
$e^2p+d^2q-4\Gamma^2$. There is no substitution of independently
attained recovery extrema. Define the explicit comparison function

$$
H(\xi)=\frac\xi{25}+\frac{\xi^2}{24}.
\tag{52.4}
$$

**Theorem 52.2 (strict all-population negative comparison).** For every
$0<\xi\le61/25$, every feasible population in (52.2) with $x<1$,
and every point of the full closed triangle $\mathcal T_x$,

$$
e^2p+d^2q-4\Gamma^2>H(\xi)>V(\xi).
\tag{52.5}
$$

Every normalized pure original effect and every whole $U\in U(4)$
with $\rho_-(E,U)=\rho(E,U)=\xi$ in this interval satisfy

$$
                         g(E,U)>H(\xi)>V(\xi).
\tag{52.6}
$$

This includes $x=1$, both population endpoints, every effect phase,
all triangle edges and repeated-pair or zero-coherence cases. There is
no determinant-sign restriction. In particular it includes $\xi=\xi_*$
by (51.10), and excludes every negative-active pure equality on the
entire requested closed prefix.

*Proof.* The proof of the bound on $V$ is given first, followed by two
closed $x$ ranges and the original-unitary consumer.

### 52.1. A complete attained positive comparator below H

For $0<\xi\le61/25<4$, choose the unique $\zeta\in(0,2/3)$ with

$$
\xi=\Xi(\zeta)=\frac{4\zeta(4+3\zeta)}{2+3\zeta},\qquad
\Xi'(\zeta)=\frac{4(9\zeta^2+12\zeta+8)}{(2+3\zeta)^2}>0.
\tag{52.7}
$$

Existence and uniqueness follow from $\Xi(0)=0$, $\Xi(2/3)=4$ and
continuity. Set

$$
\bar x=1-\zeta,\quad \bar q=\frac{4\zeta}{2+3\zeta},\quad
\bar p=\frac{2-\zeta}{2+3\zeta},\quad
\bar y=\sqrt{\zeta(2-\zeta)}.
\tag{52.8}
$$

Here $\bar p+\bar q=1$, $1/3<\bar x<1$, $0<\bar q<2/3$,
$\bar p>1/3$, and $4(1-\bar x)+2\bar q=\xi$. Thus these data give an
actual positive geometric pair at the same original level, with
$\bar q\le\xi/2$. Explicitly its effect and feedback are (51.9) with
$q_\xi,x_\xi,y_\xi$ replaced by $\bar q,\bar x,\bar y$.
The positive distance is $\xi$, and direct source calculation gives

$$
\rho_--\rho_+=2(1+2\bar p+2\bar x-2\bar y)
                    \ge6-4\sqrt2>0.
\tag{52.9}
$$

For a direct verification, put $t_+=\xi/2$ and
$\delta_+=2(1-\bar x)$, so $\bar q=t_+-\delta_+$. Then
$1+2\bar p+2\bar x-2\bar y=5-2t_++\delta_+-2\bar y$.
Since $\delta_+-2\bar y=2-2(\bar x+\bar y)\ge2-2\sqrt2$
and $t_+\le2$, this proves (52.9), exactly the scalar-distance
calculation (37.23). This is the true minimum of both sign
distances with one common scalar, rather than just the positive branch
expression. The square roots obey

$$
\sqrt{\bar q}\,\bar y=2\zeta\sqrt{\bar p},\qquad
\sqrt{\bar p}(h\bar x+c)+h\sqrt{\bar q}\,\bar y
                =\sqrt{\bar p}[h(1+\zeta)+c].
\tag{52.10}
$$

Put $D=4(2hs+s^2-hc)=2(1-h)(1-2s)$. Substitution into the original
same-feedback objective yields

$$
\begin{aligned}
G_+&=\frac4{2+3\zeta}
 \bigl((2-\zeta)(h+c)^2+4\zeta(h+s)^2
                 -(2-\zeta)[h(1+\zeta)+c]^2\bigr)\\
&=\xi\,\frac{D+2hc\zeta+\zeta^2/2}{4+3\zeta},\\
\frac{H(\xi)-G_+}{\xi}
 &=\frac{P_H(\zeta)}{(4+3\zeta)(2+3\zeta)},\\
P_H(z)&=\left(\frac8{25}-2D\right)
 +\left(\frac{18}{25}+\frac83-3D-4hc\right)z
 +\left(\frac{84}{25}-6hc\right)z^2.
\end{aligned}
\tag{52.11}
$$

The elementary radical inequalities
$7/10<h<5/7$, $9/10<c$, and $3/8<s<31/80$ follow by squaring their
positive sides using $h^2=1/2$, $s^2=(1-h)/2$, $c^2=(1+h)/2$.
They imply $hc>63/100>14/25$, so the quadratic coefficient of $P_H$
is negative. Its endpoint values have the exact bounds

$$
\begin{aligned}
P_H(0)&=-\frac{92}{25}+4h+8(1-h)s
             >h-\frac{17}{25}>\frac1{50},\\
P_H(2/3)&=-\frac{884}{225}+8h+\frac{32}{3}(1-2h)s\\
&>\frac{46}{225}-\frac4{15}h>\frac{22}{1575}>0.
\end{aligned}
\tag{52.12}
$$

For the second line $1-2h<0$ makes $s<31/80$ the correct lower-bound
substitution. Concavity places $P_H$ above its positive endpoint chord.
Theorem 37.5 orders this actual member of its restricted family, so

$$
                     V(\xi)\le G_+<H(\xi).
\tag{52.13}
$$

The positive comparison population $\bar q$ is used only here and is
not the negative population $q$ of (52.1).

### 52.2. The complete small-x block

Feasibility gives

$$
x\ge\frac{39}{100},\qquad q\le2x-\frac{39}{50}.
\tag{52.14}
$$

On $39/100\le x\le407/1000$ put $Q_s=17/500$ and

$$
\begin{aligned}
R_s&=s\frac{407}{1000}+h,\qquad
C_s=\sqrt{(c^2+h^2)\left(2-\frac{(139/100)^2}{2}\right)},\\
A_s&=e^2-4R_s^2,\qquad B_s=d^2-4C_s^2.
\end{aligned}
\tag{52.15}
$$

Equation (46.21) gives $R\le sx+h\le R_s$. Also
$F\le\sqrt{(1-X)(1-Y)}$ implies
$C\le c\sqrt{1-X}+h\sqrt{1-Y}$; Cauchy--Schwarz and
$X+Y\ge L^2/2\ge(139/100)^2/2$ give $C\le C_s$.
Since $p,q\ge0$, this proves the same-point lower bound

$$
e^2p+d^2q-4\Gamma^2\ge\ell(q)
 =A_s+(B_s-A_s)q-8R_sC_s\sqrt{q(1-q)}.
\tag{52.16}
$$

Exact rational radical enclosures specified in Section 52.4 give

$$
R_s>4/5,\qquad C_s>1,\qquad B_s-A_s<4,\qquad
\ell(17/500)>2/5.
\tag{52.17}
$$

For $0<q\le Q_s<1/25$, one has $1-2q>9/10$ and
$\sqrt{q(1-q)}<1/5$. Therefore

$$
\ell'(q)=B_s-A_s-4R_sC_s\frac{1-2q}{\sqrt{q(1-q)}}
                    <4-\frac{72}{5}<0.
\tag{52.18}
$$

Continuity includes $q=0$. Since $q\le Q_s$ by (52.14),

$$
e^2p+d^2q-4\Gamma^2\ge\ell(Q_s)>\frac25
 >\frac{1037}{3000}=H(61/25)\ge H(\xi).
\tag{52.19}
$$

This treats every triangle edge in the small-$x$ block, without a
positive-population or determinant assumption.

### 52.3. The population chord and the joint matrix on the remaining block

Let $407/1000\le x<1$ and $t=1-x\in(0,593/1000]$. The full triangle
is the image of the closed square $0\le a,b\le1$ under

$$
r=\sqrt X=1-ta,\qquad z=\sqrt Y=1-tv,\qquad v=(1-a)b.
\tag{52.20}
$$

To prove coverage, $r,z\ge x$ and $r+z\ge1+x$ give
$a=(1-r)/t\in[0,1]$, $v=(1-z)/t\ge0$ and $a+v\le1$.
For $a<1$ take $b=v/(1-a)$; for $a=1$, necessarily $v=0,z=1$
and any $b$ represents the boundary. Conversely $a+v\le1$ gives
the triangle constraint. Thus no triangle boundary is removed.

The feasible populations obey $q\le Q_p(t)$, where

$$
\begin{aligned}
Q_p(t)&=\min\{1,61/50-2t\},\qquad h_0=4/25+2t/3,
 &H_0&=th_0,\\
\delta&=2/25+2t/3+Q_p/6,
 &A_0&=e^2-H_0,\quad B_0=d^2-H_0-\delta.
\end{aligned}
\tag{52.21}
$$

Here $\delta$ is a chord coefficient, not the selected scalar argument
of Section 49. Its two polynomial expressions are

$$
\delta=\begin{cases}
37/150+2t/3,&0\le t\le11/100,\\
17/60+t/3,&11/100\le t\le593/1000.
\end{cases}
\tag{52.22}
$$

Since $\xi=4t+2q$, direct expansion gives the exact chord identity

$$
H_0+\delta q-H(4t+2q)=\frac{q(Q_p-q)}6\ge0.
\tag{52.23}
$$

For the actual same-point $R,C$ put

$$
M=\begin{pmatrix}A_0-4R^2&-4RC\\-4RC&B_0-4C^2\end{pmatrix}.
\tag{52.24}
$$

Then

$$
e^2p+d^2q-4\Gamma^2-H(\xi)
 \ge (\sqrt p,\sqrt q)M(\sqrt p,\sqrt q)^{\mathsf T}.
\tag{52.25}
$$

The vector on the right never vanishes, including $q=0,1$. To prove
positive definiteness, use the following polynomials in $(t,a,b)$:

$$
\begin{aligned}
\mathfrak r={}&4sh-2sk_-a+2hk_-v
       -t[sh-sk_-a^2+hk_-v^2],\\
W={}&4\mathfrak r-h_0,\\
C_b={}&c^2a(2-ta)+h^2v(2-tv),\\
N_b={}&(1-a)^2ab(1-b)(2-ta)(2-tv)\\
 &\hspace{8mm}\cdot[4-t(1+a+v)][(2-t)^2-t^2(a-v)^2],\\
P_b={}&WB_0-4A_0C_b,\\
Q_b={}&r^2z^2P_b^2-16A_0^2c^2h^2tN_b.
\end{aligned}
\tag{52.26}
$$

All factors of $N_b$ are nonnegative on the closed parameter boxes,
and $r,z\ge407/1000>0$. For example $a+v\le1$ gives
$4-t(1+a+v)\ge4-2t>0$ and
$(2-t)^2-t^2(a-v)^2\ge4-4t>0$.
Substitution into (52.3), with nonnegative roots, gives exactly

$$
\begin{aligned}
R^2&=(h+s)^2-t\mathfrak r,\\
F&=\frac{t^{3/2}\sqrt{N_b}}{2rz},\\
C^2&=t\left(C_b+\frac{ch\sqrt{tN_b}}{rz}\right),\\
M_{11}&=tW,\qquad
\frac{\det M}{t}=P_b-\frac{4A_0ch\sqrt{tN_b}}{rz},\\
Q_b&=r^2z^2\left[P_b^2-
       \left(\frac{4A_0ch\sqrt{tN_b}}{rz}\right)^2\right].
\end{aligned}
\tag{52.27}
$$

For the formula for $F$, factor its triangle discriminant as
$[(r+z)^2-L^2][L^2-(r-z)^2]$ and use
$1-a-v=(1-a)(1-b)$. This also checks the radical and its sign on
every boundary. The determinant formula follows by cancellation of
the two $16R^2C^2$ terms in the determinant of (52.24).

The finite rational certificate in Section 52.4 proves, on both full
closed boxes,

$$
A_0>4,\qquad W>12/5,\qquad B_0>49/5,\qquad
P_b>1/10,\qquad Q_b>3/500.
\tag{52.28}
$$

In particular the radical on the last line of (52.27) is nonnegative.
The simultaneous signs $P_b>0$ and $Q_b>0$ show that $P_b$ exceeds
that radical, rather than its negative. Consequently $\det M>0$
and $M_{11}>0$ for every $t>0$. The two-dimensional Sylvester criterion
makes $M$ positive definite. Equation (52.25) is therefore strict.
The certificate includes $t=0$ for polynomial closure, but no division
by $t$ or strict matrix assertion is used there.

### 52.4. Exact continuous-domain certificate

The certificate is the finite pair of complete binary trees in
[the exact-rational certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/014b9c9e939cc6979ef80769c4ded6dec91eb1ff/experiments/auric/four-path/negative-attained-triangle/certificate.json).
Their ordered root boxes, in coordinates $(t,a,b)$, are

$$
[0,11/100]\times[0,1]^2,\qquad
[11/100,593/1000]\times[0,1]^2.
\tag{52.29}
$$

The leaf symbol is the integer $1$. An internal node
$[j,T_\ell,T_r]$, with $j\in\{0,1,2\}$, replaces the $j$th interval
$[l_j,u_j]$ by $[l_j,(l_j+u_j)/2]$ and
$[(l_j+u_j)/2,u_j]$, respectively. Induction on this definition proves
that the leaves cover each entire closed root, including shared
boundaries. The two trees have $2385$ leaves, $4768$ nodes and maximum
depth $20$. The complete leaf data are the trees themselves, rather
than a sample mesh or a list of numerical test points.

Here is the arithmetic specification that turns those finite data into
a proof on the continuous domain. All interval endpoints are exact
rational numbers. For $[l,u]+[l',u']$ use $[l+l',u+u']$; negation
reverses endpoints. A product uses the minimum and maximum of the four
endpoint products. A reciprocal uses $[1/u,1/l]$ only when zero is
excluded. An even power has lower endpoint zero if its interval
contains zero, otherwise the smaller endpoint power; an odd power is
monotone. To bracket the square root of a nonnegative rational $v$,
put $S=10^{40}$ and

$$
k(v)=\left\lfloor\sqrt{\left\lfloor vS^2\right\rfloor}\right\rfloor.
\tag{52.30}
$$

Its lower bracket is $k(v)/S$, and its upper bracket is the same
number if its square equals $v$, otherwise $(k(v)+1)/S$. Squaring
these rational endpoints proves inclusion. Apply this to interval
endpoints and construct

$$
h=\sqrt{1/2},\qquad s=\sqrt{(1-h)/2},\qquad
c=\sqrt{(1+h)/2},\qquad e^2=4(h+s)^2,\quad d^2=4(h+c)^2.
\tag{52.31}
$$

Each enclosure contains the exact dependent constants; interval
arithmetic permits their occurrences to vary independently only to
enlarge the enclosure. It never asserts their independent realizability.

On each leaf evaluate the four polynomials
$(W,B_0,P_b,Q_b)$ from (52.21)--(52.22), (52.26). When their natural
intervals are not all positive, intersect each natural enclosure with

$$
f(m)+\sum_{j=0}^2([l_j,u_j]-m_j)\,\partial_jf(\mathcal B),\qquad
m_j=(l_j+u_j)/2,
\tag{52.32}
$$

where $\mathcal B$ is that leaf box. Exact polynomial differentiation
uses the sum, product and power rules. For each fixed choice of the
true constants, the mean-value integral along the line from $m$ to a
point of $\mathcal B$ proves (52.32). Its interval evaluation therefore
contains all values of that polynomial on the entire leaf. Intersecting
two enclosures preserves inclusion. The finite inequalities obtained
for every leaf are

$$
(W,B_0,P_b,Q_b)>(12/5,49/5,1/10,3/500)
\quad\hbox{coordinatewise}.
\tag{52.33}
$$

The accompanying
[exact arithmetic source and rational bounds](https://github.com/the-omega-institute/trureturing-experiments/tree/014b9c9e939cc6979ef80769c4ded6dec91eb1ff/experiments/auric/four-path/negative-attained-triangle)
specify all operations and the achieved rational leaf bounds. The
inequality $A_0>4$ follows by the same outward radical brackets and the
monotonicity of $H_0=4t/25+2t^2/3$, evaluated at $t=593/1000$.
The auxiliary evaluations are (52.17), $H(61/25)=1037/3000<2/5$,
and the endpoint signs of (52.11). Thus the certificate-to-mathematics
correspondence is precisely (52.20), the population chord (52.23),
and the identities (52.25)--(52.27), with the two polynomial branches
specified by (52.22). A finite continuous enclosure proves each sign;
no optimizer output or failure to find a counterexample supplies one.

### 52.5. Scalar endpoint and arbitrary whole feedback

If $x=1$, use the direct endpoint (47.11):
$U=\lambda U_-$, $\xi=2q>0$ and $g=d^2q$. Since $q\le1$,

$$
H(2q)=\frac{2q}{25}+\frac{q^2}{6}
              \le\frac{37q}{150}<d^2q.
\tag{52.34}
$$

No singular coefficient containing $1/y$ is evaluated.
For $x<1$, Sections 52.2--52.4 cover every feasible $x$ and the
complete triangle, so Lemma 46.2 gives (52.6) for every phase feedback
and every effect phase.

For an arbitrary original whole $U$, apply Continuation II, Theorem
42.3 and the variance identity (42.16), exactly as in Theorem 47.3.
The finite phase replacements retain the same $E$, the same complex
negative active trace, and hence the same $q,x$ and active distance.
Because $\xi\le61/25<13/4$, the two-sign separation (42.17)--(42.20)
makes that distance the true $\rho$ and the negative sign uniquely
active for every replacement. With nonnegative weights summing to one,

$$
g(E,U)=\sum_j\theta_jg(E,U_j)+\mathcal V,\qquad
\mathcal V\ge0.
\tag{52.35}
$$

Every positive-weight term is strictly greater than the same
$H(\xi)$, so (52.35) is strictly greater too. This proves (52.5)--(52.6).
It is a pure-input assertion and uses no purification of an arbitrary
mixed input. $\square$

**Corollary 52.3 (strict attained joint-gain comparison).** For the full
nonsingular domain of Theorem 52.2 define

$$
\begin{aligned}
\Gamma_0&=\sqrt p(sx+h)+\sqrt q\,c\sqrt{1-x^2},\\
G_{\mathrm{can}}&=e^2p+d^2q-4\Gamma_0^2,\qquad
I_- =\max_{(X,Y)\in\mathcal T_x}(\Gamma-\Gamma_0).
\end{aligned}
\tag{52.36}
$$

Then, including every slice with $\mathfrak D_-<0$,

$$
G_{\mathrm{can}}-V(\xi)-8\Gamma_0I_- -4I_-^2
                         >H(\xi)-V(\xi)>0.
\tag{52.37}
$$

*Proof.* By (47.1) the actual triangle is compact and
$XY\ge x^2>0$ makes $\Gamma$ continuous there. The maximum in (52.36)
is therefore attained. At a maximizing point
$\Gamma=\Gamma_0+I_-$. Apply (52.5) at this point and expand its square
to obtain (52.37). Strictness is retained because this is an attained
maximum, not an unattained supremum. No uniform positive margin as
$\xi\downarrow0$ is asserted. $\square$

## 53. The original global prefix, first boundaries and emerging minimizers

**Theorem 53.1 (global value and exhaustive equality through the first zero).**
On the unchanged original domain, for every $0<\xi\le\xi_*$,

$$
\min_{\rho(E,U)=\xi}g(E,U)=V(\xi),\qquad m(\xi)=N(\xi),\qquad
\mathcal A_\xi=\mathcal G_\xi.
\tag{53.1}
$$

The equality set consists exactly of (51.9), with both orientations
and every common scalar representative. Thus every original pair on
that level obeys $g\ge V$, or equivalently $f\ge N$, and equality
occurs precisely in that set. All mixed inputs, arbitrary whole
unitaries and the endpoint $\xi=\xi_*$ are included.

*Proof.* The level is nonempty by the actual geometric attainment in
Theorem 37.5. It is a closed subset of the compact original domain,
and $f,g,\rho$ are continuous, so a global minimizer exists. Since
$\xi\le\xi_*<239/100<13/4$, Theorem 48.5 of Continuation III applies
to this attained minimizer: it is pure and phase, with the actual
minimizing sign and the original common scalar. This is a statement
about a global minimizer; it has not changed an arbitrary mixed pair
or its distance.

If its sign were negative, (52.6) would give $g>V$, whereas the
selected positive geometric pair at the same true level has $g=V$.
This contradicts minimality. The minimizer is therefore positive-active.
Theorem 51.2 gives $g\ge V$, and the same selected pair gives the
reverse inequality for the minimum. Hence its value is exactly $V$,
and $f=g-\kappa\xi$ gives $m=N$. Theorem 51.2 now identifies every
minimizer with (51.9). Conversely every such pair attains this value
at true distance $\xi$. The effects in (51.9) equal those in (39.2),
since $(\psi\psi^\dagger)^{\mathsf T}
=\overline\psi\,\overline\psi^{\dagger}$ and $\psi=T\beta_\tau$.
Thus the set is exactly $\mathcal G_\xi$.

Finally any original pair with $g=V$ is itself a global minimizer and
is subject to the preceding argument. Every pair outside that set has
strictly larger value, including every mixed effect. This proves the
all-input conclusion without a pointwise purification inequality.
$\square$

**Theorem 53.2 (evaluated first-loss boundaries and endpoint inclusion).**
For the exact original sets and boundaries in (39.3),

$$
\mathcal B=\mathcal S=(\xi_*,4),\qquad
\alpha=\beta=\xi_*,\qquad
\xi_*\notin\mathcal B\cup\mathcal S.
\tag{53.2}
$$

Consequently the maximal initial positive-distance prefix with
exhaustive geometric equality is $(0,\xi_*]$. There is no separated
additional minimizing contact at its endpoint. At every
$\xi_*<\xi<4$ the original minimum is strictly below $N(\xi)$,
and every global minimizer is nongeometric.

*Proof.* Theorem 53.1 excludes both $\mathcal B$ and $\mathcal S$ on
$(0,\xi_*]$, including the endpoint. For every $\xi_*<\xi<4$,
Theorem 49.1 gives $D_{\mathrm{sel}}(\xi)<0$. At the selected
interior scalar point $x,y,p,q>0$, the true-distance calculation
(37.23) gives $1+2p+2x-2y>0$. These are exactly the hypotheses of
Theorem 36.5 of Continuation I. It supplies an actual rank-one effect
and actual phase feedback at this same true original level with
$f<N(\xi)$. This is also the strict competitor consequence stated in
Section 49.10; no global status for that competitor is required.
Therefore $m(\xi)<N(\xi)$ and $\xi\in\mathcal S\subseteq\mathcal B$.
Both sets are defined inside $(0,4)$, proving their exact values in
(53.2), and taking their infima proves $\alpha=\beta=\xi_*$.
The maximal-prefix and endpoint assertions follow directly from
(53.1)--(53.2). A global minimizer above the boundary cannot be
geometric because all pairs in $\mathcal G_\xi$ have value $N(\xi)$.
No identification of an infimum with a zero has been assumed.
$\square$

**Theorem 53.3 (complete immediate-right global branch classification).**
There is $\varepsilon>0$, with $\xi_*+\varepsilon<61/25$, such that
for every $\xi\in(\xi_*,\xi_*+\varepsilon)$ the complete actual
global minimizing set consists of the four common-scalar orbits
constructed in (49.20), (49.23), (49.45): two signs of $b$ near each
of the two selected orientations. They have the same value. In
particular these local phase branches are global on this neighborhood;
this assertion does not classify arbitrary-unitary local minima.

More explicitly, put $t=\xi/2$, $t_*=\xi_*/2$. Let $u(t)$ be the
unique positive root in (49.45), let $b_\pm(t)=\pm\sqrt{u(t)}$, and
let $\delta(t,b),a(t,b)$ be the unique stable-gradient graph of
Section 49.9, expressed in its complete chart. For each
$\tau\in\{-1,1\}$ and each choice $b=b_\pm(t)$ take
$U=\lambda\operatorname{diag}(w_\tau(\delta(t,b),a(t,b),b))U_+$
from (49.20), and the unique aligning effect $\widehat E$ from (49.23).
These, for all $|\lambda|=1$, are exactly $\mathcal A_\xi$. Their
common value has the expansion

$$
\begin{aligned}
m(2t)-N(2t)&=-\frac{A(t)^2}{4C_{\mathrm{eff}}}
                         +O(|t-t_*|^3),\\
A(t)&=\frac{4\Gamma(t)}{L_a(t)}D_{\mathrm{sel}}(2t),\qquad
A(t_*)=0,\quad A'(t_*)<0,\quad C_{\mathrm{eff}}>28/25.
\end{aligned}
\tag{53.3}
$$

Every global minimizing sequence as $\xi\downarrow\xi_*$ converges
in distance to $\mathcal G_{\xi_*}$; both selected orientations are
actual limits of these branches.

*Proof.* First localize all global minimizers, without assuming that
any local branch is global. Given any open neighborhood $\mathcal O$
of $\mathcal G_{\xi_*}$ in the compact original domain, suppose there
were levels $\xi_n\to\xi_*$ and global minimizers
$X_n\notin\mathcal O$. Compactness gives a subsequence with limit $X$.
Continuity gives $\rho(X)=\xi_*$, and the geometric competitors give

$$
f(X)=\lim_n m(\xi_n)\le\lim_n N(\xi_n)=N(\xi_*).
\tag{53.4}
$$

Theorem 53.1 forces equality and $X\in\mathcal G_{\xi_*}$, a
contradiction since the complement of $\mathcal O$ is closed. Thus all
minimizers lie in any prescribed sufficiently small neighborhood at
nearby levels. The same argument, or a shrinking-neighborhood
contradiction, proves convergence in distance to this compact set.

Choose the neighborhood small enough for the complete phase charts
(43.2), all strict sign and feasibility conditions of Section 49.5,
the unique fixed-feedback effect (49.23), and the stable-gradient
elimination in Section 49.9. Shrink the level interval so that it lies
below $61/25<13/4$. Theorem 48.5 makes every global minimizer pure
phase; (52.6) and $m\le N$ exclude a negative-active one there.
Hence it has positive phase coordinates in one of these two charts.
It must use the unique fixed-feedback minimizing effect (49.23),
otherwise that effect would strictly improve it at the same level.
Its remaining phase coordinates minimize the analytic $\Psi$ in
(49.24) in an open coordinate neighborhood, so its full gradient
vanishes.

The stable-gradient implicit function theorem has a unique graph in
a fixed smaller product neighborhood. Thus every such stationary
point lies on that graph and satisfies the reduced equation
$\partial_b\Phi(t,b)=0$. The exact even symmetry gives either $b=0$
or

$$
A(t)+2C(t)b^2+O(b^4)=0.
\tag{53.5}
$$

The left side is analytic in $(t,u=b^2)$ with $u$ derivative
$2C_{\mathrm{eff}}>0$ at $(t_*,0)$. On a smaller fixed neighborhood
that derivative stays positive. Its unique zero is precisely $u(t)$
of (49.45). This excludes additional nearby stationary roots as well
as merely constructing the two roots. The $b=0$ stationary point is
the selected geometric pair and has value $N(2t)$, while (49.46)
provides a strictly smaller actual value for every $t>t_*$ sufficiently
close. A global minimizer cannot have $b=0$. It is consequently one
of the four displayed branches.

There is no unproved equality of separately optimized values here.
The exact chart identities (49.20) show that $|P|$, $|Q|$ and the
reduced objective are independent of the orientation $\tau$.
The exact symmetry $(a,b)\mapsto(-a,-b)$ in (49.24)--(49.25), together
with uniqueness of the stable graph, makes the objective even in $b$.
All four actual branches therefore have the same value. At least one
is a global minimizer by attainment and the preceding exhaustive
localization; equality of their values makes all four global. Local
injectivity of the chart separates the two signs of $b$, and the
neighborhoods of the two endpoint scalar orbits are disjoint. Thus
there are exactly four orbits. Formula (49.46) now becomes the global
value expansion (53.3). The branch coordinates tend to their selected
base coordinates, proving attainment of both limiting orientations.
$\square$

**Definition 53.4 (scope and mathematical dependencies).** The new
negative comparison uses the original identities of source Section 23,
the restricted positive attainment of Continuation I, Theorem 37.5,
the same-effect forward transport of Continuation II, Theorem 42.3,
the common triangle of Lemma 46.2 and the compactness and endpoint
identities of Section 47. The positive comparator construction is
fully proved in (52.7)--(52.13); no unproved negative-canonical estimate
is a premise. The continuous-domain deduction uses Cauchy--Schwarz,
a quadratic chord, the two-dimensional Sylvester criterion and the
interval mean-value formula as intermediate standard facts. This is
a repo-derived synthesis, without a literature-wide priority claim.
The finite doubly stochastic permutation decomposition is used only
through the existing forward spectral transport of Theorem 42.3;
no converse normal-orbit assertion or exact semidefinite relaxation
is required.

The global consumer uses exactly Theorem 48.5 of Continuation III,
Theorem 51.2, the new Theorem 52.2, attainment and compactness. Its
first-boundary statement additionally uses the strict original
competitors of Theorem 36.5 with the selected sign and crossing proved
in Theorem 49.1. Its immediate-right classification additionally uses
the complete local chart, unique all-effect minimization and analytic
stationary equations (49.20)--(49.25), (49.44)--(49.46).
Thus the earlier unresolved prefix, endpoint and first-boundary
questions in Sections 49.10 and 51.7 and Continuation III, Definition
49.2 have the exact answers (53.1)--(53.3) on the stated ranges.
Their previously proved conditional and local statements retain their
hypotheses.

The global minimizing phase endpoint value and all minimizing orbits
away from the existential immediate-right neighborhood remain to be
evaluated. Theorem 53.2 gives strict loss on $(\xi_*,4)$, not a
complete description of the minimizing branches on that interval.
No extension of purity or phase rigidity beyond $13/4$, no global
classification at distance four or at larger original levels, and no
classification of arbitrary-unitary local minima follows. The zero
level retains its existing optimizer classes. Physical realization,
whole-POVM acquisition, and a complete reconstruction of AURIC are not
consequences of these fixed-domain mathematical results.

## 追加锚（本行以下为增补区）


## 54. An attained obstruction to the enlarged H comparison

**Theorem 54.1 (two strict original-level comparisons at thirteen-fourths).**
There are original pure pairs $W_-=(E^{(-)},U^{(-)})$ and
$W_+=(E^{(+)},U^{(+)})$ in
$\operatorname{Dens}_2\times U(4)$ such that

$$
\begin{gathered}
\rho(W_-)=\rho_-(W_-)=\frac{13}{4}<\rho_+(W_-),\qquad
\rho(W_+)=\rho_+(W_+)=\frac{13}{4}<\rho_-(W_+),\\
g(W_+)<\frac{5081}{10000}<\frac{13}{25}
       <g(W_-)<\frac9{16}<\frac{5473}{9600}=H(13/4).
\end{gathered}
\tag{54.1}
$$

Consequently the first inequality of (52.5) cannot hold on the whole
extension $61/25<\xi\le13/4$. The exhibited negative-active pair is
strictly worse than an actual positive-active pair at its true original
level, so it is not a global minimizing counterexample to positive-sign
selection.

*Proof.* Use precisely the fixed rows of Continuation II, Definition
46.1. The populations below are always away from the indicated sign:

$$
\begin{array}{c|c|c|c|c|c}
\sigma&q&p&x&X&Y\\ \hline
-&1/5&4/5&23/80&1/4&17/20\\
+&3/5&2/5&39/80&7/25&97/100.
\end{array}
\tag{54.2}
$$

In both rows $4(1-x)+2q=13/4$. The negative row satisfies
$\sqrt X+\sqrt Y>1/2+9/10>103/80=1+x$.
For the positive row,
$\sqrt X>13/25$, $\sqrt Y>49/50$, and
$13/25+49/50=3/2>119/80=1+x$.
Both rows therefore belong to the actual closed triangle, strictly
inside its curved boundary; $0<X,Y<1$.

Here is an explicit original realization, including the fixed labels.
In each row let $r=\sqrt X$, $z=\sqrt Y$, let $Z$ be (46.11), and
choose $\alpha=\arccos Z\in(0,\pi)$. In its fixed pair order set

$$
(v_j)_{j\in J}=e^{i\alpha}
       (r+i\sqrt{1-X},r-i\sqrt{1-X}),\qquad
(v_j)_{j\in K}=(z+i\sqrt{1-Y},z-i\sqrt{1-Y}),\qquad
U^{(\sigma)}=\operatorname{diag}(v)U_\sigma.
\tag{54.3}
$$

Thus $(J,K)=((3,4),(1,2))$ in the negative row and
$((1,2),(3,4))$ in the positive row. No physical labels are permuted.
The orientation in (54.3) has positive sign product and
$\sin\alpha>0$, so Lemma 46.2 gives both $|M|=2R$ and $|N|=2C$
for this same whole feedback.

Evaluate the original $P,Q$ of (23.2) on
$w=\operatorname{diag}(U^{(\sigma)}U_+^\dagger)$.
Set $a_-=1/5$, $a_+=2/5$, and choose

$$
\eta=\frac{P\overline Q}{|P||Q|},\qquad
\beta=\begin{pmatrix}\sqrt{a_\sigma}\\
                    \eta\sqrt{1-a_\sigma}\end{pmatrix},\qquad
E^{(\sigma)}=(T\beta\beta^\dagger T^\dagger)^{\mathsf T}.
\tag{54.4}
$$

The strict recovery bounds below verify $P,Q\ne0$, so this formula
is defined. Each effect is positive, pure and trace one, with the
ordinary transpose shown explicitly. Formula (23.13) aligns the two
original recovery summands. Hence the exact attained defects are

$$
G_-=\frac45e^2+\frac15d^2-\frac45(2R_-+C_-)^2,\qquad
G_+=\frac25d^2+\frac35e^2
       -4\left(\sqrt{2/5}R_++\sqrt{3/5}C_+\right)^2.
\tag{54.5}
$$

The active trace is $2(1+x)$ by (46.16). The pure distances are
therefore $13/4$. The original two-sign budget (42.17)--(42.20)
makes the indicated sign uniquely active in both rows. Multiplying
all four entries of either $v$ by one common scalar preserves these
claims and the effect; there is no independent scalar on a pair.

All estimates needed for (54.1) have rational square certificates.
First, direct squaring with
$h^2=1/2$, $s^2=(1-h)/2$, $c^2=(1+h)/2$ gives

$$
\frac{707}{1000}<h<\frac{708}{1000},\qquad
\frac{382}{1000}<s<\frac{383}{1000},\qquad
\frac{4619}{5000}<c<\frac{924}{1000}.
\tag{54.6}
$$

For the negative row put $T_-=L^2-X-Y=3569/6400$. Its coherence
factor and squared half-recoveries are exactly

$$
\begin{aligned}
F_-^2&=\frac{198704151}{2785280000},
&\frac{267}{1000}<F_-<\frac{167}{625},\\
R_-^2&=\frac{s^2}{4}+\frac{17}{40}+shT_-,
&C_-^2&=\frac{3c^2}{4}+\frac3{40}+2chF_-.
\end{aligned}
\tag{54.7}
$$

The two bounds on $F_-$ follow by comparing the displayed fraction
with the squares of its positive endpoints. In particular
$557/1000<T_-<558/1000$. Substitution of (54.6)--(54.7), keeping
all factors positive, proves

$$
\frac{781}{1000}<R_-<\frac{783}{1000},\qquad
\frac{1031}{1000}<C_-<\frac{129}{125},\qquad
\frac{148}{25}<\frac45e^2+\frac15d^2<\frac{297}{50}.
\tag{54.8}
$$

For explicit verification, lower and upper bounds for $R_-^2$ are
obtained from

$$
\frac{(382/1000)^2}{4}+\frac{17}{40}
       +\frac{382\cdot707\cdot557}{10^9}
       >\left(\frac{781}{1000}\right)^2,
\qquad
\frac{(383/1000)^2}{4}+\frac{17}{40}
       +\frac{383\cdot708\cdot558}{10^9}
       <\left(\frac{783}{1000}\right)^2.
$$

For $C_-^2$, substitute respectively
$(c,h,F_-)=(4619/5000,707/1000,267/1000)$ and
$(924/1000,708/1000,167/625)$ in (54.7); the results lie strictly
above $(1031/1000)^2$ and below $(129/125)^2$.
The energy identity used here is
$4-6h/5+32hs/5+8hc/5$; the same endpoints prove its two bounds
in (54.8). Thus

$$
\frac{13}{25}
 <\frac{148}{25}-\frac45\left(\frac{1299}{500}\right)^2
 <G_-
 <\frac{297}{50}-\frac45\left(\frac{2593}{1000}\right)^2
 <\frac9{16}.
\tag{54.9}
$$

For the positive row, $T_+=L^2-X-Y=6161/6400$, and

$$
\begin{aligned}
F_+^2&=\frac{353215242}{111247360000}
                >\left(\frac7{125}\right)^2,\\
R_+^2&=\frac7{50}+\frac{97c^2}{100}+hcT_+
                >\left(\frac{1263}{1000}\right)^2,\\
C_+^2&=\frac9{25}+\frac{3s^2}{100}+2hsF_+
                >\left(\frac{157}{250}\right)^2.
\end{aligned}
\tag{54.10}
$$

For the last two inequalities, use (54.6), $T_+>962/1000$ and
$F_+>7/125$. All terms are positive. Also

$$
\frac25d^2+\frac35e^2
 =4-\frac25h+\frac{16}{5}hc+\frac{24}{5}hs
 <\frac{7113}{1000}.
\tag{54.11}
$$

Squaring proves $\sqrt{2/5}>1581/2500$ and
$\sqrt{3/5}>1549/2000$. Therefore

$$
\sqrt{2/5}R_++\sqrt{3/5}C_+
 >\frac{1581}{2500}\frac{1263}{1000}
       +\frac{1549}{2000}\frac{157}{250}
 >\frac{257}{200}.
$$

Equations (54.5), (54.10)--(54.11) give
$G_+<7113/1000-4(257/200)^2=5081/10000<13/25$.
Finally $9/16=5400/9600<5473/9600=H(13/4)$.
This proves every strict inequality in (54.1). Since the two pairs
have the same true level, subtracting $\kappa\,13/4$ also gives
$f(W_+)<f(W_-)$. $\square$

**Definition 54.2 (sources, live use and the remaining comparison).**
The original recovery identities, alignment phase, normalized effect
and ordinary transpose are source (23.2), (23.9)--(23.13).
The two fixed sign rows and simultaneous reconstruction are
Continuation II, Definition 46.1 and Lemma 46.2; the true-distance
certificate is (42.17)--(42.20). The new result is the strict rational
separation (54.1) for these attained original pairs. It supplies an
original positive competitor below $5081/10000$ at the upper endpoint
and rules out the uniform $g>H$ route there. It makes no
literature-priority or global-minimum claim for either displayed pair.

For the remaining full-domain problem put, using the two rows of
(46.11),

$$
A_\sigma(\xi)=\min_{\substack{0\le q\le1\\(X,Y)\in\mathcal T_x}}
 \left(K_\sigma^2(1-q)+K_{-\sigma}^2q
                 -4\Gamma_\sigma(x,q;X,Y)^2\right),\qquad
x=1-\xi/4+q/2.
\tag{54.12}
$$

For $61/25<\xi\le13/4$, every such $q$ has $0<x<1$ and
$x\ge3/16$, so the full compact domain and both population endpoints
are included. By Continuation III, Theorem 48.5, and Lemma 46.2,
positive-sign selection for every original global minimizer is
exactly the still unresolved strict inequality
$A_-(\xi)>A_+(\xi)$ on this interval. No determinant-sign condition
is imposed. At the upper endpoint (54.1) proves
$A_+(13/4)<5081/10000$ and $A_-(13/4)<9/16$; neither upper bound
orders the two minima. A full proof needs a lower bound for the
entire negative triangle against an attained positive value, or a
direct strict ordering of these two attained minima. A refutation
needs a negative-active global minimizer against the entire original
same-level domain. The pair $W_-$ supplies neither. The completed
prefix and the immediate-right classification retain their stated
ranges.

## 追加锚（本行以下为增补区）
