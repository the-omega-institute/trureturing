# Four-path full-record recovery: first selected determinant zero and relaxed quartic

## 49. First selected determinant zero, population relaxation and the original local phase consequence

Use the original normalized effects, ordinary transpose and shared feedback of
the [source volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md),
Definitions 1.1, 11.1 and 23.1. Section numbers 24--39 refer to
[Continuation I](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md);
40--46 refer to
[Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md).
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
(40.21). Choose a product neighborhood of them contained in $\Omega$,
with $\xi<4$. Its strict conditions are
$uv>0$, $0<q=t-\delta<1$, $q<J_+$, $t_-<0$, and positive arc
derivative greater than $49/180$. Here $u=|P|$, $v=|Q|$;
$J_+=(3+A-B)/2$ and $t_-=(\xi-8+2B)/2$ are the original
fixed-feedback arc data of (36.2).

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
\rho_--\rho_+&=2(3+A-B-2r).
\end{aligned}
\tag{49.21}
$$

Since $t_-<0$, no effect can have negative branch equal to this
prescribed $\xi$. Every original effect with $\rho(E,U)=\xi=2t$
therefore has positive minimizing sign and satisfies exactly

$$
q=t-\delta=r-\epsilon(E)/2=r^2+|z_E|^2,\qquad
q\le r\le\min\{\sqrt q,J_+\}.
\tag{49.22}
$$

The upper bound permits a sign tie if it is feasible. It retains the
whole mixed arc and its zero-coherence endpoint. In particular one
must not set $r=q$ for mixed effects.

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

The ordinary transpose is retained. This effect is positive, trace
one and rank one; $q<J_+$ makes its positive distance uniquely
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
( -\mathcal E)(\sqrt L\,y/x)\sqrt j\,\varepsilon^2
O(\varepsilon^3)$.
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
the nearby pure constructions. More generally their membership in
$\Omega$ already enforces $q<J_+$ and $t_-<0$, hence the actual
branch statements used in (49.21)--(49.23). Both original distance
branches, not just a formal positive-branch constraint, are accounted
for.

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
purity from Theorem 45.5 does not fill these gaps. An actual arbitrary
$U(4)$ minimizing lift still requires the global phase comparison and
the variance-zero condition in (42.25): for every positive-weight
transport component, $(E,U_j)\in\mathcal A_{\mathrm{ph},\xi}$ and
$(a_j-a)F_E^{1/2}=0$. A local phase neighborhood supplies neither
condition for all competitors. This article makes no unrestricted
unitary local-minimum classification, no global equality completion,
and no claim about an empirical quantum origin, state preparation,
reset, dynamics or physical realization. These are paper proofs and
algebraic certificates; no Lean, kernel or digestion status is asserted.

## 追加锚（本行以下为增补区）
