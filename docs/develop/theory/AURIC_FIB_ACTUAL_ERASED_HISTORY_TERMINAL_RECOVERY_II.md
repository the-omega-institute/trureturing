# AURIC FIB actual erased-history terminal recovery II

## 127. The original third-horizon density-input problem

This volume continues [Actual erased-history terminal recovery][TR].
Its subject is the exact third-horizon value for a common terminal
qutrit decoder, together with the input equality set of one attaining
map and necessary support conditions for every attaining map. All
statements below are ordinary finite-dimensional mathematics.

**Definition 127.1 (Coordinates and the actual channel).** Use the
ordered orthonormal basis of [TR, Definition 93.1]: in the original
coordinates its vectors are

$$
|0\rangle=\frac{(1,1,1)^{\mathsf T}}{\sqrt3},\qquad
|1\rangle=\frac{(1,1,-2)^{\mathsf T}}{\sqrt6},\qquad
|2\rangle=\frac{(1,-1,0)^{\mathsf T}}{\sqrt2}.
\tag{127.1}
$$

In this basis let

$$
\begin{aligned}
W&=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\\
U_1&=U_0W,\qquad
\operatorname{Ad}_V(X)=VXV^\dagger,\\
\Delta_W&=\tfrac12(\operatorname{id}+\operatorname{Ad}_W),\qquad
F=\operatorname{Ad}_{U_0}\circ\Delta_W
 =\tfrac12(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1}).
\end{aligned}
\tag{127.2}
$$

The fair chronological law of [TR, Definition 93.1] assigns probability
$2^{-n}$ to each word of length $n$ in its actual letters
$V_0(\theta)=U_0e^{i\theta W}$ and $V_1(\theta)=V_0(\theta)W$.
The erased-history channel of that model is $\mathcal N_n=F^n$.
We reuse the exact transport identity [TR, (93.5), (93.10)]:

$$
\begin{aligned}
s_n&=(-1/2)^{n-1},\qquad
\mathcal N_n=\operatorname{Ad}_{U_0}\circ\Phi_{s_n}\quad(n\ge1),\\
\Phi_s(X)&=
\begin{pmatrix}
X_{00}&sX_{01}&0\\
sX_{10}&(1+s)X_{11}/2+(1-s)X_{22}/2&0\\
0&0&(1-s)X_{11}/2+(1+s)X_{22}/2
\end{pmatrix}.
\end{aligned}
\tag{127.3}
$$

These identities hold on every complex matrix unit. Here $n=3$ means
$s_3=1/4$. Write $\Phi=\Phi_{1/4}$, so explicitly

$$
\Phi(X)=
\begin{pmatrix}
X_{00}&X_{01}/4&0\\
X_{10}/4&(5X_{11}+3X_{22})/8&0\\
0&0&(3X_{11}+5X_{22})/8
\end{pmatrix}.
\tag{127.4}
$$

In particular the sign of the chronological parameter has been retained
before specializing the horizon.

**Definition 127.2 (Common decoder and identity target).** Let
$\mathsf D_3=\{\rho\in M_3:\rho\succeq0,\operatorname{Tr}\rho=1\}$,
where $M_3=\mathcal B(\mathbb C^3)$, and put

$$
\begin{aligned}
e(\mathcal R)&=\max_{\rho\in\mathsf D_3}
 \frac12\|\rho-\mathcal R\Phi(\rho)\|_1,\\
\mu(1/4)&=\min_{\mathcal R:M_3\to M_3\ {\rm CPTP}}e(\mathcal R),\\
\mu_3&=\min_{D:M_3\to M_3\ {\rm CPTP}}
 \max_{\rho\in\mathsf D_3}\frac12\|\rho-D\mathcal N_3(\rho)\|_1.
\end{aligned}
\tag{127.5}
$$

The trace norm is $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$.
One complex CPTP decoder is fixed before the input is chosen. The input
set is the entire complex density set, including every mixed state.
The decoder receives the terminal qutrit alone; a history, environment
or reference register is not supplied, and the input test has no
reference system. Internal ancillas implementing a CPTP map do not
change this domain or this common-map quantifier. No unitality condition
is imposed.

The decoder correspondence is precisely

$$
\mathcal R=D\circ\operatorname{Ad}_{U_0},\qquad
D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger},\qquad
D\mathcal N_3=\mathcal R\Phi,
\qquad \mu_3=\mu(1/4).
\tag{127.6}
$$

It is a bijection on all CPTP maps. In particular the input target in
(127.5) is not rotated. This is a mathematical consequence for the
specific fair chronological model and transport (127.3); it supplies
no inference that this model is a physical realization of a broader
theory. Compact attainment and pure-input reduction are [TR, Lemmas
105.2–105.3]. The density-input quantity in (127.5) is the one defined
in [TR, §105], distinct from the stabilized norm in [TR, §93].

## 128. The exact value and its four defining polynomials

**Definition 128.1 (Polynomial contact system).** The variable order is
$z=(r,L,p,x)$. First substitute $y=1-p-x$ and define

$$
\begin{aligned}
k&=1-r/4,\qquad
v_1=(5x+3y)/8,\qquad v_2=(3x+5y)/8,\\
d&=x-r^2v_1,\\
N(r,L;p,x)&=L^3-L(d^2+k^2px+py+xy)
             -p\{d(k^2x-y)+2kxy\},\\
\mathcal F(z)&=(N,N_p,N_x,N_r)^{\mathsf T}.
\end{aligned}
\tag{128.1}
$$

Every derivative includes the substitution $y=1-p-x$. In particular
$N_r$ differentiates the decoder parameter while holding $L,p,x$
fixed. The four entries of $\mathcal F$ are rational polynomials,
not derivatives of an unspecified optimization procedure.

Let $\varepsilon=10^{-20}$ and let $c$ be the rational centre below.
Each finite decimal denotes its exact rational value, with denominator
$10^{40}$.

| Coordinate | Exact centre |
| --- | --- |
| $r$ | $0.9215681729696027473087646795928491460085$ |
| $L$ | $0.6179889248320065700077421048549089460189$ |
| $p$ | $0.3137695512908343918136698112058502149209$ |
| $x$ | $0.2853203142243080749860551323785423531541$ |

Set

$$
\mathcal B=\{z\in\mathbb R^4:\|z-c\|_\infty\le\varepsilon\}.
\tag{128.2}
$$

The unique zero of $\mathcal F$ in $\mathcal B$, whose existence and
uniqueness are proved in §129, is denoted by
$(r_*,L_*,p_*,x_*)$. Write $y_*=1-p_*-x_*$.

**Theorem 128.2 (Exact third-horizon minimax).** For the entire complex
density-input problem (127.5),

$$
\boxed{\mu_3=\mu(1/4)=L_*},\qquad
\boxed{0.61798892483200656999<L_*<0.61798892483200657002}.
\tag{128.3}
$$

A single decoder attaining the value has the three Kraus operators

$$
K_0=\operatorname{diag}(1,r_*,0),\qquad
K_1=\sqrt{1-r_*^2}\,|2\rangle\langle1|,\qquad
K_2=|2\rangle\langle2|.
\tag{128.4}
$$

Call it $\mathcal R_*$. The original-coordinate terminal decoder is
$D_*=\mathcal R_*\circ\operatorname{Ad}_{U_0^\dagger}$.
More explicitly, the upper assertion is

$$
\forall\rho\in\mathsf D_3,\qquad
\frac12\|\rho-\mathcal R_*\Phi(\rho)\|_1\le L_*,
\tag{128.5}
$$

with equality for the pure phase orbit in §136. The lower assertion is

$$
\forall\mathcal R:M_3\to M_3\ {\rm complex\ CPTP},\qquad
\max_{\rho\in\mathsf D_3}
\frac12\|\rho-\mathcal R\Phi(\rho)\|_1\ge L_*.
\tag{128.6}
$$

Sections 130–132 prove (128.5); §§133–135 prove (128.6) using the same
isolated root. Section 136 identifies every maximizing density for
$\mathcal R_*$ and shows that each is pure. Section 137 gives necessary
Choi support for every optimal decoder and uniquely determines the
parameters surviving phase averaging and removal of invisible
multipliers. Those conditions are not a classification of all optimal
untwirled decoders.

## 129. Finite rational specification and root isolation

**Lemma 129.1 (Coefficient and derivative data).** The complete
population expansion of (128.1) is

$$
128N=\sum_{i+j\le3}h_{ij}(r,L)p^ix^j,
\tag{129.1}
$$

with all its nonzero coefficients given by this table.

| $(i,j)$ | $h_{ij}(r,L)$ |
| --- | --- |
| $(0,0)$ | $128L^3-18Lr^4$ |
| $(0,1)$ | $-24Lr^4+96Lr^2-128L$ |
| $(0,2)$ | $-8Lr^4+64Lr^2$ |
| $(1,0)$ | $36Lr^4-128L-48r^2$ |
| $(1,1)$ | $24Lr^4-104Lr^2+64Lr+128L+3r^4-24r^3+64r^2+64r-128$ |
| $(1,2)$ | $2r^4-16r^3+56r^2$ |
| $(2,0)$ | $-18Lr^4+128L+96r^2$ |
| $(2,1)$ | $-3r^4+24r^3-64r^2-64r+128$ |
| $(3,0)$ | $-48r^2$ |

Thus, in addition to $128\mathcal F_0=\sum h_{ij}p^ix^j$,
the other three polynomials are specified without any omitted terms by

$$
\begin{aligned}
128\mathcal F_1&=\sum_{i\ge1,j}i h_{ij}p^{i-1}x^j,\\
128\mathcal F_2&=\sum_{i\ge0,j\ge1}j h_{ij}p^ix^{j-1},\\
128\mathcal F_3&=\sum_{i,j}(\partial_rh_{ij})p^ix^j.
\end{aligned}
\tag{129.2}
$$

The coefficient indices in each sum range only over the table.
Expanding (128.1) gives the table directly, and ordinary polynomial
differentiation gives (129.2).

**Lemma 129.2 (Exactly one root in the rational box).** There is
exactly one zero of $\mathcal F$ in $\mathcal B$. It lies in the
interior of that box and satisfies

$$
9/10<r_*<93/100,\qquad L_*>3/5,\qquad
p_*,x_*,y_*>0.
\tag{129.3}
$$

*Proof.* Here is a finite rational recipe for every arithmetic
inequality used in the isolation. For $\nu\in\mathbb N^4$, expand
$\mathcal F_i=\sum_\nu f_{i\nu}z^\nu$ from the preceding table and put

$$
J_{ij}=\sum_{\nu:\nu_j>0}\nu_j f_{i\nu}c^{\nu-e_j},\qquad
f_i=\sum_\nu f_{i\nu}c^\nu.
\tag{129.4}
$$

Here $J=D\mathcal F(c)$, and indices of matrices start at zero.
Let $q$ be the least common multiple of the positive reduced
denominators of all $J_{ij}$, set $V=qJ$, and define

$$
\begin{aligned}
\delta&=\sum_{\pi\in S_4}\operatorname{sgn}(\pi)
                      \prod_{i=0}^3V_{i,\pi(i)},\\
C_{ij}&=(-1)^{i+j}\det V[\widehat i\mid\widehat j].
\end{aligned}
\tag{129.5}
$$

The three-by-three determinants use the same permutation formula.
Let $m$ be the least common multiple of the positive reduced
denominators of $f_i$ and let $u_i=mf_i$. These definitions specify
integers $V,\delta,C,u$ and positive integers $q,m$ solely from the
finite rational data above. Substitution and integer arithmetic give

$$
\begin{aligned}
&\delta^2\ge1,\qquad
q\max_i\sum_j|C_{ji}|<2|\delta|,\\
&10^{39}\max_i|u_i|<m,\\
&10^{39}q\max_i\left|\sum_jC_{ji}u_j\right|<m|\delta|.
\end{aligned}
\tag{129.6}
$$

In particular, no zero denominator is used in

$$
M=J^{-1}=\frac q\delta C^{\mathsf T},\qquad
\|M\|_\infty<2,\qquad
\|\mathcal F(c)\|_\infty<10^{-39},\qquad
\|M\mathcal F(c)\|_\infty<10^{-39}.
\tag{129.7}
$$

For readable outer checks of the same rational calculations,
$1.9231<\|M\|_\infty<1.9232$,
$10^{-40}<\|\mathcal F(c)\|_\infty<2\cdot10^{-40}$ and
$4\cdot10^{-41}<\|M\mathcal F(c)\|_\infty<5\cdot10^{-41}$.
The definitions (129.1)–(129.5), rather than decimal inverses, specify
the arithmetic in (129.6).

For a polynomial $h$, let $\|h\|_{\rm coeff,1}$ be the sum of the
absolute values of its expanded monomial coefficients. Direct
differentiation of (129.2) gives the following exact row sums:

| Entry | $\sum_{j,k=0}^3\|\partial_j\partial_k\mathcal F_i\|_{\rm coeff,1}$ |
| --- | --- |
| $\mathcal F_0=N$ | $345/2$ |
| $\mathcal F_1=N_p$ | $3441/32$ |
| $\mathcal F_2=N_x$ | $5311/64$ |
| $\mathcal F_3=N_r$ | $3499/16$ |

Their maximum is $H=3499/16$. The whole box is in $(0,1)^4$,
so each monomial has absolute value at most one there; these coefficient
sums therefore bound the corresponding sums of absolute second
derivatives throughout the box. With $G(z)=z-M\mathcal F(z)$,

$$
\begin{aligned}
DG(c)&=0,\\
\sup_{z\in\mathcal B}\|DG(z)\|_\infty
&\le\|M\|_\infty H\varepsilon
 <2H\varepsilon=\frac{3499}{8}\,10^{-20}<1,\\
\|G(z)-c\|_\infty
&<10^{-39}+2H\varepsilon^2<\varepsilon
\quad(z\in\mathcal B).
\end{aligned}
\tag{129.8}
$$

The mean-value bound applies along segments within this convex box.
The contraction theorem gives a unique fixed point, strictly inside
$\mathcal B$. Since $M$ is invertible, fixed points are precisely
zeros of $\mathcal F$. The centre and radius give (129.3), because
$c_p+c_x+2\varepsilon<1$. The interval
$[c_L-\varepsilon,c_L+\varepsilon]$ is strictly inside the endpoints
in (128.3). This proves the claimed value bracket independently of any
rounded root calculation. $\square$

**Convention 129.3 (Rational interval evaluation).** For sign checks
start with the four closed intervals $[c_j-\varepsilon,c_j+\varepsilon]$.
A rational constant is a singleton interval. Add endpoints, subtract
$[a,b]-[c,d]=[a-d,b-c]$, and multiply by taking the minimum and maximum
of the four endpoint products. Nonnegative integer powers may be
computed by repeated multiplication. Divide only by an interval
excluding zero, using its reciprocal interval. Repeated occurrences
may be treated independently. This is the rational interval method
of [TR, §120]; all displayed decimal bounds are strict outer rational
bounds, so no floating-point rounding rule is required.

For subsequent use define, as polynomials on the whole box,

$$
\begin{aligned}
a_0&=L^2-d^2-xy,\qquad a_1=L(L+d)-py,\\
a_2&=L(L-d)-k^2px,\qquad \tau=a_0+a_1+a_2,\\
\beta&=k(L+d)+y,\qquad
\omega_0=px\beta/4,\qquad
g=p(a_0-a_2)+r\omega_0.
\end{aligned}
\tag{129.9}
$$

Evaluation in this displayed order, starting with the auxiliaries in
(128.1), gives the following enclosures on the entire box, including
its endpoints. All entries are strictly between their displayed
endpoints.

| Expression | Lower bound | Upper bound |
| --- | --- | --- |
| $y$ | $0.400$ | $0.402$ |
| $v_1$ | $0.328$ | $0.330$ |
| $v_2$ | $0.357$ | $0.359$ |
| $a_0$ | $0.267$ | $0.268$ |
| $a_1$ | $0.259$ | $0.261$ |
| $a_2$ | $0.324$ | $0.326$ |
| $\tau$ | $0.852$ | $0.853$ |
| $a_2-a_0$ | $0.057$ | $0.058$ |
| $a_2-a_1$ | $0.065$ | $0.066$ |
| $\beta$ | $0.881$ | $0.882$ |
| $\omega_0$ | $0.019$ | $0.020$ |
| $g$ | $0.00011$ | $0.00012$ |
| $g/\tau$ | $0.00013$ | $0.00014$ |
| $L-d+kx$ | $0.831$ | $0.832$ |
| $L+kp$ | $0.859$ | $0.860$ |

The positive lower bound for $\tau$ is established before division by
it. Later division by $r$ is justified by (129.3). Thus the small
positive quantity $g$ and the associated slack $g/\tau$ have signs
certified from the same explicit finite rational data as the root.

## 130. A legal decoder and its error determinant

**Lemma 130.1 (Decoder on the whole qutrit).** For every $0\le r\le1$
let $\mathcal R_r$ have the Kraus operators (128.4) with $r_*$ replaced
by $r$. Then

$$
\mathcal R_r(X)=
\begin{pmatrix}
X_{00}&rX_{01}&0\\
rX_{10}&r^2X_{11}&0\\
0&0&(1-r^2)X_{11}+X_{22}
\end{pmatrix}.
\tag{130.1}
$$

It is CPTP, since the three adjoint products sum to
$\operatorname{diag}(1,r^2,0)+(1-r^2)E_{11}+E_{22}=I_3$.
The square root in its Kraus list is real by $0\le r\le1$.
In particular $\mathcal R_*:=\mathcal R_{r_*}$ is legal on all of $M_3$.

For completeness, specializing [TR, (105.4)] gives the following Kraus
list for $\Phi$:

$$
\operatorname{diag}(1,1/4,0),\quad
\tfrac34 E_{11},\quad
\sqrt{3/8}\,E_{21},\quad
\sqrt{3/8}\,E_{12},\quad
\sqrt{5/8}\,E_{22}.
\tag{130.2}
$$

Their adjoint products sum to $I_3$ and give (127.4) on every complex
matrix. Consequently every recovered density used below is positive
and has trace one.

**Lemma 130.2 (Cubic determinant of the actual composite).** Let
$p,x,y\ge0$ with $p+x+y=1$, put
$z=(\sqrt p,\sqrt x,\sqrt y)^{\mathsf T}$ and $P=zz^{\mathsf T}$.
Directly composing (127.4) and (130.1) gives

$$
Q:=\mathcal R_r\Phi(P)=
\begin{pmatrix}
p&(r/4)\sqrt{px}&0\\
(r/4)\sqrt{px}&r^2v_1&0\\
0&0&x+y-r^2v_1
\end{pmatrix}.
\tag{130.3}
$$

Thus the signed error is

$$
A:=P-Q=
\begin{pmatrix}
0&k\sqrt{px}&\sqrt{py}\\
k\sqrt{px}&d&\sqrt{xy}\\
\sqrt{py}&\sqrt{xy}&-d
\end{pmatrix},\qquad
\det(LI_3-A)=N(r,L;p,x).
\tag{130.4}
$$

*Proof.* Expanding this determinant gives
$L^3-L(d^2+k^2px+py+xy)-pd(k^2x-y)-2kpxy$,
which is (128.1). After $y=1-p-x$ its population degree is at most
three, as is also explicit in (129.1). $\square$

We use the pure-target determinant and inertia criterion established
in [TR, (122.7)–(122.8)]: for a density $Q$, a unit vector $z$,
$P=zz^\dagger$ and $L>0$,

$$
\begin{aligned}
\det(LI+Q-P)\ge0
&\ \Longleftrightarrow\ LI+Q-P\succeq0,\\
\tfrac12\|P-Q\|_1&=\lambda_{\max}(P-Q).
\end{aligned}
\tag{130.5}
$$

The first equivalence is the rank-one determinant formula applied to
the positive definite matrix $LI+Q$. The second uses that $P-Q$ is
nonpositive on $z^\perp$, so it has at most one positive eigenvalue,
and that its trace is zero. In particular these are statements for a
pure target against an arbitrary density, not sign tests for an
arbitrary traceless Hermitian matrix. Equality in the first determinant
at $L>0$ yields eigenvalue $L$ and hence trace distance $L$.

## 131. Exact control of all three closed edges

**Lemma 131.1 (Uniform boundary bound).** If $9/10<r<93/100$, then
for every population on the boundary of
$\mathcal T=\{(p,x):p,x\ge0,\ p+x\le1\}$,

$$
\lambda_{\max}(A)\le3/5.
\tag{131.1}
$$

*Proof.* Set $a=1-5r^2/8$ and $b=3r^2/8$, so $d=ax-by$.
Evaluation on the larger closed interval $r\in[9/10,93/100]$ gives

$$
\frac{7351}{16000}\le a\le\frac{79}{160},\qquad
\frac{243}{800}\le b\le\frac{25947}{80000},\qquad
\frac{307}{400}\le k\le\frac{31}{40}.
\tag{131.2}
$$

In particular $0<a<1/2$, $0<b<1/3$, $3/4<k<4/5$ and $a<k$.
There are three edges, and their endpoints are included in the
following calculations.

On $x=0$, the $02$ block of $A$ is
$\left(\begin{smallmatrix}0&\sqrt{y(1-y)}\\
\sqrt{y(1-y)}&by\end{smallmatrix}\right)$ and the remaining
eigenvalue is $-by$. For $m=1/(2-b)$ the block determinant at $m$ is

$$
m^2-mby-y(1-y)=(y-m)^2.
\tag{131.3}
$$

Since $m>0$ and the block has at most one positive eigenvalue, its
largest eigenvalue is at most $m$. Equality holds at $y=m\in(0,1)$.
Therefore the exact closed-edge maximum is $1/(2-b)<3/5$.

On $y=0$, the $01$ block is
$\left(\begin{smallmatrix}0&k\sqrt{x(1-x)}\\
k\sqrt{x(1-x)}&ax\end{smallmatrix}\right)$ and the other
eigenvalue is $-ax$. Put $m=k^2/(2k-a)$; its denominator is positive
because $0<a<k$. Then

$$
m^2-ma x-k^2x(1-x)=k^2(x-m/k)^2.
\tag{131.4}
$$

The exact maximum on this closed edge is $m$, attained at
$x=m/k=k/(2k-a)\in(0,1)$. The derivatives

$$
\partial_a\frac{k^2}{2k-a}=\frac{k^2}{(2k-a)^2}>0,\qquad
\partial_k\frac{k^2}{2k-a}=\frac{2k(k-a)}{(2k-a)^2}>0
\tag{131.5}
$$

hold on $0<a<k$. Increasing first $k$ to $4/5$ and then $a$ to $1/2$
stays in that domain. Consequently
$m\le(4/5)^2/(8/5-1/2)=32/55<3/5$.

On $p=0$ the eigenvalues are $0$ and
$\pm\sqrt{(ax-by)^2+xy}$. For $x,y\ge0$,

$$
\begin{aligned}
\frac{x^2}{4}+\frac{y^2}{9}-(ax-by)^2
&=(1/4-a^2)x^2+(1/9-b^2)y^2+2abxy\ge0,\\
\frac{x^2}{4}+\frac{(1-x)^2}{9}+x(1-x)
&=\frac8{23}-\frac{23}{36}(x-14/23)^2.
\end{aligned}
\tag{131.6}
$$

Thus this edge has largest eigenvalue at most $\sqrt{8/23}<3/5$;
the final comparison is $8/23<9/25$. All three estimates include
the vertices, and prove (131.1). $\square$

At $r=r_*$ and $L=L_*>3/5$ all eigenvalues of $A$ on the boundary
are strictly below $L$. Hence

$$
N(r_*,L_*;p,x)>0\qquad((p,x)\in\partial\mathcal T).
\tag{131.7}
$$

## 132. The cubic chord argument and the global upper bound

**Lemma 132.1 (Stationary-zero cubic chord lemma).** Let $K$ be a compact
convex body with nonempty interior in a finite-dimensional real affine
space. Let $f$ be a real polynomial of degree at most three on that
space. If $u\in\operatorname{int}K$, $f(u)=0$, $Df(u)=0$ and
$f>0$ on $\partial K$, then $f>0$ on $K\setminus\{u\}$.

*Proof.* Fix a nonzero direction $v$ through $u$. Its intersection with
$K$ is a segment whose boundary parameters satisfy $t_-<0<t_+$.
The zero and stationary conditions give

$$
f(u+tv)=t^2(\alpha+\beta t).
\tag{132.1}
$$

At both boundary endpoints the affine factor is positive, since the
quadratic factor is nonzero. An affine function positive at both ends
of an interval is positive on the entire interval. Thus
$f(u+tv)>0$ for $t\ne0$ between these endpoints. Every point of
$K\setminus\{u\}$ lies on one such line. $\square$

**Proposition 132.2 (All complex and mixed inputs).** The decoder
$\mathcal R_*$ has $e(\mathcal R_*)=L_*$.

*Proof.* Fix $r=r_*$ and $L=L_*$. The polynomial $N$ in $(p,x)$ has
degree at most three. The equations $N=N_p=N_x=0$ hold at
$(p_*,x_*)\in\operatorname{int}\mathcal T$. Lemma 131.1 and $L>3/5$
give strict boundary positivity (131.7). Lemma 132.1 therefore gives

$$
N(r_*,L_*;p,x)\ge0\quad((p,x)\in\mathcal T),\qquad
N=0\ \Longleftrightarrow\ (p,x)=(p_*,x_*).
\tag{132.2}
$$

Applying (130.5) to (130.3) proves the distance bound $L$ for every
nonnegative-amplitude pure input, including all edges. At the interior
contact, $N=0$ and $L>0$, so the bound is attained.

Both $\Phi$ and $\mathcal R_r$ commute with conjugation by every
diagonal unitary: this follows entry by entry from (127.4) and
(130.1), or from the covariance used in [TR, §112]. Every complex
pure input has the form $UPU^\dagger$ for such a unitary $U$ and
nonnegative amplitudes. Unitary invariance of the trace norm gives the
same bound for every phase. Zero amplitudes cause no exception.

For an arbitrary mixed density take a finite pure decomposition
$\rho=\sum_j t_jP_j$, where $t_j\ge0$ and $\sum_jt_j=1$. The pure-input
reduction of [TR, Lemma 105.3] gives explicitly

$$
\frac12\|\rho-\mathcal R_*\Phi(\rho)\|_1
\le\sum_jt_j\frac12\|P_j-\mathcal R_*\Phi(P_j)\|_1\le L_*.
\tag{132.3}
$$

The decoder has not changed with the input or its decomposition.
Contact attainment proves $e(\mathcal R_*)=L_*$ and
$\mu(1/4)\le L_*$. $\square$

## 133. The contact projector and decoder stationarity

All quantities in §§133–137 without a star are evaluated at
$(r_*,L_*,p_*,x_*)$, except where an identity is explicitly said to
hold off the root. Put $P=zz^{\mathsf T}$ for
$z=(\sqrt p,\sqrt x,\sqrt y)^{\mathsf T}$, and use $A$ from (130.4).

**Lemma 133.1 (An exact rank-one effect).** Let $B=LI_3-A$. Then

$$
\operatorname{adj}B=
\begin{pmatrix}
a_0&\sqrt{px}\,\beta&\sqrt{py}(L-d+kx)\\
\sqrt{px}\,\beta&a_1&\sqrt{xy}(L+kp)\\
\sqrt{py}(L-d+kx)&\sqrt{xy}(L+kp)&a_2
\end{pmatrix},\qquad
T=\frac{\operatorname{adj}B}{\tau}.
\tag{133.1}
$$

The operator $T$ is a rank-one orthogonal projector, hence an effect
$0\preceq T\preceq I_3$, with $AT=LT$ and $T_{ii}>0$ for all $i$.

*Proof.* Cofactor expansion gives the displayed adjugate and

$$
B\operatorname{adj}B=NI_3,\qquad
\operatorname{Tr}\operatorname{adj}B=\tau=N_L.
\tag{133.2}
$$

These are polynomial identities before the contact equations are
imposed. Proposition 132.2 and (130.5) give $B\succeq0$. At the
contact its determinant is zero, whereas $\tau>0$ by §129. Thus $B$
has rank exactly two. Its adjugate is positive semidefinite of rank
one, and division by its positive trace makes it an orthogonal
projector. Its range is the kernel of $B$, giving $AT=LT$.
The three positive cofactor bounds in §129 imply $T_{ii}>0$.
All denominators and all nonzero-amplitude claims are therefore
justified by the root-box inequalities. $\square$

**Lemma 133.2 (Exact stationarity identity).** Define

$$
w=\frac{\omega_0}{\tau}=\frac{\sqrt{px}}4T_{01}>0.
\tag{133.3}
$$

Differentiating (128.1) with respect to $r$ gives the off-root identity

$$
N_r=2rv_1(a_1-a_2)+2\omega_0.
\tag{133.4}
$$

Indeed $d_r=-2rv_1$ and $k_r=-1/4$; substituting them into the
derivative gives (133.4). At the root it reads

$$
rv_1(T_{22}-T_{11})=w.
\tag{133.5}
$$

The fourth equation $N_r=0$ thus supplies the exact complementary
relation for the unrestricted Choi certificate. The other three
equations supplied the value and input stationarity in §132.

## 134. Nine distinct qutrit witnesses and the complete Choi functional

**Definition 134.1 (Input/effect pairs).** Let $\zeta=e^{2\pi i/3}$ and
for $j,\ell\in\{0,1,2\}$ set

$$
U_{j\ell}=\operatorname{diag}(1,\zeta^j,\zeta^\ell),\qquad
P_{j\ell}=U_{j\ell}PU_{j\ell}^\dagger,\qquad
T_{j\ell}=U_{j\ell}TU_{j\ell}^\dagger.
\tag{134.1}
$$

Each pair is given weight $1/9$. Every $P_{j\ell}$ is a qutrit density
and every $T_{j\ell}$ is an effect. There are nine distinct input
projectors: since $p,x,y>0$, equality of two projectors would force
their relative diagonal unitary to be scalar on a vector with all
three coordinates nonzero. Its first entry is one, so both relative
phases must be one. The effects test ordinary qutrit outputs and do
not provide an additional register to the decoder.

Use the output-first, unnormalized Choi convention of [TR, (124.1)]:

$$
\begin{aligned}
J_{\mathcal R}&=\sum_{j,k=0}^2\mathcal R(E_{jk})\otimes E_{jk},\\
\operatorname{Tr}[T\mathcal R(Q)]
&=\operatorname{Tr}[(T\otimes Q^{\mathsf T})J_{\mathcal R}],\\
W&=\frac19\sum_{j,\ell=0}^2
T_{j\ell}\otimes\Phi(P_{j\ell})^{\mathsf T}.
\end{aligned}
\tag{134.2}
$$

Here $Q^{\mathsf T}$ is the ordinary transpose, not the adjoint; it
also applies to complex $Q$. Complete positivity and trace
preservation are $J_{\mathcal R}\succeq0$ and
$\operatorname{Tr}_{\rm out}J_{\mathcal R}=I_3$. The tensor notation
is the representation of a linear functional on a decoder, not a
reference input in (127.5).

**Lemma 134.2 (Every entry of $W$).** Index the tensor basis by
$(00,01,02,10,11,12,20,21,22)$, with the output coordinate first.
Writing $v_0=p$ and $t_i=T_{ii}=a_i/\tau$, all 81 entries are
specified by

$$
W=\begin{pmatrix}
t_0p&0&0&0&w&0&0&0&0\\
0&t_0v_1&0&0&0&0&0&0&0\\
0&0&t_0v_2&0&0&0&0&0&0\\
0&0&0&t_1p&0&0&0&0&0\\
w&0&0&0&t_1v_1&0&0&0&0\\
0&0&0&0&0&t_1v_2&0&0&0\\
0&0&0&0&0&0&t_2p&0&0\\
0&0&0&0&0&0&0&t_2v_1&0\\
0&0&0&0&0&0&0&0&t_2v_2
\end{pmatrix}.
\tag{134.3}
$$

In particular the two off-diagonal couplings have positive sign.

*Proof.* The nine-element character identity [TR, (124.5)] is
$\frac19\sum_{j,\ell=0}^2\zeta^{ju+\ell v}=1$ if both exponents
vanish modulo three, and zero otherwise. Its application here can be
specified completely by the following nine charges $c_i-c_m$,
where $c_0=(0,0),c_1=(1,0),c_2=(0,1)$ in $\mathbb Z_3^2$:

$$
\begin{array}{c|ccc}
i\backslash m&0&1&2\\\hline
0&(0,0)&(2,0)&(0,2)\\
1&(1,0)&(0,0)&(1,2)\\
2&(0,1)&(2,1)&(0,0)
\end{array}.
\tag{134.4}
$$

The entry with row $(i,j)$ and column $(m,n)$ of the summand in
(134.2) has charge $c_i-c_m+c_n-c_j$. The second pair is reversed
because of the transpose. All six off-diagonal charges in (134.4)
are distinct. The charge can vanish only if both matrix factors are
diagonal, or if $(i,m)=(j,n)$ with $i\ne m$. Since $\Phi(P)$ has only
$01$ and $10$ off-diagonal entries, the latter case gives precisely
$(00,11)$ and $(11,00)$. Their common value is
$T_{01}\sqrt{px}/4=w$. The diagonal values are $T_{ii}v_j$.
This proves every entry, including every zero, without phase sampling.
$\square$

## 135. A full positive Choi slack and the matching lower bound

**Lemma 135.1 (Slack, complementarity and exact value).** Let

$$
Y=\operatorname{diag}(pT_{00}+rw,\ v_1T_{22},\ v_2T_{22}),\qquad
S=I_{\rm out}\otimes Y-W.
\tag{135.1}
$$

Then $S\succeq0$. On $\operatorname{span}\{|00\rangle,|11\rangle\}$
its block is

$$
\begin{pmatrix}rw&-w\\-w&w/r\end{pmatrix}
=\frac wr\begin{pmatrix}r\\-1\end{pmatrix}
            \begin{pmatrix}r&-1\end{pmatrix},
\tag{135.2}
$$

and its other seven blocks, each one-dimensional, are

| Coordinate | Scalar entry of $S$ |
| --- | --- |
| $01$ | $v_1(a_2-a_0)/\tau$ |
| $02$ | $v_2(a_2-a_0)/\tau$ |
| $10$ | $\{g+p(a_2-a_1)\}/\tau$ |
| $12$ | $v_2(a_2-a_1)/\tau$ |
| $20$ | $g/\tau$ |
| $21$ | $0$ |
| $22$ | $0$ |

The five displayed nonzero scalar entries are strictly positive.
If $b_{\rm test}=\operatorname{Tr}(TP)$, then

$$
SJ_{\mathcal R_*}=0,\qquad b_{\rm test}-\operatorname{Tr}Y=L.
\tag{135.3}
$$

*Proof.* The actual $11$ diagonal entry of $I\otimes Y-W$ is
$v_1(a_2-a_1)/\tau$. Equation (133.5) makes it $w/r$ at the root.
The other entries follow by direct subtraction of (134.3), using
$g=p(a_0-a_2)+r\omega_0$. The root-box bounds give $r,w,\tau,v_1,v_2>0$,
$a_2-a_0>0$, $a_2-a_1>0$ and $g>0$. These are sufficient for
positive semidefiniteness of the entire $9\times9$ matrix, including
the small $20$ entry.

For the exact role of stationarity, define $S_{\rm cert}$ by the block
(135.2) and the seven scalar formulas even off the root, keeping the
rational expressions (129.9). Then the following identity holds before
any root equation is imposed, wherever $r\tau\ne0$:

$$
(I\otimes Y-W)-S_{\rm cert}
=-\frac{N_r}{2r\tau}|11\rangle\langle11|.
\tag{135.4}
$$

Indeed (133.4) gives
$v_1(a_2-a_1)/\tau-w/r=-N_r/(2r\tau)$.
Thus there is no rounded stationarity assumption in (135.2).

The Kraus list gives the exact Choi matrix

$$
\begin{aligned}
v&=|00\rangle+r|11\rangle,\\
J_{\mathcal R_*}&=vv^\dagger+(1-r^2)|21\rangle\langle21|
                         +|22\rangle\langle22|.
\end{aligned}
\tag{135.5}
$$

It has partial trace $\operatorname{diag}(1,r^2+1-r^2,1)=I_3$ and
rank three, since $0<r<1$. Multiplying the block and scalar formulas
by (135.5) gives $S_{\rm cert}J_{\mathcal R_*}=0$ identically.
Equation (135.4) makes this $SJ_{\mathcal R_*}=0$ at $N_r=0$.

The equality of the lower and upper values also has explicit off-root
remainders. Use (133.1) to define $T=\operatorname{adj}(LI-A)/\tau$
off the root and $b_{\rm test}=\operatorname{Tr}(TP)$ as before.
Polynomial cofactor expansion gives

$$
\begin{aligned}
\tau\{\operatorname{Tr}(TA)-L\}&=-3N,\\
\tau\{\operatorname{Tr}(T\mathcal R_r\Phi(P))-
                         \operatorname{Tr}Y\}&=\frac r2N_r,\\
\tau\{b_{\rm test}-\operatorname{Tr}Y-L\}
&=-3N+\frac r2N_r.
\end{aligned}
\tag{135.6}
$$

For the first identity one may take traces in
$(LI-A)\operatorname{adj}(LI-A)=NI_3$; the second follows by
substitution of (130.3) and (129.9), and the third is their sum.
All three are identities from the displayed finite polynomials.
The simultaneous equations $N=N_r=0$ and $\tau>0$ prove the exact
matching equality in (135.3) at the same root as the upper certificate.
$\square$

**Proposition 135.2 (Lower bound for every complex CPTP decoder).** For
every complex CPTP map $\mathcal R:M_3\to M_3$, $e(\mathcal R)\ge L_*$.

*Proof.* For a Hermitian trace-zero matrix $H$ the variational formula
is $\frac12\|H\|_1=\max_{0\preceq E\preceq I}\operatorname{Tr}(EH)$.
Applying it separately to each of the nine physical inputs and then
averaging gives, with $J=J_{\mathcal R}$,

$$
\begin{aligned}
e(\mathcal R)
&\ge\frac19\sum_{j,\ell=0}^2
\operatorname{Tr}\{T_{j\ell}[P_{j\ell}-\mathcal R\Phi(P_{j\ell})]\}\\
&=b_{\rm test}-\operatorname{Tr}(WJ)\\
&=b_{\rm test}-\operatorname{Tr}Y+\operatorname{Tr}(SJ)\\
&=L_*+\operatorname{Tr}(SJ)\ge L_*.
\end{aligned}
\tag{135.7}
$$

The first term in the average is $b_{\rm test}$ by unitary invariance.
The second is the Choi pairing (134.2). The third line uses
$\operatorname{Tr}_{\rm out}J=I_3$, and the fourth uses (135.3).
Finally $S,J\succeq0$ imply
$\operatorname{Tr}(SJ)=\operatorname{Tr}(S^{1/2}JS^{1/2})\ge0$,
even when their entries are complex and they do not commute.
The map $\mathcal R$ is the same in all nine terms and is otherwise
unrestricted. This proves (128.6), and with Proposition 132.2 proves
Theorem 128.2. $\square$

The nine pairs support a bound on the full density set. They are not a
replacement of its upper objective by a finite probe objective. The
universal input bound is supplied by the whole-simplex argument in
§132, while the nine pairs give the universal decoder lower bound.

## 136. The complete input equality set for the displayed decoder

**Theorem 136.1 (Phase orbit and no genuinely mixed maximizers).** For
$\rho\in\mathsf D_3$,

$$
\frac12\|\rho-\mathcal R_*\Phi(\rho)\|_1=L_*
\quad\Longleftrightarrow\quad
\rho=|\psi_{\alpha,\beta}\rangle\langle\psi_{\alpha,\beta}|
\text{ for some }\alpha,\beta\in\mathbb R,
\tag{136.1}
$$

where

$$
|\psi_{\alpha,\beta}\rangle=
\sqrt{p_*}|0\rangle+e^{i\alpha}\sqrt{x_*}|1\rangle
                          +e^{i\beta}\sqrt{y_*}|2\rangle.
\tag{136.2}
$$

In particular every density of rank at least two has strict error
below $L_*$ for this decoder. Every pure edge or vertex input also
has strict error below $L_*$.

*Proof.* For a pure input, (130.5) identifies equality at $L>0$ with
$N=0$. By (132.2), its populations must be exactly $(p_*,x_*,y_*)$.
Covariance then gives precisely (136.2). The boundary bounds already
give strict inequality on all edges and vertices.

At the contact the recovered density $Q$ in (130.3) is positive
definite. Its $01$ block has first diagonal entry $p>0$ and determinant

$$
r^2p(v_1-x/16)=\frac{r^2p(9x+6y)}{16}>0.
\tag{136.3}
$$

Its $22$ entry equals $(1-r^2)v_1+v_2>0$. Thus $A=P-Q$ is strictly
negative on the two-dimensional subspace $z^\perp$ and has the positive
eigenvalue $L$. Its inertia is exactly one positive and two negative
eigenvalues. There is no zero eigenvalue. The maximizing effect in
the trace-distance variational formula is consequently unique, namely
$T$; on the negative spectral subspace an attaining effect must be
zero and on the positive subspace it must be the identity.
These assertions persist under diagonal phase conjugation.

Now suppose a mixed density $\rho=\sum_i t_iP_i$, with positive
weights, attains $L$. Choose an effect $E$ attaining the variational
maximum for its error. Then

$$
L=\sum_i t_i\operatorname{Tr}\{E[P_i-\mathcal R_*\Phi(P_i)]\}
\le\sum_i t_i\frac12\|P_i-\mathcal R_*\Phi(P_i)\|_1\le L.
\tag{136.4}
$$

Every $P_i$ must be a pure contact, and $E$ must be its unique effect.
A vector spanning the range of $T$ has all three components nonzero,
because $T_{ii}>0$. If two phase conjugates of $T$ agree, the relative
diagonal unitary acts on that vector by a scalar. Its three diagonal
phases must therefore coincide. The corresponding input projectors
in (136.2) are the same. All $P_i$ in (136.4) are consequently
identical, so $\rho$ is pure. This proves both directions of (136.1).
$\square$

The equality statement is quantified over inputs for the particular
map $\mathcal R_*$ of (128.4). It does not identify the input equality
sets of every other optimal decoder.

## 137. Necessary optimal support and uniquely determined reduced data

**Theorem 137.1 (Support required of every optimizer).** If a complex
CPTP map $\mathcal R$ attains $e(\mathcal R)=L_*$, then

$$
SJ_{\mathcal R}=0,\qquad
\operatorname{ran}J_{\mathcal R}\subseteq
\operatorname{span}\{
|00\rangle+r_*|11\rangle,\ |21\rangle,\ |22\rangle\}.
\tag{137.1}
$$

*Proof.* Equality in (135.7) forces $\operatorname{Tr}(SJ)=0$.
For two positive semidefinite matrices this implies $SJ=0$:
$\operatorname{Tr}(SJ)=\|S^{1/2}J^{1/2}\|_{\rm HS}^2$, so the Gram
factor vanishes. In (135.2) the only kernel direction is
$|00\rangle+r|11\rangle$. The five nonzero scalar blocks are strictly
positive, and the other two directions are $|21\rangle$ and
$|22\rangle$. Hence the displayed space is exactly $\ker S$.
This argument precedes any averaging or reality restriction on the
optimizer. $\square$

**Proposition 137.2 (Reduced parameters after the prescribed operations).**
For any optimal $\mathcal R$, perform the diagonal-unitary twirl of
[TR, Lemma 112.2],

$$
\overline{\mathcal R}
=\int\operatorname{Ad}_{U^\dagger}\circ\mathcal R
                              \circ\operatorname{Ad}_U\,dU.
\tag{137.2}
$$

Then remove its $02$ and $12$ coherence multipliers by the pinching
described below; denote the resulting map by $\mathcal R^\flat$.
Its population matrix and retained $01$ multiplier are necessarily

$$
C_*=
\begin{pmatrix}
1&0&0\\
0&r_*^2&0\\
0&1-r_*^2&1
\end{pmatrix},\qquad \xi_*=r_*,
\tag{137.3}
$$

where $\mathcal R^\flat(E_{jj})=\sum_i(C_*)_{ij}E_{ii}$ and
$\mathcal R^\flat(E_{01})=\xi_*E_{01}$.
The composite $\mathcal R^\flat\Phi$ equals $\mathcal R_*\Phi$.
These are the six independent column-stochastic population coordinates
and the single retained multiplier of the reduced parametrization.

*Proof.* The cited twirl preserves CPTP and cannot increase $e$;
therefore it preserves optimality here. Its Choi action averages
conjugation by $U^\dagger\otimes U^{\mathsf T}$, equivalently by
$U\otimes\overline U$ after inversion of the integration variable.
On the support in (137.1) the directions
$v=|00\rangle+r|11\rangle$ and $|22\rangle$ have the trivial character,
whereas $|21\rangle$ has the nontrivial character $u_2\overline{u_1}$.
Thus the twirl removes cross terms involving $|21\rangle$ and either
of the other directions. It can retain a cross term between $v$ and
$|22\rangle$; discarding it without explanation would assert more
than the support result.

Pinch the remaining Choi matrix between the three orthogonal lines
$\mathbb Cv$, $\mathbb C|21\rangle$ and $\mathbb C|22\rangle$.
This preserves positivity. The cross term $|v\rangle\langle22|$
and its adjoint have zero output partial trace. Moreover their only
map entries are the $02$ and $12$ multipliers and their adjoints.
Since (127.4) deletes both corresponding coherences, pinching changes
neither the trace-preserving constraint nor the composite after $\Phi$.
This defines the asserted removal and gives

$$
J_{\mathcal R^\flat}
=\alpha vv^\dagger+\delta|21\rangle\langle21|
                         +\eta|22\rangle\langle22|,
\qquad \alpha,\delta,\eta\ge0.
\tag{137.4}
$$

The trace-preserving equations are
$\alpha=1$, $\alpha r^2+\delta=1$, and $\eta=1$.
They give uniquely $\alpha=1$, $\delta=1-r^2$ and $\eta=1$.
Reading the matrix units gives (137.3) and (130.1), hence the equality
of the two composites. $\square$

Theorem 137.1 is necessary for every optimal decoder.
Proposition 137.2 is uniqueness after exactly its stated twirl and
invisible-multiplier removal. Neither statement asserts that the full
untwirled map is unique, that support alone suffices for optimality,
or that all remaining decoder freedom has been parameterized.

## 138. Primary-literature correspondence and mathematical scope

The following bounded correspondences concern the methods and the
common-map objective used above.

| Source | Exact correspondence and use |
| --- | --- |
| [Coutts, Girard and Watrous, arXiv:1810.13295v4, Theorem 3][CGW] | `literature-attested`: convex channel optimality is expressed through a subgradient and a positive complementary Choi slack. In the present notation the subgradient is $-W$, and the slack is $I\otimes Y-W$. |
| [Matsumoto, arXiv:1012.2650v7, §5, Theorem 5, (12)][MAT] | `literature-attested`: comparison of state experiments uses one CPTP reconstruction map satisfying a full trace-norm bound for every index. Set the source states to $\Phi(\rho)$, the target states to $\rho$, and the full trace tolerance to $e_\rho=2L_*$. |
| [Jenčová, arXiv:1512.07016v2, §4, Theorem 4(iii)][JC] | `literature-attested`: the state-experiment reconstruction condition is $\sup_\theta\|\sigma_\theta-\alpha(\rho_\theta)\|_1\le2\epsilon$. With source $\rho_\theta=\Phi(\rho)$, target $\sigma_\theta=\rho$ and $\alpha=\mathcal R$, the parameter is $\epsilon=L_*$. |
| [Actual erased-history terminal recovery, §§93, 105, 112, 120, 122, 124][TR] | `repo-derived`: actual coordinate transport, compact attainment, pure-input reduction, diagonal twirl, rational interval conventions, the pure-target determinant/inertia criterion and the output-first Choi convention are reused with their stated domains. |
| §§128–137 of this volume | `repo-derived`: the isolated four-polynomial root, the exact value, the boundary/chord upper certificate, the nine-input Choi lower certificate, and the stated input equality and necessary-support consequences are derived here. |

For precision in the first correspondence, extend the objective to
all Hermitian Choi matrices by

$$
f(J)=\max_{P\ {\rm pure}}
\lambda_{\max}(P-\mathcal R_J\Phi(P)),
\tag{138.1}
$$

where $\mathcal R_J$ is the linear map with Choi matrix $J$.
This is a finite continuous convex function on the full Hermitian
space. On CPTP matrices it equals (127.5), by pure-input reduction
and (130.5). Each contact pair in §134 supplies an active affine
functional at $J_{\mathcal R_*}$; their average therefore supplies
$-W\in\partial f(J_{\mathcal R_*})$. The Choi set has the positive
definite relative-interior point $I_9/3$, so the relative-interior
hypothesis of [CGW, Theorem 3] holds. Complementarity gives

$$
(-W)J_{\mathcal R_*}=-(I\otimes Y)J_{\mathcal R_*},\qquad
\operatorname{Tr}_{\rm out}[(-W)J_{\mathcal R_*}]=-Y,
\tag{138.2}
$$

which identifies the signs in that theorem's supporting inequality.
The direct proof (135.7) already establishes the lower bound and does
not assume an uncomputed dual optimum or invoke a minimax exchange.

For the second and third correspondences the experiment index can
range over all densities, or over all pure projectors using the
pure-input reduction. Both comparisons retain a single common
reconstruction map and their full-trace/half-trace factor of two.
Ancillary decision spaces in equivalent statistical comparison
criteria do not become input references or accessible history in
(127.5). The channel diamond-deficiency problem in the comparison
literature is not the objective being evaluated here.

The arithmetic specification consists of the finite coefficient table,
rational centre and box, integer determinant formulas, Hessian sums,
interval operations and sign enclosures of §129. The all-input and
all-decoder quantifiers are established by the analytic arguments
of §§131–135, rather than by a numerical grid. The result is confined
to the parameter $s=1/4$ of (127.3), the identity target and the stated
unassisted density tests. It asserts neither a value at other parameters
nor a full classification of untwirled optimal maps. The bibliography
supports the indicated general methods and objective correspondence;
the exact contact and value follow from the certificates in this
volume, without a priority or physical-realization claim.

[TR]: AURIC_FIB_ACTUAL_ERASED_HISTORY_TERMINAL_RECOVERY.md "AURIC FIB actual erased-history terminal recovery"
[CGW]: https://arxiv.org/pdf/1810.13295v4 "Bryan Coutts, Mark Girard and John Watrous, Certifying optimality for convex quantum channel optimization problems, Theorem 3"
[MAT]: https://arxiv.org/pdf/1012.2650v7 "Keiji Matsumoto, A quantum version of randomization criteria, Section 5, Theorem 5"
[JC]: https://arxiv.org/pdf/1512.07016v2 "Anna Jenčová, Comparison of quantum channels and statistical experiments, Section 4, Theorem 4"

## 追加锚（本行以下为增补区）

## 139. The complete complex optimal-decoder disk

Throughout this section put $r=r_*$, $L=L_*$ and
$(p,x,y)=(p_*,x_*,y_*)$, with the root specified in Definition 128.1
and isolated by Lemma 129.2. The value and necessary support used here
are Theorems 128.2 and 137.1. The competitors remain all complex CPTP
maps on $M_3$, with the common-decoder, all-density, identity-target
quantifiers of Definition 127.2. In particular no reality, covariance,
unitality or prescribed-family condition is imposed on a competitor.

**Theorem 139.1 (All optimizers, including the PSD circle).** Set

$$
\eta=1-r^2>0,\qquad
B_r=\big[\,|00\rangle+r|11\rangle,\ |21\rangle,\ |22\rangle\,\big].
\tag{139.1}
$$

A complex CPTP map $\mathcal R$ has $e(\mathcal R)=L$ if and only if
there is a unique $z\in\mathbb C$, $|z|\le1$, such that

$$
J_{\mathcal R}=B_r
\begin{pmatrix}
1&0&z\\
0&\eta&0\\
\overline z&0&1
\end{pmatrix}B_r^\dagger.
\tag{139.2}
$$

In the output-first convention (134.2), this is exactly the map

$$
\boxed{
\mathcal R_z(X)=
\begin{pmatrix}
X_{00}&rX_{01}&zX_{02}\\
rX_{10}&r^2X_{11}&rzX_{12}\\
\overline zX_{20}&r\overline zX_{21}&\eta X_{11}+X_{22}
\end{pmatrix}}
\qquad(X\in M_3).
\tag{139.3}
$$

A Kraus list valid on the entire closed disk is

$$
K_0=\operatorname{diag}(1,r,\overline z),\qquad
K_1=\sqrt\eta\,|2\rangle\langle1|,\qquad
K_2=\sqrt{1-|z|^2}\,|2\rangle\langle2|.
\tag{139.4}
$$

Here $\mathcal R_0=\mathcal R_*$ of (128.4). The conjugate in $K_0$
is essential: $K_0E_{02}K_0^\dagger=zE_{02}$, in agreement with
(139.3) and with $J_{\mathcal R,00,22}=z$ in (139.2).

*Proof.* First determine the entire supported CPTP family, without
performing a twirl. By Theorem 137.1 an optimal Choi matrix has range
in $\operatorname{ran}B_r$. The three columns of $B_r$ are independent,
so it has a unique representation $J=B_rHB_r^\dagger$ with $H$
Hermitian. A left inverse of $B_r$ shows that $J\succeq0$ is
equivalent to $H\succeq0$. For general Hermitian $H=(H_{ab})_{a,b=0}^2$,
the output partial trace is

$$
\operatorname{Tr}_{\rm out}(B_rHB_r^\dagger)
=H_{00}E_{00}+(r^2H_{00}+H_{11})E_{11}+H_{22}E_{22}
 +H_{12}E_{12}+\overline{H_{12}}E_{21}.
\tag{139.5}
$$

For example the two terms joining the first column to $|21\rangle$
have distinct output indices and vanish under this partial trace;
$|21\rangle\langle22|$ has equal output indices and contributes
$E_{12}$. Thus trace preservation imposes exactly

$$
H=H(h,z):=
\begin{pmatrix}
1&h&z\\
\overline h&\eta&0\\
\overline z&0&1
\end{pmatrix},\qquad h,z\in\mathbb C.
\tag{139.6}
$$

Since $\operatorname{diag}(\eta,1)$ is positive definite, its Schur
complement gives the closed condition

$$
H(h,z)\succeq0
\quad\Longleftrightarrow\quad
\frac{|h|^2}{\eta}+|z|^2\le1.
\tag{139.7}
$$

This equivalence includes every singular boundary matrix. Reading
matrix units with the same output-first convention gives

$$
\begin{aligned}
\mathcal R_{h,z}(X)-\mathcal R_{0,z}(X)
={}&hX_{01}E_{02}+rhX_{11}E_{12}\\
 &+\overline hX_{10}E_{20}+r\overline hX_{11}E_{21}.
\end{aligned}
\tag{139.8}
$$

It remains to exclude $h\ne0$ by individual physical inputs. Use
$P,T,U_{j\ell},P_{j\ell},T_{j\ell}$ from §§133–134, and write
$q=1/4$. Define

$$
\Gamma=q\sqrt{px}\,T_{02}+rv_1T_{12}
=\frac{\sqrt{xy}}{\tau}
 \{qp(L-d+kx)+rv_1(L+kp)\}>0.
\tag{139.9}
$$

All the factors needed for this strict sign are positive by the
rational bounds of §129. The extra terms of
$\mathcal R_{h,z}\Phi(P_{j\ell})$ relative to
$\mathcal R_{0,z}\Phi(P_{j\ell})$ have entries

$$
\Delta_{02}=qh\sqrt{px}\,\zeta^{-j},\qquad
\Delta_{12}=rhv_1,
\tag{139.10}
$$

and their Hermitian conjugates. Also
$(T_{j\ell})_{20}=\zeta^\ell T_{02}$ and
$(T_{j\ell})_{21}=\zeta^{\ell-j}T_{12}$. Since $\Phi$ deletes the
$02$ and $12$ coherences, $\mathcal R_{0,z}\Phi=\mathcal R_*\Phi$.
The identity $AT=LT$ from Lemma 133.1 and diagonal covariance of this
composite therefore give the exact score

$$
\operatorname{Tr}\{T_{j\ell}
 [P_{j\ell}-\mathcal R_{h,z}\Phi(P_{j\ell})]\}
=L-2\Gamma\operatorname{Re}(h\zeta^{\ell-j}).
\tag{139.11}
$$

For an optimal decoder every such score is at most $L$, by the
trace-distance variational formula for the individual input.
Taking $\ell-j=0,1,2$ modulo three gives

$$
\operatorname{Re}h\ge0,\qquad
\operatorname{Re}(h\zeta)\ge0,\qquad
\operatorname{Re}(h\zeta^2)\ge0.
\tag{139.12}
$$

Their sum is zero because $1+\zeta+\zeta^2=0$. Each is therefore zero.
Writing $h=a+ib$, the first gives $a=0$ and the second then gives
$-\sqrt3 b/2=0$. Hence $h=0$. Condition (139.7) now becomes precisely
$|z|\le1$, proving necessity on the whole PSD boundary as well as
in its interior.

Conversely, for any $|z|\le1$ the Kraus operators (139.4) have adjoint
products summing to

$$
\operatorname{diag}(1,r^2,|z|^2)+\eta E_{11}
 +(1-|z|^2)E_{22}=I_3.
\tag{139.13}
$$

They give (139.3) directly, hence a CPTP map with Choi matrix (139.2).
The erased coherences again give
$\mathcal R_z\Phi=\mathcal R_*\Phi$, so Theorem 128.2 proves its
optimality. Finally $\mathcal R_z(E_{02})=zE_{02}$ proves uniqueness
of the disk coordinate. $\square$

The reduction from (139.7) to (139.2) uses the individual phase scores,
not their average. Their average cancels the $h$ term and would leave
all of (139.7). Similarly a twirl can remove $h$ from a noncovariant
map without proving that the untwirled map was optimal. Theorem 139.1
therefore supplies the classification not asserted by Proposition 137.2.

## 140. The common composite, the support face and original coordinates

**Corollary 140.1 (One recovered channel).** For every optimal decoder,
the composite on every complex matrix is the same map

$$
\begin{aligned}
v_{1,q}(X)&=\frac{(1+q)X_{11}+(1-q)X_{22}}2,\\
\mathcal C_q(X)&=
\begin{pmatrix}
X_{00}&qrX_{01}&0\\
qrX_{10}&r^2v_{1,q}(X)&0\\
0&0&X_{11}+X_{22}-r^2v_{1,q}(X)
\end{pmatrix},\qquad q=1/4.
\end{aligned}
\tag{140.1}
$$

Consequently the complete optimal set is the full CPTP fiber

$$
\operatorname{Opt}_{1/4}
=\{\mathcal R\ {\rm CPTP}:\mathcal R\Phi_{1/4}=\mathcal C_{1/4}\}
=\{\mathcal R_z:|z|\le1\}.
\tag{140.2}
$$

*Proof.* Compose (139.3) with (127.3). The image of $\Phi_q$ has zero
$02$ and $12$ entries and the displayed populations, so the result is
(140.1), independently of $z$. Theorem 139.1 gives the second equality.
Any CPTP map with this same composite has the same all-density error,
which is $L_*$; this proves the first equality in both directions.
$\square$

The term fiber here means equality of linear maps on the entire
channel image. For $q\ne0$ the population transformation on
$\operatorname{span}\{E_{11},E_{22}\}$ has determinant $q$, and the
$01$ and $10$ multipliers are $q$. Thus

$$
\operatorname{span}_{\mathbb C}\Phi_q(\mathsf D_3)
=\operatorname{span}_{\mathbb C}
 \{E_{00},E_{11},E_{22},E_{01},E_{10}\}.
\tag{140.3}
$$

Here densities span $M_3$ over $\mathbb C$, so the density image and
matrix image have the same complex span. Distinct $z$'s change only
invisible coherences, with the linked actions
$E_{02}\mapsto zE_{02}$ and $E_{12}\mapsto rzE_{12}$ and their
conjugates. They are distinct legal extensions of one restriction.

**Corollary 140.2 (Dimension, ranks and symmetry).** The optimal set is
an affine closed disk of real dimension two. Every interior point has
Choi rank three; every point on $|z|=1$ has Choi rank two. There is no
rank-one optimal decoder. All of them commute with conjugation by
every diagonal unitary, and all are nonunital.

*Proof.* The dependence of (139.2) on $(\operatorname{Re}z,
\operatorname{Im}z)$ is real affine and injective. Its coefficient
matrix has eigenvalues

$$
\eta,\qquad 1+|z|,\qquad1-|z|.
\tag{140.4}
$$

Congruence by the injective $B_r$ preserves rank, which proves all
rank statements, including the circle. Equation (140.4) describes the
coefficient matrix; it is not asserted to be the spectrum of the
unnormalized Choi matrix itself. For
$U=\operatorname{diag}(u_0,u_1,u_2)$, $|u_i|=1$, each off-diagonal
entry in (139.3) has the same phase $u_i\overline{u_j}$ as its input
entry, and its output populations depend only on input populations.
Thus, even for nonreal $z$,

$$
\mathcal R_z\operatorname{Ad}_U
=\operatorname{Ad}_U\mathcal R_z,\qquad
\mathcal R_z(I_3)=\operatorname{diag}(1,r^2,2-r^2)\ne I_3.
\tag{140.5}
$$

The last inequality uses $0<r<1$. $\square$

**Proposition 140.3 (The larger exposed face and the nonface disk).**
The exposed CPTP face selected by the slack $S$ in Lemma 135.1 is
exactly

$$
\mathcal E_r=\left\{B_rH(h,z)B_r^\dagger:
 h,z\in\mathbb C,\quad |h|^2/\eta+|z|^2\le1\right\}.
\tag{140.6}
$$

It has real affine dimension four. The optimal disk is a proper
subset of this face and is not itself a face of the CPTP set.

*Proof.* On the CPTP set $\operatorname{Tr}(SJ)\ge0$, and it is zero
at $J_{\mathcal R_*}$. Hence its zero set is an exposed face. For PSD
matrices, equality is equivalent to $\operatorname{ran}J\subseteq
\ker S=\operatorname{ran}B_r$, as proved in Theorem 137.1. Equations
(139.5)–(139.7) give precisely (140.6). Its two complex coordinates
are independent and its inequality has strict interior at $(0,0)$,
so its affine dimension is four.

Choose any real $t$ with $0<t<\sqrt\eta$. The two matrices
$B_rH(t,0)B_r^\dagger$ and $B_rH(-t,0)B_r^\dagger$ are CPTP by
(139.7). Each is nonoptimal: among the three numbers
$\operatorname{Re}(\pm t\zeta^m)$ at least one is negative, and
(139.11) then gives an individual score strictly exceeding $L$.
Their midpoint is $B_rH(0,0)B_r^\dagger=J_{\mathcal R_*}$, which
is optimal. This violates the defining segment property of a face
for the optimal disk. $\square$

**Corollary 140.4 (The specified original decoder coordinates).** With
the actual $U_0$ of (127.2), or equivalently [TR, (93.2)], all optimal
decoders for $\mathcal N_3$ are exactly

$$
D_z=\mathcal R_z\circ\operatorname{Ad}_{U_0^\dagger},\qquad
|z|\le1,\qquad D_z\mathcal N_3=\mathcal C_{1/4}.
\tag{140.7}
$$

Their Choi ranks and nonunitality are unchanged. Their transported
covariance identity, for every diagonal unitary $U$, is

$$
D_z\operatorname{Ad}_{U_0UU_0^\dagger}
=\operatorname{Ad}_U D_z.
\tag{140.8}
$$

*Proof.* Apply the bijection (127.6), which is [TR, (93.10)] with the
unchanged original identity target. Precomposition by a unitary
channel gives an invertible unitary congruence of Choi matrices and
preserves Choi rank. It also sends $I_3$ to $I_3$, so
$D_z(I_3)=\mathcal R_z(I_3)$. Equation (140.8) follows from (140.5)
by substitution. These are coordinate identities for the explicitly
specified model; they do not assert a physical realization. $\square$

## 141. An analytic branch of exact contact certificates

We now let $q$ vary near $q_0=1/4$. The channel is exactly $\Phi_q$
in (127.3), and the objective is [TR, (105.2)]:

$$
e_q(\mathcal R)=\max_{\rho\in\mathsf D_3}
 \frac12\|\rho-\mathcal R\Phi_q(\rho)\|_1,\qquad
\mu(q)=\min_{\mathcal R\ {\rm complex\ CPTP}}e_q(\mathcal R).
\tag{141.1}
$$

Every quantifier of Definition 127.2 is retained. On $0<q<1$,
$\Phi_q$ is CPTP by [TR, Lemma 105.2]. Explicitly a Kraus list is

$$
\operatorname{diag}(1,q,0),\quad
\sqrt{(1-q)(1+2q)/2}\,E_{11},\quad
\sqrt{(1-q)/2}\,E_{21},\quad
\sqrt{(1-q)/2}\,E_{12},\quad
\sqrt{(1+q)/2}\,E_{22}.
\tag{141.2}
$$

The adjoint products sum to $I_3$; the identity
$(1+q)/2-q^2=(1-q)(1+2q)/2$ verifies the $11$ population. This
channel family is defined on an interval, whereas actual horizons
in (127.3) still use the discrete parameters $s_n$.

**Definition 141.1 (The parameter-dependent polynomial system).**
Substitute $y=1-p-x$ first and put

$$
\begin{aligned}
v_1&=\frac{(1+q)x+(1-q)y}{2},&
v_2&=x+y-v_1,\\
k&=1-qr,& d&=x-r^2v_1,\\
N(q;r,L,p,x)
&=L^3-L(d^2+k^2px+py+xy)
 -p\{d(k^2x-y)+2kxy\},\\
F(q;r,L,p,x)&=(N,N_p,N_x,N_r)^{\mathsf T}.
\end{aligned}
\tag{141.3}
$$

All derivatives include the displayed substitution for $y$. Thus $F$
is a specified polynomial map, and at $q=q_0$ it is precisely
$\mathcal F$ of (128.1). The order of its four unknowns is
$u=(r,L,p,x)$. Its Jacobian with respect to those unknowns is

$$
D_uF=
\begin{pmatrix}
N_r&N_L&N_p&N_x\\
N_{pr}&N_{pL}&N_{pp}&N_{px}\\
N_{xr}&N_{xL}&N_{xp}&N_{xx}\\
N_{rr}&N_{rL}&N_{rp}&N_{rx}
\end{pmatrix}.
\tag{141.4}
$$

**Lemma 141.2 (Nonsingularity at the specified root).** The Jacobian
$D_uF(q_0;u_*)$ is nonsingular. The following rational outer enclosure
holds on the entire box $\mathcal B$ of (128.2):

$$
\begin{aligned}
1.6294931870268401569269244
&\ \le\det D_uF(q_0;u)\\
&\ \le1.6294931870268401607302784
\qquad(u\in\mathcal B).
\end{aligned}
\tag{141.5}
$$

*Proof.* Nonsingularity already follows directly from the finite
root-isolation data, without relying on a rounded determinant. Let
$M=D\mathcal F(c)^{-1}$ be the rational matrix (129.5)–(129.7).
The Hessian bound and (129.8) give

$$
\sup_{u\in\mathcal B}\|I-MD_uF(q_0;u)\|_\infty
 <\frac{3499}{8}\,10^{-20}<1.
\tag{141.6}
$$

The Neumann series makes $MD_uF(q_0;u)$ invertible at every such $u$,
so $D_uF(q_0;u_*)$ is invertible. The determinant enclosure (141.5)
uses only the same finite rational specification: obtain the entries
in (141.4) by differentiating the nine coefficients (129.1)–(129.2),
and evaluate the determinant by

$$
\det D_uF=\sum_{\pi\in S_4}\operatorname{sgn}(\pi)
              \prod_{i=0}^3(D_uF)_{i,\pi(i)}.
\tag{141.7}
$$

Interval evaluation on $[c_j-10^{-20},c_j+10^{-20}]$, with the
operations of Convention 129.3, gives the stated rational outer
bounds. All their finite decimal endpoints are rational numbers;
they are enclosures on the box, not evaluations at an approximate
zero. In particular the nonsingularity needed below is at the
isolated root itself. $\square$

**Theorem 141.3 (Local analytic persistence).** There are an open
interval $I\subset(0,1)$ containing $q_0=1/4$ and real-analytic
functions

$$
q\longmapsto(r(q),L(q),p(q),x(q)),\qquad y(q)=1-p(q)-x(q),
\tag{141.8}
$$

whose values at $q_0$ are $(r_*,L_*,p_*,x_*)$, such that
$F(q;r(q),L(q),p(q),x(q))=0$. The interval can be chosen so that,
for every $q\in I$, the unrestricted value is $\mu(q)=L(q)$ and
all optimal decoders are exactly (139.3)–(139.4), with $r=r(q)$
and $|z|\le1$. Every such decoder has the same composite (140.1),
with these continued $q,r(q)$. The support ellipsoid, optimal disk,
ranks, covariance, nonunitality and nonface conclusions all persist.

The interval is existential; no numerical radius is specified.
The analytic branch is locally unique as a zero of the four-variable
system near $u_*$. The decoders themselves form a disk and are not
unique. The proof of the value and classification is completed in
§§142–143, after the following strictness lemma.

**Lemma 141.4 (All strict conditions can be retained together).**
Along the branch define

$$
\begin{aligned}
a_0&=L^2-d^2-xy,& a_1&=L(L+d)-py,\\
a_2&=L(L-d)-k^2px,& \tau&=a_0+a_1+a_2=N_L,\\
\beta&=k(L+d)+y,& \omega&=qpx\beta,\\
w&=\omega/\tau,& g&=p(a_0-a_2)+r\omega.
\end{aligned}
\tag{141.9}
$$

One common smaller open interval around $q_0$ retains

$$
\begin{gathered}
0<q,r<1,\qquad p,x,y>0,\qquad L,\tau,a_0,a_1,a_2>0,\\
\beta,\ L-d+kx,\ L+kp,\ a_2-a_0,\ a_2-a_1,\ g>0.
\end{gathered}
\tag{141.10}
$$

It also retains $\eta=1-r^2>0$, $v_1,v_2,k,w>0$, and all the
strict scalar slacks displayed in §143.

*Proof.* Analytic IFT applied to the polynomial $F$ and Lemma 141.2
first gives (141.8) on an open interval about $q_0$. The rational
centre and box of Definition 128.1 and Lemma 129.2 give the first
line of basic parameter signs. At $q_0$, (141.9) specializes exactly
to (129.9), with $\omega=\omega_0$. Thus every remaining sign in
(141.10) is supplied by the whole-box bounds in §129. The following
additional outer intervals specify the small margin and useful
positive factors more precisely, again at $q=q_0$ and for every
$u\in\mathcal B$:

| Expression | Rational lower endpoint | Rational upper endpoint |
| --- | --- | --- |
| $g$ | $0.00011128205452303927215155916$ | $0.00011128205452303931320279159$ |
| $g/\tau$ | $0.00013053824554842534240889235$ | $0.00013053824554842539059288603$ |
| $\eta$ | $0.15071210256946835223440677$ | $0.15071210256946835227126951$ |
| $k$ | $0.76960795675759931317030883$ | $0.76960795675759931317530884$ |
| $w$ | $0.023137200311339624401525323$ | $0.023137200311339624412468074$ |
| $\Gamma/\sqrt{xy}$, with $\Gamma$ as in (139.9) | $0.38187019888773971797618789$ | $0.38187019888773971812051055$ |
| $pr^2(v_1-q^2x)$ | $0.082831250381897860842067617$ | $0.082831250381897860858603919$ |
| $(1-r^2)v_1+v_2$ | $0.40709797066733872287663940$ | $0.40709797066733872298039953$ |
| $w(r+1/r)$ | $0.046428843542101801214667873$ | $0.046428843542101801237634023$ |

For reproducibility, these intervals use (141.3), then (141.9) in
displayed order and the rational interval operations of Convention
129.3. In particular

$$
\frac{\Gamma}{\sqrt{xy}}
=\frac{qp(L-d+kx)+rv_1(L+kp)}{\tau}
\tag{141.11}
$$

has no square roots in its interval calculation. Positivity of
$\tau$ and $r$ is established before their reciprocals are taken.
The positive lower bound for $g$, despite its smaller size, is
explicitly part of the hypothesis retained here.

Every expression in the finite list (141.10) is continuous along
the analytic branch and strictly positive at $q_0$. Intersecting
finitely many neighborhoods retains all these signs on one open
interval in $(0,1)$. On it, $v_1,v_2>0$ by their positive population
coefficients, $k=1-qr>0$, $\eta>0$ and $w=qpx\beta/\tau>0$.
The five scalar slack signs follow from (141.10) and their exact
formulas (143.6). No zero eigenvalue of a singular matrix is inferred
to remain zero by this continuity argument. Its preservation will
instead follow from the identities in §143. $\square$

## 142. Uniform closed-boundary control and the global cubic upper bound

**Lemma 142.1 (A gap on the entire boundary).** After a further shrink
of $I$, the decoder $\mathcal R_0(q)$ given by (139.4) with $z=0$
and $r=r(q)$ has pure-input error strictly below $L(q)$ on the whole
closed population boundary, uniformly in that boundary.

*Proof.* Let

$$
\Delta=\{(s,t):s,t\ge0,\ s+t\le1\},\qquad
P(s,t)=a(s,t)a(s,t)^{\mathsf T},\quad
a(s,t)=(\sqrt s,\sqrt t,\sqrt{1-s-t})^{\mathsf T},
\tag{142.1}
$$

and write

$$
f(q;s,t)=\frac12\|P(s,t)-\mathcal R_0(q)\Phi_q(P(s,t))\|_1.
\tag{142.2}
$$

This is jointly continuous, including the edges and vertices. The
square roots of zero populations are continuous, and both channels
and the matrix trace norm are continuous. Lemma 131.1 and (130.5)
give $f(q_0;s,t)\le3/5$ for every $(s,t)\in\partial\Delta$.
Set

$$
\Delta_0=L_*-3/5>0,\qquad \epsilon_0=\Delta_0/4.
\tag{142.3}
$$

The set $\partial\Delta$ is compact. Joint continuity near
$\{q_0\}\times\partial\Delta$ therefore supplies one neighborhood
of $q_0$ on which $f(q;s,t)\le3/5+\epsilon_0$ for every boundary
point. For example, restrict $q$ initially to a closed interval
inside the branch domain and use uniform continuity on its product
with $\partial\Delta$. Continuity of $L(q)$ allows a common shrink
so that

$$
\max_{(s,t)\in\partial\Delta}f(q;s,t)
 \le3/5+\epsilon_0,\qquad L(q)\ge L_*-\epsilon_0.
\tag{142.4}
$$

The gap is at least $\Delta_0-2\epsilon_0=\Delta_0/2>0$.
This treats the entire closed boundary, not a finite set of boundary
tests. The interval is further intersected with the one from Lemma
141.4. $\square$

**Proposition 142.2 (Global upper certificate on the interval).**
For every $q\in I$,

$$
e_q(\mathcal R_0(q))=L(q),\qquad\mu(q)\le L(q).
\tag{142.5}
$$

*Proof.* Fix $q$, and hold its $r(q),L(q)$ fixed. For arbitrary
nonnegative populations $(s,t,1-s-t)$, composing the explicit maps
gives (130.3)–(130.4) with $r/4$ replaced by $qr$, and with $v_1,k,d$
from (141.3). Thus

$$
\begin{aligned}
Q_q(s,t)&=\mathcal R_0(q)\Phi_q(P(s,t)),\\
A_q(s,t)&=P(s,t)-Q_q(s,t),\\
\det(L(q)I_3-A_q(s,t))&=N(q;r(q),L(q),s,t).
\end{aligned}
\tag{142.6}
$$

The determinant identity follows by the same three-by-three
expansion as Lemma 130.2, now with $k=1-qr$ and
$d=t-r^2\{(1+q)t+(1-q)(1-s-t)\}/2$. No specialization of $q$
is used in that expansion. The polynomial in $(s,t)$ has degree
at most three: $d$ is affine in the populations, the terms multiplying
$L$ have degree at most two, and the remaining terms have degree at
most three.

The matrix $Q_q(s,t)$ is a density for every point of $\Delta$,
because both maps are CPTP. Hence the pure-target criterion (130.5)
applies, including at all vertices:

$$
\frac12\|A_q(s,t)\|_1=\lambda_{\max}(A_q(s,t)),\qquad
N(q;r,L,s,t)\ge0
\ \Longleftrightarrow\ \lambda_{\max}(A_q(s,t))\le L.
\tag{142.7}
$$

Here $L=L(q)>0$. To see directly why the determinant sign is
sufficient, $P-Q$ is nonpositive on the two-dimensional orthogonal
complement of the pure input vector and has trace zero. Its other
two eigenvalues are nonpositive, so the other two factors of
$\det(LI-A)$ are strictly positive. This is a pure-target argument,
not a sign criterion for arbitrary Hermitian matrices.

Lemma 142.1 now gives strict positivity of $N$ on the entire
boundary of $\Delta$. At its interior point $(p(q),x(q))$ the branch
equations give $N=N_p=N_x=0$. Apply the already proved cubic chord
Lemma 132.1: on every line through that point the polynomial is
$t^2(\alpha+\beta t)$, whose affine factor is positive at the two
boundary endpoints and hence on the whole segment. Consequently

$$
N(q;r(q),L(q),s,t)\ge0,\qquad
N=0\ \Longleftrightarrow\ (s,t)=(p(q),x(q)).
\tag{142.8}
$$

The distance is therefore at most $L(q)$ for all nonnegative-amplitude
pure inputs and equals it at the contact. The maps $\Phi_q$ and
$\mathcal R_0(q)$ commute with all diagonal unitary conjugations,
as their displayed actions show. Every complex pure state is a
diagonal phase conjugate of such a nonnegative-amplitude state,
including those with zero populations. Unitary invariance of the
trace norm proves the same bound for every complex pure input.
For a mixed density $\rho=\sum_i t_iP_i$, convexity gives

$$
\frac12\|\rho-\mathcal R_0(q)\Phi_q(\rho)\|_1
\le\sum_i t_i\frac12\|P_i-\mathcal R_0(q)\Phi_q(P_i)\|_1
\le L(q).
\tag{142.9}
$$

This uses a single decoder for every term. The contact attains
$L(q)$, proving (142.5). $\square$

## 143. Exact slack identities and the unrestricted local lower bound

Fix $q\in I$ and evaluate all contact quantities at (141.8). Let
$P=aa^{\mathsf T}$ for $a=(\sqrt p,\sqrt x,\sqrt y)^{\mathsf T}$,
and let $A=P-\mathcal R_0(q)\Phi_q(P)$. The nine phases
$U_{j\ell}$ remain exactly those of (134.1).

**Lemma 143.1 (Physical effects and exact kernel preservation).** Put

$$
T=\frac{\operatorname{adj}(LI_3-A)}{\tau},\qquad t_i=T_{ii}.
\tag{143.1}
$$

Then $T$ is a rank-one orthogonal projector, $AT=LT$, and

$$
\begin{aligned}
T_{ii}&=a_i/\tau,\\
T_{01}&=\sqrt{px}\,\beta/\tau,\\
T_{02}&=\sqrt{py}(L-d+kx)/\tau,\\
T_{12}&=\sqrt{xy}(L+kp)/\tau.
\end{aligned}
\tag{143.2}
$$

All these entries are strictly positive. With $v_0=p$, define

$$
\begin{aligned}
W_q&=\frac19\sum_{j,\ell=0}^2
 (U_{j\ell}TU_{j\ell}^\dagger)
 \otimes\Phi_q(U_{j\ell}PU_{j\ell}^\dagger)^{\mathsf T}\\
&=\sum_{i,j=0}^2 t_i v_j|ij\rangle\langle ij|
 +w\{|00\rangle\langle11|+|11\rangle\langle00|\},\\
Y_q&=\operatorname{diag}(pt_0+rw,\ v_1t_2,\ v_2t_2),\qquad
S_q=I_{\rm out}\otimes Y_q-W_q.
\end{aligned}
\tag{143.3}
$$

The slack is PSD and its kernel is exactly

$$
\ker S_q=\operatorname{span}\{
 |00\rangle+r(q)|11\rangle,\ |21\rangle,\ |22\rangle\}.
\tag{143.4}
$$

*Proof.* By Proposition 142.2 and the pure-target criterion,
$LI_3-A\succeq0$ at the contact. Its determinant is $N=0$ and its
adjugate has positive trace $\tau=N_L>0$. Therefore it has rank two
and its adjugate is PSD of rank one. Normalizing by its trace proves
the projector assertion. Direct cofactor expansion is the displayed
matrix (133.1), with the general $q$ auxiliaries (141.3). This proves
(143.2); (141.10) gives every strict sign and every denominator.
The adjugate identity gives $AT=LT$.

The charge calculation (134.4) is unchanged by $q$: only the retained
$01$ coherence is multiplied by $q$. Its coefficient in the averaged
functional is now $q\sqrt{px}T_{01}=qpx\beta/\tau=w$. Thus (143.3)
specifies all 81 entries of $W_q$, including all its zero entries.
The transpose is the ordinary matrix transpose, as in (134.2), even
when the input/effect pair is complex. The nine projectors and effects
are physical and distinct, since $p,x,y>0$, by the same argument as
Definition 134.1.

Differentiate the determinant (141.3) with $d_r=-2rv_1$ and $k_r=-q$.
The resulting exact identity, before imposing any root equation, is

$$
N_r=2rv_1(a_1-a_2)+2\omega.
\tag{143.5}
$$

Consequently at $N_r=0$ the $00,11$ block of $S_q$ and its seven
remaining scalar blocks are exactly

$$
S_q[00,11]=
\begin{pmatrix}rw&-w\\-w&w/r\end{pmatrix}
=\frac wr\begin{pmatrix}r\\-1\end{pmatrix}
              \begin{pmatrix}r&-1\end{pmatrix},
\tag{143.6}
$$

| Coordinate | Scalar block of $S_q$ |
| --- | --- |
| $01$ | $v_1(a_2-a_0)/\tau$ |
| $02$ | $v_2(a_2-a_0)/\tau$ |
| $10$ | $\{g+p(a_2-a_1)\}/\tau$ |
| $12$ | $v_2(a_2-a_1)/\tau$ |
| $20$ | $g/\tau$ |
| $21$ | $0$ |
| $22$ | $0$ |

For clarity about exact zeros, let $S_{\rm cert}$ denote this block
matrix even off the root, using (141.9) wherever $r\tau\ne0$.
Subtraction from the actual $I\otimes Y_q-W_q$ gives the identity

$$
(I\otimes Y_q-W_q)-S_{\rm cert}
=-\frac{N_r}{2r\tau}|11\rangle\langle11|,\qquad
S_{\rm cert}B_r=0.
\tag{143.7}
$$

Indeed its only possible discrepant entry is
$v_1(a_2-a_1)/\tau-w/r=-N_r/(2r\tau)$ at $11,11$.
The other entries follow by subtracting the diagonal terms in
(143.3). Both identities in (143.7) are exact for every $q$ with
the displayed definitions; the first remainder vanishes on the
branch because $N_r=0$ there.

The five nonzero scalar blocks are strictly positive by Lemma 141.4.
The coupled block has one positive eigenvalue $w(r+1/r)$ and one
zero eigenvalue, with kernel vector $(1,r)^{\mathsf T}$. Its other
two zero blocks are exactly the $21$ and $22$ directions. This proves
PSD and exactly (143.4). In particular the kernel identities hold
at every $q\in I$; continuity of a singular PSD matrix alone would
not prove them. $\square$

**Proposition 143.2 (Exact lower value and complete continued fiber).**
For every complex CPTP map $\mathcal R:M_3\to M_3$ and $q\in I$,

$$
e_q(\mathcal R)\ge L(q)+\operatorname{Tr}(S_qJ_{\mathcal R})
\ge L(q).
\tag{143.8}
$$

Equality in the minimax problem holds exactly for
$\mathcal R=\mathcal R_z(q)$, $|z|\le1$, as specified by (139.3)
with $r=r(q)$. In particular

$$
\begin{aligned}
\mu(q)&=L(q),\\
\operatorname{Opt}_q
&=\{\mathcal R_z(q):z\in\mathbb C,\ |z|\le1\}\\
&=\{\mathcal R\ {\rm CPTP}:\mathcal R\Phi_q=\mathcal C_q\}.
\end{aligned}
\tag{143.9}
$$

*Proof.* The matching lower value is an identity of the certificate,
not an additional numerical assertion. Define
$b_{\rm test}=\operatorname{Tr}(TP)$. Taking the trace of
$(LI-A)\operatorname{adj}(LI-A)=NI_3$ gives, off the root,
$\tau\{\operatorname{Tr}(TA)-L\}=-3N$. Also the explicit composite
has diagonal $(p,r^2v_1,v_1+v_2-r^2v_1)$ and $01$ entry
$qr\sqrt{px}$. Therefore, with $Q=\mathcal R_0(q)\Phi_q(P)$,

$$
\begin{aligned}
\operatorname{Tr}(TQ)-\operatorname{Tr}Y_q
 &=r^2v_1(t_1-t_2)+rw=\frac{rN_r}{2\tau},\\
\tau\{b_{\rm test}-\operatorname{Tr}Y_q-L\}
 &=-3N+\frac r2N_r.
\end{aligned}
\tag{143.10}
$$

In the first line $2qr\sqrt{px}T_{01}=2rw$ is the off-diagonal
contribution and $rw$ is subtracted as part of $\operatorname{Tr}Y_q$;
then (143.5) gives the equality. Thus $N=N_r=0$ implies
$b_{\rm test}-\operatorname{Tr}Y_q=L$ exactly.

For arbitrary complex CPTP $\mathcal R$, the variational formula
for each Hermitian trace-zero input error, followed by averaging
over the nine physical pairs, gives

$$
\begin{aligned}
e_q(\mathcal R)
&\ge\frac19\sum_{j,\ell}
 \operatorname{Tr}\{T_{j\ell}
 [P_{j\ell}-\mathcal R\Phi_q(P_{j\ell})]\}\\
&=b_{\rm test}-\operatorname{Tr}(W_qJ_{\mathcal R})\\
&=L+\operatorname{Tr}(S_qJ_{\mathcal R})\ge L.
\end{aligned}
\tag{143.11}
$$

The Choi pairing uses (134.2) and $\operatorname{Tr}_{\rm out}
J_{\mathcal R}=I_3$; the last inequality uses $S_q,J_{\mathcal R}
\succeq0$. No entry of $J_{\mathcal R}$ has been assumed real or
phase invariant. Proposition 142.2 gives the opposite minimax
inequality, proving $\mu(q)=L(q)$.

If $\mathcal R$ is optimal, (143.11) forces
$\operatorname{Tr}(S_qJ_{\mathcal R})=0$ and hence
$S_qJ_{\mathcal R}=0$, by the PSD Gram-factor argument of Theorem
137.1. Lemma 143.1 gives its exact support. The supported TP and PSD
calculations (139.5)–(139.7), which depend only on $r\in(0,1)$,
then give the full family $H(h,z)$ with
$|h|^2/(1-r^2)+|z|^2\le1$. At the continued contact, (143.2) gives

$$
\Gamma(q)=q\sqrt{px}\,T_{02}+rv_1T_{12}>0.
\tag{143.12}
$$

The individual score calculation (139.8)–(139.11), with $q$ in place
of $1/4$, reads exactly

$$
\operatorname{Tr}\{T_{j\ell}
 [P_{j\ell}-\mathcal R_{h,z}\Phi_q(P_{j\ell})]\}
=L(q)-2\Gamma(q)\operatorname{Re}(h\zeta^{\ell-j}).
\tag{143.13}
$$

Every score is at most $L(q)$ for an optimum. The same three
nonnegative real parts summing to zero force $h=0$, including for
all singular supported matrices. Conversely, every $|z|\le1$ gives
a CPTP map by (139.4) and has the common composite $\mathcal C_q$
by direct composition. Its error is $L(q)$ by Proposition 142.2.
Any CPTP map with that composite has the same error and is therefore
one of these maps. This proves every equality in (143.9) and the
complete boundary classification. $\square$

This completes Theorem 141.3. Corollaries 140.1–140.2 and Proposition
140.3 apply at each $q\in I$, since their proofs use exactly this
disk, the supported ellipsoid and $0<r(q)<1$. For the specified
unitary $U_0$, define the mathematical family
$\mathcal N_q=\operatorname{Ad}_{U_0}\Phi_q$. Its optimal decoders are
$D_z(q)=\mathcal R_z(q)\operatorname{Ad}_{U_0^\dagger}$ and have
$D_z(q)\mathcal N_q=\mathcal C_q$, with the transported covariance
(140.8). At $q=q_0$ this is the actual third-horizon identity of
(127.3). Varying $q$ on $I$ does not assert an identification with
additional actual horizons.

## 144. Input equality throughout the continued disk

**Corollary 144.1 (All maximizing densities for every optimal decoder).**
For $q\in I$, $|z|\le1$ and $\rho\in\mathsf D_3$,

$$
\frac12\|\rho-\mathcal R_z(q)\Phi_q(\rho)\|_1=L(q)
\quad\Longleftrightarrow\quad
\rho=|\psi_{\alpha,\beta}(q)\rangle
       \langle\psi_{\alpha,\beta}(q)|
\quad\text{for some }\alpha,\beta\in\mathbb R,
\tag{144.1}
$$

where

$$
|\psi_{\alpha,\beta}(q)\rangle
=\sqrt{p(q)}|0\rangle+e^{i\alpha}\sqrt{x(q)}|1\rangle
                    +e^{i\beta}\sqrt{y(q)}|2\rangle.
\tag{144.2}
$$

Thus no density of rank at least two maximizes, and every pure edge
or vertex has strict error below $L(q)$.

*Proof.* The composites are identical by (143.9), so it suffices to
consider $\mathcal R_0(q)$. For pure inputs, (142.7)–(142.8) and
diagonal covariance give exactly the populations and phases in
(144.2). At a contact the recovered density $Q=\mathcal C_q(P)$ is
positive definite. Its $01$ block has first diagonal entry $p>0$ and

$$
\begin{aligned}
\det Q[0,1]&=pr^2(v_1-q^2x)>0,\\
v_1-q^2x&=\frac{(1-q)(1+2q)}2x+\frac{1-q}{2}y>0,\\
Q_{22}&=(1-r^2)v_1+v_2>0.
\end{aligned}
\tag{144.3}
$$

Therefore $A=P-Q$ is strictly negative on the two-dimensional
orthogonal complement of the input vector. Since it also has the
positive eigenvalue $L$, it has one positive and two strictly negative
eigenvalues. Its maximizing effect is uniquely its positive spectral
projector $T$. This conclusion is invariant under all the diagonal
phases. The entries in (143.2) show that a spanning vector of $T$
has all three coordinates nonzero.

If a density $\rho=\sum_i t_iP_i$, $t_i>0$, attained $L$, an effect
$E$ attaining its variational trace-distance maximum would satisfy

$$
L=\sum_i t_i\operatorname{Tr}\{E[P_i-\mathcal C_q(P_i)]\}
\le\sum_i t_i\frac12\|P_i-\mathcal C_q(P_i)\|_1\le L.
\tag{144.4}
$$

Every $P_i$ must be a pure contact and must have the same unique
maximizing effect $E$. If two phase-conjugated contact effects agree,
their relative diagonal unitary is scalar on a vector with all three
coordinates nonzero. Its three phases must coincide, so the two
underlying contact input projectors agree as well. All $P_i$ are
therefore identical, and $\rho$ is pure. This proves both directions
of (144.1), extending the equality argument of Theorem 136.1 to the
entire optimizer disk and its local branch. $\square$

## 145. Method correspondence and limits of the continuation

The mathematical ingredients above have the following scopes.

| Source or method | Correspondence and boundary of use |
| --- | --- |
| [Choi, Completely positive linear maps on complex matrices][CHOI] | The finite-dimensional Choi theorem identifies complete positivity with positivity of the full Choi matrix. Trace preservation is imposed separately by the output partial trace. The supported congruence, Schur complement and Kraus lists in §139 use this theorem, with the tensor ordering fixed by (134.2). |
| [Jenčová, Generalized channels: channels for convex subsets of the state space, §4, Theorem 3, (10)–(11)][JGEN] | Equality of CP maps on a state subset is an affine Choi restriction described by its annihilator, with the transpose in the trace pairing. Here the subset is $\Phi_q(\mathsf D_3)$ and its span is (140.3). The generalized normalization of that paper is not substituted for the full TP equations (139.5)–(139.6). |
| [Coutts, Girard and Watrous, Theorem 3][CGW] | Convex channel optimality uses a supporting subgradient and complementary PSD slack. The full-domain convex extension and relative-interior hypothesis are as in (138.1)–(138.2), with $\Phi_q$ in place of $\Phi$. The active nine-contact average supplies $-W_q$; (143.7) and (143.10) supply exact complementarity and matching value. The direct proof (143.11) establishes the lower bound without assuming dual attainment or exchanging minimax quantifiers. |
| [Krantz and Parks, A Primer of Real Analytic Functions, §2.3][RAIFT] | Analytic IFT applies to a real-analytic finite-dimensional equation with invertible derivative in the unknown variables. Here it applies only to $F(q;u)=0$ at $(q_0,u_*)$, using Lemma 141.2. It gives a local analytic certificate branch; feasibility, the all-input upper bound and optimizer completeness require the separate arguments of §§141–143. |
| [Bellon, Henrion, Kungurtsev and Mareček, §2.3, Lemma 2.22 and Theorem 2.23][BH] | Their smooth SDP solution-branch result uses their surjective-constraint setting, continuously differentiable data, primal/dual strict feasibility and a unique strictly complementary optimal pair. The uniqueness hypothesis fails for the optimizer disk here, so that result is not invoked to justify Theorem 141.3. |
| The experiment comparisons in §138, [MAT, Theorem 5] and [JC, Theorem 4(iii)] | The common map is still tested on all densities. Their full trace-norm tolerance is $2L(q)$, or equivalently their half-norm parameter is $L(q)$. Decision-space comparison criteria do not give the decoder an input reference, history or environment, and do not replace (141.1) by a stabilized norm. |

The particular disk classification follows from the full supported TP
family and the individual phase constraints, not from these general
references alone. Its persistence combines analytic IFT, strict scalar
inequalities, compactness of the entire closed boundary, the cubic
chord Lemma 132.1, and exact kernel identities. The base premises are
the public root of Lemma 129.2, the value of Theorem 128.2, the boundary
bound of Lemma 131.1 and the support of Theorem 137.1; the formulas
and rational data used to continue them are displayed in this volume.
No private computation or runtime file is a mathematical dependency
of the argument.

The conclusion is existence on some open $I\subset(0,1)$ containing
$1/4$. It supplies no explicit radius, no continuation to every
positive parameter, no assertion at $q\to0$, and no value at another
actual horizon. It gives no sign-based comparison with a different
horizon's optimizer fiber, no parameter-slope or further algebraic
classification, and no additional physical identification. The unitary
transport uses only the already specified $U_0$ and leaves the original
identity target unchanged. The citations attest the stated methods
and correspondences within their indicated hypotheses; no exhaustive
literature or priority claim is made.

[CHOI]: https://doi.org/10.1016/0024-3795(75)90075-0 "Man-Duen Choi, Completely positive linear maps on complex matrices, Linear Algebra and its Applications 10, 285–290"
[JGEN]: https://arxiv.org/pdf/1105.1899v2 "Anna Jenčová, Generalized channels: channels for convex subsets of the state space, Section 4, Theorem 3"
[RAIFT]: https://doi.org/10.1007/978-0-8176-8134-0 "Steven G. Krantz and Harold R. Parks, A Primer of Real Analytic Functions, Section 2.3"
[BH]: https://arxiv.org/pdf/2104.05445v3 "Bellon, Henrion, Kungurtsev and Mareček, Parametric semidefinite programming, Section 2.3"

## 追加锚（本行以下为增补区）

## 146. The entire positive parameter interval

The following continuation retains the objective (141.1) and every
quantifier of Definition 127.2. The restriction at the end of §145
is the scope of the local Theorem 141.3. The finite certificates below
supply its hypotheses throughout the larger interval stated here.

**Theorem 146.1 (Global positive continuation).** Conditional on the
root, value, boundary and support premises of Lemmas 129.2 and 131.1
and Theorems 128.2 and 137.1, and the general-parameter implications proved in
§§139–145, there is a real analytic branch
$u(q)=(r(q),L(q),p(q),x(q))$, $0<q\le1/4$, satisfying (141.3),
anchored at $u(1/4)=u_*$ and specified uniquely in the tubes below.
For every such $q$,

$$
\begin{aligned}
\mu(q)&=\min_{\mathcal R\ {\rm complex\ CPTP}}
 \max_{\rho\in\mathsf D_3}\tfrac12
 \|\rho-\mathcal R\Phi_q(\rho)\|_1=L(q),\\
\operatorname{Opt}_q
 &=\{\mathcal R_{r(q),z}:z\in\mathbb C,\ |z|\le1\}\\
 &=\{\mathcal R\ {\rm complex\ CPTP}:
       \mathcal R\Phi_q=\mathcal C_q\},\\
J_{\mathcal R_{r,z}}&=B_r
 \begin{pmatrix}1&0&z\\0&1-r^2&0\\\overline z&0&1\end{pmatrix}
 B_r^\dagger,\qquad
B_r=[\,|00\rangle+r|11\rangle,|21\rangle,|22\rangle\,],\\
\mathcal C_q(X)&=
\begin{pmatrix}
X_{00}&qr(q)X_{01}&0\\
qr(q)X_{10}&r(q)^2v_{1,q}(X)&0\\
0&0&X_{11}+X_{22}-r(q)^2v_{1,q}(X)
\end{pmatrix},\\
v_{1,q}(X)&=\{(1+q)X_{11}+(1-q)X_{22}\}/2.
\end{aligned}
\tag{146.1}
$$

The decoder action is exactly (139.3); the circle $|z|=1$ is included.
One map is fixed before the unknown input, which ranges over every
complex mixed qutrit density as well as every pure density. The
identity target and half trace metric are retained. The decoder has
no input reference, history or environment. Analyticity at a positive
endpoint means local analytic extension of the contact root there.
No assertion about an optimizer fiber at $q=0$ is made.

For use below write $J=D_uF$ and retain exactly (141.3) and (141.9),
including substitution of $y=1-p-x$ before differentiation. The
pointwise implication already proved in §§142–144 requires $F=0$,
the strict scalar signs (141.10), and strict separation on the whole
closed population boundary. Its determinant, cubic chord, nine-contact
Choi slack, exact kernel, individual phase and mixed-density arguments
are used with these hypotheses; they do not require that the parameter
remain in the original existential neighborhood. The following finite data supply these hypotheses and their connection.

## 147. Exact interval rules and the common strict conditions

Every integer and fraction below is exact. Indices on vectors and
matrices begin at zero; coordinates are ordered $(r,L,p,x)$, and
rows of $F$ are ordered $(N,N_p,N_x,N_r)$. Expand rational polynomials
and differentiate over $\mathbb Q$ before interval substitution.
For a rational interval $A=[a,b]$ define outward dyadic rounding by

$$
\mathcal D(A)=
 [\lfloor2^{128}a\rfloor/2^{128},
  \lceil2^{128}b\rceil/2^{128}].
\tag{147.1}
$$

Addition and subtraction use endpoint addition and
$[a,b]-[c,d]=[a-d,b-c]$. Multiplication uses the minimum and maximum
of the four endpoint products. A rational constant is first enclosed
by $\mathcal D([a,a])$. Apply $\mathcal D$ after each coefficient
addition, subtraction and multiplication. Division by a rational
constant uses its exact reciprocal; no interval containing zero is
inverted. Polynomial multiplication means coefficient convolution,
without truncating any degree. Powers start from the constant one
and use repeated multiplication. Sums and convolution indices are
accumulated in increasing lexicographic order; products of
monomial powers use variable order $(q,r,L,p,x)$. All intervals
include their endpoints.

For an interval-coefficient polynomial $A(t)=\sum_{k=0}^d A_k t^k$
on $[-1,1]$ use

$$
\mathcal T(A)=A_0+[-S,S],\qquad
 S=\sum_{k=1}^d\max(|\inf A_k|,|\sup A_k|).
\tag{147.2}
$$

This is an enclosure for the whole interval, not interpolation-node
testing. For an interval $A$, write $|A|_{\max}$ for the maximum
absolute endpoint. The infinity matrix norm is bounded by the
maximum row sum of these absolute interval bounds. In §148 perform
all substitutions, preconditioning and subtraction as polynomials
in $t$ before taking $\mathcal T$. In particular the derivative
certificate is the interval polynomial $I-M_jJ$, not subtraction
of separately ranged scalar functions. Root errors are inserted as
constant coefficient intervals, so they vary independently over
the whole root box. These rules are ordinary rational interval
operations with specified outward rounding.

For the near-zero chart in §149, all polynomial coefficients and
interval operations may instead be kept as exact rationals; its
range rule $\mathcal A$ and perturbation rule are specified there.
Outward dyadic enclosure of a final rational endpoint is given by
(147.1), or by its explicitly indicated precision in the tables.

Set $a=1-r^2(1+q)/2$ and $b=r^2(1-q)/2$. The 31 quantities in
the next table have the definitions (141.3), (141.9), and these nine
boundary expressions:

$$
 a,\quad k-a,\quad b,\quad1-b,\quad
 E_x=(2-b)L-1,\quad E_y=(2k-a)L-k^2,\quad
 C_x=L^2-a^2,\quad C_m=L^2+ab-1/2,\quad C_y=L^2-b^2.
\tag{147.3}
$$

The column $B_h$ means $h\ge B_h>0$ on every upper tube of §148.
The last columns mean $h/q^{m_h}\ge T_h>0$ on the near-zero tube
for $q>0$, using the polynomial extension described in §149.
For the first row $q/q=1$. Every $T_h$ is an exact rational lower
bound; vanishing orders are given explicitly rather than replaced
by an unscaled positive lower bound.

| $h$ | $B_h$ on the upper tubes | $m_h$ | $T_h$ on the scaled tube |
| --- | --- | --- | --- |
| $q$ | $1/16$ | 1 | $1$ |
| $1-q$ | $3/4$ | 0 | $15/16$ |
| $r$ | $921538779/1000000000$ | 0 | $193661/200000$ |
| $1-r$ | $13784517/500000000$ | 1 | $108497/250000$ |
| $1-r^2$ | $1699313/31250000$ | 1 | $851631/1000000$ |
| $p$ | $313763719/1000000000$ | 0 | $163161/500000$ |
| $x$ | $285315799/1000000000$ | 0 | $31939/100000$ |
| $y$ | $88238517/250000000$ | 0 | $83/250$ |
| $L$ | $19312023/31250000$ | 0 | $326363/500000$ |
| $\tau$ | $852472937/1000000000$ | 0 | $239563/250000$ |
| $\beta$ | $881277767/1000000000$ | 0 | $968741/1000000$ |
| $L-d+kx$ | $83136299/100000000$ | 0 | $947547/1000000$ |
| $L+kp$ | $214863717/250000000$ | 0 | $119759/125000$ |
| $a_2-a_0$ | $4702129/250000000$ | 1 | $297337/1000000$ |
| $a_2-a_1$ | $19433379/1000000000$ | 1 | $154413/500000$ |
| $g$ | $13813/1000000000$ | 2 | $3333/1000000$ |
| $v_1$ | $328666453/1000000000$ | 0 | $66379/200000$ |
| $v_2$ | $337508423/1000000000$ | 0 | $66661/200000$ |
| $k$ | $384801341/500000000$ | 0 | $468621/500000$ |
| $a_0$ | $53494619/200000000$ | 0 | $312367/1000000$ |
| $a_1$ | $129967021/500000000$ | 0 | $312459/1000000$ |
| $a_2$ | $40632629/125000000$ | 0 | $332567/1000000$ |
| $a$ | $234597517/500000000$ | 0 | $62169/125000$ |
| $k-a$ | $7509599/25000000$ | 0 | $109239/250000$ |
| $b$ | $159225061/500000000$ | 0 | $218317/500000$ |
| $1-b$ | $111347939/200000000$ | 0 | $246687/500000$ |
| $E_x$ | $851701/50000000$ | 1 | $65617/250000$ |
| $E_y$ | $623623/31250000$ | 1 | $79813/250000$ |
| $C_x$ | $80869999/500000000$ | 0 | $175557/1000000$ |
| $C_m$ | $3131757/100000000$ | 0 | $14447/100000$ |
| $C_y$ | $230334603/1000000000$ | 0 | $46183/250000$ |

In particular the upper tubes have $g\ge13813/10^9>1/10^5$.
On the scaled tube, the displayed lower bounds give

$$
1-r>2q/5,\quad1-r^2>4q/5,\quad
 a_2-a_0>q/4,\quad a_2-a_1>q/4,\quad
 g>q^2/400,\quad E_x>q/4,\quad E_y>q/4.
\tag{147.4}
$$

The signs imply $w=qpx\beta/\tau>0$ and the positivity of the
phase factor (141.11). The singular slack uses the exact identities
(143.5)–(143.7) and (143.10), so its nullspace is preserved exactly.

**Lemma 147.1 (Whole closed boundary).** The nine boundary signs in
(147.3) imply strict error below $L$ on all three closed edges,
including the vertices.

Indeed the two edge determinant identities (131.3)–(131.4), with
these general $a,b,k$, give the exact edge maxima
$1/(2-b)$ on $x=0$ and $k^2/(2k-a)$ on $y=0$.
The signs $b,1-b,a,k-a>0$ justify the denominators and the interior
locations of their maxima. The positive numerators $E_x,E_y$
separate these maxima from $L$. On $p=0$, $x+y=1$, use

$$
 L^2(x+y)^2-(ax-by)^2-xy
 =C_xx^2+2C_mxy+C_yy^2>0.
\tag{147.5}
$$

All three coefficients are positive and at least one of $x,y$ is
nonzero. This proves the claimed separation throughout the entire
closed boundary. The fixed-parameter bound $3/5$ is not used at
other parameters. $\square$

## 148. Upper charts and their finite rational interpolation table

For $j=1,\ldots,16$ put

$$
 Q_j=[(64-3j)/256,(67-3j)/256],\qquad
 q_j(t)=(131-6j)/512+(3/512)t,\quad -1\le t\le1,
 \qquad\rho=2^{-30}.
\tag{148.1}
$$

These intervals cover exactly $[1/16,1/4]$. Let $D=2^{160}$ and
$t_h=(h-2)/2$, $h=0,\ldots,4$. The integer rows in the first table
specify the quartic predictor, with no rounding, by

$$
 c_{j,i}(t)=D^{-1}\sum_{h=0}^4 V_{jh,i}
 \prod_{\substack{0\le k\le4\\k\ne h}}
 \frac{t-t_k}{t_h-t_k},\qquad
 M_{j,ik}=D^{-1}W_{jik}.
\tag{148.2}
$$

The second table gives all four rows of every $W_j$. Repeated node
rows at adjacent slab endpoints are intentionally included to make
the endpoint identities directly visible. The tubes are
$c_j(t)+[-\rho,\rho]^4$. Interpolation only specifies these rational
polynomials; all claims concern their whole tubes.

| $j$ | $t_h$ | $V_{jh,r}$ | $V_{jh,L}$ | $V_{jh,p}$ | $V_{jh,x}$ |
| --- | --- | --- | --- | --- | --- |
| 1 | -1 | 1349978908001810920898204264873895035008475496516 | 906189722338790514402768406992182388091343578038 | 459493547063657052717421751112666739418635434366 | 419917380837720993768179573485669010581705630228 |
| 1 | -1/2 | 1349186383244898515507201182510899497763372543429 | 905437945428015254247243682238924505955648629003 | 459260638038204503993531225395508843607961501111 | 419184579812631944318159462049477201823328882936 |
| 1 | 0 | 1348404672125532660723918389315351958269828617648 | 904687713833352869711126978472108591928891163327 | 459029869215642540116330584950687874006461533330 | 418453445509310305347887174807040831688652744988 |
| 1 | 1/2 | 1347633700022728541713842377621058620556743878347 | 903939012244140389429736711662552654391541923197 | 458801230728754683839572713424354132067560997370 | 417723960223437037407251081066665703283929896998 |
| 1 | 1 | 1346873393707123164190736657205980510283851214581 | 903191825494341890705538793504931076808045672457 | 458574712956137186897175693526866473811230625871 | 416996106402593961384054197160675302232991239976 |
| 2 | -1 | 1353258685867319244972472901221260615785872896590 | 909212594564999241640631740615241479635649310557 | 460446791319360754680850938700335636501354590601 | 422865611718445496354799052736317209873960605024 |
| 2 | -1/2 | 1352422131680809598055714486829617233969574508027 | 908454480298691329005011065343416191644992768109 | 460205217782828327621161524570506671720077352347 | 422125963625047855467653914681863208424583974265 |
| 2 | 0 | 1351596704012225298929274701224988541540417825245 | 907697974090091414977336192108281186788640614241 | 459965826439956716950307045559833168529150829887 | 421388054647006457334537646009480383120955158663 |
| 2 | 1/2 | 1350782322432425128285144039862938723688802978246 | 906943060023564448009835860966673857154158049147 | 459728606408145614844083927978361958765687605182 | 420651866443626970054821744774360142440703136722 |
| 2 | 1 | 1349978908001810920898204264873895035008475496516 | 906189722338790514402768406992182388091343578038 | 459493547063657052717421751112666739418635434366 | 419917380837720993768179573485669010581705630228 |
| 3 | -1 | 1356717829989741078726649820296455863780233708131 | 912261456114603100270763841445852518621462064592 | 461435134314040448011296784502416427307077755019 | 425841967953040515724932151921600131794195804842 |
| 3 | -1/2 | 1355835934721650092691630621384696361394942311297 | 911496747255512290214950122900881342359552475919 | 461184717874394148776078895502561608095523078427 | 425095176614191886874622408067728606577572799896 |
| 3 | 0 | 1354965503115620767210289052328697036177986930575 | 910733711726731653525621149762951240490131595060 | 460936529819309866262673002961317212216601115004 | 424350199449816729980440274780826776637852730606 |
| 3 | 1/2 | 1354106448516529447803626777374396033761469668826 | 909972332962768894178430299505899379282490488187 | 460690558194530537625963650134658222529665036847 | 423607017434424369734488620927651724915776584318 |
| 3 | 1 | 1353258685867319244972472901221260615785872896590 | 909212594564999241640631740615241479635649310557 | 460446791319360754680850938700335636501354590601 | 422865611718445496354799052736317209873960605024 |
| 4 | -1 | 1360361838359127407811240201712802787406288400661 | 915337362175916824521333554300621363243251560953 | 462459332802653137300052339156944845127336320779 | 428847661903297849288031398459485382821074248505 |
| 4 | -1/2 | 1359433188901511836457933233336683407010520060717 | 914565790895818705848246555349794361766251594631 | 462199877670160734764617240954403523247801607481 | 428093419978601109499150055104362875656739958615 |
| 4 | 0 | 1358516366297280318405433898971240252802586457814 | 913795960938287611064967496832838029457791651768 | 461942701555684961568758726451566864367229393971 | 427341070155226198629060865168357362596287191787 |
| 4 | 1/2 | 1357611277202014577203418944274942820536336251558 | 913027855039397917702609305763356907151182673883 | 461687791370019603769185272790524010398038874341 | 426590592671014855573181794868716238715894336160 |
| 4 | 1 | 1356717829989741078726649820296455863780233708131 | 912261456114603100270763841445852518621462064592 | 461435134314040448011296784502416427307077755019 | 425841967953040515724932151921600131794195804842 |
| 5 | -1 | 1364196633579665870451350512261572865941981199096 | 918441412264929384887488867882223351630485168806 | 463520215701915117901176133992801192281222716943 | 431883952678137934785055114076212472803313881377 |
| 5 | -1/2 | 1363219707753456536564172087316384184974929943331 | 917662699351126396113093618011400805638683326039 | 463251507645611773944092743380107054936358167199 | 431121940818862550087128031950957157490669740099 |
| 5 | 0 | 1362254999997924657362005840567701392086139956023 | 916885798676220475236864769412952129641051490609 | 462985133955675013366385906328391702013760325549 | 430361902072380461529357170666916077070439545717 |
| 5 | 1/2 | 1361302409765100574344113070914341526595275527834 | 916110692225176687899568386723225506348332704996 | 462721080336887538901821295425764662010958892894 | 429603815884184517263147769036276299246462161925 |
| 5 | 1 | 1360361838359127407811240201712802787406288400661 | 915337362175916824521333554300621363243251560953 | 462459332802653137300052339156944845127336320779 | 428847661903297849288031398459485382821074248505 |
| 6 | -1 | 1368228595399929742805176470349019875693386305219 | 921574753565632541449516211239684541595607114276 | 464618688579614761160460432742894815664803465046 | 434952149668338556250990783960652344896855427051 |
| 6 | -1/2 | 1367201753499817824272916478033652808246365361861 | 920788607560026490533709731349646581606454489044 | 464340493756027407565931781285434477243447500602 | 434182035609800176380367501141265983783585123664 |
| 6 | 0 | 1366187551111610739468361735001133864814902542726 | 920004347855674778803779410353054519145815987156 | 464064693667597575543757118487815455282824878294 | 433413978993264096012584915220141805462609469231 |
| 6 | 1/2 | 1365185879912316873208410701108755053259240021138 | 919221955629195888299132429292598413917183819890 | 463791272733399635343385219004601380076056207268 | 432647958411984983058883370908993103918772421693 |
| 6 | 1 | 1364196633579665870451350512261572865941981199096 | 918441412264929384887488867882223351630485168806 | 463520215701915117901176133992801192281222716943 | 431883952678137934785055114076212472803313881377 |
| 7 | -1 | 1372464596858496856203463768423384490369400028514 | 924738584558825295279016687264499621177102096107 | 465755738690203491813041075807233057053284478557 | 438053616347564455436322242639133309546288251448 |
| 7 | -1/2 | 1371386072253817305545968092112501056522190060979 | 923944700821939971910546341028649018564908890684 | 465467802329949801533724021145700718817728828848 | 437275053932425928207620410916426239127776896638 |
| 7 | 0 | 1370320641270744145832740545889029096322599829710 | 923152780836176921721698166125348083731224537373 | 465182326436627552524002439463212943456400103845 | 436498636857270384479754351625082194295517149603 |
| 7 | 1/2 | 1369268187175362654989087598835140527470215313841 | 922362804907487674419827129159461405498679839574 | 464899294054270088994152816853108427858860023935 | 435724342798576242177694605995527662803149542797 |
| 7 | 1 | 1368228595399929742805176470349019875693386305219 | 921574753565632541449516211239684541595607114276 | 464618688579614761160460432742894815664803465046 | 434952149668338556250990783960652344896855427051 |
| 8 | -1 | 1376912044499893778373225397257659305925087115333 | 927934158972344984412348370041923353646880507813 | 466932440619688687391773116147357204669376037050 | 441189774367587697035757060011632959627259262654 |
| 8 | -1/2 | 1375779933171644805509541430461095674052147804145 | 927132218663673272457423032504643022554674518511 | 466634485555329042202921905918900868809639843520 | 440402402492837143133867562999704548827206059922 |
| 8 | 0 | 1374661404965883744250044603682406779368444821237 | 926332323206773988951980740389218684135493650038 | 466339062436580519491958512639063520776296684805 | 439617267695657929689607421446678346601709346184 |
| 8 | 1/2 | 1373556334029113466384272677305763613605882506557 | 925534451968936564329554433527182100736879973291 | 466046152832310566993507135406026813620381609871 | 438834346666076282315977855973482078417457857437 |
| 8 | 1 | 1372464596858496856203463768423384490369400028514 | 924738584558825295279016687264499621177102096107 | 465755738690203491813041075807233057053284478557 | 438053616347564455436322242639133309546288251448 |
| 9 | -1 | 1381578923185738016099911951678469105048718769832 | 931162790090078821221565788064119754553599699238 | 468149962612714785615876018614341094607987807836 | 444362107978638939932540201833421676489292463925 |
| 9 | -1/2 | 1380391172061329938880381716041538154622156925078 | 930352459054966767993587699789177369921537951104 | 467841687628624690520173867428538171541264888275 | 443565549458203603694855411420437197582027117778 |
| 9 | 0 | 1379217531988852339001348258732239680799530968083 | 929544257910684668431841101355790505230340954388 | 467536022246110715265615014550636068819837711883 | 442771323885263803906122811847115476645193434066 |
| 9 | 1/2 | 1378057867204174135790910945466772902358034413235 | 928738165011517239486785649573555063917022621917 | 467232946446617362557634203973868596612474899348 | 441979406888036277836833199243406579804212037142 |
| 9 | 1 | 1376912044499893778373225397257659305925087115333 | 927934158972344984412348370041923353646880507813 | 466932440619688687391773116147357204669376037050 | 441189774367587697035757060011632959627259262654 |
| 10 | -1 | 1386473846108164160563227021080020744367460934644 | 934425855462213367486465233237978551652957783470 | 469409573666256609795899150973975560547994754551 | 447572168809264901298053041943275654315717249194 |
| 10 | -1/2 | 1385228240033657564403272764992234380744415030602 | 933606783014145456794168395236374475864745463315 | 469090651648228257808748261775637805246172842004 | 446766029143322149026465001750752593412557540234 |
| 10 | 0 | 1383997314763452005350395710299363808176816741122 | 932789929749272882074634218794148049396196922956 | 468774423547749972347877101265725551142622753908 | 445962322744080028293602043373812968119574204864 |
| 10 | 1/2 | 1382780923738162651230085716645969087933023824828 | 931975272927418688417076362840755126867233143181 | 468460867632898779033441857469976233419357499286 | 445161024096302435697878776548289778815551534015 |
| 10 | 1 | 1381578923185738016099911951678469105048718769832 | 931162790090078821221565788064119754553599699238 | 468149962612714785615876018614341094607987807836 | 444362107978638939932540201833421676489292463925 |
| 11 | -1 | 1391606110709617132460887836596795149825687449552 | 937724802065112061752127200789872479904560315542 | 470712651487898848304277742713281106801794760505 | 450821581043934082518065815759508255650053763081 |
| 11 | -1/2 | 1390300257873418768174761320266789722771698060475 | 936896619650693102791316102803277750402787432954 | 470382727346583305311224911565454761974634648178 | 450005447084971026704177739005597235875026159087 |
| 11 | 0 | 1389009701217344459902656558466857697037450970895 | 936070750310655322539882651740606860189283924098 | 470055588640711217873113628288292175852759734635 | 449191851504945001187804550435375560169750664321 |
| 11 | 1/2 | 1387734282395565535670954985592723012754326272596 | 935247170120912076475011775083458521833442485257 | 469731211783550896332900431375684293746390652899 | 448380767556564085905202270281946497775057116001 |
| 11 | 1 | 1386473846108164160563227021080020744367460934644 | 934425855462213367486465233237978551652957783470 | 469409573666256609795899150973975560547994754551 | 447572168809264901298053041943275654315717249194 |
| 12 | -1 | 1396985761327933293183377459649762717294641728900 | 941061151966127549522287117858378743293445579038 | 472060691432650321700173047086138139824787987025 | 454112047040982547096989494380101358700169634923 |
| 12 | -1/2 | 1395617076919343831989334092426123535165636433860 | 940223471698225522897324224278554683945820597278 | 471719379770704891988253489302075312359881035992 | 453285485545520104047766185187623967101114606903 |
| 12 | 0 | 1394264353954151457521753383602205008099616413085 | 939388203374657421770553576662505294496868266917 | 471380952873085508299643027641093313634067693704 | 452461572707703064387584334214026937709733245372 |
| 12 | 1/2 | 1392927421187150955648435246698393370220705949561 | 938555321788982631432084963048295408627264081975 | 471045385139203979236645582915238616745112522677 | 451640280451870142004996672530225847793216203662 |
| 12 | 1 | 1391606110709617132460887836596795149825687449552 | 937724802065112061752127200789872479904560315542 | 470712651487898848304277742713281106801794760505 | 450821581043934082518065815759508255650053763081 |
| 13 | -1 | 1402623659522077777681540829323200710198851805285 | 944436508556744476325351343270158596301684929472 | 473455316551148349668941526573006776080291616490 | 457445353438379584932075691689848482867512719539 |
| 13 | -1/2 | 1401189347371709767000121239406105137860284666668 | 943588921599114794705117888005962744479118011352 | 473102199038920191417405140786464801029226610747 | 456607909492001133129217364905592747160915313646 |
| 13 | 0 | 1399771716609950294492052341547771665359345132618 | 942743850853309155918933102282804267759099053018 | 472752074116432050040047344862777376564635907335 | 455773230054797128006677641052694816535438226346 |
| 13 | 1/2 | 1398370581839780903330302085246778463630323497508 | 941901269721936433735345389194844312952492149652 | 472404913990117741960045785566432178830389550698 | 454941285617875021770573947426859447214443764546 |
| 13 | 1 | 1396985761327933293183377459649762717294641728900 | 941061151966127549522287117858378743293445579038 | 472060691432650321700173047086138139824787987025 | 454112047040982547096989494380101358700169634923 |
| 14 | -1 | 1408531563196633542069518377365289502758463106310 | 947852563426938996400745406235094995278853042169 | 474898288904573498061879038916206755873889663805 | 460823377800278038792328549851439438756761049581 |
| 14 | -1/2 | 1407028595102276798591696315129861757447875195141 | 946994638211132216895800920285596654475958341998 | 474532911323161159130371548457273430702717986362 | 459974573102172369618974245880747380029424843975 |
| 14 | 0 | 1405543088427278248184429731700945467186055117491 | 946139339334830226634939162852989410228223409436 | 474170643426359615670190906628899703581400648602 | 459128654780438300965434715590920617955211647252 |
| 14 | 1/2 | 1404074842210003529316653678239819129221492139817 | 945286638689609011701801532396563830370598674047 | 473811455025535936183295434973780726257812970824 | 458285591778606800711530244642389809977454801966 |
| 14 | 1 | 1402623659522077777681540829323200710198851805285 | 944436508556744476325351343270158596301684929472 | 473455316551148349668941526573006776080291616490 | 457445353438379584932075691689848482867512719539 |
| 15 | -1 | 1414722215837954773786591765667449564731545909104 | 951311103964814244062299901895235386074419968361 | 476391522328395124360989008504707739498625876471 | 464248095863455960345977578093061769674704001254 |
| 15 | -1/2 | 1413147308227384757600397626397259754566836857462 | 950442384217200668997706938521260468153087452168 | 476013391231773982449139898845786711481088991006 | 463387426855083884819400799669507859779981272853 |
| 15 | 0 | 1411590708257723085040700079787865801507660411207 | 949576407309347187521558846010878613701493155601 | 475638497057222333928888445596667888072803785104 | 462529772589302388661685001807134017513662182612 |
| 15 | 1/2 | 1410052197804960815184837043968716302335973117490 | 948713143488685253425150916937591568250607377980 | 475266806992579963640244966773488264577609554522 | 461675100337193915336047363371683708662782001464 |
| 15 | 1 | 1408531563196633542069518377365289502758463106310 | 947852563426938996400745406235094995278853042169 | 474898288904573498061879038916206755873889663805 | 460823377800278038792328549851439438756761049581 |
| 16 | -1 | 1421209447409068519460412006115562177141446590492 | 954814021778771397053706276088280150817863532684 | 477937096859171609443727783530999770816602579210 | 467721589449613684330902809447029624457490719517 |
| 16 | -1/2 | 1419559034928598258208327353523038282575383612841 | 953934024332004110812437019502166653036436919657 | 477545675798484601645301521561151603152004497103 | 466848525270323196986756712111936397120254150852 |
| 16 | 0 | 1417927849417657472563323447982114813117495973952 | 953056893166724033400477271045312648988509411875 | 477157630028369760220224249892218885286306045415 | 465978611227195706569363857123172534781864327981 |
| 16 | 1/2 | 1416315653778056545483792071821590399892060718341 | 952182596738284802675870326662648031223266980474 | 476772923854287893873031859175586975324149582933 | 465111812782302161144321304317100100848815668499 |
| 16 | 1 | 1414722215837954773786591765667449564731545909104 | 951311103964814244062299901895235386074419968361 | 476391522328395124360989008504707739498625876471 | 464248095863455960345977578093061769674704001254 |

| $j$ | row $i$ | $W_{ji0}$ | $W_{ji1}$ | $W_{ji2}$ | $W_{ji3}$ |
| --- | --- | --- | --- | --- | --- |
| 1 | 0 | 34658217217369536770616059889672377426844637991 | -257429632752019997210796905701532542899524286101 | 1236521903437244935298485609031669823443729477838 | -634810819284445339921863759526277491766053351513 |
| 1 | 1 | 1708172989064322465284009784038641686676225698512 | 0 | 0 | 0 |
| 1 | 2 | -15026347000267079141425703817310837327169951727 | 1000511891465697189766354193268122501268238935274 | -575828415638331478392530265390892212134316860560 | -257429632752019997210796905701532542899524286101 |
| 1 | 3 | -45905605330297958222019123696785672638576637288 | -575828415638331478392530265390892212134316860560 | 932042530148286828780480504324791689801445829825 | 1236521903437244935298485609031669823443729477838 |
| 2 | 0 | 32083198576780425813322463100266887719644421260 | -244272408086436156393446820417745082310537345121 | 1227248644452463133690745548213830309692911898659 | -607361253786552007581992779824098644313199509479 |
| 2 | 1 | 1695776632873090252218566226380722224515829758520 | 1 | 0 | 0 |
| 2 | 2 | -14817174213011718007315440271148020723426416404 | 984006813902635266978023829630438916927869512408 | -562576860870024872325530527516915194543902979174 | -244272408086436156393446820417745082310537345121 |
| 2 | 3 | -44326925380636247199941545739020238542525487957 | -562576860870024872325530527516915194543902979174 | 916167162706088479647540093130306238867014524826 | 1227248644452463133690745548213830309692911898659 |
| 3 | 0 | 29562745334860771109069959768686110681489403005 | -231301818762872739376449429272259581376185072275 | 1218261737876028653229025735970838952894799326354 | -579929766884712655208196101437075576918138155563 |
| 3 | 1 | 1683452521442093478468750062042394666908138685352 | 0 | 0 | 0 |
| 3 | 2 | -14564606680747728963520051960389600715846889550 | 967956912146947722231112350863097267051190234035 | -549740747103495463929476105441555472080397602935 | -231301818762872739376449429272259581376185072275 |
| 3 | 3 | -42699003558545247609444603187529789891136684477 | -549740747103495463929476105441555472080397602935 | 900734633720155440108999637327195763124649432752 | 1218261737876028653229025735970838952894799326354 |
| 4 | 0 | 27100415675670405012431822777127114078058838729 | -218501625137554525564174430503957549377601930823 | 1209554308471001615663025828894223292753637722770 | -552475737230803379325494403487946377124187032613 |
| 4 | 1 | 1671197857676696832532783071602425137382552956694 | 0 | 1 | 0 |
| 4 | 2 | -14268035678495242009949151728220992429691313287 | 952342177103653699269902166206325969959928106485 | -537300093755315189590608418882161891635959489966 | -218501625137554525564174430503957549377601930823 |
| 4 | 3 | -41020452877598009534946345664603040535932393360 | -537300093755315189590608418882161891635959489966 | 885722889244811556382099198293067919000472923869 | 1209554308471001615663025828894223292753637722770 |
| 5 | 0 | 24700073807169030757371459022901499160341945899 | -205855726571431737742260214216329665123047164658 | 1201119965561267638368429759897032118942243989430 | -524957272904199574582330834589268273323820345320 |
| 5 | 1 | 1659009901018953207181432336591844745711486035546 | 0 | 0 | 0 |
| 5 | 2 | -13926744934658236596555619285470202729701370487 | 937143863400778961923220331341275379173843709766 | -525236153576845181020523483712253999366003764928 | -205855726571431737742260214216329665123047164658 |
| 5 | 3 | -39289751882713921463158013630334712917817263148 | -525236153576845181020523483712253999366003764928 | 871111134928901940695573857108010030883952234112 | 1201119965561267638368429759897032118942243989430 |
| 6 | 0 | 22365935410721265027063481028421611705444031327 | -193348090501331784682176544355439504646032220962 | 1192952785879837377424647816440874096886774668459 | -497330961493203004327628787042319855113499813948 |
| 6 | 1 | 1646885964547973555918840353885290653689242515468 | 0 | 0 | 0 |
| 6 | 2 | -13539900517773254134058772961971131211032576446 | 922344403187448601322064896865863533194182065418 | -513531321163797099956072469976112388686537999303 | -193348090501331784682176544355439504646032220962 |
| 6 | 3 | -37505235217484987111528124028241992832132136537 | -513531321163797099956072469976112388686537999303 | 856879735892955060924807829539830537208502755756 | 1192952785879837377424647816440874096886774668459 |
| 7 | 0 | 20102618730951656713531102063349419741453879254 | -180962679135729308390950402041943298071502755272 | 1185047298349218531768716575252152686406223550154 | -469551597322611371010782880897142058237640500220 |
| 7 | 1 | 1634823412358468828125383477020129996891458192078 | 0 | 1 | 1 |
| 7 | 2 | -13106539478451917634242381067334010929429055786 | 907927328460136846432713776169501215571346782781 | -502169049754941558202974604164146358689793746531 | -180962679135729308390950402041943298071502755272 |
| 7 | 3 | -35665082986968045221593355339053312327280242192 | -502169049754941558202974604164146358689793746531 | 843010124656675157982526842992603675558140586702 | 1185047298349218531768716575252152686406223550154 |
| 8 | 0 | 17915202299242107834010748740744293955705033033 | -168683372930377128271823917406682503608945842296 | 1177398470678490869832288388963049080843451685235 | -441571881770718918248837534960265518130803902202 |
| 8 | 1 | 1622819657234830911809281292352801937633961518618 | 0 | 0 | -1 |
| 8 | 2 | -12625557043150242363980131406293476607988164923 | 893877201204388437760635188739267981496941983087 | -491133775528319552207267408434558643819765833204 | -168683372930377128271823917406682503608945842296 |
| 8 | 3 | -33767308772716213149274180330707771139218569175 | -491133775528319552207267408434558643819765833204 | 829484716221090975652920700441206835417893432000 | 1177398470678490869832288388963049080843451685235 |
| 9 | 0 | 15809290462954419134262612286945109938405823900 | -156493889904730539223347815762883693383107542507 | 1170001697667675990449075933494702680167817147826 | -413342091981529142579860605239342175985436586130 |
| 9 | 1 | 1610872158644356322431503155334932390996502973792 | 0 | 0 | 0 |
| 9 | 2 | -12095692122327950411720637192490643894388302041 | 880179550744307999228183805184028414612149931073 | -480410848701125233917517163856460435286550192647 | -156493889904730539223347815762883693383107542507 |
| 9 | 3 | -31809746133761364708882052981576265737207674797 | -480410848701125233917517163856460435286550192647 | 816286829496044272962238445442700234226296807980 | 1170001697667675990449075933494702680167817147826 |
| 10 | 0 | 13791088109842368449480661048783707988029274610 | -144377699742878987415091500906294635508218607563 | 1162852791112583332128749192014892465993808367626 | -384809712508691831088549393113591972035594038620 |
| 10 | 1 | 1598978421080611778607176395161036825935348694043 | 0 | 0 | 0 |
| 10 | 2 | -11515510854330694196224132370058210434850014490 | 866820817788703560509058235377405744203822918445 | -469986470826920748776062754675274472458796652228 | -144377699742878987415091500906294635508218607563 |
| 10 | 3 | -29790033400334080812223859009978799185208642672 | -469986470826920748776062754675274472458796652228 | 803400614336805408793518223175173454834751666755 | 1162852791112583332128749192014892465993808367626 |
| 11 | 0 | 11867486242191675521515398621177199597166121485 | -132317931478121703776764663428273220751293945545 | 1155947971201895275462700629998528458977935486194 | -355919023497943687040266281938149426565824369290 |
| 11 | 1 | 1587135992796785298943183775079391898408130693333 | 0 | 0 | 0 |
| 11 | 2 | -10883387856328780967230164941285911443035669261 | 853788304753136792427450801444855145666988969323 | -459847637762876902953589538685674242742137898487 | -132317931478121703776764663428273220751293945545 |
| 11 | 3 | -27705596535553195916254268869854436436658511698 | -459847637762876902953589538685674242742137898487 | 790810983514733704994995802109934473331016303770 | 1155947971201895275462700629998528458977935486194 |
| 12 | 0 | 10046160379515383534548970042631811829434576114 | -120297273382782801478045026295552876036544793491 | 1149283859291924482438792009001484429593931762052 | -326610637888680957651536968339039065940513127688 |
| 12 | 1 | 1575342464979524162289953475850101410961646108955 | 0 | 0 | 0 |
| 12 | 2 | -10197484792851597767240180793623814757554558175 | 841070132023372193702992257520082890963205496970 | -449982087852015950031460321609479407531981152090 | -120297273382782801478045026295552876036544793491 |
| 12 | 3 | -25553629803206505546887486389891664368491081655 | -449982087852015950031460321609479407531981152090 | 778503548997030911819074988529857788133954226179 | 1149283859291924482438792009001484429593931762052 |
| 13 | 0 | 8335684166791552037877432572278675625382053278 | -108297863467292587824661335056837882917406164682 | 1142857471931983624453299911727680917838601821430 | -296820978747515874272432127080166976290821776292 |
| 13 | 1 | 1563595471426690820695216681335105295104213384508 | 0 | 0 | 1 |
| 13 | 2 | -9455725798305176008773723736870577007906516407 | 828655199909932835622834631886865988921487049232 | -440378254932582271321228608414172016208361648385 | -108297863467292587824661335056837882917406164682 |
| 13 | 3 | -23331073935949856382880916676210835321854718977 | -440378254932582271321228608414172016208361648385 | 766464561950452223537735745020505819008412067694 | 1142857471931983624453299911727680917838601821430 |
| 14 | 0 | 6745661055986178699272333832711829711803358888 | -96301168726043258089024346997201725678354386418 | 1136666215992933497453737821760840508871455696899 | -266481686180185965934573947464838408105779974866 |
| 14 | 1 | 1551892688808250785313650635100000084918568680535 | 0 | 0 | 0 |
| 14 | 2 | -8655769199096606284131567224876468969849746490 | 816533156127854403220969248101593030127643862192 | -431025225850271129332843886054000926448208259667 | -96301168726043258089024346997201725678354386418 |
| 14 | 3 | -21034591446398551697354352841296330296395092503 | -431025225850271129332843886054000926448208259667 | 754680855913744804546785189321073175781245983782 | 1136666215992933497453737821760840508871455696899 |
| 15 | 0 | 5286877536005437790895768709390974551859231311 | -84287850940756084558654967468051195721257937158 | 1130707884720876961539782990707000267499700957890 | -235518941230602538994635184087121579533497151084 |
| 15 | 1 | 1540231837608882478023239942657502610476243122894 | 0 | 0 | 0 |
| 15 | 2 | -7794974869459843169306294908184969592917083297 | 804694368722662495057832477243969167008488475512 | -421912702210730908182772693402978060272355183987 | -84287850940756084558654967468051195721257937158 |
| 15 | 3 | -18660538661990842739564051468091666703784222306 | -421912702210730908182772693402978060272355183987 | 743139792603696047466021492283333691194271899914 | 1130707884720876961539782990707000267499700957890 |
| 16 | 0 | 3971482141312420578784658911570832235558850779 | -72237616450702693769767553670550352108311435241 | 1124980654493953595387813319237434393536672946556 | -203852691674887927432164932838220525656222439497 |
| 16 | 1 | 1528610683874814845733195794900847694183003221425 | 0 | 0 | -1 |
| 16 | 2 | -6870366417455570181959408479654531258737958334 | 793129904455763039446659294740707755742225300390 | -413030966171261909843895746368981662149652173908 | -72237616450702693769767553670550352108311435241 |
| 16 | 3 | -16204933991105602256268803886301684719646375777 | -413030966171261909843895746368981662149652173908 | 731829209829805329301693751086266656326100570670 | 1124980654493953595387813319237434393536672946556 |

With §147's interval polynomial rules, the full tubes satisfy

$$
\begin{aligned}
\sup_t\|M_jF(q_j(t),c_j(t))\|_\infty&<3/50000000000,\\
\sup_{t,e}\|I-M_jJ(q_j(t),c_j(t)+e)\|_\infty&<9/250,
 \qquad\|e\|_\infty\le\rho,\\
3/50000000000+(9/250)\rho&<1/10000000000<\rho.
\end{aligned}
\tag{148.3}
$$

All 31 bounds $B_h$ in §147 hold on every such tube. To specify also
the finer rational norm bounds, the following rows give exact upper
bounds $R_j,K_j,I_j$ for the residual norm, derivative norm and
image radius respectively. Their common coarse inequalities are
(148.3); no decimal approximation is needed.

| $j$ | $R_j$ | $K_j$ | $I_j$ |
| --- | --- | --- | --- |
| 1 | $1826444732390174030155102195/170141183460469231731687303715884105728$ | $4704474696022993945566213898092403715/170141183460469231731687303715884105728$ | $6665604794414811288382384331858107395/182687704666362864775460604089535377456991567872$ |
| 2 | $2023456656120062451056975227/170141183460469231731687303715884105728$ | $296319340104750388528846353941009753/10633823966279326983230456482242756608$ | $432111217650206427228335560701121881/11417981541647679048466287755595961091061972992$ |
| 3 | $4486934974606791227647182445/340282366920938463463374607431768211456$ | $2391472701403407788801220087113298619/85070591730234615865843651857942052864$ | $3595925137354330212691491313852068539/91343852333181432387730302044767688728495783936$ |
| 4 | $622458705863469664165681193/42535295865117307932921825928971026432$ | $2415117752976182637403375854440882639/85070591730234615865843651857942052864$ | $3751837645373225461743227779189514703/91343852333181432387730302044767688728495783936$ |
| 5 | $2766469242907551961273162361/170141183460469231731687303715884105728$ | $9766473668312275746906138124556307405/340282366920938463463374607431768211456$ | $15707421130151183559450583556052880333/365375409332725729550921208179070754913983135744$ |
| 6 | $1538969845050501898479342261/85070591730234615865843651857942052864$ | $9884630783922603903246056135575527121/340282366920938463463374607431768211456$ | $16494455937944697025600743278161223377/365375409332725729550921208179070754913983135744$ |
| 7 | $3429601419331406320996152099/170141183460469231731687303715884105728$ | $10015760923211466538138389436464388023/340282366920938463463374607431768211456$ | $17380773890383252705321465139987765175/365375409332725729550921208179070754913983135744$ |
| 8 | $1913875956150974342298290993/85070591730234615865843651857942052864$ | $5080389907491851550967430578287340549/170141183460469231731687303715884105728$ | $9190407227626433970320565224100523013/182687704666362864775460604089535377456991567872$ |
| 9 | $8559643253333143762080346121/340282366920938463463374607431768211456$ | $80630567404342312241418613982800469/2658455991569831745807614120560689152$ | $152434059276398748669155902096190037/2854495385411919762116571938898990272765493248$ |
| 10 | $9589216596582064172587811591/340282366920938463463374607431768211456$ | $5248354103675531751392568058343829569/170141183460469231731687303715884105728$ | $10396525563248080626572311867288170561/182687704666362864775460604089535377456991567872$ |
| 11 | $10765131891025945392792598343/340282366920938463463374607431768211456$ | $10690055633612280319694165471764666133/340282366920938463463374607431768211456$ | $22249027985883048157075686470276863765/365375409332725729550921208179070754913983135744$ |
| 12 | $3028081446886531251677846175/85070591730234615865843651857942052864$ | $10902203528530593683100411194554999459/340282366920938463463374607431768211456$ | $23907714312532606431938705643898692259/365375409332725729550921208179070754913983135744$ |
| 13 | $6830327304398208012198735215/170141183460469231731687303715884105728$ | $11134782641483752041304504983071788679/340282366920938463463374607431768211456$ | $25802798838166822228003873383566052999/365375409332725729550921208179070754913983135744$ |
| 14 | $3861502097555876653849614681/85070591730234615865843651857942052864$ | $11389632353516888714277220618322028203/340282366920938463463374607431768211456$ | $27974657575954780475171228175418500779/365375409332725729550921208179070754913983135744$ |
| 15 | $17511710508552933616269641485/340282366920938463463374607431768211456$ | $11668831887973118288387014318195185677/340282366920938463463374607431768211456$ | $30471887870786712830071295242125154317/365375409332725729550921208179070754913983135744$ |
| 16 | $1244392816287694324411304093/21267647932558653966460912964485513216$ | $11974737197516199477703884453493956703/340282366920938463463374607431768211456$ | $33353242994848132480069346582077726815/365375409332725729550921208179070754913983135744$ |

For fixed $q$, the map $v\mapsto v-M_jF(q,v)$ therefore contracts
the corresponding closed box strictly into itself. Banach gives a
unique fixed point. The derivative norm less than one makes $M_jJ$
invertible, and hence both $M_j$ and $J$ are invertible. Fixed points
are exactly $F$-zeros. Analytic IFT applies at each zero. These charts
supply hypotheses of the global theorem, rather than a separate
minimax theorem on a shorter interval.

## 149. One scaled polynomial chart down to positive zero

Put $\delta=1/16$, $u_0=(1,2/3,1/3,1/3)$. The polynomial system
(141.3) has $F(0,u_0)=0$ and

$$
 J_0=\begin{pmatrix}
0&1&0&0\\2/3&0&2&0\\4/3&0&0&0\\-16/27&0&2/3&4/3
\end{pmatrix},\qquad\det J_0=32/9,\qquad
 M_0=J_0^{-1}=\begin{pmatrix}
0&0&3/4&0\\1&0&0&0\\0&1/2&-1/4&0\\0&-1/4&11/24&3/4
\end{pmatrix}.
\tag{149.1}
$$

The complete rational degree-eight predictor $P(q)=\sum_{n=0}^8P_nq^n$
is specified in the next table, in coordinate order $(r,L,p,x)$.

| $n$ | $P_{n,r}$ | $P_{n,L}$ | $P_{n,p}$ | $P_{n,x}$ |
| --- | --- | --- | --- | --- |
| 0 | $1$ | $2/3$ | $1/3$ | $1/3$ |
| 1 | $-1/2$ | $-2/9$ | $-1/9$ | $-2/9$ |
| 2 | $25/24$ | $4/27$ | $19/108$ | $35/216$ |
| 3 | $-43/24$ | $-67/324$ | $-29/108$ | $-425/1944$ |
| 4 | $37855/10368$ | $3613/11664$ | $8341/15552$ | $9055/31104$ |
| 5 | $-234301/31104$ | $-74683/139968$ | $-74267/69984$ | $-13153/31104$ |
| 6 | $12015239/746496$ | $2439133/2519424$ | $2488915/1119744$ | $3888005/6718464$ |
| 7 | $-234469169/6718464$ | $-55654321/30233088$ | $-35634301/7558272$ | $-1538027/2239488$ |
| 8 | $49411474289/644972544$ | $96883877/26873856$ | $9837286963/967458816$ | $797386469/1934917632$ |

Exact substitution makes the coefficients of degrees zero through
eight in $F(q,P(q))$ vanish. Equivalently these coefficients can be
specified by the finite recurrence $P_0=u_0$ and
$P_n=-M_0[q^n]F(q,\sum_{k<n}P_kq^k)$ for $1\le n\le8$.
The displayed full coefficients make that recurrence unnecessary
as an external data dependency.

Use the closed scaled box

$$
 u=P(q)+q^9e,\qquad0\le q\le\delta,\qquad
 \|e\|_\infty\le R=1024,\qquad
 H(q,e)=q^{-9}F(q,P(q)+q^9e).
\tag{149.2}
$$

Here $H$ denotes its exact polynomial extension at zero. The extension
is completely specified by expanding the numerator and removing a
factor $q^9$ from every monomial. This division is exact:
$F(q,P(q))$ has zero coefficients through degree eight, and every
term of $F(q,P(q)+q^9e)-F(q,P(q))$ has a factor $q^9$.
It follows identically, including at zero, that
$D_eH=J(q,P(q)+q^9e)$. No singular division is used in any interval
calculation at zero.

Here are exact whole-box rules sufficient to reproduce every bound
in this chart. For $A(q)=\sum_n a_nq^n$ define

$$
 \mathcal A(A)=
 [a_0+\sum_{n\ge1,\ a_n<0}a_n\delta^n,
  a_0+\sum_{n\ge1,\ a_n>0}a_n\delta^n].
\tag{149.3}
$$

Use exact rational arithmetic. Let $B=[0,\delta]\times\prod_iZ_i$,
where $Z_i=\mathcal A(P_i)+[-\delta^9R,\delta^9R]$.
For definiteness, rectangular evaluation of an expanded polynomial
$h=\sum_\alpha h_\alpha q^{\alpha_0}u^\alpha$ means the sum of its
coefficient intervals times the indicated powers of these five
intervals. Each power is repeated interval multiplication, in the
variable and summation order of §147, without dyadic rounding.
Put $D_h=\sum_i|\mathcal I_B(\partial_{u_i}h)|_{\max}$.
The line integral along the segment from $P(q)$ to $P(q)+q^9e$ gives

$$
 |h(q,P(q)+q^9e)-h(q,P(q))|\le q^9R D_h.
\tag{149.4}
$$

When the exact polynomial $h(q,P(q))$ is divisible by $q^m$, $m<9$,
a whole-box enclosure for its scaled value is consequently

$$
 \frac{h(q,P(q)+q^9e)}{q^m}
 \ \in\mathcal A\big(q^{-m}h(q,P(q))\big)
 +[-\delta^{9-m}RD_h,\delta^{9-m}RD_h].
\tag{149.5}
$$

The scaled polynomial also extends at zero, since its perturbation
has a factor $q^9$. Apply (149.5) to the 30 nontrivial rows of §147
with their listed $m_h$. For $g(q,P(q))$ the coefficients of degrees
zero and one are zero and that of degree two is exactly $1/216$.
These cancellations and perturbation factors establish the strict
vanishing bounds (147.4) uniformly for all positive $q$ in the chart.

The exact rational hull $B$, in the order $(q,r,L,p,x)$, is:

| Variable | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| $q$ | $0$ | $1/16$ |
| $r$ | $1746313296265423/1803473947459584$ | $2781564773405221745/2770135983297921024$ |
| $L$ | $5297290689624143/8115632763568128$ | $231046713334996463/346266997912240128$ |
| $p$ | $662077963210115/2028908190892032$ | $1387958119446951475/4155203974946881536$ |
| $x$ | $192004238381077/601157982486528$ | $2775433442930509541/8310407949893763072$ |

For the residual, form the four exact rational polynomials
$A_i(q)=(M_0F(q,P(q)))_i/q^9$ and apply $\mathcal A$.
For the derivative, form the expanded polynomials
$K_{ik}(q,u)=(I-M_0J(q,u))_{ik}$, apply $\mathcal A$ after
substitution of $P$, and enlarge by
$[-\delta^9R D_{K_{ik}},\delta^9R D_{K_{ik}}]$.
This retains every cancellation before taking a range. The following
finite enclosures give additional coarse whole-box bounds. In these
two tables every listed interval $[l,u]$ means $[l/2^{20},u/2^{20}]$.
They are outward dyadic enclosures of exact rational bounds.

| $i$ | Residual interval $[l_i,u_i]$ |
| --- | --- |
| 0 | $[143469781,182393003]$ |
| 1 | $[6269873,7752175]$ |
| 2 | $[16108731,24522158]$ |
| 3 | $[-3566484,-859636]$ |

| row $i$ | $K_{i0}$ | $K_{i1}$ | $K_{i2}$ | $K_{i3}$ |
| --- | --- | --- | --- | --- |
| 0 | $[-2971,76850]$ | $[-359,98]$ | $[-200756,28942]$ | $[-200349,27161]$ |
| 1 | $[-1,1]$ | $[-1558,43776]$ | $[-1,1]$ | $[-1,1]$ |
| 2 | $[-2607,16087]$ | $[-5498,712]$ | $[-1129,48276]$ | $[-67055,10241]$ |
| 3 | $[-1879,22621]$ | $[-12022,1755]$ | $[-47953,5176]$ | $[-513,25826]$ |

In particular the uniform bounds, with rational strict
outer constants, are

$$
 \sup_q\|M_0H(q,0)\|_\infty<174,\qquad
 \sup_{q,e}\|I-M_0D_eH(q,e)\|_\infty<457/1000,
 \qquad174+(457/1000)1024<642<1024.
\tag{149.6}
$$

Thus $e\mapsto e-M_0H(q,e)$ is a contraction of the same closed
box strictly into itself for every $q\in[0,\delta]$. Its fixed point
is unique, its Jacobian is nonsingular, and analytic IFT and local
uniqueness give an analytic root on the chart. For $q>0$, $H=0$
is equivalent to $F=0$. The scaled system at zero is a certificate
device and supplies no optimizer classification at that endpoint.

## 150. Endpoint inclusions and completion of the positive theorem

All endpoint statements here are exact rational comparisons of the
displayed data. Write $c^*$ for the rational center in Definition
128.1. The anchor inclusions are, for each coordinate $i$,

$$
 |c_{1,i}(1)-c_i^*|+10^{-20}<2^{-30}.
\tag{150.1}
$$

Thus the entire root box of Definition 128.1, including its radius, belongs
to the first endpoint tube. The interpolation node table also gives

$$
 c_j(-1)=c_{j+1}(1),\qquad1\le j<16.
\tag{150.2}
$$

The radii of these boxes are identical, so their unique roots agree
at every shared endpoint.

At the lower joint endpoint, $\delta^9R=2^{-26}$. Put

$$
 G_i=2^{-26}-\big(|P_i(1/16)-c_{16,i}(-1)|+2^{-30}\big).
\tag{150.3}
$$

The following exact positive gaps certify containment of the entire
old endpoint box inside the new one. Every gap exceeds $10^{-8}$.

| Coordinate | $G_i$ |
| --- | --- |
| $r$ | $84897030931841799122329994464899456884058677/7191684181896040534750782140588649668971930060849152$ |
| $L$ | $299388174467480593349651798796358102391400731/21575052545688121604252346421765949006915790182547456$ |
| $p$ | $590587824558783040011326350042008480888481229/43150105091376243208504692843531898013831580365094912$ |
| $x$ | $1204479505161049966086488499063839917652378587/86300210182752486417009385687063796027663160730189824$ |

For $q=1/16>0$, an $F$-zero in the upper endpoint box is an $H$-zero
in the scaled box, and uniqueness identifies the roots. Nonsingular
analytic IFT glues the charts at the joints. Consequently they form
one branch connected to the specified $q=1/4$ root and cover every
$0<q\le1/4$; uniqueness is asserted in these chart boxes.

*Proof of Theorem 146.1.* The contractions, inclusions and analytic
IFT just described give the anchored branch and nonsingularity.
The complete 31-row table gives its admissibility and all strict
cofactor, phase and nonzero slack signs; Lemma 147.1 supplies the
entire closed population boundary. Apply the already proved
pointwise argument of Proposition 142.2 and Proposition 143.2 with
these hypotheses. The former supplies the bound for all complex
pure inputs and all mixed densities; the latter supplies the matching
lower bound for every complex CPTP map and forces exactly the closed
disk by the individual phase scores. Its exact identities preserve
the singular kernel and matching value. This proves (146.1), including
the full CPTP fiber and common composite. No new restriction on the
competing maps or input densities has entered. $\square$

The input equality conclusion of Corollary 144.1 applies pointwise
on this same interval, by its existing proof and the signs above.
Likewise the rank, covariance, nonunitality and support-face statements
of §§139–140 retain exactly their stated hypotheses. These are
consequences of the reused classification, not additional independent
parameter-range theorems.

## 151. Scope of the global positive continuation

The premises and literature correspondences remain precisely those
in §§138 and 145. In particular the unique-SDP-solution branch theorem
listed there is not used to infer uniqueness of this optimizer disk.
Banach and analytic IFT certify a contact root; the unrestricted value
and full disk still require the separate all-input and all-decoder
arguments of §§142–143. The experiment-comparison full trace tolerance
is $2L(q)$ and its half-norm parameter is $L(q)$. Ancillary decision
spaces in such comparisons add no reference system to this objective.

The theorem concerns the mathematical channel family $\Phi_q$ on
$0<q\le1/4$, conditional on the explicitly stated base premises and
the general-parameter implications proved above. Its rational data
and finite arithmetic rules are contained in this volume. It has no
private file or program as a mathematical proof dependency. The
zero endpoint is excluded, even though polynomial certificates extend
to it. The specified unitary transport keeps the original identity
target, and the result asserts no new identification with other actual
horizons. It supplies no negative-parameter theorem, physical
realization, formal-kernel verification, priority, exhaustive literature
claim or completion of a broader research program.

## 152. Applications to positive-side limits and normalization

These are direct consequences of Theorem 146.1 and the coefficients
$P_1,P_2$ in §149, under the same conditional premises.

**Positive-side optimizer cluster set.** In the Choi-matrix topology,
define the positive-side cluster set by limits of sequences
$\mathcal R_n\in\operatorname{Opt}_{q_n}$ with $q_n\downarrow0$.
It is exactly

$$
 \left\{\mathcal R_{1,z}:z\in\mathbb C,\ |z|\le1\right\},
\tag{152.1}
$$

where $\mathcal R_{1,z}$ is (139.3) evaluated at $r=1$.
Indeed (149.2) and its bounded $e$ give $r(q)\to1$.
Every sequence of optimal decoders is of the form
$\mathcal R_{r(q_n),z_n}$ with $|z_n|\le1$. The closed complex disk
is compact, so a subsequence of the $z_n$ converges to some $z$ in
that disk. The matrix coefficients in (139.3), equivalently the Choi
coefficients in (146.1), depend continuously on $(r,z)$. Thus every
decoder limit is $\mathcal R_{1,z}$. Conversely, for each fixed
$|z|\le1$ the optimal curve $q\mapsto\mathcal R_{r(q),z}$ converges
to $\mathcal R_{1,z}$. The endpoint map is CPTP by (139.4) with
$r=1$. These two inclusions prove (152.1). This is the cluster set
of the positive-parameter optimal family; it is not a classification
of all optimizers at $q=0$.

**Identity defect, state displacement and recovery gain.** For the
selected optimal family, substitution of the unnormalized identity
$I_3$ in (139.3) gives, independently of $z$,

$$
 \mathcal R_{r,z}(I_3)-I_3
 =\operatorname{diag}(0,r^2-1,1-r^2),\qquad
 d_I(q):=\tfrac12\|\mathcal R_{r(q),z}(I_3)-I_3\|_1=1-r(q)^2.
\tag{152.2}
$$

Here $0<r(q)<1$ justifies the last equality. The rows $P_1,P_2$,
together with the bounded remainder in (149.2), give

$$
 \begin{aligned}
 r(q)&=1-\tfrac12q+\tfrac{25}{24}q^2+O(q^3),\\
 \mu(q)=L(q)&=\tfrac23-\tfrac29q+\tfrac4{27}q^2+O(q^3).
 \end{aligned}
\tag{152.3}
$$

Squaring the first expansion yields
$r(q)^2=1-q+(1/4+25/12)q^2+O(q^3)
=1-q+(7/3)q^2+O(q^3)$. Consequently, as $q\downarrow0$,

$$
 \begin{aligned}
 d_I(q)&=q-\tfrac73q^2+O(q^3),\\
 G(q):=\tfrac23-\mu(q)&=\tfrac29q-\tfrac4{27}q^2+O(q^3),\\
 \frac{G(q)}{d_I(q)}&\longrightarrow\tfrac29.
 \end{aligned}
\tag{152.4}
$$

The actual maximally mixed density is $I_3/3$. Linearity and
homogeneity of the trace norm give its displacement as

$$
 \begin{aligned}
 \delta_u(q)&:=\tfrac12
 \|\mathcal R_{r(q),z}(I_3/3)-I_3/3\|_1
 =\tfrac13d_I(q)
 =\tfrac13q-\tfrac79q^2+O(q^3),\\
 \frac{G(q)}{\delta_u(q)}&\longrightarrow\tfrac23.
 \end{aligned}
\tag{152.5}
$$

Thus $d_I$ uses the unnormalized identity, whereas $\delta_u$ is a
state displacement. Both ratios concern the selected optimal decoder
family only. They assert no channel-independent tradeoff law and do
not solve the minimax problem constrained to unital decoders. The
recovery objective remains (141.1).

## 追加锚（本行以下为增补区）

## 153. The complete second-horizon complex decoder fiber

Here $\Phi=\Phi_{-1/2}$ and the objective is exactly [TR, Definition
118.1]: one common complex CPTP decoder, fixed before the unknown
qutrit density, with the identity target and half trace norm. The
input ranges over all complex pure and mixed densities. The map has
only the terminal qutrit as input. In matrix coordinates,

$$
\Phi(X)=\begin{pmatrix}
x_{00}&-x_{01}/2&0\\
-x_{10}/2&(x_{11}+3x_{22})/4&0\\
0&0&(3x_{11}+x_{22})/4
\end{pmatrix},\qquad
e(\mathcal R)=\max_{\rho\in\mathsf D_3}
\tfrac12\|\mathcal R\Phi(\rho)-\rho\|_1.
\tag{153.1}
$$

All parameters in this appendix are the coordinates of the unique
eleven-variable root of [TR, (119.4), (119.7), Lemma 120.1]. In
particular they are distinct from the positive-parameter root of
§§128–152. Put $k=\eta/a$. The reused root relations and strict
domains give

$$
ab=\eta^2,\qquad \eta=ka,\qquad b=k^2a,\qquad
0<a,b,c<1,\quad k>0,\quad L>0.
\tag{153.2}
$$

Theorem 118.2 of [TR] supplies $\min e=L$; its displayed decoder
$\mathcal R_*$ and composite $\mathcal C_*=\mathcal R_*\Phi$ are
[TR, (121.2), (121.5)]. Its all-density upper bound and unrestricted
lower bound are [TR, Proposition 122.2, Theorem 125.1]. These value
and root results are used without another isolation or upper-bound
argument.

Use output-first coordinates $|ij\rangle=|i\rangle_{\rm out}
\otimes|j\rangle_{\rm in}$, $E_{ij}=|i\rangle\langle j|$, and

$$
J_{\mathcal R}=\sum_{i,j}\mathcal R(E_{ij})\otimes E_{ij},\qquad
\operatorname{Tr}[T\mathcal R(X)]
=\operatorname{Tr}[(T\otimes X^{\mathsf T})J_{\mathcal R}].
\tag{153.3}
$$

Thus CPTP means $J\succeq0$ and
$\operatorname{Tr}_{\rm out}J=I$. The transpose in (153.3) is the
ordinary transpose, including for complex $X$.

**Theorem 153.1 (Every complex optimizer).** Let

$$
B=\big[\,|00\rangle-k|11\rangle,\ |20\rangle,\ |21\rangle,
\ |12\rangle,\ |22\rangle\,\big],
\tag{153.4}
$$

and, for $z=(z_1,z_2,z_3,z_4)\in\mathbb C^4$, set

$$
H(z)=\begin{pmatrix}
a&0&0&z_1&z_2\\
0&1-a&0&z_3&0\\
0&0&1-b&z_4&kz_1\\
\overline z_1&\overline z_3&\overline z_4&c&0\\
\overline z_2&0&k\overline z_1&0&1-c
\end{pmatrix}.
\tag{153.5}
$$

A complex CPTP map $\mathcal R$ is optimal if and only if there is a
unique $z\in\mathbb C^4$ such that

$$
J_{\mathcal R}=BH(z)B^\dagger,\qquad H(z)\succeq0.
\tag{153.6}
$$

The condition is joint and includes every singular boundary tuple.
Every optimizer has $\mathcal R\Phi=\mathcal C_*$ as linear maps on
all of $M_3(\mathbb C)$. The optimizer family has real affine
dimension eight. Its smallest containing CPTP face is the exposed
support face of dimension sixteen described in §160; the optimizer
family itself is not a CPTP face. The proof follows in §§154–160.

## 154. Individual equality in the public contact certificate

The public contacts are [TR, (123.1)–(123.5)]. They give rank-one
projectors $T_m=f_mf_m^\dagger$, unit vectors $f_m$, pure densities
$P_m$, and strictly positive weights $w_m$ summing to one. The index
$m=(r,j,\ell)$ includes both contacts $r=e,i$ and their nine phase
pairs; repeated edge pairs represent the same three physical inputs.
With $\omega=e^{2\pi i/3}$ these phases are
$U_{j\ell}=\operatorname{diag}(1,\omega^j,\omega^\ell)$.
Equations (124.2), (124.9), (124.14) and (125.6) of [TR] supply

$$
\begin{aligned}
W&=\sum_mw_mT_m\otimes\Phi(P_m)^{\mathsf T},\qquad
S=I\otimes Y-W\succeq0,\\
b_{\rm test}-\operatorname{Tr}Y&=L,\qquad
b_{\rm test}=\sum_mw_m\operatorname{Tr}(T_mP_m),\\
S&=\tau\bigl(b|00\rangle\langle00|
+\eta|00\rangle\langle11|+\eta|11\rangle\langle00|
+a|11\rangle\langle11|\bigr)\\
&\quad+s_{10}|10\rangle\langle10|
+s_{01}|01\rangle\langle01|+s_{02}|02\rangle\langle02|,
\end{aligned}
\tag{154.1}
$$

where $\tau,s_{10},s_{01},s_{02}>0$. The precise slack bounds are
[TR, (124.13)]. All unlisted entries of $S$ vanish.

**Lemma 154.1 (Saturation before averaging).** For any complex CPTP
optimizer, $SJ_{\mathcal R}=0$ and

$$
[\mathcal R\Phi(P_m)-\mathcal C_*(P_m)]f_m=0
\quad\text{for every indexed contact }m.
\tag{154.2}
$$

*Proof.* Fix the arbitrary optimizer and put
$A_m=P_m-\mathcal R\Phi(P_m)$,
$d_m=\operatorname{Tr}(T_mA_m)$. Each $A_m$ is Hermitian trace zero,
so

$$
d_m\le\tfrac12\|A_m\|_1\le L,\qquad
\sum_mw_md_m=b_{\rm test}-\operatorname{Tr}(WJ_{\mathcal R})
=L+\operatorname{Tr}(SJ_{\mathcal R})\ge L.
\tag{154.3}
$$

Strict positivity of every weight forces every $d_m=L$ and
$\operatorname{Tr}(SJ_{\mathcal R})=0$. For two PSD matrices this
trace equality implies their product is zero: the PSD matrix
$S^{1/2}JS^{1/2}$ has zero trace, whence
$J^{1/2}S^{1/2}=0$ and $SJ=0$.
Also $\lambda_{\max}(A_m)\le\|A_m\|_1/2\le L$. Therefore
$LI-A_m\succeq0$ and its zero quadratic form on $f_m$ implies
$A_mf_m=Lf_m$. The public decoder $\mathcal R_*$ saturates the same
effects by [TR, (123.3)] and their phase conjugates. Subtraction
proves (154.2). This argument has imposed no symmetry or reality
condition on $\mathcal R$. $\square$

## 155. All supported TP matrices and their observable action

The block in (154.1) has rank one because $ab=\eta^2$; its other
three positive scalar entries give $\operatorname{rank}S=4$.
The five independent columns (153.4) span $\ker S$, and

$$
B^\dagger B=\operatorname{diag}(1+k^2,1,1,1,1).
\tag{155.1}
$$

Thus a PSD matrix with $SJ=0$ is uniquely $J=BHB^\dagger$ with
$H\succeq0$. Indeed $B^+=(B^\dagger B)^{-1}B^\dagger$ gives
$H=B^+J(B^+)^\dagger$, and reconstructs $J$ on its supported
range. Conversely congruence by $B$ preserves positivity, and its
injectivity gives $\operatorname{rank}J=\operatorname{rank}H$ even
when $H$ is singular.

For a general Hermitian $H$, use zero-based indices $0,\ldots,4$.
The output partial trace is

$$
\operatorname{Tr}_{\rm out}(BHB^\dagger)=\begin{pmatrix}
H_{00}+H_{11}&H_{12}&H_{14}\\
H_{21}&k^2H_{00}+H_{22}&H_{24}-kH_{03}\\
H_{41}&H_{42}-kH_{30}&H_{33}+H_{44}
\end{pmatrix}.
\tag{155.2}
$$

In particular TP requires $H_{24}=kH_{03}$, without a conjugate
on $H_{03}$. Hermiticity supplies the conjugate equation.
All supported TP matrices therefore have exactly the form

$$
H=\begin{pmatrix}
t&U&V&z_1&z_2\\
\overline U&1-t&0&z_3&0\\
\overline V&0&1-k^2t&z_4&kz_1\\
\overline z_1&\overline z_3&\overline z_4&d&Q\\
\overline z_2&0&k\overline z_1&\overline Q&1-d
\end{pmatrix},
\tag{155.3}
$$

where $t,d$ are real and all other displayed variables are complex;
positivity is still required. Put
$q_1=(x_{11}+3x_{22})/4$, $q_2=(3x_{11}+x_{22})/4$.
Extracting the Choi entries in (153.3) gives the following composite
for every complex matrix $X$, with no Hermiticity restriction on $X$:

$$
\mathcal R\Phi(X)=\begin{pmatrix}
tx_{00}&ktx_{01}/2&Ux_{00}-Vx_{01}/2\\
ktx_{10}/2&k^2tq_1+dq_2&-kVq_1+Qq_2+kUx_{10}/2\\
\overline Ux_{00}-\overline Vx_{10}/2&
-k\overline Vq_1+\overline Qq_2+k\overline Ux_{01}/2&
(1-t)x_{00}+(1-k^2t)q_1+(1-d)q_2
\end{pmatrix}.
\tag{155.4}
$$

The four complex completion coordinates do not occur in this map.

## 156. Exact phase isolation for every optimizer

The public contact populations are $(p_e,0,1-p_e)$ and
$(p_i,x_i,1-p_i-x_i)$; all their occupied populations are positive.
At either phase-zero contact set
$B_r=LI+\mathcal C_*(P_r)-P_r$ as in [TR, (121.6), (123.1)].
The public contact lemma gives $B_r\succeq0$ of rank two, with
$T_r=\operatorname{adj}(B_r)/\operatorname{Tr}\operatorname{adj}(B_r)$.
At the edge the $11$ entry is $L+h_1>0$, whereas the singular $02$
block has nonzero offdiagonal $-\sqrt{p_e(1-p_e)}$. Its unit kernel
vector is consequently $f_e=(f_{e0},0,f_{e2})^{\mathsf T}$ with both
displayed coordinates nonzero.

At the interior let $p=p_i$, $x=x_i$, $y=1-p_i-x_i$,
$\kappa=1-\eta/2>0$, and $d_j=(B_i)_{jj}\ge0$. The public
adjugate entries [TR, (123.2)] give

$$
\begin{aligned}
(\operatorname{adj}B_i)_{01}&=\sqrt{px}(y+\kappa d_2)>0,\\
(\operatorname{adj}B_i)_{02}&=\sqrt{py}(d_1+\kappa x)>0,\\
(\operatorname{adj}B_i)_{12}&=\sqrt{xy}(d_0+\kappa p)>0.
\end{aligned}
\tag{156.1}
$$

Since this adjugate is positive rank one, every coordinate of its
unit range vector $f_i$ is nonzero. These facts concern the fixed
effects, not a reality assumption on the unknown decoder.

For $U_{0\ell}=\operatorname{diag}(1,1,\omega^\ell)$, the channel
erases the varied coherences, so $\Phi(U_{0\ell}P_rU_{0\ell}^\dagger)
=\Phi(P_r)$. Thus the difference
$D_r=\mathcal R\Phi(P_r)-\mathcal C_*(P_r)$ is common to these
three phase contacts. Lemma 154.1 annihilates each $U_{0\ell}f_r$.
The exact finite character sums are

$$
\frac13\sum_{\ell=0}^2U_{0\ell}f_r=(f_{r0},f_{r1},0)^{\mathsf T},
\qquad
\frac13\sum_{\ell=0}^2\omega^{-\ell}U_{0\ell}f_r=f_{r2}e_2.
\tag{156.2}
$$

At the edge these show that $D_e$ annihilates $e_0,e_2$. It is
Hermitian trace zero; only its $11$ entry could remain, and its trace
makes that zero too. Hence $D_e=0$. Successive entries of (155.4)
give

$$
\begin{aligned}
p_e(t-a)&=0,&p_eU&=0,\\
\frac{1-p_e}{4}[3k^2(t-a)+d-c]&=0,&
\frac{1-p_e}{4}(Q-3kV)&=0.
\end{aligned}
\tag{156.3}
$$

Therefore $t=a$, $U=0$, $d=c$, $Q=3kV$.
At the interior keep the $01$ phase zero and vary only $\ell$.
After these edge equalities, the common difference is exactly

$$
D_i=\begin{pmatrix}
0&0&-V\sqrt{p_ix_i}/2\\
0&0&2kx_iV\\
-\overline V\sqrt{p_ix_i}/2&2kx_i\overline V&0
\end{pmatrix}.
\tag{156.4}
$$

The second sum in (156.2), with $f_{i2}\ne0$, gives $D_ie_2=0$.
Since $p_i,x_i>0$, (156.4) forces $V=0$, hence $Q=0$. This proves
for every complex optimizer the eight real conditions
$t=a,d=c,U=V=Q=0$, without averaging that decoder. Substitution
in (155.4) proves on all of $M_3(\mathbb C)$ that

$$
\mathcal R\Phi(X)=\mathcal C_*(X)=\begin{pmatrix}
ax_{00}&\eta x_{01}/2&0\\
\eta x_{10}/2&bq_1+cq_2&0\\
0&0&(1-a)x_{00}+(1-b)q_1+(1-c)q_2
\end{pmatrix}.
\tag{156.5}
$$

## 157. The joint PSD domain, converse and singular boundaries

The preceding equalities turn (155.3) into exactly (153.5), proving
necessity in Theorem 153.1. Conversely, every $H(z)\succeq0$ gives
a PSD $BH(z)B^\dagger$ with partial trace $I$ by (155.2). Formula
(155.4) gives (156.5). The reused all-density value theorem then
gives $e(\mathcal R)=L$. The left inverse of $B$ makes $H$, and
hence the four coordinates $z$, unique. This proves both directions
of (153.6), including singular matrices.

An explicit scalar version keeps all PSD boundary points. Partition
$H=\begin{pmatrix}D&F\\F^\dagger&E\end{pmatrix}$ with

$$
D=\operatorname{diag}(a,1-a,1-b)>0,\quad
F=\begin{pmatrix}z_1&z_2\\z_3&0\\z_4&kz_1\end{pmatrix},\quad
E=\operatorname{diag}(c,1-c).
\tag{157.1}
$$

The invertible matrix
$T=\begin{pmatrix}I_3&-D^{-1}F\\0&I_2\end{pmatrix}$ satisfies
$T^\dagger HT=\operatorname{diag}(D,K)$, where

$$
\begin{aligned}
K&=\begin{pmatrix}A&C_0\\\overline C_0&B_0\end{pmatrix},\\
A&=c-\frac{|z_1|^2}{a}-\frac{|z_3|^2}{1-a}
       -\frac{|z_4|^2}{1-b},\\
B_0&=1-c-\frac{|z_2|^2}{a}-\frac{k^2|z_1|^2}{1-b},\\
C_0&=-\frac{\overline z_1z_2}{a}
       -\frac{k\overline z_4z_1}{1-b}.
\end{aligned}
\tag{157.2}
$$

Consequently the exact joint domain is

$$
\boxed{A\ge0,\qquad B_0\ge0,\qquad AB_0\ge|C_0|^2.}
\tag{157.3}
$$

Only the fixed positive entries of $D$ have been inverted. No
division by $A$, $B_0$, or a potentially zero determinant is involved.
Thus (157.3) includes $A=0$, $B_0=0$ and $\det K=0$ with their
necessary joint restrictions. Separate coordinate bounds cannot
replace it.

## 158. Erased action, common recovery and affine dimensions

The population transformation on $E_{11},E_{22}$ has determinant
$-1/2$, and the $01,10$ multipliers are nonzero. Therefore

$$
\begin{aligned}
\operatorname{im}\Phi
&=\operatorname{span}_{\mathbb C}\{E_{00},E_{11},E_{22},E_{01},E_{10}\},\\
\ker\Phi
&=\operatorname{span}_{\mathbb C}\{E_{02},E_{20},E_{12},E_{21}\}.
\end{aligned}
\tag{158.1}
$$

Every optimizer has the following fixed action:

$$
\begin{aligned}
\mathcal R(E_{00})&=aE_{00}+(1-a)E_{22},\\
\mathcal R(E_{11})&=bE_{11}+(1-b)E_{22},\\
\mathcal R(E_{22})&=cE_{11}+(1-c)E_{22},\\
\mathcal R(E_{01})&=-\eta E_{01},\qquad
\mathcal R(E_{10})=-\eta E_{10}.
\end{aligned}
\tag{158.2}
$$

Its entire remaining action, extracted from (153.5), is

$$
\begin{aligned}
\mathcal R(E_{02})&=z_1E_{01}+z_2E_{02}+z_3E_{21},\\
\mathcal R(E_{12})&=-kz_1E_{11}-kz_2E_{12}+z_4E_{21}+kz_1E_{22},\\
\mathcal R(E_{20})&=\mathcal R(E_{02})^\dagger,\qquad
\mathcal R(E_{21})=\mathcal R(E_{12})^\dagger.
\end{aligned}
\tag{158.3}
$$

The freedom is exactly on the erased units and remains subject to
(157.3). In particular

$$
\operatorname{Opt}_{-1/2}
=\{\mathcal R\ {\rm CPTP}:\mathcal R\Phi=\mathcal C_*\}.
\tag{158.4}
$$

The forward inclusion was proved in §156. The reverse inclusion
uses the common all-density error $L$, so the equality here is on
the whole matrix algebra, not just on the contacts.

Hermitian $5\times5$ matrices have real dimension 25. The equations
(155.2) have rank nine: three independent real diagonal conditions
and three independent complex offdiagonal conditions. The supported
TP affine hull therefore has dimension sixteen. Its point
$H_*=\operatorname{diag}(a,1-a,1-b,c,1-c)$ is positive definite,
so positivity leaves a relative open neighborhood there.
The observable parameters $t,d,U,V,Q$ in (155.4) comprise eight
real coordinates. They can all be recovered from that linear map:
its values on $E_{00}$ identify $t,U$, its $02$ entry on $E_{01}$
identifies $V$, and its $11,12$ entries on $E_{22}$ then identify
$d,Q$. The observable map thus has real rank eight, with precisely
the four complex $z$ directions as kernel. In the optimizer section
the dependence on $z$ is injective, and $H_*>0$ permits an open
neighborhood of $z=0$ in $\mathbb C^4$. Its real affine dimension
is therefore exactly eight. Also $\operatorname{rank}J
=\operatorname{rank}H\le5$ and $\operatorname{rank}J_*=5$.

## 159. Closed slices, covariance and nonunitality

If only $z_1$ is nonzero, permutation separates the blocks $(0,3)$,
$(2,4)$ and the positive scalar $1-a$. Their determinants give

$$
|z_1|^2\le\min\{ac,(1-b)(1-c)/k^2\}.
\tag{159.1}
$$

If only $z_2$ is nonzero, the only nonscalar block is $(0,4)$, so
the exact closed slice is

$$
|z_2|^2\le a(1-c).
\tag{159.2}
$$

The circle in (159.2) has a singular $2\times2$ block and gives
legal rank-four completions, illustrating the included PSD boundary.
For explicit nonzero examples the public box [TR, (119.7)] implies

$$
\frac9{10}<a<\frac{19}{20},\quad 0<b<\frac25,\quad
\frac25<c<\frac12,\quad 0<k^2=b/a<\frac49.
\tag{159.3}
$$

The tuple $(z_1,z_2,z_3,z_4)=(1/100,0,0,0)$ has strict determinant
margins

$$
ac-10^{-4}>\frac9{25}-\frac1{10000}>0,\qquad
(1-b)(1-c)-k^2 10^{-4}>\frac3{10}-\frac1{22500}>0.
\tag{159.4}
$$

It therefore has $H>0$. So does $(0,1/100,0,0)$, since
$a(1-c)-10^{-4}>9/20-1/10000>0$.

Covariance here means
$\mathcal R\operatorname{Ad}_U=\operatorname{Ad}_U\mathcal R$
for every diagonal unitary $U$ and every input matrix. The six
offdiagonal matrix units have distinct torus characters
$u_i\overline u_j$, whereas diagonals have character zero.
In (158.3), $E_{02}\mapsto E_{01}$ forces $z_1=0$,
$E_{02}\mapsto E_{21}$ forces $z_3=0$, and
$E_{12}\mapsto E_{21}$ forces $z_4=0$. Conversely, if these
coordinates vanish, every offdiagonal unit maps into its own
character space and every diagonal unit remains diagonal.
Thus the entire covariant optimizer family is exactly

$$
z_1=z_3=z_4=0,\qquad |z_2|^2\le a(1-c).
\tag{159.5}
$$

The $z_1=1/100$ example is noncovariant; the $z_2=1/100$ example
is covariant. The complex disk (159.5) is a proper subfamily of the
eight-dimensional family, not the positive-parameter disk of §139.

Finally $\Phi(I)=I$. Formula (156.5) therefore gives for every
optimizer

$$
\mathcal R(I)=\operatorname{diag}(a,b+c,3-a-b-c)\ne I,
\tag{159.6}
$$

because $a<1$. All these second-horizon optimizers are nonunital.

## 160. The exposed support face and the nonface optimizer family

On the CPTP set $\operatorname{Tr}(SJ)\ge0$, so

$$
F_S=\{J\succeq0:\operatorname{Tr}_{\rm out}J=I,
\ \operatorname{Tr}(SJ)=0\}
\tag{160.1}
$$

is an exposed face. The zero trace condition is equivalent to $SJ=0$,
so §155 describes its whole supported TP section. The dimension
calculation and $H_*>0$ in §158 give $\dim_{\mathbb R}F_S=16$.
It is the smallest CPTP face containing $J_*$, and hence containing
the optimizer set. Indeed, for any $J\in F_S$, sufficiently small
$0<\lambda<1$ makes $J_*-\lambda J\succeq0$: in supported
coordinates this is $H_*-\lambda H\succeq0$. Then

$$
J_*=\lambda J+(1-\lambda)
\frac{J_*-\lambda J}{1-\lambda}
\tag{160.2}
$$

is a convex decomposition into CPTP elements of $F_S$. Every CPTP
face containing $J_*$ must contain $J$. Since all optimizers lie in
$F_S$ and include $J_*$, this proves the assertion.

The optimizer family is convex by (153.5)–(153.6), but is not a
CPTP face. For $\epsilon=1/100$ define

$$
H_\pm=\operatorname{diag}
(a\pm\epsilon,\ 1-a\mp\epsilon,\ 1-b\mp k^2\epsilon,\ c,\ 1-c).
\tag{160.3}
$$

The weakest corresponding entries are positive by (159.3):
$a-\epsilon>89/100$, $1-a-\epsilon>1/25$,
$1-b-k^2\epsilon>134/225$, $c>2/5$, $1-c>1/2$.
Thus $J_\pm=BH_\pm B^\dagger$ are CPTP, supported, and have
midpoint $J_*$. Their recovered $00$ entries are
$(a\pm\epsilon)x_{00}$, different from (156.5), so neither is
optimal. Their optimal midpoint disproves the face property.

## 161. Source correspondence and scope of the second-horizon fiber

The exact root, value, contact effects and positive slack are the
public results [TR, §§118–125]. The passage from these premises to
the full optimizer fiber is the supported TP calculation and the
individual equality argument of §§154–160. The Choi criterion is
the one attributed to [Choi][CHOI] in §145; TP is imposed separately
by (155.2). The supporting-functional interpretation uses the same
finite-dimensional setting of [Coutts, Girard and Watrous, Theorem
3][CGW] already explained in [TR, §126]. The argument here proves
the required equality and face facts directly. These references
support the general methods, not a literature assertion of this
particular classification; priority is unclaimed.

The result concerns the original $n=2$, $s=-1/2$ all-density
half-trace-distance problem. Original terminal decoders are obtained
by $D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger}$ from [TR,
(118.3)], preserving the identity target. It does not identify this
value or fiber with the $n=3$, $q=1/4$ disk, its positive continuation,
the zero-parameter optimizer set, or another horizon. The paired
experiment-comparison convention in [TR, §126] uses full trace
tolerance $2L$; it does not add a reference, history or environment
to (153.1). No stabilized or diamond metric is substituted.
The complete joint domain and its singular boundaries have been
specified, without an extreme-point or full rank-stratum
classification or a minimal supporting-witness assertion. All
dependencies of the ordinary proof are the displayed mathematics
and the cited public source premises; no runtime computation is a
mathematical dependency. No physical or formal-kernel conclusion is
asserted.

## 追加锚（本行以下为增补区）

## 162. Budgeted tasks on the original recovered channel

Work in the ordered complex qutrit basis (127.1), with the channel
$\Phi_s$ of (127.3), for real $-1/2\le s\le1$. Explicitly, writing
$a=(1+s)/2$ and $b=(1-s)/2$,

$$
\Phi_s(X)=\begin{pmatrix}
X_{00}&sX_{01}&0\\
sX_{10}&aX_{11}+bX_{22}&0\\
0&0&bX_{11}+aX_{22}
\end{pmatrix}.
$$

Let $\mathcal C$ be all complex CPTP maps $\mathcal R:M_3\to M_3$ and
$K_s=\{\mathcal R\Phi_s:\mathcal R\in\mathcal C\}$. A decoder is fixed
before the unknown input and the task subsequently selected from its
prescribed family. Inputs range over all complex qutrit densities; the
target is the original input. The decoder receives the terminal qutrit.
The metric here is the unassisted half trace distance of (127.5).

For the actual positive finite horizon $n\ge1$, the exact correspondence is

$$
s_n=(-1/2)^{n-1},\quad
\mathcal N_n=\operatorname{Ad}_{U_0}\Phi_{s_n},\quad
\mathcal R=D\operatorname{Ad}_{U_0},\quad
D=\mathcal R\operatorname{Ad}_{U_0^\dagger}.
$$

Here $U_0=1\oplus\left(\begin{smallmatrix}-1/2&\sqrt3/2\\
\sqrt3/2&1/2\end{smallmatrix}\right)$, as in (127.2). This is a bijection
on all CPTP decoders, with $D\mathcal N_n=\mathcal R\Phi_{s_n}$ and no
target rotation. The limiting channel is $\Phi_0=\mathcal N_\infty$.
The empty horizon instead has $\mathcal N_0=\operatorname{id}$.

Fix any set $\mathcal E$ of effects $0\preceq E\preceq I_3$; the set of
all rank-one projectors is the principal example. Let
$\mathcal I=\mathcal E\times[0,\infty)$ and define

$$
e_E(\mathcal R;s)=\| (\mathcal R\Phi_s)^\dagger(E)-E\|_{\rm op},\qquad
F_{E,\epsilon}=\{\mathcal R\in\mathcal C:e_E(\mathcal R;s)\le\epsilon\}.
$$

For Hermitian $A$, $\sup_{\rho\in\mathsf D_3}|\operatorname{Tr}(A\rho)|
=\|A\|_{\rm op}$, by spectral decomposition and a maximal absolute
eigenvector. Thus this is exactly worst-density expectation error.
Both $E$ and $(\mathcal R\Phi_s)^\dagger(E)$ are effects, so
$0\le e_E\le1$. Every such error depends only on $T=\mathcal R\Phi_s$.

## 163. Compactness and the quantified incidence closures

Use the unnormalized output-first convention

$$
J(\mathcal R)=\sum_{i,j}\mathcal R(E_{ij})\otimes E_{ij},\qquad
\mathcal R(X)=\operatorname{Tr}_{\rm in}
 [J(\mathcal R)(I_{\rm out}\otimes X^{\mathsf T})].
$$

The Choi characterization gives
$\mathcal C\simeq\{J\succeq0:\operatorname{Tr}_{\rm out}J=I_3\}$
[FC-W, Theorems 2.22 and 2.26]. This set is nonempty, convex and closed,
and every member has trace three; positivity therefore bounds it.
Consequently $\mathcal C$ and its continuous linear image $K_s$ are
compact convex sets. Each error above is continuous and convex in either
decoder or recovered-channel coordinates, so each budget set is closed
and convex, including for an infinite, noncompact task language.

For arbitrary $\Gamma\subseteq\mathcal I$ and $D\subseteq\mathcal C$, set

$$
\alpha(\Gamma)=\bigcap_{t\in\Gamma}F_t,\qquad
\beta(D)=\{t\in\mathcal I:D\subseteq F_t\}.
$$

**Theorem 163.1 (Exact incidence correspondence).** For every such pair,

$$
\Gamma\subseteq\beta(D)\iff D\subseteq\alpha(\Gamma).
$$

Both maps reverse inclusion. The maps $\beta\alpha$ on task families
and $\alpha\beta$ on decoder families are extensive, monotone and
idempotent. In particular
$\alpha\beta\alpha=\alpha$ and $\beta\alpha\beta=\beta$.

*Proof.* Both sides of the equivalence state
$\forall t\in\Gamma\ \forall\mathcal R\in D:\mathcal R\in F_t$.
The definitions give antitonicity and
$\Gamma\subseteq\beta\alpha\Gamma$, $D\subseteq\alpha\beta D$.
Applying antitonicity to these inclusions, and extensiveness to their
images, gives both triple identities. They imply idempotence;
composition of two inclusion reversals gives monotonicity. $\square$

For every $E$, compactness gives
$m_E(s)=\min_{\mathcal R\in\mathcal C}e_E(\mathcal R;s)$.
For every $\Lambda\subseteq\mathcal E$, one decoder attains all individual
minima exactly when
$\alpha(\{(E,m_E(s)):E\in\Lambda\})\ne\varnothing$.
The minima need not be zero. The established individual optima and common
attainer obstruction in [FC-TR, §§103–104] remain separate results.

This is a polarity between budgeted tasks and legal decoders. It does not
identify deterministic state partitions with the convex decoder set.
The arbitrary-set static extension in [FC-TP, §10] removes a finite-state
restriction from its own deterministic setting; it does not supply this
quantitative channel geometry. Distinct decoders may have the same $T$,
and all present losses identify those invisible decoder directions.

## 164. Attained budget slack and individual-optimum regret

Empty intersections have their usual conventions:
$\alpha(\varnothing)=\mathcal C$ and $\beta(\varnothing)=\mathcal I$.
If $\alpha(\Gamma)=\varnothing$, its ordinary closure is
$\beta\alpha(\Gamma)=\mathcal I$ by vacuous inclusion.
To measure the incompatibility define, with $\sup\varnothing=0$,

$$
\delta_s(\Gamma)=\min_{\mathcal R\in\mathcal C}
 \sup_{(E,\epsilon)\in\Gamma}(e_E(\mathcal R;s)-\epsilon)_+.
$$

**Theorem 164.1 (Uniform relaxation).** The displayed minimum is attained,
and $\delta_s(\Gamma)=0$ if and only if $\alpha(\Gamma)\ne\varnothing$.
More generally, for every $\eta\ge0$, there is one decoder satisfying
$e_E\le\epsilon+\eta$ for every $(E,\epsilon)\in\Gamma$ if and only if
$\delta_s(\Gamma)\le\eta$. Thus every infeasible family has strictly
positive attained slack. At budgets $\epsilon=m_E(s)$ this is the
least worst excess above individual optima.

*Proof.* Each positive-part loss is continuous and lies in $[0,1]$.
Its arbitrary supremum is finite and lower semicontinuous, so it attains
a minimum on the nonempty compact set $\mathcal C$. At an attaining
decoder the supremum is at most $\eta$ exactly when every original error
is at most its budget plus $\eta$. This proves all equivalences, including
the empty family. For individual-minimum budgets each difference is
already nonnegative. $\square$

## 165. The exact affine dimension of the recovered-channel carrier

**Theorem 165.1.** Writing $r_s=\operatorname{rank}_{\mathbb R}
(\Phi_s|_{\operatorname{Herm}(3)})$, one has

$$
\dim_{\mathbb R}\operatorname{aff}K_s=8r_s
=\begin{cases}40&s\ne0,\\16&s=0.\end{cases}
$$

*Proof.* Let $V=\operatorname{Herm}(3)$ and
$W=\{Y\in V:\operatorname{Tr}Y=0\}$, of real dimensions nine and eight.
Differences of trace-preserving Hermiticity-preserving maps form precisely
$\operatorname{Hom}_{\mathbb R}(V,W)$. Every real-linear map on Hermitian
matrices has a unique complex-linear Hermiticity-preserving extension.
The completely depolarizing decoder has $J=I_9/3\succ0$; small perturbations
in every trace-preserving Hermitian Choi direction remain positive.
Hence $\mathcal C$ has a relative open neighborhood in the full
trace-preserving affine space, whose tangent dimension is $9\cdot8$.

Composition sends $L$ to $L\Phi_s$. Restriction onto
$\operatorname{Hom}_{\mathbb R}(\operatorname{im}\Phi_s,W)$ is surjective:
extend any linear map from $\operatorname{im}\Phi_s$ to a basis of $V$.
The image tangent space has dimension $8r_s$. A surjective linear map
between finite-dimensional spaces sends a neighborhood onto a
neighborhood in its image, so the CPTP restriction has this exact affine
dimension, rather than merely this upper bound.

On diagonal Hermitian matrices, the directions $E_{00}$, $E_{11}+E_{22}$,
$E_{11}-E_{22}$ have multipliers $1,1,s$. The two real $01$ coherence
directions have multiplier $s$; the four $02,12$ directions are killed.
Thus $r_s=5$ for every nonzero $s$ and $r_0=2$. In particular the boundary
$s=-1/2$ retains rank five. $\square$

All actual finite $n\ge1$ therefore have dimension 40, while the actual
limit has dimension 16. For the separate empty-horizon identity carrier,
the same tangent argument gives dimension 72. With nonnegative effect
budgets, its identity decoder satisfies every task, so an empty-horizon
infeasibility witness does not arise.

## 166. Finite witnesses for arbitrary budgeted task families

We use the following elementary finite-dimensional intersection fact.
For a finite family of convex sets in a real affine space of dimension
$d$, an empty intersection has an empty subfamily of at most $d+1$ sets.
Indeed, take an inclusion-minimal empty family $A_1,\ldots,A_m$ and choose
$x_i\in\bigcap_{j\ne i}A_j$. If $m\ge d+2$, any $d+2$ of these points
have an affine dependence $\sum_i c_ix_i=0$, $\sum_i c_i=0$, with some
positive and some negative coefficients. Normalize their two signs to
obtain a point in both corresponding convex hulls. For each $A_j$, use
the hull whose selected indices omit $j$; every point in that hull belongs
to $A_j$. If $j$ was not selected, either hull works. This gives a point
in every $A_j$, a contradiction. Zero coefficients may be discarded.

**Theorem 166.1 (All-small-subfamilies criterion).** Put
$d_s=\dim\operatorname{aff}K_s$. For every $\Gamma\subseteq\mathcal I$,

$$
\alpha(\Gamma)\ne\varnothing
\iff \forall\Gamma_0\subseteq\Gamma,\quad
 |\Gamma_0|\le d_s+1\Longrightarrow\alpha(\Gamma_0)\ne\varnothing.
$$

*Proof.* View every budget set inside $K_s$, intersecting it with this
carrier. It is closed and convex there. If the full intersection is empty,
compactness of $K_s$ supplies a finite empty subfamily by the finite
intersection property. The preceding finite argument reduces it to at
most $d_s+1$ sets. The reverse implication is immediate. Nonemptiness in
$K_s$ is equivalent to a legal decoder realizing its point. $\square$

Thus 41 tasks suffice to witness any infeasibility at every actual finite
$n\ge1$, and 17 suffice at the limit. These are sufficient upper bounds;
no sharpness or minimal cardinality is asserted. Feasibility of just one
small subfamily does not establish feasibility of the entire family.

## 167. An exact finite certificate for the full density-input value

Let $\mathcal P_3=\{P\in\mathsf D_3:P^2=P\}$ be the compact pure-state
set and write

$$
f_P(T)=\tfrac12\|T(P)-P\|_1,\qquad
\mu(s)=\min_{T\in K_s}\max_{\rho\in\mathsf D_3}
 \tfrac12\|T(\rho)-\rho\|_1.
$$

**Theorem 167.1 (Exact finite pure-input value).** There exist
$1\le k\le d_s+1$ pure inputs $P_1,\ldots,P_k$ such that

$$
\min_{T\in K_s}\max_{1\le i\le k} f_{P_i}(T)=\mu(s).
$$

Both the full and finite minima are attained. In particular 41 inputs
suffice at any actual finite positive horizon and 17 at the limit.

*Proof.* For fixed $T$, the loss is convex in the density input. A spectral
decomposition bounds any mixed-state loss by the largest loss among its
pure components. Hence the full maximum equals $\max_{P\in\mathcal P_3}
f_P(T)$. Joint continuity and compactness give this maximum and a full
minimizer $T_*\in K_s$. Denote its value by $\mu$.

If $\mu=0$, any one pure input has finite minimum zero, using $T_*$ and
nonnegativity. If $\mu>0$, choose $0\le a_j<\mu$ with $a_j\uparrow\mu$.
For each $j$, the closed convex sets
$\{T\in K_s:f_P(T)\le a_j\}$, indexed by pure $P$, have empty total
intersection. The compact-carrier intersection argument of §166 supplies
at most $d_s+1$ pure inputs whose finite minimum $v_j$ exceeds $a_j$.
The strict inequality uses attainment of the continuous finite maximum
on compact $K_s$. Evaluation at $T_*$ gives $v_j\le\mu$.

Pad the input tuples with repetitions to length $d_s+1$. Compactness of
$\mathcal P_3^{d_s+1}$ supplies a convergent subsequence. Joint continuity
on $K_s\times\mathcal P_3$ is uniform, so convergence of the tuple makes
its finite maximum converge uniformly on $K_s$. Minima differ by at most
this uniform difference. Passing to the limit gives a tuple with finite
minimum $\mu$, since $a_j<v_j\le\mu$. Repetitions may be removed, and
$T_*$ attains the finite value as well. $\square$

This supplies existence of an exact supporting input family for the
unrestricted problem. It specifies neither an input list nor a procedure
for obtaining one. It does not evaluate $\mu(s)$ or interchange a minimax.
For the separate identity horizon, $\mu_0=0$ and one arbitrary pure input
already suffices.

## 168. Symmetry, restricted representatives and full orbit expansion

Let $\omega=e^{2\pi i/3}$ and
$G=\{U_{pq}=\operatorname{diag}(1,\omega^p,\omega^q):p,q\in\mathbb Z_3\}$.
The channel $\Phi_s$ commutes with each $\operatorname{Ad}_{U_{pq}}$ and
is real in the specified basis. Write $c(X)=\overline X$.
The decoder actions
$\mathcal R\mapsto\operatorname{Ad}_{U^\dagger}\mathcal R
\operatorname{Ad}_U$ and $\mathcal R\mapsto c\mathcal Rc$ generate a
finite group $H$ of 18 real-linear actions. The latter preserves CPTP:
conjugating every Kraus operator gives a Kraus list for $c\mathcal Rc$.
It does not use $c$ alone as a legal decoder.

Let $\mathsf P_H\mathcal R$ denote the average of these decoder actions.
Covariance, conjugation invariance of trace norm and convexity imply

$$
f_P((\mathsf P_H\mathcal R)\Phi_s)
 \le |H|^{-1}\sum_{h\in H}f_{hP}(\mathcal R\Phi_s)
 \le\max_{h\in H}f_{hP}(\mathcal R\Phi_s),
$$

where $hP$ is the corresponding unitary or antiunitary action on a pure
state; inverse conventions give the same full orbit. Maximizing over
all pure inputs shows that an $H$-fixed full minimizer exists. Thus
restriction to $K_s^H=\{(\mathsf P_H\mathcal R)\Phi_s:\mathcal R\in\mathcal C\}$
preserves the full value.

For $s\ne0$ this fixed carrier has exact real affine dimension seven.
To check it, give the basis vectors phase weights $(0,0),(1,0),(0,1)$.
Their six ordered nonzero differences in $\mathbb Z_3^2$ are distinct.
Character orthogonality therefore leaves a phase-fixed decoder with
$\mathcal R(E_{jj})=\sum_i C_{ij}E_{ii}$ and
$\mathcal R(E_{ij})=\lambda_{ij}E_{ij}$ for $i\ne j$.
Hermiticity gives conjugate multipliers and trace preservation gives
three population column sums one: six real population parameters.
Precomposition by $\Phi_s$ retains all six, since its population block
has determinant $s$, and retains only the $01$ coherence multiplier.
Phase averaging alone leaves two real coordinates of that multiplier;
$c\mathcal Rc$ fixes it to be real, leaving one. These seven tangent
directions are independent. The fixed depolarizing decoder has strictly
positive Choi matrix, so small fixed TP perturbations in all seven
directions remain CPTP. This proves equality of affine dimension.

Theorem 167.1 on this carrier gives at most eight representative pure
inputs $S$ for the restricted optimization. For arbitrary untwirled
$\mathcal R$, the preceding averaging inequality gives

$$
\max_{Q\in H S} f_Q(\mathcal R\Phi_s)
 \ge\max_{P\in S}f_P((\mathsf P_H\mathcal R)\Phi_s)\ge\mu(s).
$$

A fixed full minimizer gives the opposite finite-minimax inequality.
Hence the full physical orbit $HS$ is an exact unrestricted certificate,
with at most $18\cdot8=144$ states before repetitions are removed.
The generic unrestricted bound 41 is smaller than this orbit upper
bound. Eight representatives by themselves certify only the restricted
problem. The seven-dimensional assertion applies only to $s\ne0$;
at zero the unconditional unrestricted bound remains 17.

For a prescribed effect-task family, averaging requires its own invariance
check, including transport of budgets. Closure under $E\mapsto hE$ with
unchanged budget is sufficient: the transported inequalities and convexity
then preserve feasibility and the worst budget slack. Literal orbit
closure is not necessary in every redundant or accidentally invariant
instance. No such invariance is assumed for an arbitrary $\Gamma$.

For example, at $s=1$ let $X$ swap $|0\rangle,|1\rangle$ and fix $|2\rangle$,
and take $\mathcal R=\operatorname{Ad}_X$. The input
$P=|+\rangle\langle+|$, $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$, has zero
state and effect error. For $U=\operatorname{diag}(1,\omega,1)$,
$UPU^\dagger$ is still in the preserved $01$ block, but its overlap with
its swapped vector has modulus $1/2$. Its trace-distance error is therefore
$\sqrt{1-1/4}=\sqrt3/2$; the difference of the two rank-one projectors has
eigenvalues $0,\pm\sqrt3/2$, giving the same effect error. A representative
can consequently miss an orbit failure of an unrestricted decoder.

## 169. Source correspondence and the remaining scope

The incidence polarity and finite convex-intersection argument are mature
general tools, proved explicitly above in the forms used here. Compactness
adds the infinite-family passage; compactness of pure inputs adds exact
finite value attainment. The channel-specific contributions are their
parameter correspondence, the recovered affine dimensions 40 and 16,
and the justified fixed-family and orbit bounds. The proofs use no
historical original-text attribution for Helly or Carathéodory.

[FC-W, (2.65)–(2.66), Theorems 2.22 and 2.26] supplies the unnormalized
output-first Choi, complete-positivity and trace-preservation interfaces:
its input and output spaces are both $\mathbb C^3$ here. Trace preservation
ensures its nonzero-map hypothesis where required. The compact-carrier
proof avoids any additional constrained-subgradient supplier.

The common-map experiment comparisons already stated in §138 have source
states $\Phi_s(\rho)$, target states $\rho$, and reconstruction map
$\mathcal R$. A half-trace threshold $a$ corresponds to the full trace
threshold $2a$ there. Their auxiliary comparison tests do not change the
input or decoder permissions specified in §162. The present proofs do not
depend on any further experiment-comparison theorem.

Existing exact results include [FC-TR, §§107, 115–118] at the stated
endpoints and second horizon, §§153–161 for its full optimizer classification,
and §§128, 139–152 for the third horizon and positive interval $0<s\le1/4$.
The latter retains Theorem 146.1's explicit base premises and gives its
anchored exact value and optimizer disk. The finite-certificate theorems
apply throughout their stated domains, independently of whether a value
has been evaluated. They do not turn those published evaluations into
unknown problems or supply a general negative-parameter evaluation.
They assert no sharp certificate cardinality, explicit optimal input list,
or classification beyond the existing parameter-specific results.

[FC-W]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf "John Watrous, The Theory of Quantum Information, Chapter 2, equations (2.65)–(2.66), Theorems 2.22 and 2.26"
[FC-TR]: AURIC_FIB_ACTUAL_ERASED_HISTORY_TERMINAL_RECOVERY.md "Actual erased-history terminal recovery, original channel and no-reference objective"
[FC-TP]: FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md "Task–partition Galois correspondence, arbitrary-set extension in Section 10"

## 追加锚（本行以下为增补区）
