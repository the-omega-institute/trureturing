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
