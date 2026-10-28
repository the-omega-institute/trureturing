# FIB strict-real joint incidence: the full seven-world inverse

## 1. Original worlds and the fixed terminal fibre

**Definition 1.1 (Inherited model and response coordinates).** Use the
complete worlds of [O, Definitions 1.1–1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md):

$$
\begin{gathered}
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\\
b>0,\qquad 0<r<1,\qquad
0\ne g\in\mathbb R[s],\qquad \deg g\le3,\qquad d\in\mathbb R,\\
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\\
Q_0=I,\qquad Q_i=E_iQ_{i-1},\qquad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\end{gathered}
\tag{1.1}
$$

The fixed history, entire acquired child, and terminal functions are

$$
\begin{gathered}
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\qquad p\ne24,\\
j=b+\frac{r(1-r)}b,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b,\\
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7).
\end{gathered}
\tag{1.2}
$$

The acquired word through clock six is $J,M,J,M,M,M$. Its traces,
followed by the terminal $M$ trace, are exactly

$$
(1,j,T,n,U,U+n,2U+n,3U+2n).
\tag{1.3}
$$

The terminal $J$ trace is $T+2j+4r$. These are the original left-product
traces of O, (1.6)–(1.7). Every clock $0,\ldots,7$ uses the same source,
one whole polynomial $g$, and one fixed drift $d$. The terminal actions
are alternatives at the same clock. For real $p\ne24,v,m$ define

$$
\mathcal W(p,v,m)=\{W\in C(p,v):m(W)=m\}.
\tag{1.4}
$$

Cardinality counts distinct complete triples. No sign of $g$, exact gain
degree, simplicity of its roots, nonzero drift, source separation, or
upper bound on the positive off-diagonal entries is imposed.

**Assumption 1.2 (Owning interfaces and parameter correspondence).** The
symbols O and F refer respectively to the common-parent volume and
[the all-response finite-fibre volume](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md).
The symbols S, SII, SIII, SIV, SV refer to the
[first support volume](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md) and
its [second](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md),
[third](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
[fourth](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md), and
[fifth](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md) volumes.
The following are the reused mathematical interfaces.

| Source | Exact correspondence and scope |
| --- | --- |
| O, Theorem 2.1 | The full-parent converse with all original rows; the variables are the identical $r,b,d,g$, with $\epsilon=d-24$ and $\beta=1/8$. |
| O, Theorem 2.2; F, Lemma 30.2 | On $p\ne24$, one has $d\ne24$; the faithful coordinates are $(x,d)$ with $x=n/U$ and whole interpolant $H=Ug$. |
| O, Lemma 12.2 and Theorem 12.3 | At a fixed strict source and fixed $p$, the whole gain and drift are unique, including the singular-parent stratum. |
| F, Sections 30–33 | The same entire $C(p,v)$ and terminal alternatives; Theorem 32.1 bounds $|C(p,v)|$ by $24$ before fixing $m$. |
| S, Definition 1.2; SIII, Definition 19.1 | Independent distinct equal-$J$ and equal-$M$ pairs in one entire child, allowing cross-pair overlap and independent common terminal values. |
| SII, Definition 25.1 | The full response tuple is exactly $\Psi_M=(p,v,m)$ on the same whole world. |
| SIV, Theorem 8.2; SV, (2.1)–(2.2) | Undivided original response identities; singular sources and every gain stratum remain admissible. |

Only the original-world and uniqueness interfaces in this table are
needed for the inverse below. The regional conclusions of SIV and SV
are not hypotheses on $(p,v)$. SIII, Theorem 17.3 fixes $(p,r/b)$;
that four-world bound has different fixed data from (1.4).

The consequence $d\ne24$ is used only with its stated off-$24$
hypothesis. In particular it removes neither $d=0$ nor any singular
source. In the notation of O the singular coefficient is

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n;
\tag{1.5}
$$

no condition $\Lambda\ne0$ is imposed here.

## 2. Fixed-node interpolation and the drift equation

**Definition 2.1 (Tail coordinates and exact circuits).** Put

$$
x=\frac nU>0,\qquad u=\frac1U\in(0,1),\qquad h(s)=Ug(s).
\tag{2.1}
$$

For arbitrary real $d$ and $x>0$, with $p,v,m$ fixed, define

$$
h_4=18-d,\qquad h_5=\frac{p-d}{x+1},\qquad
h_6=\frac{v-d}{x+2},\qquad h_7=\frac{m-d}{2x+3},
\tag{2.2}
$$

and let

$$
\ell_i(s)=\prod_{\substack{4\le k\le7\\k\ne i}}\frac{s-k}{i-k},
\qquad h(s)=\sum_{i=4}^7h_i\ell_i(s),\qquad H_i=h(i).
\tag{2.3}
$$

Thus $H_i=h_i$ for $i=4,5,6,7$. The four earlier values are

$$
\begin{aligned}
H_0&=35h_4-84h_5+70h_6-20h_7,\\
H_1&=20h_4-45h_5+36h_6-10h_7,\\
H_2&=10h_4-20h_5+15h_6-4h_7,\\
H_3&=4h_4-6h_5+4h_6-h_7.
\end{aligned}
\tag{2.4}
$$

Define the polynomials

$$
\begin{aligned}
\Delta&=(x+1)(x+2)(2x+3),\\
K&=8x^4+29x^3+18x^2-15x-6,\\
N&=(72x-24)\Delta-6px(x+2)(2x+3)\\
&\hspace{18mm}+4vx(x+1)(2x+3)-mx(x+1)(x+2).
\end{aligned}
\tag{2.5}
$$

Here $K$ is a univariate quartic, unrelated to any rectangular base region
or fixed-width family denoted $K$ in a supplier. The symbol $\Delta$ in
this volume is the positive tail denominator (2.5), not $b-1/8$.

**Proposition 2.2 (Exact fixed-terminal drift identity).** On $x>0$,

$$
xH_3+d-24=\frac{N-Kd}{\Delta}.
\tag{2.6}
$$

Consequently every $W\in\mathcal W(p,v,m)$ satisfies $K(x)d=N(x)$.
Conversely (2.6) makes this equation sufficient for the clock-three row
of the tail interpolant.

Proof. Substitute (2.2) in the last row of (2.4), multiply by
$\Delta$, and collect the constant and $d$ coefficients. They are
$N$ and $-K$, respectively. By (1.3), clock three is exactly
$d+xh(3)=24$. The other tail traces divided by $U$ are
$1,x+1,x+2,2x+3$, giving precisely (2.2). The polynomial in (2.3)
is the whole $Ug$ by distinct-node interpolation, including degree
drops and vanishing samples. The interpolation fact is the classical
formula of Berrut–Trefethen, *Barycentric Lagrange Interpolation*,
SIAM Review 46 (2004), §2,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715),
already used by O and F. Its use here is at the fixed nodes $4,5,6,7$. ∎

## 3. The ordinary inverse

**Definition 3.1 (Polynomial numerators and strict ordinary roots).** All
the following polynomials have coefficients in $\mathbb Q[p,v,m]$:

$$
\begin{gathered}
f_4=18K-N,\qquad f_5=\frac{pK-N}{x+1},\qquad
f_6=\frac{vK-N}{x+2},\qquad f_7=\frac{mK-N}{2x+3},\\
Z_0=35f_4-84f_5+70f_6-20f_7,\\
Z_1=20f_4-45f_5+36f_6-10f_7,\\
Z_2=10f_4-20f_5+15f_6-4f_7,\\
Z_3=4f_4-6f_5+4f_6-f_7,\\
B_*=5Z_2+10N-294K,\qquad D_*=5(Z_0^2+Z_2^2),\\
W_*=-5NZ_0-Z_2B_*,\qquad L=24K-N,\qquad Z=xZ_1-L,\\
F=Z_0B_*-5NZ_2,\\
G=(D_*-W_*)\bigl(2LZ_1D_*-(D_*-W_*)Z_1^2\bigr)
 -4ZD_*(W_*Z_1-ZD_*).
\end{gathered}
\tag{3.1}
$$

The displayed quotients defining $f_5,f_6,f_7$ are exact polynomial
quotients, not rational functions with additional exceptional domains.
The starred symbols are particular polynomials of this volume; $D_*$
is not a regular-source denominator from another chart.

Let $\mathcal R(p,v,m)$ be the set of real $x$ satisfying

$$
\begin{gathered}
F(x)=G(x)=0,\qquad x>0,\qquad K(x)\ne0,\qquad D_*(x)>0,\\
0<W_*(x)<D_*(x),\qquad Z(x)Z_1(x)>0,\\
\bigl(W_*(x)Z_1(x)-Z(x)D_*(x)\bigr)Z_1(x)>0.
\end{gathered}
\tag{3.2}
$$

**Proposition 3.2 (Polynomiality and degree bounds).** Each $f_i$ and
$Z_i$ has $x$-degree at most three. One has

$$
\deg_xF\le7,\qquad \deg_xG\le20,\qquad
xZ_3+N-24K=0.
\tag{3.3}
$$

Proof. The leading term of $N$ is $144x^4$, so $18K-N$ has degree
at most three. At the three tail denominator roots,

$$
\begin{gathered}
K(-1)=6,\qquad K(-2)=-8,\qquad K(-3/2)=-3/8,\\
N(-1)=6p,\qquad N(-2)=-8v,\qquad N(-3/2)=-3m/8.
\end{gathered}
\tag{3.4}
$$

The factor theorem gives each exact quotient and its degree bound.
Thus $\deg B_*\le4$, $\deg D_*\le6$, $\deg W_*\le7$,
and $\deg L,\deg Z\le4$. Substitution in (3.1) gives the stated
bounds. Substitution of the last row defining $Z_3$ gives the last
identity in (3.3); equivalently it is (2.6) after $d=N/K$ and
$H_3=Z_3/K$. Both sides are polynomials, so this identity also holds
at $K=0$. ∎

**Theorem 3.3 (Ordinary complete-world equivalence).** For any real
$p\ne24,v,m$, the ordinary worlds in $\mathcal W(p,v,m)$, namely
those with $K(x)\ne0$, are in bijection with $\mathcal R(p,v,m)$.
The inverse is

$$
\begin{gathered}
d=\frac NK,\qquad u=\frac{W_*}{D_*},\qquad
b=\frac{1-u}{2u},\qquad
r=\frac{Z}{uZ_1},\\
n=\frac xu,\qquad j=\frac{L}{uZ_1},\qquad
g(s)=\frac uK\sum_{i=4}^7f_i\ell_i(s),\qquad W=(P(r,b),g,d).
\end{gathered}
\tag{3.5}
$$

Proof. Fix an ordinary actual world. By (2.6), $d=N/K$, and hence
$h_i=f_i/K$ and $H_i=Z_i/K$. Clocks zero and two are

$$
uH_0+d=0,\qquad uH_2+H_2+2d-294/5=0.
\tag{3.6}
$$

The pair $(H_0,H_2)$ cannot vanish: (3.6) would force both $d=0$
and $2d=294/5$. Define

$$
S_0=H_0^2+H_2^2>0,\qquad C_0=H_2+2d-294/5,\qquad
\Phi=H_0C_0-dH_2.
\tag{3.7}
$$

The compatibility equation of (3.6) is $\Phi=0$. The exact identities

$$
\begin{gathered}
5K^2\Phi=F,\qquad
u=-\frac{dH_0+H_2C_0}{S_0}=\frac{W_*}{D_*},\\
uH_0+d=-\frac{H_2\Phi}{S_0},\qquad
uH_2+C_0=\frac{H_0\Phi}{S_0}
\end{gathered}
\tag{3.8}
$$

show both necessity and sufficiency, including when either $H_0$ or
$H_2$ alone is zero. The clock-one row and $d\ne24$ give

$$
H_1\ne0,\qquad
j=\frac{24-d}{uH_1}=\frac{L}{uZ_1},\qquad
r=n-j=\frac{Z}{uZ_1}.
\tag{3.9}
$$

The positive sum of squares gives $D_*>0$. The inequalities
$0<u<1$ are exactly $0<W_*<D_*$. Since $u>0$ and $D_*>0$,
the two strict source inequalities $r>0$ and $1-r>0$ are exactly
the last two guards in (3.2). In particular these guards imply
$Z_1\ne0$. The source identity is

$$
bj=b^2+r(1-r).
\tag{3.10}
$$

Upon making the substitutions (3.5), its precise cleared form is

$$
4W_*^2Z_1^2\bigl(bj-b^2-r(1-r)\bigr)=G.
\tag{3.11}
$$

All its clearing factors are nonzero under (3.2). This proves that
every ordinary actual world yields a root of (3.2).

Conversely take such a root. Form (3.5) and the whole polynomial
$h=g/u$. The guards give $b>0$ and $0<r<1$. Equations (3.10)–(3.11)
then give $j=b+r(1-r)/b>0$, while the definitions give
$n=j+r=x/u$. Thus $U=1/u=1+2b$ and $T=(1+u)/(2u)$ are exactly
the source coordinates of O. Equations (3.8) supply clocks zero and
two. Equation (3.9) supplies clock one, and (3.3) supplies clock three.
The four samples $h_i=f_i/K$ supply clocks four through seven with
readings $18,p,v,m$, using the trace factors in (1.3).

This also identifies $h$ with the interpolant of F, (30.4)–(30.6):
both are the degree-at-most-three polynomial with the same samples
at $3,4,5,6$. In F, Lemma 30.2, the parameter substitution is
$H=h$, $U=1/u$, and
$B_0=294/5-2d-H_2$; (3.6) reads $dU=-H_0$, $B_0U=H_2$.
Thus the reused whole-world interface is precisely the original one.
The first two readings differ, so $g$ is not the zero polynomial.
Each root determines its entire $g$, drift, and source uniquely.
Different roots have different $x=n/U$, so give different worlds.
This proves the claimed bijection. ∎

## 4. The exceptional positive coordinate

**Proposition 4.1 (The quartic root and exact coprimality data).** The
quartic $K$ has exactly one positive root $\kappa$, with

$$
\frac58<\kappa<\frac23.
\tag{4.1}
$$

All complex roots of $K$ are simple. Define

$$
\begin{aligned}
M_0&=70x^3+267x^2+157x-124,\\
M_2&=20x^3+76x^2+53x-23,\\
\mathscr H&=M_0(M_2-2\Delta)+M_2\Delta\\
&=1160x^6+8664x^5+20938x^4+13420x^3
 -11360x^2-8824x+4202.
\end{aligned}
\tag{4.2}
$$

Then $\gcd_{\mathbb Q[x]}(K,K')=\gcd_{\mathbb Q[x]}(K,\mathscr H)=1$.
In particular $\Delta(\kappa)\mathscr H(\kappa)\ne0$.

Proof. The descending nonzero coefficient signs of $K$ are
$+,+,+,-,-$, with one change. Descartes' rule bounds the number
of positive roots counted with multiplicity by one. The exact values

$$
K(5/8)=-11/256,\qquad K(2/3)=176/81
\tag{4.3}
$$

give a positive root by continuity, and hence the unique positive
simple root in (4.1). This real sign argument is independent of the
following finite-field certificates.

In $\mathbb F_5[x]$, the monic reduction of $K$ and the reduction
of $\mathscr H$ are

$$
k=x^4+3x^3+x^2+3,\qquad
\overline{\mathscr H}=4x^5+3x^4+x+2.
\tag{4.4}
$$

The following are the complete nonzero monic Euclidean remainder
lists. At each step the new nonzero remainder is divided by its
leading coefficient.

| Initial ordered pair in $\mathbb F_5[x]$ | Successive monic remainders |
| --- | --- |
| $k,\ (k')/4=x^3+x^2+3x$ | $x^2+4x+3,\ x+2,\ 1$ |
| $\overline{\mathscr H},\ k$ | $x^3+3x^2+3x+3,\ x^2+4x+1,\ x+4,\ 1$ |

Each next remainder after $1$ is zero. Thus the respective reduced
polynomials are coprime. To infer rational coprimality, suppose a
nonconstant primitive integer polynomial $q$ divided $K$ and one
of $K',\mathscr H$ over $\mathbb Q$. Gauss' lemma makes it a
divisor over $\mathbb Z$. Its leading coefficient divides $8$, so
its reduction modulo $5$ keeps positive degree. It would divide both
reduced polynomials, contradicting the displayed Euclidean lists.
This proves the two rational gcd statements. The first makes $K$
squarefree in characteristic zero; the second excludes
$\mathscr H$ at every complex root of $K$. Finally (3.4) shows that
$K$ and $\Delta$ have no common root. ∎

**Definition 4.2 (Exceptional drift roots).** Fix $x=\kappa$ in
(2.2)–(2.4), regarding each $H_i$ as an affine function of $d$.
If $N(\kappa;p,v,m)\ne0$, put $\mathcal E(p,v,m)=\varnothing$.
If $N(\kappa;p,v,m)=0$, define

$$
\Phi_\kappa(d)=H_0(H_2+2d-294/5)-dH_2.
\tag{4.5}
$$

For each real root of (4.5), first require

$$
H_0^2+H_2^2>0,\qquad H_1\ne0,
\tag{4.6}
$$

then set

$$
\begin{gathered}
u=-\frac{dH_0+H_2(H_2+2d-294/5)}{H_0^2+H_2^2},\qquad
b=\frac{1-u}{2u},\\
j=\frac{24-d}{uH_1},\qquad
n=\frac\kappa u,\qquad
r=\frac{\kappa H_1+d-24}{uH_1}.
\end{gathered}
\tag{4.7}
$$

Here require $0<u<1$ before using the divisions by $u$. Keep the root
exactly when also

$$
0<r<1,\qquad bj=b^2+r(1-r).
\tag{4.8}
$$

The resulting set of drift roots is $\mathcal E(p,v,m)$. Its world is
$W=(P(r,b),g,d)$ with $g=uh$ and the one interpolant (2.3).

**Theorem 4.3 (Genuine quadratic and exceptional equivalence).** For
every $p\ne24,v,m$, the worlds in $\mathcal W(p,v,m)$ with $K(x)=0$
are in bijection with $\mathcal E(p,v,m)$. In the layer $N(\kappa)=0$,
$\Phi_\kappa$ is genuinely quadratic in $d$, with leading coefficient

$$
[d^2]\Phi_\kappa=\frac{\mathscr H(\kappa)}{\Delta(\kappa)^2}\ne0.
\tag{4.9}
$$

In particular there are at most two exceptional worlds.

Proof. The coefficients of $d$ in $H_0,H_2$ from (2.4) are exactly
$-M_0/\Delta,-M_2/\Delta$. Therefore the coefficient of $d^2$ in
$H_0(H_2+2d-294/5)-dH_2$ is

$$
\frac{M_0M_2-2M_0\Delta+M_2\Delta}{\Delta^2}
=\frac{\mathscr H}{\Delta^2}.
\tag{4.10}
$$

Proposition 4.1 proves its nonvanishing at $\kappa$, independently
of $(p,v,m)$. Every exceptional actual world has $x=\kappa$ by
Proposition 4.1 and $N(\kappa)=0$ by (2.6). Its clocks zero and two
give (4.5), the positive sum of squares, and the unique $u$ in (4.7)
by the residual identities (3.8), which do not require $K\ne0$ when
written in $H_i,d$. The consequence $d\ne24$ and clock one give
$H_1\ne0$. The remaining formulas and guards are its strict source
coordinates and source identity.

Conversely an allowed drift root determines $h$ and the unique $u$
in (4.7). The same residual identities give clocks zero and two;
the definition of $j$ gives clock one. Since $K=N=0$, (2.6) gives
clock three for this drift without a division by $K$. The four tail
rows hold by (2.2)–(2.3). The source identity and strict guards give
the original positive source, $n=j+r$, $U=1/u$, and a nonzero
whole gain $g=uh$ as in Theorem 3.3. Thus every retained drift root
is sufficient for a full original world. Different roots give different
drifts and hence different complete triples. The nonzero quadratic
has at most two distinct real roots, whether or not it has a repeated
root. ∎

## 5. Uniform noncollapse and the seven-world bound

**Proposition 5.1 (Noncollapse for every response specialization).** For
every complex triple $(p,v,m)$, the polynomial $F(x;p,v,m)$ in (3.1)
is not identically zero. The exact polynomial divisibility identity is

$$
K\ \bigm|\ \Delta^2F-5N^2\mathscr H
\qquad\text{in }\mathbb Q[p,v,m][x].
\tag{5.1}
$$

If $N(\kappa;p,v,m)=0$, then $(x-\kappa)^2$ divides the specialized
$F$ over $\mathbb C[x]$.

Proof. Since $\gcd(K,\Delta)=1$, calculations modulo $K$ may use
$\Delta^{-1}$. The definitions give, modulo $K$,

$$
Z_0\equiv-\frac{NM_0}{\Delta},\qquad
Z_2\equiv-\frac{NM_2}{\Delta},\qquad
B_*\equiv5N\left(2-\frac{M_2}{\Delta}\right).
\tag{5.2}
$$

Substitution in $F$ gives (5.1). These are congruences of the exact
polynomials (3.1), so (5.1) remains true under every specialization.
Let $\lambda$ be any complex root of $K$. By Proposition 4.1 and
(3.4), $\mathscr H(\lambda)\Delta(\lambda)\ne0$; hence

$$
F(\lambda)=\frac{5N(\lambda)^2\mathscr H(\lambda)}{\Delta(\lambda)^2}.
\tag{5.3}
$$

If a specialization made $F$ identically zero, then $N$ would vanish
at all four distinct complex roots of $K$. The factor theorem in
characteristic zero would give $K\mid N$. But $[x^4]N=144$ and
$[x^4]K=8$, so necessarily $N=18K$. Their constant terms contradict
this: $N(0)=-144$, whereas $18K(0)=-108$. Thus $F$ never collapses.
The finite-field computation in Proposition 4.1 supplies rational
coprimality; the argument (5.3) takes place in characteristic zero
and does not infer real positivity from reduction modulo $5$.

Finally suppose $N(\kappa)=0$. Since $K(\kappa)=0$ and all tail
denominators are nonzero, each $f_i(\kappa)=0$. Consequently each
$Z_i$, as well as $N$ and $B_*$, vanishes at $\kappa$. Both products
in $F=Z_0B_*-5NZ_2$ have at least two factors $x-\kappa$.
This proves the asserted double factor, without asserting simplicity
of any other root of $F$. ∎

**Theorem 5.2 (Full fixed-response inverse and the bound seven).** For
every real $p\ne24,v,m$, reconstruction gives a disjoint bijection

$$
\mathcal R(p,v,m)\ \sqcup\ \mathcal E(p,v,m)
\ \longrightarrow\ \mathcal W(p,v,m),
\tag{5.4}
$$

where the two maps are (3.5) and (4.7). In particular,

$$
|\mathcal W(p,v,m)|\le7.
\tag{5.5}
$$

If the exceptional layer $N(\kappa)=0$ is present, there are at most
five ordinary worlds and at most two exceptional worlds.

Proof. Every actual world has $x>0$ and either $K(x)\ne0$ or
$x=\kappa$. Theorems 3.3 and 4.3 give the two exhaustive bijections.
Their images are disjoint because their $x$ coordinates differ.
In particular these maps count distinct worlds, not algebraic
multiplicities or alternative descriptions of one whole gain.

If $N(\kappa)\ne0$, there is no exceptional world. Proposition 5.1
and the degree bound $\deg F\le7$ give at most seven distinct roots
of $F$, and hence at most seven ordinary worlds. If $N(\kappa)=0$,
the nonzero polynomial $F/(x-\kappa)^2$ has degree at most five.
Every ordinary root is a distinct root of this quotient, so there are
at most five ordinary worlds. The genuine exceptional quadratic adds
at most two. These classical polynomial root bounds apply also after
any degree drop or repeated root. They yield (5.5) in both cases. ∎

**Corollary 5.3 (Exact finite M-fibre ambiguity).** Let
$\nu_M(p,v,m)$ be the number of different reconstructed strict sources
from (5.4). Then

$$
\nu_M(p,v,m)=|\mathcal W(p,v,m)|\le7,
\qquad
D_M=\{(p,v):p\ne24,\ \exists m\in\mathbb R,\ \nu_M(p,v,m)\ge2\}.
\tag{5.6}
$$

For fixed $(p,v,m)$, an equal-$M$ pair may have two ordinary endpoints,
one ordinary and one exceptional endpoint, or two exceptional endpoints.

Proof. At fixed $p$, O, Theorem 12.3 makes the complete world unique
at any strict source, including $\Lambda=0$. Thus different worlds in
(5.4) are exactly different sources, and the union has no hidden gain
or drift multiplicity at a fixed source. The definition of $D_M$ in
S, Definition 1.2, now gives (5.6). The three pair types exhaust an
unordered pair in the disjoint union (5.4). A repeated root of $F$
or $\Phi_\kappa$ is counted once, and a root failing a strict guard
is not counted. ∎

## 6. The actual J terminal and the independent pair question

**Theorem 6.1 (Actual J terminal in inverse coordinates).** Every world
reconstructed by (5.4) has

$$
a(W)=d+\left(\frac{1+u}{2}+2x+2ur\right)
                    \frac{m-d}{2x+3}.
\tag{6.1}
$$

Proof. On the original source,

$$
\frac TU=\frac{1+u}{2},\qquad \frac jU=x-ur,\qquad
\frac{T+2j+4r}{U}=\frac{1+u}{2}+2x+2ur.
\tag{6.2}
$$

The terminal $M$ row gives $h(7)=(m-d)/(2x+3)$. Substitute (6.2)
and $g(7)=uh(7)$ in the actual trace formula
$a=d+(T+2j+4r)g(7)$. This proves (6.1), including $m=d$, for which
both terminal responses equal $d$. No division by $m-d$ occurs. ∎

**Proposition 6.2 (An exact distinction between two rational expressions).**
The expression

$$
\widetilde a=d+\frac{1+u}{2}+2x+\frac{2ur}{2x+3}
\tag{6.3}
$$

does not equal the actual terminal response on all original worlds.
Specifically take

$$
\begin{gathered}
b=1,\qquad r=1/2,\qquad d=3933/121,\\
g(s)=\frac{1199s^3-9783s^2+24133s-19665}{605}.
\end{gathered}
\tag{6.4}
$$

This is a strict world in $\mathcal W(p,v,m)$ with

$$
\begin{gathered}
p=9918/121,\qquad v=1068459/2420,\qquad m=206823/121,\\
a=547179/605,\qquad \widetilde a=624677/18150,\qquad
a-\widetilde a=15790693/18150\ne0.
\end{gathered}
\tag{6.5}
$$

Proof. The source has $j=5/4$, $n=7/4$, $T=2$, $U=3$,
$u=1/3$, $x=7/12$. The complete gain samples at $0,\ldots,7$ are

$$
\left(-\frac{3933}{121},-\frac{4116}{605},-\frac{939}{605},
-\frac{588}{121},-\frac{585}{121},\frac{1260}{121},
\frac{31929}{605},\frac{81156}{605}\right).
\tag{6.6}
$$

Multiplying these by the traces (1.3) and adding the fixed $d$ gives
$0,24,147/5,24,18,p,v,m$ exactly. In particular $p\ne24$.
The actual $J$ trace is $T+2j+4r=13/2$, giving the stated $a$.
Direct substitution in (6.3) gives the stated $\widetilde a$ and
their nonzero difference. ∎

**Definition 6.3 (The full same-base relation in inverse variables).**
For each fixed base $(p,v)$ with $p\ne24$, select real numbers
$m_0,m_1,m$ independently. Let $\xi_0,\xi_1$ belong respectively
to the full disjoint unions
$\mathcal R(p,v,m_0)\sqcup\mathcal E(p,v,m_0)$ and
$\mathcal R(p,v,m_1)\sqcup\mathcal E(p,v,m_1)$; let
$\xi_2,\xi_3$ belong to the full disjoint union
$\mathcal R(p,v,m)\sqcup\mathcal E(p,v,m)$. The values $m_0,m_1$ may
coincide. Denote their reconstructed worlds by $W_i$ and evaluate
$a_i$ by (6.1), using the appropriate $m_i$ for each of $i=0,1$.
The relation is

$$
W_0\ne W_1,\qquad a_0=a_1,\qquad W_2\ne W_3.
\tag{6.7}
$$

There is no cross-pair inequality, no requirement $m_0=m_1$, and no
equation between the common $J$ response and the common $M$ response.

**Proposition 6.4 (Faithful joint consumer and its unresolved existence).**
There is a base in $D_J\cap D_M$ exactly when (6.7) has a solution
for some real $p\ne24,v,m_0,m_1,m$ and guarded candidates as in
Definition 6.3. A positive solution requires only the four actual
endpoints, with permitted overlap, and does not require exhaustion of
$C(p,v)$.

Proof. The bijection (5.4) reconstructs precisely every original world
with any specified auxiliary terminal $M$ value. Given an actual
$J$ pair, assign its two individual $M$ responses to $m_0,m_1$.
Given an independently selected actual $M$ pair in the same child,
assign its common $M$ response to $m$. Equation (6.1) identifies
the actual $J$ equality, so these choices give (6.7). Conversely the
four reconstructed worlds all belong to the same entire $C(p,v)$;
(6.7) gives the two within-pair distinctness conditions, the $J$
equality, and the $M$ equality by construction. These are precisely
S, Definition 1.2 and SIII, Definition 19.1, with independent pair
choices. No condition is imposed on unused companions. ∎

**Definition 6.5 (Remaining mathematical question and scope).** The
unresolved question is whether there exist real $p\ne24,v$ and an
independently selected distinct equal-$J$ pair and distinct equal-$M$
pair in the entire actual $C(p,v)$, equivalently a solution of (6.7).
The seven-world bound fixes the full tuple $(p,v,m)$, while the
published bound $24$ fixes only $(p,v)$. No attainment of seven,
global collision curve, same-base joint witness, or all-domain absence
is asserted by (5.5). A complete absence result would have to cover
every such base and all auxiliary terminal values in Definition 6.3,
including ordinary/exceptional mixtures, repeated roots, degree drops,
zero drift, sampled gain zeros, and singular sources.

The quartic and its unique-positive-root fact are reused from
FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY §26 and
FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV §2. The source-specific
content here is the actual fixed-terminal inverse, the guarded circuits,
and the noncollapse/double-factor count. Distinct-node interpolation,
the factor theorem, Descartes' rule, and Euclidean coprimality are
classical intermediate tools. The general world reconstruction, source
uniqueness, and independent-pair semantics remain the cited O/F/S
interfaces; their general conclusions are reused with the parameter
correspondences above.

## 追加锚（本行以下为增补区）

## 7. The original parent and the complete exceptional interval

**Definition 7.1 (Parent worlds and cited source versions).** The symbols
O, F, IX and SIII retain the source meanings of Sections 1 and 6. The
citations in Sections 7–11 use the following mathematical texts at revision
$\texttt{403741dec0c5df912168c53ed1cdce6707041300}$:

| Citation | Source and interface |
| --- | --- |
| O | [Common-parent geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3 and Theorem 2.1: the original source, clocks and zero-safe parent converse. |
| F | [All-response finite-fibre geometry](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md), Theorems 26.3–26.4 and 32.1: the complete exceptional chart, equal-ratio $M$ classification and off-$24$ child bound. |
| IX | [Trace-corrected complex projection](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md), Propositions 2.1–2.3: literal traces, the clock-four identity and the whole-gain bridge. |
| SIII | [Third support volume](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Corollary 27.2: the same equal-ratio exclusion with F's sixth response $u$ identified with the present $v$. |
| X | Sections 1–6 of this volume: the ordinary and exceptional inverses, noncollapse, double factor, seven-world bound and independent-pair relation. |

Write $\mathcal P=\mathcal F(H_4)$ for the entire original parent, with
$P(r,b),J,M,H_4$ exactly as in (1.1)–(1.3). For a parent world put

$$
e=d-24,\qquad x=\frac nU,\qquad t=\frac rb.
\tag{7.1}
$$

The acquired functions on this parent, before fixing either response, are

$$
p(W)=24+e+(U+n)g(5),\qquad
v(W)=24+e+(2U+n)g(6).
\tag{7.2}
$$

For every real $p,v$, including $p=24$, use the notation

$$
\widehat C(p,v)=\{W\in\mathcal P:p(W)=p,\ v(W)=v\}.
\tag{7.3}
$$

Thus $\widehat C(p,v)=C(p,v)$ when $p\ne24$. No extra reading is
acquired by naming $x$ or $t$.

The reused converse of O, Theorem 2.1, with its $\beta=1/8$ and
$\epsilon=e$, is the following undivided interface:

$$
\begin{gathered}
b>0,\quad 0<r<1,\quad
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\\
e\Lambda+\frac65\frac{(8b-1)(5b+2)}{TU}=0,\\
(q_0,q_1,q_2,q_3)=
\left(-24-e,-\frac ej,\frac{27/5-e}{T},-\frac en\right),\\
g(s)=\sum_{i=0}^3q_i
 \prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k},
\qquad d=24+e.
\end{gathered}
\tag{7.4}
$$

Here $T=1+b$, $U=1+2b$, $j=b+r(1-r)/b$ and $n=j+r$ are positive.
This interface is a bijection with complete parent worlds. In particular,
$g$ is the single whole polynomial of degree at most three, and is
nonzero because the first two readings differ. By IX, Proposition 2.1,
the undivided residual at clock four is exactly

$$
y_4-18=U\left(e\Lambda+
       \frac65\frac{(8b-1)(5b+2)}{TU}\right).
\tag{7.5}
$$

The same fixed-node interpolant gives the actual clock-five formula

$$
g(5)=96-\frac{108}{T}
       +e\left(4+\frac{20}{T}-\frac{15}{j}-\frac{10}{n}\right).
\tag{7.6}
$$

Equations (7.4)–(7.6) use the original clocks and fixed drift. They do
not divide by $e,d,g(i)$, a leading coefficient, or a gain-root difference.
Their domain includes sampled zeros, degree drops and repeated roots.

**Definition 7.2 (Exact change from the existing exceptional chart).**
Let $\kappa$ be the unique positive root of $K$ in (2.5). F,
Theorem 26.3, already parametrizes the entire source locus $x=\kappa$
and proves $\Lambda<0$ and uniqueness of its complete parent lift.
The symbol $\alpha$ in F, Section 26, denotes this $\kappa$;
it does not denote the golden number used in Section 10 below.

Here is the exact reparametrization of that existing chart. With
$c_x=x^2+x-1$, write its denominator as

$$
D_F=(1-x)^2+(2x-1)(1-x)z+c_xz^2.
$$

Its source is $b=z(1-x)/D_F$ and
$r=z\{x(1-x)+c_xz\}/D_F$. Set

$$
t=x+\frac{c_x}{1-x}z,\qquad
z=\frac{(1-x)(t-x)}{c_x}.
\tag{7.7}
$$

At $x=\kappa$, $1-x>0$ and $c_x>0$. The map (7.7) carries
$0<z<1$ bijectively onto the connected strict interval

$$
I_\kappa=\left(\kappa,\frac{2\kappa-1}{1-\kappa}\right).
\tag{7.8}
$$

For use in the response circuit define, in variable order $(x,t)$,

$$
\begin{aligned}
V&=t^2+t-1,&D&=t^2-t+2x-1,\\
B&=t^2+x-1,&E&=(x-1)t^2+2xt-x.
\end{aligned}
\tag{7.9}
$$

The letters $B,D,E,V$ in (7.9) are chart polynomials. In particular
$V$ here is not O's trace abbreviation $U+n$, and $D$ is not
$D_*$ of (3.1). The change (7.7) satisfies the rational identities

$$
\begin{gathered}
D(x,t(x,z))=\frac{c_x}{(1-x)^2}D_F(x,z),\\
\frac{t-x}{D}=\frac{z(1-x)}{D_F},\qquad
\frac{t(t-x)}{D}=\frac{z\{x(1-x)+c_xz\}}{D_F},\\
\left.t\right|_{z=1}=\frac{2x-1}{1-x}.
\end{gathered}
\tag{7.10}
$$

Thus the following source formulas and their exhaustive domain are
exactly F's chart in the new parameter, rather than a new source locus:

$$
\begin{gathered}
x=\kappa,\quad t\in I_\kappa,\qquad
b=\frac{t-x}{D},\quad r=\frac{t(t-x)}{D},\\
U=\frac VD,\quad T=\frac BD,\quad
j=\frac ED,\quad n=\frac{xV}{D}.
\end{gathered}
\tag{7.11}
$$

The denominator guards needed for this use are explicit. Proposition 4.1
and the exact additional endpoint evaluation give

$$
K(5/8)=-\frac{11}{256},\qquad
K(313/500)=\frac{100301547}{15625000000}>0,\qquad
\frac58<\kappa<\frac{313}{500}<\frac23.
\tag{7.12}
$$

Consequently

$$
D(\kappa,t)=\left(t-\frac12\right)^2+2\kappa-\frac54>0
\quad\hbox{for every real }t.
\tag{7.13}
$$

There is no omitted $D=0$ source on the exceptional layer. In (7.11),
$1-r=\{(x-1)t+2x-1\}/D>0$ precisely up to the upper endpoint
of (7.8), while $b>0$ precisely after its lower endpoint. Also
$x,T,U,j,n,B,V,E$ are all positive there. These are the strict source
and trace guards of the reused chart; its endpoints are not worlds.

For the derivative below a convenient quantitative form of the existing
pole exclusion is

$$
\Lambda<-\frac4{21}\qquad(x=\kappa,\ t\in I_\kappa).
\tag{7.14}
$$

Indeed $t>x$ gives $r>xb$ and $j=xU-r<xT$, whereas $r=tb<1$
gives $b<1/t<1/x<8/5$ and $U<21/5$. Therefore

$$
\begin{aligned}
\Lambda
&<1+\frac{6-4/x}{T}+\frac{1-4/x}{U}\\
&<1-\frac5U<-\frac4{21},
\end{aligned}
$$

using $x<2/3$. This bound holds before fixing $p,v$ or a terminal.
The parent lift and its nonzero denominator are the ones already supplied
by F, Theorem 26.3 and (7.4).

## 8. The original fifth response and its full rational certificate

**Definition 8.1 (Response polynomials).** In $\mathbb Q[x,t]$, use
(7.9) and define

$$
\begin{aligned}
C&=-t^2+9t-10x+1,\\
L_c&=2t^2+3t-x-2,\\
A&=xBVE+6xDVE+(x-4)DBE-4xDBV,\\
I_c&=DBxE+(1+x)(4VBxE+20VDxE-15VDBx-10DBE),\\
Q_c&=5ADB,\\
P_c&=24Q_c+5A(1+x)V(96B-108D)-6C L_c I_c,\\
H&=(\partial_tP_c)Q_c-P_c(\partial_tQ_c).
\end{aligned}
\tag{8.1}
$$

Here $L_c$ is unrelated to $L$ in (3.1), and $P_c$ is not the source
matrix. Substitution of (7.11) in the original equations (7.4), (7.6)
and (7.2) gives the rational identities

$$
\Lambda=\frac{A}{xBVE},\qquad
e=-\frac{6xECL_c}{5A},\qquad p=\frac{P_c}{Q_c}.
\tag{8.2}
$$

These identities hold wherever their displayed denominators are nonzero;
their cleared numerators vanish in $\mathbb Q[x,t]$, without reducing
modulo $K$. On the complete exceptional interval, (7.13)–(7.14) and
$x,B,V,E>0$ give $A=xBVE\Lambda<0$ and $Q_c\ne0$. Thus (8.2)
is the actual response of every whole parent world on that interval.

**Lemma 8.2 (Evaluated tensor certificate).** The bidegrees of
$P_c,Q_c$ are both $(6,10)$; $H$ has bidegree exactly $(12,18)$
and $192$ nonzero power coefficients. On the entire rectangle

$$
\mathcal R_c=[5/8,313/500]\times[5/8,27/40]
$$

one has

$$
H(x,t)\ \ge\ \frac{631875}{2^{61}}>0.
\tag{8.3}
$$

Proof. The following finite rational certificate specifies every
coefficient. Put

$$
\begin{gathered}
\widehat H(X,Y)=H\left(\frac58+\frac{X}{1000},
                         \frac58+\frac{Y}{20}\right)
 =\sum_{k=0}^{12}\sum_{l=0}^{18}h_{kl}X^kY^l,\\
\beta_{ij}=\sum_{k=0}^i\sum_{l=0}^j
 h_{kl}\frac{\binom ik}{\binom{12}k}
         \frac{\binom jl}{\binom{18}l},
\quad 0\le i\le12,\quad0\le j\le18.
\end{gathered}
\tag{8.4}
$$

For a direct conversion using only the circuit (8.1), write
$a_{ab}=[x^at^b]H$ with missing entries zero. Then

$$
h_{kl}=\frac{1}{1000^k20^l}
 \sum_{a=k}^{12}\sum_{b=l}^{18}
 a_{ab}\binom ak\binom bl
 \left(\frac58\right)^{a-k+b-l}.
\tag{8.5}
$$

The exact evaluated values $\beta_{ij}=n_{ij}/d_{ij}$ are all the
entries of the following table; both integer columns are positive.

| $i$ | $j$ | $n_{ij}$ | $d_{ij}$ |
| --- | --- | --- | --- |
| 0 | 0 | 631875 | 2305843009213693952 |
| 0 | 1 | 4354475 | 6917529027641081856 |
| 0 | 2 | 162401905 | 117597993469898391552 |
| 0 | 3 | 113997641 | 39199331156632797184 |
| 0 | 4 | 28937848471 | 4899916394579099648000 |
| 0 | 5 | 398279687171 | 34299414762053697536000 |
| 0 | 6 | 49432257188793 | 2229461959533490339840000 |
| 0 | 7 | 13121794206501 | 318494565647641477120000 |
| 0 | 8 | 19599116176341199 | 262758016659304218624000000 |
| 0 | 9 | 288311547381905511 | 2189650138827535155200000000 |
| 0 | 10 | 1489336973584844959 | 6568950416482605465600000000 |
| 0 | 11 | 3033039325533661 | 7962364141191036928000000 |
| 0 | 12 | 21758008319235840777 | 34835343117710786560000000000 |
| 0 | 13 | 13393538785976445603 | 13398208891427225600000000000 |
| 0 | 14 | 74728243410154495719 | 47850746040811520000000000000 |
| 0 | 15 | 22787053989937040601 | 9570149208162304000000000000 |
| 0 | 16 | 847279366576223064939 | 239253730204057600000000000000 |
| 0 | 17 | 361224351666296961381 | 70368744177664000000000000000 |
| 0 | 18 | 2547554724664213750731 | 351843720888320000000000000000 |
| 1 | 0 | 675439 | 2305843009213693952 |
| 1 | 1 | 348260791 | 518814677073081139200 |
| 1 | 2 | 64775034899 | 44099247551211896832000 |
| 1 | 3 | 226734179891 | 73498745918686494720000 |
| 1 | 4 | 19132982561323 | 3062447746611937280000000 |
| 1 | 5 | 157571509475279 | 12862280535770136576000000 |
| 1 | 6 | 97525975060013567 | 4180241174125294387200000000 |
| 1 | 7 | 387342615218929837 | 8957659658839916544000000000 |
| 1 | 8 | 197325533829356587 | 2526519390954848256000000000 |
| 1 | 9 | 188268210346842026129 | 1368531336767209472000000000000 |
| 1 | 10 | 2911910847100255593377 | 12316782030904885248000000000000 |
| 1 | 11 | 443990462018225580877 | 1119707457354989568000000000000 |
| 1 | 12 | 42404032274728451253071 | 65316268345707724800000000000000 |
| 1 | 13 | 26070244088668636241491 | 25121641671426048000000000000000 |
| 1 | 14 | 29062909784444170265149 | 17944029765304320000000000000000 |
| 1 | 15 | 73799997472352953599201 | 29906716275507200000000000000000 |
| 1 | 16 | 548596722021529527365927 | 149533581377536000000000000000000 |
| 1 | 17 | 46775278461382813597647 | 8796093022208000000000000000000 |
| 1 | 18 | 1650078176720405909301783 | 219902325555200000000000000000000 |
| 2 | 0 | 49626033 | 158526706883441459200 |
| 2 | 1 | 5801383621 | 8106479329266892800000 |
| 2 | 2 | 23677668371101 | 15159116345729089536000000 |
| 2 | 3 | 68882034494111 | 21054328257957068800000000 |
| 2 | 4 | 62606112808767313 | 9474447716080680960000000000 |
| 2 | 5 | 2448607534772563 | 189488954321613619200000000 |
| 2 | 6 | 35269023470766485233 | 1436957903605569945600000000000 |
| 2 | 7 | 4109550271815185987 | 90564573756653568000000000000 |
| 2 | 8 | 814555059994245262603 | 9962103113231892480000000000000 |
| 2 | 9 | 33802990023425199445481 | 235216323506864128000000000000000 |
| 2 | 10 | 1043604115055830834712527 | 4233893823123554304000000000000000 |
| 2 | 11 | 397118467409537502206651 | 962248596164444160000000000000000 |
| 2 | 12 | 3029670960437511366800177 | 4490493448767406080000000000000000 |
| 2 | 13 | 1550281732422369221520677 | 1439260720758784000000000000000000 |
| 2 | 14 | 51795905024485729669632511 | 30841301159116800000000000000000000 |
| 2 | 15 | 13143182192778836187134359 | 5140216859852800000000000000000000 |
| 2 | 16 | 53268952729805987157962597 | 14018773254144000000000000000000000 |
| 2 | 17 | 41631030696159963504096859 | 7559142440960000000000000000000000 |
| 2 | 18 | 53422429850190767527218027 | 6871947673600000000000000000000000 |
| 3 | 0 | 16569355132677 | 49539595901075456000000000 |
| 3 | 1 | 566825127036871 | 743093938516131840000000000 |
| 3 | 2 | 20977285276983899 | 12632596954774241280000000000 |
| 3 | 3 | 365183332376130177 | 105271641289785344000000000000 |
| 3 | 4 | 11033839828853582383 | 1579074619346780160000000000000 |
| 3 | 5 | 753180137763120578521 | 55267611677137305600000000000000 |
| 3 | 6 | 30914668608186303436367 | 1197464919671308288000000000000000 |
| 3 | 7 | 122166790019554910876399 | 2565996256438517760000000000000000 |
| 3 | 8 | 805257258801485116824031 | 9408652940274565120000000000000000 |
| 3 | 9 | 176531227245764374940768751 | 1176081617534320640000000000000000000 |
| 3 | 10 | 906570087532860561321989513 | 3528244852602961920000000000000000000 |
| 3 | 11 | 40514933396011010700716807 | 94338097663180800000000000000000000 |
| 3 | 12 | 13116853903530955617539482183 | 18710389369864192000000000000000000000 |
| 3 | 13 | 202794320471514332367036479 | 181419418583040000000000000000000000 |
| 3 | 14 | 134245912396326838991248199891 | 77103252897792000000000000000000000000 |
| 3 | 15 | 13615923572937824250974383317 | 5140216859852800000000000000000000000 |
| 3 | 16 | 137901565518435603114284997277 | 35046933135360000000000000000000000000 |
| 3 | 17 | 215524605780685882748890702669 | 37795712204800000000000000000000000000 |
| 3 | 18 | 304317867742753832139690433017 | 37795712204800000000000000000000000000 |
| 4 | 0 | 3318545307436993 | 9288674231451648000000000000 |
| 4 | 1 | 339763273139059211 | 417990340415324160000000000000 |
| 4 | 2 | 20903303078114893379 | 11843059645100851200000000000000 |
| 4 | 3 | 217758812584821636301 | 59215298225504256000000000000000 |
| 4 | 4 | 32808973910141592547309 | 4441147366912819200000000000000000 |
| 4 | 5 | 446716094408778011369317 | 31088031568389734400000000000000000 |
| 4 | 6 | 3657561519138583648924109 | 134714803463022182400000000000000000 |
| 4 | 7 | 72088022162973216982864627 | 1443372894246666240000000000000000000 |
| 4 | 8 | 2176539220730477689213469 | 24299206973849600000000000000000000 |
| 4 | 9 | 2304408663730931103677862879 | 14701020219179008000000000000000000000 |
| 4 | 10 | 106299998738472015623527791803 | 396927545917833216000000000000000000000 |
| 4 | 11 | 403101195796457779104599674411 | 902108058904166400000000000000000000000 |
| 4 | 12 | 7665288159401411761046726779121 | 10524594020548608000000000000000000000000 |
| 4 | 13 | 14084910116026443200701669451509 | 12143762331402240000000000000000000000000 |
| 4 | 14 | 78273120856528559171831234303741 | 43370579755008000000000000000000000000000 |
| 4 | 15 | 7932919266102548476418603301473 | 2891371983667200000000000000000000000000 |
| 4 | 16 | 883378754755931433725614247148697 | 216852898775040000000000000000000000000000 |
| 4 | 17 | 376482458057983266727780329359851 | 63780264345600000000000000000000000000000 |
| 4 | 18 | 295403487622949617874344464018929 | 35433480192000000000000000000000000000000 |
| 5 | 0 | 23626085606387323 | 61924494876344320000000000000 |
| 5 | 1 | 36197588766560283281 | 41799034041532416000000000000000 |
| 5 | 2 | 6663970008236241269917 | 3552917893530255360000000000000000 |
| 5 | 3 | 1538628830301978605327 | 394768654836695040000000000000000 |
| 5 | 4 | 315272131381309661752507 | 40374066971934720000000000000000000 |
| 5 | 5 | 47093305213155970621073027 | 3108803156838973440000000000000000000 |
| 5 | 6 | 1922907593309143935792496013 | 67357401731511091200000000000000000000 |
| 5 | 7 | 7560961203422663762831429387 | 144337289424666624000000000000000000000 |
| 5 | 8 | 82674220458924302993466829403 | 882061213150740480000000000000000000000 |
| 5 | 9 | 3609198236466725696932059044203 | 22051530328768512000000000000000000000000 |
| 5 | 10 | 55388009290904719670418476653699 | 198463772958916608000000000000000000000000 |
| 5 | 11 | 41934808745017215850591948307279 | 90210805890416640000000000000000000000000 |
| 5 | 12 | 113746614547009515494312595188107 | 150351343150694400000000000000000000000000 |
| 5 | 13 | 1461207694792371601290171593114747 | 1214376233140224000000000000000000000000000 |
| 5 | 14 | 8111972587423925097371349469523177 | 4337057975500800000000000000000000000000000 |
| 5 | 15 | 4107569566660177742792131403207093 | 1445685991833600000000000000000000000000000 |
| 5 | 16 | 3657455686566972336314762426517269 | 867411595100160000000000000000000000000000 |
| 5 | 17 | 7792484204606993373501319052460397 | 1275605286912000000000000000000000000000000 |
| 5 | 18 | 30578194310079086515349301093206149 | 3543348019200000000000000000000000000000000 |
| 6 | 0 | 27589199520796148671 | 67729916271001600000000000000000 |
| 6 | 1 | 1405651734206588009927 | 1523923116097536000000000000000000 |
| 6 | 2 | 73749813056934924097237 | 37009561390940160000000000000000000 |
| 6 | 3 | 10614486653000865171717 | 2570108429926400000000000000000000 |
| 6 | 4 | 89080274476949498448972433 | 10794455405690880000000000000000000000 |
| 6 | 5 | 201075163256088897559787079 | 12593531306639360000000000000000000000 |
| 6 | 6 | 49134112646253085068128618057 | 1637159069863116800000000000000000000000 |
| 6 | 7 | 144538801513324765807656798151 | 2631148505137152000000000000000000000000 |
| 6 | 8 | 44105019554243539497315939631 | 449768975237120000000000000000000000000 |
| 6 | 9 | 27474515625381056936476795717677 | 160792408647270400000000000000000000000000 |
| 6 | 10 | 467569643831261639793440943139189 | 1607924086472704000000000000000000000000000 |
| 6 | 11 | 637120098488438853922762707889 | 1317682544640000000000000000000000000000 |
| 6 | 12 | 20099385126648601126049689403410309 | 25580610466611200000000000000000000000000000 |
| 6 | 13 | 18419402350698826946078737881181609 | 14758044499968000000000000000000000000000000 |
| 6 | 14 | 204301679034641058021030024479968901 | 105414603571200000000000000000000000000000000 |
| 6 | 15 | 7047921147347539094240670283035373 | 2395786444800000000000000000000000000000000 |
| 6 | 16 | 2299896832480667492964480832963233677 | 527073017856000000000000000000000000000000000 |
| 6 | 17 | 1469750394124847688812433831041257487 | 232532213760000000000000000000000000000000000 |
| 6 | 18 | 461474372020545640641065187353788943 | 51673825280000000000000000000000000000000000 |
| 7 | 0 | 6310374639631756924741 | 14513553486643200000000000000000000 |
| 7 | 1 | 641504902926341603343101 | 653109906898944000000000000000000000 |
| 7 | 2 | 117504185181590602695434917 | 55514342086410240000000000000000000000 |
| 7 | 3 | 404822507917782518101391063 | 92523903477350400000000000000000000000 |
| 7 | 4 | 20169007774857600318525270107 | 2313097586933760000000000000000000000000 |
| 7 | 5 | 817309450919607602176244283739 | 48575049325608960000000000000000000000000 |
| 7 | 6 | 650982141550685984152450427263 | 20636458863820800000000000000000000000000 |
| 7 | 7 | 25979766516858665606575153672237 | 451054029452083200000000000000000000000000 |
| 7 | 8 | 195751040864794168210132669846867 | 1908305509220352000000000000000000000000000 |
| 7 | 9 | 1575738541439359673132699673340561 | 8834747727872000000000000000000000000000000 |
| 7 | 10 | 187885233451507526544778991643061679 | 620199290496614400000000000000000000000000000 |
| 7 | 11 | 141758160680823643185816178487685901 | 281908768407552000000000000000000000000000000 |
| 7 | 12 | 13417496657853257548197868209213349829 | 16444678157107200000000000000000000000000000000 |
| 7 | 13 | 1169553117771141799450112369276261743 | 903553744896000000000000000000000000000000000 |
| 7 | 14 | 2473950386831865379665836511272731919 | 1232118743040000000000000000000000000000000000 |
| 7 | 15 | 13758166028890535669849155026162568843 | 4517768724480000000000000000000000000000000000 |
| 7 | 16 | 61189944423800492564264340455092419269 | 13553306173440000000000000000000000000000000000 |
| 7 | 17 | 7722465280335508672084808129677323 | 1181116006400000000000000000000000000000000 |
| 7 | 18 | 272818910989857202107768054399978303 | 29527900160000000000000000000000000000000000 |
| 8 | 0 | 701455130468405143371987 | 1511828488192000000000000000000000000 |
| 8 | 1 | 213425586308979443416712119 | 204096845905920000000000000000000000000 |
| 8 | 2 | 1444250593336308503112660691 | 642527107481600000000000000000000000000 |
| 8 | 3 | 133993736334853738500382504637 | 28913719836672000000000000000000000000000 |
| 8 | 4 | 19974575607068039716385032968821 | 2168528987750400000000000000000000000000000 |
| 8 | 5 | 269101643675639331259778771454833 | 15179702914252800000000000000000000000000000 |
| 8 | 6 | 10903189732367215695029121904886377 | 328893563142144000000000000000000000000000000 |
| 8 | 7 | 1091152493224234299954823892238749 | 18071074897920000000000000000000000000000000 |
| 8 | 8 | 4158684440130257328751030363255086719 | 38762455656038400000000000000000000000000000000 |
| 8 | 9 | 6680923460862975228803666302309793751 | 35891162644480000000000000000000000000000000000 |
| 8 | 10 | 27799408504771683879241802909049358093 | 88096490127360000000000000000000000000000000000 |
| 8 | 11 | 230320368907094906495641517680912200971 | 440482450636800000000000000000000000000000000000 |
| 8 | 12 | 621916581798062584255103470207387164479 | 734137417728000000000000000000000000000000000000 |
| 8 | 13 | 126328168484998264013789699771909123983 | 94120181760000000000000000000000000000000000000 |
| 8 | 14 | 1761811915391237539188803954343474276013 | 847081635840000000000000000000000000000000000000 |
| 8 | 15 | 177998898790695129591905614910612977249 | 56472109056000000000000000000000000000000000000 |
| 8 | 16 | 791229890893327508441689034784355186529 | 169416327168000000000000000000000000000000000000 |
| 8 | 17 | 67387163520312525844805457656312575547 | 9965666304000000000000000000000000000000000000 |
| 8 | 18 | 17636342092898286102835827646303708919 | 1845493760000000000000000000000000000000000000 |
| 9 | 0 | 11693073471979355049587841 | 23622320128000000000000000000000000000 |
| 9 | 1 | 131460834475325511344547261 | 118111600640000000000000000000000000000 |
| 9 | 2 | 23958914848106064561297022833 | 10039486054400000000000000000000000000000 |
| 9 | 3 | 246341951739844178432853989593 | 50197430272000000000000000000000000000000 |
| 9 | 4 | 12208646120636427291606876726069 | 1254935756800000000000000000000000000000000 |
| 9 | 5 | 492142815443536912765323840908089 | 26353650892800000000000000000000000000000000 |
| 9 | 6 | 1808112555948959309043746845197409 | 51908706304000000000000000000000000000000000 |
| 9 | 7 | 25812408638572669527905850528708717 | 407854120960000000000000000000000000000000000 |
| 9 | 8 | 7550108413797308073719787315728151997 | 67295929958400000000000000000000000000000000000 |
| 9 | 9 | 21786095195332538694979698778629622899 | 112159883264000000000000000000000000000000000000 |
| 9 | 10 | 552913050451408633517752177920845325277 | 1682398248960000000000000000000000000000000000000 |
| 9 | 11 | 138576259702132659988209550395606161813 | 254908825600000000000000000000000000000000000000 |
| 9 | 12 | 1569211889388252995635036678571838410927 | 1784361779200000000000000000000000000000000000000 |
| 9 | 13 | 27286239067477185505975166478172519213 | 19608371200000000000000000000000000000000000000 |
| 9 | 14 | 126713441837626846644396088636836371087 | 58825113600000000000000000000000000000000000000 |
| 9 | 15 | 12791638182522930937650085210347682957 | 3921674240000000000000000000000000000000000000 |
| 9 | 16 | 8610453757676211246763103448934559463 | 1782579200000000000000000000000000000000000000 |
| 9 | 17 | 733136637005559056130487552163968063 | 104857600000000000000000000000000000000000000 |
| 9 | 18 | 11398156811262924790568627352535560837 | 1153433600000000000000000000000000000000000000 |
| 10 | 0 | 623590993275389877202509369 | 1181116006400000000000000000000000000000 |
| 10 | 1 | 1398900757154752341766554851 | 1181116006400000000000000000000000000000 |
| 10 | 2 | 2288840991990335020301701726157 | 903553744896000000000000000000000000000000 |
| 10 | 3 | 39121222782860974537372716129773 | 7529614540800000000000000000000000000000000 |
| 10 | 4 | 5801303544855290030457154561062581 | 564721090560000000000000000000000000000000000 |
| 10 | 5 | 2356043271042773159742660516218849 | 119789322240000000000000000000000000000000000 |
| 10 | 6 | 13567735779834714334485387460130799 | 370776473600000000000000000000000000000000000 |
| 10 | 7 | 1352534651910881310261701036713478627 | 20392706048000000000000000000000000000000000000 |
| 10 | 8 | 78941325551084771396273507822178995537 | 672959299584000000000000000000000000000000000000 |
| 10 | 9 | 5682594113120975863150316489173481687189 | 28039970816000000000000000000000000000000000000000 |
| 10 | 10 | 17272899648349271892710314229196721106627 | 50471947468800000000000000000000000000000000000000 |
| 10 | 11 | 2592974317137025009680669727905624982291 | 4588358860800000000000000000000000000000000000000 |
| 10 | 12 | 9772660108143375023397542603361643154221 | 10706170675200000000000000000000000000000000000000 |
| 10 | 13 | 323996604868273757224685180598749806867 | 224604979200000000000000000000000000000000000000 |
| 10 | 14 | 1312137246665910728744593866299927544763 | 588251136000000000000000000000000000000000000000 |
| 10 | 15 | 36095417349931139062932389823784891279 | 10695475200000000000000000000000000000000000000 |
| 10 | 16 | 587649878139452863894718324990205951527 | 117650227200000000000000000000000000000000000000 |
| 10 | 17 | 150062860592964540081477569031943095367 | 20761804800000000000000000000000000000000000000 |
| 10 | 18 | 23567072570532512064354365574067880821 | 2306867200000000000000000000000000000000000000 |
| 11 | 0 | 944540006981517371678263731 | 1677721600000000000000000000000000000000 |
| 11 | 1 | 3170973719360469881124784601 | 2516582400000000000000000000000000000000 |
| 11 | 2 | 5750411261149817742018062236469 | 2139095040000000000000000000000000000000000 |
| 11 | 3 | 29410259742595148331281146008419 | 5347737600000000000000000000000000000000000 |
| 11 | 4 | 8699821714486613061402880369060087 | 802160640000000000000000000000000000000000000 |
| 11 | 5 | 58146943829198581957316269398767849 | 2807562240000000000000000000000000000000000000 |
| 11 | 6 | 668007940732361203921005521306299249 | 17380147200000000000000000000000000000000000000 |
| 11 | 7 | 3019567447372119258587607749160526471 | 43450368000000000000000000000000000000000000000 |
| 11 | 8 | 351670614287670233663857762201199357233 | 2867724288000000000000000000000000000000000000000 |
| 11 | 9 | 1981285485903452775909085722919903673 | 9371648000000000000000000000000000000000000000 |
| 11 | 10 | 68121638585702491556264677788762199531 | 191181619200000000000000000000000000000000000000 |
| 11 | 11 | 15312980435276950500234782015296914161 | 26070220800000000000000000000000000000000000000 |
| 11 | 12 | 14775844532377236355257606685286790897 | 15597568000000000000000000000000000000000000000 |
| 11 | 13 | 11660093444806165808025902601404670553 | 7798784000000000000000000000000000000000000000 |
| 11 | 14 | 2724316506804784382311910237241165931 | 1179648000000000000000000000000000000000000000 |
| 11 | 15 | 2333763054723536501350590273769763063 | 668467200000000000000000000000000000000000000 |
| 11 | 16 | 33139538435583106897818761256572227 | 6417285120000000000000000000000000000000000 |
| 11 | 17 | 4406205015837892989827125383489224879 | 589824000000000000000000000000000000000000000 |
| 11 | 18 | 1383985812355458262478953935140285091 | 131072000000000000000000000000000000000000000 |
| 12 | 0 | 50347189011833373168248692491 | 83886080000000000000000000000000000000000 |
| 12 | 1 | 562114640532530590889996005149 | 419430400000000000000000000000000000000000 |
| 12 | 2 | 101684767788090250230297080842891 | 35651584000000000000000000000000000000000000 |
| 12 | 3 | 1037463703348817077595308640435229 | 178257920000000000000000000000000000000000000 |
| 12 | 4 | 9002837794879797362900750505196421 | 786432000000000000000000000000000000000000000 |
| 12 | 5 | 680196396144637446426563156068069019 | 31195136000000000000000000000000000000000000000 |
| 12 | 6 | 16368712412906390040995924621723324917 | 405536768000000000000000000000000000000000000000 |
| 12 | 7 | 12653496390566132920674562102809855811 | 173801472000000000000000000000000000000000000000 |
| 12 | 8 | 436814639140696818116635341714193467 | 3407872000000000000000000000000000000000000000 |
| 12 | 9 | 2554997531725992882683777664177986757 | 11586764800000000000000000000000000000000000000 |
| 12 | 10 | 709162855162569258590575159823522548051 | 1911816192000000000000000000000000000000000000000 |
| 12 | 11 | 35363833508662240221240314567579915697 | 57933824000000000000000000000000000000000000000 |
| 12 | 12 | 398639251133202059879931656719236864413 | 405536768000000000000000000000000000000000000000 |
| 12 | 13 | 48333932587460654221768286305287648827 | 31195136000000000000000000000000000000000000000 |
| 12 | 14 | 10654075120531336201903413809513976591 | 4456448000000000000000000000000000000000000000 |
| 12 | 15 | 16092326394224213354199401903130590181 | 4456448000000000000000000000000000000000000000 |
| 12 | 16 | 71366866964669571918758358457315018213 | 13369344000000000000000000000000000000000000000 |
| 12 | 17 | 2023621960516913364805114313148334221 | 262144000000000000000000000000000000000000000 |
| 12 | 18 | 2860227443038466215149534353350355247 | 262144000000000000000000000000000000000000000 |

Expanding (8.1) and applying (8.5), then (8.4), yields exactly this
table. Equivalently, expansion of its following tensor expression
recovers every coefficient of $\widehat H$:

$$
\widehat H(X,Y)=\sum_{i=0}^{12}\sum_{j=0}^{18}
 \frac{n_{ij}}{d_{ij}}\binom{12}i X^i(1-X)^{12-i}
                          \binom{18}j Y^j(1-Y)^{18-j}.
\tag{8.6}
$$

In particular the table and (8.1), (8.4)–(8.5) specify the finite
coefficient identity in both directions. Exact integer comparison gives

$$
\min_{i,j}\beta_{ij}=\beta_{00}
 =\frac{631875}{2305843009213693952}
 =\frac{631875}{2^{61}},
\tag{8.7}
$$

with $(0,0)$ its only minimizer: every other row satisfies
$2^{61}n_{ij}>631875d_{ij}$, and the $(0,0)$ row satisfies equality.
The degrees and the count $192$ follow by expansion of the same circuit.
The tensor basis in (8.6) is nonnegative and sums to one on
$[0,1]^2$, proving (8.3) by the affine change in (8.4). This is the
classical Bernstein convex-hull identity, applied separately in both
variables; see Mourrain–Rouillier–Roy,
[*Bernstein's basis and real root isolation*](https://inria.hal.science/inria-00071434/document),
Section 2, Proposition 2.8, also used in F, Lemma 18.2. ∎

## 9. The earlier response separates the entire exceptional layer

**Theorem 9.1 (Whole-$\kappa$ $p$ separation).** On the complete
original parent stratum

$$
\mathcal P_\kappa=\{W\in\mathcal P:n(W)/U(W)=\kappa\},
$$

$p(W)$ is strictly increasing in $t=r/b$ throughout $I_\kappa$.
For every real $p_0$, including $p_0=24$,

$$
\left|\{W\in\mathcal P_\kappa:p(W)=p_0\}\right|\le1.
\tag{9.1}
$$

This is separation by $p$ alone, before fixing $v$ or either terminal;
it asserts at most one world and does not assert existence for arbitrary
$p_0$.

Proof. F, Theorem 26.3 and (7.7)–(7.11) identify every strict source
in this layer with exactly one $t\in I_\kappa$, and (7.4) supplies its
unique whole gain and drift. To cover the entire interval in the
certificate, the function $(2x-1)/(1-x)$ has derivative
$1/(1-x)^2>0$ for $x<1$. The rational root enclosure (7.12) gives

$$
\frac{2\kappa-1}{1-\kappa}
 <\frac{126}{187}<\frac{27}{40},\qquad
\frac58<\kappa<\frac{313}{500}.
\tag{9.2}
$$

Thus every $(\kappa,t)$ in the complete strict interval belongs to
$\mathcal R_c$. There is no break at a parent pole: (8.2) has
$Q_c\ne0$ at every such source. Lemma 8.2 therefore proves

$$
\frac{dp}{dt}(\kappa,t)=\frac{H(\kappa,t)}{Q_c(\kappa,t)^2}>0
\quad(t\in I_\kappa).
\tag{9.3}
$$

The mean value theorem on any two points of this interval gives strict
increase. Equal $p$ forces equal $t$, hence the same $b,r$, the same
$e$ by (7.4), and the same entire interpolant $g$ and fixed drift.
It therefore forces equality of complete worlds. No nonzero sample,
exact gain degree, gain sign or root-simplicity condition has entered. ∎

## 10. The independent golden-coordinate layer

**Theorem 10.1 (Complete golden layer and its $p$ separation).** Let

$$
\alpha=\frac{\sqrt5-1}{2},\qquad \alpha^2+\alpha-1=0.
\tag{10.1}
$$

The complete strict source locus $x=\alpha$ consists exactly of

$$
r=\alpha b,\quad 0<b<1/\alpha,\qquad
j=\alpha(1+b),\quad n=\alpha(1+2b).
\tag{10.2}
$$

Each such source has exactly one complete parent world. On this entire
interval its original fifth response is strictly increasing in $b$.
Consequently, for every real $p_0$,

$$
\left|\{W\in\mathcal P:n(W)/U(W)=\alpha, p(W)=p_0\}\right|\le1.
\tag{10.3}
$$

Proof. In the original source variable $t=r/b$, the equation $n=xU$
is $bD-t+x=0$. At $x=\alpha$ it factors exactly as

$$
bD-t+\alpha=(t-\alpha)\{b(t-\alpha^2)-1\}.
\tag{10.4}
$$

The second factor being zero would imply $r=tb=1+\alpha^2b>1$,
contrary to the strict source guard. Thus $t=\alpha$ and
$r=\alpha b$, with exactly the interval in (10.2). Substitution in
$j=b+r(1-r)/b$ and $n=j+r$ gives the remaining formulas there,
using $\alpha^2=1-\alpha$.

This layer is treated in its original source coordinates. At
$x=t=\alpha$ both $D$ and $V$ in (7.9) vanish, so the quotient
formulas (7.11) cannot be substituted at this point. Their coordinate
degeneration omits none of (10.2).

For the original parent and response define

$$
\begin{aligned}
D_g&=b^2+(2-6\alpha)b-4\alpha,\\
Q_g&=(1+b)D_g,\\
P_g&=(90-486\alpha)+(-297-1215\alpha)b\\
 &\qquad+(-1041-288\alpha)b^2+(-384+576\alpha)b^3.
\end{aligned}
\tag{10.5}
$$

Substitution in (7.4), (7.6) and (7.2), with
$\alpha^2+\alpha-1=0$, gives the exact identities

$$
\Lambda=\frac{2D_g}{(1+b)(1+2b)},\qquad
e=-\frac{3(8b-1)(5b+2)}{5D_g},\qquad
p=\frac{P_g}{5Q_g}.
\tag{10.6}
$$

To justify every denominator before using this lift, the quadratic
$D_g$ is convex and has the strictly negative endpoint values

$$
D_g(0)=-4\alpha<0,\qquad
D_g(1/\alpha)=-2-\alpha<0.
\tag{10.7}
$$

It lies at most at the chord between these two values, so $D_g<0$
on the whole closed interval $[0,1/\alpha]$. In particular $Q_g\ne0$
and $\Lambda<0$ on its strict interior. O, Theorem 2.1 through (7.4)
therefore gives exactly one parent lift per source, with $d=24+e$
and the same whole nonzero degree-at-most-three interpolant.

The derivative of the actual response (10.6) is the polynomial identity

$$
\begin{aligned}
5Q_g^2\frac{dp}{db}
&=(\partial_bP_g)Q_g-P_g(\partial_bQ_g)\\
&=(-180+3060\alpha)+(-4068+15852\alpha)b\\
&\qquad+(-12783+29085\alpha)b^2
       +(-12462+23934\alpha)b^3\\
&\qquad+(-3567+7776\alpha)b^4.
\end{aligned}
\tag{10.8}
$$

For clarity all five exact coefficient signs follow from the single
rational bound $\alpha>3/5$:

| Power of $b$ | Coefficient in (10.8) | Strict lower bound |
| --- | --- | --- |
| $0$ | $-180+3060\alpha$ | $1656$ |
| $1$ | $-4068+15852\alpha$ | $27216/5$ |
| $2$ | $-12783+29085\alpha$ | $4668$ |
| $3$ | $-12462+23934\alpha$ | $9492/5$ |
| $4$ | $-3567+7776\alpha$ | $5493/5$ |

The bound $\alpha>3/5$ follows by evaluating $z^2+z-1$ at
$z=3/5$, where it is $-1/25$, and using its strict increase on
$z>0$. Hence (10.8) is strictly positive throughout $0<b<1/\alpha$.
Since $5Q_g^2>0$, the mean value theorem gives strict increase of $p$.
Equality of $p$ forces equality of $b$, then of the source and its
unique complete parent lift. This proves (10.3).

Finally

$$
K(\alpha)=\alpha-1=-\alpha^2\ne0.
\tag{10.9}
$$

Thus the golden layer is an ordinary layer of the inverse in Section 3.
It is different from $x=\kappa$ and does not replace the exceptional
layer or its inverse. ∎

## 11. Entire-child consumers and the unchanged joint question

**Corollary 11.1 (Two $p$-only restrictions on selected endpoints).**
For any real $p,v$, the entire $\widehat C(p,v)$ contains at most one
world with $x=\kappa$ and at most one with $x=\alpha$. A distinct
pair in that child cannot have both endpoints in either of these
individual strata. In particular no distinct equal-$J$ pair can have
two $\kappa$ endpoints or two golden endpoints.

Proof. Every member of $\widehat C(p,v)$ is a complete parent world
with the same fifth response $p$. Apply (9.1) and (10.3), respectively.
These conclusions do not require equality of $v$ or of a terminal in
the larger parent set being separated. ∎

**Reused equal-$M$ exclusions and counting consequences.** F,
Theorem 26.4 already excludes every distinct equal-$x$, equal-$M$
pair in the entire $C(p,v)$ for $p\ne24$. Its sixth response $u$
is precisely the present $v$, and its reflected alternative occurs
only at $p=24$. SIII, Corollary 27.2 uses this identical correspondence.
Thus the exclusion of a two-$\kappa$ $M$ pair, and also of a two-golden
$M$ pair off $24$, are applications of that existing result. The
additional strength of Corollary 11.1 for the $\kappa$ layer is
separation before fixing $v$ or any terminal, and in particular its
$J$ consequence.

For real $p\ne24,v,m$, retain the exact $N$, $F$, $\mathcal R$,
$\mathcal E$ and $\mathcal W$ of (2.5), (3.1), Definition 4.2 and
(1.4). The exceptional equivalence in Theorem 4.3 and the cited
F26.4 exclusion already give

$$
|\mathcal E(p,v,m)|\le1.
\tag{11.1}
$$

This also follows from (9.1). Reusing Proposition 5.1's noncollapse
and double factor and Theorem 5.2's ordinary inverse gives the
conditional consequence

$$
p\ne24,\quad N(\kappa;p,v,m)=0
\quad\Longrightarrow\quad |\mathcal W(p,v,m)|\le6.
\tag{11.2}
$$

Indeed the nonzero polynomial $F/(x-\kappa)^2$ has degree at most
five by those existing results, so supplies at most five ordinary
worlds; (11.1) supplies at most one exceptional world. This argument
does not require an exceptional world to exist. If $N(\kappa)\ne0$,
there is no exceptional world, and the ordinary bound is seven.
Consequently the unconditional bounds retained from Theorem 5.2 and
F, Theorem 32.1 are

$$
p\ne24:\qquad |\mathcal W(p,v,m)|\le7,\qquad |C(p,v)|\le24.
\tag{11.3}
$$

Neither (11.2) nor (11.3) is asserted at $p=24$. The inverse,
noncollapse and double-factor mechanism in these statements are the
existing results of Sections 3–5; the conditional count combines them
with the existing F26.4 exclusion.

**Definition 11.2 (Independent pairs in the original whole child).**
The global question remains the existence of real $p\ne24,v,a,m$
and complete worlds $W_0,W_1,W_2,W_3\in C(p,v)$ such that

$$
W_0\ne W_1,\quad a(W_0)=a(W_1)=a,\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3)=m.
\tag{11.4}
$$

The two common values $a,m$ are independent and may differ. The two
pairs are independently chosen, and cross-pair overlap remains allowed.
For the $J$ endpoints their separate auxiliary values
$m_0=m(W_0)$ and $m_1=m(W_1)$ need not agree. Their actual $J$
responses are the unchanged expression of Theorem 6.1,

$$
a(W_i)=d_i+\left(\frac{1+u_i}{2}+2x_i+2u_ir_i\right)
                      \frac{m_i-d_i}{2x_i+3},\qquad u_i=1/U_i.
\tag{11.5}
$$

There is no division by $m_i-d_i$. If each selected pair uses a
$\kappa$ endpoint, both such labels must name the same unique
$\kappa$ world; that permitted sharing does not equate $a$ with $m$.
The same statement holds for a shared golden endpoint. A mixed
golden/other-source pair is not excluded by either $p$-only theorem.

Equations (9.1) and (10.3) restrict individual strata, and do not decide
(11.4). Ordinary–ordinary and ordinary–$\kappa$ endpoint cases,
mixed golden cases and all other original sources remain subject to
(11.4) and the cited existing exclusions. There is no restriction on
unused companions, no change of source, clock, action or acquired history,
and no added sign, exact-degree, root-simplicity, drift or nonzero-sample
hypothesis. Singular sources outside the two separated strata remain in
the original parent. The strict-real restrictions here do not delete
complex exceptional components from IX's saturation. No whole-domain
joint witness or absence conclusion follows from these two separations.

The source-specific content of Sections 8–10 is the explicit derivative
of the original $p$ response over the entire $\kappa$ layer and the
independent golden-layer exhaustion and derivative. F's complete chart
and pole exclusion, its equal-ratio $M$ classification, O's zero-safe
whole-world lift, IX's literal bridge and X's inverse/count mechanism are
the cited suppliers. Distinct-node interpolation is the classical formula
of Berrut–Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46
(2004), Section 2,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
The Bernstein identity, mean value theorem and polynomial root bound are
classical tools. No claim of priority in the mathematical literature is
made for the source-specific conclusions.

## 追加锚（本行以下为增补区）

## 12. The entire regular inventory on a closed actual negative-J segment

### 12.1. Original worlds, the full base and the inherited interfaces

Retain the complete worlds of (1.1), with their literal chronological
products:

$$
\begin{gathered}
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\\
0<r<1,\qquad b>0,\qquad
0\ne g\in\mathbb R[s],\qquad\deg g\le3,\qquad d\in\mathbb R,\\
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\\
(E_1,\ldots,E_6)=(J,M,J,M,M,M),\\
y_i=d+g(i)\operatorname{tr}(Q_iP),\qquad
(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v).
\end{gathered}
\tag{12.1}
$$

Both terminal alternatives act at clock seven on this same complete
world. With
$j=b+r(1-r)/b$, $n=j+r$, $T=1+b$, $U=1+2b$, their traces and readings are

$$
\begin{gathered}
(\operatorname{tr}(Q_iP))_{i=0}^6
 =(1,j,T,n,U,U+n,2U+n),\\
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7).
\end{gathered}
\tag{12.2}
$$

The entire $C(p,v)$ contains every world satisfying (12.1). The
independent-pair question (11.4) retains the quantifiers

$$
\begin{gathered}
\exists\,p\ne24,\ v,\ a,\ m,\quad W_0,W_1,W_2,W_3\in C(p,v):\\
W_0\ne W_1,\quad a(W_0)=a(W_1)=a,\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3)=m.
\end{gathered}
\tag{12.3}
$$

The pairs may overlap or be disjoint, and $a,m$ are unrelated common
values. Every world has its own fixed drift and one whole polynomial.
Lower gain degrees, zero samples and repeated gain roots remain allowed.
There is no shared-drift condition, reset, copy, extra port, clock shift
or replacement of the original source domain.

Use the exact rational interval and full-base rectangle

$$
\begin{gathered}
Q=[999/10^6,1001/10^6],\\
p_c=-4978573051372107/10^{13},\qquad r_p=17/500,\\
v_c=-476795440523806079/(5\cdot10^{14}),\qquad r_v=31/500,\\
\mathcal B=[p_c-r_p,p_c+r_p]\times[v_c-r_v,v_c+r_v].
\end{gathered}
\tag{12.4}
$$

All terminating decimals below are exact rationals. The following
ordinary mathematical interfaces are reused with their original
conditions and parameter correspondence.

| Published interface | Correspondence used here |
| --- | --- |
| [IX, Section 12, (12.1)–(12.9)](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#12-reused-whole-world-projection-inverse-and-normalized-carrier) | The identical complete world has $x=n/U$, $H=Ug$, the same $d,p,v$, the faithful inverse, and the necessary carrier $R=0$. Its (12.8) covers regular sources even at zeros of the intermediate factors $A$ or $F_0$. |
| [IX, Sections 24–26, especially (24.5)–(24.8), (25.1)–(25.2), Theorem 26.1](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#24-polynomial-secants-in-the-source-chart) | The exact secant zero $(X,Y,K_{\rm sec})(q)$ is the continued first equal-$J$ germ, within coordinate error $\rho=10^{-12}$ of the specified predictors on every closed cell, including their seams. $K_{\rm sec}$ is IX's secant coordinate $K$. |
| [IX, Theorem 27.1 and (27.3)](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#27-the-unique-transverse-strict-source-corner) | Its corner satisfies $q_*>0.0022954525$. Consequently the whole closed $Q$ lies strictly in $0<q<q_*$. |
| [IX, Theorem 28.1, (28.3)–(28.7)](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#28-original-world-lifts-and-the-closed-negative-base-range) | Before that corner, the two endpoints lift to distinct strict regular original worlds with equal $p,v,a$, using their respective whole gains and fixed drifts. |

These interfaces include their ordinary proofs. The full continuation,
germ attachment, corner proof and faithful-inverse proof are used in
their published scope. The calculations below supply the particular
full-base inclusion, exhaustive regular inventory and quantitative
terminal separation on (12.4).

The class
$\mathscr R=\{0<b\le1/10,\ 1\le r/b\le107/100\}$
in [IX, Sections 35–40](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#35-a-source-class-containing-the-negative-continuation)
has its stated restricted terminal-order theorem. Its containment of the
selected $J$ endpoints does not place all companions there. Moreover,
[IX, Proposition 41.1 and Section 42](https://github.com/the-omega-institute/trureturing/blob/79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md#41-strict-rational-failure-of-the-exterior-sign-implication)
give a strict regular exterior world with $v-2p>0$, equivalently the
negative product in IX (41.10). Thus that uniform exterior sign
implication cannot remove companions. The argument here counts all
regular projections over $\mathcal B$.

### 12.2. The regular source circuit and the exact continued endpoints

To specify the regular denominator and every evaluated response, put
$t=r/b$ and use the polynomial circuit of IX (12.5) and (24.2):

$$
\begin{gathered}
r=tb,\quad j=t+b(1-t^2),\quad n=j+tb,\quad T=1+b,\quad U=1+2b,\\
D_s=5\{(b^2+8b+4)jn-2TU(j+n)\},\qquad S=(8b-1)(2+5b),\\
C_0=-24D_s+3Sjn,\qquad C_1=3Sn,\\
C_2=3(49b+34)jn-54U(j+n),\qquad C_3=3Sj,\\
B_5=-4C_0+15C_1-20C_2+10C_3,\\
B_6=-10C_0+36C_1-45C_2+20C_3,\\
B_7=-20C_0+70C_1-84C_2+35C_3,\\
N_p=-C_0+(U+n)B_5,\qquad N_v=-C_0+(2U+n)B_6,\\
N_a=-C_0+(T+2j+4tb)B_7,\qquad N_m=-C_0+(3U+2n)B_7.
\end{gathered}
\tag{12.5}
$$

A world is called regular here exactly when $D_s\ne0$. Denote its
subset of the entire child by $C_{\rm reg}(p,v)$. The supplied
regular whole-world lift is

$$
\begin{gathered}
d=-C_0/D_s,\qquad
g(s)=\frac1{D_s}\sum_{i=0}^3 C_i
 \prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k},\\
(p,v,a,m)=(N_p,N_v,N_a,N_m)/D_s.
\end{gathered}
\tag{12.6}
$$

The parent identities IX (12.7) and (28.6), with $D=D_s$ there,
restore all five fixed parent readings in (12.1); $B_5,B_6,B_7$
evaluate this same interpolant at clocks five, six and seven. Unequal
readings $0,24$ ensure $g\ne0$ without a nonzero-sample assumption.

Let $(X,Y,K_{\rm sec})(q)$ be precisely the exact zero of IX (24.5)
identified in Theorem 26.1, rather than its rational predictor. Define

$$
h=\sqrt q,\qquad
t_\pm=X\pm K_{\rm sec}h,\qquad b_\pm=Y\pm h,\qquad
r_\pm=t_\pm b_\pm.
\tag{12.7}
$$

IX (24.7), applied separately to $p,v,a$, gives equality of these
three responses when both $D_{s,\pm}$ are nonzero. Theorems 27.1 and
28.1 supply that condition and strict original worlds $W_\pm(q)$
for $0<q<q_*$. Their distinction follows from
$b_+-b_-=2\sqrt q>0$. In particular this construction applies on
the entire closed $Q$, whose lower endpoint is positive and whose
upper endpoint is less than the stated lower bound for $q_*$.

### 12.3. The normalized necessary carrier and the faithful coordinates

For any compatible original world put $x=n/U>0$ and $H=Ug$. Its
whole polynomial is the unique degree-at-most-three interpolant at
the original nodes $3,4,5,6$ with values

$$
h_3=(24-d)/x,\qquad h_4=18-d,\qquad
h_5=(p-d)/(x+1),\qquad h_6=(v-d)/(x+2).
\tag{12.8}
$$

Its other needed values, and the general zero-safe inverse quantities,
are

$$
\begin{gathered}
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\\
H_2=4h_3-6h_4+4h_5-h_6,\qquad
H_7=-h_3+4h_4-6h_5+4h_6,\\
B_0=294/5-2d-H_2,\qquad \chi=d^2+B_0^2,\\
U=(-dH_0+B_0H_2)/\chi,\qquad b=(U-1)/2,\\
j=U(24-d)/H_1,\qquad r=xU-j,\qquad
g=H/U,\qquad m=d+(3+2x)H_7.
\end{gathered}
\tag{12.9}
$$

For actual $p\ne24$ worlds, IX (12.1)–(12.2) prove
$d\ne24$, $H_1\ne0$, $\chi>0$, $U>1$ and the restored identities
$dU=-H_0$, $B_0U=H_2$. Together with $0<r<1$ and
$j=b+r(1-r)/b$, those are the faithful inverse guards. Thus a
permitted $(x,d)$ determines at most one complete world, including
its entire gain. No condition $d\ne0$ is needed for this general
interface.

The following denominator is different from $D_s$:

$$
\begin{gathered}
D=x(x+1)(x+2),\\
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\qquad
a_2=4z_3-6z_4+4z_5-z_6,\qquad
z_*=xa_1-D(24-d).
\end{gathered}
\tag{12.10}
$$

Here $a_i=DH_i$ for $i=0,1,2$. Define the necessary polynomials

$$
\begin{aligned}
f&=5dDa_2+a_0\{(294-10d)D-5a_2\},\\
\mathcal K&=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1\\
&\qquad -(a_0+dD)\{dD+(1-2x)a_0\}a_1^2.
\end{aligned}
\tag{12.11}
$$

$\mathcal K$ is IX (12.3)'s polynomial called $K$; it is unrelated
to the quartic $K$ of (2.5) or the secant coordinate $K_{\rm sec}$.
Write $f=Ad^2+B_fd+C_f$ and
$\mathcal K=\sum_{i=0}^4 k_id^i$. Before any specialization, form
the following exact polynomial quotients in $\mathbb Q[x,p,v]$:

$$
\begin{aligned}
\alpha&=k_4(-B_f^3+2AB_fC_f)+k_3A(B_f^2-AC_f)
          -k_2A^2B_f+k_1A^3,\\
\zeta&=k_4(-B_f^2C_f+AC_f^2)+k_3AB_fC_f-k_2A^2C_f+k_0A^3,\\
F_0&=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480,\\
E&=(A\zeta^2-B_f\alpha\zeta+C_f\alpha^2)/A^3,\qquad
R=E/(256D^8F_0^2).
\end{aligned}
\tag{12.12}
$$

Expansion gives zero remainder in both polynomial divisions.
The resulting $R$ has coordinate degrees $(18,6,6)$ and total
$(p,v)$ degree six. In particular $\deg_xR\le18$ under every
base specialization. These definitions are exactly IX (12.3)–(12.4),
with the notation change $\mathcal K=K$ just specified.

Necessity at $A=0$ or $F_0=0$ does not follow merely from cancelling
those factors at a point. Use the supplied source identity IX (12.8):
if $R=\sum c_{ijk}x^ip^jv^k$, then

$$
\sum c_{ijk}n^iU^{18-i}N_p^jN_v^kD_s^{6-j-k}=0.
\tag{12.13}
$$

For a regular original source, its left side is
$U^{18}D_s^6R(n/U,N_p/D_s,N_v/D_s)$; $U>0$ and $D_s\ne0$.
Thus every regular original world satisfies $R=0$, including those
exceptional intermediate points. Every such world also satisfies
$f=\mathcal K=0$ by the same published inverse. Neither $A$ nor
$F_0$ is inverted at a world. No exclusion of the quartic-$K=0$
layer of Section 4 is made here.

### 12.4. Eighteen uniform disks exhaust the carrier

For a rational complex center $c$, expand the polynomial just defined:

$$
R(c+z,p_c+u,v_c+w)=\sum_{k,j,\ell}T_{kj\ell}z^ku^jw^\ell.
\tag{12.14}
$$

For a complex rational coefficient $a$ put
$\mathfrak U(a)=|\Re a|+|\Im a|$ and
$\mathfrak L(a)=\max(|\Re a|,|\Im a|)$. Define

$$
\begin{gathered}
E_k=\sum_{j+\ell>0}\mathfrak U(T_{kj\ell})r_p^jr_v^\ell,\qquad
U_k=\mathfrak U(T_{k00})+E_k,\\
L_1=\mathfrak L(T_{100})-E_1,\qquad
\Theta(c,\epsilon)=
\frac{U_0+\sum_{k=2}^{18}U_k\epsilon^k}{L_1\epsilon}.
\end{gathered}
\tag{12.15}
$$

The exact rational coefficient comparisons give $L_1>0$ and
the following strict bounds. Each displayed center and radius is
rational, including the real and imaginary coordinates of the last
two centers.

| Disk $j$ | $\Re c_j$ | $\Im c_j$ | $\epsilon_j$ | $\Theta(c_j,\epsilon_j)<$ |
| --- | --- | --- | --- | --- |
| 0 | -18.1078145193260267 | 0 | $1/10$ | 0.270 |
| 1 | -6.8548120586969603 | 0 | $1/100$ | 0.440 |
| 2 | -5.6391380897664973 | 0 | $1/100$ | 0.268 |
| 3 | -4.6679093711815433 | 0 | $1/100$ | 0.158 |
| 4 | -3.1887959786467426 | 0 | $1/1000$ | 0.475 |
| 5 | -3.1799246720608286 | 0 | $1/1000$ | 0.469 |
| 6 | -2.4835588139286718 | 0 | $1/10000$ | 0.470 |
| 7 | -0.4110614439347009 | 0 | $1/1000000$ | 0.558 |
| 8 | 0.3434434654565345 | 0 | $1/100000$ | 0.198 |
| 9 | 0.4075545729310278 | 0 | $1/100000$ | 0.271 |
| 10 | 0.9678579505862664 | 0 | $1/1000$ | 0.150 |
| 11 | 0.9930955345564154 | 0 | $1/1000$ | 0.230 |
| 12 | 1.9223318809923248 | 0 | $1/1000$ | 0.122 |
| 13 | 2.5069731622049084 | 0 | $1/1000$ | 0.146 |
| 14 | 30.3412706951550927 | 0 | $1/100$ | 0.749 |
| 15 | 30.3902806577818153 | 0 | $1/100$ | 0.756 |
| 16 | 0.7235008085094468 | -0.1131405572686191 | $1/100000$ | 0.212 |
| 17 | 0.7235008085094468 | 0.1131405572686191 | $1/100000$ | 0.212 |

These comparisons are finite sums specified by (12.10)–(12.15).
For a fixed $(u,w)\in[-r_p,r_p]\times[-r_v,r_v]$, the coefficient
of $z$ in (12.14) has modulus at least $L_1$. On $|z|=\epsilon_j$,
the modulus of the constant and degree-at-least-two terms together is
at most $U_0+\sum_{k=2}^{18}U_k\epsilon_j^k<L_1\epsilon_j$.
Rouché's theorem therefore gives exactly one root, counted with
multiplicity, in each open disk for every base in $\mathcal B$.

The rational centers also give
$|c_i-c_j|^2>(\epsilon_i+\epsilon_j)^2$ for every $i\ne j$,
so the disks are pairwise disjoint. Their eighteen roots exhaust the
degree-at-most-eighteen polynomial. Hence its degree is exactly
eighteen, all roots are simple, and no other complex root exists,
uniformly on the entire closed $\mathcal B$.

Disks 0–7 are wholly in the negative real half-plane. Disks 16–17
miss the real axis. For real-centered disks the unique root is real,
because conjugation preserves both the real polynomial and the disk.
Consequently exactly eight positive real carrier roots remain,
one in each disk 8–15. This accounts for every possible $x>0$,
without imposing a source box on the original worlds.

### 12.5. All drift roots and the strict-source filters

For $8\le j\le15$ write
$I_j=[c_j-\epsilon_j,c_j+\epsilon_j]$ for the full real diameter.
At a rational drift endpoint $d_e$, expand

$$
f(c_j+\xi,p_c+u,v_c+w,d_e)
 =\sum_{\alpha,\beta,\gamma}
 t_{\alpha\beta\gamma}(d_e)\xi^\alpha u^\beta w^\gamma,
\qquad
\tau_j(d_e)=
\sum_{\alpha+\beta+\gamma>0}
 |t_{\alpha\beta\gamma}(d_e)|
 \epsilon_j^\alpha r_p^\beta r_v^\gamma.
\tag{12.16}
$$

The interval
$t_{000}(d_e)+[-\tau_j(d_e),\tau_j(d_e)]$
encloses $f$ on $I_j\times\mathcal B$ at that endpoint.
In each row of the table, for each endpoint separately, the printed
sign times $t_{000}(d_e)$ minus $\tau_j(d_e)$ exceeds the printed
integer margin. Thus the signs and margins hold on the whole box,
not just at the center or at a projected root.

| Disk | Branch | Rational drift endpoints $(d_l,d_u)$ | Signs at $(d_l,d_u)$ | Both endpoint absolute margins $>$ | Uniform inverse filter |
| --- | --- | --- | --- | --- | --- |
| 8 | 0 | $(-158.819,-158.618)$ | $+,-$ | 6620 | $b<-9.922$ |
| 8 | 1 | $(-229.274,-229.073)$ | $-,+$ | 5609 | $b<-1.531$ |
| 9 | 0 | $(-238.519,-238.318)$ | $+,-$ | 3162 | $b<-5.346$ |
| 9 | 1 | $(-292.909,-292.708)$ | $-,+$ | 3016 | $b<-2.079$ |
| 10 | 0 | $(585.481,589.482)$ | $+,-$ | 154730 | possible lift retained |
| 10 | 1 | $(393.466,397.467)$ | $-,+$ | 358795 | $r>3.447$ |
| 11 | 0 | $(547.055,551.056)$ | $+,-$ | 336313 | possible lift retained |
| 11 | 1 | $(362.349,366.350)$ | $-,+$ | 619656 | $r>3.915$ |
| 12 | 0 | $(170.268,172.269)$ | $+,-$ | 12668743 | $b<-0.249$ |
| 12 | 1 | $(118.501,118.702)$ | $-,+$ | 260469 | $r>19.198$ |
| 13 | 0 | $(124.805,125.006)$ | $+,-$ | 1190290 | $b<-0.484$ |
| 13 | 1 | $(90.104,90.305)$ | $-,+$ | 2384863 | $r>25.641$ |
| 14 | 0 | $(26.046,26.067)$ | $+,-$ | 19567497167 | $b<-1.679$ |
| 14 | 1 | $(24.447,24.468)$ | $-,+$ | 17615104790 | $b<-0.334$ |
| 15 | 0 | $(26.038,26.059)$ | $+,-$ | 18976836893 | $b<-1.682$ |
| 15 | 1 | $(24.436,24.457)$ | $-,+$ | 17043733106 | $b<-0.335$ |

For every fixed $(x,p,v)\in I_j\times\mathcal B$, the two
disjoint opposite-sign brackets give two distinct drift roots by the
intermediate value theorem. As $f$ has degree at most two in $d$,
these are all its roots and each bracket has exactly one. In
particular the polynomial is genuinely quadratic there: a vanishing
leading coefficient or an identically zero polynomial cannot have
the displayed endpoint signs and two distinct roots. All brackets
avoid $d=0$ and $d=24$. Their exclusion here is a consequence of
these uniform signs, rather than an assumption on original drifts.

Since $x,x+1,x+2$ are positive on all eight diameters, $D>0$.
After the drift exhaustion has supplied $d\ne0$, the necessary
inverse simplifies to

$$
\begin{gathered}
U=-H_0/d,\qquad b=(U-1)/2,\qquad
r=xU-U(24-d)/H_1,\\
b=\frac{-a_0-dD}{2dD},\qquad
r=\frac{-a_0\{xa_1-D(24-d)\}}{dDa_1}.
\end{gathered}
\tag{12.17}
$$

To obtain the filter column, keep the rational numerators in
(12.17). For a proposed rational bound $\mu/\nu$, $\nu>0$,
compare $\nu$ times the numerator minus $\mu$ times its denominator,
using the denominator's sign. Translate this polynomial at the
exact midpoint of
$I_j\times[p_c-r_p,p_c+r_p]\times[v_c-r_v,v_c+r_v]
\times[d_l,d_u]$.
The constant coefficient plus or minus the absolute coefficient tail
on its four radii gives each displayed strict filter inequality.
This procedure retains the cancellations in (12.17).

Every branch with $b<0$ is rejected using only $2dD\ne0$;
no division by $H_1$ is used on such a branch. On every branch
where $r$ is used, its additional divisor is nonzero, as shown by
the following direct outward bounds from (12.8)–(12.9):

| Disk | Branch | Enclosure for $H_1$ on the entire drift box |
| --- | --- | --- |
| 10 | 0 | $[-718.218,-538.444]$ |
| 10 | 1 | $[-1366.875,-1192.863]$ |
| 11 | 0 | $[-625.050,-448.709]$ |
| 11 | 1 | $[-1313.362,-1142.327]$ |
| 12 | 1 | $[-555.886,-545.873]$ |
| 13 | 1 | $[-413.022,-404.704]$ |

In particular $a_1=DH_1<0$ there. The four alternate branches
with $r>1$ violate strictness. The only remaining possibilities
are branch 0 in disk 10 and branch 0 in disk 11.
At any fixed base each disk contains one $x$, each retained bracket
contains one $d$ for that $x$, and the faithful inverse determines
at most one complete world from $(x,d)$. It follows that

$$
|C_{\rm reg}(p,v)|\le2\qquad((p,v)\in\mathcal B).
\tag{12.18}
$$

The necessary equation $\mathcal K=0$ and remaining sufficient
inverse guards can only remove these possibilities. No assertion
that $f=R=0$ alone creates a world is needed. Carrier degree
collapse, repeated carrier roots and drift degree drops have been
excluded by the actual uniform comparisons, without restrictions
on gain degree, gain roots or sampled gains.

### 12.6. Simultaneous actual-base and terminal enclosures on both closed cells

For completeness, the local calculation uses exactly the following
part of IX (25.1)–(25.2):

$$
\begin{gathered}
I_i=[i/5000,(i+1)/5000],\qquad
c_i=(2i+1)/10000,\qquad \nu=(q-c_i)/10^{-4},\\
J_4=Q\cap I_4=[0.000999,0.001],\qquad
J_5=Q\cap I_5=[0.001,0.001001],\\
\widehat z_i(q)=(\widehat X_i,\widehat Y_i,\widehat K_i)
 =10^{-55}\sum_{k=0}^4(a_{iXk},a_{iYk},a_{iKk})\nu^k,\\
\|(X,Y,K_{\rm sec})(q)-\widehat z_i(q)\|_\infty<\rho,
\qquad \rho=10^{-12},\qquad q\in J_i.
\end{gathered}
\tag{12.19}
$$

The six inherited coefficient rows are reproduced to specify the
rational inputs; entries are in ascending powers of $\nu$.

| Cell | Coordinate | $(a_0,a_1,a_2,a_3,a_4)$ |
| --- | --- | --- |
| 4 | $X$ | $(10266304321470101811692411698581629650684861357979633160,1464168059434268517957802728410056361961539722211370,1249749957810952072972171246381867236018905314719,1360060041495343970105334044654147009192630299,1667715131504076334026575440091267909161260)$ |
| 4 | $Y$ | $(469445052819957978196241999967799400899210918868984230,689241728388713650834870768891314603498608970459903,233492581610790092677766532522926169131080883352,90946144816697581586994988618775847722681111,40687472473695203876455940355331944956079)$ |
| 4 | $K_{\rm sec}$ | $(5806412912111385730905709653498462252826459108491456346,3591872992339961756780770307997397109186639407613368,3700252206500061022800076399827262690632311193313,4414622327194285048954439428847275090784301232,5710798424760826632346012928329040298764148)$ |
| 5 | $X$ | $(10269237667496016889079942913593471599228244853143181918,1469183433500169934935055135641038067923535825149648,1257950505356164029114165940781842681115503652307,1373490347210155425951125859610098359618209229,1689919690408973248001225615393120505475461)$ |
| 5 | $Y$ | $(470824470975282436623145928025479471062080870172455502,690176791372122152690871666344753489295520313008065,234039236330706404598955362392854412652001340378,91272382344840755624467433069533976868972127,40872094321925604065005630345813596148986)$ |
| 5 | $K_{\rm sec}$ | $(5813611494513425476989632049643081846476551547510006011,3606727159900913975802291423436094792496219163984445,3726877573720002708197103826644065246554103469308,4460622394478526947617344363792274350958576378,5789429804548091763516887016912979802413911)$ |

Both cells are closed. At $q=0.001$ the uniqueness join in IX
Theorem 26.1 identifies their exact solutions; there is no gap or
choice of a new branch at that seam.

Substitute $q=h^2$ before evaluating the predictors. Their
coordinates become polynomials of degree eight in the common
variable $h$, and the predicted sources are
$(\widehat X_i\pm\widehat K_i h,\widehat Y_i\pm h)$.
Compose (12.5) polynomially. The composed denominators have degree
68 and the numerators for $p,v,m$ have degree 86. Translate these
univariate polynomials at the exact rational

$$
h_c=0.031622776601683793.
\tag{12.20}
$$

Enclose $\sqrt{J_i}-h_c$ by integer square roots. Explicitly,
with $G=10^{75}$ and rational endpoints $q_l,q_u$ of $J_i$,
both $G^2q_l,G^2q_u$ are integers, and

$$
\sqrt{J_i}\subset
\left[
\frac{\lfloor\sqrt{G^2q_l}\rfloor}{G},
\frac{\lfloor\sqrt{G^2q_u}\rfloor+1}{G}
\right].
\tag{12.21}
$$

For $f=p,v,m$ use the centered quotient

$$
\widehat f_i(h)=f_c+
\frac{\widehat N_{f,i}(h)-f_c\widehat D_{s,i}(h)}
     {\widehat D_{s,i}(h)},
\qquad
f_c=p_c,\ v_c,\ -1705,\ -1700,
\tag{12.22}
$$

respectively for $p,v,m_-,m_+$. Both polynomials in this quotient
are translated and evaluated in the same $h-h_c$ interval. In
particular $q$ and $\sqrt q$, and the source coordinates generated
from them, are not replaced by independent parameters.

Correct predictor values by the mean value bound

$$
|f_\pm(X,Y,K_{\rm sec},h)
 -f_\pm(\widehat X_i,\widehat Y_i,\widehat K_i,h)|
\le \rho\sum_{u=X,Y,K_{\rm sec}}\sup_{Z_{i,\pm}}|\partial_u f_\pm|.
\tag{12.23}
$$

Here $f_\pm$ means the original rational response circuit evaluated
at $(X\pm K_{\rm sec}h,Y\pm h)$. The set $Z_{i,\pm}$ uses the
interval hull of each predictor coordinate on $J_i$, enlarged by
$[-\rho,\rho]$, and the same $h\in\sqrt{J_i}$. It contains
every segment from the predictor to the exact zero at fixed $h$.
The source denominators exclude zero on these hulls.

Differentiate (12.5) and its quotients with the ordinary product and
quotient rules, and evaluate the resulting expressions on these
hulls. Strict integer upper bounds for the gradient sums in
(12.23) are

| Response and source | Cell 4 | Cell 5 |
| --- | --- | --- |
| $p_+$ | 10037371 | 10038834 |
| $v_+$ | 23309144 | 23312710 |
| $m_-$ | 10437466 | 10431616 |
| $m_+$ | 55321673 | 55330519 |

All polynomial constructions and translations in (12.10)–(12.16)
and (12.19)–(12.22) use exact rational coefficients. For the
univariate evaluations and derivative enclosures, interval addition,
multiplication and nonzero-denominator reciprocal enclose exact
endpoints, rounded outwards on $10^{-75}\mathbb Z$:

$$
[l,u]\longmapsto
\left[10^{-75}\lfloor10^{75}l\rfloor,\
      10^{-75}\lceil10^{75}u\rceil\right].
\tag{12.24}
$$

Univariate products are formed before evaluation, translation uses
the binomial identity, and interval Horner evaluation encloses their
values. Applying (12.23) after this common-parameter evaluation
gives the following simultaneous actual-base enclosures:

| Parameter cell | Actual $p(q)$ | Actual $v(q)$ |
| --- | --- | --- |
| $J_4$ | $[-497.89083841,-497.85729509]$ | $[-953.65259033,-953.59085773]$ |
| $J_5$ | $[-497.85731518,-497.82378226]$ | $[-953.59090437,-953.52919087]$ |

The exact secant equalities identify these plus-source readings with
the minus-source readings at the same $q$. Comparing the four
rational endpoints with (12.4) proves

$$
(p(q),v(q))\in\operatorname{int}\mathcal B,\qquad p(q)\ne24
\qquad(q\in Q).
\tag{12.25}
$$

This is simultaneous inclusion of both acquired readings from the
same exact worlds, rather than a fifth-reading match.

The regularity bounds, including predictor error, are

| Cell | Actual $D_{s,-}$ | Actual $D_{s,+}$ |
| --- | --- | --- |
| 4 | $[0.010737202348,0.010738918157]$ | $[0.005493944178,0.005495257262]$ |
| 5 | $[0.010738918093,0.010740633229]$ | $[0.005492631700,0.005493944253]$ |

Both denominators are positive and exceed $0.0038$. The
predictor-only plus denominators lie strictly between $0.0054926$
and $0.0054953$. Direct interval Horner evaluation of (12.19),
enlargement by $\rho$, and then (12.7) give the explicit strict-source
guards

| Cell | Source | $t$ enclosure | $b$ enclosure | $r=tb$ enclosure |
| --- | --- | --- | --- | --- |
| 4 | $-$ | $[1.008402647,1.008413417]$ | $[0.015389986,0.015406492]$ | $[0.015519303,0.015536113]$ |
| 4 | $+$ | $[1.045139064,1.045149835]$ | $[0.078619724,0.078636230]$ | $[0.082168545,0.082186643]$ |
| 5 | $-$ | $[1.008394814,1.008405583]$ | $[0.015374868,0.015391367]$ | $[0.015503937,0.015520740]$ |
| 5 | $+$ | $[1.045149832,1.045160601]$ | $[0.078636229,0.078652727]$ | $[0.082186641,0.082204732]$ |

Thus $t_\pm>0$, $b_\pm>0$ and $0<r_\pm<1$ hold throughout both
closed cells, including the seam. The lift (12.6) uses positive
$D_{s,\pm}$ and constant interpolation divisors; its $g$ is the
single whole nonzero polynomial already identified. These bounds
also place both selected sources in IX's $\mathscr R$, without
assuming this for an arbitrary companion.

The same polynomial composition, centered evaluation and error
correction gives the terminal bounds

| Parameter cell | Actual $m(W_-(q))$ | Actual $m(W_+(q))$ |
| --- | --- | --- |
| $J_4$ | $[-1705.04831638,-1704.94134514]$ | $[-1700.57340993,-1700.46388073]$ |
| $J_5$ | $[-1704.94138475,-1704.83443702]$ | $[-1700.46421316,-1700.35474402]$ |

In particular the union of the two closed cells yields

$$
\begin{gathered}
-1705.04831638\le m(W_-(q))\le-1704.83443702,\\
-1700.57340993\le m(W_+(q))\le-1700.35474402,\\
m(W_+(q))-m(W_-(q))
 \ge4.26102709>4.26102243809>213/50
\qquad(q\in Q).
\end{gathered}
\tag{12.26}
$$

Each terminal in this comparison belongs to its original complete
world at the same actual full base $(p(q),v(q))$.

### 12.7. Exact regular inventory and the independent-pair boundary

**Theorem 12.1 (All regular companions at these actual bases).**
On the rectangle (12.4), the original regular child has at most
two worlds. On its actual continued bases for every $q\in Q$,

$$
C_{\rm reg}(p(q),v(q))=\{W_-(q),W_+(q)\},\qquad
a(W_-(q))=a(W_+(q)),
\qquad
m(W_+(q))-m(W_-(q))>213/50.
\tag{12.27}
$$

Consequently there is no independently chosen distinct equal-$M$
pair whose two endpoints are regular in that same entire child.

Proof. The necessary carrier identity (12.13) places every regular
world above a root of $R$. The uniform disjoint disks exhaust
those roots, including all degree possibilities. The two strict-sign
drift brackets at each positive projection exhaust its drift roots.
The inverse filters and faithful uniqueness give (12.18), on the
entire rectangle and for every original strict source.

For each $q\in Q$, (12.25) places the exact full base in that
rectangle. The inherited exact continuation and the explicit
strictness and denominator bounds above supply two distinct
regular worlds there. They therefore occupy the bound of two,
proving the inventory equality. Their equal-$J$ reading is the
secant equality, and (12.26) supplies their strict $M$ separation.
Any two regular endpoints chosen independently in this child must
be these worlds if they are distinct, so cannot have equal $M$.
This proves the final assertion. ∎

In particular the conclusion excludes regular equal-$M$ alternatives
with one or both endpoints outside IX's source class, including a
mixed interior/exterior regular pair or two exterior regular endpoints.
It follows by an inventory of all original regular worlds at the
actual full base; no uniform exterior sign implication, source-class
localization assumption, cap or shared drift is used. The source
boxes in the inverse calculation arise from exhaustive carrier and
drift accounting.

The evaluated addition is the whole-rectangle bound (12.18),
the simultaneous actual-base enclosures on both closed cells, and
their exact all-regular-companion consequence (12.27) with the
quantitative terminal gap. The original model and traces, regular
whole-gain circuit, normalized carrier, exceptional-point necessity,
faithful inverse, exact first-$J$ continuation and corner are the
attributed ordinary results of IX specified above. The qualitative
$M$ order of the two selected endpoints is already IX Theorem 28.1;
the present terminal table supplies its stated uniform numerical
margin. Polynomial root counting, distinct-node interpolation,
Rouché's theorem and the mean value bound are the ordinary tools
used with these interfaces.

This theorem leaves $D_s=0$ worlds unresolved, including at every
base in (12.27). It also leaves unresolved every equal-$M$ pair
with at least one such singular endpoint. Regular incidence on the
continued branch outside $Q$, other $J$ branches and all other
entire children remain outside this bounded result. In particular
it neither proves nor refutes (12.3). The quantifiers there still
range over all original worlds with their arbitrary own fixed
drifts, lower gain degrees, zero samples and repeated gain roots.
There is no whole-child global resolution in the regular inventory.

## 追加锚（本行以下为增补区）

## 13. Singular exclusion on the negative-J continuation and the entire two-world child on Q

### 13.1. Original worlds and the ordinary mathematical inputs

Retain exactly the worlds and terminal alternatives of (12.1)–(12.3):

$$
\begin{gathered}
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\\
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\\
(E_1,\ldots,E_6)=(J,M,J,M,M,M),\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\\
y_i=d+g(i)\operatorname{tr}(Q_iP),\qquad
(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v).
\end{gathered}
\tag{13.1}
$$

Here $J,M$ are the matrices in (12.1). The entire $C(p,v)$ consists
of all such complete worlds. Each world has its own arbitrary fixed
drift and its one whole gain polynomial. At the original clock seven,
$a(W)$ and $m(W)$ are the alternative readings in (12.2). Lower gain
degrees, zero gain samples, repeated roots, zero drift and unbounded
positive offdiagonals remain in the domain. No source box, common
drift, reset, copy, shifted clock or new port is imposed.

The ordinary inputs have the following precise scope. Write O for
[FIB common-parent geometry and two exact mixed children](https://github.com/the-omega-institute/trureturing/blob/91bbfd39908a68f6dd967bf645799dd03942130b/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
S for [FIB entire singular-response children and terminal-M injectivity](https://github.com/the-omega-institute/trureturing/blob/91bbfd39908a68f6dd967bf645799dd03942130b/docs/develop/theory/FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md),
and F for [FIB all-response finite-fibre geometry](https://github.com/the-omega-institute/trureturing/blob/91bbfd39908a68f6dd967bf645799dd03942130b/docs/develop/theory/FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
at the indicated revision. Write IX for
[FIB strict-real joint incidence: the trace-corrected complex M projection curve](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md),
specifically its completed Sections 24–28 and the coefficient rows of
(25.2). Section 12 of this volume is used with its ordinary proofs.

| Ordinary input | Exact correspondence and retained condition |
| --- | --- |
| O, Theorem 2.1, Lemma 12.2, Theorems 12.3 and 29.2 | O's $\beta=1/8$, $a=24/5$, $\epsilon=d-24$; its fifth response is this $p$, and its sixth-M response is this $v$. The singular classification and unique whole-gain lift hold for every real $p$. |
| S, Definition 2.3, Definition 3.2 and Lemma 3.3 | The two algebraic root brackets and cubic representative of the actual singular sixth-M response; the response identity holds for every real $p$. No theorem restricted to S's particular $p_J$ is transferred. |
| F, Definition 30.1 and Lemma 30.2 | The identical entire child has $x=n/U$ and $H=Ug$, with the same $p,v,d$. Its faithful whole-world reconstruction holds for all real $p\ne24$, including negative $p$, without assuming a nonzero drift. These coordinates do not restrict the original sources. |
| IX, (24.2)–(24.8), (25.1)–(25.2), (25.10)–(25.13), Theorems 26.1, 27.1 and 28.1 | The same exact continued secant zero, the full coordinate radius $10^{-12}$, uniqueness joins, exact germ attachment, strict-source event and whole-gain lifts. |
| This volume, Theorem 12.1 and (12.25)–(12.27) | The entire regular inventory and terminal gap only on its closed $Q=[999/10^6,1001/10^6]$. |

The conclusions below are ordinary mathematical consequences of these
interfaces with their stated premises. The inherited classification,
continuation and regular inventory are reused. Theorem 13.1 establishes the evaluated separation
from both singular-response lines, and Theorem 13.2 gives its entire-child
consequence.

### 13.2. The zero-safe singular alternatives and their affine responses

Put

$$
\begin{gathered}
j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad e=d-24,\\
B_{\rm coef}=6/T-2/U=2(2+5b)/(TU)>0.
\end{gathered}
\tag{13.2}
$$

O's full-parent equation and whole-world converse give

$$
e\Lambda+\frac{24}{5}(b-1/8)B_{\rm coef}=0.
\tag{13.3}
$$

For completeness, the zero-safe fifth-response lift uses

$$
\begin{gathered}
V=U+n,\qquad A_5=1+V(4-15/j+20/T-10/n),\\
K_5=96(b-1/8)V/T,\qquad Z=\Lambda^2+A_5^2>0,\\
e=\frac{-(24/5)(b-1/8)B_{\rm coef}\Lambda
             +A_5(p-24-K_5)}{Z}.
\end{gathered}
\tag{13.4}
$$

Its whole $g$ is the degree-at-most-three interpolant at the fixed
nodes $0,1,2,3$ with values

$$
(-24-e,\ -e/j,\ (27/5-e)/T,\ -e/n),\qquad d=24+e.
\tag{13.5}
$$

The condition $Z>0$ is O, Lemma 12.2 on the full strict domain.
The gain cannot vanish identically, since readings zero and $24$
would then coincide. These are complete-world statements, rather than
an equation for a sampled or substituted gain.

If $\Lambda=0$, positivity in (13.3) forces $b=1/8$. At that width,
O's identity is

$$
\Lambda=\frac{\Phi(r)}{960jn},\qquad
\Phi(t)=438272t^4-931328t^3+540800t^2-50728t-853.
\tag{13.6}
$$

O, Theorem 4.2 proves that exactly two roots are strict. Denote them
by $\varrho_-,\varrho_+$. S's finer brackets are

$$
\begin{aligned}
J_-&=[134815875067638653367017716061081265110899687,
       134815875067638653367017716061081265110899688]/10^{45},\\
J_+&=[902449681772056265377872651296542856186276499,
       902449681772056265377872651296542856186276500]/10^{45}.
\end{aligned}
\tag{13.7}
$$

The endpoint signs of $\Phi$ are respectively $(-,+)$ and $(+,-)$.
The designated roots, rather than the centers of these intervals,
are used throughout.

To display the whole-gain singular identity, define

$$
\begin{aligned}
\mathcal D={}&1731744020342106665,\\
A_s(t)={}&13656112734222647296t^3-33583101098863014400t^2\\
&+20502976421172725312t-3401342974535580372,\\
B_s(t)={}&-327746705621343535104t^3+916826043674607172160t^2\\
&-616757003572777087368t+31411654798932835643,\\
s_\sigma(p)={}&\alpha_\sigma p+\beta_\sigma
=-\frac{3\{pA_s(\varrho_\sigma)+B_s(\varrho_\sigma)\}}{\mathcal D}.
\end{aligned}
\tag{13.8}
$$

Here is an exact verification of the response identity, retaining the
normalization of the original whole gain. At width $1/8$ put

$$
\begin{gathered}
j(t)=1/8+8t(1-t),\quad n(t)=j(t)+t,\\
F_5=jn+(n+5/4)\{(196/9)jn-15n-10j\},\\
F_6=jn+(n+5/2)\{50jn-36n-20j\},\qquad F_0=84+24n.
\end{gathered}
\tag{13.9}
$$

At a designated root, $F_5=jnA_5\ne0$ by $Z>0$ and $\Lambda=0$.
The inherited whole-world response is
$F_0+(p-24)F_6/F_5$. Reduction by

$$
t^4\equiv(931328t^3-540800t^2+50728t+853)/438272\pmod\Phi
\tag{13.10}
$$

gives both exact remainder vectors, in ascending powers $1,t,t^2,t^3$:

$$
\begin{aligned}
\operatorname{rem}(\mathcal D F_6+3A_sF_5,\Phi)&=(0,0,0,0),\\
\operatorname{rem}(\mathcal D(F_0F_5-24F_6)+3B_sF_5,\Phi)&=(0,0,0,0).
\end{aligned}
\tag{13.11}
$$

They prove (13.8) for every real $p$. In particular the classification
has no positive-$p$ restriction: every singular world in any $C(p,v)$
must satisfy $v=s_-(p)$ or $v=s_+(p)$. Conversely O's unique lift
supplies each singular fifth-response world. No division by $\Lambda$,
drift, a gain sample, leading gain coefficient or root difference occurs.
The divisions in this argument use positive source traces, the proved
positive $Z$, and the proved nonzero $F_5$.

Exact rational Horner evaluation of $-3A_s/\mathcal D$ and
$-3B_s/\mathcal D$ on (13.7) gives the following enclosures.
All displayed terminating decimals in this section denote exact rationals.

| $\sigma$ | Enclosure $\mathcal A_\sigma$ for $\alpha_\sigma$ | Enclosure $\mathcal B_\sigma$ for $\beta_\sigma$ |
| --- | --- | --- |
| $-$ | $[2.10332127276981,2.10332127276982]$ | $[62.15085699544574,62.15085699544575]$ |
| $+$ | $[3.83234815291643,3.83234815291644]$ | $[33.58501339171649,33.58501339171650]$ |

For example Horner evaluation means starting from the leading integer
coefficient, multiplying its interval by $J_\sigma$, and adding the
next integer, through the constant term, before multiplying by the
negative rational $-3/\mathcal D$. Thus these are algebraic-root
interval enclosures, with no root-center substitution.

### 13.3. Common-parameter bounds on all twelve closed cells

Use IX's exact analytic continuation
$x(q)=(X,Y,K_{\rm sec})(q)$, which is the continuation of its attached
first equal-$J$ germ. Retain all thirty-six predictor rows of IX
(25.2), with their ascending coefficient order, by the definition

$$
\begin{gathered}
I_i=[i/5000,(i+1)/5000],\quad c_i=(2i+1)/10000,\quad w=1/10000,\\
\widehat x_{iu}(q)=10^{-55}\sum_{k=0}^4a_{iuk}\nu^k,\quad
\nu=(q-c_i)/w,\quad u=X,Y,K_{\rm sec},\\
\|x(q)-\widehat x_i(q)\|_\infty<\rho=10^{-12},\qquad
q\in I_i,\quad0\le i\le11.
\end{gathered}
\tag{13.12}
$$

These are the named coefficient rows of that ordinary source, not a
new choice of predictors. At the same parameter put

$$
h=\sqrt q,\qquad t_+=X+K_{\rm sec}h,\qquad b_+=Y+h.
\tag{13.13}
$$

For clarity the polynomial circuit needed for the two readings is

$$
\begin{gathered}
r=tb,\quad j=t+b(1-t^2),\quad n=j+tb,\quad T=1+b,\quad U=1+2b,\\
D_0=5\{(b^2+8b+4)jn-2TU(j+n)\},\quad S_0=(8b-1)(2+5b),\\
C_0=-24D_0+3S_0jn,\quad C_1=3S_0n,\\
C_2=3(49b+34)jn-54U(j+n),\quad C_3=3S_0j,\\
B_5=-4C_0+15C_1-20C_2+10C_3,\\
B_6=-10C_0+36C_1-45C_2+20C_3,\\
N_p=-C_0+(U+n)B_5,\qquad N_v=-C_0+(2U+n)B_6.
\end{gathered}
\tag{13.14}
$$

This is IX (24.2), equivalently (12.5) with $D_0=D_s$.
On the exact secant zero, its plus readings are the common $p(q),v(q)$.
To retain their dependence, bound the single numerator

$$
R_\sigma=N_v-\alpha_\sigma N_p-\beta_\sigma D_0,\qquad
F_\sigma=R_\sigma/D_0=v(q)-s_\sigma(p(q)).
\tag{13.15}
$$

The following finite coefficient bounds specify uniform inequalities
on each cell. They also give a rational reproduction of the numerical
bounds without replacing the cell by point values.

Set $G_h=10^{40}$ and define integers

$$
\ell_i=\left\lfloor\sqrt{G_h^2i/5000}\right\rfloor,\qquad
u_i=\left\lceil\sqrt{G_h^2(i+1)/5000}\right\rceil.
\tag{13.16}
$$

The radicands are integers; floor square roots are characterized by
$k^2\le N<(k+1)^2$, and the ceiling equals $k$ only for a square.
Put $m_i=(\ell_i+u_i)/(2G_h)$, $d_i=(u_i-\ell_i)/(2G_h)$ and
$h=m_i+d_i z$, $|z|\le1$. This contains every $h=\sqrt q$ for
$q\in I_i$. In every predictor substitute $q=h^2$ before composing
$t=\widehat X_i(h^2)+h\widehat K_i(h^2)$ and
$b=\widehat Y_i(h^2)+h$. All resulting circuit entries are
univariate polynomials in this same $z$.

For a fully rational coefficient convention set $G=10^{80}$.
Enclose a coefficient or interval by

$$
\mathsf E([l,u])=[\lfloor Gl\rfloor/G,\ \lceil Gu\rceil/G].
\tag{13.17}
$$

Interval addition uses endpoint addition; subtraction uses
$[l,u]-[a,b]=[l-b,u-a]$; multiplication uses the minimum and maximum
of the four endpoint products. Apply $\mathsf E$ after every operation.
Construct predictor polynomials by descending Horner evaluation of
the five inherited coefficients. Polynomial products use coefficient
convolution, summing in increasing indices. Follow the parentheses
of (13.14), with each displayed unparenthesized sum added from left
to right. Complete these polynomial products before taking ranges.
For $V(z)=\sum_k V_kz^k$ use

$$
\mathcal C(V)=V_0+[-s,s],\qquad
s=\sum_{k\ge1}\max(|\inf V_k|,|\sup V_k|).
\tag{13.18}
$$

This encloses every value on $[-1,1]$ by the triangle inequality.
Form $\widehat D_i,\widehat N_{p,i},\widehat N_{v,i}$ this way.
For the singular coefficients use the full intervals
$\mathcal A_\sigma,\mathcal B_\sigma$ displayed above, and form

$$
\widehat R_{i\sigma}=
\widehat N_{v,i}-\mathcal A_\sigma\widehat N_{p,i}
                         -\mathcal B_\sigma\widehat D_i
\tag{13.19}
$$

as an interval-coefficient polynomial before applying $\mathcal C$.
Coefficient rounding and the algebraic-root uncertainties are thereby
included in the central range. In particular separate marginal
$p,v$ intervals are not subtracted to infer the sign.

It remains to include the entire radius-$\rho$ tube, rather than only
the rational predictors. Use the mean-value gradient guard of IX
(25.12). IX (25.10) and $0\le h<1/20$ place every plus-source segment
between the predictor and the exact zero in
$1\le t\le11/10$, $0\le b\le1/10$.
Indeed its full tube has $1.025<X<1.029$, $0.0463<Y<0.048$ and
$0.577<K_{\rm sec}<0.587$; these imply the stated larger rectangle.
For any circuit polynomial $L(t,b)=\sum_{a,k}c_{ak}t^ab^k$, put

$$
\Gamma(L)=\frac{21}{20}\sum_{a\ge1,k\ge0}
 a|c_{ak}|(11/10)^{a-1}(1/10)^k
 +\sum_{a\ge0,k\ge1}k|c_{ak}|(11/10)^a(1/10)^{k-1}.
\tag{13.20}
$$

At fixed $h$, the three partials are $L_t,L_b,hL_t$ in
$X,Y,K_{\rm sec}$. Thus (13.20) bounds their absolute sum on the
whole segment. Expansion of the displayed two-variable circuit gives

| Polynomial | Exact $\Gamma(L)$ | Strict integer upper guard |
| --- | --- | --- |
| $D_0$ | $7667254617/20000000$ | $384$ |
| $N_p$ | $13033889043873/1250000000$ | $10428$ |
| $N_v$ | $97107509878563/2000000000$ | $48554$ |

This is a monomial derivative bound on a rectangle, not a derivative
sample. With $a_\sigma^+=\sup\mathcal A_\sigma$ and
$b_\sigma^+=\sup\mathcal B_\sigma$, set

$$
\begin{gathered}
E_D=384\rho,\qquad
E_\sigma=\rho(48554+10428a_\sigma^++384b_\sigma^+),\\
D_i^- =\inf\mathcal C(\widehat D_i)-E_D,\quad
D_i^+ =\sup\mathcal C(\widehat D_i)+E_D,\\
R_{i\sigma}^- =\inf\mathcal C(\widehat R_{i\sigma})-E_\sigma.
\end{gathered}
\tag{13.21}
$$

These errors use the full $10^{-12}$ coordinate radius. The coefficient
intervals already contain the root errors; no additional assumption
that a displayed coefficient equals its center is made. For size,
$E_-<10^{-7}$ and $E_+<11\cdot10^{-8}$.
When $D_i^->0$ and $R_{i\sigma}^->0$, ordinary positive division gives
$F_\sigma\ge R_{i\sigma}^-/D_i^+$. Applying (13.16)–(13.21) gives
all the following rational inequalities. The denominator intervals
are enlarged outwards and the separation lower bounds are rounded
downwards; the latter apply after both tube and root errors.

| Cell $i$ | Full-tube $D_0$ enclosure | Lower bound for $F_-$ | Lower bound for $F_+$ |
| --- | --- | --- | --- |
| 0 | $[0.006830389236,0.007894405816]$ | $33.603064$ | $846.533715$ |
| 1 | $[0.006405716396,0.006842834999]$ | $34.547745$ | $900.877126$ |
| 2 | $[0.006063603991,0.006408184817]$ | $33.144646$ | $897.169944$ |
| 3 | $[0.005765858050,0.006066148405]$ | $31.553498$ | $888.052705$ |
| 4 | $[0.005493943831,0.005768394266]$ | $29.916223$ | $876.977204$ |
| 5 | $[0.005238496633,0.005496449047]$ | $28.276043$ | $864.998602$ |
| 6 | $[0.004994030209,0.005240965566]$ | $26.646443$ | $852.554045$ |
| 7 | $[0.004757015802,0.004996463407]$ | $25.039763$ | $839.852073$ |
| 8 | $[0.004525031229,0.004759415804]$ | $23.461394$ | $826.997178$ |
| 9 | $[0.004296331767,0.004527401159]$ | $21.913216$ | $814.038726$ |
| 10 | $[0.004069612802,0.004298674782]$ | $20.396077$ | $800.992612$ |
| 11 | $[0.003843869102,0.004071931883]$ | $18.910227$ | $787.851260$ |

As one explicit comparison, (13.18) in cell 11 gives central numerator
lower bounds $0.077001253663$ and $3.208076768816$ for the minus
and plus alternatives. Subtracting their respective exact errors in
(13.21), then dividing by $0.004071931883$, still exceeds
$18.910227$ and $787.851260$, respectively. All twelve rows use the
same coefficient construction and inequalities. They are bounds on
whole closed cells, so their positive minima do not require an
interpolation or sample-to-uniform inference.

The cells cover exactly $[0,3/1250]$. The eleven adjacent predictor
seam distances, computed from the named arrays at $\nu=1,-1$, are
at most $2\cdot10^{-55}<\rho$. IX, Theorem 26.1 identifies the zeros
in the overlapping uniqueness tubes and identifies the zero at $q=0$
with the exact germ. Thus both sides of every closed-cell seam concern
the same analytic continuation.

### 13.4. Singular exclusion and the complete local child

**Theorem 13.1 (No singular alternative anywhere on the selected arc).**
For the common-response functions of IX's continued zero,

$$
v(q)-s_\sigma(p(q))>0\qquad
(0\le q\le3/1250,\quad\sigma\in\{-,+\}).
\tag{13.22}
$$

Consequently every actual original world in $C(p(q),v(q))$ is
nonsingular for $0<q<q_*$, where

$$
0.002295452521112227202566167277417
<q_*<0.002295452521112227202566167277419.
\tag{13.23}
$$

Proof. The twelve rows of (13.21)'s evaluation give positive
$D_i^-$ and positive lower bounds for both $R_{i\sigma}^-/D_i^+$.
They cover the closed interval and the exact tube, proving (13.22).
For an actual world with $\Lambda=0$, (13.3)–(13.11) force one of
$v(q)=s_-(p(q))$ or $v(q)=s_+(p(q))$, contradicting (13.22).
IX gives $p(q)<0$ on this continuation, so in particular $p(q)\ne24$.
The classification used here is the full strict-source classification,
including arbitrary own drift and every permitted gain stratum. ∎

The values in (13.22) at zero and at $q_*$ are values of the common
analytic response functions. They supply no strict distinct-pair
witness at either endpoint. At $q=0$ the two continued sources
coalesce; at $q=q_*$ the minus source has $b_-=r_-=0$ and is outside
the original strict domain. On $0<q<q_*$, IX, Theorem 28.1 supplies
two distinct complete worlds $W_-(q),W_+(q)$ with equal $p,v,a$;
their gains and drifts are their respective original whole-world lifts.

For comparison with the word “regular” in Section 12, direct
multiplication of (13.2) gives, for every original strict source,

$$
D_s=D_0=\frac52TUjn\Lambda.
\tag{13.24}
$$

All four factors $T,U,j,n$ are positive. Hence nonsingularity is
exactly $D_s\ne0$, not a different exclusion of worlds.

**Theorem 13.2 (The entire original child on Q).** For every
$q\in Q=[999/10^6,1001/10^6]$,

$$
\begin{gathered}
C(p(q),v(q))=\{W_-(q),W_+(q)\},\\
W_-(q)\ne W_+(q),\qquad a(W_-(q))=a(W_+(q)),\\
m(W_+(q))-m(W_-(q))>213/50.
\end{gathered}
\tag{13.25}
$$

In particular there is no independently chosen distinct equal-$M$
pair in that entire child, and the independent-pair predicate (12.3)
fails at every one of these actual full bases.

Proof. The exact rational comparisons
$0<999/10^6\le1001/10^6<0.0022954525<q_*$ put the whole closed
$Q$ in the strict pair interval. Theorem 13.1 and (13.24) identify
the entire child with its regular subset. Theorem 12.1, applied
only on this $Q$, identifies that regular subset with the two
continued worlds and gives the equal-$J$ reading and the strict
terminal gap. Any two independently chosen distinct worlds of this
child must therefore be these two worlds, whose $M$ readings differ.
This excludes every proposed equal-$M$ pair, irrespective of its
relationship to the selected $J$ pair. ∎

This conclusion uses the entire original $C(p,v)$, including companions
outside any selected source class. Its scope outside $Q$ is exactly
the singular exclusion (13.22) along the selected continuation; the
regular inventory there is unresolved. Other source branches and
other full bases are unresolved. The original global target (12.3)
continues to ask for one entire $C(p,v)$, $p\ne24$, containing
independently selected within-pair distinct equal-$J$ and equal-$M$
pairs. Their overlap or disjointness and their unrelated common
terminal values remain allowed. No global existence or nonexistence
conclusion follows from (13.25).

## 追加锚（本行以下为增补区）

## 14. A uniform negative-response strip and the entire first negative-J child

### 14.1. Worlds, strip coordinates and the reused interfaces

Retain the entire original world space (13.1), the acquired word
$J,M,J,M,M,M$, and the readings $(0,24,147/5,24,18,p,v)$ at the
original clocks zero through six. Thus $P=P(r,b)$ has $0<r<1$,
$b>0$, rank one and trace one; every world has its own arbitrary
real constant $d$ and one nonzero real polynomial $g$ of degree at
most three. The alternative $m(W)$ is the immediately read atomic
$M$ at clock seven, as in (12.2). Write

$$
\begin{gathered}
w=v-\frac{46}{25}p,\\
\mathcal S=\left\{(p,v):-534\le p\le-457,\quad
 -\frac{1877}{50}\le w\le-\frac{3749}{100}\right\}.
\end{gathered}
\tag{14.1}
$$

Here $C(p,v)$ still means all complete original worlds at that base,
and $C_{\rm reg}(p,v)$ means exactly those with $D_s\ne0$ in
(12.5). The letter $\mathcal S$ distinguishes this strip from the
smaller rectangle $\mathcal B$ in (12.4). In particular no bounded
source class is part of the definition of $C$ or $C_{\rm reg}$.

The necessary carrier $R$, with its exact polynomial quotients formed
before specialization, is precisely (12.10)–(12.12). Every regular
world satisfies $R(x,p,v)=0$ at $x=n/U>0$ by the source identity
(12.13), even when $A=0$ or $F_0=0$. The inverse (12.8)–(12.9),
equivalently all-response geometry, Definition 30.1 and Lemma 30.2,
is injective on complete worlds in $(x,d)$ for every $p\ne24$.
Its guards are $d\ne24$, $H_1\ne0$, $\chi>0$, $U>1$ and the
original strict source inequalities; it does not assume $d\ne0$.
Every base in (14.1) has $p\ne24$.

For the selected pair, $q$, $(X,Y,K_{\rm sec})(q)$ and $W_\pm(q)$
mean exactly IX (24.6), (25.2) and Theorems 26.1–28.1. Their whole
polynomial and own constant drift are the lifts (12.6), with the
same original clock. IX Theorem 28.1 supplies their existence,
distinction, equal $J$ responses and unequal $M$ responses for every
$0<q<q_*$. Theorem 13.1 and (13.24) exclude every singular companion
on precisely this strict interval. These inputs do not by themselves
count the regular companions outside the smaller $Q$ of Theorem 13.2.

### 14.2. Closed-box coefficient bounds for the carrier

The following notation specifies the finite rational inequalities used
below. If $L(z)=\sum_\alpha c_\alpha z^\alpha$ is a polynomial on
$Z=\prod_{j=1}^s[l_j,u_j]$, let $n_j=\deg_{z_j}L$ and, for
$0\le t_j\le n_j$, set

$$
\begin{aligned}
\beta_t(L;Z)
 &=\sum_\alpha c_\alpha\prod_{j=1}^s
 \left\{\sum_{k=0}^{\min(\alpha_j,t_j)}
 \binom{\alpha_j}{k}l_j^{\alpha_j-k}(u_j-l_j)^k
 \frac{\binom{t_j}{k}}{\binom{n_j}{k}}\right\},\\
\mathfrak b_Z(L)&=\min_{0\le t_j\le n_j}\beta_t(L;Z),\qquad
\mathfrak B_Z(L)=\max_{0\le t_j\le n_j}\beta_t(L;Z).
\end{aligned}
\tag{14.2}
$$

Include every index in this rectangular tensor, including coefficients
that are zero. Constant polynomials have degree zero in every
variable. Expanding $z_j=l_j+(u_j-l_j)y_j$ and then using

$$
y^k=\sum_{t=k}^n\frac{\binom tk}{\binom nk}
                 \binom nt y^t(1-y)^{n-t}
\quad(0\le k\le n)
\tag{14.3}
$$

gives the Bernstein expansion with coefficients (14.2).
Its basis functions are nonnegative and sum to one on the entire
closed box, so $\mathfrak b_Z(L)\le L\le\mathfrak B_Z(L)$ there.
This is the classical convex-hull bound; see Mourrain, Rouillier and
Roy, *Bernstein's basis and real root isolation*, INRIA RR-5149,
[Proposition 2.8](https://inria.hal.science/inria-00071434/document).
The tensor statement follows by the same partition of unity in each
coordinate. No generic specialization or square-free assumption is
used in this bound.

Put

$$
\widetilde R(x,p,w)=R\left(x,p,\frac{46}{25}p+w\right),\qquad
Z_{pw}=[-534,-457]\times[-1877/50,-3749/100].
\tag{14.4}
$$

Applying the exact sums (14.2) to (12.10)–(12.12) gives the following
strict rational inequalities. The degree vector for each row is
$(18,6,6)$, so each comparison includes $19\cdot7\cdot7=931$
coefficients.

| Closed $x$ interval $I$ | Sign $\epsilon$ | $\mathfrak b_{I\times Z_{pw}}(\epsilon\widetilde R)>$ |
| --- | --- | --- |
| $[0,343/1000]$ | $+1$ | $6\cdot10^{23}$ |
| $[344/1000,407/1000]$ | $-1$ | $10^{24}$ |
| $[409/1000,24/25]$ | $+1$ | $10^{24}$ |
| $[501/500,1917/1000]$ | $+1$ | $10^{24}$ |
| $[1927/1000,2493/1000]$ | $-1$ | $2\cdot10^{28}$ |
| $[1259/500,27]$ | $+1$ | $3\cdot10^{29}$ |

The two polynomial divisions in (12.12) have zero remainder; the
resulting carrier has 512 nonzero monomials in $(x,p,v)$ and degree
vector $(18,6,6)$. These facts and (14.2) specify the comparisons
without selecting any roots. The attempted translated-tail certificate
is not used: the finite data above do not establish a uniform sign on
the unbounded tail. We therefore use the source equation itself for
$x\ge34$; the exact exclusion is proved in Section 14.3 below. No
assertion about the sign of $R$ on that tail is needed. Finally,

$$
\mathfrak b_{[24/25,501/500]\times Z_{pw}}
                 (\partial_x^2\widetilde R)>264\cdot10^{26}.
\tag{14.6}
$$

Here the degree vector is $(16,6,6)$ and all 833 tensor coefficients
are included. Equations (14.2), (14.4), (14.6) and the displayed
polynomial definitions are finite rational expressions for all the
bounds; in particular (14.6) holds at the strip faces as well.

For an actual source with $0<x\le34$, the finite comparisons above
place every possible carrier root in the union

$$
\begin{aligned}
\mathcal I={}&[343/1000,344/1000]\cup[407/1000,409/1000]\cup I_c\\
 &\cup[1917/1000,1927/1000]\cup[2493/1000,1259/500]
       \cup[27,34],\\
I_c={}&[24/25,501/500].
\end{aligned}
\tag{14.7}
$$

The closed complementary intervals include every boundary; allowing
those boundary points again in (14.7) only enlarges the possible root
set. Strict positivity of the second derivative on
$I_c$ implies at most two distinct roots there: three distinct roots
would, by two applications of Rolle's theorem, force a zero of the
second derivative. This argument includes repeated-root
specializations and does not require a root to lift to a world.

### 14.3. A necessary quadratic with strict-source guards

For an actual world at a base in $\mathcal S$, define the following
rational functions of the same $x,p,v$:

$$
\begin{gathered}
\gamma=294/5,\quad
\tau=20/x-45+36/(x+1)-10/(x+2),\\
\tau_2=4/x-6+4/(x+1)-1/(x+2),\qquad
s=16/x+1/(x+2),\\
c_0=480/x-810+36p/(x+1)-10v/(x+2),\\
c_2=96/x-108+4p/(x+1)-v/(x+2),\qquad
e=c_0-9c_2=162-384/x-v/(x+2).
\end{gathered}
\tag{14.8}
$$

All three denominators $x,x+1,x+2$ are positive. Interpolation gives
$H_0=c_0-d\tau$, $H_2=c_2-d\tau_2$ and
$9\tau_2-\tau=s-9$. The restored identities in (12.9) therefore give

$$
\begin{aligned}
A_U&=d(U-\tau)+c_0=0,\\
B_U&=(U+1)(c_2-d\tau_2)-(\gamma-2d)U=0.
\end{aligned}
\tag{14.9}
$$

Consequently the necessary quadratic is

$$
\begin{aligned}
\Phi(U)
 &=(U+1)\{c_2(U-\tau)+c_0\tau_2\}
                     -\{\gamma(U-\tau)+2c_0\}U\\
 &=(U-\tau)B_U+\{(U+1)\tau_2-2U\}A_U=0,\\
\Phi(U)&=\lambda_2U^2+\lambda_1U+\lambda_0,\\
\lambda_2&=c_2-\gamma,\\
\lambda_1&=\{c_0(s-26)+e(\tau-1)\}/9+\gamma\tau,\\
\lambda_0&=\{c_0(s-9)+e\tau\}/9.
\end{aligned}
\tag{14.10}
$$

In particular the factor $U+1$ multiplies the entire first bracket.
The undivided identity in (14.10) is valid also at $d=0$ or
$U=\tau$; no converse from $\Phi=0$ alone is asserted.

The original source identity $j=b+r(1-r)/b$, together with
$x=(j+r)/U$ and $U=1+2b$, gives

$$
\begin{gathered}
r^2-(b+1)r+bxU-b^2=0,\\
\Psi(U):=(5-8x)U^2+(8x-6)U+5=4(2r-b-1)^2\ge0.
\end{gathered}
\tag{14.11}
$$

If $x>13/16$, then $\Psi''<0$, $\Psi'(1)=4-8x<0$ and
$\Psi(2)=13-16x<0$. Since the source has $U>1$, monotonicity on
$[1,\infty)$ forces $1<U<2$. This uses the actual source equation,
without selecting either of its quadratic roots.

Here are sufficient rational bounds for (14.10). They hold on each
entire indicated closed interval and all of $Z_{pw}$.

| $x$ interval | Bounds for $\tau,s$ | Bounds for $c_0,c_2,e$ |
| --- | --- | --- |
| $[1/3,5/12]$ | $1<\tau<40$, $s>35$ | $c_0<-5000$, $c_2<0$, $e<0$ |
| $I_c=[24/25,501/500]$ | $-11<\tau<-9$, $s<35/2$ | $c_0<-5500$, $c_2<0$, $e<130$ |
| $[19/10,63/25]$ | $-30<\tau<0$, $s<9$ | $c_0<-3200$, $c_2<0$, $e<280$ |
| $[27,34]$ | $-44<\tau<-43$, $1/3<s<1$ | $-1140<c_0<0$, $c_2<0$, $e>172$ |

For completeness these bounds follow from elementary endpoint
comparisons, not from evaluations at candidate roots. Put

$$
a(x)=\frac{36}{x+1}-\frac{92}{5(x+2)},\qquad
a_2(x)=\frac4{x+1}-\frac{46}{25(x+2)}.
\tag{14.12}
$$

Both functions are positive and strictly decreasing for $x>0$;
this follows directly by comparison of their two terms and their
derivatives, since $36>92/5$, $4>46/25$ and $x+1<x+2$.
Also $\tau'<0$ and $s'<0$: for $\tau'$ the term
$10/(x+2)^2$ is smaller than $20/x^2$. Now

$$
\begin{gathered}
c_0=480/x-810+pa(x)-10w/(x+2),\\
c_2=96/x-108+pa_2(x)-w/(x+2),\qquad
87837/100\le-v\le10201/10.
\end{gathered}
\tag{14.13}
$$

For $[1/3,5/12]$, endpoint substitution gives $a>17$, $a_2>2$,
$-10w/(x+2)<161$ and $-w/(x+2)<17$. Hence

$$
\begin{gathered}
c_0<1440-810-457\cdot17+161=-6978,\\
c_2<288-108-457\cdot2+17=-717,\\
e\le162-4608/5+30603/70=-22569/70<0.
\end{gathered}
\tag{14.14}
$$

On $I_c$, $a>59/5$, $a_2>1$, the two positive $w$ terms are
less than $130,13$, respectively, and
$384/x>380$, $(-v)/(x+2)<348$. Therefore

$$
c_0<500-810-457\cdot59/5+130=-27863/5<-5500,\quad
c_2<100-108-457+13=-452,\quad e<130.
\tag{14.15}
$$

On $[19/10,63/25]$, $a>6$, $a_2>0$ and

$$
\begin{gathered}
480/x-10w/(x+2)
 \le480/(19/10)+(1877/5)/(39/10)=258526/741<350,\\
c_0<350-810-457\cdot6=-3202,\qquad
c_2<51-108+10=-47,\qquad e<162-152+262=272<280.
\end{gathered}
\tag{14.16}
$$

On $[27,34]$, $0<a<33/50$, $a_2>0$ and endpoint comparison gives

$$
\begin{gathered}
c_0>14-810-534\cdot33/50+10=-28461/25>-1140,\\
c_0<18-810+13=-779<0,\qquad c_2<4-108+2=-102,\\
e>162-43/3+73/3=172.
\end{gathered}
\tag{14.17}
$$

The bounds on $\tau,s$ in the table are their monotone endpoint
bounds on the same intervals. Thus $\Phi''=2(c_2-\gamma)<0$
throughout all four ranges.

On $[1/3,5/12]$, (14.10) has $\lambda_0<0$ and
$\lambda_2<0$. Moreover
$\lambda_1<-5000+\gamma\cdot40=-2648<0$.
Thus $\Phi(U)<0$ for every $U>0$, which excludes any actual world.

For the other ranges $x>13/16$, so $1<U<2$ by (14.11).
The endpoint and derivative formulas from (14.10) are

$$
\begin{aligned}
\Phi(1)&=2c_0(s-17)/9-(2e/9+\gamma)(1-\tau),\\
\Phi(2)&=c_0(s-19)/3-(e/3+2\gamma)(2-\tau),\\
\Phi'(1)&=c_0(s-24)/9-e(3-\tau)/9+\gamma(\tau-2),\\
\Phi'(2)&=c_0(s-22)/9-e(5-\tau)/9+\gamma(\tau-4).
\end{aligned}
\tag{14.18}
$$

On $[19/10,63/25]$ these give

$$
\begin{aligned}
\Phi(1)&>51200/9-(560/9+294/5)\,31=9686/5>0,\\
\Phi(2)&>32000/3-(280/3+588/5)\,32=19584/5>0.
\end{aligned}
\tag{14.19}
$$

Concavity places $\Phi$ above its positive endpoint chord on
$[1,2]$, excluding every source there. On $[27,34]$,

$$
\begin{aligned}
\Phi(1)&<(2280/9)(50/3)-(344/9+294/5)\,44=-2104/45<0,\\
\Phi'(1)&<3040-172\cdot46/9-2646=-4366/9<0.
\end{aligned}
\tag{14.20}
$$

Concavity then makes $\Phi$ strictly decreasing and negative for
$U\ge1$, again excluding every source.

The same source-side exclusion covers the unbounded tail. For
$x\ge34$, $a(x)<18/x$, $a_2(x)>0$, and the strip bounds give

$$
\begin{gathered}
-45<\tau<-43,\qquad 0<s<1,\qquad c_0>-1070,\qquad c_0<0,\\
c_2<0,\qquad e>162.
\end{gathered}
\tag{14.21a}
$$

Here $a$ is decreasing and $a(x)<18/x$ follows by cross
multiplication; also $-v\ge87837/100$ on the strip. Explicitly,

$$
c_0>-810-\frac{9132}{x}+\frac{1877}{5(x+2)}>-1070,
$$

because the last difference from $-1070$ is increasing for $x\ge34$
and equals $5629/3060$ at $x=34$. Further,

$$
e\ge162-\frac{384}{x}+\frac{87837}{100(x+2)}>162,
$$

since $49437x-76800>0$ there. The remaining displayed bounds follow
from $\tau'<0$, $s'<0$, and the endpoint estimates
$96/x-108+1877/(1800)<0$ and
$480/x-810+1877/(180)<0$. Using (14.18), these inequalities yield

$$
\Phi(1)<\frac{36380}{9}-\frac{20856}{5}<0,
\qquad
\Phi'(1)<\frac{25680}{9}-828-2646<0.
\tag{14.21b}
$$

Together with $\Phi''=2(c_2-\gamma)<0$, this makes $\Phi$ negative
for every $U\ge1$. The source identity (14.11) gives $1<U<2$ for
$x\ge34$, so no actual source occurs on the tail. This argument uses
the source equation and does not claim that every tail carrier root is
positive or that a carrier root lifts to a world.

Finally on $I_c$, (14.18) gives

$$
\Phi'(2)>2750-2080/9-882=14732/9>0.
\tag{14.21}
$$

Since $\Phi''<0$, it follows that $\Phi'(U)\ge\Phi'(2)>0$ on
$[1,2]$. For fixed $(x,p,v)$ there is at most one admissible $U$.
Also $U-\tau>0$ there, so (14.9) uniquely fixes
$d=-c_0/(U-\tau)$. The injective full-world inverse consequently
permits at most one complete world for each such $x$.

### 14.4. The uniform regular inventory bound

**Theorem 14.1 (At most two regular worlds on the entire closed strip).**
For every $(p,v)\in\mathcal S$,

$$
|C_{\rm reg}(p,v)|\le2.
\tag{14.22}
$$

Proof. Any original regular world gives $x>0$ and $R(x,p,v)=0$
by (12.13). If $x\le34$, the finite coefficient bounds place it in
one of the six closed ranges of (14.7); if $x\ge34$, the tail
exclusion in (14.21a)–(14.21b) applies directly to the source. The
first two ranges are contained in $[1/3,5/12]$; the fourth and fifth
are contained in $[19/10,63/25]$; the last is $[27,34]$. The necessary
quadratic excludes actual worlds on all these exterior ranges. Thus
every regular world has $x\in I_c$, where (14.6) allows at most two
distinct carrier roots. Equations (14.9) and (14.21), followed by
the faithful inverse, allow at most one complete world over each.
This proves (14.22).

Every use of a source restriction above was a consequence of that
same world's original equations. No division by $A$, $F_0$, $d$,
$D_s$ at a singular source, a gain sample, a leading gain coefficient
or a root difference is used. The sole additional inverse division
$U-\tau$ occurs after its strict positivity on $I_c$ is proved.
Neither a carrier root nor a zero of $\Phi$ is asserted to be a
faithful world. The count therefore retains negative gains, lower
degrees, sampled zeros, repeated roots and arbitrary own drifts. ∎

### 14.5. The exact continuation lies in the strip

The simultaneous enclosure needed for the entire selected family uses
the common parameter of the exact secant zero, rather than separate
marginal bounds for $p,v$. Set

$$
\bar q=\frac{229545252522}{10^{14}},\qquad
G=10^{40},\qquad \rho=10^{-12},\qquad
q_{i,l}=i/5000,\quad q_{i,u}=\min\{(i+1)/5000,\bar q\}
\quad(0\le i\le11).
\tag{14.23}
$$

The rational comparison with (13.23) gives
$11/5000<\bar q<12/5000$ and $q_*<\bar q$.
For each cell let

$$
\ell_i=\left\lfloor\sqrt{G^2q_{i,l}}\right\rfloor,\quad
u_i=\left\lceil\sqrt{G^2q_{i,u}}\right\rceil,\quad
h_i(z)=\frac{\ell_i+u_i+(u_i-\ell_i)z}{2G},\quad -1\le z\le1.
\tag{14.24}
$$

Both radicands are integers, and these definitions enclose the full
square-root interval, including zero and all cell seams. Use the
same predictor row $i$ of IX (25.2), including its factor $10^{-55}$,
and substitute $q=h_i(z)^2$ before forming

$$
\widehat t_i=\widehat X_i(h_i^2)+h_i\widehat K_i(h_i^2),\qquad
\widehat b_i=\widehat Y_i(h_i^2)+h_i.
\tag{14.25}
$$

Compose the whole polynomial circuit (13.14) at these two
polynomials, and denote its entries by
$\widehat D_i,\widehat N_{p,i},\widehat N_{v,i}$. The following
four polynomials have degree 86:

$$
\begin{aligned}
L_{i1}&=\widehat N_{p,i}+534\widehat D_i,\\
L_{i2}&=-457\widehat D_i-\widehat N_{p,i},\\
L_{i3}&=\widehat N_{v,i}-\tfrac{46}{25}\widehat N_{p,i}
                                  +\tfrac{1877}{50}\widehat D_i,\\
L_{i4}&=-\widehat N_{v,i}+\tfrac{46}{25}\widehat N_{p,i}
                                  -\tfrac{3749}{100}\widehat D_i.
\end{aligned}
\tag{14.26}
$$

All these compositions have exact rational coefficients; no rounding
convention is needed. For the actual exact zero in the cell, use the
full $\rho$ tube in IX Theorem 26.1. The segment from the predictor
to the zero lies in the rectangle of (13.20). Its derivative guards,
with the same plus-source convention as (14.25), are

$$
\Gamma(D_s)=\frac{7667254617}{20000000}<384,\quad
\Gamma(N_p)=\frac{13033889043873}{1250000000}<10428,\quad
\Gamma(N_v)=\frac{97107509878563}{2000000000}<48554.
\tag{14.27}
$$

The mean value bound therefore changes the four actual numerators
from (14.26) by at most, respectively,

$$
\begin{aligned}
E_1&=\rho(10428+534\cdot384),\\
E_2&=\rho(10428+457\cdot384),\\
E_3&=\rho(48554+\tfrac{46}{25}10428+\tfrac{1877}{50}384),\\
E_4&=\rho(48554+\tfrac{46}{25}10428+\tfrac{3749}{100}384).
\end{aligned}
\tag{14.28}
$$

The exact sums (14.2), now in one variable on $[-1,1]$, give

$$
\mathfrak b_{[-1,1]}(L_{ij})-E_j>10^{-9}T_{ij}>0
\tag{14.29}
$$

with the following integer matrix. The bounds already include the
entire predictor error; they are not values only at the predictor.

| Cell $i$ | $T_{i1}$ | $T_{i2}$ | $T_{i3}$ | $T_{i4}$ |
| --- | --- | --- | --- | --- |
| 0 | 3845018 | 472161935 | 121273 | 193512 |
| 1 | 54582059 | 395340711 | 78509 | 220604 |
| 2 | 97899078 | 331027273 | 52215 | 241612 |
| 3 | 135869861 | 274693506 | 38795 | 249333 |
| 4 | 169277191 | 224467569 | 35761 | 238572 |
| 5 | 198565733 | 179335539 | 35960 | 219833 |
| 6 | 224028329 | 138666027 | 41926 | 194369 |
| 7 | 245873927 | 102030520 | 55167 | 163375 |
| 8 | 264259324 | 69120749 | 74311 | 127999 |
| 9 | 279306283 | 39705479 | 98087 | 89354 |
| 10 | 291111694 | 13605778 | 125297 | 48522 |
| 11 | 299754035 | 2275769 | 154793 | 28572 |

These finite inequalities use precisely the inherited rational arrays,
the integer square-root brackets (14.24), the displayed source
circuit and (14.2); all 87 coefficients in each univariate comparison
are included. The same coefficient bound also gives
$\mathfrak b_{[-1,1]}(\widehat D_i)-384\rho>0$ for every cell,
in agreement with the full-tube denominator bounds (13.21).
Thus division by the actual positive denominator turns the four
positive numerators into

$$
-534<p(q)<-457,\qquad
-1877/50<v(q)-(46/25)p(q)<-3749/100
\quad(0\le q\le q_*).
\tag{14.30}
$$

These are readings of the plus endpoint at the same exact parameter.
The secant equalities make them the minus endpoint's readings as
well wherever it is a strict world. IX Theorem 26.1 identifies the
seam solutions and attaches the exact first negative-$J$ germ, so
this enclosure covers the specified continuation throughout, rather
than an independent selection of zeros in successive cells.

### 14.6. Entire-child inventory and terminal-M injectivity

**Theorem 14.2 (The entire first negative-J family).** For every
$0<q<q_*$ of exactly the continuation specified above,

$$
\begin{gathered}
(p(q),v(q))\in\mathcal S,\qquad
C(p(q),v(q))=\{W_-(q),W_+(q)\},\\
W_-(q)\ne W_+(q),\qquad a(W_-(q))=a(W_+(q)),\\
m(W_-(q))<m(W_+(q)).
\end{gathered}
\tag{14.31}
$$

In particular $m$ is injective on this entire original child.

Proof. The common-parameter enclosure (14.30) puts the exact base
in $\mathcal S$. Theorem 13.1 excludes all singular original worlds
there, and (13.24) identifies this nonsingularity with the regularity
used in Theorem 14.1. Hence the entire child has at most two worlds.
IX Theorem 28.1 supplies two distinct complete original worlds at
this identical full base, with their own original whole-gain lifts
and drifts. They exhaust the child. Its same theorem, (28.1)–(28.2),
gives their equal $J$ readings and strict $M$ ordering. Any two
distinct worlds in the entire child must therefore be this pair, so
their terminal $M$ readings differ. ∎

The new uniform conclusions are the regular-world count on all of
$\mathcal S$ and the complete-child inventory on every strict
parameter of this first continuation. The Bernstein estimate is a
classical tool, and the existence, original-world lifts and strict
$M$ ordering of the selected pair are the cited inputs. The deductions
here are specific to the displayed source equations; no
literature-priority claim is made for them.

Theorem 14.1 does not assert two-world existence, singular exclusion
or $M$ injectivity at every base of the strip. The endpoints $q=0$
and $q=q_*$ are excluded from (14.31): the two endpoints coalesce
at zero, whereas the minus source has $b_-=r_-=0$ at $q_*$. The
analytic enclosure (14.30) does not turn either limit into a strict
distinct pair. Other bases and branches, globally independent $J/M$
incidence, the fixed48 obligation V (18.12)(i), earlier losing
histories and their common-tree feasibility, the original rootQ,
eight-read recovery and the nine-read question remain outside these
conclusions. The lower bound $n_{\rm det}(3,0)\ge8$ is unchanged.

## 追加锚（本行以下为增补区）
