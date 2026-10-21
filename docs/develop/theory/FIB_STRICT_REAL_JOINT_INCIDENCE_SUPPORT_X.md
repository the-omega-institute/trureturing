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
