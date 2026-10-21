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
