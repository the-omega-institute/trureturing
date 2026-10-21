# FIB strict-real joint incidence: regular critical separation

## 1. Original worlds and the precise scope

**Definition 1.1 (Complete worlds and readings).** A world is a triple
$W=(P,g,d)$ with

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\quad b>0,\quad d\in\mathbb R,
\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3.
\tag{1.1}
$$

The same entire polynomial and the same drift are used at every clock.
Set

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{1.2}
$$

The original history at clocks zero through four is
$(0,J,24,M,147/5,J,24,M,18)$. The acquired fifth and sixth actions
are $M,M$, with readings $p,v$. At clock seven write $a$ for the
alternative $J$ response and $m$ for the alternative $M$ response.
No alternative response is an additional acquisition. Let $\mathcal H$
be the entire strict parent realizing the original history. Define
$C(p,v)=\{W\in\mathcal H:p(W)=p,\ v(W)=v\}$, also at $p=24$ when
using the ambient parent. The augmented map in this volume is

$$
\Psi_M:\mathcal H\longrightarrow\mathbb R^3,\qquad
\Psi_M(W)=(p(W),v(W),m(W)).
\tag{1.3}
$$

All gain signs, degree drops, sampled zeros, repeated roots and all real
drifts are retained. Distinctness means distinct complete triples.

**Definition 1.2 (Mathematical suppliers).** Use the following source
abbreviations. The statements and parameter correspondences in this
table are the premises used from those sources.

| Source | Exact interface used here |
| --- | --- |
| [O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3 and Theorem 2.1 | The original worlds, clocks, left products, zero-safe full-parent equation and whole-gain reconstruction. O's $\epsilon$ is $e=d-24$ here; its $u_M,f_{MM},f_{MJ}$ are $v,m,a$. |
| [F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md), Definition 27.1 and Theorem 27.2 | The central world and its output; local central saturation is a matching-pair statement, not immersion at the centre. F's $u$ is $v$. |
| [SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Theorem 27.2 | On the full parent, every strict $p=24$ world except the central world has rank-two $\Psi_M$ and a neighbourhood of local injectivity. Singular sources and K/H meetings are included. |
| SII, Theorem 29.1 | There is one $\epsilon>0$, uniform for every real $v$, such that $0<|p-24|<\epsilon$ excludes every within-pair-distinct equal-$m$ pair in the entire actual $C(p,v)$. |
| [III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Definition 10.1, Lemma 10.2 and Lemma 11.2 | The analytic parent in $(r,b,e)$ is the complete-world parent, including padded gain coefficients. It is a smooth surface also at every singular-source world, for every real drift. |
| III, Theorem 13.1 | At every strict singular-source world, $\Psi_M$ has full-parent rank two and is locally injective, for every real drift and every allowed gain stratum. |
| III, Lemma 16.3 and Theorem 16.4 | The actual analytic distinct $J$-pair arc $z_J(p)$ for $10\le p\le34$, with the rational centre arrays of (16.7) and radius $\rho=1/100000$ pointwise tubes. Its common sixth response is $v_J(p)$. |
| III, Definition 23.1 and Theorem 23.2 | The sets $K_+$ and $K_J$ of Definition 7.1 below are compact in complete-world and $(r,b,e)$ coordinates, including the entire $p=24$ fibre and every unused or singular companion. |
| [S](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md), Corollary 18.2 | In the presence of an actual distinct $J$ pair, every endpoint of an actual distinct off-$24$ equal-$m$ pair is regular. This does not restrict unused companions. |

The III arc and compactness statements mean the source version containing
Sections 16 and 20–23, with SHA256
`3d179efcb5d63392cd6db0d0c8e374fb2222bab90b1dc6ab164fb2913d6f3a40`.
Those statements are an integration dependency. The results below using
$v_J$ and $K_J$ use that precise arc and whole-companion compactness;
they do not replace them by a numerical source box.

The substantive calculation here is the regular critical-locus
elimination in Sections 3–6. The all-companion immersion and compact
separated collision relation are its consequences with the stated
suppliers. They do not assert global injectivity or settle the original
independent-pair problem. All proofs are ordinary mathematical proofs
with exact finite certificates.

## 2. The full parent and its regular rational chart

**Definition 2.1 (Zero-safe parent and regularity).** Put

$$
\begin{gathered}
c=r(1-r)/b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
\kappa=6/T-2/U=2(2+5b)/(TU)>0,\\
e=d-24,\qquad H(r,b,e)=e\Lambda+\frac{24}{5}(b-1/8)\kappa.
\end{gathered}
\tag{2.1}
$$

The parent is $H=0$ in $0<r<1,b>0,e\in\mathbb R$. A world is
regular when $\Lambda\ne0$, and singular when $\Lambda=0$; this
terminology concerns the reconstruction chart. Singular-source worlds
are smooth points of the full parent by III, Lemma 11.2.

For a parent triple the whole gain is the unique degree-at-most-three
interpolant of

$$
(G_0,G_1,G_2,G_3)=
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right)
\tag{2.2}
$$

at the fixed nodes $0,1,2,3$. The inverse of this reconstruction reads
$r=P_{11}$, $b=P_{12}$ and $e=d-24$. In particular it identifies the
parent topology with the topology of all four gain coefficients padded
through degree three. No gain value or coefficient is divided out.

**Lemma 2.2 (Explicit regular response circuit).** Set $t=r/b$.
Then $j=t+b(1-t^2)$, $n=j+tb$, and the strict chart is
$t>0,b>0,tb<1$. Define integer polynomials in $t,b$ by

$$
\begin{aligned}
D&=5\bigl((b^2+8b+4)jn-2TU(j+n)\bigr),&A&=(8b-1)(2+5b),\\
C_0&=-24D+3Ajn,&C_1&=3An,\\
C_2&=3(49b+34)jn-54U(j+n),&C_3&=3Aj,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
B_7&=-20C_0+70C_1-84C_2+35C_3,\\
N_0&=-C_0+(U+n)B_5,\\
N_1&=-C_0+(2U+n)B_6,\\
N_2&=-C_0+(3U+2n)B_7.
\end{aligned}
\tag{2.3}
$$

On the regular parent,

$$
D=\frac52 TUjn\Lambda\ne0,\qquad
f_M(t,b)=\frac{(N_0,N_1,N_2)}D=(p,v,m),\qquad d=-C_0/D.
\tag{2.4}
$$

The whole gain interpolates $C_i/D$ at $i=0,1,2,3$.

Proof. The original left products have traces
$1,j,T,n,U,U+n,2U+n$ at clocks zero through six; a seventh $M$
has trace $3U+2n$. At the first four clocks the readings give (2.2).
The fourth-clock interpolation residual is

$$
-G_0+4G_1-6G_2+4G_3-\frac{18-(24+e)}U=H.
\tag{2.5}
$$

Thus $H=0$ is exactly the remaining original row, as in O,
Theorem 2.1. Solve only for $e$ on $\Lambda\ne0$. Multiplication
by $D=(5/2)TUjn\Lambda$ gives precisely the four $C_i$ of (2.3).
The fixed-node Lagrange evaluation rows at $5,6,7$ are respectively
$(-4,15,-20,10)$, $(-10,36,-45,20)$ and $(-20,70,-84,35)$.
They give $B_i$ and hence $N_i$. The unequal original readings
$0,24$ exclude an identically zero reconstructed gain. All source
denominators $b,j,n,T,U$ are positive. Regularity is the only extra
division, and the correspondence holds on every regular gain and drift
stratum. ∎

## 3. Integral equations for the regular critical locus

**Definition 3.1 (Normalized minor polynomials).** For $i=0,1,2$ let

$$
B_{it}=D\partial_tN_i-N_i\partial_tD,\qquad
B_{ib}=D\partial_bN_i-N_i\partial_bD.
\tag{3.1}
$$

For $(i,k)=(0,1),(0,2),(1,2)$, in this order, put

$$
M_{ik}=B_{it}B_{kb}-B_{ib}B_{kt},\qquad
E_{ik}(r,b)=\frac{b^7}{45}\left(\frac{M_{ik}}D\right)(r/b,b).
\tag{3.2}
$$

Write $E_0=E_{01}$, $E_1=E_{02}$, $E_2=E_{12}$. Formula (3.2)
is an exact polynomial definition, rather than a division at a selected
source.

**Lemma 3.2 (Normalization and rank equivalence).** Each $M_{ik}$ is
divisible by $D$ in $\mathbb Z[t,b]$; (3.2) belongs to
$\mathbb Z[r,b]$. Each $E_i$ has $r$ degree $15$, $b$ degree $17$,
total degree $17$, exactly $134$ nonzero monomials and integer content
one. The derivatives in the independent $(r,b)$ coordinates satisfy

$$
\det\frac{\partial(f_i,f_k)}{\partial(r,b)}
=\frac{45E_{ik}(r,b)}{b^8D(r/b,b)^3}.
\tag{3.3}
$$

Consequently the full-parent regular rank is less than two exactly
when $E_0=E_1=E_2=0$.

Proof. Expanding the integer circuit (2.3), taking its derivatives and
performing exact polynomial division gives the divisibility and integer
coefficient assertions. Section 10 gives all inputs, the exact divisions
with zero remainder, and every stated degree, content and monomial
check, so this finite identity does not require any unspecified expanded
coefficient array. Quotient differentiation gives $M_{ik}/D^4$ in
$(t,b)$ coordinates. The coordinate change $t=r/b$ has Jacobian
determinant $1/b$, yielding (3.3) after (3.2). Strictness gives $b>0$
and regularity gives $D\ne0$, so no zero of a regular minor is lost
or added. The regular chart parametrizes the full parent since
$H_e=\Lambda\ne0$. ∎

## 4. Fixed determinants and the degree-sixty-seven cover

**Definition 4.1 (Determinants with no specialization convention).**
For two polynomials of fixed $r$ degree $15$, their Sylvester matrix
has rows the coefficient vectors of

$$
r^{14}E_0,\ldots,E_0,\quad r^{14}E_k,\ldots,E_k
\tag{4.1}
$$

in columns $r^{29},\ldots,1$. Define $R_k(b)$ as its determinant
for $k=1,2$. The degrees remain fixed in this definition even when a
specialized leading coefficient vanishes.

For the linear subresultant take the $28$ rows
$r^{13}E_0,\ldots,E_0,r^{13}E_1,\ldots,E_1$ in columns
$r^{28},\ldots,1$. Retain the first $27$ columns and append either
the $r$ column or the constant column. Their determinants, in that
order, are $a_0(b)$ and $c_0(b)$. Thus

$$
L(r,b)=a_0(b)r+c_0(b).
\tag{4.2}
$$

For a nonzero rational polynomial, $\operatorname{pp}_+$ means its
primitive integer associate with positive leading coefficient. Put
$h=\operatorname{pp}_+(\gcd(a_0,c_0))$, $a=a_0/h$, $c=c_0/h$.
These divisions are exact in $\mathbb Q[b]$; the actual coefficients
in this normalization are integers.

**Lemma 4.2 (Exact elimination identities).** Let $F(b)$ be the degree
$67$ polynomial whose $68$ descending integer coefficients are `FC` in
Section 10. It is primitive and has positive leading coefficient. Then

$$
\begin{aligned}
\deg R_1=\deg R_2&=285,\\
\operatorname{pp}_+(\gcd(R_1,R_2))
&=b^{110}(2b+1)^8(5b+2)^{17}(8b-1)^{17}\\
&\quad\cdot(5b^2+2b+1)(b^2+8b+4)^2F(b),\\
h&=b^{90}(2b+1)^5(5b+2)^{14}(8b-1)^{20}(b^2+8b+4)^2,\\
(\deg a_0,\deg c_0,\deg h,\deg a,\deg c)&=(252,253,133,119,120),\\
\gcd(F,h)=\gcd(F,a)=\gcd(F,F')&=1
\quad\hbox{up to nonzero constants.}
\end{aligned}
\tag{4.3}
$$

The two resultant quotients by their common primitive factor have degree
$60$ each and are coprime. The reduced $a,c$ are also coprime.

Proof. These are finite integer polynomial identities, reproducible by
the exact prescription in Section 10. For completeness that prescription
also checks the computed subresultants against the fixed determinants,
rather than relying on specialization of an implementation convention.
Here is why its finite determinant checks establish polynomial equality.

Every coefficient of $r^j$ in an $E_i$ has $b$ degree at most $17-j$.
In a Sylvester determinant term the sum of coefficient $r$ exponents is

$$
\sum_{j=0}^{29}j-2\sum_{j=0}^{14}j=225.
$$

Its $b$ degree is therefore at most $30\cdot17-225=285$.
For (4.2) the row-shift sum is $2\sum_{j=0}^{13}j=182$.
The first $27$ column exponents sum to $\sum_{j=2}^{28}j=405$.
Appending the $r$ column gives bound $28\cdot17-(406-182)=252$;
appending the constant column gives bound $253$.
The certificate computes both Sylvester determinants at all integers
$0,\ldots,285$, and both linear minors at $0,\ldots,253$.
Agreement at those distinct integers proves their full polynomial
identities by these degree bounds. Exact Euclidean gcd and exact
division then give (4.3), with the explicitly listed coefficients of
$F$. This includes every exceptional factor, with multiplicity. ∎

**Lemma 4.3 (Necessary cover and guarded lift).** A strict regular
critical world either has $b=1/8$, or satisfies

$$
F(b)=0,\qquad r=-c(b)/a(b).
\tag{4.4}
$$

This remains a necessary condition at every leading-coefficient drop;
no converse about resultant roots is asserted.

Proof. At a finite common $r=\lambda$ root, each specialized Sylvester
matrix annihilates the nonzero vector
$(\lambda^{29},\ldots,1)^{\mathsf T}$: its rows give multiples of the
two vanishing polynomials. Both $R_k(b)$ therefore vanish even at degree
drops. Their gcd also vanishes, since it is a rational polynomial
combination of them. For $b>0$, all displayed factors of (4.3) other
than $8b-1$ and $F$ are strictly positive.

For the $28$-row matrix defining (4.2), let its columns be
$C_{28},\ldots,C_0$. At a common root,

$$
\lambda C_1+C_0=-\sum_{j=2}^{28}\lambda^jC_j.
\tag{4.5}
$$

Taking the determinant with the first $27$ columns gives
$a_0(b)\lambda+c_0(b)=0$, with no leading coefficient divided out.
If $F(b)=0$, (4.3) makes both $h(b)$ and $a(b)$ nonzero, giving
(4.4). Spurious projected roots cause no problem for a necessary cover.
∎

## 5. All positive roots and their original-source exclusions

**Definition 5.1 (Signed Sturm and interval conventions).** Start with
$S_0=F$, $S_1=\operatorname{pp}(F')$, where $\operatorname{pp}$ divides
by positive integer content and preserves sign. Recursively take
$-\operatorname{rem}(S_{i-1},S_i)$ over $\mathbb Q[b]$ and clear
denominators and content by positive factors only. Equivalently, if
$k=\deg S_{i-1}-\deg S_i+1$, use

$$
\operatorname{pp}\left(
-\operatorname{prem}(S_{i-1},S_i)
\operatorname{sign}(\operatorname{lc}S_i)^k\right).
\tag{5.1}
$$

No positive-leading-coefficient normalization is applied to this chain.
$V(x)$ counts sign variations after zero entries are omitted, and the
sign at $+\infty$ is the leading coefficient sign.

All interval operations below have exact rational endpoints. Multiplication
uses the minimum and maximum of the four endpoint products. Division
uses the reciprocal interval only after zero is excluded. Horner
means descending powers, starting at zero. For two variables use
$b$ Horner inside the other variable's Horner, retaining zero coefficients.

**Lemma 5.2 (Exhaustive positive-root certificate).** The Sturm chain
has $68$ polynomials of degrees $67,66,\ldots,0$, with
$V(0)=27$ and $V(+\infty)=21$. Its six positive roots are simple and
lie one each in the following disjoint open intervals. In the first
column $I=(q/10^8,(q+1)/10^8)$.

| $q$ | $\operatorname{sign}F$ at the two endpoints | $V$ at the two endpoints | Exact lifted $r$ enclosure | Original-source or response exclusion |
| --- | --- | --- | --- | --- |
| $845744$ | $+,-$ | $27,26$ | $0<r<1/100$ | $690<p<691$ |
| $4228383$ | $-,+$ | $26,25$ | $519/1000<r<520/1000$ | $1<p<2$ |
| $5311219$ | $+,-$ | $25,24$ | $-3/1000<r<-2/1000$ | $r<0$ |
| $6737603$ | $-,+$ | $24,23$ | $-4/1000<r<-3/1000$ | $r<0$ |
| $12758053$ | $+,-$ | $23,22$ | $900/1000<r<901/1000$ | $7<p<8$ |
| $88676283$ | $-,+$ | $22,21$ | $964/1000<r<965/1000$ | $57<p<58$ |

For each row the enclosures mean the following deterministic rational
calculation. Bisect $I$ exactly $256$ times, always retaining the half
with opposite nonzero endpoint $F$ signs. Denote the resulting closed
interval by $I^*$. Its width is $1/(10^8 2^{256})$. Evaluate $a,c$ by
interval Horner on $I^*$ and set

$$
R=-c(I^*)/a(I^*).
\tag{5.2}
$$

The signs of $a(I^*)$ in the six rows are $-,+,+,+,+,-$; thus every
division in (5.2) is legal. The resulting $R$ lies strictly inside the
listed $r$ enclosure. In rows $1,2,5,6$, form the integer polynomials

$$
\widetilde D(r,b)=b^2D(r/b,b),\qquad
\widetilde N(r,b)=b^3N_0(r/b,b).
\tag{5.3}
$$

Evaluate them on the full rectangle $R\times I^*$, then divide by the
positive interval powers of $b$. The $D$ interval signs are respectively
$-,+,-,-$ and the quotient $N_0/D$ lies strictly within the listed
$p$ enclosure.

Proof. The coefficient list `FC`, the recurrence (5.1), and the exact
interval operations in Section 10 give these finite assertions. The
public code checks all chain degrees, endpoint variations, opposite
endpoint signs, $1536$ midpoint bisections, six lift denominators and
four response denominators. In particular it does not use floating-point
root labels. Sturm's theorem gives six positive roots in total. The six
unit variation drops sum to six, so every positive root occurs in the
table; $\gcd(F,F')=1$ also supplies simplicity. Every root retained by
the necessary lift (4.4) is therefore either outside the original strict
source domain or outside the closed response window $[10,34]$.
The table does not assert that each resultant candidate is a genuine
common zero of all three minors. It excludes them even if it is. ∎

## 6. The exceptional branch and the regular critical theorem

**Lemma 6.1 (The sole regular exceptional critical world).** At $b=1/8$
the regular parent has $e=0$, $d=24$ and

$$
g(s)=h(s)=\frac85(s-1)(s-3)(s-5),\qquad p=24.
\tag{6.1}
$$

The only regular common zero of $E_0,E_1,E_2$ on this strict branch is
$r=9/16$. Its world $W_c$ satisfies

$$
(p,v,m)(W_c)=(24,591/4,720),\quad
D(W_c)=4762875/65536,\quad\Lambda(W_c)=12701/3417.
\tag{6.2}
$$

Proof. The undivided parent gives $e\Lambda=0$ at $b=1/8$.
Regularity forces $e=0$, and (2.2) uniquely interpolates (6.1).
Its fifth value is zero, so $p=24$. For an explicit branch certificate,
put

$$
\begin{aligned}
S(r)&=438272r^4-931328r^3+540800r^2-50728r-853,\\
A_s(r)&=64r^2-64r-1,\qquad B_s(r)=64r^2-72r-1.
\end{aligned}
\tag{6.3}
$$

Exact univariate gcd gives

$$
\gcd\bigl(E_0(r,1/8),E_1(r,1/8),E_2(r,1/8)\bigr)
\doteq(16r-9)S(r)^2,
\qquad \Lambda(r,1/8)=\frac{S(r)}{15A_s(r)B_s(r)}.
\tag{6.4}
$$

Here $\doteq$ permits a nonzero rational scalar. For $0<r<1$,
$A_s=-1-64r(1-r)<0$ and $B_s=A_s-8r<0$. Thus $S=0$ is exactly
the singular condition on this branch, and every regular common zero
has $r=9/16$. Substitution in (2.3) gives (6.2). At this point $t=9/2$
and direct quotient differentiation gives

$$
D_{(t,b)}f_M(W_c)=
\begin{pmatrix}
0&39437184/317525\\
0&31382784/317525\\
0&-209979456/317525
\end{pmatrix}.
\tag{6.5}
$$

Its rank is exactly one, so it really is critical. Equations
(6.4)–(6.5) are also checked by the public certificate. This central
world and its output are the world already described in F,
Definition 27.1; they are not a separate new configuration. ∎

**Theorem 6.2 (Regular critical exclusion on the full response window).**
For every strict regular complete world with $10\le p\le34$,

$$
\operatorname{rank}D\Psi_M<2\quad\Longleftrightarrow\quad W=W_c.
\tag{6.6}
$$

In particular every such world with $p\ne24$ has rank two, uniformly
for all real $v$ and every permitted entire gain and fixed drift.

Proof. Lemma 3.2 converts criticality into a common zero of the three
$E_i$. Lemma 4.3 leaves only $b=1/8$ or a lifted positive $F$ root.
Every positive $F$ root is excluded from this strict response window
by Lemma 5.2. Lemma 6.1 treats $b=1/8$ and proves both directions
of (6.6). This argument never bounds $v$ and never divides by drift,
a gain coefficient, a sampled gain or a root difference. The separate
SII, Theorem 27.2 is consistent with (6.6) and additionally covers
all noncentral singular $p=24$ worlds on the full parent. ∎

## 7. The actual arc and immersion at every companion

**Definition 7.1 (Whole-companion regions).** Use the actual arc $v_J$
of III, Theorem 16.4, not an arbitrary function in an output tube.
With $\ell(p)=(37p+421)/10$ set

$$
\begin{aligned}
K_J&=\{W\in\mathcal H:10\le p(W)\le34,\ v(W)=v_J(p(W))\},\\
K_+&=\{W\in\mathcal H:10\le p(W)\le34,\ v(W)\ge\ell(p(W))-1/25\}.
\end{aligned}
\tag{7.1}
$$

III, Theorems 22.3 and 23.2 give $K_J\subset K_+$ and compactness
of both sets. Both definitions retain the entire fibre at $p=24$.
Neither definition selects just the two worlds used to define the arc.

**Lemma 7.2 (Exact separation of the central output).** The actual arc
satisfies

$$
131<v_J(24)<132<591/4.
\tag{7.2}
$$

Proof. In the $[20,30]$ centre block of III, (16.7), the parameter
at $p=24$ is $u=(2p-50)/10=-1/5$. Exact descending evaluation of
its $L$ centre arrays gives

$$
\widehat t_L=
\frac{4171523022167046121474201119}{1907348632812500000000000000},
\qquad
\widehat b_L=
\frac{610351562503660641621076147}{4882812500000000000000000000}.
\tag{7.3}
$$

The actual $L$ endpoint belongs to the closed rectangle with these
centres and coordinate radius $1/100000$ by III, Lemma 16.3.
This is an enclosure of an actual endpoint, not a claim that the
rational centre itself is an exact world. Expand the original integer
polynomials $D,N_1$ of (2.3), and use descending $b$ Horner inside
$t$ Horner on that entire rectangle. Exact interval arithmetic gives

$$
\begin{gathered}
D\in\left(\frac{3337045049}{10^8},\frac{3340057149}{10^8}\right),\\
\frac{N_1}D\in
\left(\frac{65785649}{500000},\frac{13183121189}{10^8}\right)
\subset(131,132).
\end{gathered}
\tag{7.4}
$$

The first interval excludes zero before division. Section 10 supplies
the two needed centre coefficient lists as well as the full exact
calculation, so (7.3) and (7.4) are reproducible without a private
source of numerical bounds. The actual $L$ response equals $v_J(24)$,
proving (7.2). ∎

**Theorem 7.3 (All-companion full-parent immersion).** At every world
of $K_J$, including every unused, singular or degree-drop companion,
$\Psi_M$ has rank two on the full analytic parent. Each such world
has an open full-parent neighbourhood on which $\Psi_M$ is injective.

Proof. At a regular world with $p\ne24$, apply Theorem 6.2. At
$p=24$, Lemma 7.2 excludes the central world from $K_J$; SII,
Theorem 27.2 then supplies full-parent immersion at every remaining
companion. At any singular world, for any parameter and any real drift,
III, Theorem 13.1 supplies the same conclusion. Thus no condition
requiring all companions to be regular has entered the argument.

For the local-injectivity conclusion, at a regular point $H_e\ne0$
gives a two-dimensional analytic chart. At a singular point the full
surface chart is supplied by III, Lemma 11.2. Rank two selects two
output coordinates with invertible derivative in that chart. The
inverse function theorem makes that two-coordinate submap injective
on one neighbourhood, hence makes $\Psi_M$ injective there. Through
the whole-gain reconstruction this is local uniqueness of complete
worlds on the full parent, not just uniqueness on a fixed-source line
or within a selected gain stratum. ∎

**Proposition 7.4 (Why the larger enclosure is not an immersion domain).**
$\Psi_M$ is not an immersion at every point of $K_+$.

Proof. The strict regular world $W_c$ has $p=24$ and
$v=591/4>\ell(24)-1/25=6543/50$, so it belongs to $K_+$.
Equation (6.5) gives rank one there. Compactness of $K_+$ remains
available as an enclosure result, while Theorem 7.3 concerns the actual
$K_J$ and uses the exact exclusion (7.2). ∎

## 8. Derived separation and compact ordered collisions

**Theorem 8.1 (A uniform positive separation is a consequence).** Write
$z(W)=(r,b,e)$ and use the Euclidean norm. There is a $\delta>0$
such that for every $W,W'\in K_J$,

$$
W\ne W',\quad\Psi_M(W)=\Psi_M(W')
\quad\Longrightarrow\quad
\|z(W)-z(W')\|_2\ge\delta.
\tag{8.1}
$$

The same $\delta$ works for the Euclidean distance between the full
tuples $(P_{11},P_{12},P_{21},P_{22},\alpha_0,\alpha_1,\alpha_2,
\alpha_3,d)$, where $g(s)=\sum_{i=0}^3\alpha_i s^i$.
No numerical value of $\delta$ is asserted or assumed.

Proof. If there are no distinct matching pairs, choose any positive
$\delta$. Otherwise, if no positive separation exists, choose distinct
equal-output pairs with $\|z(W_n)-z(W'_n)\|_2\to0$.
III, Theorem 23.2 makes $K_J$ compact, so along a subsequence
$W_n\to W\in K_J$. The coordinate distance implies
$z(W'_n)\to z(W)$, and continuity of whole-gain reconstruction gives
$W'_n\to W$ as complete worlds. Theorem 7.3 supplies one full-parent
local-injectivity neighbourhood of $W$. Both endpoints are eventually
in that same neighbourhood and have equal $\Psi_M$, contradicting
their distinctness. This proves (8.1). The full tuple norm dominates
the norm of its $P_{11},P_{12},d$ coordinate differences, which equal
the $r,b,e$ differences. ∎

**Corollary 8.2 (Compact full ordered collision relation).** The set

$$
\mathcal R=\{(W,W')\in K_J^2:W\ne W',\
\Psi_M(W)=\Psi_M(W')\}
\tag{8.2}
$$

is compact in either of the coordinate topologies just specified.

Proof. For a $\delta$ supplied by Theorem 8.1, (8.2) is exactly

$$
\{(W,W')\in K_J^2:\Psi_M(W)=\Psi_M(W'),\
\|z(W)-z(W')\|_2\ge\delta\}.
\tag{8.3}
$$

This is closed in compact $K_J^2$ by continuity, hence compact.
The argument derives the removal of a neighbourhood of the diagonal;
it does not discard near-diagonal worlds as an input restriction. ∎

**Corollary 8.3 (Compact ordered off-twenty-four collision relation).**
The actual ordered relation

$$
\mathcal R^\times=\{(W,W')\in\mathcal R:p(W)\ne24\}
\tag{8.4}
$$

is compact. For the uniform $\epsilon>0$ of SII, Theorem 29.1,

$$
\mathcal R^\times=\mathcal R\cap
\{(W,W'):|p(W)-24|\ge\epsilon\}.
\tag{8.5}
$$

Proof. On $\mathcal R$ the endpoints lie in the same $C(p,v)$ and
have equal $m$. Every off-$24$ pair therefore has
$|p-24|\ge\epsilon$ by that supplier, uniformly in all real $v$;
conversely the inequality implies $p\ne24$. This proves (8.5), a
closed subset of the compact relation of Corollary 8.2.
Retaining $p=24$ in $K_J$ was essential in the compact diagonal-limit
argument. Merely removing a fibre from a compact set would not prove
compactness. No claim that every unused $p=24$ companion is a limit
of off-$24$ worlds is needed. ∎

## 9. Applicability, remaining original gap and method attribution

**Definition 9.1 (The remaining independent-pair problem).** The
original target permits independently chosen worlds
$W_0,W_1,W_2,W_3\in C(p,v)$ with $p\ne24$ and

$$
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\tag{9.1}
$$

Cross-pair overlap is free; the two common terminal values need not
agree. On the actual arc the $J$ pair is supplied, so the remaining
question is whether $\mathcal R^\times$ is empty or contains an actual
pair. If such a pair exists, S, Corollary 18.2 makes both its endpoints
regular, using the actual $J$ pair at that same base. Unused singular
companions remain part of $K_J$ and are covered by Theorem 7.3.

Theorem 6.2 removes the regular critical-diagonal alternative on this
arc. It does not compare distant local-injectivity neighbourhoods.
Distinct separated incidences, including nontransverse incidences,
remain possible and unresolved. Neither nonemptiness nor emptiness
of $\mathcal R^\times$ is proved here. Other $J$ arcs and other bases
in the full strict real domain have not been exhausted. Thus (9.1),
as a witness-or-full-domain-absence problem, remains open. Immersion,
uniform separation and compactness do not supply global injectivity,
a completed finite pair search or a new child-cardinality bound.

**Definition 9.2 (Source and literature status).** The normalized
regular minors, their degree-$67$ necessary elimination cover, its
complete positive-root exclusions and the exact central-output gap
are `repo-derived` model calculations proved here. The central world,
full-parent singular and $p=24$ immersion, actual arc, compactness and
uniform $p=24$ collision gap are the supplier results of Definition 1.2.
No literature-priority claim accompanies either kind of result.

Fixed-node Lagrange interpolation, Sylvester determinants, polynomial
subresultants, Sturm's real-root theorem, exact rational interval
arithmetic, the inverse function theorem and finite-dimensional
compactness are classical methods. The separation argument of Theorem
8.1 is a classical compact local-injectivity application; it is not the
new elimination content. Standard method references include Berrut and
Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46,
DOI [10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715),
and Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*,
second edition, DOI [10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2).
These references supply general methods, not the source-specific
coefficients or incidence conclusions. The proofs above and the finite
certificate below carry those model-specific assertions.

## 10. Public exact finite certificate

The following single Python program uses integer polynomial arithmetic
and exact rational endpoints. It requires Python with SymPy; no external
data file, oracle, private calculation or floating-point root routine is
an input. `FC` fixes all coefficients of $F$ in descending powers.
The two centre lists are precisely the $L$ coordinate lists in the
$[20,30]$ block of III, (16.7), divided by $10^{20}$.

The polynomial algorithm computes subresultants for efficiency. The
$1080$ fixed integer determinant comparisons, with the degree bounds
in Lemma 4.2, check the entire determinant identities independently of
that algorithm's sign or specialization convention. Exact divisions,
gcds and Sturm arithmetic then supply the finite certificate used in
the proofs. The single terminal message is reached only after every
assertion succeeds.

```python
from fractions import Fraction as Q
from functools import reduce
import sympy as s

t, b, r, e = s.symbols("t b r e")
FC = [
    455647548909844223078998897859465916725196513457155096425068786902952576434018875871493709318400,
    9025960433004279264943149372467574304674121011171829655058229977402313848128645316806994456602160,
    95414993878322482468375257316288423668771257134324314591685987148235046290960665292451965293817136,
    691853652328261458003961505865158327362194479682591351870900534905894309680175051776741586722562208,
    3794896200748372824504929504942510337175196255416066166289546752480928480327885076396194019148266612,
    16790778988834341699323305893268467804761927661940033593066160151944444547781025812231408201393472064,
    63113863244921446341492104376418369820101062816267915874730036282769631584595256897417888329020807566,
    210064223026025168050581779422955405372778663177891566371194580371989482849285299679333819804339015258,
    637417553115769591972553634545578944919639947332077349829503334703539362569769992003560850016576495113,
    1791665693269324595223639417190135537242031696464123804587629876099293471346247230065243664889700681054,
    4687480386726370236787843573052034165644970569711645627089902346493120782918148859406163928710408287255,
    11397473006480145218956776136148235794057721445907021886951255273424489936182563673663977276686432075158,
    25675913850616427841659788187802362233309394150731036275872980625105687226838688211487787503727914486629,
    53488702475204969138775942794344270060286892906233092966201282973819240122479135216977813359092404535664,
    103027964232714819577864075265846810521426108352059661869497246670891705010522156045402184861053352371219,
    183682169678184113038204979003659001625059755127803278148670516838652446555344371576456407473254054465808,
    303539000857770579623415059190584540014045404645441027548386128810226709834683287812009263696556867258816,
    465425353051037764941402986595996374840615600773252566602497158105557609262810978079703649244112920866658,
    662248206027059299102261953233142338835894334396848280658928942835665130293198687648799927150263684576732,
    873297019427894225545691504061636672863554833861602581405720806232209905397524899587637375085161136136156,
    1063746442024633503557708829618701411081643626809827254227632946686492757390791585125009950025656659954398,
    1189309275750596057300207543409721257394051868575808954264882319689644524138068349396700982747685268916732,
    1206566880560916115944757608862030420809454440764961613508962380699984443675698103548173424264352815007836,
    1087167713840411874358761450408889892452562446987070014686448754782195765183617896661503048678856246481520,
    831465707956791688548886316317113586222005985256856023462491447683602960912482212005020083981016637221016,
    475396021263308500837064959673883466824125177335839225505133402793118627878867851770606963813476757898536,
    85165193028327818919033715314314835519854801749459318770318448678029429569186472152395120102182580361632,
    -261114324756307572466870584187384334041506119081265929964406094065722953780317624442403603253981259838736,
    -498740900302351094284429088424599103951956085061624734188128601733240275009048137766806237985449445160184,
    -597535003517470421565696745049035636904761058732909649064869568771739023525283911514310866415560365898240,
    -568717513135151073356482569670573717572940237435460739646076116003460174454222078948958792700194302863664,
    -454930405770632560461741541333978813345653580619608283939522775834745879352557671301052555807505619967520,
    -309703998164817510255721979676892077665930366820640554346705203806159332578782903476756130195550824402896,
    -177262283538844788543526952553628086228873916286288385256679233169991914758517182546236740649040737193792,
    -81388896019916360197774253667848536415562903094549705312344406489112290935794430177134396951831685912800,
    -25578228920258267749262890121096133560908460163231614615923118217478164420655882725441834553315419687936,
    -647618507930208976461559405702757661195408167911171606847402287516617665359002464469250397475412368864,
    6234230330027641861236150834026383952929693685862361765124681853613293209382202306296319565251260587712,
    5469843010940968065519805557057314380852483913897416210660506583422463344007801996673266863945583426176,
    3023280870861672517921049398677653532411782633837860998935733460075772864192162695113756150190348103424,
    1196744912101864132611800819629147170999943935913389350191323655703521822461804770448024872480272674816,
    304476566503827344107866842961988484232686627419919586704419232960354760792446467418973244578396882944,
    5186788143782720886762862534475509992196815063859642881790835811495165253537223960155379389099330048,
    -45072362282375359991327249113387510912596253220126049107115526890535758122498036600387991992558071808,
    -29901783110568050009784972977278286403276974569130696914690608824863343317057710889949509977790526976,
    -12689612991946399060773768845154566035298323053015829409378831168506195520351823402590577281381567488,
    -4090368557542165409385287018172067262758279526670005355166618155405379111593028088695866839582865408,
    -1042990420931790535309362823689567054617668167991206799717043801392783080257442057720132136957005824,
    -210356097133269463164881988652453140197244206619765900074263483547705914908546823146168473794232320,
    -32475411249353348837912000839888245168028821526067592943010528265254727218855417168805026451226624,
    -3462275535725516926287160634968523094492234624507494087752903121191488916149777141824901106499584,
    -149357449089483583662706189559461695399412018460500232133501900646546299398704159930807465279488,
    28504997427987329771145496312187941623986049600290787541792865292431372977465437697129718743040,
    7802540347282790584751125028123756170083303237991884430627839240656324287291549118845249126400,
    1096518828956542999868667658635543500280457266293036650668889583129887305434328923545688604672,
    118134581842134171123381173623805251034696314414802113081073350395353118431808348198426116096,
    11314155724918600448416843671832152958443997439892400492473557747486116094461544696381440000,
    864544019226613655798722390404941066205834967341694895017420243984875071615133587752353792,
    18365292838736643864953664082128379961532511403525326431105810962090627320814462159552512,
    -6397955659392307791587466014205440829072335038506917467780480816241582031258722488025088,
    -887829232429554259267353503521781397505293617052983951149594689388913386271099871821824,
    -38681031771104189007602444044931815306546132679753102555120104754786012582912532152320,
    1608951406684740225662900194893965238513125892209117214165472255363833933858529607680,
    221693105062241980487369407355971501112836239502387116118441956631385739677715660800,
    4205423693389840382321722725002036769922985679239763456256726065622834346983424000,
    -280686446638925780186984409780903207190724062373799374112866828667264402718720000,
    -8747715069471903893629714745174199802450260615803596300658424320695153459200000,
    90329522308128136985602480549785412236973653084074706244266266946699264000000,
]
F = s.Poly.from_list(FC, b)
assert len(FC) == 68 and F.degree() == 67
assert F.content() == 1 and F.LC() > 0

def sign(x):
    return 1 if x > 0 else -1 if x < 0 else 0

def pp(p):
    content, out = p.primitive()
    assert content > 0
    return out

def pp_plus(p):
    out = pp(s.Poly(p, b))
    return out if out.LC() > 0 else -out

j = t + b*(1-t*t)
n = j + t*b
T, U = 1+b, 1+2*b
D = s.Poly(5*((b*b+8*b+4)*j*n-2*T*U*(j+n)), t, b)
A = (8*b-1)*(2+5*b)
C = [-24*D.as_expr()+3*A*j*n, 3*A*n,
     3*(49*b+34)*j*n-54*U*(j+n), 3*A*j]
rows = [[-4,15,-20,10], [-10,36,-45,20], [-20,70,-84,35]]
B = [sum(x*y for x,y in zip(row,C)) for row in rows]
N = [s.Poly(-C[0]+w*v,t,b)
     for w,v in zip([U+n,2*U+n,3*U+2*n],B)]
assert [(p.degree(t),p.degree(b)) for p in [D]+N] == [
    (4,4), (6,4), (6,4), (6,4)]

# Original left products and one whole polynomial, independently of late N.
J = s.Matrix([[0,1],[1,0]])
M = s.Matrix([[0,1],[1,1]])
P = s.Matrix([[t*b,b],[t*(1-t*b),1-t*b]])
product = s.eye(2)
traces = [s.trace(product*P)]
for action in [J,M,J,M,M,M,M]:
    product = action*product
    traces.append(s.trace(product*P))
assert all(s.expand(x-y) == 0 for x,y in zip(
    traces,[1,j,T,n,U,U+n,2*U+n,3*U+2*n]))
Lam = 1+6/T+1/U-4/j-4/n
kappa = 6/T-2/U
H = e*Lam+s.Rational(24,5)*(b-s.Rational(1,8))*kappa
G = [-24-e,-e/j,(s.Rational(27,5)-e)/T,-e/n]
assert s.cancel(-G[0]+4*G[1]-6*G[2]+4*G[3]
                -(18-(24+e))/U-H) == 0
assert s.cancel(D.as_expr()-s.Rational(5,2)*T*U*j*n*Lam) == 0
esol = -s.Rational(24,5)*(b-s.Rational(1,8))*kappa/Lam
assert all(s.cancel(G[i].subs(e,esol)*D.as_expr()-C[i]) == 0
           for i in range(4))
x = s.symbols("x")
lagrange = [s.prod((x-k)/s.Integer(i-k)
                  for k in range(4) if k != i) for i in range(4)]
assert [[s.expand(L).subs(x,k) for L in lagrange] for k in [5,6,7]] == rows

Bt = [D*p.diff(t)-p*D.diff(t) for p in N]
Bb = [D*p.diff(b)-p*D.diff(b) for p in N]
E = []
for i,k in [(0,1),(0,2),(1,2)]:
    quotient, remainder = s.div(Bt[i]*Bb[k]-Bb[i]*Bt[k],D)
    assert remainder.is_zero
    terms = {}
    for (it,ib),coefficient in quotient.terms():
        assert ib-it+7 >= 0 and coefficient % 45 == 0
        terms[(it,ib-it+7)] = coefficient//45
    out = s.Poly.from_dict(terms,(r,b))
    assert (out.degree(r),out.degree(b),out.total_degree(),
            len(out.terms()),out.content()) == (15,17,17,134,1)
    E.append(out)

sequences = [s.subresultants(E[0].as_expr(),E[k].as_expr(),r)
             for k in [1,2]]
assert all([s.degree(p,r) for p in seq] ==
           [15,15,13,12,11,10,9,8,7,6,5,4,3,2,1,0]
           for seq in sequences)
R = [s.Poly(seq[-1],b) for seq in sequences]
assert [p.degree() for p in R] == [285,285]
common = pp_plus(s.gcd(R[0],R[1]))
factor = s.Poly(b**110*(2*b+1)**8*(5*b+2)**17*(8*b-1)**17
                *(5*b*b+2*b+1)*(b*b+8*b+4)**2,b)
assert common == factor*F and common.degree() == 225
quotients = [s.exquo(p,common) for p in R]
assert [p.degree() for p in quotients] == [60,60]
assert s.gcd(*quotients).degree() == 0
linear = s.Poly(next(p for p in reversed(sequences[0])
                     if s.degree(p,r) == 1),r)
a0 = s.Poly(linear.coeff_monomial(r),b)
c0 = s.Poly(linear.coeff_monomial(1),b)
h = pp_plus(s.gcd(a0,c0))
a, c = s.exquo(a0,h), s.exquo(c0,h)
assert h == s.Poly(b**90*(2*b+1)**5*(5*b+2)**14
                  *(8*b-1)**20*(b*b+8*b+4)**2,b)
assert [p.degree() for p in [a0,c0,h,a,c]] == [252,253,133,119,120]
assert all(p.domain.is_ZZ for p in [a0,c0,h,a,c])
assert all(s.gcd(p,q).degree() == 0
           for p,q in [(F,h),(F,a),(F,F.diff()),(a,c)])

# Fixed determinant definitions, including every possible degree drop.
def matrix(f,g,shift,top):
    polys = [s.Poly(r**i*p.as_expr(),r)
             for p in [f,g] for i in range(shift,-1,-1)]
    return s.Matrix([[p.coeff_monomial(r**j)
                      for j in range(top,-1,-1)] for p in polys])

determinants = 0
for beta in range(286):
    specialized = [s.Poly(p.as_expr().subs(b,beta),r) for p in E]
    for k in [1,2]:
        assert matrix(specialized[0],specialized[k],14,29).det(
            method="domain-ge") == R[k-1].eval(beta)
        determinants += 1
    if beta < 254:
        mat = matrix(specialized[0],specialized[1],13,28)
        assert mat[:,list(range(27))+[27]].det(
            method="domain-ge") == a0.eval(beta)
        assert mat[:,list(range(27))+[28]].det(
            method="domain-ge") == c0.eval(beta)
        determinants += 2
assert determinants == 1080

S = 438272*r**4-931328*r**3+540800*r**2-50728*r-853
As, Bs = 64*r*r-64*r-1, 64*r*r-72*r-1
special = [s.Poly(p.as_expr().subs(b,s.Rational(1,8)),r) for p in E]
assert reduce(s.gcd,special).monic() == s.Poly((16*r-9)*S**2,r).monic()
assert s.cancel(Lam.subs(t,r/b).subs(b,s.Rational(1,8))
                -S/(15*As*Bs)) == 0
centre_world = {t:s.Rational(9,2),b:s.Rational(1,8)}
assert D.eval(centre_world) == s.Rational(4762875,65536)
assert s.cancel(Lam).subs(centre_world) == s.Rational(12701,3417)
responses = [s.cancel(p.as_expr()/D.as_expr()) for p in N]
assert [p.subs(centre_world) for p in responses] == [24,s.Rational(591,4),720]
assert s.Matrix([[p.diff(y).subs(centre_world) for y in [t,b]]
                 for p in responses]) == s.Matrix([
    [0,s.Rational(39437184,317525)],
    [0,s.Rational(31382784,317525)],
    [0,-s.Rational(209979456,317525)]])

# Signed primitive Sturm chain. Positive content removal preserves signs.
sturm = [F,pp(F.diff())]
while sturm[-1].degree() > 0:
    p,q = sturm[-2:]
    exponent = p.degree()-q.degree()+1
    sturm.append(pp(-p.prem(q)*sign(q.LC())**exponent))
assert [p.degree() for p in sturm] == list(range(67,-1,-1))

def coefficients(p):
    return [int(x) for x in p.all_coeffs()]

def rational_sign(cs,x):
    numerator,denominator = x.numerator,x.denominator
    value,power = cs[0],denominator
    for coefficient in cs[1:]:
        value = value*numerator+coefficient*power
        power *= denominator
    return sign(value)

sturm_coefficients = [coefficients(p) for p in sturm]
def signs_at(x):
    return "".join("+" if rational_sign(cs,x)>0 else
                   "-" if rational_sign(cs,x)<0 else "0"
                   for cs in sturm_coefficients)

def variations(word):
    word = word.replace("0","")
    return sum(x!=y for x,y in zip(word,word[1:]))

ZERO_WORD = '+--+++--+++--+--++-+++--+--+-----+++-++++---++--+---+----+++--------'
INFINITY_WORD = '++--+++--+++--+++--+++--++-+++---+++---+++-----+----+++++++++-------'
ENDPOINT_WORDS = [['+--+++--+++-++-+++-+++--+--+-----+++-++----+++--+---+----+++--------', '---+++--+++-++-+++-+++--+--+-----+++-++----+++--+---+----+++--------'], ['-++---++---+--++--+---++-++-+++++---+----++---++-++++---++++--------', '+++---++---+--++--+---++-++-+++++---+----++---++-++++---++++--------'], ['+--+++--+++-++--++-+++--+--+-----+++--+++--+++---+---+++++++--------', '---+++--+++-++--++-+++--+--+-----+++--+++--+++---+---+++++++--------'], ['-++---++---+--++--+---++-++-+++++---++---++---+++----+++++++--------', '+++---++---+--++--+---++-++-+++++---++---++---+++----+++++++--------'], ['+--+++--+++--+--++-+++--+--+-----+++---++++---+++---++++++++--------', '---+++--+++--+--++-+++--+--+-----+++---++++---+++---++++++++--------'], ['-++---++--+++-++---+++--++--++---+++---+++-----+----++++++++--------', '+++---++--+++-++---+++--++--++---+++---+++-----+----++++++++--------']]
assert signs_at(Q(0)) == ZERO_WORD
assert "".join("+" if p.LC()>0 else "-" for p in sturm) == INFINITY_WORD
assert (variations(ZERO_WORD),variations(INFINITY_WORD)) == (27,21)

# Closed exact rational interval arithmetic, with no rounding.
def point(x):
    return Q(x),Q(x)

def add(x,y):
    return x[0]+y[0],x[1]+y[1]

def negative(x):
    return -x[1],-x[0]

def multiply(x,y):
    products = [a*b for a in x for b in y]
    return min(products),max(products)

def divide(x,y):
    assert y[0]*y[1] > 0
    return multiply(x,(1/y[1],1/y[0]))

def power(x,n):
    out = point(1)
    for i in range(n):
        out = multiply(out,x)
    return out

def horner(cs,x):
    out = point(0)
    for coefficient in cs:
        out = add(multiply(out,x),point(coefficient))
    return out

def box(poly,x,y):
    first,second = poly.gens
    out = point(0)
    for i in range(poly.degree(first),-1,-1):
        row = [int(poly.coeff_monomial(first**i*second**k))
               for k in range(poly.degree(second),-1,-1)]
        out = add(multiply(out,x),horner(row,y))
    return out

Dc = s.Poly.from_dict({(it,ib-it+2):v for (it,ib),v in D.terms()},(r,b))
Nc = s.Poly.from_dict({(it,ib-it+3):v for (it,ib),v in N[0].terms()},(r,b))
assert all(ib>=0 for (it,ib),v in Dc.terms()+Nc.terms())
left_numerators = [845744,4228383,5311219,6737603,12758053,88676283]
r_bounds = [(0,Q(1,100)),(Q(519,1000),Q(520,1000)),
            (Q(-3,1000),Q(-2,1000)),(Q(-4,1000),Q(-3,1000)),
            (Q(9,10),Q(901,1000)),(Q(964,1000),Q(965,1000))]
p_bounds = [(690,691),(1,2),None,None,(7,8),(57,58)]
a_signs = [-1,1,1,1,1,-1]
d_signs = [-1,1,None,None,-1,-1]
for k,num in enumerate(left_numerators):
    lo,hi = Q(num,10**8),Q(num+1,10**8)
    words = [signs_at(lo),signs_at(hi)]
    assert words == ENDPOINT_WORDS[k]
    assert [variations(w) for w in words] == [27-k,26-k]
    left_sign = rational_sign(FC,lo)
    assert left_sign == (1 if k%2 == 0 else -1)
    assert left_sign*rational_sign(FC,hi) == -1
    for step in range(256):
        midpoint = (lo+hi)/2
        midpoint_sign = rational_sign(FC,midpoint)
        assert midpoint_sign != 0
        if midpoint_sign == left_sign:
            lo = midpoint
        else:
            hi = midpoint
    assert hi-lo == Q(1,10**8*2**256)
    interval = lo,hi
    ai,ci = horner(coefficients(a),interval),horner(coefficients(c),interval)
    assert ai[0]*ai[1] > 0 and sign(ai[0]) == a_signs[k]
    ri = divide(negative(ci),ai)
    assert r_bounds[k][0] < ri[0] <= ri[1] < r_bounds[k][1]
    if p_bounds[k] is not None:
        di = divide(box(Dc,ri,interval),power(interval,2))
        ni = divide(box(Nc,ri,interval),power(interval,3))
        assert di[0]*di[1] > 0 and sign(di[0]) == d_signs[k]
        pi = divide(ni,di)
        assert p_bounds[k][0] < pi[0] <= pi[1] < p_bounds[k][1]

L_T = [-64760914995336,-141100470063114,-72520370219354,
       -145269729373691,-728244036456201,-2245702071706101,
       -7245822024720854,-23692327394115831,-73163432013250704,
       -197029754390717363,-528694944588356620,-584207156211347097,
       4492542348396760978,219625886685223990790]
L_B = [-1723603413335,-1880359411512,11905805971444,
       49433821136737,124147171707093,215207360044166,
       34937022519674,-1562471228161450,-7777580962203138,
       -22939857428839428,-39711075675135058,193301006165304340,
       4916488201945917316,13475282226511291486]
centres = []
for cs in [L_T,L_B]:
    out = Q(0)
    for coefficient in cs:
        out = out*Q(-1,5)+Q(coefficient,10**20)
    centres.append(out)
assert centres == [
    Q(4171523022167046121474201119,1907348632812500000000000000),
    Q(610351562503660641621076147,4882812500000000000000000000)]
rho = Q(1,100000)
tube = [(x-rho,x+rho) for x in centres]
di = box(D,*tube)
assert Q(3337045049,10**8) < di[0] <= di[1] < Q(3340057149,10**8)
vi = divide(box(N[1],*tube),di)
assert Q(65785649,500000) < vi[0] <= vi[1] < Q(13183121189,10**8)
assert 131 < vi[0] <= vi[1] < 132 < Q(591,4)
print("ALL_FINITE_CHECKS_PASSED")
```

## 追加锚（本行以下为增补区）
