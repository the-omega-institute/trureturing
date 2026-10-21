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
## 11. Quantitative collars and the effective collision-chart boundary

**Definition 11.1 (Sources and output region).** Retain the complete worlds of Definition 1.1, the zero-safe parent and whole-gain reconstruction of Definition 2.1, and the actual analytic $J$ arc $v_J$ of [III], Theorem 16.4. Write $e=d-24$, $c=r(1-r)/b$, $j=b+c$, $n=j+r$, $T=1+b$ and $U=1+2b$. Define

$$
\mathcal Q=\left\{(p,v):10\le p\le34,\quad 0\le v\le200,\quad
v\ge\frac{37p+426}{10}\right\}.
\tag{11.1}
$$

The quantifier over a companion means every complete world in $C(p,v)$, including worlds unused by a selected pair. Singular sources, zero drift $d=0$, $e=0$, sampled gain zeros and all gain degrees at most three remain in this quantifier. Write SIII for [III] of Definition 1.2. In addition to those suppliers, use [SIV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md), Theorems 8.2–8.3 and 9.1 for the universal response algebra and coefficient separation, and [SV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md), Section 3 for the zero-safe interval-cover method. SIV's particular rectangle is not substituted for $\mathcal Q$.

### 11.1. A quantitative collar for every companion

**Theorem 11.2 (All-companion source collar).** Every complete world with $(p,v)\in\mathcal Q$ satisfies

$$
\begin{gathered}
10^{-6}\le r\le1-10^{-6},\qquad b\ge10^{-6},\qquad c\ge10^{-6},\\
b<30,\qquad c<10,\qquad \frac1{1024}<j<40,\qquad
|e|<643520<655000.
\end{gathered}
\tag{11.2}
$$

*Proof.* The first two exclusion arguments in SIV, Theorem 8.3, apply to every parent world with $p\ge0$: $b\ge30$ forces $p<0$, and $c\ge10$ forces $p<-7/2$. Thus $b<30$, $c<10$, $j<40$, $n<41$ and $U<61$. These conclusions precede any lower bound on a source coordinate.

For the drift bound use the coefficients of SIV, (9.1), here denoted $A^{\mathrm{IV}},B^{\mathrm{IV}},P_0^{\mathrm{IV}},V_0^{\mathrm{IV}}$ to distinguish them from the coefficients below. Their undivided identities and universal separation give

$$
p-24=P_0^{\mathrm{IV}}+eA^{\mathrm{IV}},\qquad
v-24=V_0^{\mathrm{IV}}+eB^{\mathrm{IV}},\qquad
\max(|A^{\mathrm{IV}}|,|B^{\mathrm{IV}}|)>1/100.
$$

The same source bounds give $|P_0^{\mathrm{IV}}|<1224$ and $|V_0^{\mathrm{IV}}|<31296/5$. Since $|p-24|\le14$ and $|v-24|\le176$,

$$
|e|<100\max\{14+1224,176+31296/5\}=643520.
\tag{11.3}
$$

To prove the lower bound for $j$, suppose $0<z=j\le1/1024$. The rank relation gives $r(1-r)=bc\le z^2/4$. If $r\le1/2$, then $u=r/z\in[0,z/2]$; if $r\ge1/2$, then $a=1-r\in[0,z^2/2]$. Put

$$
q=-\frac{6(8b-1)(5b+2)}{5TU},\qquad e=zw.
$$

Multiplying the parent equation by $z$ gives the following two exact forms:

$$
\begin{array}{c|c|c|c}
 &n&w&(G_0,G_1,G_2,G_3)\\ \hline
r\le1/2&z(1+u)&\displaystyle\frac q{z(1+6/T+1/U)-4-4/(1+u)}
&(-24-e,-w,(27/5-e)/T,-w/(1+u))\\
r\ge1/2&z+1-a&\displaystyle\frac q{z(1+6/T+1/U)-4-4z/n}
&(-24-e,-w,(27/5-e)/T,-zw/n).
\end{array}
\tag{11.4}
$$

For clarity, the exact interval arithmetic in this proof uses $[a,b]+[c,d]=[a+c,b+d]$, negation $-[a,b]=[-b,-a]$, the minimum and maximum of the four endpoint products for multiplication, and reciprocal $[1/b,1/a]$ only when $0\notin[a,b]$. Every rational input is a point interval. Powers mean repeated multiplication. Horner evaluation starts at zero and visits every descending coefficient, including zeros. There is no rounding.

Evaluate (11.4) on $b,z\in[0,1/1024]$, with respectively $u\in[0,1/2048]$ and $a\in[0,1/(2\cdot1024^2)]$. The two denominator intervals are

$$
[-8,-2095615/262272],\qquad
[-8396796/2097151,-511/128].
\tag{11.5}
$$

In particular both divisions are legal, including on these enlarged closed boxes. Set $g_5=-4G_0+15G_1-20G_2+10G_3$ and $g_6=-10G_0+36G_1-45G_2+20G_3$, as in Lemma 2.2, and set $p=24+e+(U+n)g_5$, $v=24+e+(2U+n)g_6$. Interval evaluation in the displayed order gives

$$
\begin{array}{c|c}
 &\text{upper endpoint for }v-37p/10-213/5\\ \hline
r\le1/2&-816054840064061222792519/13140085367094902784000\\
r\ge1/2&-18851570816816384430377401873/689085087558387648823296000.
\end{array}
\tag{11.6}
$$

Both endpoints are less than $-20$, contradicting (11.1). Thus $j>1/1024$.

It remains to prove the four source collars. The following finite rational tree specifies the certificate completely. Its root is the box

$$
B_\varnothing=[0,1]_r\times[0,30]_b\times[1/1024,40]_j,
\qquad \delta=1/10^6.
\tag{11.7}
$$

For a node $B=R\times B_b\times J_0$, first mark it interior if

$$
\inf R\ge\delta,\quad \sup R\le1-\delta,\quad
\inf B_b\ge\delta,\quad \inf J_0-\sup B_b\ge\delta.
\tag{11.8}
$$

An interior node is a terminal node. Otherwise form the exact range $Q_R$ of $r(1-r)$ on $R$: its lower endpoint is the smaller endpoint value, and its upper endpoint is $1/4$ if $1/2\in R$, or the larger endpoint value otherwise. Form successively

$$
J=J_0\cap(B_b+[0,10]),\qquad
J\leftarrow J\cap(B_b+Q_R/B_b)\quad\hbox{if }\inf B_b>0.
\tag{11.9}
$$

An empty intersection marks an excluded terminal node. Next exclude the node if $0\notin B_b(J-B_b)-Q_R$. In all remaining interval expressions use $r\in R$, $b\in B_b$, $j\in J$, $n=J+R$, $T=1+B_b$, $U=1+2B_b$, and the circuits

$$
\begin{aligned}
\Lambda&=1+6/T+1/U-4/J-4/n,&
 d_b&=6(8B_b-1)(5B_b+2)/(5TU),\\
p_0&=24+(U+n)(96-108/T),&
 A_p&=1+(U+n)(4-15/J+20/T-10/n),\\
v_0&=24+(2U+n)(240-243/T),&
 A_v&=1+(2U+n)(10-36/J+45/T-20/n).
\end{aligned}
\tag{11.10}
$$

Here an integer denotes a point interval. The exact parent and reading equations are $\Lambda e=-d_b$, $A_pe=p-p_0$, $A_ve=v-v_0$. Start with $E=[-655000,655000]$. In the order

$$
(\Lambda,-d_b),\quad(A_p,[10,34]-p_0),\quad(A_v,[0,200]-v_0),
\tag{11.11}
$$

replace $E$ by $E\cap H/A$ for a pair $(A,H)$ only when $0\notin A$. An empty intersection excludes the node. With the resulting common $E$, exclude the node if any of the three intervals $AE-H$ excludes zero. Finally exclude it if the upper endpoint of

$$
v_0-\frac{37}{10}p_0-\frac{213}{5}
+\left(A_v-\frac{37}{10}A_p\right)E
\tag{11.12}
$$

is negative. If no terminal condition applies, split the original box $B$, not its contraction, at the rational midpoint of its coordinate of greatest normalized width

$$
\bigl(\operatorname{wid}R,\operatorname{wid}B_b/3,
\operatorname{wid}J_0/4\bigr).
\tag{11.13}
$$

Ties use the first coordinate in this displayed order. Both closed midpoint halves are children. These rules determine every node without choices. Their finite rational data are

| Node or terminal condition | Count |
| --- | ---: |
| All nodes | 169103 |
| Binary splits | 84551 |
| Interior terminal nodes | 31787 |
| Empty first intersection in (11.9) | 4724 |
| Empty second intersection in (11.9) | 4901 |
| Rank residual excluding zero | 14136 |
| Empty common-$e$ intersection | 27652 |
| Common-$e$ residual excluding zero | 128 |
| Negative barrier (11.12) | 1224 |
| Nonterminal nodes at depth 49 | 0 |

The maximum node depth is $49$. Thus there are $52765$ excluded terminal nodes and $31787$ interior terminal nodes, and $169103=2(52765+31787)-1$. The table is obtained by the rational endpoint rules (11.7)–(11.13); these rules are also a finite definition of every leaf and every rational inequality represented by the counts.

Every contraction contains every actual source in its original node: (11.9) follows from $c\in(0,10)$ and $bc=r(1-r)$, and (11.11) uses the same actual $e$ in all equations. All $J,n,T,U$ intervals have positive lower endpoints. Coefficient intervals containing zero are never divided. Every excluded node contradicts a necessary equation or (11.1), whereas (11.8) gives all four collars on every interior node, since $c=j-b$. Closed midpoint children cover their parent. The finite tree therefore covers the root with precisely these two types of terminal node and proves the four collars. Neither a nonzero drift nor regularity nor a nonzero gain sample has entered the argument. ∎

**Corollary 11.3 (Every actual-arc companion is covered).** For every $p\in[10,34]$, every complete world in $C(p,v_J(p))$ satisfies (11.2).

*Proof.* SIII, Theorem 22.3 gives $v_J(p)>(37p+426)/10$. To check the remaining output bound use precisely the $\tau_L,b_L$ descending coefficient rows of SIII, (16.7), with denominator $10^{20}$ and radius $\rho=10^{-5}$. For each of the three parameter blocks $[L,H]$, put

$$
I_k=[-1+2k/1024,-1+2(k+1)/1024],\quad
p(u)=(L+H)/2+(H-L)u/2,\quad 0\le k\le1023,
$$

and let $X_t=\widehat\tau_L(I_k)+[-\rho,\rho]$, $X_b=\widehat b_L(I_k)+[-\rho,\rho]$. Evaluate the integer $D,N_v$ arrays in SIII, Lemma 16.3 by descending $b$ Horner inside descending $t$ Horner, retaining all seven rows and five columns. The exact interval rules above give the following strict rational enclosures over all $1024$ cells of each block:

$$
\begin{array}{c|c|c}
[L,H]&D&N_v/D\\ \hline
[10,20]&(4728407/125000,44307113/10^6)&(16368057/200000,117541097/10^6)\\
[20,30]&(23208057/10^6,9490353/250000)&(29153959/250000,31126333/200000)\\
[30,34]&(7678107/500000,14607/625)&(76502951/500000,85080543/500000).
\end{array}
\tag{11.14}
$$

In particular the denominators are positive, and the three response ranges lie respectively in $(81,118)$, $(116,156)$ and $(153,171)$. SIII, Lemma 16.3 places the actual endpoint in these boxes; its response is $v_J$. Thus $0<v_J<200$ and the actual arc lies in $\mathcal Q$. Theorem 11.2 applies to all its companions, regardless of whether they are among the two endpoints defining the arc. Arc existence, analyticity, the scalar barrier and the parameter-to-world correspondence are reused from SIII, Sections 16 and 22, rather than inferred from the response enclosures. ∎

### 11.2. A zero-safe comparator and an explicit source tube

**Definition 11.4 (Polynomial comparator).** In the regular polynomial circuit of Lemma 2.2 write $N_p=N_0$, $N_v=N_1$ and $N_m=N_2$. Define polynomial quotients

$$
S(t,b)=-\frac{N_p-24D}{3(8b-1)},\qquad
C(t,b)=-\frac{5N_m-32N_v+1128D}{3(8b-1)}.
\tag{11.15}
$$

These expressions mean exact polynomial division, including evaluation at $b=1/8$. Their remainders are zero. Define

$$
\begin{aligned}
\mathscr H(r,b)={}&14b^6+(95-73r)b^5+(47r^2-39r+30)b^4
+r(147r^2-232r+105)b^3\\
&+2r(1-r)(44r^2-55r+15)b^2-64r^3(1-r)^2b-32r^3(1-r)^3,\\
C_*(r,b)={}&-1055b^6+(5815r-7529)b^5+(-5140r^2+5260r-3102)b^4\\
&+(-8795r^3+13798r^2-6351r)b^3
 +(7015r^4-16924r^3+13011r^2-3102r)b^2\\
&+(1920r^5-1610r^4-2540r^3+2230r^2)b
 -960r^6+2880r^5-2880r^4+960r^3.
\end{aligned}
\tag{11.16}
$$

The symbol $\mathscr H$ is the source sextic of O, (12.2), and SII, (25.7), distinct from the full-parent equation $H(r,b,e)$ in (2.1). Exact substitution gives

$$
b^3 S(r/b,b)=\mathscr H(r,b),\qquad
b^3 C(r/b,b)=C_*(r,b).
\tag{11.17}
$$

For two sources define

$$
F(r,s,b_1,b_2)=C_*(s,b_2)\mathscr H(r,b_1)
-C_*(r,b_1)\mathscr H(s,b_2).
\tag{11.18}
$$

**Lemma 11.5 (Comparator on every source stratum).** At every strict parent world,

$$
\begin{aligned}
(5b+2)jn(p-24)&=eS(r/b,b),\\
(5b+2)jn(5m-32v+1128)&=eC(r/b,b).
\end{aligned}
\tag{11.19}
$$

Consequently $p\ne24$ implies $eS\ne0$, and at fixed off-$24$ readings $(p,v)$ two companions have equal $m$ if and only if $F=0$.

*Proof.* Use the whole-gain samples (2.2) and the three interpolation rows of Lemma 2.2 before solving the parent for $e$. Denote these ambient readings by $\widetilde p,\widetilde v,\widetilde m$, and put $R_0=e\Lambda+d_b$, with $d_b$ as in (11.10). Direct multiplication gives the stronger ambient identities

$$
\begin{aligned}
(5b+2)jn(\widetilde p-24)-eS(r/b,b)
 &=10Ujn(U+n)R_0,\\
(5b+2)jn(5\widetilde m-32\widetilde v+1128)-eC(r/b,b)
 &=-10Ujn(170b+30n+89)R_0.
\end{aligned}
\tag{11.20}
$$

One can reproduce these identities by keeping $b,j,n,e$ independent in the interpolated readings, subtracting the displayed multiples of $R_0$, and then substituting $j=t+b(1-t^2)$, $n=j+tb$. The remaining coefficients of $e$ are exactly the two polynomial quotients (11.15). Thus the identities use no division by $\Lambda$, $e$, $8b-1$ or a gain value. On the parent $R_0=0$, proving (11.19), including singular worlds. Since $(5b+2)jn>0$, the first identity gives $eS\ne0$ when $p\ne24$. Dividing the two identities and using (11.17) gives

$$
m=\frac{32}{5}v-\frac{1128}{5}
+\frac{p-24}{5}\frac{C_*(r,b)}{\mathscr H(r,b)}.
\tag{11.21}
$$

The two nonzero sextic denominators allow cross multiplication, yielding exactly (11.18). This last equivalence is restricted to $p\ne24$. ∎

**Theorem 11.6 (Explicit mirror-tube exclusion).** On the source tube

$$
\begin{gathered}
267/1000\le r\le277/1000,\qquad |s+r-9/8|\le10^{-5},\\
|b_1-1/8|\le10^{-5},\qquad |b_2-1/8|\le10^{-5},
\end{gathered}
\tag{11.22}
$$

one has $F>1/40$. Hence no pair of companions at common $(p,v)$ with $p\ne24$ and equal $m$ has a labeling satisfying (11.22). The same exclusion holds for the reversed labeling.

*Proof.* On the central segment $s=9/8-r$, $b_1=b_2=1/8$, exact expansion of (11.16)–(11.18) gives

$$
\begin{aligned}
F_0(r)=\frac{21(16r-9)(64r^2-72r-1)}{68719476736}
\bigl(&16777216r^6-56623104r^5+93622272r^4\\
&-91210752r^3+37316032r^2+622224r-230227\bigr).
\end{aligned}
\tag{11.23}
$$

Here is the exact Bernstein convention for all coefficient bounds in this section. If a degree-$q$ polynomial $f$ has $f(a+(b-a)x)=\sum_{i=0}^q c_ix^i$, its Bernstein coefficients on $[a,b]$ are

$$
\mathcal B_k(f;a,b)=\sum_{i=0}^k c_i\frac{\binom{k}{i}}{\binom{q}{i}},
\qquad 0\le k\le q.
\tag{11.24}
$$

Expansion in $\binom qk x^k(1-x)^{q-k}$ proves this formula by coefficient comparison. These basis functions are nonnegative and sum to one on $[0,1]$, so their coefficient minimum is a lower bound for $f$. For the degree-nine polynomial (11.23), $a=267/1000$, $b=277/1000$, the ten rational coefficients (11.24) have their minimum at $k=0$, namely

$$
\frac{14656469065762145135535204561}
{512000000000000000000000000000}>\frac1{35}.
\tag{11.25}
$$

For the perturbation, use the rectangular intervals

$$
R=[267/1000,277/1000],\quad
S_0=[9/8-277/1000-10^{-5},9/8-267/1000+10^{-5}],\quad
B=[1/8-10^{-5},1/8+10^{-5}].
$$

For any of $\mathscr H,C_*$ or their derivatives, expand in powers of $r,b$, pad the coefficient matrix to indices $0\le i,j\le6$, and evaluate descending $b$ Horner inside descending $r$ Horner. Use the exact interval operations specified after (11.4). Denote these enclosures on $(R,B)$ by $H_1,C_1,H_{1b},C_{1b}$ and on $(S_0,B)$ by $H_2,C_2,H_{2b},C_{2b},H_{2s},C_{2s}$. Product-rule enclosures are

$$
\begin{aligned}
F_{b_1}&\in C_2H_{1b}-C_{1b}H_2\subset(-11,19),\\
F_{b_2}&\in C_{2b}H_1-C_1H_{2b}\subset(-24,19),\\
F_s&\in C_{2s}H_1-C_1H_{2s}\subset(-62,58).
\end{aligned}
\tag{11.26}
$$

All inclusions follow by rational multiplication and addition of the explicitly defined coefficient matrices; in particular they imply $|F_{b_1}|<20$, $|F_{b_2}|<25$, $|F_s|<65$. For a point of (11.22), hold $r$ fixed and join it to $(r,9/8-r,1/8,1/8)$. The segment stays in the rectangle, and each of its three varying coordinates changes by at most $10^{-5}$. The mean-value formula gives

$$
F>\frac1{35}-(20+25+65)10^{-5}
=\frac{1923}{70000}>\frac1{40}.
\tag{11.27}
$$

Lemma 11.5 excludes an off-$24$ collision. Reversing labels changes the sign of the comparator and transports the stated tube to its reversed image; nonvanishing is preserved. ∎

**Proposition 11.7 (Correspondence with the actual mirror sources).** The tube (11.22) contains the two actual $p=24$ K-mirror sources in the labeling with smaller first coordinate. Its off-$24$ interpretation does not exclude that $p=24$ collision and does not specify a numerical width in $p$.

*Proof.* Lemma 7.2 gives $131<v_J(24)<132$. Set

$$
n_0=\frac{v_J(24)-84}{24}\in(47/24,2),\qquad
\Delta=\sqrt{\frac{85/32-n_0}{2}},\qquad
r_0=\frac9{16}-\frac\Delta2,\quad
s_0=\frac9{16}+\frac\Delta2.
\tag{11.28}
$$

On the published K family, $b=1/8$, $e=0$, $n(r)=1/8+9r-8r^2$ and $(p,v,m)=(24,84+24n,312+768n/5)$; these are SII, (25.5)–(25.6). Thus the two distinct sources in (11.28), each with $b=1/8$, are complete companions with equal $m$. Since

$$
(571/1000)^2<21/64<\Delta^2<67/192<(591/1000)^2,
$$

one has $267/1000<r_0<277/1000$ and $s_0+r_0=9/8$. This proves the tube correspondence. Equation (11.21) used $p\ne24$, so $F>1/40$ at the mirror is consistent with their actual equality of $m$ at $p=24$. The tube is a source-coordinate statement; no quantitative inverse control from $p$ to sources has been inferred. ∎

### 11.3. Actual companion branches with unbounded chart slope

**Theorem 11.8 (Blowup on the broader common-child carrier).** There are two analytic strict complete branches $W_r(p),W_s(p)\in C(p,v_J(p))$ through the mirrors in (11.28). Write

$$
\beta=(b_s-b_r)'(24),\qquad \mu=(m_s-m_r)'(24).
$$

Then

$$
\frac1{600}<-\beta<\frac1{250},\qquad
\frac1{10}<\mu<\frac14,\qquad
-65<\frac\mu\beta<-61.
\tag{11.29}
$$

For $p\ne24$ sufficiently close to $24$, order these two branches by $b_y>b_x$ and set

$$
h=b_y-b_x,\qquad
\sigma=\frac{r_y/b_y-r_x/b_x}{h}.
\tag{11.30}
$$

They satisfy

$$
\frac h{|p-24|}\longrightarrow-\beta>0,\qquad
|\sigma|\longrightarrow\infty,\qquad
\frac{m_y-m_x}{h}\longrightarrow\frac\mu\beta\in(-65,-61).
\tag{11.31}
$$

These branches have unequal $m$ at every sufficiently close off-$24$ parameter. Thus they rule out an $h$ floor or a slope cap on the broader carrier of distinct companions matching only $(p,v_J(p))$.

*Proof.* Use the full-parent chart from O, Lemma 16.2 and SII, (27.4). At every K source the dependent coordinate $b=b(r,e)$ exists analytically because the derivative of the parent with respect to $b$ is $448/25$. It obeys

$$
b(r,0)=1/8,\quad b_r(r,0)=0,\quad
b_e(r,0)=-25\Lambda(r,1/8)/448.
\tag{11.32}
$$

This chart includes singular source parameters. Let $k=m-32v/5$. On K, $p_r=k_r=0$ and $v_r=24n'(r)$, with $n'(r)=9-16r$. The derivatives in the $e$ direction are the full-parent derivatives of SII, (27.5), explicitly

$$
\begin{aligned}
\Lambda&=107/15-4/j-4/n,& b_e&=-25\Lambda/448,\\
\gamma_5&=(-256+85/j+190/n)/21,&
\gamma_6&=(-185+48/j+160/n)/7,\\
\gamma_7&=-48+10/j+45/n,&
\alpha:=p_e&=1+(n+5/4)\gamma_5,\\
\eta:=k_e&=-27/5+(15/4+2n)\gamma_7
 -(32/5)(5/2+n)\gamma_6-(768/5)b_e.
\end{aligned}
\tag{11.33}
$$

They follow by differentiating the same four gain samples: their $e$ derivatives in this chart are $(-1,-1/j,-\theta/T,-1/n)$, where $T=9/8$ and $\theta=1+(24/5)b_e$. Apply the three fixed-node rows, then differentiate the response traces. The terms involving $n_e$ cancel from $k_e$ because $2(384/5)-(32/5)24=0$. This yields (11.33), so no drift or gain parameter was independently reselected.

For an indeterminate $n$ define

$$
\begin{aligned}
P(n)={}&16777216n^6-13631488n^5-53190656n^4+34142752n^3
 +41464676n^2-21500400n-225625,\\
B(n)={}&716n^2+31n-900,\\
R(n)={}&-8192n^3+119952n^2-12320n-57875.
\end{aligned}
\tag{11.34}
$$

Substitute $r=9/16-\Delta/2$, $s=9/16+\Delta/2$, $j_r=n-r$, $j_s=n-s$ into (11.33). Rational collection using $\Delta^2=(85/32-n)/2$ gives

$$
\begin{aligned}
\alpha(r)\alpha(s)&=\frac{P(n)}{1764n^2(64n^2-64n-1)},\\
\frac{b_e(s)}{\alpha(s)}-\frac{b_e(r)}{\alpha(r)}
 &=-\frac{175nB(n)\Delta}{P(n)},\\
\frac{\eta(s)}{\alpha(s)}-\frac{\eta(r)}{\alpha(r)}
 &=\frac{336nR(n)\Delta}{5P(n)}.
\end{aligned}
\tag{11.35}
$$

The quadratic $B$ is the polynomial denoted $D(n)$ in SIII, Lemma 14.2; the cubic $R$ is SII, (28.1). Their use in the normalized derivative differences is through (11.35). These are exact identities in the quadratic rational algebra with the displayed relation for $\Delta^2$: clear denominators, replace each even power of $\Delta$ by the corresponding power of $(85/32-n)/2$, and compare the constant and linear coefficients. Formulae (11.33)–(11.35) therefore specify every coefficient of the derivative calculation.

Using (11.24) on $n\in[47/24,2]$ gives the finite bounds

$$
\begin{array}{c|c|c|c}
f&\text{degree}&\min_k\mathcal B_k(f)&\max_k\mathcal B_k(f)\\ \hline
P&6&842710954799/5832&182258007\\
B&2&274553/144&2026\\
R&3&34181767/108&331757\\
48R-61\cdot125B&3&476086&31388821/48\\
65\cdot125B-48R&3&43110037/144&536914.
\end{array}
\tag{11.36}
$$

In particular $P>0$ and $64n^2-64n-1>0$ on this interval. Thus both $\alpha(r_0),\alpha(s_0)$ are nonzero. Also $n'(r_0)=8\Delta$ and $n'(s_0)=-8\Delta$ are nonzero. The $(e,r)$ Jacobian determinant of $(p,v)$ is $24\alpha n'$, since $p_r=0$. The analytic implicit-function theorem applied separately at the two mirrors gives the asserted branches for the same prescribed analytic $v_J(p)$. Strictness persists in a neighbourhood, and the whole-gain reconstruction gives actual complete worlds on both branches.

Differentiating $p(W_i(p))=p$ gives $e_i'=1/\alpha_i$ at $24$. Since $b_r=k_r=0$ there,

$$
b_i'(24)=b_{e,i}/\alpha_i,\qquad
m_i'(24)=\frac{32}{5}v_J'(24)+\eta_i/\alpha_i.
$$

The common $v_J'$ term cancels in their difference. Equations (11.35) at $n=n_0$ prove

$$
\beta=-175n_0B(n_0)\Delta/P(n_0),\qquad
\mu=336n_0R(n_0)\Delta/(5P(n_0)),\qquad
\mu/\beta=-48R(n_0)/(125B(n_0)).
\tag{11.37}
$$

For explicit numerical bounds, $57/100<\Delta<3/5$, since $(57/100)^2<21/64$ and $67/192<(3/5)^2$. Applying the positive bounds in (11.36) to (11.37) gives the enclosing intervals

$$
\begin{aligned}
\frac{1716230803}{839844896256}
 &<-\beta<\frac{354468960}{120387279257},\\
\frac{213670225517}{1640322063000}
 &<\mu<\frac{557224365312}{3009681981425}.
\end{aligned}
\tag{11.38}
$$

These imply the first two bounds in (11.29); positivity of the last two rows of (11.36) implies the ratio bounds.

Finally $b_s-b_r=\beta(p-24)+o(|p-24|)$, $m_s-m_r=\mu(p-24)+o(|p-24|)$, whereas $r_s/b_s-r_r/b_r\to8\Delta\ne0$. Sorting by $b$ gives $h=|b_s-b_r|$, proving the first two limits in (11.31). For either sorting, $(m_y-m_x)/h=(m_s-m_r)/(b_s-b_r)$, proving the third. Since $\mu\ne0$, the unsorted $m$ difference is nonzero for every sufficiently close off-$24$ parameter. These are companion branches in a common acquired child, with an actual $J$ pair also present, but they are not $M$ collisions off $24$. ∎

### 11.4. The collision chart and its missing effective gap

**Definition 11.9 (Unequal-$b$ collision chart and coverage premise).** For two distinct actual off-$24$ equal-$m$ companions on the arc whose $b$ coordinates differ, label them so $b_y>b_x$ and set

$$
t=r_x/b_x,\quad b=b_x,\quad h=b_y-b_x>0,\quad
\sigma=(r_y/b_y-t)/h,\qquad
x=(t,b),\quad y=(t+h\sigma,b+h).
\tag{11.39}
$$

The strict source guards are $t>0$, $b>0$, $tb<1$ at $x$, and the same three inequalities at $y$. To extend this chart to all distinct off-$24$ collisions, the supplied fixed-$b$ injectivity conclusion is used in precisely the following form: distinct complete worlds with common $(p,v,m)$ and $p\ne24$ have unequal $b$. This conclusion is a premise of that coverage assertion, not a new quantitative result here. The chart and Theorem 11.8 require no unpublished source or fixed-$b$ theorem beyond this explicitly stated scope. The selected collision endpoints are regular by [S], Corollary 18.2, because the actual $J$ pair exists; unused companions retain all source strata.

For each of the three pairs $(f,g)=(N_p,D),(N_v,D),(C,S)$ define the polynomial

$$
R_{f,g}(t,b,h,\sigma)=
\frac{f(t+h\sigma,b+h)g(t,b)-f(t,b)g(t+h\sigma,b+h)}h.
\tag{11.40}
$$

The numerator vanishes identically at $h=0$, so division is exact in $\mathbb Q[t,b,h,\sigma]$. In the order just given, the quotients have respectively $1518,1518,853$ monomials and total degrees $23,23,21$. These data are obtained directly from the coefficient circuits (2.3) and (11.15); every remainder is zero. In particular the third quotient uses $C,S$ in $(t,b)$ coordinates, not $C_*,\mathscr H$ evaluated as if their first variable were $t$.

**Proposition 11.10 (Exact chart correspondence and quantitative boundary).** With the coverage premise of Definition 11.9, the actual off-$24$ collision relation on the arc is in bijection with solutions of

$$
\begin{gathered}
10\le p\le34,\quad p\ne24,\quad h>0,\quad
D(x)D(y)\ne0,\quad\text{both strict source guards},\\
N_p(x)/D(x)=p,\qquad N_v(x)/D(x)=v_J(p),\\
R_{N_p,D}=R_{N_v,D}=R_{C,S}=0,
\end{gathered}
\tag{11.41}
$$

with one ordering bit recovering both original endpoint orderings. Every such solution satisfies

$$
10^{-6}\le b<30,\qquad
\frac1{30000000}<t<10^6,\qquad
0<h<30-10^{-6},\qquad |h\sigma|<10^6.
\tag{11.42}
$$

*Proof.* A collision has unequal $b$ by the stated premise, and its selected endpoints are regular by S, Corollary 18.2. Sorting and (11.39) give unique chart coordinates; equality of $p,v$ gives the first two polynomial residuals and Lemma 11.5 gives the third. Conversely, the regular reconstruction of Lemma 2.2 at both guarded points gives two complete worlds. The first two residuals give the same $(p,v_J(p))$ at both, and the third gives equal $m$ by Lemma 11.5. The positive $h$ makes their sources distinct. This proves both directions and uniqueness. The only analytic input in (11.41) is the given function $v_J$; the three divided differences are polynomial.

Theorem 11.2 applies to both endpoints by Corollary 11.3. Thus $r\ge10^{-6}$ and $b<30$ give $t>1/30000000$, while $r<1$ and $b\ge10^{-6}$ give $t<10^6$. The $b$ bounds give the bound on $h$, and both $t$ coordinates belong to $(0,10^6)$, giving $|h\sigma|<10^6$. ∎

**Definition 11.11 (The effective gap still required).** The unresolved effective collision-chart problem is to exhibit a rational $\eta>0$ and prove that (11.41) has no solution with $0<h<\eta$, retaining all original world strata and the actual arc. Such a proof would combine with (11.42) to give $|\sigma|<10^6/\eta$ on actual collisions. Theorem 11.6 quantifies one source neighbourhood of distinct mirror limits; it supplies neither this $\eta$ nor a numerical $p=24$ exclusion width.

The diagonal part still requires quantitative local-injectivity radii in full-parent charts over all actual companions, including singular source charts. The separated, nearly equal-$b$ part outside (11.22) still requires a robust unequal-$b$ residual bound with all exceptional factors and degree drops retained. Exact injectivity at $h=0$, including positivity of an elimination polynomial there, is not such a perturbation bound. Theorem 11.8 proves why replacing the actual collision set by all $(p,v)$-matching pairs cannot supply the missing bound.

The qualitative counterpart is the existing compactness inference: Theorems 7.3 and 8.1 and Corollaries 8.2–8.3 give a compact off-$24$ collision relation separated from the diagonal. With the fixed-$b$ premise, its $b$-ordered half is closed, since $h=0$ cannot occur on that relation. If nonempty, continuous $h$ has a positive minimum and continuous $\sigma$ has a finite maximum in absolute value; if empty, these bounds are vacuous. This is reuse of compactness and the supplied injectivity conclusion, not a computed rational bound.

The source collar, polynomial mirror tube and branch asymptotics are model-specific repository-derived calculations. Their methods are fixed-node interpolation, exact rational interval inclusion, finite covering, the Bernstein convex-hull identity (11.24), and the analytic implicit-function theorem. The source correspondence is O, Sections 2, 12 and 16; F, Sections 30–33; S, Corollary 18.2; SII, Sections 25–29; SIII, Lemma 14.2 and Sections 16 and 20–23; SIV, Sections 8–9; SV, Section 3; and the preceding VI results. No claim of literature priority attaches to these calculations. The original independent-pair objective remains unresolved: these results provide neither an actual off-$24$ $M$ witness over the arc, nor arcwise or global absence, nor a completed whole-domain target. The two selected terminal pairs may still overlap or be disjoint, and their terminal values need not coincide.

## 追加锚（本行以下为增补区）

## 12. Exact common-root lifts of the critical cover

**Definition 12.1 (The second linear subresultant).** Let $F\in\mathbb Z[b]$
be the univariate polynomial of Lemma 4.2, with the coefficient list
given there. Retain $E_0,E_1,E_2,R_1,R_2,a_0,c_0,h,a,c$ exactly as in
Definitions 3.1 and 4.1. In particular $a_0=ha$ and $c_0=hc$.
For the ordered pair $(E_0,E_2)$ form the $28$ rows

$$
r^{13}E_0,\ldots,E_0,\quad r^{13}E_2,\ldots,E_2
\tag{12.1}
$$

in columns $r^{28},r^{27},\ldots,1$. Let $a_2$ be the determinant
retaining columns $r^{28},\ldots,r^2,r$, and $c_2$ the determinant
retaining columns $r^{28},\ldots,r^2,1$. Thus

$$
L_2(r,b)=a_2(b)r+c_2(b).
\tag{12.2}
$$

The row order and column order are part of the definition. Neither
the initial leading coefficients nor a factor of $a_2,c_2$ is removed.
Write $\ell_k=\operatorname{lc}_rE_k$ for $k=0,1,2$.
All remainders and gcds below are in $\mathbb Q[b]$; a gcd is normalized
to be monic. For $V\ne0$, $\operatorname{rem}_V U$ denotes the unique
polynomial of degree less than $\deg V$ for which
$U-QV=\operatorname{rem}_V U$ for some $Q\in\mathbb Q[b]$.

**Lemma 12.2 (Finite specialization certificates).** The polynomials
of Definition 12.1 satisfy

$$
\begin{array}{c|c}
U&\operatorname{rem}_F U\\ \hline
R_1&0\\
R_2&0\\
ac_2-ca_2&0
\end{array}
\qquad
\begin{array}{c|c}
U&\gcd(F,U)\\ \hline
h&1\\
a_0&1\\
a&1\\
a_2&1\\
\ell_0&1\\
\ell_1&1\\
\ell_2&1
\end{array}.
\tag{12.3}
$$

Consequently every complex root $\beta$ of $F$ preserves the initial
$r$ degrees $15$ of all three $E_k$. Both linear subresultants in
(4.2) and (12.2) are nonzero at $b=\beta$.

*Proof.* The first two remainder identities and the gcds with $h,a,a_0$
follow already from (4.3), using $a_0=ha$. Here are finite coefficient
operations specifying the remaining identities, including their
normalization. Expand the integer circuit (2.3), form (3.1), and use
the exact divisions (3.2) to obtain $E_0,E_1,E_2$. Extract their
$r^{15}$ coefficients to obtain $\ell_0,\ell_1,\ell_2$. Form the two
determinants of (12.1) and the determinants of Definition 4.1.
For each remainder in (12.3), polynomial division consists of repeatedly
replacing a nonzero current polynomial $U$ of degree at least $67$ by

$$
U-\frac{\operatorname{lc}U}{\operatorname{lc}F}
       b^{\deg U-67}F.
\tag{12.4}
$$

For a gcd entry use the successive pairs
$(U,V)\mapsto(V,\operatorname{rem}_V U)$, starting with $(F,U)$,
and normalize the last nonzero constant or polynomial to be monic.
These exact operations give the following coefficient equalities and
terminal degrees:

$$
\begin{gathered}
\operatorname{rem}_F(ac_2)=\operatorname{rem}_F(ca_2),\\
\deg\gcd(F,a_2)=0,\qquad
(\deg\gcd(F,\ell_0),\deg\gcd(F,\ell_1),
 \deg\gcd(F,\ell_2))=(0,0,0).
\end{gathered}
\tag{12.5}
$$

Thus (12.3) is a finite collection of rational coefficient identities
whose inputs are (2.3), (3.2), the fixed determinants and the existing
coefficient list of $F$. No choice of a root or a tolerance enters
these operations. Determinants may equivalently be expanded by
$\det A=\sum_\sigma\operatorname{sgn}(\sigma)
\prod_j A_{j,\sigma(j)}$; thus the operations determine every
coefficient without an additional polynomial array.

If $F(\beta)=0$, a Bézout identity for each gcd in (12.3) gives
$h(\beta),a_0(\beta),a(\beta),a_2(\beta),\ell_k(\beta)\ne0$.
In particular no initial $r$ degree drops, and the coefficients of
$r$ in both specialized linear subresultants are nonzero. ∎

**Lemma 12.3 (Sufficiency of the algebraic lift).** For every complex
root $\beta$ of $F$, the specialized polynomials
$E_0(r,\beta),E_1(r,\beta),E_2(r,\beta)$ have the unique common root

$$
\rho=-\frac{c(\beta)}{a(\beta)}.
\tag{12.6}
$$

Each of the pairs $(E_0,E_1)$ and $(E_0,E_2)$ has specialized gcd
of degree exactly one. In particular the lift (12.6) is real whenever
$\beta$ is real.

*Proof.* Use the classical subresultant gcd criterion over
$\mathbb C$: for two polynomials whose initial degrees are preserved,
vanishing of the resultant and nonvanishing of the degree-one
subresultant imply that the gcd has degree exactly one, and that
subresultant is a nonzero scalar multiple of the gcd. The criterion
uses the fixed determinantal subresultants of Definitions 4.1 and
12.1; a common nonzero normalization scalar does not change its root.
A reference for this algebraic criterion is Basu, Pollack and Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapter 8,
[DOI 10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2).

Lemma 12.2 supplies every specialization hypothesis. For $(E_0,E_1)$
the linear gcd has root $-c_0(\beta)/a_0(\beta)$; cancellation of
$h(\beta)\ne0$ gives (12.6). For $(E_0,E_2)$ its root is
$-c_2(\beta)/a_2(\beta)$. The third remainder identity of (12.3)
and $a(\beta)a_2(\beta)\ne0$ make these two roots equal. Hence the
same $\rho$ is a zero of all three $E_k$, and uniqueness follows
from either linear gcd. This also explains why two vanishing
resultants alone would not have supplied sufficiency: their common
roots with $E_0$ would still have to be identified. All coefficients
in (12.6) are real at a real $\beta$, with nonzero denominator. ∎

## 13. The four actual critical worlds on the entire off-twenty-four parent

**Definition 13.1 (Four algebraic complete worlds).** For

$$
(q_1,q_2,q_3,q_4)=(845744,4228383,12758053,88676283)
\tag{13.1}
$$

let $b_i$ be the unique root of $F$ in
$I_i=(q_i/10^8,(q_i+1)/10^8)$, as isolated in Lemma 5.2. Set

$$
r_i=-c(b_i)/a(b_i),\qquad t_i=r_i/b_i.
\tag{13.2}
$$

Using the polynomials $C_0,\ldots,C_3,D$ of Lemma 2.2 at $(t_i,b_i)$,
define

$$
\begin{aligned}
P_i&=\begin{pmatrix}t_ib_i&b_i\\t_i(1-t_ib_i)&1-t_ib_i\end{pmatrix},
&d_i&=-C_0(t_i,b_i)/D(t_i,b_i),\\
g_i(s)&=\frac1{D(t_i,b_i)}\sum_{k=0}^3 C_k(t_i,b_i)
               \prod_{\substack{0\le l\le3\\l\ne k}}\frac{s-l}{k-l},
&W_i&=(P_i,g_i,d_i).
\end{aligned}
\tag{13.3}
$$

Write $p_i=p(W_i)$, $v_i=v(W_i)$, $m_i=m(W_i)$, $a_i=a(W_i)$.
These are definitions by polynomial equations, rational functions and
isolating intervals, rather than by approximate coordinates.

**Lemma 13.2 (Strict lift and response certificates).** The four
worlds of Definition 13.1 are well defined and belong to $\mathcal H$.
The following are strict rational enclosures; each finite decimal
denotes the displayed exact rational number.

| $i$ | $r_i$ | $b_i$ | $\operatorname{sign}D(t_i,b_i)$ |
| --- | --- | --- | --- |
| $1$ | $(0.0084901253,0.0084901254)$ | $(0.0084574469,0.0084574470)$ | $-$ |
| $2$ | $(0.5195359430,0.5195359431)$ | $(0.0422838313,0.0422838314)$ | $+$ |
| $3$ | $(0.9005088162,0.9005088163)$ | $(0.1275805397,0.1275805398)$ | $-$ |
| $4$ | $(0.9648629529,0.9648629530)$ | $(0.8867628398,0.8867628399)$ | $-$ |

| $i$ | $p_i$ | $v_i$ | $d_i$ |
| --- | --- | --- | --- |
| $1$ | $(690.595905,690.595906)$ | $(1416.434664,1416.434665)$ | $(-659.603336,-659.603335)$ |
| $2$ | $(1.830485,1.830486)$ | $(175.912050,175.912051)$ | $(24.243210,24.243211)$ |
| $3$ | $(7.283036,7.283037)$ | $(61.494372,61.494373)$ | $(27.263115,27.263116)$ |
| $4$ | $(57.070846,57.070847)$ | $(305.047970,305.047971)$ | $(28.731355,28.731356)$ |

| $i$ | $m_i$ | $a_i$ |
| --- | --- | --- |
| $1$ | $(3014.237990,3014.237991)$ | $(1548.191707,1548.191708)$ |
| $2$ | $(1077.618894,1077.618895)$ | $(1001.314438,1001.314439)$ |
| $3$ | $(351.057514,351.057515)$ | $(313.557782,313.557783)$ |
| $4$ | $(1228.882278,1228.882279)$ | $(782.150437,782.150438)$ |

*Proof.* The intervals and the signs of $D$ follow by the rational
interval definitions in Definition 14.1 below; that definition and
the derivative formulas there also specify a finite certificate for
these tables. For these first tables only the polynomials
$a,c,D,N_0,N_1,N_2,C_0$ and

$$
N_a=-C_0+(T+2j+4tb)B_7
\tag{13.4}
$$

are needed. The trace at the alternative seventh action $J$ is
$T+2j+4tb$, so $a=N_a/D$.

In particular $b_i>0$, $0<r_i<1$ and $D(t_i,b_i)\ne0$.
Thus $t_i>0$, $t_ib_i<1$, and (13.3) gives a strict rank-one,
trace-one matrix. The determinant is
$t_ib_i(1-t_ib_i)-b_it_i(1-t_ib_i)=0$, and the trace is one.
Lemma 2.2 and the full-parent converse of O, Theorem 2.1, identify
the interpolated gain and drift with an actual original world.
For clarity, their original-clock identities are

$$
\begin{aligned}
(Z_0,Z_1,Z_2,Z_3,Z_4,Z_5,Z_6)
  &=(1,j,T,n,U,U+n,2U+n),\\
d_i+Z_k g_i(k)&=(0,24,147/5,24,18)_k\quad(0\le k\le4),\\
d_i+Z_5g_i(5)&=p_i,\qquad d_i+Z_6g_i(6)=v_i,\\
d_i+(3U+2n)g_i(7)&=m_i,\qquad
d_i+(T+2j+4r_i)g_i(7)=a_i.
\end{aligned}
\tag{13.5}
$$

The fourth-clock row is included: substituting the four samples in
(2.5) gives $H=0$, since (2.4) solves the regular parent equation.
The fixed-node interpolant is one polynomial of degree at most three;
if it were identically zero, the original readings $0$ and $24$
would both equal $d_i$, a contradiction. All original source
denominators $b,j,n,T,U$ are positive. The only chart denominator
$D$ is separately certified nonzero, and every $p_i\ne24$. ∎

**Theorem 13.3 (Exhaustive actual off-twenty-four critical classification).**
For every complete strict world $W\in\mathcal H$ with $p(W)\ne24$,

$$
\operatorname{rank}D\Psi_M(W)<2
\quad\Longleftrightarrow\quad
W\in\{W_1,W_2,W_3,W_4\}.
\tag{13.6}
$$

At each of the four worlds the rank is exactly one.

*Proof.* First suppose $\Lambda(W)=0$. III, Theorem 13.1, already
gives rank two on the full analytic parent at every point of both
entire strict singular lines, for all real $e=d-24$. Thus no singular
world is a critical world in (13.6). This uses that existing stronger
all-drift result without a restriction to a regular chart.

For a regular world, Lemma 3.2 gives criticality exactly when all three
$E_k$ vanish. Lemma 4.3, which also covers leading-coefficient drops,
leaves $b=1/8$ or $F(b)=0$ with the unique lift $r=-c(b)/a(b)$.
At $b=1/8$, Lemma 6.1 gives $e=0$, $p=24$ on the regular parent,
so the off-$24$ hypothesis excludes this branch. The factors

$$
b,\quad 2b+1,\quad 5b+2,\quad
5b^2+2b+1,\quad b^2+8b+4
\tag{13.7}
$$

removed in passing from the resultant gcd to $F$ have no positive
zero. The remaining factor $8b-1$ has just been treated. The removed
subresultant factor $h$ has no zero at a root of $F$ by (12.3).
These are all removed factors of the necessary cover (4.3).

Lemma 5.2 exhausts the positive roots of $F$: there are six, one in
each of its six displayed intervals. The two with
$q=5311219,6737603$ have $r<0$ under the same uniquely guarded lift
and hence are outside the strict source domain. The other four are
exactly (13.1). Lemma 13.2 makes all four strict and regular.
Lemma 12.3 now supplies the converse missing from a necessary
resultant cover: all three $E_k$ really vanish at each of these
four lifts. Lemma 3.2 therefore makes each $W_i$ critical.
The $p_b\ne0$ certificates of Lemma 14.2 give rank at least one,
and the vanishing minors give rank at most one.

The parent/world identification of Definition 2.1 and O, Theorem 2.1,
means that a regular source fixes the whole gain and the drift;
no additional critical complete world can lie over one of these
four sources. No division by $d$, $e$, a gain sample, a leading
gain coefficient or a gain-root difference has occurred. Thus zero
drift, every lower degree and all sample-zero strata are retained
in the quantified domain of (13.6). ∎

## 14. Source two-jets and the four Whitney cross-caps

**Definition 14.1 (Exact jet and interval certificates).** In the
independent source coordinates $(t,b)$ put

$$
f=(N_0,N_1,N_2)/D=(p,v,m),\qquad a=N_a/D,
\tag{14.1}
$$

where $N_a$ is (13.4). For any of these four numerator polynomials
$N$ and $x,y\in\{t,b\}$ define the integer polynomials

$$
\begin{aligned}
\mathcal D_xN&=DN_x-ND_x,\\
\mathcal H_{xy}N
 &=D^2N_{xy}-D(N_xD_y+N_yD_x+ND_{xy})+2ND_xD_y.
\end{aligned}
\tag{14.2}
$$

The first and second derivatives of $N/D$ are respectively
$\mathcal D_xN/D^2$ and $\mathcal H_{xy}N/D^3$.
At a point with $p_b\ne0$ set

$$
\begin{gathered}
s=p_t/p_b,\qquad K=\partial_t-s\partial_b,\\
H_{KK}=f_{tt}-2sf_{tb}+s^2f_{bb},\qquad
H_{Kb}=f_{tb}-sf_{bb},\\
\Delta=\det(f_b,H_{KK},H_{Kb}),\qquad
a_K=a_t-sa_b,\\
\chi=(H_{KK})_v-\frac{v_b}{p_b}(H_{KK})_p.
\end{gathered}
\tag{14.3}
$$

The Hessians in (14.3) evaluate fixed vectors at the chosen point.
They do not differentiate the coefficient $s$ as a vector field.

Here is the rational interval convention for the finite tables.
For $X=[x_-,x_+]$ define

$$
\mathcal R(X)=2^{-512}
 [\lfloor2^{512}x_-\rfloor,\lceil2^{512}x_+\rceil].
\tag{14.4}
$$

Addition and multiplication mean their usual interval hull followed
by $\mathcal R$; multiplication takes the minimum and maximum of
the four endpoint products. Negation reverses endpoints and changes
their signs, and subtraction is addition of a negated interval.
For an interval $Y$ excluding zero, $X/Y$ means rounded multiplication
of $X$ by the exact reciprocal interval $[1/y_+,1/y_-]$.
An integer is initially its exact singleton interval. Powers mean
repeated multiplication starting from $[1,1]$.

For a univariate coefficient list use descending Horner, starting
from $[0,0]$. For a polynomial in $t,b$, expand in monomials and pad
all coefficients to its full rectangular bidegree; evaluate descending
$b$ Horner inside descending $t$ Horner. In particular no zero
coefficient between the top degree and degree zero is omitted.

Let $I_i^*$ be the closed interval obtained from $\overline I_i$
by $256$ midpoint bisections retaining the half with opposite
nonzero endpoint signs of $F$. An exact specification of each
midpoint sign is the sign of
$v^{67}F(u/v)$ at its rational midpoint $u/v$, with $v>0$;
this is an integer. Every midpoint is nonzero under $F$, and
$|I_i^*|=1/(10^8 2^{256})$. Define the interval lifts

$$
R_i=-c(I_i^*)/a(I_i^*),\qquad
T_i=R_i/I_i^*.
\tag{14.5}
$$

The signs of $a(I_i^*)$ are $-,+,+,-$ in the four rows, so
these divisions are legal, as also follows from Lemma 5.2.
Evaluate $D,N_0,N_1,N_2,N_a,-C_0$ on $T_i\times I_i^*$.
Divide the last five by the interval for $D$ to enclose
$p,v,m,a,d$, respectively. Evaluate (14.2) on the same rectangle
and divide by the indicated interval powers of $D$ to enclose
all derivatives. Evaluate $s,H_{KK},H_{Kb},a_K,\chi$ in the
order (14.3), after excluding zero from the $p_b$ interval.
For columns $u,v,w$ the determinant convention is

$$
\det(u,v,w)=
u_1(v_2w_3-v_3w_2)-v_1(u_2w_3-u_3w_2)
+w_1(u_2v_3-u_3v_2).
\tag{14.6}
$$

All interval statements below refer to these finite rational
expressions. Their inputs are the existing integer circuit, the
fixed determinants and the single existing coefficient list of $F$.

**Lemma 14.2 (Nonzero source-jet certificates).** The preceding
interval expressions are defined in all four rows. They give the
tables of Lemma 13.2 and the following strict inclusions:

| $i$ | $p_b$ | $\Delta$ | $a_K$ | $\chi$ |
| --- | --- | --- | --- | --- |
| $1$ | $(-830779,-830778)$ | $(-3418000000000000,-3417000000000000)$ | $(176,177)$ | $(47481,47482)$ |
| $2$ | $(702,703)$ | $(16.52,16.54)$ | $(5,6)$ | $(-0.951,-0.950)$ |
| $3$ | $(405954,405955)$ | $(1543600000,1543700000)$ | $(4,5)$ | $(0.140,0.141)$ |
| $4$ | $(35,36)$ | $(168543,168544)$ | $(173,174)$ | $(-37.564,-37.563)$ |

In particular $p_b\Delta a_K\chi\ne0$ and $a_K>0$ at every $W_i$.

*Proof.* The rational operations of Definition 14.1 give the stated
inclusions by substitution into (14.2) and (14.3). More precise
intermediate enclosing intervals for the three jet quantities that
certify rank, cross-cap recognition and $J$ separation are

$$
\begin{array}{c|c|c|c}
i&p_b&\Delta&a_K\\ \hline
1&(-830778.852988,-830778.852987)
 &(-3417716279736341.173526,-3417716279736341.173525)
 &(176.491607,176.491608)\\
2&(702.496383,702.496384)
 &(16.528488,16.528489)&(5.534633,5.534634)\\
3&(405954.500756,405954.500757)
 &(1543628106.368296,1543628106.368297)&(4.299489,4.299490)\\
4&(35.324086,35.324087)
 &(168543.426152,168543.426153)&(173.429994,173.429995).
\end{array}
\tag{14.7}
$$

The corresponding $\chi$ intervals are

$$
\begin{aligned}
&(47481.395648,47481.395649),\quad
(-0.950574,-0.950573),\\
&(0.140892,0.140893),\quad
(-37.563042,-37.563041).
\end{aligned}
\tag{14.8}
$$

These are finite rational inequalities: for example the $i=2$
determinant enclosure in (14.7) means that the lower and upper
endpoints of the interval expression (14.6), with (14.2)–(14.5)
substituted, are strictly between $16528488/10^6$ and
$16528489/10^6$. The other entries have the same meaning. Thus
the tables specify both the algebraic objects and explicit rational
comparison bounds without an external source of coefficients.

Horner enclosure follows inductively from interval addition and
multiplication. Each application of $\mathcal R$ enlarges the exact
interval, so it preserves inclusion. The intervals for $D$ have the
nonzero signs of Lemma 13.2, and the $p_b$ intervals in (14.7)
exclude zero before their reciprocals are used. Hence every quotient
in these expressions is valid on its entire evaluation rectangle.
The derivative identity (14.2) follows by differentiating $N/D$
twice; it therefore bounds the actual two-jet, rather than an
unrelated cleared expression. Finally the sign-preserving bisections
keep $b_i$ in $I_i^*$ and (14.5) keeps $r_i,t_i$ in $R_i,T_i$.
The inclusions thus apply at the exact algebraic worlds. ∎

**Theorem 14.3 (Whitney cross-caps at all four actual worlds).** At
each $W_i$, the map $\Psi_M$ on the full parent has a Whitney
cross-cap singularity. Equivalently, its smooth map germ is equivalent
under local diffeomorphisms of source and target to

$$
(u,w)\longmapsto(u,uw,w^2).
\tag{14.9}
$$

*Proof.* Work in the full two-dimensional regular parent chart
$(t,b)$, justified at $W_i$ by Lemma 13.2. All three minors vanish
by Lemma 12.3. Since $p_b\ne0$, the first and second columns of
$df$ obey $f_t=(p_t/p_b)f_b$, so $df(K)=0$ and $df$ has rank one.
Use the affine source coordinates given near the chosen point by

$$
t=t_i+w,\qquad b=b_i+u-s_iw,
\qquad s_i=p_t(W_i)/p_b(W_i).
\tag{14.10}
$$

Their Jacobian is invertible. At the origin their derivatives are

$$
f_w=0,\qquad f_u=f_b,\qquad
f_{uw}=H_{Kb},\qquad f_{ww}=H_{KK}.
\tag{14.11}
$$

Lemma 14.2 gives
$\det(f_u,f_{uw},f_{ww})=-\Delta\ne0$.
This is precisely the classical Whitney recognition criterion:
$f_w=0$ and linear independence of $f_u,f_{uw},f_{ww}$ imply a
cross-cap germ. We use that criterion as stated in
Hasegawa–Honda–Naokawa–Umehara–Yamada, *Intrinsic Invariants of Cross
Caps*, [arXiv:1207.3853v2](https://arxiv.org/html/1207.3853v2),
Introduction immediately after equation (1), with its attribution to
Whitney, *The Singularities of a Smooth n-Manifold in (2n−1)-Space*,
Annals of Mathematics **45**, 247–293,
[DOI 10.2307/1969266](https://doi.org/10.2307/1969266).
It applies to the displayed source jets without a genericity
hypothesis. The source-specific assertions are the actual common
roots and the nonzero certificates (14.7); the recognition criterion
itself is the cited classical result. ∎

## 15. Real analytic original-world collision germs

**Theorem 15.1 (Actual strict $M$ double-point germs).** For each
$i\in\{1,2,3,4\}$ there are real analytic complete-world maps
$W_i^+(h),W_i^-(h)$ for $|h|<\varepsilon_i$, with
$W_i^+(0)=W_i^-(0)=W_i$, such that for $0<|h|<\varepsilon_i$,

$$
\begin{gathered}
W_i^+(h),W_i^-(h)\in\mathcal H,\qquad
W_i^+(h)\ne W_i^-(h),\\
\Psi_M(W_i^+(h))=\Psi_M(W_i^-(h)),\qquad
p(W_i^\pm(h))\ne24.
\end{gathered}
\tag{15.1}
$$

The two maps exchange under $h\mapsto-h$. In particular every
$W_i$ is an actual strict off-$24$ interior diagonal limit of
$M$ pairs, and $\Psi_M$ is not locally injective there.

*Proof.* Since $p_b(W_i)\ne0$, the real analytic inverse-function
theorem makes

$$
x=p(t,b)-p_i,\qquad y=t-t_i
\tag{15.2}
$$

local source coordinates. Write their analytic inverse as
$t=t_i+y$, $b=\beta_i(x,y)$, and write

$$
f=(p_i+x,V(x,y),\mathcal M(x,y)).
\tag{15.3}
$$

At the origin $V_y=\mathcal M_y=0$ because the $y$ direction is
$K$. To identify the needed Jacobian exactly, put $s=p_t/p_b$ at
the origin and differentiate (15.2):

$$
\begin{gathered}
\beta_x=1/p_b,\qquad \beta_y=-s,\\
\beta_{yy}=-(H_{KK})_p/p_b,
\qquad
\beta_{xy}=-(p_{tb}-sp_{bb})/p_b^2.
\end{gathered}
\tag{15.4}
$$

It follows that the vectors $f_{yy}$ and $f_{xy}$ in these new
coordinates are respectively

$$
H_{KK}-\frac{(H_{KK})_p}{p_b}f_b,
\qquad
\frac1{p_b}H_{Kb}-\frac{(H_{Kb})_p}{p_b^2}f_b.
\tag{15.5}
$$

Also $f_x=f_b/p_b$. Taking determinants of these three columns
in the order $(f_x,f_{xy},f_{yy})$ gives

$$
\det\begin{pmatrix}V_{xy}&V_{yy}\\
                    \mathcal M_{xy}&\mathcal M_{yy}\end{pmatrix}
=-\frac{\Delta}{p_b^2}\ne0.
\tag{15.6}
$$

In particular $V_{yy}=\chi\ne0$ by (14.8): the acquired projection
$(p,v)$ has nonzero second derivative in its null direction at
each of these worlds.

For an analytic scalar function $Z(x,y)$ equal to $V$ or
$\mathcal M$, consider

$$
\frac{Z(x,z+h)-Z(x,z-h)}{2h}.
\tag{15.7}
$$

Its value at $h=0$ is $Z_y(x,z)$. Its analytic extension is even
in $h$ and is an analytic function of $(x,z,q)$, where $q=h^2$.
Indeed write the convergent power series
$Z(x,y)=\sum_{j,k\ge0}c_{jk}x^jy^k$ on a smaller polydisc.
For each monomial its divided difference is the polynomial

$$
\frac{(z+h)^k-(z-h)^k}{2h}
=\sum_{\nu=0}^{\lfloor(k-1)/2\rfloor}
  \binom{k}{2\nu+1}z^{k-2\nu-1}q^\nu
\quad(k\ge1),
\tag{15.8}
$$

and it is zero for $k=0$. Absolute convergence on a smaller
polydisc justifies summation and differentiation: choose
$|z|+\sqrt{|q|}$ smaller than the original $y$ radius, and use
the absolutely convergent differentiated series of $Z$ to dominate
the binomial sums. Thus (15.8) defines a real analytic function
$\mathcal D_Z(x,z,q)$ also for small negative real $q$.

At $(x,z,q)=(0,0,0)$,
$\mathcal D_V=\mathcal D_{\mathcal M}=0$ and their Jacobian in
$(x,z)$ is the invertible matrix in (15.6). The real analytic
implicit-function theorem supplies analytic functions $x_i(q),\zeta_i(q)$,
with $x_i(0)=\zeta_i(0)=0$, satisfying

$$
\mathcal D_V(x_i(q),\zeta_i(q),q)
=\mathcal D_{\mathcal M}(x_i(q),\zeta_i(q),q)=0.
\tag{15.9}
$$

These applications use only the classical inverse and implicit
function theorems on analytic maps with the displayed invertible
Jacobians; the construction of the divided differences is explicit.
Define two source points by

$$
\begin{aligned}
t_i^\pm(h)&=t_i+\zeta_i(h^2)\pm h,\\
b_i^\pm(h)&=\beta_i(x_i(h^2),\zeta_i(h^2)\pm h).
\end{aligned}
\tag{15.10}
$$

They have the same $p=p_i+x_i(h^2)$. For $h\ne0$, equations
(15.7)–(15.9) give exactly equal $v$ and $m$, and their $t$
coordinates differ by $2h$. Hence they are distinct sources.
They converge to $(t_i,b_i)$ and exchange when $h$ changes sign.
Their source derivatives at zero are $\pm(1,-s_i)=\pm K_i$,
so both analytic branches are nonconstant.

At both points lift to a complete world by (13.3), evaluated at
$(t_i^\pm(h),b_i^\pm(h))$ in place of $(t_i,b_i)$. The source
inequalities $t>0$, $b>0$, $tb<1$, the nonvanishing of $D$, and
$p\ne24$ all persist after reducing $\varepsilon_i$. This lift
is real analytic, including all four padded coefficients of its
one whole gain. Lemma 2.2 and O, Theorem 2.1, give every original
clock equation (13.5) for each lifted point. The unequal original
readings again exclude the zero gain. Each world retains its own
single fixed real drift and degree-at-most-three real polynomial
at clocks $0$ through $7$. The two worlds need not have the same
drift or polynomial, as permitted by Definition 1.1.

Their distinct sources imply distinct complete worlds. Both complete
worlds converge to $W_i$, so every full-parent neighbourhood of
$W_i$ contains a distinct actual equal-$\Psi_M$ pair. This proves
(15.1) directly in the original real model, independently of whether
the diffeomorphisms in the Whitney normal form are analytic. ∎

## 16. Local $J$ separation and the exact remaining incidence quantifiers

**Theorem 16.1 (Local $J$ separation at the four critical worlds).**
For each $i$ there is an open full-parent neighbourhood
$\mathcal U_i$ of $W_i$ on which $(p,a)$ is one-to-one. Consequently

$$
\begin{gathered}
W,W'\in\mathcal U_i,\quad p(W)=p(W'),\quad W\ne W'
\quad\Longrightarrow\quad a(W)\ne a(W').
\end{gathered}
\tag{16.1}
$$

For sufficiently small $h\ne0$, the two worlds of Theorem 15.1
therefore have unequal $a$, despite their equal $p,v,m$.
More precisely,
$a(W_i^+(h))-a(W_i^-(h))=2a_K(W_i)h+O(h^3)$.

*Proof.* In $(t,b)$ coordinates,

$$
\det\frac{\partial(p,a)}{\partial(t,b)}
=p_ta_b-p_ba_t=-p_ba_K\ne0
\tag{16.2}
$$

by Lemma 14.2. The analytic inverse-function theorem gives
$\mathcal U_i$; the complete-world identification preserves this
local assertion. Both collision-germ endpoints eventually belong to
the same $\mathcal U_i$, so (16.1) applies to them.
The quantifiers in (16.1) require both endpoints in this one
neighbourhood, and impose no condition on worlds elsewhere in the
entire $C(p,v)$. The displayed asymptotic follows by applying the
same symmetric divided difference (15.7) to the analytic function
$a$ in coordinates (15.2): its value at $(0,0,0)$ is $a_K(W_i)$,
while $x_i(h^2),\zeta_i(h^2),h^2$ are all $O(h^2)$. ∎

**Theorem 16.2 (Strict interior $M$ diagonal limits).** Suppose
$W_n,W'_n\in\mathcal H$ are complete worlds satisfying

$$
\begin{gathered}
W_n\ne W'_n,\qquad
\Psi_M(W_n)=\Psi_M(W'_n),\qquad p(W_n)\ne24,\\
W_n\longrightarrow W,\qquad W'_n\longrightarrow W,
\qquad W\in\mathcal H,\qquad p(W)\ne24.
\end{gathered}
\tag{16.3}
$$

Then $W$ is one of $W_1,W_2,W_3,W_4$. Conversely every one of
these four worlds occurs as such a limit. The same necessary
conclusion applies when the $M$ pair is selected from a sequence
of original joint configurations, without any assumption on the
limits of their independently selected $J$ endpoints.

*Proof.* If $D\Psi_M(W)$ had rank two, a two-coordinate output
submap would have invertible differential on a full-parent chart
at $W$. The inverse-function theorem would make $\Psi_M$
injective on a neighbourhood of $W$. Both endpoints in (16.3)
would eventually lie there, contradicting their distinctness and
equal augmented output. Thus $W$ is critical, and Theorem 13.3
identifies it. This argument uses the smooth full-parent surface,
including at singular worlds, as supplied by III, Lemma 11.2 and
Theorem 13.1. The converse is Theorem 15.1. The selected-pair
assertion follows because its $M$ endpoints satisfy the same
hypotheses, regardless of any cross-pair overlap.

The convergence and the strict off-$24$ limit are hypotheses of
this statement. No compactness, source collar, nonzero gain sample
or additional control of $J$ endpoints is used. In particular the
conclusion classifies common interior limits of the $M$ endpoints;
it places no restriction on a pair with two distinct limits. ∎

**Definition 16.3 (A polynomial whole-world relation).** For
$w=(r,b,c,d,k_0,k_1,k_2,k_3)\in\mathbb R^8$ put
$g_w(s)=\sum_{l=0}^3k_ls^l$ and

$$
\begin{aligned}
(Z_0,\ldots,Z_6)&=
(1,b+c,1+b,b+c+r,1+2b,1+2b+b+c+r,2(1+2b)+b+c+r),\\
\mathfrak a(w)&=d+g_w(7)(1+b+2(b+c)+4r),\\
\mathfrak m(w)&=d+g_w(7)(3(1+2b)+2(b+c+r)).
\end{aligned}
\tag{16.4}
$$

Let $\mathscr W(p,v;w)$ be the conjunction

$$
\begin{gathered}
0<r<1,\qquad b>0,\qquad c>0,\qquad bc=r(1-r),
\qquad\sum_{l=0}^3 k_l^2>0,\\
d+g_w(l)Z_l=(0,24,147/5,24,18,p,v)_l
\quad(0\le l\le6).
\end{gathered}
\tag{16.5}
$$

Define the original independent-pair relation by

$$
\begin{aligned}
\mathscr I(p,v;w_0,w_1,w_2,w_3)\quad\Longleftrightarrow\quad
& p\ne24\ \land\ \bigwedge_{l=0}^3\mathscr W(p,v;w_l)\\
&\land\ \mathfrak a(w_0)=\mathfrak a(w_1)
          \ \land\ \|w_0-w_1\|^2>0\\
&\land\ \mathfrak m(w_2)=\mathfrak m(w_3)
          \ \land\ \|w_2-w_3\|^2>0.
\end{aligned}
\tag{16.6}
$$

The norm is the Euclidean norm in the full eight-coordinate tuple.
There are no inequalities between cross-pair labels and no equality
between the two common terminal values.

For the exact constants of Definition 13.1 let $\mathsf J_i$ denote
the sentence

$$
\exists w_0,w_1:\quad
\mathscr W(p_i,v_i;w_0)\land\mathscr W(p_i,v_i;w_1)
\land\mathfrak a(w_0)=\mathfrak a(w_1)
\land\|w_0-w_1\|^2>0.
\tag{16.7}
$$

Put $z(w)=(r,b,d)$ and $z_i=(r_i,b_i,d_i)$. Let $\mathsf Q_i$
denote

$$
\begin{aligned}
\forall\epsilon>0\ \exists p,v,w_0,w_1,w_2,w_3:\quad
&\mathscr I(p,v;w_0,w_1,w_2,w_3)\\
&\land\ \|z(w_2)-z_i\|^2+\|z(w_3)-z_i\|^2<\epsilon^2.
\end{aligned}
\tag{16.8}
$$

Finally write $\mathsf I$ for the original global sentence
$\exists p,v,w_0,w_1,w_2,w_3:\mathscr I(p,v;w_0,w_1,w_2,w_3)$.

**Theorem 16.4 (Faithful incidence and diagonal-accumulation tests).**
The sentence $\mathsf I$ is equivalent to the original assertion
$D_J\cap D_M\ne\varnothing$ with the entire-child quantifiers
of Definition 9.1. For each $i$, $\mathsf J_i$ is equivalent to
$(p_i,v_i)\in D_J$, and $\mathsf Q_i$ is equivalent to existence
of a sequence of original joint configurations whose two selected
$M$ endpoints both converge as complete worlds to $W_i$.
These are finite real-algebraic sentences with algebraic constants.

In a configuration of (16.6), the two selected $J$ worlds cannot
both belong to the same $\mathcal U_i$ of Theorem 16.1, even if
both selected $M$ worlds do belong to it. The scope of the existing
regional $J$ exclusion in [SV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md),
Theorem 1.1, does not include the fourth base $(p_4,v_4)$.

*Proof.* The source inequalities and equation $bc=r(1-r)$ in
(16.5) give exactly a strict trace-one rank-one source, with
$c=r(1-r)/b$. The four coefficients specify one entire real
polynomial of degree at most three and their sum-of-squares guard
excludes only the identically zero gain. That guard also follows
from the unequal original readings, so it removes no original
world. The seven equations are exactly the original left-action
clock equations, including the fourth reading and both acquired
readings. Formula (16.4) supplies the two alternative clock-seven
responses. This identifies $\mathscr W$ bijectively with the
entire $C(p,v)$, including singular sources, zero drift, degree
drops and gain samples that vanish. A positive squared difference
means distinct complete worlds. Thus (16.6) and (16.7) have exactly
the asserted independent-pair and base-pair quantifiers.

If $\mathsf Q_i$ holds, choose its witnesses with
$\epsilon=1/n$. Both selected $M$ triples $(r,b,d)$ converge to
$z_i$. Since $b_i>0$, the entries $c=r(1-r)/b$ converge too.
Set $e=d-24$ and use the whole-gain samples (2.2): their positive
source denominators are bounded away from zero near this strict
limit, and each sample is a continuous function of $(r,b,d)$.
Fixed-node interpolation then gives convergence of all four padded
gain coefficients. Hence both selected complete worlds converge
to $W_i$. Their common $p,v$ converge to $p_i,v_i$ by continuity,
and all worlds in the sequence retain the strict original guards.

Conversely, for a sequence of such joint configurations with
both selected $M$ worlds converging to $W_i$, the sum in (16.8)
tends to zero; for every $\epsilon>0$ some member supplies its
witnesses. This proves the exact equivalence. Theorem 16.2
classifies the possible strict off-$24$ common limits in this
equivalence. It does not supply the independent $J$ pair in any
of the constructed $M$ germs.

All expressions in (16.4)–(16.8) are polynomial equalities and
inequalities with rational coefficients apart from the specified
real algebraic constants. Those constants are themselves defined
by $F$, the isolating intervals and (13.2)–(13.4). Denominators
there are certified nonzero; their defining rational equations
may therefore be expressed by multiplication without selecting
additional components. Classical quantifier elimination over real
closed fields applies, including to the quantified $\epsilon$
in (16.8); the general method is that of Basu–Pollack–Roy cited
in Lemma 12.3. For the fixed-base tests, F, Theorem 32.1, also
bounds each entire off-$24$ child by $24$ worlds, so direct
unordered comparison has at most $\binom{24}{2}=276$ pairs.

The local assertion follows directly from (16.1), since the $J$
pair shares both $p$ and $a$. It leaves at least one $J$ endpoint
outside that patch and permits every original cross-pair overlap.
Finally $v_4>305.047970>305$ by Lemma 13.2, whereas SV,
Theorem 1.1, excludes $J$ pairs only for
$(p,v)\in[56,58]\times[304,305]$. Thus its rectangle cannot be
enlarged to this fourth critical base by that theorem.

Theorem 16.2 assumes a common strict interior limit of the $M$
endpoints. It gives no reduction of configurations whose $M$
endpoints remain separated, or whose common limit is a boundary
world or has $p=24$. Moreover $\neg\mathsf J_i$ alone asserts
absence only at one exact base: it supplies no neighbourhood
absence for independently selected $J$ pairs whose endpoints can
approach their own boundary or diagonal. Conversely
$\mathsf J_i$ by itself supplies no intersection of its base
pair with the neighbouring $M$ double-point branch. The global
sentence $\mathsf I$ therefore retains all bases, all independent
$J$ roles and all separated $M$ pairs in (16.6). ∎
