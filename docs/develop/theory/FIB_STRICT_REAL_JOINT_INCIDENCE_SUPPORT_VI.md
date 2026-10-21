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

## 17. Three closed target rectangles and the whole-child compactness theorem

Retain the complete worlds, the undivided parent equation, the one whole
real gain of degree at most three, the fixed real drift, the original
clocks, and the entire-child quantifiers of Sections 1--16.  Put

\[
\begin{aligned}
 K_1&=[690.595905,690.595906]\times[1416.434664,1416.434665],\\
 K_2&=[1.830485,1.830486]\times[175.912050,175.912051],\\
 K_3&=[7.283036,7.283037]\times[61.494372,61.494373].
\end{aligned}
\tag{17.1}
\]

Every terminating decimal in this appendix denotes the corresponding exact
rational number.  Let \(\Phi(W)=(p(W),v(W))\), and give the strict complete
world space its topology in \((r,b,c,d,k_0,k_1,k_2,k_3)\), where
\(g(s)=\sum_{q=0}^3k_qs^q\).  The map \(\Phi\) is the original sixth-clock
map, including all lower-degree strata and zero samples.

The whole-world coercivity and nonproper-value classification used below
are [S], Section 7 and Theorems 12.1 and 12.3, with the boundary lifts of
Definition 12.2 there.  These statements retain singular sources, arbitrary
real drift, every allowed gain stratum, and unused companions; they impose
no terminal-value condition.

**Definition 17.1 (Normalized boundary rows).**  If
\(A=(A_0,\ldots,A_m)\), write \([A](x)=\sum_{q=0}^mA_qx^q\).  For the four
nonstrict source faces, in the order
\[
(r,b,c)=(0,x,0),\ (1,x,0),\ (0,0,x),\ (1,0,x),\qquad x>0,
\]
put \(D_\nu=[D_{\nu,q}]\), \(P_\nu=[P_{\nu,q}]\), and
\(V_\nu=[V_{\nu,q}]\) from the following ascending coefficient arrays:

\[
\begin{array}{c|c|c|c}
\nu&D_\nu&P_\nu&V_\nu\\ \hline
1&(-20,-40,0,5)&(-390,-1395,-2238,-216)&(-1032,-7458,-13293,-1125)\\
2&(-10,-30,-20,5,5)&(-180,-1086,-1326,-366,-216)&(-798,-5118,-7458,-2643,-1125)\\
3&(-10,10)&(-195,240,-48)&(-516,375,135)\\
4&(-5,0,10)&(-90,12,144,-48)&(-399,-99,645,135).
\end{array}
\tag{17.2}
\]

The auxiliary boundary image is
\[
 (p,v)=\bigl(P_\nu(x)/D_\nu(x),V_\nu(x)/D_\nu(x)\bigr),
\tag{17.3}
\]
whenever the denominator is nonzero.  This fixes both the face normalization
and the coefficient order.  It is the specialization of the undivided
interpolation circuit of this volume, Lemma 2.2, (2.3)--(2.5), and therefore
retains the original clock-four equation rather than replacing it by a
divided equation.

For \(f_{\nu,p}=pD_\nu-P_\nu\) and
\(f_{\nu,v}=vD_\nu-V_\nu\), form the Sylvester matrix \(S_\nu(p,v)\)
with descending coefficients, the shifted \(f_{\nu,p}\) rows first, and
then the shifted \(f_{\nu,v}\) rows.  Gaussian elimination is performed over rational
intervals: at step \(k\), interchange the displayed pivot row with row \(k\),
include the interchange sign in the determinant accumulator, and replace
\(A_{ij}\) by \(A_{ij}-A_{ik}A_{kj}/A_{kk}\) for \(i,j>k\).  Products use the
four endpoint products and division reverses an interval disjoint from zero.
The following table gives every pivot interval.  The pivot row numbers are
zero-based.  Each bracket is an exact rational interval, and the entries are
listed in elimination order; a superscript \(q\) repeats the preceding interval \(q\) times, and hence all seventy-two pivots are displayed.

\[
\begin{array}{c|c|l}
(\nu,i)&\text{pivot rows}&\text{pivot intervals in order}\\ \hline
(1,1)&(3,4,5,3,4,5)&[205179333/25000,328286933/40000]^3;[-26286761543977/10^9,-2628676118673/10^8];[-1471463890833/62500000,-5885855508523/250000000];[-12765417263/500000000,-12765279217/500000000]\\
(1,2)&(3,4,3,5,5,5)&[8018241/4000,400912051/200000]^2;[-3665470054989/10^9,-229091859527/62500000];[13553314334779/10^9,13553314385439/10^9];[611748191763/500000000,611748226421/500000000];[-164292487/800000,-51341375091/250000000]\\
(1,3)&(3,4,5,3,5,5)&[71623593/50000,286494373/200000]^3;[-10411816808129/10^9,-5205905596279/500000000];[264749719533/10^9,66187463069/250000000];[-33934971153/200000000,-33934744337/200000000]\\
(2,1)&(4,5,6,7,4,5,6,7)&[205179333/25000,328286933/40000]^4;[-25263965433/3125000,-25263963803/3125000];[-223020054537/31250000,-7136640781149/10^9];[-993362182019/10^9,-496680005047/500000000];[-531309649/125000000,-4247609359/10^9]\\
(2,2)&(4,5,6,7,6,6,7,7)&[8018241/4000,400912051/200000]^4;[882903586409/10^9,220725911669/250000000];[1776899456219/10^9,888450252593/500000000];[153573654637/200000000,76786860821/10^8];[11184243621/200000000,5592189001/10^8]\\
(2,3)&(4,5,6,7,4,5,7,7)&[71623593/50000,286494373/200000]^4;[-268368662299/200000000,-670921108503/500000000];[-1197696498653/10^9,-1197695486427/10^9];[48918253199/250000000,24459189363/125000000];[10704464239/10^9,1338130921/125000000]\\
(3,1)&(2,2,3,3)&[-135,-135];[11568837855333/10^9,11568837868889/10^9];[6827203271071/500000000,13654406552459/10^9];[-996921/10^9,-38673/40000000]\\
(3,2)&(2,2,3,3)&[-135,-135];[270436583333/10^9,270436596889/10^9];[1251683016363/10^9,1251683039769/10^9];[3283313937/10^9,3283343241/10^9]\\
(3,3)&(2,3,3,3)&[-135,-135]^2;[-40928158667/500000000,-81856303777/10^9];[-2173299769/10^9,-2173217333/10^9]\\
(4,1)&(3,3,4,5,5,5)&[-135,-135];[11568837855333/10^9,11568837868889/10^9];[13519617367279/10^9,5281100538/390625];[2703933289957/200000000,3379916614947/250000000];[-4073484821/200000000,-20367409187/10^9];[-9974039023/500000000,-19948062767/10^9]\\
(4,2)&(3,3,4,5,5,5)&[-135,-135];[270436583333/10^9,270436596889/10^9];[562850886393/500000000,1125701783367/10^9];[280151019233/250000000,112060408767/100000000];[25053652531/10^9,25053663119/10^9];[2364564821/100000000,1477853789/62500000]\\
(4,3)&(3,4,5,5,4,5)&[-135,-135]^3;[-40928158667/500000000,-81856303777/10^9];[37840834727/10^9,9460213991/250000000];[39442226093/10^9,9860572557/250000000].
\end{array}
\tag{17.4}
\]

Put \((s_1,s_2,s_3,s_4)=(21,27,7,17)\).  The following table encloses
\(10^{-s_\nu}\det S_\nu(p,v)\) for \((p,v)\in K_i\); the positive
factors \(10^{-s_\nu}\) scale only the determinants.  The Sylvester matrices
and the pivot intervals in (17.4) are unscaled:
\[
\begin{array}{c|ccc}
\nu&K_1&K_2&K_3\\ \hline
1&[8734696043/10^9,4367395359/500000000]&[-50158421/10^9,-25079193/500000000]&[21481/15625000,343699/250000000]\\
2&[220902669/200000000,1105261713/10^9]&[-271933/250000000,-1087717/10^9]&[-567/40000000,-14173/10^9]\\
3&[-425193913/200000000,-2061790163/10^9]&[7501981399/500000000,7502048869/500000000]&[-2026373/6250000,-10131479/31250000]\\
4&[1159819469/10^9,1159821211/10^9]&[272833/10^9,136417/500000000]&[601/200000000,1503/500000000].
\end{array}
\tag{17.5}
\]

Every displayed pivot and scaled determinant interval is disjoint from zero.
Since each determinant scale factor is positive, the Sylvester determinant
cannot vanish on any of the twelve target rectangles.
The pole guards are also exact: on the first two faces \(P_\nu(x)<0\) for
\(x>0\); on the third face \(P_3(1)=-3\); and on the fourth face,
\(2x^2=1\) implies \(P_4(x)=-12x-18<0\).  Hence a positive denominator
zero never supplies a finite target point.  The two corners are controlled by
[S], Sections 7 and 12: their target limits are
\[
(39/2,258/5),\qquad (18,399/5),
\tag{17.6}
\]
while the two unbounded geometric limits are
\((-216/5,-225)\) and \(p\to-\infty\), respectively.  None belongs to
any \(K_i\).

**Theorem 17.2 (Whole-child compactness over the first three rectangles).**
For each \(i\in\{1,2,3\}\), the set
\[
 \Phi^{-1}(K_i)=\{W:\Phi(W)\in K_i\}
\tag{17.9}
\]
is compact in the strict complete-world space.

**Proof.** Let \(W_n\) be a sequence in (17.9).  If \(b_n\) were unbounded,
[S], Section 7, would give a subsequence whose base tends to
\((-216/5,-225)\), outside the closed rectangle \(K_i\).  Thus \(b_n\)
is bounded.  Since \(p_n\) is bounded on \(K_i\), [S], Theorem 12.1,
bounds \(c_n,d_n\) and all four padded gain coefficients, retaining the
\(\Lambda=0\), lower-degree, zero-drift, zero-sample, and unused-companion
strata.  By [S], Definition 12.2 and Theorem 12.3, every finite
strictness-boundary limit lies on one of the four faces in (17.2) or at one
of the two corners.  Equations (17.2)--(17.6) exclude every such limit over
\(K_i\): the twelve Sylvester determinants exclude all finite face
intersections, the pole guards exclude denominator cancellations, and
(17.6) excludes the corners.  The cited escape classification excludes
infinity.

Consequently a subsequence has convergent source, drift, and padded gain
coordinates with a strict source limit.  The original seven clock equations
are closed under this convergence.  The limit gain is not identically zero,
since its first two prescribed readings are distinct.  The limit is therefore
an element of the strict complete-world space.  The topology is Euclidean in
finitely many coordinates, so boundedness and sequential closedness give
compactness (Heine--Borel); no pair relation has been included in (17.9).
\(\square\)

## 18. An actual remote regular branch over the third rectangle

Use the regular circuit of this volume, Lemma 2.2, (2.3)--(2.5), with
\(t=r/b\), and write
\[
 F(r,b)=\left(N_0(r/b,b)/D(r/b,b),\ N_1(r/b,b)/D(r/b,b)\right).
\tag{18.1}
\]
Here \(D,N_0,N_1\) are exactly the integer polynomials in (2.3), after
the indicated substitution; the identities (2.4)--(2.5), including
\(D=(5/2)TUjn\Lambda\), \(d=-C_0/D\), and the whole interpolant
\(g(i)=C_i/D\) are retained.  Put
\[
 x_0=(0.048472239114,0.046421593505),\qquad
 R=\{x:\|x-x_0\|_\infty\le10^{-8}\}.
\tag{18.2}
\]
The inverse preconditioner and its determinant are
\[
 Y=\begin{pmatrix}
-0.009735466305&0.004818667927\\
-0.009305738900&0.004566737839
\end{pmatrix},\qquad
 \det Y={76388643822649081\over200000000000000000000000}\ne0.
\tag{18.3}
\]

For a polynomial \(Q(r,b)\), define its exact Taylor enclosure on a square of
radius \(\rho\) by
\[
 q_{ij}(Q)={1\over i!j!}\partial_r^i\partial_b^jQ(x_0),\qquad
 \mathcal T_\rho(Q)=q_{00}(Q)+[-S_\rho(Q),S_\rho(Q)],
\quad
 S_\rho(Q)=\sum_{i+j>0}|q_{ij}(Q)|\rho^{i+j}.
\tag{18.4}
\]
For \(E_{kl}=\delta_{kl}L^2-\sum_iY_{ki}((\partial_lP_i)L-P_i\partial_lL)\),
where \(L=b^3D\) and \(P_i=b^3N_i\), the identity
\[
 I-YDF=E/L^2
\tag{18.5}
\]
holds.  The finite sums (18.4), followed by rational interval division by
\(\mathcal T_{10^{-8}}(L)^2\), give
\[
10^9(I-YDF(R))\subset
\begin{pmatrix}
[-61299,61307]&[-65343,65335]\\
[-102136,102111]&[-108449,108475]
\end{pmatrix},
\quad
\|I-YDF(R)\|_\infty<211/10^6<1/1000.
\tag{18.6}
\]
The same exact Taylor rule applied to \(Y(F(x_0)-y)\), uniformly for
\(y\in K_3\), gives
\[
10^{15}Y(F(x_0)-y)\in[-7506636,7047499]\times[-7162674,6709804].
\tag{18.7}
\]
Thus the contraction image radius is less than
\(8.01\cdot10^{-9}<10^{-8}\).  On the enlarged open rectangle
\[
 \widehat K_3=(7.283036-10^{-7},7.283037+10^{-7})
 \times(61.494372-10^{-7},61.494373+10^{-7}),
\tag{18.8}
\]
the same finite Taylor calculation gives the sharper uniform image radius
\[
 896415551941/10^{20}<10^{-8}.
\tag{18.9}
\]

The source and parent guards on \(R\) have the exact outward enclosures
\[
\begin{gathered}
 r\in[0.048472229114,0.048472249114],\quad
 b\in[0.046421583505,0.046421603505],\\
 c\in[0.99356049,0.99356135],\quad
 D\in[0.41331626,0.41333581],\\
 \Lambda\in[0.127714779,0.127721037].
\end{gathered}
\tag{18.10}
\]
In particular the source is strict and regular throughout \(R\).  The
corresponding complete-world drift, alternative readings, and a whole gain
sample are bounded by
\[
 d\in[35.527142,35.529885],\quad
 a\in[220.955521,220.976926],\quad
 m\in[340.198640,340.231979],\quad
 g(0)=-d\ne0.
\tag{18.11}
\]

**Theorem 18.1 (Actual remote companion and analytic continuation).**  For
every \(y\in K_3\), there is exactly one \(x\in R\) with \(F(x)=y\).  The
corresponding regular complete world is an original whole world in the
child \(C(y)\), and these worlds form one real-analytic branch over the open
rectangle \(\widehat K_3\).

**Proof.** For fixed \(y\), let
\[
 T_y(x)=x-Y(F(x)-y).
\]
Equations (18.6)--(18.7) show that \(T_y\) is a contraction of the complete
square \(R\) into its interior.  Banach's fixed-point theorem gives a unique
fixed point.  Since \(Y\) is invertible, the fixed-point equation is exactly
\(F(x)=y\).  The derivative bound (18.6), together with \(\det Y\ne0\)
from (18.3), makes \(DF\) invertible on \(R\); the implicit-function theorem
gives local
real-analytic inverse sheets.  The enlarged estimate (18.9) gives the same
argument throughout \(\widehat K_3\), and the sheets agree on overlaps by
uniqueness in \(R\).  Finally Lemma 2.2, (2.3)--(2.5), and the undivided
parent converse reconstruct one drift and one degree-at-most-three real gain
for that world and all original clock readings.  Hence this is an actual branch
of the original model, not a branch of a reduced response equation.  \(\square\)

## 19. Necessary incidence consumers and the exact remaining alternatives

Let \(W_3\) be the third critical world of Section 13.  Lemma 14.2 and
Theorem 16.1 give \(\operatorname{rank}D(p,a)(W_3)=2\) and a full-parent neighborhood
\(\mathcal U_3\) of \(W_3\) on which \((p,a)\) is injective.  Lemma 13.2
places \(\Phi(W_3)\) strictly inside \(K_3\) and gives \(313<a(W_3)<314\).
By continuity, shrink \(\mathcal U_3\) so that \(313<a<314\), it is disjoint
from \(R\), and \(\mathcal U_3\subset\Phi^{-1}(\operatorname{int}K_3)\).
The remote branch has the separation
\[
  a(\mathcal U_3)-a(R)>46011537/500000>92.02.
\tag{19.1}
\]
At fixed \(y\in K_3\), there is one world in \(R\).  The local injectivity
in \(\mathcal U_3\), uniqueness in \(R\), and (19.1) imply that \(a\) is
injective on \(\mathcal U_3\cup R\) in each entire child.

**Theorem 19.1 (Four-child-world necessary condition near the third
\(M\)-germ).**  If an original joint configuration has both selected
\(M\)-endpoints in \(\mathcal U_3\), then its entire child contains at least
four distinct complete worlds.

**Proof.** The two selected \(M\)-endpoints are distinct by (16.6).  Their
common base lies in \(\operatorname{int}K_3\) by the choice of
\(\mathcal U_3\).  Theorem 18.1 supplies a third world in \(R\), distinct
from both.  A selected \(J\)-pair cannot have both endpoints in
\(\mathcal U_3\cup R\),
since they would have equal \(p,a\) and injectivity would identify them.
Choose an endpoint outside this union.  It is distinct from the two local
\(M\)-endpoints and from the remote world.  Thus four distinct child worlds
exist.  The other \(J\)-endpoint may coincide with any of these worlds; no
cross-pair disjointness has been assumed.  \(\square\)

**Theorem 19.2 (The \(Q_3\) third-world consequence).**  For the original
Euclidean-squared predicate \(Q_3\) of (16.8), \(Q_3\) implies that the exact
base child \(C(p_3,v_3)\) contains a third strict world besides \(W_3\) and
the unique world of Theorem 18.1 in \(R\).

**Proof.** Take witnesses in (16.8) with \(\epsilon=1/n\).  Their two
selected \(M\)-endpoints eventually lie in \(\mathcal U_3\), while their
bases lie in \(K_3\).  By Theorem 19.1, choose a selected \(J\)-endpoint
outside \(\mathcal U_3\cup R\).  Passing to a subsequence and applying
Theorem 17.2 gives a strict complete-world limit in the exact base child
\(C(p_3,v_3)\).  The limit cannot be \(W_3\), because \(W_3\) is interior to
\(\mathcal U_3\), and cannot be the remote world, because that world has a
strict interior margin in \(R\).  It is therefore a third distinct base
world.  No closedness of the distinct-pair relation is used, and the
conclusion is a necessary condition only.  \(\square\)

**Theorem 19.3 (The three first-target alternatives).**  For each
\(i\in\{1,2,3\}\), \(Q_i\) implies one of the following two alternatives in
the exact base child \(C(p_i,v_i)\):

\[
\begin{array}{ll}
(a)&\text{there are two distinct worlds with equal }(p_i,a);\\
(b)&\text{there is a different strict regular world }W\ne W_i\text{ with }\\
&\qquad D(p,v,a)(W)<2.
\end{array}
\tag{19.2}
\]

Here rank failure is necessary only; it is not a construction of a collision.

**Proof.** Apply Theorem 17.2 to both selected \(J\)-endpoints along one
common subsequence of witnesses for \(Q_i\).  If their limits are distinct,
continuity of \((p,a)\) gives (a).  If the limits coincide at a world \(W\),
the distinct approximating endpoints give a failure of local injectivity of
\((p,v,a)\).  The singular-world exclusion of [SIII], Theorem 13.1, removes
the \(\Lambda=0\) possibility.  At a regular world, the inverse-function
criterion shows that rank two would make \((p,v,a)\) locally injective;
hence rank is less than two.  The local \((p,a)\)-injectivity at \(W_i\)
from Theorem 16.1 excludes \(W=W_i\).  This leaves exactly (b).
The argument takes both endpoints from the same subsequence and permits all
cross-pair overlaps.  \(\square\)

Theorems 17.2--19.3 do not decide \(J_i\) or \(Q_i\) for
\(i\in\{1,2,3\}\), or the original independent \(J/M\) intersection.
Compactness supplies bounded complete-world families, not finite cardinality;
the separate at-most-24 result [F], Theorem 32.1, remains a distinct
hypothesis and gives no inventory over a continuum of target values.

For the fourth critical world, [SV], Theorems 9.2 and 12.2, prove
\(\neg J_4\) and \(\neg Q_4\).  Terminal \(J\) is injective on each entire
child over \(K_+=[56,58]\times[304,306]\), and no original joint
configuration has a selected \(M\) source in the fourth neighborhood of
[SV], (12.3).  The first-three \(J_i,Q_i\) questions, the remaining regular
critical worlds in (19.2), and separated selected \(M\)-pairs outside the
known exclusions remain unresolved.  The global sentence \(\mathsf I\) of
Definition 16.3 retains its entire strict-world domain and its original
independent-pair quantifiers; the fourth-region exclusion does not resolve it.

## 20. References used by the new proofs

The boundary exclusion uses the Sylvester resultant criterion and rational
interval elimination; see Basu--Pollack--Roy, *Algorithms in Real Algebraic
Geometry*, 2nd ed., Chapters 8--9.  Sequential compactness is the
Heine--Borel theorem (Rudin, *Principles of Mathematical Analysis*, Theorem 2.41).  The fixed-point step in Theorem 18.1 is
the Banach contraction theorem, and the analytic continuation step is the
real implicit-function theorem; see Krantz--Parks, *The Implicit Function
Theorem*, Chapters 1--2.  The nonproperness terminology is compatible with
Jelonek, “The set of points at which a polynomial map is not proper,” *Ann.
Polon. Math.* 58 (1993), 259--266, but that complex-polynomial result is not
used as a substitute for the strict-real boundary calculation above.


## 21. Third-target source polynomials and their fixed normalizations

Retain the complete parent of Definition 2.1, the original independent-pair
relation (16.6), and the exact critical world $W_3$ of Definition 13.1.
Write $y_3=(p_3,v_3)=\Phi(W_3)$. By Lemma 13.2,
$y_3\in\operatorname{int}K_3$ and $p_3\ne24$. For $y\in\widehat K_3$,
let $Z(y)$ be the actual complete world supplied by Theorem 18.1, and put
$Z_3=Z(y_3)$. In particular $Z_3$ is strictly inside the source square $R$.

**Definition 21.1 (The ordered $r$ projection of the original circuit).**
In the independent coordinates $(r,b)$ put

$$
\begin{gathered}
X=b^2+r-r^2,\qquad N=X+br,\qquad T=1+b,\qquad U=1+2b,\\
A=(8b-1)(2+5b),\\
\delta=5\bigl((b^2+8b+4)XN-2bTU(X+N)\bigr),\\
\widehat B_5=(8b-1)\bigl(96XN-30(2+3b)bX-15(2+b)bN\bigr),\\
\widehat B_6=24\delta+(8b-1)
 \bigl(15(14-b)XN-30(8b+5)bX-54bN\bigr),\\
F_0=(24-p)b\delta-3AbXN+(Ub+N)\widehat B_5,\\
F_1=(24-v)b\delta-3AbXN+(2Ub+N)\widehat B_6.
\end{gathered}
\tag{21.1}
$$

The symbols $D,C_i,B_i,N_i$ in the following identities refer exactly to
this volume's Lemma 2.2, evaluated at $(t,b)=(r/b,b)$:

$$
\begin{gathered}
j=X/b,\quad n=N/b,\quad \delta=b^2D,
\quad\widehat B_5=b^2B_5,\quad\widehat B_6=b^2B_6,\\
F_0=b^3(N_0-pD),\qquad F_1=b^3(N_1-vD).
\end{gathered}
\tag{21.2}
$$

Thus $F_0=-\mathsf A$ and $F_1=-\mathsf B$ of [O], (20.1), with
exactly that normalization; here the eliminated variable is $r$.
Both $F_i$ have generic $r$ degree six. Form the $12$ by $12$ matrix
$\mathscr S$ whose rows are the descending coefficients of

$$
r^5F_0,r^4F_0,\ldots,F_0,
\quad r^5F_1,r^4F_1,\ldots,F_1
$$

in columns $r^{11},r^{10},\ldots,1$. Form also the $10$ by $11$
matrix $\mathscr M$ with rows
$r^4F_0,r^3F_0,\ldots,F_0,r^4F_1,r^3F_1,\ldots,F_1$
in columns $r^{10},r^9,\ldots,1$, denoted $c_{10},\ldots,c_0$.
Define

$$
\begin{gathered}
S_1=\det(c_{10},c_9,\ldots,c_2,c_1),\qquad
S_0=\det(c_{10},c_9,\ldots,c_2,c_0),\\
\gamma=2430b^{13}(8b-1)^3(2b+1),\\
\det\mathscr S=72900b^{20}(8b-1)^4(2b+1)^2
                  \mathcal E(b;p,v),\qquad
S_i=\gamma\lambda_i(b;p,v)\quad(i=0,1).
\end{gathered}
\tag{21.3}
$$

These are exact polynomial identities over $\mathbb Z[b,p,v]$.
They fix every scalar and sign, with no later primitive-part operation.
The full integer coefficient array in Section 24 is another specification
of the same three quotients. In monomial order $(b,p,v)$ their nonzero
term counts and coordinate degrees are

$$
\begin{array}{c|c|c}
 &\text{terms}&(\deg_b,\deg_p,\deg_v)\\ \hline
\mathcal E&644&(22,6,6)\\
\lambda_1&399&(18,5,5)\\
\lambda_0&378&(19,5,5).
\end{array}
\tag{21.4}
$$

For any finite common $r$ root of $F_0,F_1$, evaluation of the rows of
$\mathscr M$ gives

$$
S_1r+S_0
=\det(c_{10},\ldots,c_2,c_1r+c_0)=0,
\tag{21.5}
$$

since $c_1r+c_0=-\sum_{k=2}^{10}c_kr^k$.
This is the ordered-minor argument of [O], Theorem 20.2, with the
projection interchanged. The fixed-size Sylvester matrix likewise has a
nonzero evaluation vector in its kernel at any common finite root.
Neither implication requires preservation of the generic degree or a
simple common root. On $b>0$, $b\ne1/8$, the removed factors in (21.3)
are nonzero. Every regular world over $K_3$ therefore satisfies

$$
\mathcal E(b;p,v)=0,\qquad
\lambda_1(b;p,v)r+\lambda_0(b;p,v)=0.
\tag{21.6}
$$

The remaining regular source $b=1/8$ has $e=0$ and $p=24$ by Lemma 6.1,
and hence cannot lie over $K_3$. Where $\lambda_1\ne0$, a fixed finite
$b$ admits at most one common $r$, namely $-\lambda_0/\lambda_1$.
This is a necessary lift relation, not an existence assertion.

For any strict regular source the original parent fixes
$e=-3Ajn/D$, $d=24+e=-C_0/D$, and the whole gain is the unique
interpolant of $C_i/D$ at $0,1,2,3$. Its traces at clocks zero through
six and at the two alternative seventh actions are respectively

$$
(1,j,T,n,U,U+n,2U+n),\qquad T+2j+4r,\qquad3U+2n.
\tag{21.7}
$$

Thus a regular geometry has at most one complete-world lift. Lemma 2.2,
(2.3)--(2.5), gives all original readings for that lift; the unequal
readings $0,24$ ensure that its one gain is not the zero polynomial.
In particular the known $W_3$ and $Z_3$ are actual lifts independently
of the eliminant. No gain sample, leading gain coefficient, drift,
$e$, or gain-root difference is cancelled in these implications.

**Definition 21.2 (The existing singular image in a fixed sign convention).**
At $b=1/8$ put

$$
\begin{gathered}
J_s=1+64r-64r^2,\quad N_s=1+72r-64r^2,\\
q=107J_sN_s-480(J_s+N_s)
 =438272r^4-931328r^3+540800r^2-50728r-853,\\
k_p=72J_sN_s+(10+N_s)(196J_sN_s-1080N_s-720J_s),\\
k_v=8J_sN_s+(20+N_s)(50J_sN_s-288N_s-160J_s),\\
E_s=9(p-24)k_v-(v-84-3N_s)k_p,\\
h_s=(14982985728p-5246389760v+494892469248)r^3\\
\qquad+(-19475629824p+5440701760v-449551623744)r^2\\
\qquad+(-2154767712p+1307330280v-61223107032)r\\
\qquad+40933920p+7210730v-1537135965,\\
T_s(p,v)=\frac{\operatorname{Res}_r(q,h_s)}
                  {4413938512638368063632179200}.
\end{gathered}
\tag{21.8}
$$

The resultant in (21.8) is the fixed $7$ by $7$ determinant with rows
$r^2q,rq,q,r^3h_s,r^2h_s,rh_s,h_s$ in columns $r^6,\ldots,1$.
The quotient is an integer polynomial with the fifteen coefficients
in Section 24. Here $q$ is exactly the published singular polynomial
$\Phi$ of [S], Section 3, not the target map $\Phi(W)$ of Section 17;
$T_s$ is exactly $-S_4$ of [S], Definition 9.1. In particular the
$v^4$ coefficient of $T_s$ is $-99133686444483896037925$.
Singular coverage is [S], Lemma 9.2.

The zero-safe correspondence with that coverage can also be expressed by
the following polynomial and original-response identities:

$$
\begin{gathered}
\Lambda(r,1/8)=q/(15J_sN_s),\\
p-24=\frac{e k_p}{72J_sN_s},\qquad
v-84-3N_s=\frac{e k_v}{8J_sN_s},\\
107^3 E_s-24h_s=q R_s,\\
R_s=27574321152r^4-62042222592r^3\\
\quad+(-329731200p+143616256v+25511292672)r^2\\
\quad+(370947600p-161568288v+10505729088)r\\
\quad+109079010p-25033292v-437956836.
\end{gathered}
\tag{21.9}
$$

The parent equation with $\Lambda=0$ forces $b=1/8$, since $\kappa>0$.
For a strict source $J_s,N_s>0$. Consequently a singular world has
$q=E_s=h_s=0$, including when $e=0$, and hence $T_s(p,v)=0$.
This uses the existing singular image and its coverage; the specialized
nonzero bound over $K_3$ below is the additional exclusion used here.

## 22. Exact third-rectangle coefficient, root and lifting certificates

**Definition 22.1 (Finite rational evaluation rules).**
Use the finite Taylor enclosure rule (18.4), in its multivariable
coefficient form, for the following specified polynomial inputs.
For a polynomial $Q(x)=\sum_\nu a_\nu x^\nu$ in $n$ variables,
a rational centre $x^0$ and rational half-widths $h_i\ge0$, define

$$
\begin{aligned}
q_\alpha(Q;x^0)
 &=\sum_{\nu\ge\alpha}a_\nu
       \prod_{i=1}^n\binom{\nu_i}{\alpha_i}(x_i^0)^{\nu_i-\alpha_i},\\
H_h(Q;x^0)&=\sum_{\alpha\ne0}|q_\alpha(Q;x^0)|
                      \prod_{i=1}^n h_i^{\alpha_i},\\
\mathcal T_{x^0,h}(Q)&=
 [q_0(Q;x^0)-H_h(Q;x^0),q_0(Q;x^0)+H_h(Q;x^0)].
\end{aligned}
\tag{22.1}
$$

All sums are finite and rational, with $0^0=1$. They enclose $Q$ on the
closed product of the stated centre intervals. They use every monomial,
including mixed terms; no first-order or asymptotic truncation is made.
Interval addition and negation are exact endpoint operations,
multiplication takes the hull of the four endpoint products, and division
is permitted only by an interval excluding zero. A square is its exact
interval image, with lower endpoint zero if the interval contains zero.
Every terminating decimal below denotes an exact rational number.

Let

$$
\bar p=7.2830365,\quad\bar v=61.4943725,\quad\rho=0.0000005,
\qquad\mathcal E(b;p,v)=\sum_{k=0}^{22}c_k(p,v)b^k.
\tag{22.2}
$$

For these $23$ coefficients let
$C_k=c_k(\bar p,\bar v)$ and
$H_k=H_{(\rho,\rho)}(c_k;(\bar p,\bar v))$.
The following table gives both exact rationals and an outward error-ratio
bound $H_k/|C_k|\le u_k/10^{12}$, in ascending $b$ degree.

| $k$ | $C_k$ | $H_k$ | sign | $u_k$ |
| --- | --- | --- | --- | --- |
| $0$ | $\frac{361736766749751312449903922617053916570022000673341}{1000000000000000000000000000000}$ | $\frac{1054330473881752009874146542187538556269560483}{25000000000000000000000000000000}$ | $+$ | $116586$ |
| $1$ | $\frac{3389097858559222430554355164102941290342283481147999}{400000000000000000000000000000}$ | $\frac{69597629974823852767805117735273727297752086809}{50000000000000000000000000000000}$ | $+$ | $164286$ |
| $2$ | $\frac{-235733035163271280577979239949677786762322800284637419}{800000000000000000000000000000}$ | $\frac{7035550909452415115963163483076109115182066795057}{100000000000000000000000000000000}$ | $-$ | $238764$ |
| $3$ | $\frac{-2025969230470117498996581620389103328808393680167490853}{800000000000000000000000000000}$ | $\frac{103246741525244044665115675323442980828677397782569}{100000000000000000000000000000000}$ | $-$ | $407694$ |
| $4$ | $\frac{34790010707595061185906472055518951230854017564835682899}{2000000000000000000000000000000}$ | $\frac{3063320602154497836772071237469543726765928266199513}{100000000000000000000000000000000}$ | $+$ | $1761035$ |
| $5$ | $\frac{474416857165432609217823557278203997930021090651752355937}{2000000000000000000000000000000}$ | $\frac{1282948844128016951910287310721339322457094228185847}{5000000000000000000000000000000}$ | $+$ | $1081706$ |
| $6$ | $\frac{442158862698122765215169501414894451351051516428969278363}{1000000000000000000000000000000}$ | $\frac{9831874993783933540674957350492741819345321268180307}{10000000000000000000000000000000}$ | $+$ | $2223607$ |
| $7$ | $\frac{-308908958242286132137141181021091394501715941596172958106861}{64000000000000000000000000000000}$ | $\frac{1842292306398552930757375555629488868274105260999178713}{1600000000000000000000000000000000}$ | $-$ | $238555$ |
| $8$ | $\frac{-8580785790964560054651502123491902857619871517278808219873821}{256000000000000000000000000000000}$ | $\frac{6545661497968345925187917149322747483329291286632846041}{1280000000000000000000000000000000}$ | $-$ | $152566$ |
| $9$ | $\frac{-47151032677083301840676795103008725497605138659601718325396299}{512000000000000000000000000000000}$ | $\frac{63268311102999304477618118470622423895802256901074628489}{2560000000000000000000000000000000}$ | $-$ | $268365$ |
| $10$ | $\frac{-100036564605724992932351311944687156856903473121039942478436809}{1024000000000000000000000000000000}$ | $\frac{1102594117349698282138530449953066227589693692425860225887}{25600000000000000000000000000000000}$ | $-$ | $440877$ |
| $11$ | $\frac{10360788851484906972850642414361943483665838115384149723722299}{102400000000000000000000000000000}$ | $\frac{194762862010994461966978266918425418491479521804766951119}{12800000000000000000000000000000000}$ | $+$ | $150385$ |
| $12$ | $\frac{6924048807903823831396660633763336251937456664226888097841759}{16000000000000000000000000000000}$ | $\frac{227674269378949375098551255208022968254019138299923506803}{3200000000000000000000000000000000}$ | $+$ | $164409$ |
| $13$ | $\frac{240311880318930126961607956847973522524983407061229003972410637}{512000000000000000000000000000000}$ | $\frac{3380128795614324715626930186253044202905092504918864313229}{25600000000000000000000000000000000}$ | $+$ | $281312$ |
| $14$ | $\frac{22675508798375819898974716727278806792176083116880068888860427}{2048000000000000000000000000000000}$ | $\frac{4140924353190137814986060906312611874841099522857078589387}{51200000000000000000000000000000000}$ | $+$ | $7304665$ |
| $15$ | $\frac{-238447787626766356250599143082607683120618063181560129928369273}{512000000000000000000000000000000}$ | $\frac{402138668781237042153261588819612520613529326823608166967}{12800000000000000000000000000000000}$ | $-$ | $67460$ |
| $16$ | $\frac{-407172978120385932040135969219118742379924862703433160906163203}{819200000000000000000000000000000}$ | $\frac{9137136567993318492666711613578054152012296697225529430607}{102400000000000000000000000000000000}$ | $-$ | $179524$ |
| $17$ | $\frac{-2498731020750533369097211619735500489838148681407445607219931}{10240000000000000000000000000000}$ | $\frac{1769043241642141724597215842884914347706605910809929218053}{25600000000000000000000000000000000}$ | $-$ | $283191$ |
| $18$ | $\frac{-69909219432944750357915007127100909403199198238963851656527}{2048000000000000000000000000000}$ | $\frac{159090609294461582491112991113690156744891503543631357977}{6400000000000000000000000000000000}$ | $-$ | $728216$ |
| $19$ | $\frac{59510528805303257716247023861107067154548614104994983164789}{1638400000000000000000000000000}$ | $\frac{2853651478967283021175849351860798708736784670395959851}{5120000000000000000000000000000000}$ | $+$ | $15345$ |
| $20$ | $\frac{4417818597827651865178011093976487983031112475921323348923}{262144000000000000000000000000}$ | $\frac{12180934388766051319803596478773396153441038134585603453}{4096000000000000000000000000000000}$ | $+$ | $176463$ |
| $21$ | $\frac{-238175198548699081775228263667930810141675040689062281}{131072000000000000000000000}$ | $\frac{1814250143283689557428680509648886849860380621987783}{12800000000000000000000000000000}$ | $-$ | $78002$ |
| $22$ | $\frac{-42373675662696931834276996581899347137039540473512429}{419430400000000000000000000}$ | $\frac{7179305482020796237296526443549077624492676682401723}{163840000000000000000000000000000}$ | $-$ | $433737$ |

In particular every $c_k$ has its displayed nonzero sign throughout
$K_3$. The sign string from $c_0$ through $c_{22}$ is

$$
\texttt{++--+++----++++----++--},\qquad
\operatorname{var}(c_0,\ldots,c_{22})=7,
\qquad\max_k H_k/|C_k|<1/100000.
\tag{22.3}
$$

Thus $\mathcal E(\,\cdot\,;p,v)$ has degree exactly $22$, nonzero
constant term, and at most seven positive real roots counted with
multiplicity for every $(p,v)\in K_3$, by Descartes' rule of signs.

Define four positive closed intervals

$$
\begin{gathered}
B_1=[0.74775,0.74778],\quad B_2=[0.78806,0.78810],\\
B_3=[2.8856,2.8858],\quad B_4=[7.7898,7.79].
\end{gathered}
\tag{22.4}
$$

For an endpoint $\beta$, evaluate (22.1) in variables $(b,p,v)$ at
$(\beta,\bar p,\bar v)$ with half-widths $(0,\rho,\rho)$.
The two endpoint enclosures are as follows; the positive scale $10^s$
divides only the values of $\mathcal E$.

| interval | $s$ | $10^{-s}\mathcal E(\min B_i;K_3)$ | $10^{-s}\mathcal E(\max B_i;K_3)$ |
| --- | --- | --- | --- |
| $B_1$ | $20$ | $[-1343,-1338]$ | $[1842,1846]$ |
| $B_2$ | $20$ | $[3220,3228]$ | $[-4468,-4460]$ |
| $B_3$ | $30$ | $[-2484,-2471]$ | $[3809,3822]$ |
| $B_4$ | $38$ | $[2127,2141]$ | $[-2703,-2690]$ |

Every target in $K_3$ therefore gives at least one positive root in the
interior of each $B_i$. Uniqueness at the exact target will follow from
the multiplicity budget, not from these endpoint signs alone.

For lifting put

$$
I_Z=[0.046421583505,0.046421603505],\qquad
I_c=[0.1275805397,0.1275805398].
\tag{22.5}
$$

For any row interval $I=[l,u]$ in the following table use (22.1) at
$((l+u)/2,\bar p,\bar v)$ with half-widths $((u-l)/2,\rho,\rho)$.
Denote these exact rational intervals for $\lambda_i$ by $\mathcal T_I(\lambda_i)$.
The table gives outward enclosures of $\mathcal T_I(\lambda_1)$ and of
$-\mathcal T_I(\lambda_0)/\mathcal T_I(\lambda_1)$. The quotient uses
the exact intervals from (22.1), before widening for the printed columns.

| $I$ | $s$ | $10^{-s}\mathcal T_I(\lambda_1)$ | $-\mathcal T_I(\lambda_0)/\mathcal T_I(\lambda_1)$ |
| --- | --- | --- | --- |
| $I_Z$ | $13$ | $[-4856,-4855]$ | $[0.0484719,0.0484726]$ |
| $I_c$ | $15$ | $[3355,3356]$ | $[0.90050,0.90052]$ |
| $B_1$ | $16$ | $[5732,10023]$ | $[2,5]$ |
| $B_2$ | $17$ | $[7188,8147]$ | $[-1.5,-1]$ |
| $B_3$ | $29$ | $[1753,1755]$ | $[4.30,4.32]$ |
| $B_4$ | $36$ | $[-3543,-3541]$ | $[-6.91,-6.89]$ |

All six $\lambda_1$ intervals exclude zero. In each of $B_1,\ldots,B_4$
the only possible finite common $r$ is outside $0<r<1$. The two other
rows provide uniqueness of a finite common $r$; existence there is
supplied only by actual worlds.

For the independent singular normalization of (21.8), rule (22.1) at
$(\bar p,\bar v)$ with half-widths $(\rho,\rho)$ gives

$$
10^{-22}T_s(K_3)\subset[-1570,-1565].
\tag{22.6}
$$

Together with [S], Lemma 9.2, this excludes every singular-source world
over $K_3$, including every real drift on the singular parent.

For clarity the derivative needed at $W_3$ is taken in $(r,b)$, with $b$
fixed when differentiating in $r$. Put

$$
L=b\delta,\qquad P_0=F_0(r,b,0),\qquad
Q_r=(\partial_rP_0)L-P_0\partial_rL.
\tag{22.7}
$$

Then $p=P_0/L$ and $p_r=Q_r/L^2$ on the regular chart. Use (22.1) on
the closed source rectangle

$$
X_c=[0.9005088162,0.9005088163]
       \times[0.1275805397,0.1275805398]
\tag{22.8}
$$

with its midpoint and both half-widths $0.00000000005$.
Evaluate $D=\delta/b^2$ by dividing the Taylor interval of $\delta$
by the exact positive $b^2$ interval, and $p_r$ by dividing the Taylor
interval of $Q_r$ by the square of the Taylor interval of $L$.
The rational enclosures are

$$
\begin{gathered}
\mathcal T_{X_c}(L)\subset(-0.000150,-0.000149),\\
D(X_c)\subset[-0.071890,-0.071889],\qquad
p_r(X_c)\subset[51960,51970],\qquad p_r(W_3)>51960.
\end{gathered}
\tag{22.9}
$$

**Lemma 22.2 (The specialized certificate identities and inclusions).**
The exact divisions (21.3), (21.8), the source identities (21.2),
(21.9), and every rational table and inclusion in this section hold.

*Proof.* Expand (21.1) and extract all seven coefficients in $r$, including
zeros, for each $F_i$. In each prescribed row the coefficient of $r^k$
in $r^aF_i$ is $[r^{k-a}]F_i$, interpreted as zero outside degrees
$0,\ldots,6$. Expand each fixed determinant by
$\det A=\sum_\sigma\operatorname{sgn}(\sigma)\prod_i A_{i,\sigma(i)}$.
Multiplication by the respective divisors in (21.3) recovers these
determinants from the complete coefficient arrays in Section 24.
The same coefficient comparison for the seven-row determinant in
(21.8) gives its stated scalar and the fifteen-term $T_s$ array.
These polynomial comparisons establish the exact divisions without
any specialization or leading-coefficient assumption. Substitution of
$X=bj$, $N=bn$ into (2.3) gives (21.2); expansion of (21.8) gives
(21.9). The resulting $T_s$ is $-S_4$ with the sign convention of [S],
Definition 9.1.

Apply the finite binomial sum (22.1) to each of the $23$ coefficient
polynomials specified in Section 24. The exact $C_k,H_k$ values in the
table result; comparing the integer cross-products gives
$10^{12}H_k\le u_k|C_k|$ and $u_k<10^7$ for every $k$.
The endpoint table uses the same sum with zero $b$ half-width.
For the lifting table use the specified midpoint of each $I$ and its
half-width. Each $\mathcal T_I(\lambda_1)$ excludes zero, so taking
the hull of the four exact endpoint quotients gives the displayed
$r$ enclosure. Equation (22.6) uses the fifteen coefficients of $T_s$.
Finally expand $L,Q_r$ from (22.7) and use the midpoint of (22.8).
The $L$ enclosure excludes zero; the positive $b$ interval and the
squared $L$ interval are therefore lawful denominators in (22.9).
The strict last bound follows from the sharper rational enclosure

$$
p_r(X_c)\subset
[1299159933837/25000000,5196645965191/100000000]
\subset(51960,51970).
\tag{22.10}
$$

All operations here are exact integer coefficient comparisons and finite
rational sums with their stated input arrays and intervals. The
root-count consequence is the classical Descartes rule; the endpoint
existence consequence is the intermediate value theorem. No numerical
approximation to $W_3$ is used as its definition. $\square$

## 23. The exact third-critical entire child and its open local exclusion

**Theorem 23.1 (Exact whole-child inventory at the third critical target).**
With the original complete-world meaning of the child,

$$
C(p_3,v_3)=\{W_3,Z_3\}.
\tag{23.1}
$$

Moreover $\mathcal E(\,\cdot\,;p_3,v_3)$ has precisely six positive
root locations: $b(Z_3)$, $b_3$, and one root in each $B_i$.
The root at $b_3$ has multiplicity exactly two; the other five are simple.

*Proof.* On a regular source neighbourhood of $W_3$ with $b\ne1/8$,
(21.2)--(21.3) give the identity

$$
\mathcal E(b;p(r,b),v(r,b))=0.
\tag{23.2}
$$

By (22.9) $dp(W_3)\ne0$. Theorem 13.3 gives
$\operatorname{rank}D(p,v,m)(W_3)=1$, so $dv$ is proportional to $dp$
there. The vector $k=(-p_b,p_r)$, in independent $(r,b)$ coordinates,
satisfies $dp(k)=dv(k)=0$ and has $b$ component $p_r\ne0$.
Differentiate (23.2) along this vector at $W_3$:

$$
0=\mathcal E_b(b_3;p_3,v_3)p_r(W_3).
\tag{23.3}
$$

Thus $b_3$ is a positive root of multiplicity at least two. The
nonzero leading coefficient in (22.3) ensures that this is a root
of a nonzero polynomial.

Theorem 18.1 supplies the actual $Z_3$ with $b(Z_3)\in I_Z$, hence
another positive root. The four opposite endpoint signs supply a root
inside each $B_i$. These six locations are pairwise disjoint, and
$b_3\in\operatorname{int}I_c$ by Lemma 13.2. Their multiplicities
total at least $1+2+4=7$. Descartes' upper bound (22.3) is seven.
Consequently they exhaust all positive roots, with exactly the
multiplicities stated in the theorem.

Every regular world in the exact child projects to one of those roots
by (21.6). The lifting table excludes a strict $r$ at the four $B_i$
roots. At $b(Z_3)$ and $b_3$, $\gamma\lambda_1\ne0$, so (21.5) forces
one unique finite $r$. The known actual worlds already supply those
two lifts. The original parent and whole-gain reconstruction in Lemma
2.2 then force a unique drift and polynomial at each geometry.
Equation (22.6) and the existing singular coverage exclude all singular
worlds, while the remaining regular $b=1/8$ case has $p=24$.
This exhausts the entire original child, including unused companions.
No lift is inferred from one of the four nonstrict eliminant roots,
and a double root is not counted as two worlds. $\square$

**Theorem 23.2 (Open target neighbourhood with entire-child $J$ injectivity).**
There exists an open neighbourhood $V$ of $y_3$, contained in
$\operatorname{int}K_3$, such that for every $y\in V$ the entire
original child $C(y)$ has at most three complete worlds and its
clock-seven $J$ response $a$ is injective. In particular no original
independent-pair configuration (16.6) has target in $V$.

*Proof.* Start with the full-parent neighbourhood $\mathcal U_3$ of
Section 19. Shrink it using (22.9) and the inverse-function theorem
so that $(p,b)$ is injective there as well: the determinant of
$D(p,b)$ in coordinates $(r,b)$ is $p_r\ne0$ at $W_3$.
Retain $(p,a)$ injective, $313<a<314$, and
$\mathcal U_3\subset\Phi^{-1}(\operatorname{int}K_3)$, and also require
$b(\mathcal U_3)\subset\operatorname{int}I_c$.
Let $\mathcal U_Z$ be the relatively open full-parent set whose source
geometry belongs to $\operatorname{int}R$.
It contains $Z_3$ by Theorem 18.1, and is disjoint from $\mathcal U_3$.
All its worlds are regular by (18.10); at a target in $K_3$ it contains
exactly the unique remote world $Z(y)$. The remote $a$ interval in
(18.11) is disjoint from $(313,314)$, with gap greater than
$46011537/500000$.

We claim that an open $V$ about $y_3$, inside $\operatorname{int}K_3$,
can be chosen so that

$$
\Phi^{-1}(V)\subset\mathcal U_3\cup\mathcal U_Z.
\tag{23.4}
$$

Otherwise choose targets $y_n\to y_3$ in $\operatorname{int}K_3$ and
whole worlds $W_n\in C(y_n)$ outside that open union. Theorem 17.2
gives a subsequence converging in all complete-world coordinates to a
strict world $W$. By continuity $W\in C(y_3)$, so Theorem 23.1 makes
$W$ equal to $W_3$ or $Z_3$. Both lie in the open union, whereas its
complement is relatively closed. This is a contradiction and proves
(23.4). Only compactness of individual complete worlds is used;
no closedness of a distinct-pair relation is required.

For $y\in V$, two worlds of $C(y)\cap\mathcal U_3$ with equal $a$
are equal by $(p,a)$ injectivity. There is only one world in
$C(y)\cap\mathcal U_Z$. A world in each set cannot have equal $a$
because of the separated intervals. Equation (23.4) therefore proves
$a$ injective on the entire child, without imposing any condition on
an independently selected $M$ pair.

For the cardinality bound, (22.4) supplies four distinct positive roots
of $\mathcal E(\,\cdot\,;y)$, and the actual remote world supplies a
fifth in $I_Z$. These five locations lie outside $I_c$. At most two
positive-root multiplicities remain by (22.3). Distinct worlds in
$C(y)\cap\mathcal U_3$ have distinct $b$, since their $p$ is fixed
and $(p,b)$ is injective on this neighbourhood. They therefore consume
distinct remaining positive roots in $I_c$, giving at most two such
worlds. Together with $Z(y)$ this is at most three.

The $J$ pair required in (16.6) is impossible by the already proved
entire-child injectivity. The conclusion allows every original
cross-pair overlap and requires no equality between the common $a$
and common $m$. The neighbourhood $V$ is asserted to exist; no
numerical radius for it is specified. $\square$

**Corollary 23.3 (Exactly three along the third $M$ germ, and the original
$\mathsf J_3,\mathsf Q_3$ sentences).** For all sufficiently small
nonzero real $h$, let $y(h)=\Phi(W_3^+(h))=\Phi(W_3^-(h))$ for the
actual germ of Theorem 15.1. Then

$$
\begin{gathered}
C(y(h))=\{W_3^+(h),W_3^-(h),Z(y(h))\},\qquad |C(y(h))|=3,\\
a\text{ is injective on }C(y(h)),\qquad
\neg\mathsf J_3,\qquad\neg\mathsf Q_3.
\end{gathered}
\tag{23.5}
$$

Here $\mathsf J_3$ and $\mathsf Q_3$ are exactly (16.7) and (16.8).

*Proof.* The two actual distinct germ worlds tend to $W_3$, so they
eventually lie in $\mathcal U_3$ and have target in $V$. Theorem 18.1
supplies the distinct remote world in $\mathcal U_Z$. The upper bound
of Theorem 23.2 makes these exactly all three worlds. Their gains and
drifts are their own original complete-world lifts, with no added
nonvanishing sample or degree hypothesis. Entire-child $J$ injectivity
is the other conclusion of that theorem.

Since $y_3\in V$, the distinct equal-$a$ pair in the precise sentence
(16.7) cannot exist, proving $\neg\mathsf J_3$.
If (16.8) held, Theorem 16.4 would give original joint configurations
whose selected $M$ endpoints both converge as complete worlds to
$W_3$. Their targets would converge to $y_3$, eventually lying in
$V$, where Theorem 23.2 excludes every such configuration.
This proves $\neg\mathsf Q_3$ using its original Euclidean-squared
quantifiers, regardless of the locations of the $J$ endpoints.
Equivalently, Theorem 19.2 would force a third world at the exact
base, contradicting Theorem 23.1. $\square$

Theorem 23.1 is an exact two-world inventory at $y_3$ only.
Theorem 23.2 is a whole-child exclusion and an at-most-three bound on
some open $V$ only. The exact-three conclusion of Corollary 23.3 is
restricted to the sufficiently small nontrivial actual $M$ germ;
no constant-cardinality assertion on $V$ or $K_3$ is made.

For $i=1,2$, the sentences $\mathsf J_i,\mathsf Q_i$ retain their full
definitions (16.7)--(16.8); the third-target inventory does not decide
them. For the fourth target the separate $\neg\mathsf J_4$ and
$\neg\mathsf Q_4$, the entire $K_+=[56,58]\times[304,306]$ $J$
exclusion, and the specified fourth source neighbourhood are exactly
those of [SV], Theorems 9.2 and 12.2, with no enlargement.
The original sentence $\mathsf I$ continues to quantify over all
$p\ne24$ and all entire strict children, including separated selected
$M$ pairs outside these exclusions. It requires one independent
distinct $J$ pair and one independent distinct $M$ pair in the same
child, permits cross-pair overlap, and does not require $a=m$.
No truth value for that global sentence is asserted here.

## 24. Complete polynomial coefficient tables and mathematical suppliers

For the three normalized polynomials in (21.3) use

$$
(\mathcal E,\lambda_1,\lambda_0)
  =\sum_{(k,i,j)}(e_{kij},\ell_{kij},d_{kij})b^kp^iv^j.
\tag{24.1}
$$

Every nonzero monomial of any of the three polynomials occurs in the
following table. A printed zero is a zero coefficient, and every
unlisted exponent triple has zero coefficient in all three polynomials.
Thus the table specifies all coefficients, including every degree drop
after target specialization. The definitions (21.1)--(21.3), with
their fixed row and column orders, fix the same integer polynomials.

| $(k,i,j)$ | $e_{kij}$ | $\ell_{kij}$ | $d_{kij}$ |
| --- | --- | --- | --- |
| $(22,6,0)$ | $29370937500000000$ | $0$ | $0$ |
| $(22,5,1)$ | $-32656500000000000$ | $0$ | $0$ |
| $(22,5,0)$ | $22550010187500000000$ | $0$ | $0$ |
| $(22,4,2)$ | $14603948437500000$ | $0$ | $0$ |
| $(22,4,1)$ | $-19124795418750000000$ | $0$ | $0$ |
| $(22,4,0)$ | $4038566421269531250000$ | $0$ | $0$ |
| $(22,3,3)$ | $-3359218437500000$ | $0$ | $0$ |
| $(22,3,2)$ | $6225112635468750000$ | $0$ | $0$ |
| $(22,3,1)$ | $-2272868074250859375000$ | $0$ | $0$ |
| $(22,3,0)$ | $-136023587217874687500000$ | $0$ | $0$ |
| $(22,2,4)$ | $419236576171875$ | $0$ | $0$ |
| $(22,2,3)$ | $-974005093406250000$ | $0$ | $0$ |
| $(22,2,2)$ | $456275074130876953125$ | $0$ | $0$ |
| $(22,2,1)$ | $84233102335619203125000$ | $0$ | $0$ |
| $(22,2,0)$ | $-9276021426813578718750000$ | $0$ | $0$ |
| $(22,1,5)$ | $-26897400000000$ | $0$ | $0$ |
| $(22,1,4)$ | $73111449993750000$ | $0$ | $0$ |
| $(22,1,3)$ | $-37669261130071875000$ | $0$ | $0$ |
| $(22,1,2)$ | $-16689994131061856250000$ | $0$ | $0$ |
| $(22,1,1)$ | $3142634102852360175000000$ | $0$ | $0$ |
| $(22,1,0)$ | $24980047458363055800000000$ | $0$ | $0$ |
| $(22,0,6)$ | $691200000000$ | $0$ | $0$ |
| $(22,0,5)$ | $-2091821760000000$ | $0$ | $0$ |
| $(22,0,4)$ | $1010605501395000000$ | $0$ | $0$ |
| $(22,0,3)$ | $1070614870141950000000$ | $0$ | $0$ |
| $(22,0,2)$ | $-264640046103518400000000$ | $0$ | $0$ |
| $(22,0,1)$ | $-5395130655065595720000000$ | $0$ | $0$ |
| $(22,0,0)$ | $123050268339471946800000000$ | $0$ | $0$ |
| $(21,6,0)$ | $145975218750000000$ | $0$ | $0$ |
| $(21,5,1)$ | $-176156798437500000$ | $0$ | $0$ |
| $(21,5,0)$ | $-175125854334375000000$ | $0$ | $0$ |
| $(21,4,2)$ | $86497178828125000$ | $0$ | $0$ |
| $(21,4,1)$ | $155681687822343750000$ | $0$ | $0$ |
| $(21,4,0)$ | $-109007649837004921875000$ | $0$ | $0$ |
| $(21,3,3)$ | $-21993149207031250$ | $0$ | $0$ |
| $(21,3,2)$ | $-54014433049523437500$ | $0$ | $0$ |
| $(21,3,1)$ | $72188422482707191406250$ | $0$ | $0$ |
| $(21,3,0)$ | $-6805080698241237187500000$ | $0$ | $0$ |
| $(21,2,4)$ | $3034754197656250$ | $0$ | $0$ |
| $(21,2,3)$ | $9254386808429296875$ | $0$ | $0$ |
| $(21,2,2)$ | $-17830877012271147656250$ | $0$ | $0$ |
| $(21,2,1)$ | $3286146611452874814843750$ | $0$ | $0$ |
| $(21,2,0)$ | $47147157477704152546875000$ | $0$ | $0$ |
| $(21,1,5)$ | $-214213665000000$ | $0$ | $0$ |
| $(21,1,4)$ | $-791279756853750000$ | $0$ | $0$ |
| $(21,1,3)$ | $1950538051495622109375$ | $0$ | $0$ |
| $(21,1,2)$ | $-528002136253723215937500$ | $0$ | $0$ |
| $(21,1,1)$ | $-16034964615550707215625000$ | $0$ | $0$ |
| $(21,1,0)$ | $188209467496176779722500000$ | $0$ | $0$ |
| $(21,0,6)$ | $6001920000000$ | $0$ | $0$ |
| $(21,0,5)$ | $27251736984000000$ | $0$ | $0$ |
| $(21,0,4)$ | $-79900394572440000000$ | $0$ | $0$ |
| $(21,0,3)$ | $28224606663336394125000$ | $0$ | $0$ |
| $(21,0,2)$ | $1337490126818091006750000$ | $0$ | $0$ |
| $(21,0,1)$ | $-22138794040657073787000000$ | $0$ | $0$ |
| $(21,0,0)$ | $-2307821987855329452540000000$ | $0$ | $0$ |
| $(20,6,0)$ | $-18568825572656250000$ | $0$ | $0$ |
| $(20,5,1)$ | $21314213977265625000$ | $0$ | $0$ |
| $(20,5,0)$ | $-14516137147386093750000$ | $0$ | $0$ |
| $(20,4,2)$ | $-9912524671064453125$ | $0$ | $0$ |
| $(20,4,1)$ | $13095703332101765625000$ | $0$ | $0$ |
| $(20,4,0)$ | $-2370647288145892201171875$ | $0$ | $0$ |
| $(20,3,3)$ | $2392367280463281250$ | $0$ | $0$ |
| $(20,3,2)$ | $-4605529857698465625000$ | $0$ | $0$ |
| $(20,3,1)$ | $1550277293193836810156250$ | $0$ | $0$ |
| $(20,3,0)$ | $-7407812002390814425781250$ | $0$ | $0$ |
| $(20,2,4)$ | $-316645968237656250$ | $0$ | $0$ |
| $(20,2,3)$ | $792464683601853750000$ | $0$ | $0$ |
| $(20,2,2)$ | $-376984697351305798828125$ | $0$ | $0$ |
| $(20,2,1)$ | $2638306073205484163437500$ | $0$ | $0$ |
| $(20,2,0)$ | $466974060690206149127578125$ | $0$ | $0$ |
| $(20,1,5)$ | $21841055876000000$ | $0$ | $0$ |
| $(20,1,4)$ | $-66897896841726000000$ | $0$ | $0$ |
| $(20,1,3)$ | $40364790017125100765625$ | $0$ | $0$ |
| $(20,1,2)$ | $-254716946573382709031250$ | $0$ | $0$ |
| $(20,1,1)$ | $-153789926254919692271437500$ | $0$ | $0$ |
| $(20,1,0)$ | $-2814427666718902364288625000$ | $0$ | $0$ |
| $(20,0,6)$ | $-614685648000000$ | $0$ | $0$ |
| $(20,0,5)$ | $2220754489310400000$ | $0$ | $0$ |
| $(20,0,4)$ | $-1603736106765673500000$ | $0$ | $0$ |
| $(20,0,3)$ | $3600211144636944590625$ | $0$ | $0$ |
| $(20,0,2)$ | $12519935486249452963734375$ | $0$ | $0$ |
| $(20,0,1)$ | $468279291523877181056025000$ | $0$ | $0$ |
| $(20,0,0)$ | $5779064376656147143476000000$ | $0$ | $0$ |
| $(19,6,0)$ | $-383420758615312500000$ | $0$ | $0$ |
| $(19,5,1)$ | $450273891182109375000$ | $0$ | $0$ |
| $(19,5,0)$ | $-169161746661520664062500$ | $0$ | $-1860159375000000$ |
| $(19,4,2)$ | $-215405812938287500000$ | $0$ | $0$ |
| $(19,4,1)$ | $155226256678095116015625$ | $0$ | $1854489843750000$ |
| $(19,4,0)$ | $-11814614242235001871875000$ | $0$ | $-1474925844375000000$ |
| $(19,3,3)$ | $53754277779472109375$ | $0$ | $0$ |
| $(19,3,2)$ | $-55773870576401813906250$ | $0$ | $-713874195312500$ |
| $(19,3,1)$ | $7657966297329983676562500$ | $0$ | $1091565855281250000$ |
| $(19,3,0)$ | $138930472480211120552343750$ | $0$ | $-296581199772445312500$ |
| $(19,2,4)$ | $-7388433260836421875$ | $0$ | $0$ |
| $(19,2,3)$ | $9836416361298785765625$ | $0$ | $132528345703125$ |
| $(19,2,2)$ | $-1845792139939045332328125$ | $0$ | $-291133701168750000$ |
| $(19,2,1)$ | $-72986551430173052809781250$ | $0$ | $143245691044323046875$ |
| $(19,2,0)$ | $145090392192190002586218750$ | $0$ | $-1447503010381364062500$ |
| $(19,1,5)$ | $530993423143600000$ | $0$ | $0$ |
| $(19,1,4)$ | $-852956913494114850000$ | $0$ | $-11899080000000$ |
| $(19,1,3)$ | $195736820863107647475000$ | $0$ | $33414432236250000$ |
| $(19,1,2)$ | $12738455518658198392518750$ | $0$ | $-22743036423343125000$ |
| $(19,1,1)$ | $-35917087311198912205996875$ | $0$ | $264587308814396250000$ |
| $(19,1,0)$ | $-6323004762456783285897075000$ | $0$ | $99786235297587007500000$ |
| $(19,0,6)$ | $-15606292972800000$ | $0$ | $0$ |
| $(19,0,5)$ | $29119622107549440000$ | $0$ | $414720000000$ |
| $(19,0,4)$ | $-7687992934393969500000$ | $0$ | $-1399010112000000$ |
| $(19,0,3)$ | $-738128715875363068717500$ | $0$ | $1184332796901000000$ |
| $(19,0,2)$ | $1984145594761840397118750$ | $0$ | $-2478070252494000000$ |
| $(19,0,1)$ | $961091026911808793771883750$ | $0$ | $-18575070080862312000000$ |
| $(19,0,0)$ | $29344853159895304178011575000$ | $0$ | $360030064708674864000000$ |
| $(18,6,0)$ | $-3280979140443562500000$ | $0$ | $0$ |
| $(18,5,1)$ | $3903268560418570312500$ | $0$ | $0$ |
| $(18,5,0)$ | $-832895077431890320312500$ | $-685321875000000$ | $-38477338593750000$ |
| $(18,4,2)$ | $-1899385383269266640625$ | $0$ | $0$ |
| $(18,4,1)$ | $768576871174300247343750$ | $724455468750000$ | $40453683328125000$ |
| $(18,4,0)$ | $-25230164387218809702890625$ | $-601885181250000000$ | $-15446686132406250000$ |
| $(18,3,3)$ | $484104059704834671875$ | $0$ | $0$ |
| $(18,3,2)$ | $-278774180970936401390625$ | $-299221414062500$ | $-16625278785546875$ |
| $(18,3,1)$ | $15682340397460264608093750$ | $486012065343750000$ | $12643370710771875000$ |
| $(18,3,0)$ | $560911351459809778739718750$ | $-155849487404695312500$ | $-50962464589573828125$ |
| $(18,2,4)$ | $-68214203513212743750$ | $0$ | $0$ |
| $(18,2,3)$ | $49784144329155864834375$ | $60357525390625$ | $3335405700703125$ |
| $(18,2,2)$ | $-3606128896306295610506250$ | $-143733925298437500$ | $-3804616963557187500$ |
| $(18,2,1)$ | $-284563725274189335845615625$ | $88251740783110546875$ | $177337361006765859375$ |
| $(18,2,0)$ | $-3452546748902449862825353125$ | $-10000677900592364062500$ | $31936604532439630078125$ |
| $(18,1,5)$ | $5042770619732360000$ | $0$ | $0$ |
| $(18,1,4)$ | $-4382727300128435610000$ | $-5955240000000$ | $-326714271000000$ |
| $(18,1,3)$ | $362153588691335801731875$ | $18518481251250000$ | $498654175420500000$ |
| $(18,1,2)$ | $48069885336560378566239375$ | $-16491888101885625000$ | $-58193032718146359375$ |
| $(18,1,1)$ | $1178006070623549000033345625$ | $3616175825818593750000$ | $-8763390562293550687500$ |
| $(18,1,0)$ | $4472903769747301193945073750$ | $-43917253724887402500000$ | $-88074110892885305062500$ |
| $(18,0,6)$ | $-152911216577280000$ | $0$ | $0$ |
| $(18,0,5)$ | $152256068705578944000$ | $230400000000$ | $12513024000000$ |
| $(18,0,4)$ | $-13324264007861403720000$ | $-879345216000000$ | $-24016617470400000$ |
| $(18,0,3)$ | $-2703231046983375019469250$ | $1018212622065000000$ | $5003304166099800000$ |
| $(18,0,2)$ | $-99606371267714128296671250$ | $-327472862121378000000$ | $563697928927692675000$ |
| $(18,0,1)$ | $-1114490771685842277838609125$ | $9260470933797420000000$ | $22658107618698941250000$ |
| $(18,0,0)$ | $49047893533398900154994409375$ | $-859787042383079064000000$ | $-3321800486012629289700000$ |
| $(17,6,0)$ | $-15241587287883721875000$ | $0$ | $0$ |
| $(17,5,1)$ | $18208384135830359531250$ | $0$ | $0$ |
| $(17,5,0)$ | $-2294727194939652032343750$ | $-45424477968750000$ | $-138240744468750000$ |
| $(17,4,2)$ | $-8927087906711130406250$ | $0$ | $0$ |
| $(17,4,1)$ | $2110361871614847487359375$ | $46997565421875000$ | $171118958146875000$ |
| $(17,4,0)$ | $-21598860080833786876500000$ | $-31915010482031250000$ | $57458309637909375000$ |
| $(17,3,3)$ | $2299940874609057034375$ | $0$ | $0$ |
| $(17,3,2)$ | $-765342760240934539228125$ | $-18952179605859375$ | $-83237756873203125$ |
| $(17,3,1)$ | $10741091603527145592618750$ | $24726142260262500000$ | $-31958632768798828125$ |
| $(17,3,0)$ | $976047057258014917677712500$ | $-5676320264146962890625$ | $14846279898575228203125$ |
| $(17,2,4)$ | $-328602501883784784375$ | $0$ | $0$ |
| $(17,2,3)$ | $137017416884538530889375$ | $3725322152031250$ | $19763432448734375$ |
| $(17,2,2)$ | $-1720531710582430619908125$ | $-6988334700853593750$ | $4571388055757109375$ |
| $(17,2,1)$ | $-477222484677778283377235625$ | $2928113708227312500000$ | $-6507478528844757046875$ |
| $(17,2,0)$ | $-10241128103319830602198620000$ | $-58943400594351217734375$ | $-30917974088544730031250$ |
| $(17,1,5)$ | $24701026889662080000$ | $0$ | $0$ |
| $(17,1,4)$ | $-12120333974576183370000$ | $-357927723000000$ | $-2277688023400000$ |
| $(17,1,3)$ | $78315736430240585386875$ | $859727653605750000$ | $87800033740800000$ |
| $(17,1,2)$ | $77742675869865808009950000$ | $-501345384102136546875$ | $890344842614127731250$ |
| $(17,1,1)$ | $3369995327523047160004126875$ | $18761462310950573625000$ | $18032971936067047153125$ |
| $(17,1,0)$ | $44708248632731304812594085000$ | $-164322915381436682812500$ | $-2049880637861360090043750$ |
| $(17,0,6)$ | $-763614253155200000$ | $0$ | $0$ |
| $(17,0,5)$ | $424003956590116800000$ | $13489920000000$ | $101731817600000$ |
| $(17,0,4)$ | $1677571786852308856800$ | $-39028232107200000$ | $-37860019752960000$ |
| $(17,0,3)$ | $-4222451420922105584957925$ | $28494091776952800000$ | $-36141356274209100000$ |
| $(17,0,2)$ | $-274160069039324353397429250$ | $-1457020205936354025000$ | $-2291312441769871820625$ |
| $(17,0,1)$ | $-8248251297959218563098323275$ | $-5977471330933576650000$ | $375472018716652699655625$ |
| $(17,0,0)$ | $22052225997791876077505970750$ | $5439116253554273144700000$ | $-1364766886295754117300000$ |
| $(16,6,0)$ | $-44774537038748898750000$ | $0$ | $0$ |
| $(16,5,1)$ | $53371920391600368375000$ | $0$ | $0$ |
| $(16,5,0)$ | $-4039455436148787026343750$ | $-926251710468750000$ | $1880416896468750000$ |
| $(16,4,2)$ | $-26182124149874499587500$ | $0$ | $0$ |
| $(16,4,1)$ | $3668706711939441155250000$ | $964465156523437500$ | $-1739150936821875000$ |
| $(16,4,0)$ | $15465654373282058849512500$ | $-432593322503582812500$ | $1014321566667933281250$ |
| $(16,3,3)$ | $6768193772683810008125$ | $0$ | $0$ |
| $(16,3,2)$ | $-1316952560501046430858125$ | $-392364083220000000$ | $596952219281281250$ |
| $(16,3,1)$ | $-17305403936746190466577500$ | $336823225962309609375$ | $-729146877717373734375$ |
| $(16,3,0)$ | $750676705064866802066107500$ | $-35423415866672912812500$ | $56432855531816308968750$ |
| $(16,2,4)$ | $-972827430083520560000$ | $0$ | $0$ |
| $(16,2,3)$ | $233775655873881077447625$ | $77975946356421875$ | $-91732170623725000$ |
| $(16,2,2)$ | $6138564485905418046726375$ | $-95924292536879953125$ | $186807034868517384375$ |
| $(16,2,1)$ | $-323760167804164388510485125$ | $18100917095789000953125$ | $-25861696420034410762500$ |
| $(16,2,0)$ | $-14349300004986940018893198375$ | $-65061409090091096953125$ | $-806879894967956710518750$ |
| $(16,1,5)$ | $73750678891914440000$ | $0$ | $0$ |
| $(16,1,4)$ | $-20532236669175346542000$ | $-7585094987200000$ | $5794840175880000$ |
| $(16,1,3)$ | $-890852711934019011593625$ | $11905024792014450000$ | $-20126575571791770000$ |
| $(16,1,2)$ | $45852472505935988529339600$ | $-3052891208969524040625$ | $3812659793975738632500$ |
| $(16,1,1)$ | $4406030420368711696164448425$ | $8320208858005080684375$ | $285109262836260538005000$ |
| $(16,1,0)$ | $106076861297138826185807925450$ | $2388545014468539308456250$ | $-1068573000152684835478125$ |
| $(16,0,6)$ | $-2304769022465280000$ | $0$ | $0$ |
| $(16,0,5)$ | $713954034781159872000$ | $289618960000000$ | $-81475701120000$ |
| $(16,0,4)$ | $46146762913351911156000$ | $-545281459481280000$ | $757961523812352000$ |
| $(16,0,3)$ | $-2137661720469797228256240$ | $169771693113031860000$ | $-177217546667884488000$ |
| $(16,0,2)$ | $-329714864277843145229999730$ | $813762722792256856875$ | $-25252275177396936318375$ |
| $(16,0,1)$ | $-18370612066420179927244964790$ | $-472595724667125152049375$ | $211628735487231544019250$ |
| $(16,0,0)$ | $-120684071929913968611296323350$ | $4068027024735022833825000$ | $4728076778471991872410125$ |
| $(15,6,0)$ | $-91984232997532326937500$ | $0$ | $0$ |
| $(15,5,1)$ | $108887627628458396231250$ | $0$ | $0$ |
| $(15,5,0)$ | $-4790742574810977282318750$ | $-8557724131790625000$ | $18593226710358750000$ |
| $(15,4,2)$ | $-53169996512639337728750$ | $0$ | $0$ |
| $(15,4,1)$ | $4248117436423023448931250$ | $8971282775737968750$ | $-18567537412471781250$ |
| $(15,4,0)$ | $65612568706892781733282500$ | $-2357870091461021250000$ | $4017281352339977718750$ |
| $(15,3,3)$ | $13713122216738234731250$ | $0$ | $0$ |
| $(15,3,2)$ | $-1490300058713778363487125$ | $-3687404260168390625$ | $7187704305224687500$ |
| $(15,3,1)$ | $-51208365726926534995170750$ | $1835296429575333750000$ | $-2972768889034372481250$ |
| $(15,3,0)$ | $-360292807423315373604734250$ | $-101405983362683739609375$ | $64378424052070525406250$ |
| $(15,2,4)$ | $-1970905140967401221250$ | $0$ | $0$ |
| $(15,2,3)$ | $258577899870571571147250$ | $742967410300506250$ | $-1343484082285242500$ |
| $(15,2,2)$ | $14694478265457427618256400$ | $-524123278584489009375$ | $800575027197934173750$ |
| $(15,2,1)$ | $272016528667552303885489500$ | $51116853557585069887500$ | $-26411513609193784509375$ |
| $(15,2,0)$ | $-7436087195347434763978998750$ | $666651061641647644537500$ | $-2012769834245639213208750$ |
| $(15,1,5)$ | $149718854284522480000$ | $0$ | $0$ |
| $(15,1,4)$ | $-22184417182961181108000$ | $-73485521309160000$ | $120793564026800000$ |
| $(15,1,3)$ | $-1848698810661570905062575$ | $65312786356091370000$ | $-93042571284055392000$ |
| $(15,1,2)$ | $-58721926433604162380437950$ | $-8451059913296883804375$ | $3319508630510891661375$ |
| $(15,1,1)$ | $1510291619047893616778962035$ | $-264079998495453608623125$ | $690779627304800516452125$ |
| $(15,1,0)$ | $130188188621914840901306763360$ | $3336248501254789670536875$ | $7346894618491719383170125$ |
| $(15,0,6)$ | $-4697715725298560000$ | $0$ | $0$ |
| $(15,0,5)$ | $752444684144309568000$ | $2859313324800000$ | $-4154326943360000$ |
| $(15,0,4)$ | $86412492455576177541600$ | $-3003714473676864000$ | $3929155605527616000$ |
| $(15,0,3)$ | $3872523857947363703235735$ | $456379860200642244000$ | $-116751832530811761600$ |
| $(15,0,2)$ | $-39839368012041440479598910$ | $26014964213668484736000$ | $-59261988536996028125625$ |
| $(15,0,1)$ | $-20850094318829072869673609985$ | $-579860221334992067568375$ | $-1199535424105972644495675$ |
| $(15,0,0)$ | $-314640263014577026286239750860$ | $-11407636487369596042573875$ | $-13749950435098069002459600$ |
| $(14,6,0)$ | $-141089957157004194375000$ | $0$ | $0$ |
| $(14,5,1)$ | $165302917193063045175000$ | $0$ | $0$ |
| $(14,5,0)$ | $-3700457330567450251443750$ | $-42057801741836250000$ | $71894783168200687500$ |
| $(14,4,2)$ | $-80050540940598396817500$ | $0$ | $0$ |
| $(14,4,1)$ | $3141163118398676340513750$ | $44051453110031343750$ | $-72778077771340293750$ |
| $(14,4,0)$ | $81201251287909781018399250$ | $-7067025877855275843750$ | $7621797263335835006250$ |
| $(14,3,3)$ | $20516084106490172400000$ | $0$ | $0$ |
| $(14,3,2)$ | $-1053535378043652746504250$ | $-18143955029559993750$ | $28866602759794153750$ |
| $(14,3,1)$ | $-56226581654981487520632300$ | $5473172507924766853125$ | $-5617346652989253037500$ |
| $(14,3,0)$ | $-1555796540890536002636536800$ | $-132080782648335892762500$ | $-37731266570382052612500$ |
| $(14,2,4)$ | $-2935712222317278578750$ | $0$ | $0$ |
| $(14,2,3)$ | $174167480964587321163000$ | $3673915662772555000$ | $-5602409351643997500$ |
| $(14,2,2)$ | $14506245624722058648043425$ | $-1560154248538578131250$ | $1522108968893539314000$ |
| $(14,2,1)$ | $849553356708410146508545380$ | $63390871020215153896875$ | $30935090484968530005000$ |
| $(14,2,0)$ | $9109125941712284446569655740$ | $2026220492699540524575000$ | $-1819233249182178910701750$ |
| $(14,1,5)$ | $222432105153242640000$ | $0$ | $0$ |
| $(14,1,4)$ | $-14146381685418834024000$ | $-366016313663840000$ | $531603722010240000$ |
| $(14,1,3)$ | $-1661565649688537663524050$ | $194351642086539972000$ | $-179771667572622648000$ |
| $(14,1,2)$ | $-149313146567983434359049915$ | $-9844815850620269686875$ | $-7317451886900444330400$ |
| $(14,1,1)$ | $-4421415260448234746685828225$ | $-741113435419279306174125$ | $608347659864998551193100$ |
| $(14,1,0)$ | $67852629420341693150615261670$ | $-5486904746057559942135000$ | $11788508200479897370117950$ |
| $(14,0,6)$ | $-6972972799475200000$ | $0$ | $0$ |
| $(14,0,5)$ | $449345509191609216000$ | $14368036863360000$ | $-19708341355520000$ |
| $(14,0,4)$ | $71693767408842773272800$ | $-8937286061767872000$ | $7803021699169536000$ |
| $(14,0,3)$ | $8467554876811138124410770$ | $489067464570476839200$ | $534330402523376738400$ |
| $(14,0,2)$ | $480882200019449503333775598$ | $67323564912407219374725$ | $-51163482701386663429770$ |
| $(14,0,1)$ | $-7938633548121081855030950724$ | $1061163181336815723286350$ | $-1876015069681077105436170$ |
| $(14,0,0)$ | $-354896998268128579053354662892$ | $-3028164846272871277713525$ | $-36344330735194314771730380$ |
| $(13,6,0)$ | $-168165220460363739562500$ | $0$ | $0$ |
| $(13,5,1)$ | $194620191052840593150000$ | $0$ | $0$ |
| $(13,5,0)$ | $-1361566806174343912387500$ | $-127473582333671437500$ | $157784024002478062500$ |
| $(13,4,2)$ | $-93287818589991700338750$ | $0$ | $0$ |
| $(13,4,1)$ | $1019771455032722533665000$ | $132719499740093193750$ | $-159006586439304412500$ |
| $(13,4,0)$ | $40738431744663632392380750$ | $-12594834645853995393750$ | $7492987094996116631250$ |
| $(13,3,3)$ | $23712751995138062021250$ | $0$ | $0$ |
| $(13,3,2)$ | $-296791154532370302104250$ | $-54492394871755055000$ | $63181737159118251250$ |
| $(13,3,1)$ | $-21236678166332240597739150$ | $9642802200338082600000$ | $-5290496189526442458750$ |
| $(13,3,0)$ | $-1638705561475209314821255260$ | $-25762520323497844451250$ | $-171977425023116091381750$ |
| $(13,2,4)$ | $-3371811253553203505000$ | $0$ | $0$ |
| $(13,2,3)$ | $41187168811474933329750$ | $11029249957896163750$ | $-12372253940259995000$ |
| $(13,2,2)$ | $3700322922852433276553250$ | $-2728649214267251843250$ | $1378482904387233945000$ |
| $(13,2,1)$ | $793467566604710168294767680$ | $2729525336649270995625$ | $101144315238619669224300$ |
| $(13,2,0)$ | $20430292441987045964929232790$ | $1820415382629038489364750$ | $87214631263205734409400$ |
| $(13,1,5)$ | $254324389731015920000$ | $0$ | $0$ |
| $(13,1,4)$ | $-2609343220122186588000$ | $-1100775464060800000$ | $1193691442204960000$ |
| $(13,1,3)$ | $-231834100250676684629700$ | $338337234198648660000$ | $-156813598892846088000$ |
| $(13,1,2)$ | $-121680972157367491189283520$ | $1649370976383940153650$ | $-19634704492256192144700$ |
| $(13,1,1)$ | $-7923518143513690562867574198$ | $-638672288703399705000375$ | $-57495864078877738379130$ |
| $(13,1,0)$ | $-31012335427229341078041454428$ | $-12330157984255525524618375$ | $3517728569898017882195970$ |
| $(13,0,6)$ | $-7949833052727040000$ | $0$ | $0$ |
| $(13,0,5)$ | $52994235002866176000$ | $43359491874560000$ | $-45379893350400000$ |
| $(13,0,4)$ | $2796621538722575299200$ | $-15512822956325760000$ | $6555927419076864000$ |
| $(13,0,3)$ | $5835388466781215075796570$ | $-231839063428238474400$ | $1259601285834693518400$ |
| $(13,0,2)$ | $736335052567963853945332158$ | $55001180279621384440740$ | $6605215993490911079940$ |
| $(13,0,1)$ | $10019145694496110152769316340$ | $2346526940504447073078810$ | $-432134977727227889305440$ |
| $(13,0,0)$ | $-197960805771062542870146703452$ | $17953112299233887446834080$ | $-20382035602222096295650830$ |
| $(12,6,0)$ | $-159261423346752901875000$ | $0$ | $0$ |
| $(12,5,1)$ | $182038162927235683200000$ | $0$ | $0$ |
| $(12,5,0)$ | $661135685410966235400000$ | $-255499209876972375000$ | $222159177093821625000$ |
| $(12,4,2)$ | $-86402744054447825527500$ | $0$ | $0$ |
| $(12,4,1)$ | $-658297528969041246056250$ | $263158308923641218750$ | $-219995092460687512500$ |
| $(12,4,0)$ | $-19426203917593996979268000$ | $-13291330896685968918750$ | $2451643684107438262500$ |
| $(12,3,3)$ | $21804408159212357792500$ | $0$ | $0$ |
| $(12,3,2)$ | $245364653784071175143250$ | $-107219409855269638750$ | $86270375702043807500$ |
| $(12,3,1)$ | $22073451651926622394269300$ | $9924489737977408698750$ | $-1250712828924411716250$ |
| $(12,3,0)$ | $-557736639733896325662893580$ | $137012039523144246957750$ | $-184082956200276834665250$ |
| $(12,2,4)$ | $-3085924281326260190000$ | $0$ | $0$ |
| $(12,2,3)$ | $-43602532767331832833500$ | $21601502638526277500$ | $-16751727926037130000$ |
| $(12,2,2)$ | $-7799746348301643583063650$ | $-2751198415739168730750$ | $187032441272716953000$ |
| $(12,2,1)$ | $156080015731487510746647570$ | $-81951890535419915986650$ | $100866699894704619635100$ |
| $(12,2,0)$ | $16431702778809205296286152672$ | $-466339824133468517719800$ | $1516364902954390731172560$ |
| $(12,1,5)$ | $232219616230907360000$ | $0$ | $0$ |
| $(12,1,4)$ | $3755065946634404160000$ | $-2152043291551440000$ | $1610756727443200000$ |
| $(12,1,3)$ | $1102954593224253582886050$ | $335128687287402084000$ | $-2863963779024048000$ |
| $(12,1,2)$ | $517742035915858202785050$ | $16287707790489290189850$ | $-18505554701740364672100$ |
| $(12,1,1)$ | $-5729415384016674681209122842$ | $212991210770611960149930$ | $-539634691076414333059710$ |
| $(12,1,0)$ | $-77525343889252457765624247600$ | $-4627316547804819293435880$ | $-5993683116537464545294170$ |
| $(12,0,6)$ | $-7257388348337920000$ | $0$ | $0$ |
| $(12,0,5)$ | $-127790594953009536000$ | $84817496476160000$ | $-61349927196160000$ |
| $(12,0,4)$ | $-54376216818607449907200$ | $-15121183049310336000$ | $-820627830498048000$ |
| $(12,0,3)$ | $-1788596783470495858222350$ | $-1069879115950872393600$ | $1137839552222651424000$ |
| $(12,0,2)$ | $471947506970467378665850200$ | $-24705306119202426044820$ | $47521340712734481545940$ |
| $(12,0,1)$ | $16721503790596614899728661142$ | $918257065620982794496350$ | $1095265460604414521725128$ |
| $(12,0,0)$ | $-6950832916505082452147273724$ | $14997929953330493984276370$ | $10777791317185384806009852$ |
| $(11,6,0)$ | $-121364038342962967500000$ | $0$ | $0$ |
| $(11,5,1)$ | $137371043047042549200000$ | $0$ | $0$ |
| $(11,5,0)$ | $1350449138353801230562500$ | $-352521874445577187500$ | $212758474363567875000$ |
| $(11,4,2)$ | $-64812957048136920930000$ | $0$ | $0$ |
| $(11,4,1)$ | $-1104802291665332029320000$ | $357100695943958362500$ | $-204181981592082187500$ |
| $(11,4,0)$ | $-47399711471911023200428500$ | $-7099835624132155031250$ | $-2977377329356655175000$ |
| $(11,3,3)$ | $16321096633543704385000$ | $0$ | $0$ |
| $(11,3,2)$ | $343532373131044134682500$ | $-143553594065107760000$ | $77774305149807525000$ |
| $(11,3,1)$ | $36659330932608435018194550$ | $4952229103997747553750$ | $2785492409850068377500$ |
| $(11,3,0)$ | $518920314990292549626983100$ | $164544413604413797766250$ | $-77073439451969092306500$ |
| $(11,2,4)$ | $-2313648404700735800000$ | $0$ | $0$ |
| $(11,2,3)$ | $-50083208330983970148000$ | $28630601554429475000$ | $-14705139367432940000$ |
| $(11,2,2)$ | $-10181981814714305672725350$ | $-1285010347038085935000$ | $-930579753349320906000$ |
| $(11,2,1)$ | $-391790264037888475223984160$ | $-86969262562300435262850$ | $37289181371342254087950$ |
| $(11,2,0)$ | $4492593654435589890221650008$ | $-1987088442126370629477930$ | $1236192688923482768718420$ |
| $(11,1,5)$ | $175006440006296000000$ | $0$ | $0$ |
| $(11,1,4)$ | $3343976885880110736000$ | $-2832741366051200000$ | $1380403708757120000$ |
| $(11,1,3)$ | $1201159784351163394260000$ | $146420049184830888000$ | $133924720664602752000$ |
| $(11,1,2)$ | $90221215503828568320622170$ | $15246685617987678833250$ | $-6020081711320422061800$ |
| $(11,1,1)$ | $-994539987865039092804520722$ | $760690720796839087530330$ | $-423808858769216584888530$ |
| $(11,1,0)$ | $-58408303853554784202861981612$ | $5673127244740051417802640$ | $-6268676816249643105780156$ |
| $(11,0,6)$ | $-5515052819819520000$ | $0$ | $0$ |
| $(11,0,5)$ | $-77804905813687296000$ | $111217184326400000$ | $-51466237916160000$ |
| $(11,0,4)$ | $-50584868717427691185600$ | $-6158852237121408000$ | $-7077644948726784000$ |
| $(11,0,3)$ | $-6483586135698635654486340$ | $-882273792073512686400$ | $326843971287177571200$ |
| $(11,0,2)$ | $18520779836975511397323420$ | $-73045478473833522060270$ | $36351762501587763773520$ |
| $(11,0,1)$ | $10823279878752920824700129976$ | $-1181108715551072841650472$ | $1030660133006668203666900$ |
| $(11,0,0)$ | $92635268977217753628535973808$ | $5353161301030731990014790$ | $17353050893829788775839640$ |
| $(10,6,0)$ | $-75188015427785603625000$ | $0$ | $0$ |
| $(10,5,1)$ | $84867682732652464050000$ | $0$ | $0$ |
| $(10,5,0)$ | $990886226847968210625000$ | $-344138591461956750000$ | $142512352801636500000$ |
| $(10,4,2)$ | $-40139698185292243637500$ | $0$ | $0$ |
| $(10,4,1)$ | $-728029796633876169345000$ | $340542479698075462500$ | $-130136931989983275000$ |
| $(10,4,0)$ | $-34733153904535058630656500$ | $463467205371195000000$ | $-4651103840910082087500$ |
| $(10,3,3)$ | $10183865696977091190000$ | $0$ | $0$ |
| $(10,3,2)$ | $198416060427176799295500$ | $-134144778964833375000$ | $47091194068191970000$ |
| $(10,3,1)$ | $22267328113895501946528000$ | $-722742492290710747500$ | $3723074939066536755000$ |
| $(10,3,0)$ | $766817914474758410905190760$ | $54326843858440444578750$ | $19826662098487872240000$ |
| $(10,2,4)$ | $-1461246769592074500000$ | $0$ | $0$ |
| $(10,2,3)$ | $-23913082229077800960000$ | $26303896691827270000$ | $-8438466220414560000$ |
| $(10,2,2)$ | $-4976688094353695400962400$ | $292642070309097738000$ | $-1105635628796795700000$ |
| $(10,2,1)$ | $-450249603283787930462259000$ | $-20717281272029156704350$ | $-15458903989683824897100$ |
| $(10,2,0)$ | $-3215365478472950939154407256$ | $-1264311825311617973620020$ | $292269789653450506278300$ |
| $(10,1,5)$ | $112331301266535040000$ | $0$ | $0$ |
| $(10,1,4)$ | $1114876558728169344000$ | $-2567880539941440000$ | $748313202790400000$ |
| $(10,1,3)$ | $438523771359271434978600$ | $-45675700095942048000$ | $144792480869905152000$ |
| $(10,1,2)$ | $85129057859301853797188700$ | $1919617950664236201300$ | $3631122658284563520000$ |
| $(10,1,1)$ | $1735122477454501274136939492$ | $463489244071456523926770$ | $-90071068603572125618040$ |
| $(10,1,0)$ | $-21232936493118104051436507288$ | $6381469881243840652625250$ | $-1812348502967011549665600$ |
| $(10,0,6)$ | $-3609654764129280000$ | $0$ | $0$ |
| $(10,0,5)$ | $-5814119205714432000$ | $99844684689920000$ | $-26238454333440000$ |
| $(10,0,4)$ | $-11227976468045700739200$ | $2469664807768320000$ | $-7075266541016064000$ |
| $(10,0,3)$ | $-5175876892844407298787360$ | $6483679153508952000$ | $-267889714235804620800$ |
| $(10,0,2)$ | $-207261590815545832371862728$ | $-40743578399655829106160$ | $7022476406371749540480$ |
| $(10,0,1)$ | $2495515813467154730675952408$ | $-1469908889437785430278852$ | $250242695283352833434880$ |
| $(10,0,0)$ | $97418478329850808493577225936$ | $3616932522014314340500620$ | $6332337089249649527401488$ |
| $(9,6,0)$ | $-38360771903652297750000$ | $0$ | $0$ |
| $(9,5,1)$ | $43700949355941725775000$ | $0$ | $0$ |
| $(9,5,0)$ | $428488559312270000625000$ | $-242597292594284250000$ | $67239644484138750000$ |
| $(9,4,2)$ | $-20968390427700663240000$ | $0$ | $0$ |
| $(9,4,1)$ | $-290011640833150394452500$ | $232989201480677362500$ | $-56784022518871800000$ |
| $(9,4,0)$ | $-10679206138731165439332000$ | $3660016157241729637500$ | $-3214384326454122225000$ |
| $(9,3,3)$ | $5418077088577187600000$ | $0$ | $0$ |
| $(9,3,2)$ | $74643716402955630873000$ | $-89352777015298700000$ | $18780423024133720000$ |
| $(9,3,1)$ | $3818687515506338881595400$ | $-2819769828459353887500$ | $2369962170936585420000$ |
| $(9,3,0)$ | $437849012894799216314313000$ | $-37097679147513215283000$ | $43227073471820265796500$ |
| $(9,2,4)$ | $-793851828621511520000$ | $0$ | $0$ |
| $(9,2,3)$ | $-9267172401273023952000$ | $17120139974307880000$ | $-3021459501837120000$ |
| $(9,2,2)$ | $127448178655013843846400$ | $794701807648490844000$ | $-650827209138548928000$ |
| $(9,2,1)$ | $-221593365163732696862164740$ | $26186664228666772313700$ | $-25331811387095817000000$ |
| $(9,2,0)$ | $-3982220511282490333820057352$ | $31936617358985061816300$ | $-190909808217727142820480$ |
| $(9,1,5)$ | $62408391035578880000$ | $0$ | $0$ |
| $(9,1,4)$ | $593922761212665216000$ | $-1640308312307200000$ | $233941920271360000$ |
| $(9,1,3)$ | $-161960606074043137195200$ | $-96716150115758016000$ | $78906211823572992000$ |
| $(9,1,2)$ | $34708169065042690393870080$ | $-5984078538609445258800$ | $4940927989171846977600$ |
| $(9,1,1)$ | $1712793051560749586951155248$ | $-38344290262862139509040$ | $72773688729470878509120$ |
| $(9,1,0)$ | $761366404120615249906353600$ | $2155270934480833425574512$ | $676714543927347645919440$ |
| $(9,0,6)$ | $-2052059213168640000$ | $0$ | $0$ |
| $(9,0,5)$ | $-18436078465766400000$ | $62917419489280000$ | $-6834141880320000$ |
| $(9,0,4)$ | $13959174280669070400000$ | $4273794381505536000$ | $-3565077976160256000$ |
| $(9,0,3)$ | $-1640368432448402039225280$ | $438150907474065388800$ | $-321296934845437286400$ |
| $(9,0,2)$ | $-170002729392176382695800704$ | $8053920454920896499840$ | $-6766063624608656561280$ |
| $(9,0,1)$ | $-1568388737928912350323598352$ | $-549705138908234617679760$ | $-140105544220285908111360$ |
| $(9,0,0)$ | $54924814581855200999679104352$ | $-734067625955430871960272$ | $-1085537444929688987353728$ |
| $(8,6,0)$ | $-16371512575057633500000$ | $0$ | $0$ |
| $(8,5,1)$ | $19087991080352614500000$ | $0$ | $0$ |
| $(8,5,0)$ | $117203800928141707650000$ | $-125692342759398375000$ | $22052858887800000000$ |
| $(8,4,2)$ | $-9375662182988487050000$ | $0$ | $0$ |
| $(8,4,1)$ | $-93056544277838504475000$ | $116812841839874025000$ | $-16344146238310800000$ |
| $(8,4,0)$ | $2194227354998540304252000$ | $2813828066489485012500$ | $-1361341322869222800000$ |
| $(8,3,3)$ | $2474774840740240720000$ | $0$ | $0$ |
| $(8,3,2)$ | $36002558399946137676000$ | $-43532932465594440000$ | $4523237271784080000$ |
| $(8,3,1)$ | $-3784538865772526618891700$ | $-1978373679892626810000$ | $911062252085526000000$ |
| $(8,3,0)$ | $106196389723740588522216840$ | $-43792090828321379422500$ | $25987720135371872643000$ |
| $(8,2,4)$ | $-369042750808473600000$ | $0$ | $0$ |
| $(8,2,3)$ | $-8336026503104562336000$ | $8148407824678480000$ | $-551296007554240000$ |
| $(8,2,2)$ | $1596523510880337982521600$ | $509873426988475224000$ | $-224190703068298656000$ |
| $(8,2,1)$ | $-33241418929358401204629000$ | $24104379086580470592600$ | $-14007075401319182208000$ |
| $(8,2,0)$ | $-2011848736188281112793581552$ | $450247066120934955845460$ | $-191077431490788921227520$ |
| $(8,1,5)$ | $29398007638164480000$ | $0$ | $0$ |
| $(8,1,4)$ | $1048781857173359616000$ | $-767911882570240000$ | $24327563622400000$ |
| $(8,1,3)$ | $-252555114748267125403200$ | $-56535195688055808000$ | $23841781077441024000$ |
| $(8,1,2)$ | $398054317784150468232000$ | $-4352191249255238800800$ | $2526007822460735155200$ |
| $(8,1,1)$ | $754538041408247817117842448$ | $-190141257514655128692960$ | $67595300394600344417280$ |
| $(8,1,0)$ | $6350739752602931033033097696$ | $-284556623485490322216480$ | $754189620315237665079840$ |
| $(8,0,6)$ | $-975291911331840000$ | $0$ | $0$ |
| $(8,0,5)$ | $-53174552314902528000$ | $29216307261440000$ | $94405591040000$ |
| $(8,0,4)$ | $13561692545309866214400$ | $2249368156013568000$ | $-910774986522624000$ |
| $(8,0,3)$ | $354314724087449277973440$ | $253288728808841779200$ | $-152890117061675673600$ |
| $(8,0,2)$ | $-62962973078384695363243776$ | $20167918177826427598080$ | $-5949093073645850751360$ |
| $(8,0,1)$ | $-1829469410346056796295375392$ | $121910136634066757093280$ | $-129454904542104208476288$ |
| $(8,0,0)$ | $12618751558614370434617396544$ | $-5440046132609289752182704$ | $-1704137022652097488702464$ |
| $(7,6,0)$ | $-5912198920124415000000$ | $0$ | $0$ |
| $(7,5,1)$ | $7106938081081887600000$ | $0$ | $0$ |
| $(7,5,0)$ | $25754438039413923900000$ | $-48895638327096750000$ | $4817475952929000000$ |
| $(7,4,2)$ | $-3560544277218417280000$ | $0$ | $0$ |
| $(7,4,1)$ | $-44425108932795142440000$ | $44306669753990400000$ | $-2762388116331600000$ |
| $(7,4,0)$ | $3755315006092993875588000$ | $1160531867527157250000$ | $-372123311769009900000$ |
| $(7,3,3)$ | $947231926181004320000$ | $0$ | $0$ |
| $(7,3,2)$ | $27872255372484619008000$ | $-16218489530985120000$ | $445618320541280000$ |
| $(7,3,1)$ | $-3268077107407541643225600$ | $-760932205620551160000$ | $213815370693983040000$ |
| $(7,3,0)$ | $-20591070247717359844590720$ | $-16801509911755281754500$ | $8914579063757018010000$ |
| $(7,2,4)$ | $-140667813596682560000$ | $0$ | $0$ |
| $(7,2,3)$ | $-7912427213189089824000$ | $3007621613971040000$ | $14150272014080000$ |
| $(7,2,2)$ | $977987630617489024488000$ | $184428851016732432000$ | $-42265484688992256000$ |
| $(7,2,1)$ | $25022343242323060563234240$ | $7271708590263376054800$ | $-4388510558083110062400$ |
| $(7,2,0)$ | $-556974197179935827303400192$ | $249916288645267284360960$ | $-79903025923481992149120$ |
| $(7,1,5)$ | $11034718805596160000$ | $0$ | $0$ |
| $(7,1,4)$ | $1034667922337604096000$ | $-283512605214720000$ | $-9220520591360000$ |
| $(7,1,3)$ | $-119706405794179072992000$ | $-19649774352797184000$ | $3083832953508864000$ |
| $(7,1,2)$ | $-7126670860060946044875840$ | $-855103504180432003200$ | $712519980416558035200$ |
| $(7,1,1)$ | $141312938972954358496792896$ | $-99960324934715428613760$ | $27300567407822513426880$ |
| $(7,1,0)$ | $4784745638778533530015923072$ | $-602562071429869020368400$ | $296327154570822378783936$ |
| $(7,0,6)$ | $-356931143598080000$ | $0$ | $0$ |
| $(7,0,5)$ | $-50724937046913024000$ | $10897628037120000$ | $590967767040000$ |
| $(7,0,4)$ | $5027060076740922470400$ | $782503330234368000$ | $-41044392861696000$ |
| $(7,0,3)$ | $574354685507637581193600$ | $16696118405991398400$ | $-38158510379484672000$ |
| $(7,0,2)$ | $-4750190383108706799408000$ | $9205396833086501849280$ | $-2337144056138395180800$ |
| $(7,0,1)$ | $-930428749874280527632846080$ | $225140302701670950937152$ | $-47259715043747731107456$ |
| $(7,0,0)$ | $-6507801548316299188897560576$ | $-4031184677935913295365376$ | $-639507809966421592369152$ |
| $(6,6,0)$ | $-1798695710866314000000$ | $0$ | $0$ |
| $(6,5,1)$ | $2211580239602966400000$ | $0$ | $0$ |
| $(6,5,0)$ | $10109637694160346600000$ | $-14764102542454500000$ | $627014215764000000$ |
| $(6,4,2)$ | $-1106411705558230640000$ | $0$ | $0$ |
| $(6,4,1)$ | $-26774650675671486480000$ | $13390797209799600000$ | $-152157753472800000$ |
| $(6,4,0)$ | $1841229335885075113608000$ | $294587853051204900000$ | $-63843370162315200000$ |
| $(6,3,3)$ | $287459868161111360000$ | $0$ | $0$ |
| $(6,3,2)$ | $17306616858466673040000$ | $-4945774806049760000$ | $-66350415194240000$ |
| $(6,3,1)$ | $-1263456024627886354180800$ | $-196937259581608320000$ | $26804114495544000000$ |
| $(6,3,0)$ | $-26892044281196895627757440$ | $-1155297502253165751000$ | $1902249240337271484000$ |
| $(6,2,4)$ | $-40799846151063360000$ | $0$ | $0$ |
| $(6,2,3)$ | $-4673934651418502208000$ | $929967040909120000$ | $28107666163840000$ |
| $(6,2,2)$ | $287331654433847651942400$ | $52706807482627584000$ | $-2221156438342656000$ |
| $(6,2,1)$ | $19167825488672257780982400$ | $-470586132719239500000$ | $-811513881070562620800$ |
| $(6,2,0)$ | $-58903194066652911449882880$ | $48027102914934532267200$ | $-19954681788768690407040$ |
| $(6,1,5)$ | $2990601897656320000$ | $0$ | $0$ |
| $(6,1,4)$ | $570342044257763328000$ | $-88842783201280000$ | $-3390074961920000$ |
| $(6,1,3)$ | $-23578566117371094585600$ | $-6944656397339136000$ | $-316018362691584000$ |
| $(6,1,2)$ | $-4032337850986128627876480$ | $332270393553357984000$ | $105962997851994585600$ |
| $(6,1,1)$ | $-28337495650543087745597568$ | $-15342444457289969158080$ | $6568061666997650780160$ |
| $(6,1,0)$ | $2251002748492399799569220352$ | $-353375877958740759031200$ | $67462003068619775490432$ |
| $(6,0,6)$ | $-88092209479680000$ | $0$ | $0$ |
| $(6,0,5)$ | $-25989769666142208000$ | $3439371386880000$ | $127161794560000$ |
| $(6,0,4)$ | $386406486240543129600$ | $379151102840832000$ | $39687467237376000$ |
| $(6,0,3)$ | $258412183421326901591040$ | $-35797678132588185600$ | $-3836478153682944000$ |
| $(6,0,2)$ | $6766837858952353494224640$ | $636693915212872439040$ | $-547038865362144407040$ |
| $(6,0,1)$ | $-286023686788343247991462656$ | $108401811523519913980416$ | $-10003265458072413972480$ |
| $(6,0,0)$ | $-7462410384940721081721921024$ | $-574436717738875840114944$ | $-123472955842284704209920$ |
| $(5,6,0)$ | $-448300282882788000000$ | $0$ | $0$ |
| $(5,5,1)$ | $550207834743098400000$ | $0$ | $0$ |
| $(5,5,0)$ | $5224488744812202000000$ | $-3617976333231000000$ | $30656601540000000$ |
| $(5,4,2)$ | $-264882243602550720000$ | $0$ | $0$ |
| $(5,4,1)$ | $-11928594046341880560000$ | $3403386035658000000$ | $33469202284800000$ |
| $(5,4,0)$ | $522497487814858812240000$ | $51847413742495800000$ | $-6059556275886000000$ |
| $(5,3,3)$ | $63861637215735360000$ | $0$ | $0$ |
| $(5,3,2)$ | $6973363043574260640000$ | $-1287750349257600000$ | $-23788033453760000$ |
| $(5,3,1)$ | $-271288675279530027763200$ | $-48961915661925360000$ | $559044009845760000$ |
| $(5,3,0)$ | $-10857187875821253729765120$ | $1424941397919180702000$ | $247093818157996056000$ |
| $(5,2,4)$ | $-8040558702168320000$ | $0$ | $0$ |
| $(5,2,3)$ | $-1711055321481928128000$ | $242168841311680000$ | $4450577721600000$ |
| $(5,2,2)$ | $31311673855272875865600$ | $18648807437742336000$ | $699331787574528000$ |
| $(5,2,1)$ | $6751504511230147287765120$ | $-976276023094798286400$ | $-77774567370162969600$ |
| $(5,2,0)$ | $16686877547938928211304704$ | $-9503344345495283544960$ | $-3155187414977455104000$ |
| $(5,1,5)$ | $486926154362880000$ | $0$ | $0$ |
| $(5,1,4)$ | $189397845635343360000$ | $-22270453350400000$ | $-229590917120000$ |
| $(5,1,3)$ | $2370631126447767168000$ | $-3244793124710400000$ | $-160862806702080000$ |
| $(5,1,2)$ | $-1187536814128333547527680$ | $205599320337594067200$ | $3775100192656128000$ |
| $(5,1,1)$ | $-27543128990038036025992704$ | $6858272106845375063040$ | $982808224914266657280$ |
| $(5,1,0)$ | $742140017733351621729705984$ | $-146088347004871023131712$ | $9957398325965429218560$ |
| $(5,0,6)$ | $-10227899105280000$ | $0$ | $0$ |
| $(5,0,5)$ | $-7788906231939072000$ | $785052958720000$ | $-5099356160000$ |
| $(5,0,4)$ | $-408837985491236659200$ | $209039714107392000$ | $9302639149056000$ |
| $(5,0,3)$ | $60240863985094636346880$ | $-12736350386437017600$ | $429984439260364800$ |
| $(5,0,2)$ | $3745678695378628936628736$ | $-1037414804489206387200$ | $-79200989912094428160$ |
| $(5,0,1)$ | $-48746971724124115557536256$ | $22079263443748886064384$ | $-1340369894179668142080$ |
| $(5,0,0)$ | $-3501722075935719318780340224$ | $691849919695889209464576$ | $-13561313181772209117696$ |
| $(4,6,0)$ | $-87141896443368000000$ | $0$ | $0$ |
| $(4,5,1)$ | $102928729130428800000$ | $0$ | $0$ |
| $(4,5,0)$ | $1839490166924863200000$ | $-736965496062000000$ | $-3002864832000000$ |
| $(4,4,2)$ | $-45136918060912320000$ | $0$ | $0$ |
| $(4,4,1)$ | $-3458425821491470560000$ | $720738077772000000$ | $6684565603200000$ |
| $(4,4,0)$ | $92241148202638332768000$ | $9417224011068000000$ | $-170579045030400000$ |
| $(4,3,3)$ | $9181529354099840000$ | $0$ | $0$ |
| $(4,3,2)$ | $1794151102897194048000$ | $-266692468971200000$ | $-2005879667840000$ |
| $(4,3,1)$ | $-26043337914702562224000$ | $-14965271879699520000$ | $-283808919894720000$ |
| $(4,3,0)$ | $-2587661852822646953990400$ | $606481111326150756000$ | $17380769064764112000$ |
| $(4,2,4)$ | $-828448842851840000$ | $0$ | $0$ |
| $(4,2,3)$ | $-388417324274042496000$ | $45198332563840000$ | $-1004526080000$ |
| $(4,2,2)$ | $-6883499885698368345600$ | $6734967193580352000$ | $135720027335424000$ |
| $(4,2,1)$ | $1453660362164695738325760$ | $-280686940605829641600$ | $-1225987873465881600$ |
| $(4,2,0)$ | $8668353214522923582841344$ | $-7845627350412153360000$ | $-310474385845054986240$ |
| $(4,1,5)$ | $16971800698880000$ | $0$ | $0$ |
| $(4,1,4)$ | $36984567182204928000$ | $-3251863900160000$ | $53110702080000$ |
| $(4,1,3)$ | $2546057633451992640000$ | $-1174137124758528000$ | $-16111687323648000$ |
| $(4,1,2)$ | $-202071962755653392448000$ | $28975538000095257600$ | $-1214024543308569600$ |
| $(4,1,1)$ | $-9128460400815891671986176$ | $4380834197024727022080$ | $87441041054555573760$ |
| $(4,1,0)$ | $171884737668074845218462720$ | $-43024599439184665390464$ | $1021017294555611074560$ |
| $(4,0,6)$ | $1135774597120000$ | $0$ | $0$ |
| $(4,0,5)$ | $-1249138246090752000$ | $59150499840000$ | $-4213309440000$ |
| $(4,0,4)$ | $-183689131386245529600$ | $70133403107328000$ | $290340667392000$ |
| $(4,0,3)$ | $5926396602929385300480$ | $351114625684684800$ | $165829099371724800$ |
| $(4,0,2)$ | $1035074699081405888495616$ | $-479127269205374561280$ | $-6726197383343631360$ |
| $(4,0,1)$ | $-774392791960389331699200$ | $-2052021529241066234880$ | $-119078267344436920320$ |
| $(4,0,0)$ | $-998404618906080088758199296$ | $450887183449692955743744$ | $-1021604707768079084544$ |
| $(3,6,0)$ | $-12373802679888000000$ | $0$ | $0$ |
| $(3,5,1)$ | $13404514665619200000$ | $0$ | $0$ |
| $(3,5,0)$ | $398341147487083200000$ | $-119038143348000000$ | $-473090544000000$ |
| $(3,4,2)$ | $-4860247533068800000$ | $0$ | $0$ |
| $(3,4,1)$ | $-635905751251566720000$ | $113907849052800000$ | $375657091200000$ |
| $(3,4,0)$ | $9617799380646959424000$ | $2201097155364000000$ | $17254571659200000$ |
| $(3,3,3)$ | $619518306986240000$ | $0$ | $0$ |
| $(3,3,2)$ | $286593528011434368000$ | $-36084413578240000$ | $23493950720000$ |
| $(3,3,1)$ | $1660925937142068595200$ | $-3838081096430400000$ | $-30580447758720000$ |
| $(3,3,0)$ | $-394560827203112753955840$ | $114849048343852872000$ | $433481964980832000$ |
| $(3,2,4)$ | $17754160496640000$ | $0$ | $0$ |
| $(3,2,3)$ | $-50883792881204736000$ | $3923192779520000$ | $-42516413440000$ |
| $(3,2,2)$ | $-3128458389696000806400$ | $1595509079780352000$ | $6602666159616000$ |
| $(3,2,1)$ | $197331736258707124423680$ | $-28947050557842297600$ | $405896251447641600$ |
| $(3,2,0)$ | $1875974413108044074379264$ | $-2085165338878792465920$ | $-17452854830632872960$ |
| $(3,1,5)$ | $-9737031270400000$ | $0$ | $0$ |
| $(3,1,4)$ | $3423042959020032000$ | $52854292480000$ | $6009159680000$ |
| $(3,1,3)$ | $646466947747614720000$ | $-233442505451520000$ | $328571437056000$ |
| $(3,1,2)$ | $-16821695702799497848320$ | $-5701111133958720000$ | $-175266969028761600$ |
| $(3,1,1)$ | $-1781109069650059358052864$ | $1127622180922871569920$ | $3926494776767362560$ |
| $(3,1,0)$ | $27091584684282294614430720$ | $-8153524875210816418560$ | $72976719400254074880$ |
| $(3,0,6)$ | $553455452160000$ | $0$ | $0$ |
| $(3,0,5)$ | $-44575010390016000$ | $-23403888640000$ | $-124518400000$ |
| $(3,0,4)$ | $-36314837339336294400$ | $10560129957888000$ | $-120998461440000$ |
| $(3,0,3)$ | $-532123502987202831360$ | $1152864517474713600$ | $17185869036748800$ |
| $(3,0,2)$ | $172357557927835403197440$ | $-97126791128510123520$ | $-275154837652131840$ |
| $(3,0,1)$ | $1700219992237446547113984$ | $-2360145078793882967040$ | $-6885382761987922944$ |
| $(3,0,0)$ | $-183258896959949481442160640$ | $128410087174708851030528$ | $-82485668759442020352$ |
| $(2,6,0)$ | $-1176939160128000000$ | $0$ | $0$ |
| $(2,5,1)$ | $1089379996761600000$ | $0$ | $0$ |
| $(2,5,0)$ | $51540092126352000000$ | $-13462199352000000$ | $-17713728000000$ |
| $(2,4,2)$ | $-252225197605760000$ | $0$ | $0$ |
| $(2,4,1)$ | $-70550400364815360000$ | $11210798160000000$ | $3466195200000$ |
| $(2,4,0)$ | $465244835229974016000$ | $395293138545600000$ | $1120468464000000$ |
| $(2,3,3)$ | $-21365104519680000$ | $0$ | $0$ |
| $(2,3,2)$ | $25976172698482560000$ | $-2099184469760000$ | $4833569280000$ |
| $(2,3,1)$ | $745418003916833510400$ | $-591491423867520000$ | $-820597190400000$ |
| $(2,3,0)$ | $-37817728322308561059840$ | $11037518607116016000$ | $-7493239454400000$ |
| $(2,2,4)$ | $14283335296000000$ | $0$ | $0$ |
| $(2,2,3)$ | $-2868601805663232000$ | $-242997660160000$ | $-689008640000$ |
| $(2,2,2)$ | $-503807734373882572800$ | $199473256131072000$ | $-93730728960000$ |
| $(2,2,1)$ | $15978019735903050915840$ | $1366392013270963200$ | $24768717425280000$ |
| $(2,2,0)$ | $235812219494744549984256$ | $-298573072423357317120$ | $-430619673577190400$ |
| $(2,1,5)$ | $-1610967121920000$ | $0$ | $0$ |
| $(2,1,4)$ | $-67404936314880000$ | $91401338880000$ | $-284426240000$ |
| $(2,1,3)$ | $81454436288904038400$ | $-17717475016704000$ | $91614314496000$ |
| $(2,1,2)$ | $152490440180970593280$ | $-2483206245929088000$ | $-7142333432832000$ |
| $(2,1,1)$ | $-214389680925771410770944$ | $158613839184307161600$ | $47725041848186880$ |
| $(2,1,0)$ | $2733127063940652517656576$ | $-877642447259662479360$ | $2752961861526202368$ |
| $(2,0,6)$ | $50521702400000$ | $0$ | $0$ |
| $(2,0,5)$ | $18419342376960000$ | $-5634129920000$ | $47185920000$ |
| $(2,0,4)$ | $-3524647318253568000$ | $-128254869504000$ | $-10369105920000$ |
| $(2,0,3)$ | $-222169402421615001600$ | $284046477893222400$ | $608061269606400$ |
| $(2,0,2)$ | $16972917669086665881600$ | $-9054574036284026880$ | $-1948330791567360$ |
| $(2,0,1)$ | $395538483003412106483712$ | $-583984501168513711104$ | $-185954844061163520$ |
| $(2,0,0)$ | $-21187636885917725008637952$ | $19931981444100116739072$ | $-4679648905304346624$ |
| $(1,6,0)$ | $-65456004096000000$ | $0$ | $0$ |
| $(1,5,1)$ | $45525016569600000$ | $0$ | $0$ |
| $(1,5,0)$ | $3640914685555200000$ | $-887004432000000$ | $0$ |
| $(1,4,2)$ | $803334328320000$ | $0$ | $0$ |
| $(1,4,1)$ | $-4182730577170560000$ | $519963753600000$ | $0$ |
| $(1,4,0)$ | $-3380839186288896000$ | $37661281516800000$ | $0$ |
| $(1,3,3)$ | $-5476255508480000$ | $0$ | $0$ |
| $(1,3,2)$ | $1037523906480384000$ | $61297628160000$ | $0$ |
| $(1,3,1)$ | $77264774896674355200$ | $-45275608391040000$ | $0$ |
| $(1,3,0)$ | $-2073658845283945297920$ | $448930662231456000$ | $0$ |
| $(1,2,4)$ | $1013794693120000$ | $0$ | $0$ |
| $(1,2,3)$ | $67271854190592000$ | $-63574507520000$ | $0$ |
| $(1,2,2)$ | $-38776175120251699200$ | $9521098500096000$ | $0$ |
| $(1,2,1)$ | $651262093503186263040$ | $522074864764108800$ | $0$ |
| $(1,2,0)$ | $16802320723423064414208$ | $-23029716482423239680$ | $0$ |
| $(1,1,5)$ | $-22303211520000$ | $0$ | $0$ |
| $(1,1,4)$ | $-40472706023424000$ | $7224033280000$ | $0$ |
| $(1,1,3)$ | $4901181389110886400$ | $877940244480000$ | $0$ |
| $(1,1,2)$ | $144470385466113761280$ | $-315532835020800000$ | $0$ |
| $(1,1,1)$ | $-14729536185608271015936$ | $11756995633133936640$ | $0$ |
| $(1,1,0)$ | $156844537712381700440064$ | $-42640695417424112640$ | $0$ |
| $(1,0,6)$ | $-4141875200000$ | $0$ | $0$ |
| $(1,0,5)$ | $2824517713920000$ | $10485760000$ | $0$ |
| $(1,0,4)$ | $-116232705736704000$ | $-217486196736000$ | $0$ |
| $(1,0,3)$ | $-24173012794027622400$ | $28469320394342400$ | $0$ |
| $(1,0,2)$ | $852145487138156544000$ | $-150943108480819200$ | $0$ |
| $(1,0,1)$ | $39929557545089487433728$ | $-66163059090783903744$ | $0$ |
| $(1,0,0)$ | $-1405046549802303824338944$ | $1636205412682778370048$ | $0$ |
| $(0,6,0)$ | $-1579585536000000$ | $0$ | $0$ |
| $(0,5,1)$ | $614053094400000$ | $0$ | $0$ |
| $(0,5,0)$ | $107038132992000000$ | $-24681024000000$ | $0$ |
| $(0,4,2)$ | $378167938560000$ | $0$ | $0$ |
| $(0,4,1)$ | $-96288510585600000$ | $5738169600000$ | $0$ |
| $(0,4,0)$ | $-902072360655360000$ | $1390181616000000$ | $0$ |
| $(0,3,3)$ | $-144456499200000$ | $0$ | $0$ |
| $(0,3,2)$ | $3317407902720000$ | $6805463040000$ | $0$ |
| $(0,3,1)$ | $2830189703186304000$ | $-1221661785600000$ | $0$ |
| $(0,3,0)$ | $-49396607660865484800$ | $1805321597760000$ | $0$ |
| $(0,2,4)$ | $-15325184000000$ | $0$ | $0$ |
| $(0,2,3)$ | $10930228690944000$ | $-1193779200000$ | $0$ |
| $(0,2,2)$ | $-1158821295928934400$ | $-61212672000000$ | $0$ |
| $(0,2,1)$ | $7548490451630684160$ | $30531038939136000$ | $0$ |
| $(0,2,0)$ | $527077246124070752256$ | $-751173628926643200$ | $0$ |
| $(0,1,5)$ | $8957460480000$ | $0$ | $0$ |
| $(0,1,4)$ | $-2246981713920000$ | $-425984000000$ | $0$ |
| $(0,1,3)$ | $94945244457369600$ | $147566493696000$ | $0$ |
| $(0,1,2)$ | $8171187974580879360$ | $-14036227850649600$ | $0$ |
| $(0,1,1)$ | $-440057903093507911680$ | $349773041653309440$ | $0$ |
| $(0,1,0)$ | $3822034941486799478784$ | $-355966410159876096$ | $0$ |
| $(0,0,6)$ | $-734003200000$ | $0$ | $0$ |
| $(0,0,5)$ | $115511132160000$ | $73400320000$ | $0$ |
| $(0,0,4)$ | $2606874034176000$ | $-16924016640000$ | $0$ |
| $(0,0,3)$ | $-933881188102963200$ | $978150614630400$ | $0$ |
| $(0,0,2)$ | $13361507759373189120$ | $21787493819351040$ | $0$ |
| $(0,0,1)$ | $1589009275366836019200$ | $-2930995323513815040$ | $0$ |
| $(0,0,0)$ | $-40734284865794246393856$ | $55647930144527659008$ | $0$ |

For the singular normalization write $T_s(p,v)=\sum t_{ij}p^iv^j$.
Its full coefficient list is

| $(i,j)$ | $t_{ij}$ |
| --- | --- |
| $(4,0)$ | $-29469173147451300042088704$ |
| $(3,1)$ | $31420706350241322564450048$ |
| $(3,0)$ | $-570313915199421348668237568$ |
| $(2,2)$ | $-11612825009762148107450784$ |
| $(2,1)$ | $218046390007554044346203136$ |
| $(2,0)$ | $11189757888806026407872905296$ |
| $(1,3)$ | $1794323529173675035284240$ |
| $(1,2)$ | $-8311053024794010948005808$ |
| $(1,1)$ | $-5775813925940023591231252872$ |
| $(1,0)$ | $45639853754159198200873260960$ |
| $(0,4)$ | $-99133686444483896037925$ |
| $(0,3)$ | $-2039095207067762374304760$ |
| $(0,2)$ | $576172660941418884580861101$ |
| $(0,1)$ | $6637180808032838988054990840$ |
| $(0,0)$ | $-669434267517247721659071783600$ |

The generic algebraic mechanisms used in Sections 21--23 are the
fixed-size resultant criterion, the ordered-minor relation of [O],
Theorem 20.2, and the existing singular coverage of [S], Lemma 9.2.
They are used with the explicitly specified original-source inputs,
rather than as new elimination or singular-locus results.
The new specialized content is the $K_3$ nonzero and root-budget
calculation, the two-world exact inventory, and its open local
whole-child consequences. The four actual critical worlds and their
rank and germ properties are those of Sections 13--16;
whole-world compactness and the actual remote sheet are Theorems 17.2
and 18.1. The separate global finite-fibre bound is [F], Theorem 32.1,
and is not needed to turn the local calculation into a continuum
inventory.

For the classical algebra see Basu--Pollack--Roy, *Algorithms in Real
Algebraic Geometry*, 2nd ed., Chapters 2 and 8--9, and Cox--Little--O'Shea,
*Ideals, Varieties, and Algorithms*, Chapter 3. The topological transport
in (23.4) uses Heine--Borel sequential compactness as in Theorem 17.2;
the local coordinate choices use the inverse-function theorem as in
Theorem 16.1. Neither generic algebra nor compactness asserts the
existence of an original world at an extraneous root, closedness of a
distinct-pair locus, or a global independent-pair exclusion.
