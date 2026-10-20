# FIB strict-real joint incidence: an unused-companion fold

## 1. Original worlds, acquired children and supplier assumptions

**Definition 1.1 (Worlds and observations).** Use the complete-world domain of
[O, Definitions 1.1–1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md):

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

The drift $d$ is one fixed real number. There is no upper bound on either
positive off-diagonal entry. Lower degrees, sampled zeros, repeated roots and
zero drift remain in this domain. Put

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
$$

The literal parent and acquired child are

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\qquad p\ne24.
$$

The initial reading counts, every action is immediately read, and the original
clocks are $0,\ldots,7$. The acquired word through clock six is
$J,M,J,M,M,M$. Each world uses its one entire polynomial, source and drift at
every clock. There is no reset, copy, skipped reading, clock change or extra
observation. The two terminal actions at clock seven are alternatives.

Write

$$
j=b+\frac{r(1-r)}b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad x=\frac nU,
$$

and abbreviate the terminal responses by

$$
a(W)=f_{MJ}(W),\qquad m(W)=f_{MM}(W).
$$

These are the functions of O, (1.7), on the same complete world.

**Definition 1.2 (Strict same-child pairs).** The sets $D_J,D_M$ are those of
[S, Definition 1.2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md):

$$
\begin{aligned}
(p,v)\in D_J&\iff\exists W_0\ne W_1\in C(p,v):\ a(W_0)=a(W_1),\\
(p,v)\in D_M&\iff\exists W_2\ne W_3\in C(p,v):\ m(W_2)=m(W_3).
\end{aligned}
$$

Both within-pair distinctness conditions are retained. All four labels belong
to the same entire actual $C(p,v)$; cross-pair reuse is permitted, and the two
common terminal values need not coincide. In particular, a possible $J$ pair
need not contain either endpoint of a selected $M$ pair.

**Assumption 1.3 (Owning mathematical suppliers).** The following results are
used with their stated hypotheses and scopes.

| Supplier | Use |
| --- | --- |
| O, Theorem 2.1 | Necessary and sufficient full-parent lift, with the entire gain and all original rows. |
| [F, Lemma 30.2](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md) | Zero-safe faithful reconstruction and injectivity of complete worlds into $(x,d)$ for $p\ne24$. |
| F, Definition 31.1 and Lemma 31.2 | The fixed polynomial equations and the uniquely normalized degree-eighteen carrier. |
| S, Theorem 4.1 | Necessity of this carrier for every actual world, including $d=0$, $F_0=0$ and singular $\Lambda=0$ worlds. |

The later singular-$M$ classification is not an additional premise. The
distinct-node interpolation theorem, Banach contraction theorem, Rouché's
theorem, analytic implicit-function theorem and Taylor's theorem are used as
classical tools at the particular maps and domains below.

## 2. The original regular lift and its critical polynomial

**Definition 2.1 (Regular response map).** On the strict source domain put

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n.
$$

Where $\Lambda\ne0$, the regular part of the owning lift O, Theorem 2.1, is

$$
e=-\frac{24}{5}\left(b-\frac18\right)
       \frac{6/T-2/U}{\Lambda},\qquad d=24+e,
$$

with $g$ the unique degree-at-most-three polynomial having samples

$$
(g(0),g(1),g(2),g(3))=
\left(-d,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{2.1}
$$

Thus $(P(r,b),g,d)$ is the complete original world, rather than just a point
in a response projection. Define $\Psi=(p,v,a,m)$ by

$$
\begin{aligned}
p&=d+(U+n)g(5),&v&=d+(2U+n)g(6),\\
a&=d+(T+2j+4r)g(7),&m&=d+(3U+2n)g(7).
\end{aligned}
\tag{2.2}
$$

The interpolation rows taking the four samples in (2.1) to $g(5),g(6),g(7)$
are, respectively,

$$
(-4,15,-20,10),\qquad(-10,36,-45,20),\qquad(-20,70,-84,35).
\tag{2.3}
$$

In particular (2.1)–(2.3) always specify one entire $g$, not independent gain
samples. Its nonzeroness follows from the unequal original readings $0,24$.

**Definition 2.2 (Integer circuit).** In $\mathbb Z[r,b]$ set

$$
\begin{gathered}
J_b=b^2+r-r^2,\qquad N_b=J_b+rb,\\
\ell=(TU+6U+T)J_bN_b-4bTU(J_b+N_b),\\
E=-6(8b-1)(2+5b)J_bN_b,\qquad d_N=120\ell+E,\qquad Q=5bT\ell,\\
q_N=\bigl(-d_NT,\ 6(8b-1)(2+5b)bN_bT,\ 27\ell-E,
                 \ 6(8b-1)(2+5b)bJ_bT\bigr).
\end{gathered}
\tag{2.4}
$$

Let $G_5,G_6,G_7$ be the three rows in (2.3) applied to $q_N$, and put

$$
\begin{aligned}
P_0&=d_NbT+(bU+N_b)G_5,\\
P_1&=d_NbT+(2bU+N_b)G_6,\\
P_2&=d_NbT+(bT+2J_b+4rb)G_7,\\
P_3&=d_NbT+(3bU+2N_b)G_7.
\end{aligned}
\tag{2.5}
$$

Define the integer polynomial $F_v$ by the exact division

$$
\begin{aligned}
A_v={}&Q(P_{0,r}P_{1,b}-P_{0,b}P_{1,r})\\
 &+Q_r(P_{0,b}P_1-P_0P_{1,b})
  +Q_b(P_0P_{1,r}-P_{0,r}P_1),\\
F_v={}&A_v/(-360bT^3).
\end{aligned}
\tag{2.6}
$$

**Proposition 2.3 (Critical equation for the fixed original responses).** The
division in (2.6) has zero remainder. The quotient has $134$ nonzero monomials,
total degree $17$ and coordinate degrees $(15,17)$ in $(r,b)$. On the regular
strict domain,

$$
\Psi_i=P_i/Q\quad(0\le i\le3),\qquad
\det D(p,v)=\frac{-360bT^3}{Q^3}F_v.
\tag{2.7}
$$

Proof. One has $j=J_b/b$, $n=N_b/b$ and
$\Lambda=\ell/(TUJ_bN_b)$. Hence $e=E/(5\ell)$,
$d=d_N/(5\ell)$, and $q_N/(5T\ell)$ is exactly (2.1). Substitution into
(2.2) gives (2.5) divided by $Q$. Expanding (2.6) and dividing by
$-360b(1+b)^3$ gives the stated integer quotient and monomial counts.
The quotient rule for $P_0/Q,P_1/Q$ cancels one common factor $Q$ from the
Jacobian numerator and leaves $A_v/Q^3$. This proves (2.7). All polynomial
coefficients used here are fixed by (2.4)–(2.6). ∎

## 3. Exact rational data and inverse bins

**Definition 3.1 (Rational arithmetic conventions).** Every terminating decimal
in this volume denotes its exact rational value. For a real rational $y$ put

$$
\operatorname{Round}_N(y)=10^{-N}\left\lfloor10^Ny+\frac12\right\rfloor.
\tag{3.1}
$$

Apply this separately to real and imaginary parts and entrywise to matrices.
The interval operations used below are closed rational operations, with each
elementary lower endpoint rounded down and each upper endpoint rounded up to
a multiple of $10^{-160}$. Products take the extrema of the four endpoint
products. Inversion of $[l,u]$ uses $[1/u,1/l]$ only when $0\notin[l,u]$.
Derivatives and Hessians use the product and quotient rules with these same
operations. Powers are formed successively in increasing exponent order;
expanded multivariate polynomials are summed in ascending lexicographic
monomial order, and univariate polynomials use descending Horner evaluation.
For $(r,b)$ the exponent pair order is $(\deg_r,\deg_b)$; for the carrier
coefficients it is $(\deg_p,\deg_v)$ after collecting powers of $x$.

The vector norm is $\|z\|_\infty=\max_i|z_i|$ and the matrix norm is the
maximum absolute row sum. A complex rectangle uses the maximum of its two
real component norms.

**Definition 3.2 (Exact source centres).** In the coordinate order
$z=(r_A,b_A,r_B,b_B,r_C,b_C)$ define $c$ by the following exact rationals.

| Coordinate | Value |
| --- | --- |
| $c_{r_A}$ | $0.011040740984264802064647949585735869727661613881395347359001810436665458024000746729699250543745331581328410994$ |
| $c_{b_A}$ | $0.003962723577463874818263626029535093281419190142635147021781853025586501137354768180757151464683631330705203932$ |
| $c_{r_B}$ | $0.97992797302746303180053622826538821921038985763850405714590446724974146706279617478113389564167543107192131558$ |
| $c_{b_B}$ | $0.010982029913376597728809344595122526404073875499630550851661077718211059956915914214021785943155599264463078441$ |
| $c_{r_C}$ | $0.33034887900698987798772668697766854267251024409082757608881549778187071201500425705195179373367097543968233944$ |
| $c_{b_C}$ | $0.26845625565847527476206129462256453297796607359729631105617248577400292582360417214038409775641200375896791102$ |

Write $c_A,c_B,c_C$ for the corresponding source pairs, and define

$$
\mathcal B_6=\{z:\|z-c\|_\infty\le10^{-90}\},\qquad
\mathcal U_i=\{s\in\mathbb R^2:\|s-c_i\|_\infty\le10^{-10}\}
\quad(i=A,B,C).
\tag{3.2}
$$

**Definition 3.3 (Acquired-base box).** Put

$$
\begin{aligned}
p_c&=6.4132616258396395688631019445778072168786388832392856847475579137520339873564425957661352268013624229857500318,\\
v_c&=90.275754789581458754432169761625440305747653000136796904935974019232371303573092271897653494832726197867160204,\\
Q_{70}&=\{(p,v)\in\mathbb R^2:|p-p_c|\le10^{-70},\ |v-v_c|\le10^{-70}\}.
\end{aligned}
\tag{3.3}
$$

In particular $Q_{70}\subset\{p\ne24\}$.

**Definition 3.4 (Finite inverse-bin specification).** The square matrices to
be inverted are

$$
\begin{gathered}
F_6(z)=(p_A-p_B,v_A-v_B,m_A-m_B,p_A-p_C,v_A-v_C,F_v(r_C,b_C)),\\
A_6=DF_6(c),\qquad C_6=\operatorname{Round}_{100}(A_6^{-1}),\\
A_i^J=D(p,a)(c_i),\quad B_i^J=\operatorname{Round}_{100}((A_i^J)^{-1})
\quad(i=A,B,C),\\
A_C^M=D(p,m)(c_C),\qquad B_C^M=\operatorname{Round}_{100}((A_C^M)^{-1}).
\end{gathered}
\tag{3.4}
$$

All entries of the matrices $A$ in (3.4) are exact rationals obtained by
differentiating (2.1)–(2.6) and substituting Definition 3.2. Here is an entirely
integer specification of every $100$-place inverse bin. Their rational
determinants are nonzero. Set
$h=\operatorname{lcm}$ of the positive denominators of the entries of $A$,
$N=hA$, $\delta=\det N$, $q=|\delta|$, and

$$
u_{ij}=h\operatorname{sgn}(\delta)(\operatorname{adj}N)_{ij},\qquad
n_{ij}=\left\lfloor\frac{2\cdot10^{100}u_{ij}+q}{2q}\right\rfloor.
\tag{3.5}
$$

Then the corresponding entry of the rounded inverse is $10^{-100}n_{ij}$.
Its exact bin is certified by the integer comparisons

$$
(2n_{ij}-1)q\le2\cdot10^{100}u_{ij}<(2n_{ij}+1)q.
\tag{3.6}
$$

Thus (3.4)–(3.6), without a floating inverse, specify all preconditioners.
In particular every entry differs from the exact inverse by at most
$\tfrac12 10^{-100}$.

For quantitative inverse enclosure, a rational matrix $G$ with
$\|I-GA\|_\infty<1$ gives

$$
\|A^{-1}-G\|_\infty\le
\frac{\|I-GA\|_\infty\|G\|_\infty}{1-\|I-GA\|_\infty}.
$$

Alternatively the exact cofactor rule specifies
$G_6=\operatorname{Round}_{145}(A_6^{-1})$ directly, with
$\|A_6^{-1}-G_6\|_\infty\le3\cdot10^{-145}<8.41\cdot10^{-140}$.
The comparisons (3.6) settle each individual $100$-place bin, including
entries whose rounded value is zero.

The following smaller integers give quantitative outer bins for every entry.
If $n$ is an entry in the table, the corresponding $100$-place rounded
inverse entry lies strictly between $(n-1)10^{-12}$ and $(n+1)10^{-12}$.
Rows and columns have the orders in (3.4).

| Matrix and row | Integers specifying the entry bins |
| --- | --- |
| $C_6$, row 1 | $(6207952329622,-4855941259108,824056137530,-3434419503,1255805281,0)$ |
| $C_6$, row 2 | $(2226235197144,-1741390199584,295514958940,-1082017345,395642726,0)$ |
| $C_6$, row 3 | $(-3921500398920,3073239671612,-521288103808,1387734164,-507428953,0)$ |
| $C_6$, row 4 | $(2138431986022,-1676129501274,284346829120,-129581125,47381708,0)$ |
| $C_6$, row 5 | $(2488734375104,-1946720479371,330359630292,-4413399480,-584053876,1666495701250)$ |
| $C_6$, row 6 | $(1535838536451,-1201352929354,203870311017,-2723580735,-360429164,968513872213)$ |
| $B_A^J$, row 1 | $(11730529813,485850461)$ |
| $B_A^J$, row 2 | $(4272480389,164433651)$ |
| $B_B^J$, row 1 | $(-7966919976,-257503762)$ |
| $B_B^J$, row 2 | $(4589335709,99122877)$ |
| $B_C^J$, row 1 | $(-54278175501,12281651932)$ |
| $B_C^J$, row 2 | $(-31328660967,7137702342)$ |
| $B_C^M$, row 1 | $(-279499208031,37272795089)$ |
| $B_C^M$, row 2 | $(-162219904285,21661753506)$ |

For example these bins give $\|C_6\|_\infty<12$ and, in the order
$B_A^J,B_B^J,B_C^J,B_C^M$, the norm upper bounds
$123/10000,83/10000,666/10000,317/1000$.

## 4. An exact actual $M$ pair and a third world

**Proposition 4.1 (Source contraction and strict lifts).** The function $F_6$
has exactly one zero $z^*$ in $\mathcal B_6$, and that zero is interior.
At this zero the three source pairs lift to strict complete worlds
$W_A^*,W_B^*,W_C^*$ satisfying

$$
p_A^*=p_B^*=p_C^*,\qquad
v_A^*=v_B^*=v_C^*,\qquad m_A^*=m_B^*,\qquad F_v(r_C^*,b_C^*)=0.
\tag{4.1}
$$

Their common acquired base $q^*=(p^*,v^*)$ belongs to
$\operatorname{int}Q_{70}$, and the three worlds are distinct.

Proof. The exact interval inequalities for (3.2)–(3.4) are

$$
\begin{aligned}
\sup_{z\in\mathcal B_6}\|I-C_6DF_6(z)\|_\infty
    &<\frac{117}{100}\,10^{-81},\\
\|C_6F_6(c)\|_\infty&<\frac{2704}{1000}\,10^{-111}.
\end{aligned}
\tag{4.2}
$$

These are finite rational bounds: expand $F_v$ by (2.4)–(2.6), differentiate
the original rational lift for the five response differences, use the inverse
bins (3.5)–(3.6), and apply Definition 3.1 on $\mathcal B_6$. The same
substitution gives the following guard and base bounds.

| Source pair in $\mathcal B_6$ | $\Lambda$ | $d$ |
| --- | --- | --- |
| $A$ | $(5,6)$ | $(24.45,24.46)$ |
| $B$ | $(4,5)$ | $(24.51,24.52)$ |
| $C$ | $(-0.092,-0.091)$ | $(49.72,49.73)$ |

All three source pairs are strict and pairwise disjoint; $b,j,n,T,U$ are
positive. Moreover

$$
\sup_{z\in\mathcal B_6}|p_A(z)-p_c|<2.222\cdot10^{-86},\qquad
\sup_{z\in\mathcal B_6}|v_A(z)-v_c|<6.366\cdot10^{-86}.
\tag{4.3}
$$

The map $z\mapsto z-C_6F_6(z)$ has Lipschitz constant bounded by the first
line of (4.2). Its distance from $c$ is at most the second bound plus
$10^{-90}$ times the first, strictly less than $10^{-90}$. It is therefore
a contraction of the complete closed box into its interior. Banach's theorem
gives a unique fixed point. Since $\|I-C_6DF_6\|<1$, the square matrix
$C_6$ is nonsingular; thus its fixed points are exactly zeros of $F_6$.
This establishes exact equalities (4.1). Neither a response interval nor a
small residual has been used as an equality proof.

Apply the owning lift O, Theorem 2.1, through (2.1) at each source. It supplies
the full original history and one nonzero entire gain at each fixed drift.
The disjoint source pairs give distinct complete worlds. Finally (4.3)
places the exact common base strictly inside $Q_{70}$. ∎

## 5. The fixed all-world carrier and unique local drift

**Definition 5.1 (Carrier coefficient specification).** Use the normalization
of F, (31.3)–(31.8). For coefficient reproduction it is convenient to write
$K=4k$ and to put

$$
\begin{gathered}
D=x(x+1)(x+2),\\
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\quad
a_2=4z_3-6z_4+4z_5-z_6,\quad z_*=xa_1-D(24-d),\\
f=5dDa_2+a_0\bigl((294-10d)D-5a_2\bigr),\\
K=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1
 -(a_0+dD)\bigl(dD+(1-2x)a_0\bigr)a_1^2,\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\end{gathered}
\tag{5.1}
$$

The fixed Sylvester determinant, with rows $d^3f,d^2f,df,f,dK,K$ and columns
$d^5,d^4,\ldots,1$, satisfies

$$
\operatorname{Res}_d(f,K)=256D^8F_0^2R.
\tag{5.2}
$$

This specifies the same $R$ as F, Lemma 31.2: replacing both $k$ rows by
$4k$ multiplies its determinant by $16$. The division has zero remainder,
and $R$ has $512$ monomials and coordinate degrees $(18,6,6)$ in $(x,p,v)$.
No change of primitive factor or normalization is made.

**Definition 5.2 (Linear drift remainder).** Write

$$
f=A_fd^2+B_fd+C_f,\qquad K=\sum_{j=0}^4 K_jd^j,
$$

and set

$$
\begin{aligned}
\alpha={}&K_4(-B_f^3+2A_fB_fC_f)
 +K_3A_f(B_f^2-A_fC_f)-K_2A_f^2B_f+K_1A_f^3,\\
\zeta={}&K_4(-B_f^2C_f+A_fC_f^2)
 +K_3A_fB_fC_f-K_2A_f^2C_f+K_0A_f^3.
\end{aligned}
\tag{5.3}
$$

The different letter $\zeta$ keeps this remainder coefficient distinct from
the fold derivative $\beta$ below. Polynomial reduction gives

$$
f\ \mid\ A_f^3K-(\alpha d+\zeta).
\tag{5.4}
$$

Consequently every actual common root satisfies $\alpha d+\zeta=0$.
This implication divides by neither $A_f$ nor $d$; whenever $\alpha\ne0$,
the only possible drift at that $x,p,v$ is $d=-\zeta/\alpha$.

**Assumption 5.3 (All-world necessity and faithful filtering).** By the owning
S, Theorem 4.1, every actual $W\in C(p,v)$ satisfies
$x(W)>0$ and $R(x(W),p,v)=0$. This includes singular sources, zero drift
and $F_0=0$. By the owning F, Lemma 30.2, compute from $(x,d,p,v)$

$$
\begin{gathered}
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\quad
H_2=4h_3-6h_4+4h_5-h_6,\\
B_0=294/5-2d-H_2,\qquad C_0=d^2+B_0^2,\\
U=\frac{-dH_0+B_0H_2}{C_0},\quad b=(U-1)/2,\quad
j=\frac{U(24-d)}{H_1},\quad r=xU-j.
\end{gathered}
\tag{5.5}
$$

For an actual world the remaining faithful guards are

$$
\begin{gathered}
d\ne24,\quad H_1\ne0,\quad C_0>0,\quad U>1,\quad0<r<1,\\
j=b+r(1-r)/b,\qquad dU=-H_0,\qquad B_0U=H_2.
\end{gathered}
\tag{5.6}
$$

The whole polynomial is $g=H/U$, where $H$ interpolates $h_3,h_4,h_5,h_6$
at $3,4,5,6$. These statements are the cited reconstruction interface;
they are not inferred merely from $R=0$ or from $f=K=0$. In particular
the expression $U=-H_0/d$ is not substituted for (5.5).

## 6. A uniform degree-eighteen root cover on $Q_{70}$

**Definition 6.1 (Sixteen exact simple-root centres).** Throughout $Q_{70}$
let $L(p,v)=[x^{18}]R$ and $\overline R(x,p,v)=R(x,p,v)/L(p,v)$.
Set $R_0(x)=\overline R(x,p_c,v_c)$. The following table lists exact
Gaussian-rational seeds $s_i$.

| $i$ | $\operatorname{Re}s_i$ | $\operatorname{Im}s_i$ |
| --- | --- | --- |
| 1 | $-28.205117$ | $0$ |
| 2 | $-1.634149$ | $0$ |
| 3 | $-1.509750$ | $0$ |
| 4 | $-1.506124$ | $0$ |
| 5 | $-1.323109$ | $0$ |
| 6 | $-1.243240$ | $0$ |
| 7 | $-1.196076$ | $0$ |
| 8 | $-0.380415$ | $0$ |
| 9 | $0.342675$ | $0$ |
| 10 | $0.519008$ | $0$ |
| 11 | $0.685489$ | $0.101740$ |
| 12 | $0.685489$ | $-0.101740$ |
| 13 | $1.124463$ | $0$ |
| 14 | $1.243534$ | $0$ |
| 15 | $2.722150$ | $0$ |
| 16 | $2.748608$ | $0$ |

Starting with $c_i^{(0)}=s_i$, define the exact finite recurrence

$$
c_i^{(j+1)}=\operatorname{Round}_{100}
 \left(c_i^{(j)}-\frac{R_0(c_i^{(j)})}{R_0'(c_i^{(j)})}\right)
\quad(0\le j<8),\qquad
\xi_i=c_i^{(8)},\quad
\gamma_i=\operatorname{Round}_{100}(1/R_0'(\xi_i)).
\tag{6.1}
$$

All divisions in this recurrence are nonzero rational divisions. Each real
or imaginary rounding bin is specified exactly as in (3.1); for a component
$u/q$, $q>0$, its bin integer $n$ is equivalently characterized by
$(2n-1)q\le2\cdot10^{100}u<(2n+1)q$. Thus the table and eight steps
fix the centres and multipliers without approximate root choices.

Let $\mathcal R_i$ be the closed rectangle with component radius $10^{-30}$
about $\xi_i$. For the remaining cluster put

$$
\begin{aligned}
\xi_C&=0.92578100246830237565341788390822926849403571160742662339440563548687934029175535,\\
\rho_x&=10^{-25},\qquad
\mathcal D_C=\{x\in\mathbb C:|x-\xi_C|<\rho_x\}.
\end{aligned}
\tag{6.2}
$$

**Proposition 6.2 (Complete uniform root allocation).** For every real
$(p,v)\in Q_{70}$, each $\mathcal R_i$ contains exactly one simple root of
$R(x,p,v)$, and $\mathcal D_C$ contains exactly two roots counted with
multiplicity. These eighteen roots exhaust the polynomial. Eight simple
roots are negative real, two are nonreal conjugates, and the other six
simple roots are positive real.

Proof. Formula (5.2) gives every coefficient. Rational evaluation of those
coefficients over the full closed parameter box gives

$$
L(p,v)>10^{19}.
\tag{6.3}
$$

In particular the monic normalization has no parameter pole. For each of
the sixteen rectangles, the uniform inequalities are

$$
\begin{aligned}
\sup_{\mathcal R_i\times Q_{70}}
 \bigl(|\operatorname{Re}(1-\gamma_i\overline R_x)|
       +|\operatorname{Im}(1-\gamma_i\overline R_x)|\bigr)
 &<8.493\cdot10^{-24},\\
\sup_{q\in Q_{70}}\max\bigl(
 |\operatorname{Re}(\gamma_i\overline R(\xi_i,q))|,
 |\operatorname{Im}(\gamma_i\overline R(\xi_i,q))|\bigr)
 &<7.189\cdot10^{-64}.
\end{aligned}
\tag{6.4}
$$

These bounds use the rational recurrence (6.1) and Definition 3.1;
all $128$ Newton-step bins and the sixteen multiplier bins have the integer
description immediately following (6.1). For fixed $q$, the map
$x\mapsto x-\gamma_i\overline R(x,q)$ has the first line of (6.4) as a
Lipschitz bound in the real-component maximum norm. The second line plus
$10^{-30}$ times the first is strictly less than $10^{-30}$. Hence the map
is a contraction into the rectangle's interior. Its unique fixed point is
a root, and the first inequality also makes its derivative nonzero.

For the cluster write $\overline R=\sum_{j=0}^{18}c_j(q)x^j$ and

$$
\overline R(\xi_C+h,q)=\sum_{k=0}^{18}t_k(q)h^k,\qquad
t_k(q)=\sum_{j=k}^{18}\binom jk c_j(q)\xi_C^{j-k}.
\tag{6.5}
$$

The exact uniform coefficient bounds needed for the circle $|h|=\rho_x$ are

$$
19<t_2(q)<21,\qquad
\frac{\sup|t_0|+\rho_x\sup|t_1|
 +\sum_{k=3}^{18}\rho_x^k\sup|t_k|}
 {\rho_x^2\inf|t_2|}<1.298\cdot10^{-16}<1.
\tag{6.6}
$$

Every supremum and infimum in (6.6) is over $Q_{70}$, with (6.5)
evaluated by the rational rules of Definition 3.1. Rouché's theorem applied
to $t_2h^2$ gives exactly two cluster roots counted with multiplicity and
none on its boundary.

The sixteen rectangles and the cluster disk are pairwise disjoint.
The real-centred rectangles lie strictly on the indicated negative or
positive sides of zero. Their centres are real by (6.1), so conjugation
and uniqueness force their roots to be real. The other two rectangles
are conjugate and disjoint from the real axis. Finally (6.3) gives degree
exactly eighteen throughout the box. The sixteen simple roots and the
two cluster roots already account for that degree, leaving no other roots.
This is an allocation of polynomial roots; it does not assert that they
are legal worlds. ∎

## 7. Every actual companion lies in one of three source patches

**Proposition 7.1 (Guarded whole-child cover).** For every real
$q\in Q_{70}$, every complete world in $C(q)$ has source in
$\mathcal U_A\cup\mathcal U_B\cup\mathcal U_C$. The entire child has at
most four worlds. Each of $\mathcal U_A,\mathcal U_B$ contains at most one
actual world over $q$.

Proof. Apply the owning all-world necessity in Assumption 5.3 before doing
any division. Since $x>0$, an actual world must use one of the six positive
simple-root rectangles or a real root in the cluster disk of Proposition
6.2. On the corresponding seven closed real intervals, uniformly over
$Q_{70}$, the finite rational evaluations give

$$
D>0,\qquad |\alpha|>10^{15},\qquad |H_1|>\frac1{10},\qquad C_0>50.
\tag{7.1}
$$

For the simple roots the real intervals have centre $\xi_i$ and radius
$10^{-30}$; for the cluster use $[\xi_C-10^{-25},\xi_C+10^{-25}]$.
First evaluate (5.3), then $d=-\zeta/\alpha$, then (5.5). Thus (7.1)
does not assume the legality of an unfiltered root. More precise common
lower bounds from these same evaluations are
$|\alpha|>1.811\cdot10^{15}$, $|H_1|>0.1669$, $C_0>56$.

The source filter is as follows. The displayed short $x$ decimals identify
the intervals already specified exactly by (6.1)–(6.2).

| Interval | Identifying $x$ value | Necessary source conclusion from (5.5) |
| --- | --- | --- |
| $\mathcal R_9$ | $0.34267538271006$ | $7<r<8$ |
| $\mathcal R_{10}$ | $0.51900782006855$ | $-6.2<b<-6.0$ |
| $\mathcal R_{13}$ | $1.1244628159959$ | $-0.43<b<-0.42$ |
| $\mathcal R_{14}$ | $1.2435339891637$ | $-0.57<b<-0.55$ |
| $\mathcal R_{16}$ | $2.7486080291816$ | $\|(r,b)-c_A\|_\infty<10^{-22}$ |
| $\mathcal R_{15}$ | $2.7221501401249$ | $\|(r,b)-c_B\|_\infty<10^{-22}$ |
| $\mathcal D_C\cap\mathbb R$ | $0.9257810024683$ | $\|(r,b)-c_C\|_\infty<10^{-14}$ |

The first four rows violate a strict original source guard. Every remaining
actual world therefore lies in the indicated $A,B,C$ patch. By (5.4) and
(7.1), each possible $x$ fixes one drift, and F, Lemma 30.2, fixes at most
one entire world at that $(x,d)$. The two retained simple roots permit at
most one world each; the cluster permits at most two. This proves the
four-world bound and the asserted patch bounds.

This argument has not removed an exceptional sector as a hypothesis.
The carrier statement was applied to every actual singular, zero-drift,
lower-degree, sampled-zero, repeated-root or $F_0=0$ companion. The filter
then placed each possible world in a regular patch. The full converse
guards (5.6) remain necessary for any proposed root lift; no surviving
carrier root is declared legal solely from its survival in this table. ∎

## 8. Terminal injectivity on the entire child

**Proposition 8.1 (Whole-child $J$ injectivity and the possible $M$ pair).**
For every $q\in Q_{70}$, $a=f_{MJ}$ is injective on the entire $C(q)$.
If this child contains an $M$ pair, that pair consists of its one $A$-patch
world and its one $B$-patch world, and is its unique unordered $M$ pair.

Proof. The source squares in (3.2) are convex, disjoint and strict.
Substitution of their rational endpoints into the regular circuit gives
$\Lambda\in(5,6),(4,5),(-0.092,-0.091)$, respectively. Thus the original
regular lift and its derivatives are defined throughout each square.
With the exact matrices from (3.4)–(3.6), the uniform rational chart bounds
and terminal ranges are

| Source square | $\sup\|I-B_i^JD(p,a)\|_\infty$ | $a$ range | $m$ range |
| --- | --- | --- | --- |
| $\mathcal U_A$ | $<1/50$ | $(406,407)$ | $(522,524)$ |
| $\mathcal U_B$ | $<1/50$ | $(517,518)$ | $(522,524)$ |
| $\mathcal U_C$ | $<1/50$ | $(333,334)$ | $(492,493)$ |

On $\mathcal U_C$ one also has

$$
\sup\|I-B_C^MD(p,m)\|_\infty<\frac1{10}.
\tag{8.1}
$$

The matrices and their quantitative bins are in Section 3. The inequalities
in this table and (8.1) use the derivatives of (2.1)–(2.3) on the entire
squares, with the rational interval rules of Definition 3.1. In particular
the domains here have radius $10^{-10}$, not radius $10^{-90}$.

For $s_0,s_1$ in one square with equal $L(s)=(p(s),a(s))$, integrate
$B_i^JDL$ on the straight segment joining them. The equality of the
endpoints gives

$$
s_1-s_0=\int_0^1\bigl(I-B_i^JDL(s_0+u(s_1-s_0))\bigr)(s_1-s_0)\,du.
$$

The norm bound forces $\|s_1-s_0\|_\infty\le
\tfrac1{50}\|s_1-s_0\|_\infty$, hence $s_0=s_1$. The regular lift
has only one complete world at that source. Distinct patches have disjoint
$a$ ranges. Proposition 7.1 therefore proves injectivity on every actual
companion of the entire child, including companions unused by a selected
pair.

The same segment argument with (8.1) excludes a distinct $M$ pair within
$\mathcal U_C$. Its $m$ range excludes $C$-to-$A$ and $C$-to-$B$ pairs.
Proposition 7.1 allows at most one world in each of the other two patches.
Consequently the only possible $M$ pair is the unordered $A,B$ pair. ∎

**Corollary 8.2 (Local strict-joint exclusion).** One has
$Q_{70}\cap D_J=\varnothing$ and hence
$Q_{70}\cap D_J\cap D_M=\varnothing$.

Proof. A strict $J$ pair would contradict Proposition 8.1. ∎

## 9. The actual $M$ curve and the orientation of the unused fold

**Definition 9.1 (Source derivatives at the exact zero).** Put
$t^*=r_A^*$ and let

$$
\mathcal M(r_A,b_A,r_B,b_B)=(p_A-p_B,v_A-v_B,m_A-m_B),\qquad
\mathscr D=\left.\frac{\partial\mathcal M}{\partial(b_A,r_B,b_B)}\right|_{z^*}.
\tag{9.1}
$$

Define the exact common-base derivatives by solving

$$
\begin{pmatrix}b_A'\\r_B'\\b_B'\end{pmatrix}
=-\mathscr D^{-1}\frac{\partial\mathcal M}{\partial r_A},\qquad
p_M'=p_{A,r}+p_{A,b}b_A',\quad
v_M'=v_{A,r}+v_{A,b}b_A'.
\tag{9.2}
$$

At $C^*$ put

$$
\begin{gathered}
k=-p_r/p_b,\qquad w=(1,k),\qquad
\beta=w^{\mathsf T}\left(D^2v-\frac{v_b}{p_b}D^2p\right)w,\\
\eta=v_M'-\left(\frac{v_b}{p_b}\right)_{C^*}p_M',\qquad
a_s=a_r+ka_b,\quad m_s=m_r+km_b,\quad x_s=x_r+kx_b,\\
\lambda=\sqrt{-2\eta/\beta}>0.
\end{gathered}
\tag{9.3}
$$

**Proposition 9.2 (Transversality and fold derivatives).** The following
strict bounds hold at the exact zero of Proposition 4.1.

| Quantity | Rational interval |
| --- | --- |
| $\det\mathscr D$ | $(12803962,12803963)$ |
| $p_M'$ | $(-78,-77)$ |
| $v_M'$ | $(584,585)$ |
| $p_b(C^*)$ | $(4628,4629)$ |
| $k$ | $(0.5811,0.5812)$ |
| $\beta$ | $(-643,-642)$ |
| $\eta$ | $(796,797)$ |
| $a_s$ | $(81,82)$ |
| $m_s$ | $(26,27)$ |
| $x_s$ | $(-0.00971,-0.00970)$ |
| $\lambda^2$ | $(2.47,2.48)$ |
| $2a_s\lambda$ | $(256,257)$ |
| $2m_s\lambda$ | $(84,85)$ |

Proof. Differentiate the rational response circuit and $x=(j+r)/U$,
evaluate the resulting first and second derivatives on $\mathcal B_6$,
and use (9.2)–(9.3) with Definition 3.1. The inverse in (9.2) can be
evaluated by its adjugate and determinant; the first interval in the table
excludes zero on this whole evaluation box. The positive square-root
bounds are verified by squaring positive rational endpoints. The last
three rows use the direct expression $-2\eta/\beta$ and the corresponding
products, rather than replacing their factors by the earlier coarse table
intervals. These operations give the displayed strict rational intervals
at every possible $z^*\in\mathcal B_6$. ∎

**Theorem 9.3 (A transverse unused-companion birth with entire-child counts).**
There is a $\delta>0$ and an actual analytic $M$-pair curve

$$
A(t)=(P(t,b_A(t)),g_A(t),d_A(t)),\quad
B(t)=(P(r_B(t),b_B(t)),g_B(t),d_B(t)),\quad |t-t^*|<\delta,
$$

whose worlds are given by the original lift (2.1). Their exact common
acquired base $q(t)=(p(t),v(t))$ lies in $\operatorname{int}Q_{70}$ and
satisfies $m(A(t))=m(B(t))$, with $A(t)\ne B(t)$ throughout. Their entire
actual child is

$$
C(q(t))=
\begin{cases}
\{A(t),B(t),C_+(t),C_-(t)\},&t^*-\delta<t<t^*,\\
\{W_A^*,W_B^*,W_C^*\},&t=t^*,\\
\{A(t),B(t)\},&t^*<t<t^*+\delta.
\end{cases}
\tag{9.4}
$$

All worlds in the first line are distinct strict original worlds.
Throughout the interval, $J$ is injective on the entire child and the
unique unordered $M$ pair is $\{A(t),B(t)\}$. The quantities
$\delta$ and the curve neighbourhood are asserted to exist sufficiently
small; no numerical $t$ interval is specified.

Proof. The first bound in Proposition 9.2 and the analytic
implicit-function theorem solve $\mathcal M=0$ uniquely near the exact
zero for $(b_A,r_B,b_B)$ as functions of $t=r_A$. The resulting sources
remain in the disjoint strict $A,B$ patches. Evaluating their original
lifts gives analytic complete worlds, with exact equality of their
$p,v,m$ functions. Shrinking the interval keeps $q(t)$ inside
$\operatorname{int}Q_{70}$.

Since $p_b(C^*)\ne0$, the analytic implicit-function theorem gives a
source coordinate $b=b(p,r)$ near $C^*$. This is a mathematical chart,
not an additional observed quantity. Put

$$
\widehat v(p,r)=v(r,b(p,r)).
$$

Equation (2.7), the exact equality $F_v(C^*)=0$ and $p_b\ne0$ imply
$\widehat v_r(p^*,r_C^*)=0$. Differentiating $p(r,b(p,r))=p$ shows
$b_r=k$ and gives

$$
\widehat v_{rr}(p^*,r_C^*)
=w^{\mathsf T}\left(D^2v-\frac{v_b}{p_b}D^2p\right)w=\beta<0.
\tag{9.5}
$$

There is consequently an analytic critical source $r=\sigma(p)$ with
$\sigma(p^*)=r_C^*$ and a strict nondegenerate maximum in the $r$
coordinate. Define its critical-value curve and the transverse displacement
by

$$
h(p)=\widehat v(p,\sigma(p)),\qquad
\Delta(t)=v(t)-h(p(t)).
$$

At the critical source, $h'(p^*)=(v_b/p_b)_{C^*}$. Hence

$$
\Delta(t^*)=0,\qquad\Delta'(t^*)=\eta>0.
\tag{9.6}
$$

The equation $\widehat v(p(t),r)=v(t)$ therefore has two nearby real
sources for $t<t^*$, one for $t=t^*$ and none for $t>t^*$, after
shrinking the interval. For completeness, Taylor's theorem writes
$h(p)-\widehat v(p,r)=(r-\sigma(p))^2u(p,r)$ with $u>0$ near the
critical source. The coordinate $(r-\sigma(p))\sqrt{u(p,r)}$ has
nonzero $r$ derivative at the centre. In this coordinate the equation
is $y^2=-\Delta(t)$, giving precisely these local real counts.

It remains to show that these are counts for the whole actual child.
First the carrier at $q^*$ has a double root at the source $C^*$.
Indeed the owning necessity gives the identity

$$
R(x(r,b),p(r,b),v(r,b))=0
$$

on the regular source neighbourhood. Differentiate at $C^*$ in direction
$w$. Both $p_w$ and $v_w$ vanish there, so $R_xx_s=0$.
Proposition 9.2 gives $x_s\ne0$, hence $R_x=0$. The actual $C^*$ root
lies in $\mathcal D_C$, whose total root multiplicity is two. Its
multiplicity is therefore exactly two, and it exhausts that cluster at
$q^*$. The unit $\alpha$ fixes one drift there, and faithful
reconstruction fixes one complete world. The other retained simple roots
are the actual worlds $A^*,B^*$ from Proposition 4.1. Thus the entire
child at $q^*$ consists of exactly three worlds.

As $q\to q^*$ in $Q_{70}$, both roots of the cluster tend to this unique
double root: any convergent subsequence in the closed cluster disk must
limit to a root at $q^*$, and the uniform Rouché inequality excludes its
boundary. The continuous rational drift and reconstruction functions are
defined on the full real cluster interval by (7.1). Consequently every
possible actual $C$-patch companion tends to $C^*$ and eventually lies in
the local fold neighbourhood. No other $C$-patch worlds can remain
outside that neighbourhood on arbitrarily small parts of the curve.

Proposition 7.1 already excludes every other patch and permits at most one
world in each $A,B$ patch. The analytic selected worlds provide those two
worlds throughout. The two local real fold sources for $t<t^*$ are strict
and regular, so their original lifts are actual worlds at exactly $q(t)$.
They exhaust all possible $C$ companions. This proves (9.4), including
its entire-child quantifier. Finally Proposition 8.1 proves whole-child
$J$ injectivity and uniqueness of the unordered selected $M$ pair on
both sides and at the fold. ∎

## 10. Exact two-sheet lifts and the complete six-pair product

**Proposition 10.1 (Original-world two-sheet expansions).** For
$t=t^*-\rho^2$, $\rho>0$ sufficiently small, label the two additional
worlds in Theorem 9.3 by $C_+(\rho),C_-(\rho)$ so that their source
$r$ derivatives at $\rho=0$ are $+\lambda,-\lambda$. Their sources
are analytic in $\rho$ and satisfy

$$
\begin{aligned}
r_+(\rho)&=r_C^*+\lambda\rho+O(\rho^2),&
r_-(\rho)&=r_C^*-\lambda\rho+O(\rho^2),\\
b_+(\rho)&=b_C^*+k\lambda\rho+O(\rho^2),&
b_-(\rho)&=b_C^*-k\lambda\rho+O(\rho^2).
\end{aligned}
\tag{10.1}
$$

For each sign its entire gain, drift and source are exactly

$$
\begin{gathered}
P_\pm=P(r_\pm,b_\pm),\quad
e_\pm=-\frac{24}{5}(b_\pm-1/8)
                 \frac{6/T_\pm-2/U_\pm}{\Lambda_\pm},\quad
d_\pm=24+e_\pm,\\
g_\pm(s)=\sum_{i=0}^3 q_{\pm,i}
                   \prod_{\substack{0\le j\le3\\j\ne i}}\frac{s-j}{i-j},\\
(q_{\pm,0},q_{\pm,1},q_{\pm,2},q_{\pm,3})
=\left(-d_\pm,-e_\pm/j_\pm,
       (27/5-e_\pm)/T_\pm,-e_\pm/n_\pm\right).
\end{gathered}
\tag{10.2}
$$

They have the common exact acquired base $q(t^*-\rho^2)$ and the
original readings at all clocks zero through six. Their terminal splittings
are

$$
\begin{aligned}
a(C_+(\rho))-a(C_-(\rho))&=2a_s\lambda\rho+O(\rho^2),\\
m(C_+(\rho))-m(C_-(\rho))&=2m_s\lambda\rho+O(\rho^2),
\end{aligned}
\tag{10.3}
$$

with $256<2a_s\lambda<257$ and $84<2m_s\lambda<85$.

Proof. In the fold equation substitute

$$
t=t^*-\rho^2,\qquad r=\sigma(p(t))+\rho u.
$$

The analytic numerator
$\widehat v(p(t),\sigma(p(t))+\rho u)-v(t)$ is divisible by
$\rho^2$. Its quotient extends analytically to $\rho=0$ and there equals

$$
\eta+\frac\beta2u^2.
\tag{10.4}
$$

The two roots $u=\pm\lambda$ are simple because $\beta\lambda\ne0$.
The analytic implicit-function theorem supplies analytic $u_\pm(\rho)$
with those limiting values. Since $p(t)-p^*=O(\rho^2)$, the shifts
$\sigma(p(t))-r_C^*$ and $b(p(t),\sigma(p(t)))-b_C^*$ are both
$O(\rho^2)$. Differentiating $b(p,r)$ in $r$ gives $k$ at the centre,
proving (10.1).

The strict source inequalities and $\Lambda\ne0$ persist. Formula (10.2)
is precisely the original owning lift at each source, so it gives one
whole nonzero polynomial of degree at most three, one fixed drift and all
five $H_4$ readings. The equations defining $b(p,r)$ and the fold roots
give exactly $p=p(t)$ and $v=v(t)$ for those same worlds. There is no
refitting of gains or additional acquired terminal value. The nonzero
$r$ splitting makes the worlds distinct for $\rho>0$. Taylor expansion
of the two terminal functions gives (10.3); the coefficients have the
rational bounds of Proposition 9.2. ∎

**Theorem 10.2 (Nonzero deflated all-six-pair $J$ product).** For positive
$\rho$ sufficiently small, use the ordered labels

$$
W_1=A(t^*-\rho^2),\quad W_2=B(t^*-\rho^2),\quad
W_3=C_+(\rho),\quad W_4=C_-(\rho).
$$

These are all the worlds in the same entire actual child. Put
$a_i=a(W_i)$ and retain every possible unordered $J$ pair in

$$
\begin{aligned}
Z_J(\rho)&=\prod_{1\le i<j\le4}(a_i-a_j)\\
&=(a_A-a_B)(a_A-a_{C_+})(a_A-a_{C_-})
  (a_B-a_{C_+})(a_B-a_{C_-})(a_{C_+}-a_{C_-}).
\end{aligned}
\tag{10.5}
$$

Then

$$
\begin{aligned}
\lim_{\rho\downarrow0}\frac{Z_J(\rho)}\rho
&=(a_A^*-a_B^*)(a_A^*-a_C^*)^2(a_B^*-a_C^*)^2
                   (2a_s\lambda)\\
&\in(-5.181\cdot10^{12},-5.180\cdot10^{12}).
\end{aligned}
\tag{10.6}
$$

In particular this signed local limit is nonzero. The raw product has a
zero at $\rho=0$ solely from the repeated label $C_+=C_-=W_C^*$,
which is one world and does not satisfy within-pair distinctness.

Proof. The five factors in (10.5) other than $a_{C_+}-a_{C_-}$ have
nonzero limits, by the disjoint $a$ ranges in Proposition 8.1.
Proposition 10.1 writes the remaining factor as
$\rho\theta(\rho)$, with $\theta$ analytic and
$\theta(0)=2a_s\lambda\in(256,257)$. Thus only this certified diagonal
birth factor $\rho$ is removed in (10.6); all six pair differences
remain represented, including every pair using neither selected $M$
endpoint. Taking their limits gives the first equality in (10.6).

For its rational interval, evaluate $a_A,a_B,a_C,a_s,-2\eta/\beta$ on
$\mathcal B_6$ by (2.1)–(2.3), (9.2)–(9.3) and Definition 3.1,
enclose the positive square root by squared rational endpoint comparisons,
and multiply the displayed factors. This yields the second line of
(10.6); no approximate terminal equality is involved. Its sign also
follows without the finer endpoints: $a_A^*-a_B^*<0$, both squared
differences are positive, and $a_s,\lambda>0$.

For $\rho>0$ all four worlds are distinct and $Z_J(\rho)\ne0$.
At $\rho=0$ the two $C$ labels coalesce, while $A^*,B^*$ remain
distinct with exactly equal $m$ responses. The resulting raw diagonal
zero is therefore not a strict $J$ pair. Removing it does not settle
any product away from this sufficiently small collar. ∎

## 11. Mathematical dependencies and remaining incidence

**Assumption 11.1 (Classical tools and correspondence).** The intermediate
tools used above have their usual mathematical hypotheses. In the present
application their particular domains and hypotheses are as follows.

| Tool | Particular use and verified hypothesis |
| --- | --- |
| Distinct-node polynomial interpolation; Berrut–Trefethen, [§2](https://doi.org/10.1137/S0036144502417715) | Nodes $0,1,2,3$ in the original lift and $3,4,5,6$ in faithful reconstruction; sampled zeros and lower degrees are allowed. |
| Banach contraction theorem; Rudin, *Principles of Mathematical Analysis*, Theorem 9.23 | The complete closed real source box of Proposition 4.1 and the complete closed complex rectangles of Proposition 6.2; strict self-map and contraction inequalities are (4.2) and (6.4). |
| Rouché's theorem; Rudin, *Real and Complex Analysis*, Chapter 10 | The circle $|x-\xi_C|=10^{-25}$, the degree-two term $t_2(x-\xi_C)^2$ and the strict boundary inequality (6.6). |
| Analytic implicit-function theorem; Krantz–Parks, *A Primer of Real Analytic Functions*, implicit-function theorem | The actual $M$-difference Jacobian, $p_b(C^*)$, the nonzero fold curvature and the two simple roots in (10.4); all functions are rational with excluded poles near their stated sources. |
| Taylor's theorem; Rudin, *Principles of Mathematical Analysis*, Theorem 5.15 | The analytic critical-value displacement and two-sheet terminal expansions, with the exact derivatives and signs of Proposition 9.2. |

For the distinction between strict multiple points and diagonal limits,
Nuno-Ballesteros–Peñafort-Sanchis,
[*Multiple point spaces of finite holomorphic maps*, Definition 2.1 and
Example 2.2](https://arxiv.org/html/1509.04990v2), give a related general
setting. No holomorphic stability assertion or requirement that all four
labels be pairwise distinct is transferred to Definition 1.2. Here all four
are distinct only on the four-world side of this particular fold.
Gaillard–Safey El Din,
[*Solving parameter-dependent semi-algebraic systems*, Problem 1 and
Theorem 2.4](https://arxiv.org/html/2402.07782v2), concern parameter-dependent
real-root information under their stated algebraic hypotheses; those
general results do not supply all-parameter coverage of the present strict
world problem. The numerical locations, rational inequalities, strict
lifts and local fold consequences in Sections 2–10 are source-specific
consequences of the displayed formulas and owning suppliers.

**Definition 11.2 (Unresolved all-real and ancestor statements).** The
remaining all-real question retains the quantifier

$$
\exists (p,v)\in\mathbb R^2,\quad p\ne24,\quad
(p,v)\in D_J\cap D_M,
\tag{11.1}
$$

or its exhaustive negation. Its pairs must satisfy both strict distinctness
guards in Definition 1.2, including the possibility of overlapping pairs.
Only the explicitly specified box $Q_{70}$ is excluded here. The local
curve has no asserted connection to the separate off-$24$ component of
[B](FIB_OFF_P24_UNEQUAL_RATIO_COLLISION_GEOMETRY.md), and no classification
of singular or unbounded sectors outside $Q_{70}$ follows.

Even a solution of (11.1) would leave the same-fifth-response sixth-$J$
child and all the ancestor conjunctions of O, Theorem 17.1. The local
$4/3/2$ counts, whole-child $J$ injectivity and the deflated limit do not
establish a fifth-$M$ $L_2$, an $H_4$ $L_3$, a guarded root $L_7$, an
eight-versus-nine conclusion or an unrestricted recovery theorem.

## 追加锚（本行以下为增补区）

## 12. Separation of all finite boundary labels

**Definition 12.1 (Augmented maps and auxiliary boundary).** Retain the
complete worlds, original clocks, acquired child and distinct-pair guards
of Definitions 1.1–1.2. Write $c=r(1-r)/b$ and

$$
\tau_J=a,\qquad \tau_M=m,\qquad
\Psi_E=(p,v,\tau_E),\qquad
\delta(W)=\min\{r,1-r,b,c\}.
\tag{12.1}
$$

Let $\mathcal H=\mathcal F(H_4)$ be the full strict complete parent,
including its $p=24$ worlds. Its topology uses the source entries, drift
and four padded polynomial coefficients. The off-$24$ subspace is
$X=\{W\in\mathcal H:p(W)\ne24\}$. No sample of the gain, drift,
leading coefficient or discriminant is required to be nonzero.

The finite auxiliary boundary $\partial_f\mathcal H$ consists of the
following nonnegative source labels with their complete gains and drifts:

| Label | $(r,b,c)$ | $q_i(t)$ | $e_i(t)=d_i(t)-24$ |
| --- | --- | --- | --- |
| $C_0(t)$ | $(0,t,0)$ | $t^3-8t-4$ | $-24t(t-1/8)(2+5t)/(5(t^3-8t-4))$ |
| $C_1(t)$ | $(1,t,0)$ | $(t+1)(t^3-4t-2)$ | $-24t(t-1/8)(2+5t)/(5(t^3-4t-2))$ |
| $B_0(t)$ | $(0,0,t)$ | $t-1$ | $3t/(10(t-1))$ |
| $B_1(t)$ | $(1,0,t)$ | $2t^2-1$ | $3t(t+1)/(5(2t^2-1))$ |

Here $t>0$ and $q_i(t)\ne0$. On each open face the single whole gain
is interpolated from $(-24-e,-e/j,(27/5-e)/T,-e/n)$ at $0,1,2,3$.
These are precisely the lifts of S, Definition 12.2. The two additional
corner labels are

| Label | $(r,b,c)$ | $d$ | $(g(0),g(1),g(2),g(3))$ | $(p,v,a,m)$ |
| --- | --- | --- | --- | --- |
| $L$ | $(0,0,0)$ | $24$ | $(-24,3/10,27/5,3/10)$ | $(39/2,258/5,819/10,1977/10)$ |
| $R$ | $(1,0,0)$ | $24$ | $(-24,3/5,27/5,0)$ | $(18,399/5,366,366)$ |

The rational response curves below extend to $t=0$, with identifications
$C_0(0)=B_0(0)=L$ and $C_1(0)=B_1(0)=R$, as complete tuples.
These labels describe limits; they are not legal strict worlds.

**Lemma 12.2 (Exact face fractions).** With the respective $q_i$ in
Definition 12.1, the four responses are as follows.

$$
\begin{aligned}
p_{C_0}(t)&=\frac{-3(72t^3+746t^2+465t+130)}{5q_{C_0}}\\
v_{C_0}(t)&=\frac{-3(375t^3+4431t^2+2486t+344)}{5q_{C_0}}\\
a_{C_0}(t)&=\frac{-9(136t^3+2062t^2+1163t+182)}{5q_{C_0}}\\
m_{C_0}(t)&=\frac{-3(1088t^3+16523t^2+9445t+1318)}{5q_{C_0}}.
\end{aligned}
$$

$$
\begin{aligned}
p_{C_1}(t)&=\frac{-6(36t^4+61t^3+221t^2+181t+30)}{5q_{C_1}}\\
v_{C_1}(t)&=\frac{-3(375t^4+881t^3+2486t^2+1706t+266)}{5q_{C_1}}\\
a_{C_1}(t)&=\frac{-6(204t^4+869t^3+2469t^2+2981t+610)}{5q_{C_1}}\\
m_{C_1}(t)&=\frac{-3(1088t^4+3483t^3+9978t^2+7102t+1220)}{5q_{C_1}}.
\end{aligned}
$$

$$
\begin{aligned}
p_{B_0}(t)&=\frac{-3(16t^2-80t+65)}{10q_{B_0}}\\
v_{B_0}(t)&=\frac{3(45t^2+125t-172)}{10q_{B_0}}\\
a_{B_0}(t)&=\frac{3(384t^2-113t-273)}{10q_{B_0}}\\
m_{B_0}(t)&=\frac{3(384t^2+271t-659)}{10q_{B_0}}.
\end{aligned}
$$

$$
\begin{aligned}
p_{B_1}(t)&=\frac{-6(8t^3-24t^2-2t+15)}{5q_{B_1}}\\
v_{B_1}(t)&=\frac{3(45t^3+215t^2-33t-133)}{5q_{B_1}}\\
a_{B_1}(t)&=\frac{3(384t^3+1039t^2-232t-610)}{5q_{B_1}}\\
m_{B_1}(t)&=\frac{3(384t^3+1039t^2-232t-610)}{5q_{B_1}}.
\end{aligned}
$$

Proof. Substitute the face source and its $e$ into (2.1), apply the
three interpolation rows (2.3), and multiply by the traces in (2.2).
This gives the displayed fractions by rational reduction. In particular
every row still comes from one polynomial and one fixed drift.
The $B_0,B_1$ fractions are exactly S, Theorem 13.1, and the face and
corner lifts are those of S, Definition 12.2. ∎

**Lemma 12.3 (Twenty localized rational certificates).** Order the faces
as $C_0,C_1,B_0,B_1$. For $i\le j$ and $E\in\{J,M\}$ define

$$
\begin{aligned}
A_{ij}&=\operatorname{num}(p_i(t)-p_j(s)),\\
V_{ij}&=\operatorname{num}(v_i(t)-v_j(s)),\\
T_{ij,E}&=\operatorname{num}(\tau_{E,i}(t)-\tau_{E,j}(s)).
\end{aligned}
\tag{12.2}
$$

Here $\operatorname{num}$ means the numerator after cancelling the
polynomial gcd of numerator and denominator over $\mathbb Q$; multiplication
by a nonzero rational unit is immaterial. When $i=j$, divide each of the
three displayed numerators by $t-s$, exactly, and use those quotients
instead. There is no cancellation of a factor $t$ or $s$. In
$\mathbb Q[w,s,t]$ let

$$
I_{ij,E}=\langle A_{ij},V_{ij},T_{ij,E},
                 wq_i(t)q_j(s)-1\rangle.
\tag{12.3}
$$

The reduced monic Gröbner bases for lexicographic order $w>s>t$ are:

| $(i,j)$ | $E=J$ | $E=M$ |
| --- | --- | --- |
| $(C_0,C_0)$ | $\{1\}$ | $\{1\}$ |
| $(C_0,C_1)$ | $\{1\}$ | $\{1\}$ |
| $(C_0,B_0)$ | $\{w-1/4,s,t\}$ | $\{w-1/4,s,t\}$ |
| $(C_0,B_1)$ | $\{1\}$ | $\{1\}$ |
| $(C_1,C_1)$ | $\{1\}$ | $\{1\}$ |
| $(C_1,B_0)$ | $\{1\}$ | $\{1\}$ |
| $(C_1,B_1)$ | $\{w-1/2,s,t\}$ | $\{w-1/2,s,t\}$ |
| $(B_0,B_0)$ | $\{1\}$ | $\{1\}$ |
| $(B_0,B_1)$ | $\{1\}$ | $\{1\}$ |
| $(B_1,B_1)$ | $\{1\}$ | $\{1\}$ |

Proof. Equations (12.2)–(12.3) and Lemma 12.2 specify every rational
coefficient of these twenty finite computations. One exact reduction
rule to reproduce the table is the following. Make each nonzero generator
monic in the stated lexicographic order. For each pair $f,g$ form

$$
S(f,g)=\frac{\operatorname{lcm}(\operatorname{LM}f,\operatorname{LM}g)}
 {\operatorname{LM}f}f-
\frac{\operatorname{lcm}(\operatorname{LM}f,\operatorname{LM}g)}
 {\operatorname{LM}g}g.
\tag{12.4}
$$

Divide by the current ordered list using exact rational leading-term
reduction. Append each nonzero monic remainder and include its new pairs;
continue until all pair remainders are zero. Delete redundant leading
terms and reduce each remaining polynomial by the others. This gives
exactly the bases displayed in the table. All operations are over
$\mathbb Q$; the input fractions, diagonal divisions, localization and
monomial order are fixed above. The unit rows mean equality to the whole
polynomial ring. The two nonunit rows mean, respectively, equality to
$\langle4w-1,s,t\rangle$ and $\langle2w-1,s,t\rangle$.
Their localizing constants also follow directly from
$q_{C_0}(0)q_{B_0}(0)=4$ and $q_{C_1}(0)q_{B_1}(0)=2$.
Thus they represent exactly the two corner identifications. ∎

**Theorem 12.4 (T1: full finite-boundary separation).** For each
$E\in\{J,M\}$ the augmented map $\Psi_E$ is injective on
$\partial_f\mathcal H$, with its two corner identifications.
The assertion includes all nonpole boundary labels with $p=24$.

Proof. Any two nonpole parameters with the same three responses supply a
common zero of the corresponding localized ideal, by taking
$w=1/(q_i(t)q_j(s))$. For two distinct parameters on one face, division
by $t-s$ preserves this implication. Lemma 12.3 excludes every such
zero except $t=s=0$ in the two identified chart pairs. Every corner is
represented by a chart at zero, so the same table includes comparisons
between corners and open faces and between the two corners. The gains
and drifts at the identified corners agree by Definition 12.1.

For the $B$ faces, S, Theorem 13.1, already proves same-face
acquired-base injectivity, and S, Proposition 13.3, already excludes
opposite-face equal-terminal coincidences away from the poles. Those
comparisons supply the corresponding open-$B$ cases. The remaining
comparisons in Lemma 12.3 supply the $C/C$, $C/B$ and corner cases.
No equation here divides by $p-24$. For clarity, the reduced numerators
of $p_i(t)-24$ are

$$
\begin{array}{c|l}
C_0&-3(8t-1)(14t^2+95t+30)\\
C_1&-6(8t-1)(7t^3+11t^2+19t+10)\\
B_0&-3(16t^2-15)\\
B_1&-6(8t^3+16t^2-2t-5).
\end{array}
\tag{12.5}
$$

All allowed zeros of these expressions remain in the assertion. ∎

## 13. Local injectivity on the full parent at finite boundary labels

**Definition 13.1 (Transverse source charts).** Near an open face use
coordinates $(t,z)$ with the following exact source expressions:

$$
\begin{array}{c|ccc}
 &r&b&c\\ \hline
C_0&z&t&z(1-z)/t\\
C_1&1-z&t&z(1-z)/t\\
B_0&tz&z&t-t^2z\\
B_1&1-tz&z&t-t^2z.
\end{array}
\tag{13.1}
$$

The face is $z=0$, $t>0$. Every row satisfies $bc=r(1-r)$
identically and is a local chart of that source surface. At an allowed
face point $j,n,T,U,\Lambda$ are nonzero. Consequently the full
parent converse gives a unique analytic drift and whole gain in this
two-dimensional chart, using precisely (2.1)–(2.3).

**Lemma 13.2 (Twelve minors and eight nonzero resultants).** Evaluate at
$z=0$ the minors

$$
M_{pv}=p_t v_z-v_t p_z,\qquad
M_{pE}=p_t\tau_{E,z}-\tau_{E,t}p_z.
\tag{13.2}
$$

Let $P_i,N_{i,J},N_{i,M}$ be the positive-leading integer polynomials
whose complete descending coefficient lists are below. A list
$(a_d,\ldots,a_0)$ means $\sum_{k=0}^d a_k t^k$.

$$
\begin{aligned}
\operatorname{coeff}_{\downarrow}(P^{C_0})&=(155926,-601697,-1542906,-4285783,-4638172,-687942,930652,283120)\\
\operatorname{coeff}_{\downarrow}(N_{J}^{C_0})&=(21340,157300,599729,1849195,2184931,1104443,271656,28170)\\
\operatorname{coeff}_{\downarrow}(N_{M}^{C_0})&=(960520,-2391609,-2601574,-2463507,1450942,9415154,6961040,1403320).
\end{aligned}
$$

$$
\begin{aligned}
\operatorname{coeff}_{\downarrow}(P^{C_1})&=(77963,-101611,70626,755023,601239,-322676,-493790,-140952,-43178,-59380,-19276)\\
\operatorname{coeff}_{\downarrow}(N_{J}^{C_1})&=(85360,205720,409436,983356,405462,324593,610101,247856,-106980,-90804,-25716)\\
\operatorname{coeff}_{\downarrow}(N_{M}^{C_1})&=(960520,-862625,1054299,9415074,7210470,-3592846,-5634854,-2220148,-1159732,-861256,-223968).
\end{aligned}
$$

$$
\begin{aligned}
\operatorname{coeff}_{\downarrow}(P^{B_0})&=(25680,-37062,-41788,90489,-37320)\\
\operatorname{coeff}_{\downarrow}(N_{J}^{B_0})&=(176640,-403664,154720,189841,-117540)\\
\operatorname{coeff}_{\downarrow}(N_{M}^{B_0})&=(164352,-294544,-96992,412369,-185190).
\end{aligned}
$$

$$
\begin{aligned}
\operatorname{coeff}_{\downarrow}(P^{B_1})&=(25680,66742,-29150,-85105,9535,35742,-505,-4819)\\
\operatorname{coeff}_{\downarrow}(N_{J}^{B_1})&=(76032,169560,-83960,-206086,38555,85392,-8869,-12858)\\
\operatorname{coeff}_{\downarrow}(N_{M}^{B_1})&=(82176,184888,-95368,-238974,32487,101504,-2495,-13998).
\end{aligned}
$$

The superscript on a polynomial names its face. Their precise scalar
normalizations in (13.2) are:

| Face $i$ | $D_i$ | $M_{pv}$ | $M_{pJ}$ | $M_{pM}$ |
| --- | --- | --- | --- | --- |
| $C_0$ | $25t(t^3-8t-4)^3$ | $-9P_i/D_i$ | $-288N_{i,J}/D_i$ | $-9N_{i,M}/D_i$ |
| $C_1$ | $25t(t+1)^3(t^3-4t-2)^3$ | $18P_i/D_i$ | $72N_{i,J}/D_i$ | $9N_{i,M}/D_i$ |
| $B_0$ | $200(t-1)^3$ | $-9P_i/D_i$ | $-9N_{i,J}/D_i$ | $-9N_{i,M}/D_i$ |
| $B_1$ | $25(2t^2-1)^3$ | $-9P_i/D_i$ | $-18N_{i,J}/D_i$ | $-18N_{i,M}/D_i$ |

The degrees and Sylvester determinant residues are:

| Face | $(\deg P_i,\deg N_{i,J},\deg N_{i,M})$ over $\mathbb Q$ and $\mathbb F_{101}$ | $\operatorname{Res}_t(P_i,N_{i,J})\bmod101$ | $\operatorname{Res}_t(P_i,N_{i,M})\bmod101$ |
| --- | --- | --- | --- |
| $C_0$ | $(7,7,7)$ | $27$ | $58$ |
| $C_1$ | $(10,10,10)$ | $78$ | $58$ |
| $B_0$ | $(4,4,4)$ | $73$ | $18$ |
| $B_1$ | $(7,7,7)$ | $40$ | $19$ |

Proof. Differentiate the whole-parent circuit (2.1)–(2.3) after
substitution of (13.1), and then set $z=0$. Reducing each rational
minor gives exactly the coefficient lists and scalar factors above.
This calculation differentiates the transverse direction as well as
the face parameter; differentiating only Lemma 12.2 would not suffice.

For a completely specified resultant convention, if $F,G$ have degrees
$d,e$, take rows $t^{e-1}F,\ldots,F,t^{d-1}G,\ldots,G$, with columns
$t^{d+e-1},\ldots,1$. Its determinant, applied to the displayed
integer lists and reduced modulo $101$, gives the eight entries of the
table. Their leading coefficients remain nonzero modulo $101$, so
these are degree-preserving reductions of the integer Sylvester
matrices. Each integer resultant is nonzero. Thus $P_i$ has no common
complex zero with either $N_{i,J}$ or $N_{i,M}$. This is the classical
Sylvester criterion, with the convention of F, Lemma 31.2; see also
Moreno Maza, *The resultant*, Definition 4 and Propositions 5–7,
[as cited there](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html).
All $D_i$ are nonzero on the allowed open face. ∎

**Proposition 13.3 (Full-parent injectivity at every open face).** At
each allowed open-face label and for either $E$, a neighbourhood in
complete source/gain/drift coordinates has $\Psi_E$ injective on its
strict full-parent worlds.

Proof. By Lemma 13.2, $M_{pv}$ and $M_{pE}$ cannot both vanish.
At least one two-coordinate submap of $\Psi_E$ therefore has an
invertible differential on the two-dimensional chart (13.1).
The inverse-function theorem gives a neighbourhood on which that
submap is injective. The parent lift is unique throughout a smaller
neighbourhood because $\Lambda\ne0$ there. The source chart and
whole-world lift identify all nearby strict parent worlds with this
chart, proving the assertion. No condition on individual gain samples,
drift or polynomial degree was introduced. ∎

**Lemma 13.4 (One analytic neighbourhood at the lower corner).** Put
$j=b+c$, $\theta=b/j$ and $u=\theta(1-\theta)$. On the lower
rank-one branch define

$$
\begin{gathered}
r=\frac{2u j^2}{1+\sqrt{1-4u j^2}},\qquad
\rho=\frac rj=\frac{2u j}{1+\sqrt{1-4u j^2}},\qquad
T=1+\theta j,\quad U=1+2\theta j,\\
L_-=j(1+6/T+1/U)-4-4/(1+\rho),\\
N=-\frac{24}{5}(\theta j-1/8)(6/T-2/U),\qquad h=N/L_-.
\end{gathered}
\tag{13.3}
$$

Use the analytic expressions at $j=0$ in these formulas. The entire
response circuit extends analytically to one open neighbourhood of

$$
\mathcal R=\{(j,\theta):|j|\le1/64,\ -1/4\le\theta\le5/4\}.
\tag{13.4}
$$

On this rectangle the whole gain samples and drift are

$$
e=jh,\quad d=24+jh,\qquad
(g_0,g_1,g_2,g_3)=
\left(-24-jh,-h,\frac{27/5-jh}{T},-\frac h{1+\rho}\right).
\tag{13.5}
$$

Proof. Here $|u|\le1$, $1-4uj^2\ge1-1/1024$,
$|\rho|<1/32$, $T\ge251/256$, $U\ge123/128$ and
$|j(1+6/T+1/U)|<1/4$. In particular

$$
L_-<-4-128/33+1/4<-7.
\tag{13.6}
$$

Every square root has positive radicand and every denominator is
separated from zero on the whole compact rectangle. These strict
bounds persist on an open neighbourhood of it. Since
$j\Lambda=L_-$, the parent equation gives $e=jh$, and cancellation
within these analytic formulas gives exactly (13.5). Interpolation
and multiplication by the original traces are analytic operations
there, proving the common extension. ∎

**Lemma 13.5 (Lower-corner jets and uniform first-derivative bounds).**
Let $\Psi_E(L)$ be the corner triple in Definition 12.1. On the common
neighbourhood of Lemma 13.4,

$$
\Psi_E(j,\theta)-\Psi_E(L)
=j A_E\begin{pmatrix}1\\\theta\\\theta(1-\theta)\end{pmatrix}
+j^2 R_E(j,\theta),
\tag{13.7}
$$

where

$$
A_J=\begin{pmatrix}
-9/2&141/4&3/4\\
141/10&1278/5&24/5\\
579/5&975/4&21/4
\end{pmatrix},\qquad
A_M=\begin{pmatrix}
-9/2&141/4&3/4\\
141/10&1278/5&24/5\\
582/5&18099/20&63/4
\end{pmatrix}.
\tag{13.8}
$$

Their determinants are $-136431/40$ and $221589/400$. The first
two rows of their inverses are, respectively,

$$
L_J=\begin{pmatrix}
-764/15159&10/15159&100/15159\\
-3569/25265&491/15159&-143/15159
\end{pmatrix},\qquad
L_M=\begin{pmatrix}
-4712/8207&1830/8207&-1000/24621\\
14962/24621&-7030/24621&1430/24621
\end{pmatrix}.
\tag{13.9}
$$

Both $R_E$ and its first derivatives with respect to $j$ and $\theta$
are uniformly bounded on $\mathcal R$.

Proof. Substitution of (13.3)–(13.5) into the original response circuit
gives the four coefficients of $j$, in order $p,v,a,m$,

$$
\begin{pmatrix}
-9/2+36\theta-3\theta^2/4\\
141/10+1302\theta/5-24\theta^2/5\\
579/5+249\theta-21\theta^2/4\\
582/5+9207\theta/10-63\theta^2/4
\end{pmatrix}.
\tag{13.10}
$$

These are precisely (13.8) applied to
$(1,\theta,\theta(1-\theta))$. Rational matrix multiplication gives
$L_E A_E=(I_2\;0)$ and the stated determinants. To justify the
remainder and its derivatives uniformly, use Taylor's integral formula:

$$
\begin{aligned}
R_E(j,\theta)
 &=\int_0^1(1-s)\,\partial_j^2\Psi_E(sj,\theta)\,ds,\\
\partial_jR_E(j,\theta)
 &=\int_0^1s(1-s)\,\partial_j^3\Psi_E(sj,\theta)\,ds,\\
\partial_\theta R_E(j,\theta)
 &=\int_0^1(1-s)\,\partial_\theta\partial_j^2
                      \Psi_E(sj,\theta)\,ds.
\end{aligned}
\tag{13.11}
$$

All displayed derivatives are continuous on the common compact
rectangle, by Lemma 13.4. Their maxima there bound the three integrals.
This supplies uniform first-derivative remainder bounds on one
neighbourhood, rather than only a pointwise quadratic remainder. ∎

**Proposition 13.6 (A lower Lipschitz bound on the lower-corner cone).**
For both actions $\Psi_E$ is injective on all strict full-parent
worlds in a sufficiently small neighbourhood of $L$.

Proof. Write $\widetilde R_E=L_ER_E$. Let $M\ge0$ bound, for
both actions, the Euclidean norms of $\widetilde R_E$,
$\partial_j\widetilde R_E$ and $\partial_\theta\widetilde R_E$
on $0\le j\le1/128$, $0\le\theta\le1$. Such a common finite
$M$ exists by Lemma 13.5. Choose

$$
\eta=\min\left\{\frac1{128},\frac1{12(M+1)}\right\}.
\tag{13.12}
$$

On the convex triangle $\mathcal T_\eta=\{(j,b):0<b<j<\eta\}$,
the affine response transform is

$$
G_E(j,b):=L_E(\Psi_E(j,b/j)-\Psi_E(L))
=(j,b)^{\mathsf T}+H_E(j,b),\qquad
H_E=j^2\widetilde R_E(j,b/j).
\tag{13.13}
$$

At fixed $b$ or fixed $j$, respectively, its error derivative columns are

$$
\partial_jH_E=2j\widetilde R_E+j^2\partial_j\widetilde R_E
                   -b\partial_\theta\widetilde R_E,\qquad
\partial_bH_E=j\partial_\theta\widetilde R_E.
\tag{13.14}
$$

The uniform bounds give $\|DH_E\|\le6M\eta<1/2$.
Integrate on the segment between any $x,y\in\mathcal T_\eta$:

$$
\|G_E(x)-G_E(y)\|\ge(1-6M\eta)\|x-y\|
>\tfrac12\|x-y\|.
\tag{13.15}
$$

Thus $G_E$, and hence $\Psi_E$, is injective. Every strict source
sufficiently near $(r,b,c)=(0,0,0)$ has the lower root in (13.3),
$0<b<j<\eta$ and $j\Lambda=L_-<-7$. Its parent drift and whole
gain are therefore uniquely (13.5). Consequently this argument covers
all nearby strict full-parent worlds. ∎

**Proposition 13.7 (The upper-corner chart).** Both augmented maps
are locally injective on the strict full parent at $R$.

Proof. In ambient coordinates $(j,b)$ put

$$
r=\frac{1+\sqrt{1-4b(j-b)}}2,\quad c=j-b,\quad n=j+r.
\tag{13.16}
$$

Here $n(0,0)=1$ and
$L_+=j(1+6/T+1/U-4/n)-4$ has value $-4$ at the origin.
The parent formula consequently makes $e/j$ analytic near the origin.
The four gain samples, and hence the entire response circuit, are
analytic there as well. Its full first-order jet is

$$
\begin{pmatrix}p\\v\\a\\m\end{pmatrix}
=\begin{pmatrix}18\\399/5\\366\\366\end{pmatrix}
+j\begin{pmatrix}-12/5\\99/5\\696/5\\696/5\end{pmatrix}
+b\begin{pmatrix}57\\1263/5\\2757/5\\4467/5\end{pmatrix}
+O((|j|+|b|)^2),
\tag{13.17}
$$

with analytic remainder on this one neighbourhood. In particular

$$
D_{(j,b)}(p,v)(0,0)=
\begin{pmatrix}-12/5&57\\99/5&1263/5\end{pmatrix},\qquad
\det D_{(j,b)}(p,v)(0,0)=-43371/25\ne0.
\tag{13.18}
$$

The inverse-function theorem gives local injectivity already for
$(p,v)$, and therefore for each $\Psi_E$. Every nearby strict source
lies on the upper branch (13.16) and has the unique regular parent
lift. ∎

**Theorem 13.8 (T2: full-parent boundary local injectivity).** For
every $B\in\partial_f\mathcal H$ and $E\in\{J,M\}$ there is a
neighbourhood $U_B$ in complete source/gain/drift coordinates such that
$\Psi_E$ is injective on $U_B\cap\mathcal H$.

Proof. Proposition 13.3 treats the four open faces, Proposition 13.6
treats $L$, and Proposition 13.7 treats $R$. These exhaust
Definition 12.1. The face and corner proofs do not restrict $p$,
so the statement includes their $p=24$ labels. ∎

## 14. A uniformly interior endpoint of every bounded-fifth-response pair

**Assumption 14.1 (Exact coercivity suppliers).** The following owning
results are used with their full complete-world domains:

| Supplier | Exact consequence used here |
| --- | --- |
| S, Theorem 7.3 | One finite $B_*>0$ bounds $b$ at both endpoints of every distinct equal-terminal $J$ or $M$ pair at every real off-$24$ acquired base. |
| S, Theorem 12.1 | With $b\le B_*$ and $|p|\le P$, $c$, drift, all four padded coefficients of the same entire gain and all remaining responses are bounded; $p=24$ and singular sources are included in this coercivity statement. |
| S, Definition 12.2 and the exhaustion proof of Theorem 12.3 | Every finite nonstrict source limit with bounded drift and gain is one of the four nonpole face lifts or the two complete corner tuples in Definition 12.1. |
| O, Lemma 12.2 and Theorem 12.3 | $\Lambda^2+A_5^2>0$ at every strict source, including $\Lambda=0$; the fifth response fixes one whole world even at a singular parent source. |
| F, Lemmas 30.2 and 31.3, as used by S, Theorem 7.3 | Zero-safe faithful reconstruction and leading-drift noncollapse in the uniform $b$-cap proof. |

In particular S, Theorem 7.3, is an all-actual-pair theorem, not a
regular-source restriction. Its proof combines the injective large-$b$
parent chart with S, Lemma 7.2: a finite limiting companion would have
$(x,d)=(1/2,0)$ and $H_0=66/5$, while the original equation
$dU=-H_0$ forces that companion back to $b\to\infty$.
The cap is reused with these zero-safe premises; none of the earlier
high-degree elimination certificates is replaced by the boundary
calculations in Sections 12–13.

**Lemma 14.2 (Finite exhaustion also when $p$ tends to $24$).** Suppose
$W_n\in\mathcal H$ have bounded $b_n,p_n$, and
$\delta(W_n)\to0$. After passage to a subsequence their complete
tuples converge to a label in $\partial_f\mathcal H$.
This holds even if $p_n\to24$.

Proof. S, Theorem 12.1, bounds $c_n,d_n$ and every gain coefficient.
Pass to simultaneous limits in these finite-dimensional coordinates.
The source equation $bc=r(1-r)$ passes to the limit, and
$\delta\to0$ forces a nonstrict source. If $j>0$, this is one of
the four open faces. A zero of $\Lambda$ there has nonzero parent
right-hand side, so cannot have finite drift. At every other face
point the parent equation uniquely gives the drift and the four gain
samples in Definition 12.1.

If $j\to0$ on the lower branch, then

$$
\frac rj=\frac{bc}{(1-r)(b+c)}\longrightarrow0,\qquad
\frac nj\longrightarrow1,\qquad
j\Lambda\longrightarrow-8,\qquad e/j\longrightarrow-3/10.
\tag{14.1}
$$

On the upper branch $n\to1$, $j\Lambda\to-4$ and
$e/j\to-3/5$. The original four samples and traces give exactly
$L$ or $R$. This is the finite-exhaustion part of S, Theorem 12.3,
before its intersection with the relative target $Y=\{p\ne24\}$.
It has made no assumption that the limiting $p$ is off $24$.
S, Proposition 12.4, explicitly prevents omitting this distinction. ∎

**Theorem 14.3 (T3: selected-pair interior endpoint).** For every
$P>0$ there is $\varepsilon(P)>0$ such that, for every real
$p\ne24$ with $|p|\le P$, every real $v$, either $E\in\{J,M\}$,
and every distinct pair $W,W'\in C(p,v)$ satisfying
$\tau_E(W)=\tau_E(W')$,

$$
\max\{\delta(W),\delta(W')\}\ge\varepsilon(P).
\tag{14.2}
$$

The same constant works for both actions. No numerical value is asserted.

Proof. Fix $P$ and one action. If no positive constant worked, choose
actual distinct pairs with $|p_n|\le P$, $p_n\ne24$ and
$\max\{\delta(W_n),\delta(W'_n)\}\to0$. The common $b$ cap
of S, Theorem 7.3, and the coercivity of S, Theorem 12.1, give
simultaneously bounded sources, drifts, whole gain coefficients and
responses. Extract a convergent subsequence for both endpoints.
Lemma 14.2 identifies both limiting tuples with finite boundary labels,
including the possibility $p_n\to24$.

Their equal $(p,v,\tau_E)$ responses pass to the limit. Theorem 12.4
makes the two limiting boundary labels equal, with the corner
identifications understood. Theorem 13.8 supplies a common neighbourhood
where the strict full-parent map is injective. Eventually both endpoints
are in that neighbourhood and have equal augmented responses, contrary
to their strict distinctness. Thus there is a positive constant for
each action; take the smaller of the two. ∎

The maximum in (14.2) selects at least one endpoint of the given pair.
It does not bound each endpoint separately and does not impose any
source cutoff on the original world domain.

## 15. Two compact anchors for a joint configuration

**Theorem 15.1 (T4: compact strict anchors).** For every $P>0$ there
is a compact subset $\mathcal A_P\subset\mathcal H$ with the
following property. Every original joint configuration

$$
W_0\ne W_1,\quad W_2\ne W_3,\quad
W_i\in C(p,v),\quad p\ne24,\quad |p|\le P,\qquad
a(W_0)=a(W_1),\quad m(W_2)=m(W_3)
\tag{15.1}
$$

can be relabelled within its two selected pairs so that
$W_0,W_2\in\mathcal A_P$ and
$\delta(W_0),\delta(W_2)\ge\varepsilon(P)$.
If the common base is restricted to a compact
$K\subset\{(p,v):p\ne24\}$, the two anchors lie in a compact
subset $\mathcal A_{P,K}\subset X$.

The anchors may coincide. Cross-pair reuse, different terminal common
values, all nonanchor endpoints and all unused companions retain the
guards of Definition 1.2.

Proof. Apply Theorem 14.3 independently to the selected $J$ pair and
selected $M$ pair. Choose the endpoint with $\delta\ge\varepsilon(P)$
in each. Assumption 14.1 bounds their $b,c,d$ and every padded gain
coefficient by a common finite constant, enlarged if necessary.
In the resulting closed bounded coordinate box impose

$$
bc=r(1-r),\qquad \delta\ge\varepsilon(P),\qquad |p|\le P,
\qquad\text{all five original }H_4\text{ reading equations}.
\tag{15.2}
$$

This defines a closed bounded set in finite-dimensional real space.
Its source is strict by the positive $\delta$ bound. Its gain is
nonzero because a zero gain would make the original readings $0$ and
$24$ equal to the same drift. It is therefore a compact subset
$\mathcal A_P$ of the full parent, containing both chosen endpoints.
It may contain $p=24$ worlds. Intersecting with the closed inverse
image of $K$ under the continuous acquired-base map gives the compact
$\mathcal A_{P,K}$ inside $X$. The endpoint choices do not change
any world, clock, action or acquired observation. ∎

## 16. Off-twenty-four finite-base limits and the remaining joint relation

**Theorem 16.1 (T5: selected-pair finite-base trichotomy).** Let
$E\in\{J,M\}$ and let $(W_n,W'_n)$ be distinct equal-terminal
pairs in $C(p_n,v_n)$, where

$$
(p_n,v_n)\longrightarrow q_*=(p_*,v_*),\qquad p_n\ne24,
\qquad p_*\ne24.
\tag{16.1}
$$

After a subsequence and relabelling within each pair, $W_n$ converges
to a strict world $W\in C(q_*)$, and exactly one of the following
holds for the companion limit:

1. $W'_n\to W'\in C(q_*)$ with $W'\ne W$ and
   $\tau_E(W')=\tau_E(W)$, an actual strict pair.
2. $W'_n\to W$ and
   $\operatorname{rank}(d\Psi_E)_W<2$ on the full analytic parent.
3. $W'_n\to B\in\partial_f\mathcal H$ with
   $\Psi_E(B)=\Psi_E(W)$, a mixed boundary/interior incidence.

No subsequence of such pairs can have both endpoint limits in
$\partial_f\mathcal H$. For a joint sequence apply this statement
to both selected pairs at the same base and on a common subsequence;
no cross-pair distinctness is added.

Proof. The fifth responses are bounded. By Theorem 14.3 choose an
anchor in each pair with $\delta\ge\varepsilon(P)$ for one fixed
$P$ containing the sequence. The cap and coercivity give simultaneous
convergent subsequences of all source, drift and gain coordinates.
The anchor limit is strict by its positive $\delta$ bound. The
original readings pass to the limit, its gain stays nonzero by the
unequal readings $0,24$, and its acquired base is $q_*$. Thus it is
an actual world of $C(q_*)$.

If the companion limit is strict, continuity gives another actual
world of $C(q_*)$ with the same terminal response. If distinct from
the anchor this is case 1. If equal to it, use the analytic
complete-parent surface of S, Theorem 14.2. This surface statement
includes the singular sources: at $\Lambda=0$ one has $b=1/8$,
$\Lambda_r\ne0$ at the two simple roots of O, Theorem 4.2, and
$e\ne0$ for $p_*\ne24$ by F, Lemma 30.2. Hence the defining
parent equation has nonzero $r$ derivative there; elsewhere it solves
for $e$. If $d\Psi_E$ had rank two at $W$, two of its three
coordinates would give a locally injective submap by the
inverse-function theorem. The two convergent endpoints would eventually
be equal, a contradiction. This proves case 2.

If the companion limit is nonstrict, Lemma 14.2 identifies it with
one of the finite boundary tuples. Equality of augmented responses
passes to the limit, giving case 3. The anchor is strict, so these
three alternatives are exhaustive and disjoint. Theorem 14.3 also
excludes a limit with both endpoints boundary. There are only four
selected labels in a joint sequence, so all subsequence extractions
can be made simultaneously after independently relabelling the two
pairs. ∎

**Proposition 16.2 (Scope of the boundary support reduction).** On a
bounded-$p$ region every selected joint configuration has two compact
strict anchors. At an off-$24$ finite-base limit, each selected pair
has one of the three alternatives of Theorem 16.1. In particular a
strict equal-world limit requires criticality of the augmented map
$\Psi_E$, a stronger necessary condition than criticality of the
acquired-base projection alone.

Proof. The first assertion is Theorem 15.1. The alternatives and
augmented criticality are Theorem 16.1. Since $(p,v)$ is a coordinate
projection of $\Psi_E$, rank two for $d(p,v)$ would imply rank two
for $d\Psi_E$. The converse implication need not hold. ∎

Case 2 is an equal-world limit of distinct pairs, not itself a strict
pair. Its criticality is necessary and supplies no sufficient condition
for a strict pair nearby. Case 3 retains a boundary label only as an
auxiliary limit, not as a legal endpoint of the original joint relation.
The trichotomy assumes $p_*\ne24$; Sections 12–14 retain the
$p\to24$ boundary limits without asserting this trichotomy there.

The original alternative (11.1) remains unresolved. Compact anchors do
not give a point of $D_J\cap D_M$, an exhaustive exclusion of that
set, closedness or properness of a collision projection, or a constant
$\varepsilon$ independent of $P$. Mixed boundary/interior incidence,
the augmented interior critical loci and their actual strict-pair
limits, unbounded real $p$, and all exceptional real-lift and
within-pair-distinctness obligations remain. No singular $J$ endpoint,
unused singular companion, zero drift, lower degree, sampled or repeated
root, or nonsingular exceptional reconstruction stratum is removed.
The same-fifth-response sixth-$J$ child and all ancestor conjunctions
of O, Theorem 17.1, also remain as stated in Definition 11.2.

**Assumption 16.3 (Classical tools and their exact domains).** The
inverse-function theorem is used only for an analytic map from a
specified two-dimensional chart with a displayed nonzero minor:
(13.1)–(13.2), (13.16)–(13.18), or the strict off-$24$ parent in
Theorem 16.1. The analytic implicit-function theorem and references
in Assumption 11.1 supply these classical local tools. Taylor's integral
formula is used on the single neighbourhood of the compact rectangle
(13.4), with derivatives justified in (13.11); see the Taylor theorem
reference in Assumption 11.1. The lower-corner injectivity itself is
the convex-segment estimate (13.15). Compactness in Sections 14–16
is closed bounded finite-dimensional compactness, applied to padded
whole gain coefficients and source entries with all original reading
equations imposed. The distinction between strict pairs and diagonal
limits agrees with the multiple-point-space distinction cited in
Assumption 11.1; no additional holomorphic hypothesis or conclusion
is transferred. The source-specific fractions, localized ideals,
transverse minors and corner jets are the explicit calculations above.

## 追加锚（本行以下为增补区）
