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

## 17. Zero-safe equations for lower-face mixed incidence

**Definition 17.1 (The lower auxiliary face and its actual companions).**
All strict worlds, clocks, histories, terminal functions and entire children
remain those of Definitions 1.1–1.2. In particular $c=r(1-r)/b$,
$0<r<1$, $b>0$, $d$ is fixed in each world, and its one nonzero whole
real polynomial has degree at most three. Write $L(t)=B_0(t)$ for the
auxiliary complete boundary label in Definition 12.1 with

$$
(r,b,c)=(0,0,t),\qquad t>0,\quad t\ne1.
$$

For this section only put

$$
\begin{gathered}
q=10(t-1),\quad P=-48t^2+240t-195,\\
V=135t^2+375t-516,\qquad M_t=1152t^2+813t-1977,\\
p_L=P/q,\quad v_L=V/q,\quad m_L=M_t/q,\quad
 a_L=3(384t^2-113t-273)/q.
\end{gathered}
\tag{17.1}
$$

The symbol $M_t$ is a polynomial, whereas the action $M$ is unchanged.
These are precisely the $B_0$ fractions of Lemma 12.2, equivalently
S, Theorem 13.1. Its drift is $24+3t/[10(t-1)]$ and its one whole gain
is interpolated at $0,1,2,3$ from

$$
(-24-e,-e/t,27/5-e,-e/t),\qquad e=3t/[10(t-1)].
\tag{17.2}
$$

The label is a limit, never a strict world. The relation to classify is

$$
\mathcal L_M=\{(t,W):t>0, t\ne1, p_L(t)\ne24,
 W\in C(p_L(t),v_L(t)), m(W)=m_L(t)\}.
\tag{17.3}
$$

There is no upper bound on $t$, and no compactness assumption on this
rational curve or its pole approaches.

**Definition 17.2 (A uniform rank equation).** Reuse exactly $D,z_i,a_i,f,K$
of (5.1), and set

$$
\begin{gathered}
a_7=-z_3+4z_4-6z_5+4z_6,\quad z=xa_1-D(24-d),\\
b_*=(294-10d)D-5a_2,\\
A_*=4z^2-2za_1+(2x-1)a_1^2,\quad
B_*=-2za_1+2(1-x)a_1^2,\\
\mathcal Q(u,w)=A_*u^2+B_*uw-a_1^2w^2,\qquad
K_{\rm s}=25K+\mathcal Q(5a_2,b_*).
\end{gathered}
\tag{17.4}
$$

Here $\mathcal Q(-a_0,dD)=K$, identically. The asterisked polynomial
$B_*$ in (17.4) is unrelated to the finite source cap in Assumption 14.1.
Write $H_i=a_i/D$ for $i=0,1,2,7$, and use $B_0,C_0,U,b,j,r$
from (5.5). The terminal functions of that same reconstructed world are

$$
\begin{aligned}
m&=d+(2x+3)a_7/D,\\
a&=d+\left(4x+\frac12+\frac1{2U}
                   -\frac{2(24-d)}{H_1}\right)a_7/D.
\end{aligned}
\tag{17.5}
$$

**Lemma 17.3 (Faithful use of the uniform equation).** For real $p\ne24,v$,
the full actual $C(p,v)$ is in bijection with the solutions of

$$
f=K_{\rm s}=0,\qquad
x>0,\quad d\ne24,\quad H_1\ne0,\quad C_0>0,\quad U>1,\quad0<r<1.
\tag{17.6}
$$

The complete world is reconstructed by (5.5), $c=r(1-r)/b$, and
$g=H/U$, with the single interpolant $H$ at the original nodes $3,4,5,6$
in Assumption 5.3. No division by $d,H_0,H_7,F_0$, a leading gain
coefficient or a discriminant is part of (17.6).

Proof. This is an algebraic form of F, Lemma 30.2, recalled in
Assumption 5.3. Indeed

$$
f=5D^2(dH_2+H_0B_0).
$$

When $C_0>0$, $f=0$ makes $(-H_0,H_2)$ parallel to $(d,B_0)$.
Its projection gives the value of $U$ in (5.5) and both equations
$dU=-H_0$, $B_0U=H_2$. Put

$$
S_r=r^2-(1+b)r+b(xU-b),\qquad c_*=25d^2D^2+b_*^2=25D^2C_0.
$$

The definitions of $r,j,b$ give, by expansion,
$\mathcal Q(U,1)=4a_1^2S_r$. The two clock equations give
$-a_0=dDU$ and $5a_2=b_*U$, whence

$$
K_{\rm s}=c_*\mathcal Q(U,1)=4c_*a_1^2S_r.
\tag{17.7}
$$

Thus, under the guards, $K_{\rm s}=0$ is exactly the rank-one source
identity $j=b+r(1-r)/b$. F, Lemma 30.2, now gives both directions,
all original readings and uniqueness of the entire world. Its gain
cannot vanish identically because the original readings $0,24$ differ.
The second terminal formula follows from
$(T+2j+4r)/U=4x+1/2+1/(2U)-2j/U$ and $j/U=(24-d)/H_1$.
In particular zero drift is included in this argument. ∎

**Definition 17.4 (The terminal-affine companion equations).** Put

$$
\begin{gathered}
\lambda(x)=-8x^4-29x^3-18x^2+15x+6,\\
N(x;p,v,m)=(2x+3)a_7(x,0,p,v)-mD,\\
F_M=\lambda^2 f(x,-N/\lambda,p,v)/D^2,\qquad
G_M=\lambda^4 K_{\rm s}(x,-N/\lambda,p,v)/D^4.
\end{gathered}
\tag{17.8}
$$

The letter $\lambda(x)$ here denotes the terminal drift slope; it is
not the fold constant in (9.3). The terminal equation is exactly
$\lambda d+N=0$. Both $F_M,G_M$ are polynomials: the divisions in
(17.8) have zero remainder after homogeneous substitution. Define

$$
\begin{aligned}
F(x,t)&=\frac{q^2F_M(x;P/q,V/q,M_t/q)}{90(x-t)},\\
G(x,t)&=\frac{q^4G_M(x;P/q,V/q,M_t/q)}{8100(x-t)}.
\end{aligned}
\tag{17.9}
$$

These are integer polynomials of coordinate degrees $(\deg_x,\deg_t)$
$(6,3)$ and $(13,7)$. Equations (5.1), (17.4), (17.8)–(17.9)
are algorithmic definitions of every coefficient. Equivalently set
$L=q\lambda$, $\nu=-qN(x;P/q,V/q,M_t/q)$ and substitute $d=\nu/L$
in $L^2f/[90D^2(x-t)]$ and $L^4K_{\rm s}/[8100D^4(x-t)]$.
Each indicated polynomial division has zero remainder.

If an actual companion has $x=t$ and $\lambda(t)\ne0$, the terminal
equation gives $d=24+3t/[10(t-1)]$. Reconstruction gives $U=1$,
the auxiliary face itself, violating (17.6). Thus dividing out $x-t$
removes no strict companion in the $\lambda\ne0$ sector. The entire
$\lambda=0$ sector is treated in Lemma 19.1.

## 18. Exact elimination and subresultant units

**Definition 18.1 (Coefficient and determinant conventions).** A descending
list $(a_d,\ldots,a_0)$ specifies $\sum_{i=0}^d a_i t^i$.
For a nonzero rational polynomial $h$, $\operatorname{pp}(h)$ clears
denominators, removes positive integer content, and chooses positive
leading coefficient. The resultant of degrees $d,e$ uses rows
$t^{e-1}h,\ldots,h,t^{d-1}k,\ldots,k$, with descending coefficient
columns. For $F,G$ of $x$ degrees $6,13$, respectively, define $S_j$
for $j=1,2$ as follows. Use rows

$$
x^{5-j}G,\ldots,G,\quad x^{12-j}F,\ldots,F,
\qquad n_j=19-2j.
$$

For $0\le i\le j$, take the $n_j$ by $n_j$ coefficient matrix whose
first $n_j-1$ columns are $x^{18-j},\ldots,x^{j+1}$ and whose last
column is $x^i$. Its determinant is $s_{j,i}$; put
$S_j=\sum_{i=0}^j s_{j,i}x^i$. A common finite root annihilates $S_j$.
The determinant subresultant criterion says that preserved degrees,
zero resultant and nonzero linear $S_1$ give a degree-one gcd, whose
root is the unique common finite root. This follows also by ordinary
polynomial row elimination on the displayed coefficient matrices.

**Lemma 18.2 (Complete factorization and degree-preserving units).** The
four integer polynomials used in the factorization are the following.

$$
\operatorname{coeff}_{\downarrow}(Q_{4\ell})=\bigl(
8,
29,
18,
-15,
-6
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(Q_{4e})=\bigl(
1561361616,
-6013487520,
8677301265,
-5559718700,
1334543691
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(Q_{10})=\bigl(
4861042409741225600,
-47756762588832747920,
579939925876114599409,
-1628025238366216881120,
2346419680298287360766,
-5408314435974028938334,
17109455218395558595400,
-33480234355949654381792,
36126151495662229435888,
-20148480242449265968214,
4545984222735301909597
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(Q_{27})=\bigl(
1334027503831187016595025759862764912524811806629747144096768,
-18717709455628897786698125599977594521377696363300307439733536,
115076249557407927271664211389710033825567403033558899275712704,
-397543368503139176278806283819486441742852101388159036972942820,
793372796018276082772677663530968073511815868848288980173285237,
-688419667392011573225741886083409559366446957717666385998840083,
-741433241819035647621251899730842414992007185859648103114191220,
3012382096759818006284250447371048607025175786545841146667846354,
-3575368750491378256467049125974203060944016330738039875861868204,
495305570043479277266044672799568681023174589295797458662560314,
3758193684764767264967572596555045362309319627230746160830249374,
-4107731537458892633813832666745042217648382316726802435606432070,
204050536338145991017153962131302458469341826641212770168527432,
1756516145201828393750641371693101005382709013931013692263352270,
1754086361541444583723574253770332326578534230834585277684617596,
-4932243315605239719257576526795352853614778749110925883195970680,
1306654081142371562148683200873871742954532300156772167274620607,
5281501696431758905885717810641209029471385952333189998645596999,
-6278790282499525750695446749313916965242498237490808093798024850,
1306072007206429624124291241382710780723246242289459907876242160,
2677973566324562554868682580880488868614421993464346476175637997,
-2143270894146628101603230955605060423610650396165743964728723221,
-173472136937457594111772125235175742390063619298000517181899908,
1189693817701878581680225488886706153058983018770636192004826814,
-846492568480000414500168235983319259447807114345404586354118645,
305447370645344830966410010417835039919737307114854971178582241,
-59074801591012821245993839060637415586546591348442999665216536,
4898267198605812863383893862109668208075770098725872640375610
\bigr).
$$

They satisfy the exact identity

$$
\operatorname{Res}_x(F,G)
=-516096\,Q_{4\ell}^3Q_{4e}^8Q_{10}Q_{27}.
\tag{18.1}
$$

The four factors are pairwise coprime over $\mathbb Q$, and
$Q_{27}(1)\ne0$. Write $S_1=\alpha(t)x+\beta(t)$. Its coefficient
gcd is $1024Q_{4e}^3$, and

$$
A=\alpha/(1024Q_{4e}^3),\quad
B=\beta/(1024Q_{4e}^3),\qquad
\deg\alpha=\deg\beta=71,\quad\deg A=\deg B=59.
\tag{18.2}
$$

The following table supplies unit certificates. A row $(H,h;d,e;u)$
means that $\operatorname{pp}(H),\operatorname{pp}(h)$ have degrees
$d,e$ both over $\mathbb Q$ and after reduction modulo $101$, and
that their Sylvester resultant is $u\ne0$ modulo $101$.

| $H$ | $h$ | $(d,e)$ | $u$ |
| --- | --- | --- | --- |
| $Q_{27}$ | $\alpha$ | $(27,71)$ | $63$ |
| $Q_{27}$ | $A$ | $(27,59)$ | $2$ |
| $Q_{27}$ | $[x^6]F$ | $(27,3)$ | $21$ |
| $Q_{27}$ | $[x^{13}]G$ | $(27,6)$ | $9$ |
| $Q_{4\ell}$ | $\alpha$ | $(4,71)$ | $87$ |
| $Q_{4e}$ | $h_2$ | $(4,3)$ | $73$ |

For $S_2$ reduce each coefficient modulo $Q_{4e}$ and write
$h_2x^2+h_1x+h_0$. The exact remainder identities are

$$
\begin{gathered}
\beta+t\alpha\equiv0\pmod{Q_{4\ell}},\\
h_1^2-4h_2h_0\equiv0\pmod{Q_{4e}},\\
\sum_{i=0}^4[x^i]\lambda\,(-h_1)^i(2h_2)^{4-i}
\equiv0\pmod{Q_{4e}}.
\end{gathered}
\tag{18.3}
$$

Proof. Expand the circuits of Definition 17.4 over $\mathbb Z[x,t]$,
perform the two exact divisions, and take the fixed determinants of
Definition 18.1. Their determinant gives (18.1). The same minors give
(18.2); rational polynomial division gives (18.3). For each unit row,
clear content before reducing the two polynomials modulo $101$, form
the degree-preserving Sylvester matrix, and eliminate over
$\mathbb F_{101}$. Its determinant is the displayed residue. Nonzero
residue proves the integer resultant nonzero, so $h$ vanishes at no
complex root of $H$. Pairwise Euclidean gcds of the four displayed
factors are $1$. All inputs, normalizations and operations for these
finite integer identities have been specified above. ∎

**Lemma 18.3 (Exhaustion when the terminal slope is nonzero).** Every
strict companion in (17.3) with $\lambda(x)\ne0$ must have $Q_{27}(t)=0$.
At every real root $t$ of $Q_{27}$ the finite common root of $F,G$
exists, is unique, and is $x=-B(t)/A(t)$.

Proof. The self case $x=t$ is excluded in Definition 17.4. Every other
companion gives $F=G=0$ and hence a zero of (18.1). If
$Q_{4\ell}(t)=0$, the nonzero linear subresultant and (18.3) force
$x=t$, already excluded. If $Q_{4e}(t)=0$, $h_2$ is a unit,
and (18.3) makes $S_2$ a nonzero quadratic with its unique double
root $-h_1/(2h_2)$. Every common root must equal this root, and the
last identity of (18.3) gives $\lambda(x)=0$, contrary to this case.
Lemma 19.2 excludes positive roots of $Q_{10}$.

At a root of $Q_{27}$ the leading coefficients of $F,G$ and $\alpha$
are nonzero by the unit table. The degrees remain $6,13$, the
resultant vanishes, and $S_1$ is nonzero linear. The determinant
subresultant criterion therefore gives a degree-one gcd, proving both
existence and uniqueness of the common root $-\beta/\alpha=-B/A$.
This proves a finite common-root lift of the polynomial equations;
the additional real-world guards are still required. ∎

## 19. The terminal-slope pole, real-root exhaustion and strict lifts

**Lemma 19.1 (No strict companion at zero terminal slope).** No element
of $\mathcal L_M$ has $\lambda(x)=0$.

Proof. Work in $\mathbb Q[x]/(\lambda)$, always using the unique
remainder of $x$ degree less than four. Set

$$
n_\ell=504x^3+1260x^2+1044x,\qquad
n_r=-480x^3-1149x^2-921x+18.
$$

Direct reduction of $qN$ gives

$$
qN\equiv(t-x)(n_\ell t+n_r)\pmod\lambda.
\tag{19.1}
$$

For $x>0$, $n_\ell>0$. Since $q\ne0$, every actual pole-sector
solution has either $t=x$ or $t=-n_r/n_\ell$. Neither branch is dropped.
Reduce the $d$ coefficients of
$f_q=q^2f(x,d,P/q,V/q)$ and $K_q=q^4K_{\rm s}(x,d,P/q,V/q)$
modulo $\lambda$, and write

$$
f_q=A_2d^2+B_2d+C_2,\qquad K_q=\sum_{i=0}^4G_id^i.
$$

Define in this quotient ring

$$
\begin{aligned}
\alpha_p={}&G_4(-B_2^3+2A_2B_2C_2)
 +G_3A_2(B_2^2-A_2C_2)-G_2A_2^2B_2+G_1A_2^3,\\
\beta_p={}&G_4(-B_2^2C_2+A_2C_2^2)
 +G_3A_2B_2C_2-G_2A_2^2C_2+G_0A_2^3,\\
Z={}&\operatorname{rem}_x
 (A_2\beta_p^2-B_2\alpha_p\beta_p+C_2\alpha_p^2,\lambda).
\end{aligned}
\tag{19.2}
$$

Pseudo-division gives $f_q\mid A_2^3K_q-(\alpha_pd+\beta_p)$.
At any simultaneous root, $\alpha_pd+\beta_p=0$, and substitution
into the quadratic shows $Z=0$, even if $A_2$ or $\alpha_p$ vanishes.
Thus no division by a leading drift coefficient was assumed.

The coordinate degrees of $Z$ in $(x,t)$ are $(3,30)$. Evaluate $Z$
at $t=-n_r/n_\ell$ by Horner operations in the quotient ring. The
result $Z_{\rm alt}$ has all four coefficients strictly negative.
The descending coefficients of $\operatorname{pp}(Z_{\rm alt})$ are
as follows; the sign of the actual remainder is negative.

$$
\operatorname{coeff}_{\downarrow}(Z_+)=\bigl(
12319622927537099033683278525987522082353266819117556188238166550172030929962425483194981590815124163983913495612385242678707326000232559597495825068731965435367028774927271910879852175121444127038093015722671202336034300994106461823163296265952533,
52362367952813978015563261902939797407783261786947023167226044422692477234608634367950576708039111768522733685378789532710269653568560398301814533947334763799091113748303405466037268373392175282209634559450817783804804995474213158591064647689657978,
60483181752943077656912163158603419015953282014783518562933588693348999912225420380466601163560342573217164409017080574891226488106137653739607036098779757213968741234182150569206573600686853463346755153118905329597066934086964787688059905247958409,
14759658962767195646132587368953316943947758245568431411080782911574414107310271502133095176019138983651144960406379151268238178306165398186139788174685980446368758295150242825952944694126104520430398236175622549582194584921534166047400439471906314
\bigr).
$$

Thus $Z_{\rm alt}=-\kappa Z_+$ for one positive rational $\kappa$,
so it is strictly negative for every positive $x$. This excludes the
alternative branch.

For $t=x$, $\alpha_p$ is a unit modulo $\lambda$, and the exact
identity is

$$
\beta_p+\alpha_p\left(24+\frac{3x}{10(x-1)}\right)
\equiv0\pmod\lambda.
\tag{19.3}
$$

The monic common drift factor on this branch is equivalently

$$
d+\frac{6x^3}{85}+\frac{111x^2}{340}
  +\frac{33x}{68}-\frac{4071}{170}.
\tag{19.4}
$$

The unit certificates below have the degree and residue convention of
Lemma 18.2, now in the variable $x$. They also justify the inverses
in the quotient-ring evaluation.

| First polynomial | Second polynomial | Degrees over $\mathbb Q$ and $\mathbb F_{101}$ | Resultant modulo $101$ |
| --- | --- | --- | --- |
| $\lambda$ | $n_\ell$ | $(4,3)$ | $23$ |
| $\lambda$ | $x-1$ | $(4,1)$ | $34$ |
| $\lambda$ | $\alpha_p(x,x)$ | $(4,3)$ | $86$ |

All these entries follow from (19.1)–(19.2) by rational remainders,
primitive parts and the same Sylvester determinant rule. In particular
(19.3) forces the boundary drift on the self branch. Substitution in
(5.5) gives $U=1$, contradicting (17.6). This excludes that branch
and exhausts the pole sector. ∎

**Lemma 19.2 (All positive roots and exact brackets).** $Q_{10}$ has
no positive real root. $Q_{27}$ has exactly ten positive real roots,
all simple; write them in increasing order as $t_1,\ldots,t_{10}$.
For reproducibility use the ordinary Sturm chain
$S_0=Q,S_1=Q',S_{i+1}=-\operatorname{rem}(S_{i-1},S_i)$ until
constant, allowing only positive rescalings of its entries. Its exact
sign and variation certificates are:

| $Q_{10}$ | Signs | Variations |
| --- | --- | --- |
| $0$ | $(+,-,-,+,+,-,-,+,+,-,-)$ | 5 |
| $+\infty$ | $(+,+,-,-,+,+,-,-,+,+,-)$ | 5 |

| $Q_{27}$ | Signs | Variations |
| --- | --- | --- |
| $0$ | $(+,-,-,+,+,-,-,+,-,+,+,+,-,+,+,+,-,+,-,+,-,-,+,-,+,-,-,+)$ | 18 |
| $+\infty$ | $(+,+,+,+,-,-,-,+,+,-,+,+,-,-,+,+,+,+,+,+,+,-,-,-,-,-,+,+)$ | 8 |

The following integer $c_i$ specifies the open bracket
$I_i=((c_i-1)/10^{95},(c_i+1)/10^{95})$. The last column gives
$\operatorname{sgn}Q_{27}$ at its left and right endpoints.

| $i$ | $c_i$ | Endpoint signs |
| --- | --- | --- |
| 1 | 76505995352160688509469772646881017481041149762762933298308854275662749615613848948454851632735 | $(1,-1)$ |
| 2 | 83697985732238599375160730366593772885820553102707690535970274323124341964823633134484669382555 | $(-1,1)$ |
| 3 | 89680369655244537276490927042787265723608794422005836283630517082102631909285176895662501033582 | $(1,-1)$ |
| 4 | 94022880328740730515370331885322688445062979672738034163232363536347942492519397436812639394805 | $(-1,1)$ |
| 5 | 99728924757391346684825572393260169127045671355254888814019089727073009127577859338917411844520 | $(1,-1)$ |
| 6 | 99955292152822208657149138390552998376176811159812601345977607458991362513227641301160434464531 | $(-1,1)$ |
| 7 | 101448478149413324858135570886774705443392948091690984311899395612288064692175019321695332052322 | $(1,-1)$ |
| 8 | 101651805482088270123218601586557595064864894343417781221150658469954379849176870616147772895663 | $(-1,1)$ |
| 9 | 102847080733487775318337234387164023770866742076473540291824548398272570702114327044177620939712 | $(1,-1)$ |
| 10 | 241991416623725834367929362747969593017100018988154065497487490682831100007618740872281162519708 | $(-1,1)$ |

Proof. Exact Euclidean division gives the displayed Sturm signs.
The variation differences are $0$ and $10$. The chain terminates in
a nonzero constant, so the polynomial has no repeated root. Integer
Horner evaluation at the two rational endpoints gives the signs in
the bracket table. The ten brackets are positive, disjoint, ordered
as listed and avoid $1$. Their sign changes and the total Sturm
count place exactly one root in each, exhausting all positive roots. ∎

**Lemma 19.3 (Guard-filter certificates).** For each $t_i\in I_i$ set

$$
x_i=-B(t_i)/A(t_i),\qquad
d_i=-N(x_i;P(t_i)/q(t_i),V(t_i)/q(t_i),M_t(t_i)/q(t_i))/\lambda(x_i).
\tag{19.5}
$$

Apply (5.5) to these exact algebraic values. In each of the following
tables an entry $[l,u]$ denotes the closed rational enclosure
$[l/10^9,u/10^9]$, including in columns with large integers.

| $i$ | $x$ | $d$ | $U$ | $b$ | $r$ |
| --- | --- | --- | --- | --- | --- |
| 1 | $[615053677,615053678]$ | $[4858575109,4858575110]$ | $[-14745264255,-14745264254]$ | $[-7872632128,-7872632127]$ | $[-4981854261,-4981854260]$ |
| 2 | $[616575752,616575753]$ | $[4319785444,4319785445]$ | $[-16203715857,-16203715856]$ | $[-8601857929,-8601857928]$ | $[-5381884745,-5381884744]$ |
| 3 | $[321773588,321773589]$ | $[22802203725,22802203726]$ | $[1941128014,1941128015]$ | $[470564007,470564008]$ | $[1419499861,1419499862]$ |
| 4 | $[-206044985,-206044984]$ | $[24977387328,24977387329]$ | $[4080934062,4080934063]$ | $[1540467031,1540467032]$ | $[-1027992496,-1027992495]$ |
| 5 | $[1206618531,1206618532]$ | $[-46729101442,-46729101441]$ | $[547101591,547101592]$ | $[-226449205,-226449204]$ | $[-205139537,-205139536]$ |
| 6 | $[991684316,991684317]$ | $[-661260652530,-661260652529]$ | $[1033078679,1033078680]$ | $[16539339,16539340]$ | $[16673032,16673033]$ |
| 7 | $[2269387036,2269387037]$ | $[25455117944,25455117945]$ | $[895149389,895149390]$ | $[-52425306,-52425305]$ | $[1051473895,1051473896]$ |
| 8 | $[2282060617,2282060618]$ | $[24916668846,24916668847]$ | $[816864148,816864149]$ | $[-91567926,-91567925]$ | $[-166583232,-166583231]$ |
| 9 | $[2681008729,2681008730]$ | $[22615182283,22615182284]$ | $[530502594,530502595]$ | $[-234748703,-234748702]$ | $[1114327920,1114327921]$ |
| 10 | $[2377764520,2377764521]$ | $[24614429363,24614429364]$ | $[1024053499,1024053500]$ | $[12026749,12026750]$ | $[982363610,982363611]$ |

| $i$ | $H_1$ | $C_0$ | $\lambda$ | $a$ | $H_7$ |
| --- | --- | --- | --- | --- | --- |
| 1 | $[69054660081,69054660082]$ | $[36357019497,36357019498]$ | $[524324565,524324566]$ | $[164599750429,164599750430]$ | $[67346758291,67346758292]$ |
| 2 | $[69190106689,69190106690]$ | $[29545410043,29545410044]$ | $[451820110,451820111]$ | $[169778996294,169778996295]$ | $[69915132324,69915132325]$ |
| 3 | $[-2925005928,-2925005927]$ | $[540069853410,540069853411]$ | $[7910993843,7910993844]$ | $[249659936570,249659936571]$ | $[79218929126,79218929127]$ |
| 4 | $[-21314138320,-21314138319]$ | $[626900492159,626900492160]$ | $[2384403269,2384403270]$ | $[-9021513820,-9021513819]$ | $[115890246160,115890246161]$ |
| 5 | $[44720661707,44720661708]$ | $[11869146560881,11869146560882]$ | $[-70010999663,-70010999662]$ | $[408495903888,408495903889]$ | $[147933358872,147933358873]$ |
| 6 | $[702438688041,702438688042]$ | $[898881858114241,898881858114242]$ | $[-32846349328,-32846349327]$ | $[1539997017819,1539997017820]$ | $[733841298650,733841298651]$ |
| 7 | $[-1329175954,-1329175953]$ | $[665294728581,665294728582]$ | $[-603791682190,-603791682189]$ | $[241616939461,241616939462]$ | $[27201764563,27201764564]$ |
| 8 | $[-368733810,-368733809]$ | $[645196989443,645196989444]$ | $[-615129991144,-615129991143]$ | $[175385933505,175385933506]$ | $[28560942527,28560942528]$ |
| 9 | $[2385580293,2385580294]$ | $[590054736235,590054736236]$ | $[-1055328746572,-1055328746571]$ | $[351933603784,351933603785]$ | $[29922948618,29922948619]$ |
| 10 | $[-433161873,-433161872]$ | $[628230734198,628230734199]$ | $[-705677947449,-705677947448]$ | $[469025460901,469025460902]$ | $[57999210460,57999210461]$ |

| $i$ | $t$ | $p$ | $v$ |
| --- | --- | --- | --- |
| 1 | $[765059953,765059954]$ | $[16804633737,16804633738]$ | $[63882152401,63882152402]$ |
| 2 | $[836979857,836979858]$ | $[17022760072,17022760073]$ | $[65979754848,65979754849]$ |
| 3 | $[896803696,896803697]$ | $[17802423130,17802423131]$ | $[68921011651,68921011652]$ |
| 4 | $[940228803,940228804]$ | $[19706041672,19706041673]$ | $[73731368701,73731368702]$ |
| 5 | $[997289247,997289248]$ | $[125083391212,125083391213]$ | $[285804164044,285804164045]$ |
| 6 | $[999552921,999552922]$ | $[685425286068,685425286069]$ | $[1406540244624,1406540244625]$ |
| 7 | $[1014484781,1014484782]$ | $[-6380919811,-6380919810]$ | $[23272758832,23272758833]$ |
| 8 | $[1016518054,1016518055]$ | $[-3841231472,-3841231471]$ | $[28399104123,28399104124]$ |
| 9 | $[1028470807,1028470808]$ | $[3726231132,3726231133]$ | $[43810137913,43810137914]$ |
| 10 | $[2419914166,2419914167]$ | $[7373131625,7373131626]$ | $[83246280490,83246280491]$ |

The exact interval rule for these tables is closed rational arithmetic:
round each elementary lower and upper endpoint outward to
$10^{-200}\mathbb Z$; multiply using all four endpoint products;
invert only intervals excluding zero. Form interval powers by repeated
multiplication. For expanded polynomial coefficients sum monomials in
descending lexicographic order; for univariate substitution use descending
Horner evaluation. Evaluate the determinant-defined $A,B$ from
(18.2) on $I_i$, then (19.5), then (5.5) and (17.5). The table is
an outward enclosure, rather than a substitution of rounded centres.

Proof. The nonzero denominator bounds in the tables and Lemma 18.2
justify every indicated interval inversion. Rational evaluation by
the specified rule gives the displayed enclosures. In order, the
strict failures for $i=1,\ldots,10$ are

$$
U<1, U<1, r>1, x<0, U<1,
\text{all guards hold}, U<1, U<1, U<1, \text{all guards hold}.
\tag{19.6}
$$

For $i=6,10$, $x>0$, $d\ne24$, $H_1\ne0$, $C_0>0$,
$U>1$, $0<r<1$, $\lambda\ne0$ and $p\ne24$ all have strict
rational margins. The $t$ and $x$ columns also separate $t_i$ from
$x_i$ for both survivors. No condition on the exact degree or sampled
roots of the whole gain enters this filter. ∎

**Theorem 19.4 (L1: complete strict lower-face classification).** The
entire relation (17.3) is exactly

$$
\mathcal L_M=\{(t_6,W_6),(t_{10},W_{10})\}.
\tag{19.7}
$$

Here $x_i,d_i$ are the exact algebraic expressions (19.5),
$r_i,b_i,U_i$ are reconstructed by (5.5), and

$$
\begin{gathered}
c_i=r_i(1-r_i)/b_i,\qquad
h_3=(24-d_i)/x_i,\quad h_4=18-d_i,\\
h_5=(p_L(t_i)-d_i)/(x_i+1),\quad
h_6=(v_L(t_i)-d_i)/(x_i+2),\\
g_i(s)=\frac1{U_i}\sum_{k=3}^6h_k
       \prod_{\substack{3\le l\le6\\l\ne k}}\frac{s-l}{k-l},
\qquad W_i=(P(r_i,b_i),g_i,d_i).
\end{gathered}
\tag{19.8}
$$

In particular each displayed world uses the same polynomial and drift
at every original clock $0,\ldots,7$.

Proof. Every actual companion has either nonzero terminal slope,
covered by Lemma 18.3, or zero slope, excluded by Lemma 19.1.
The ten roots of Lemma 19.2 and the guard filter leave only $6,10$.
Conversely at either surviving root the subresultant criterion proves
$F=G=0$. Since $q,D,\lambda,x-t$ are nonzero there, undoing
(17.9)–(17.8) proves $f=K_{\rm s}=0$ and the exact terminal
identity. Every guard in (17.6) holds by Lemma 19.3. Lemma 17.3
therefore gives the actual complete world (19.8), all original
readings and $m=m_L$. Its injectivity makes that world unique.
The classification has quantified over all finite $t>0$, $t\ne1$
with $p_L\ne24$, not merely the bracketed region: the brackets
exhaust the positive eliminant roots and all other factors and poles
were treated separately. ∎

## 20. Open whole-child terminal-J exclusion at both survivor bases

**Definition 20.1 (Two rational base rectangles).** For $i=6,10$ let
$(p_i,v_i)=(p_L(t_i),v_L(t_i))$. Put $D_b=10^{75}$ and use the
following integer centres $(u_i,w_i)$:

| $i$ | $u_i$ | $w_i$ |
| --- | --- | --- |
| 6 | 685425286068780686189702527301251594300764701605323009028090840309515317000521 | 1406540244624863302579206505570720931226426246588562728967102507942057638741597 |
| 10 | 7373131625307828814294109720471027276746788662069168217247458139271996610295 | 83246280490696325367579902235723030540443681710401925564414526626277977322350 |

Define

$$
\mathcal B_i=\{(p,v):|p-u_i/D_b|<2/D_b, |v-w_i/D_b|<2/D_b\}.
\tag{20.1}
$$

These are open rectangles contained in $p\ne24$. Evaluation of
(17.1) on $I_i$, using the rational rule in Lemma 19.3, gives the
strict inequalities $(p_i,v_i)\in\mathcal B_i$. All uniform bounds
below are valid on the corresponding closed rectangles as well.

**Definition 20.2 (The exact degree-eighteen disc certificates).** Use
exactly the $R$ of (5.2), with its $512$ terms and coordinate degrees
$(18,6,6)$. Thus its coefficient circuit is the fixed determinant

$$
R=\operatorname{Res}_d(f,K)/(256D^8F_0^2).
\tag{20.2}
$$

This is a polynomial identity with zero division remainder, not a
pointwise cancellation at $F_0=0$. Its all-actual-world necessity is
S, Theorem 4.1, with the same $x=(j+r)/U,p,v$ correspondence as
Assumption 5.3. In particular it applies before excluding any singular
or otherwise exceptional world.

Each row below supplies integers $u,w$ for the exact centre
$\xi=(u+\mathrm i w)/10^{45}$ and an integer $h$. Its disc is
$|x-\xi|<\rho$, $\rho=10^{-35}$. There are eighteen rows for
each base rectangle.

| Disc in $\mathcal B_{6}$ | $u$ | $w$ | $h$ |
| --- | --- | --- | --- |
| 1 | -11328024704556795669075257004276744123671748017 | 0 | 29974070142 |
| 2 | -10296309727424036417573651872187560048892444245 | 0 | 636442294326 |
| 3 | -8632648863989778687330020286948967169472063748 | 0 | 10970165923 |
| 4 | -7507577006134771828458222941875014959702372377 | 0 | 21398716357 |
| 5 | -3942710319905009814706608503860445987331653407 | 0 | 89315349329 |
| 6 | -3926585254369346723036814919521247903015696429 | 0 | 23757117940 |
| 7 | -2583794404812496981785225349592912647117658936 | 0 | 76417586133 |
| 8 | -413870447709520369729653397808193186287846962 | 0 | 11699678129 |
| 9 | 344936877728394109592560685447350263893488831 | 0 | 16911784094 |
| 10 | 397297877440957595394886795956721757718952082 | 0 | 10485595776 |
| 11 | 991684316612358118424490218836921950629169482 | 0 | 89945296690 |
| 12 | 999552921528222086571491383905529983761768111 | 0 | 16718884942 |
| 13 | 2235198431991486182631475801127368994570788478 | 0 | 35494124691 |
| 14 | 3157799982071252384280962858079227275600551616 | 0 | 17473893983 |
| 15 | -51297464647625859275025754122130842582506642359 | -638239445004375795122078404379756751549637499 | 11200400847 |
| 16 | -51297464647625859275025754122130842582506642359 | 638239445004375795122078404379756751549637498 | 11286164239 |
| 17 | 729284480812076229218360208580712663387601232 | -111593587351107688618618315585022040077948236 | 8788937633 |
| 18 | 729284480812076229218360208580712663387601232 | 111593587351107688618618315585022040077948235 | 5567596864 |

| Disc in $\mathcal B_{10}$ | $u$ | $w$ | $h$ |
| --- | --- | --- | --- |
| 1 | -1663311206210997567028062877710534702132487849 | 0 | 12014217914 |
| 2 | -1529658272600869524639338236999839755617268058 | 0 | 34915297633 |
| 3 | -1526223135771408780515089252454905876665908424 | 0 | 10907074525 |
| 4 | -1336359175947181442460178561383314338954859482 | 0 | 23224026950 |
| 5 | -1252942939950621780273117864972455033429683409 | 0 | 10436856377 |
| 6 | -1204125606578887697417748606627489432784262042 | 0 | 91350877006 |
| 7 | -376267138582013192277447222473200111064148460 | 0 | 40378942578 |
| 8 | 340302907706220774952091713761183708564977429 | 0 | 19073814924 |
| 9 | 530132537517198960567248344034114239516154975 | 0 | 10446559029 |
| 10 | 943249412303874718215822010962046986685206440 | 0 | 14101627500 |
| 11 | 953208222972626421739282819432191055035967394 | 0 | 19397848609 |
| 12 | 1100600016349823037617370077481970761434825598 | 0 | 44863186176 |
| 13 | 1202847061183560232953114456022468591701505268 | 0 | 74879257607 |
| 14 | 2377764520473090697884503530593035914513766653 | 0 | 14010772631 |
| 15 | 2419914166237258343679293627479695930171000189 | 0 | 11343776312 |
| 16 | 43306187499468032274347304706801679753092263286 | 0 | 23141400978 |
| 17 | 683309840665318296652194434486646539807518200 | -98573392127001109805896498110183720288783923 | 10975144715 |
| 18 | 683309840665318296652194434486646539807518200 | 98573392127001109805896498110183720288783922 | 6602603284 |

Here is the exact inequality specified by $h$. Write $R=\sum_{j=0}^{18}r_jx^j$
and, uniformly over the closed base rectangle, form

$$
T_k=\rho^k\sum_{j=k}^{18}\binom jk r_j\xi^{j-k},\qquad
R(\xi+\rho z)=\sum_{k=0}^{18}T_kz^k.
\tag{20.3}
$$

Use the rational interval rule of Lemma 19.3 for real and imaginary
components; polynomial coefficients in $p,v$ are summed in descending
lexicographic order with repeated-multiplication powers. For a real
interval $I=[l,u]$ set

$$
\operatorname{loabs}(I)=\max\{l,-u,0\},\qquad
\operatorname{hiabs}(I)=\max\{|l|,|u|\}.
$$

For its complex interval enclosures define

$$
L=\max\{\operatorname{loabs}(\operatorname{Re}T_1),
        \operatorname{loabs}(\operatorname{Im}T_1)\},\qquad
B=\sum_{k\ne1}\bigl(\operatorname{hiabs}(\operatorname{Re}T_k)
                    +\operatorname{hiabs}(\operatorname{Im}T_k)\bigr).
\tag{20.4}
$$

The table gives $\lfloor L/B\rfloor=h>1$. The leading coefficient
has these enclosures, with the same $[l,u]/10^9$ convention:

| Base rectangle | $[x^{18}]R$ |
| --- | --- |
| $\mathcal B_{6}$ | $[715706186670432957361776747931,715706186670432957361776747932]$ |
| $\mathcal B_{10}$ | $[-8325931644667958868422117585,-8325931644667958868422117584]$ |

**Lemma 20.3 (Exhaustion by eighteen discs).** For every base in either
closed rectangle, each of its eighteen discs contains exactly one simple
root of $R$, and the discs exhaust its roots. The positive real roots
are exactly discs $9,\ldots,14$ for $\mathcal B_6$ and
$8,\ldots,16$ for $\mathcal B_{10}$.

Proof. Formula (20.2), (20.3) and rational evaluation give (20.4) with
the tabulated integer bounds. On $|z|=1$, the modulus of $T_1z$
is at least $L$, and that of the sum of all other terms is at most
$B<L$. Rouché's theorem gives one root counted with multiplicity
inside each disc and none on its boundary. The leading-coefficient
table gives degree exactly eighteen. The discs are pairwise disjoint,
so these eighteen roots exhaust the degree and are simple.

The nonreal discs do not intersect the real axis. A real-centred disc
is invariant under conjugation, so its unique root is real. Their
centres and radii put the first eight or seven, respectively, strictly
on the negative side, and the stated six or nine strictly on the
positive side. This allocation does not assert that every positive
root is an actual world. ∎

**Definition 20.4 (The drift subresultant and terminal intervals).**
Write $f=A_2d^2+B_2d+C_2$ and
$K_{\rm s}=k_4d^4+k_3d^3+k_2d^2+k_1d+k_0$. Form

$$
\alpha_d=\det\begin{pmatrix}
k_4&k_3&k_2&k_1\\
A_2&B_2&C_2&0\\
0&A_2&B_2&C_2\\
0&0&A_2&B_2
\end{pmatrix},\qquad
\beta_d=\det\begin{pmatrix}
k_4&k_3&k_2&k_0\\
A_2&B_2&C_2&0\\
0&A_2&B_2&0\\
0&0&A_2&C_2
\end{pmatrix}.
\tag{20.5}
$$

Their coordinate degrees in $(x,p,v)$ are $(32,3,3)$ and $(32,4,4)$.
Polynomial pseudo-division, or expansion of these minors, gives the
necessary relation $\alpha_dd+\beta_d=0$ at every common root of
$f,K_{\rm s}$. For every positive real disc of Lemma 20.3 evaluate
$\alpha_d$, then $d=-\beta_d/\alpha_d$, then (5.5) and (17.5)
on $[\xi-\rho,\xi+\rho]$ and the entire closed base rectangle.
All table entries below are $[l,u]/10^9$ as before. Disc numbers
refer to Definition 20.2; no guard filter has yet removed a disc.

| Disc in $\mathcal B_{6}$ | $x$ | $d$ | $U$ | $r$ |
| --- | --- | --- | --- | --- |
| 9 | $[344936877,344936878]$ | $[257748961197,257748961198]$ | $[-14681597162,-14681597161]$ | $[-9205698860,-9205698859]$ |
| 10 | $[397297877,397297878]$ | $[408181539813,408181539814]$ | $[-2932129649,-2932129648]$ | $[861737270,861737271]$ |
| 11 | $[991684316,991684317]$ | $[-661260652530,-661260652529]$ | $[1033078679,1033078680]$ | $[16673032,16673033]$ |
| 12 | $[999552921,999552922]$ | $[-646723140093,-646723140092]$ | $[999999999,1000000001]$ | $[-1,1]$ |
| 13 | $[2235198431,2235198432]$ | $[-135770163116,-135770163115]$ | $[45767335,45767336]$ | $[848638893,848638894]$ |
| 14 | $[3157799982,3157799983]$ | $[-79895343304,-79895343303]$ | $[-33960984,-33960983]$ | $[-278253434,-278253433]$ |

| Disc in $\mathcal B_{6}$ | $\alpha_d$ | $H_1$ | $C_0$ | $a$ |
| --- | --- | --- | --- | --- |
| 9 | $[-1147173551482223821588013730856,-1147173551482223821588013730853]$ | $[828644006748,828644006749]$ | $[67548781696479,67548781696480]$ | $[-295715986002,-295715986001]$ |
| 10 | $[-8250274159537062940521172528809,-8250274159537062940521172528801]$ | $[-555824194263,-555824194262]$ | $[320344450771578,320344450771579]$ | $[344675806250,344675806251]$ |
| 11 | $[336556812961317536064718846784540742,336556812961317536064718846785099852]$ | $[702438688041,702438688042]$ | $[898881858114241,898881858114242]$ | $[1539997017819,1539997017820]$ |
| 12 | $[442407135710924078501882487260370861,442407135710924078501882487261011237]$ | $[671023140092,671023140093]$ | $[875393320498630,875393320498631]$ | $[1538494776744,1538494776745]$ |
| 13 | $[2103128407738273052171380920757694862399405803,2103128407738273052171380920757708635009510158]$ | $[-9797486930,-9797486929]$ | $[118215729570545,118215729570546]$ | $[25150140656901,25150140656902]$ |
| 14 | $[13872535851252896341136936720397296289023660235151,13872535851252896341136936720397355287932577198437]$ | $[-20632467893,-20632467892]$ | $[57583739030905,57583739030906]$ | $[3371551896416,3371551896417]$ |

| Disc in $\mathcal B_{10}$ | $x$ | $d$ | $U$ | $r$ |
| --- | --- | --- | --- | --- |
| 8 | $[340302907,340302908]$ | $[16507393811,16507393812]$ | $[9531042903,9531042904]$ | $[5992988770,5992988771]$ |
| 9 | $[530132537,530132538]$ | $[-2214142895,-2214142894]$ | $[-14849065177,-14849065176]$ | $[59636773,59636774]$ |
| 10 | $[943249412,943249413]$ | $[44802315070,44802315071]$ | $[1316711388,1316711389]$ | $[174396730,174396731]$ |
| 11 | $[953208222,953208223]$ | $[42434433489,42434433490]$ | $[1688603962,1688603963]$ | $[545086537,545086538]$ |
| 12 | $[1100600016,1100600017]$ | $[39496191029,39496191030]$ | $[149190625,149190626]$ | $[864671194,864671195]$ |
| 13 | $[1202847061,1202847062]$ | $[36627913282,36627913283]$ | $[-126685887,-126685886]$ | $[-310044740,-310044739]$ |
| 14 | $[2377764520,2377764521]$ | $[24614429363,24614429364]$ | $[1024053499,1024053500]$ | $[982363610,982363611]$ |
| 15 | $[2419914166,2419914167]$ | $[24511280376,24511280377]$ | $[999999999,1000000001]$ | $[-1,1]$ |
| 16 | $[43306187499,43306187500]$ | $[18446055129,18446055130]$ | $[35906919,35906920]$ | $[1283191656,1283191657]$ |

| Disc in $\mathcal B_{10}$ | $\alpha_d$ | $H_1$ | $C_0$ | $a$ |
| --- | --- | --- | --- | --- |
| 8 | $[443405080642416782611986978,443405080642416782611986979]$ | $[-25972404529,-25972404528]$ | $[278489181226,278489181227]$ | $[362487470473,362487470474]$ |
| 9 | $[149422510655648787620179638,149422510655648787620179639]$ | $[49076485990,49076485991]$ | $[25746468707,25746468708]$ | $[193562640486,193562640487]$ |
| 10 | $[78092027076495747617342084737,78092027076495747617342084751]$ | $[-25656508592,-25656508591]$ | $[2184049825131,2184049825132]$ | $[295350647737,295350647738]$ |
| 11 | $[79070460912964589173960640914,79070460912964589173960640930]$ | $[-29242199724,-29242199723]$ | $[1894694736935,1894694736936]$ | $[325630020669,325630020670]$ |
| 12 | $[-17506984299540851302238308377284,-17506984299540851302238308377077]$ | $[3300469499,3300469500]$ | $[1868687727136,1868687727137]$ | $[1385561258438,1385561258439]$ |
| 13 | $[-227259640586443535842148065006989,-227259640586443535842148065005827]$ | $[10146951114,10146951115]$ | $[1615600459080,1615600459081]$ | $[321374233414,321374233415]$ |
| 14 | $[571508276970638864189487618824774707282299,571508276970638864189487618824782443629460]$ | $[-433161873,-433161872]$ | $[628230734198,628230734199]$ | $[469025460901,469025460902]$ |
| 15 | $[980244473451625717141519828976107038412943,980244473451625717141519828976119121155690]$ | $[-211280377,-211280376]$ | $[624702445262,624702445263]$ | $[359651551197,359651551198]$ |
| 16 | $[499732416496015624891715841766913349325682191056720073855722114731445909908995332,499732416496015624891715841766913358753337967476575222924246183100686057651061539]$ | $[733719521,733719522]$ | $[787516502784,787516502785]$ | $[934154741680,934154741681]$ |

**Theorem 20.5 (Whole-child J injectivity on both open rectangles).**
For every $(p,v)\in\mathcal B_6\cup\mathcal B_{10}$, the
terminal function $a$ is injective on the entire actual $C(p,v)$.
Thus $(\mathcal B_6\cup\mathcal B_{10})\cap D_J=\varnothing$.

Proof. Take any actual world, including a singular $J$ label or an
unused singular world, zero drift, $F_0=0$, a degree drop, or a gain
with sampled or repeated roots. S, Theorem 4.1, first puts its
$x>0$ on $R=0$. Lemma 20.3 puts it in one of the listed positive
discs. Lemma 17.3 gives $f=K_{\rm s}=0$. The $\alpha_d$ table
excludes zero throughout each positive real disc, so (20.5) fixes
its drift uniquely. F, Lemma 30.2, fixes at most one complete world
at that $(x,d)$. Two distinct worlds must therefore come from
different discs. Their necessary $a$ intervals in Definition 20.4
are pairwise disjoint within each rectangle, so they cannot have equal
terminal $J$ values.

This even retains the disc whose reconstruction is near $U=1,r=0$;
its legality need not be decided. All positive carrier roots were
covered before any source filtering, so the conclusion quantifies
over the whole actual child. ∎

## 21. The shared-base lower-face stratum and its finite limiting end

**Theorem 21.1 (L2: empty lower-boundary-M/actual-J stratum).** There is
no tuple $(t,W,J_0,J_1)$ such that $(t,W)\in\mathcal L_M$ and
$J_0\ne J_1$ are actual complete worlds in the same entire
$C(p_L(t),v_L(t))$ with $a(J_0)=a(J_1)$.

Proof. Theorem 19.4 forces $t=t_6$ or $t=t_{10}$. Definition 20.1
puts the corresponding exact base strictly inside its open rectangle,
and Theorem 20.5 excludes every actual $J$ pair there. No assumption
has connected either $J$ endpoint to the strict mixed-$M$ companion.
Unused worlds and arbitrary pair overlap remain in scope. ∎

**Theorem 21.2 (L3: no finite off-24 joint end on the open lower face).**
Let original joint configurations have acquired bases converging to a
finite $(p_*,v_*)$ with $p_*\ne24$. Neither selected $M$ endpoint
can converge in complete source, whole-gain and drift coordinates to
$L(t)$ with $t>0,t\ne1$.

Proof. If one did, its $\delta$ would tend to zero. Choose one finite
$P$ bounding the fifth responses. Theorem 14.3 forces the other
selected $M$ endpoint to have $\delta\ge\varepsilon(P)$ eventually.
The cap and coercivity in Assumption 14.1 give a convergent subsequence
of its complete coordinates, with a strict limit $W\in C(p_*,v_*)$.
This is precisely the mixed alternative of Theorem 16.1; it uses the
compact strict-anchor construction of Theorem 15.1, or the same closed
bounded set for this selected pair.

Continuity of all original readings and terminal $M$ responses gives
$(p_*,v_*)=(p_L(t),v_L(t))$ and $m(W)=m_L(t)$. Theorem 19.4
makes this one of the two survivor bases. Each has an open neighbourhood
from Definition 20.1 on which the entire actual child is $J$ injective.
All sufficiently late bases lie there, contradicting their original
selected distinct $J$ pairs. This argument makes no compactness or
convergence assumption on those $J$ endpoints. It also adds no
cross-pair distinctness requirement. ∎

## 22. Exact exclusion of both corner mixed-M relations

**Definition 22.1 (Corner systems).** Use the two auxiliary complete corner
tuples $L,R$ of Definition 12.1. Their respective $(p,v,m)$ are

$$
(39/2,258/5,1977/10),\qquad (18,399/5,366).
\tag{22.1}
$$

Their whole gains have samples $(-24,3/10,27/5,3/10)$ and
$(-24,3/5,27/5,0)$ at $0,1,2,3$, both with drift $24$.
Neither corner is a legal endpoint. Specialize $F_M,G_M$ of (17.8)
at the corresponding rational triple and take positive-leading primitive
integer parts. Denote these polynomial pairs by $(f_-,g_-)$ and
$(f_+,g_+)$, with complete coefficient lists below.

$$
\operatorname{coeff}_{\downarrow}(f_-)=\bigl(
1642320,
970073,
2144104,
-4273136,
4528846,
-1555483,
-492420,
0
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(g_-)=\bigl(
134006660446032,
-486765699860232,
913019068868549,
-1087813500618794,
846109262381000,
-377006767784245,
24778834503455,
98037115860966,
-73209913838814,
26539280444773,
-4540844494154,
-305571117252,
1464412968,
0,
0
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(f_+)=\bigl(
623680,
-1051168,
2214651,
-3646243,
2736266,
-1028650,
105159,
46305
\bigr).
$$

$$
\operatorname{coeff}_{\downarrow}(g_+)=\bigl(
11877259874304,
-78285462466560,
214781375474048,
-317070184384128,
263866056659737,
-104954811316425,
-11352297359697,
35652434925343,
-19261034697427,
5697427653797,
-1076704426475,
138646493037,
-14401449810,
1857103200,
-162082944
\bigr).
$$

**Lemma 22.2 (Corner units and pole certificates).** The following table
lists the exact common factor $h$, the preserved quotient degrees and
nonzero resultant residue for
$\operatorname{pp}(f_\pm/h),\operatorname{pp}(g_\pm/h)$, and the
exact rational resultant of $\lambda,N$ at the corner triple.

| Corner | $h$ | Quotient degrees over $\mathbb Q$ and $\mathbb F_{101}$ | Quotient resultant modulo $101$ | $\operatorname{Res}_x(\lambda,N)$ |
| --- | --- | --- | --- | --- |
| $L$ | $x$ | $(6,13)$ | $10$ | $46698352835472/625$ |
| $R$ | $x-1$ | $(6,13)$ | $52$ | $-155083881111552/625$ |

Proof. Substitute (22.1) into (17.8), clear denominators, and remove
positive contents. This gives exactly the four displayed integer lists.
Divide by the stated $h$ with zero remainder. Sylvester elimination
modulo $101$ gives $10,52$, with quotient degrees $6,13$ preserved.
Consequently the two quotients share no complex root. The rational
Sylvester determinants of $\lambda,N$ give the last column; neither
vanishes. These are full polynomial-pair certificates, including the
terminal-slope pole, rather than tests on a finite set of real guesses. ∎

**Theorem 22.3 (C1: both corner mixed-M systems are empty).** No actual
strict world in $C(39/2,258/5)$ has $m=1977/10$, and no actual
strict world in $C(18,399/5)$ has $m=366$.

Proof. At either corner the nonzero resultant of $\lambda,N$ excludes
$\lambda=0$ for an actual terminal-equal world. For $\lambda\ne0$
the equations force the common roots of $f_\pm,g_\pm$. Lemma 22.2
leaves only $x=0$ in the lower case and $x=1$ in the upper case.
The former violates $x>0$. For the latter the affine terminal equation
gives $d=24$, excluded for the actual off-$24$ child by F, Lemma 30.2.
Thus no strict complete world survives either system. ∎

## 23. One global positive collar for selected-M endpoint sums

**Theorem 23.1 (C2: a uniform lower bound on both selected b+c sums).**
There is one $\eta>0$ such that for every real $p\ne24,v$ and every
actual distinct terminal-$M$-equal pair $W,W'\in C(p,v)$,

$$
b(W)+c(W)\ge\eta,\qquad b(W')+c(W')\ge\eta.
\tag{23.1}
$$

No numerical value of $\eta$ is asserted.

Proof. If no such constant existed, choose actual distinct pairs and
one selected endpoint, denoted $W_n$, with
$j_n=b_n+c_n\to0$. Since $b_nc_n=r_n(1-r_n)$ and
$0<r_n<1$, a subsequence has $r_n\to0$ or $r_n\to1$.
Both $b_n,c_n$ tend to zero. On the lower branch,

$$
\frac{r_n}{j_n}=\frac{b_nc_n}{(1-r_n)(b_n+c_n)}\longrightarrow0,
\qquad n_n/j_n\longrightarrow1,
\qquad j_n\Lambda_n\longrightarrow-8.
\tag{23.2}
$$

For example $b_nc_n/(b_n+c_n)\le j_n/4$, which justifies the
first limit. On the upper branch $n_n\to1$ and
$j_n\Lambda_n\to-4$. Thus these sources are regular eventually,
and the same parent formula (2.1), whose numerator tends to $12/5$,
gives

$$
e_n/j_n\longrightarrow-3/10\quad\hbox{or}\quad-3/5.
\tag{23.3}
$$

It follows that $d_n\to24$ and the four samples of the same whole
gain tend respectively to

$$
(-24,3/10,27/5,3/10)\quad\hbox{or}\quad(-24,3/5,27/5,0).
\tag{23.4}
$$

Fixed-node interpolation makes all four padded polynomial coefficients
converge. The source and original trace formulas then make all responses
converge to the corresponding complete corner tuple. In particular
$p_n\to39/2$ or $18$, and $(p_n,v_n,m_n)$ tends to the
corresponding triple (22.1). This derives bounded fifth responses from
the violating sequence; the theorem assumes no global bound on $p$.

Choose $P$ bounding those $p_n$. Since
$\delta(W_n)\le j_n\to0$, Theorem 14.3 gives
$\delta(W'_n)\ge\varepsilon(P)$ for all sufficiently large $n$.
The uniform pair cap and bounded-$p$ coercivity of Assumption 14.1
bound $W'_n$ in complete coordinates. Extract a convergent subsequence;
its positive $\delta$ bound makes the limit a strict source. All
original readings pass to the limit, and its gain is nonzero because
of the readings $0,24$. This is the strict compact-anchor reasoning
of Theorem 15.1, applied to this selected $M$ pair.

The limit is an actual strict world at the relevant off-$24$ corner
base. Equality $m(W'_n)=m(W_n)$ passes to the limit and gives that
corner's $m$ value. This contradicts Theorem 22.3. Therefore the
infimum of $b+c$ over every endpoint of every such selected pair is
positive, which gives one $\eta$ in (23.1). If the set of pairs is
empty, any positive $\eta$ works. ∎

The sum bound does not give a separate positive lower bound on $b$ or
on $c$. Theorem 23.1 concerns selected $M$ collision endpoints only;
it states no such bound for selected $J$ endpoints or unused worlds.

## 24. Reuse, exact scope and residual joint incidence

**Assumption 24.1 (Supplier correspondence and classical tools).**
The parameter correspondences used in Sections 17–23 are:

| Owning result | Correspondence and use |
| --- | --- |
| Definitions 1.1–1.2; O, Definitions 1.1–1.3 and Theorems 2.1–2.2 | The same $(P(r,b),g,d)$, literal $H_4$, clocks and left products throughout. |
| F, Lemma 30.2; Assumption 5.3 | Exactly $x=(j+r)/U$, $H=Ug$, $B_0=2(147/5-d)-H_2$ and the full faithful guard set. Lemma 17.3 expresses this interface by a uniform rank equation. |
| F, Definition 31.1 and Lemma 31.2; (5.1)–(5.2); S, Theorem 4.1 | The same fixed $R$ normalization, applied to every actual child world before any division by $F_0$ or drift. |
| Lemma 12.2; S, Theorem 13.1 | $L(t)=B_0(t)$, $q=10(t-1)$, exact lower-face fractions and its one whole boundary gain. |
| Definition 12.1; S, Definition 12.2 | The exact two complete corner labels, not strict endpoints. |
| Assumption 14.1 and Theorems 14.3–16.1 | The existing cap, bounded-$p$ coercivity, selected-pair interior endpoint and complete strict-anchor extraction, used only in the two limit contradictions. |

Distinct-node interpolation, Sylvester determinants, the determinant
subresultant gcd criterion, Sturm's theorem and Rouché's theorem are
classical mathematical tools. Here their specialized inputs are the
explicit polynomial circuits, coefficient lists, exact unit residues,
Sturm signs, rational brackets and strict circle inequalities above.
Rouché's theorem has the same complex-polynomial and strict-boundary
hypotheses as in Assumption 11.1. Compactness is the finite-dimensional
closed bounded argument of Sections 14–16, with padded whole-gain
coefficients. No generic real-root lift, properness theorem or
unproved specialization converse replaces the displayed guards.
These source-specific deductions make no literature-priority claim.

**Proposition 24.2 (Useful delta and unresolved original objective).**
Sections 17–23 classify the entire finite nonpole lower-face mixed-$M$
relation into two actual strict companions, exclude its shared-base
actual-$J$ consumer, exclude the stated finite off-$24$ joint end,
exclude both corner mixed-$M$ relations, and give the global selected-$M$
endpoint sum bound (23.1).

Proof. These are Theorems 19.4, 21.1–21.2, 22.3 and 23.1.
The rational lower curve, faithful reconstruction, all-world carrier,
finite boundary tuples and strict-anchor bounds are the listed suppliers;
those earlier results alone did not classify the strict mixed companions
or prove the whole-child $J$ exclusions at the two resulting bases. ∎

The original alternative (11.1), namely a strict off-$24$ joint child
or an exhaustive all-real exclusion, remains unresolved. In particular
the residual strict interior common components and isolated intersections,
other finite faces, augmented interior critical limits, exceptional
meetings, unbounded acquired bases and limits with $p\to24$ remain.
No separate upper-face classification is a premise of Sections 17–23.
The interval root covers are consumed by the full lower-face theorem;
they are not an assertion of global $J$ injectivity. Neither closedness
nor properness of a collision projection follows.

All singular $J$ endpoints and unused singular worlds, zero drift,
nonsingular $F_0=0$, lower degrees and sampled or repeated gain roots
remain in the actual-world quantifiers until an explicit certificate
excludes them. The original $J$ and $M$ pairs may overlap or be disjoint,
and their terminal common values may differ. No terminal alternative
has become an acquired port. The same-fifth-response sixth-$J$ child
and the other fifth-$J$/common-parent requirements and O, Theorem 17.1,
ancestor conjunctions remain separate obligations. No fifth-$M$ $L_2$,
$H_4$ $L_3$, guarded root $L_7$ or eight-versus-nine conclusion follows.

## 追加锚（本行以下为增补区）

## 25. The finite coefficient closure above the fifth response twenty-four

**Definition 25.1 (Complete tuples and the closed fibre).** Retain
Definitions 1.1–1.2 and 12.1, including the entire actual child $C(p,v)$,
all original clocks and the one whole gain of each world. Write a complete
tuple as $(r,b,c,d,g_0,g_1,g_2,g_3)$, where $g_i=[s^i]g$ and
$bc=r(1-r)$. The topology is the Euclidean topology of these coordinates;
lower-degree gains are padded by zero. Let

$$
\mathcal L_{24}=\overline{\mathcal H}\cap\{p=24\},\qquad
\mathcal H=\mathcal F(H_4),\qquad
\Psi_M=(p,v,m),\quad
k=m-\frac{32}{5}v,\quad \ell=m-\frac{24}{5}v.
\tag{25.1}
$$

The closure here consists of finite tuples. At a boundary tuple, responses
are evaluated by their original polynomial matrix formulas. Boundary tuples
are auxiliary limits, not additional actual worlds. In particular no
compact source restriction is part of this definition.

Set $e=d-24$, $\Delta=b-1/8$ and, wherever $j,n>0$,

$$
\begin{gathered}
j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad V=U+n,\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
B_{\rm coef}=6/T-2/U=\frac{2(2+5b)}{TU},\\
R_0(b,r,e)=e\Lambda+\frac{24}{5}\Delta B_{\rm coef}.
\end{gathered}
\tag{25.2}
$$

The complete parent equation is $R_0=0$. Its gain is the single polynomial
of degree at most three with values

$$
(g(0),g(1),g(2),g(3))=
\left(-24-e,-e/j,\frac{27/5-e}{T},-e/n\right).
\tag{25.3}
$$

These are the zero-safe parent equations of O, Theorem 2.1. In particular
they do not require $e\ne0$ or $\Lambda\ne0$. The original left products give

$$
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\qquad
(\operatorname{tr}(Q_iP))_{i=0}^6=(1,j,T,n,U,U+n,2U+n),
\tag{25.4}
$$

and terminal traces $T+2j+4r$ and $3U+2n$ for $J$ and $M$.
The extrapolation rows from (25.3) to clocks $5,6,7$ are exactly (2.3).
Thus $\Psi_M$ always uses the same interpolated whole gain and fixed drift.
Neither $k$ nor $\ell$ is an additional acquired observation.

**Definition 25.2 (The two closed families).** Put

$$
\begin{gathered}
h(s)=\frac85(s-1)(s-3)(s-5),\qquad
\overline{\mathcal K}(r)=(P(r,1/8),h,24),\quad 0\le r\le1,\\
c=8r(1-r),\qquad n(r)=\frac18+9r-8r^2,\qquad k_0=-\frac{1128}{5}.
\end{gathered}
\tag{25.5}
$$

At $r=0,1$ these are auxiliary complete tuples. Direct evaluation gives

$$
p=24,\qquad v=84+24n(r),\qquad
m=312+\frac{768}{5}n(r),\qquad k=k_0.
\tag{25.6}
$$

The external family uses the following sextic, distinct from the history
$H_4$ and from the gain polynomial:

$$
\begin{aligned}
H(r,b)={}&14b^6+(95-73r)b^5+(47r^2-39r+30)b^4\\
&+r(147r^2-232r+105)b^3
 +2r(1-r)(44r^2-55r+15)b^2\\
&-64r^3(1-r)^2b-32r^3(1-r)^3.
\end{aligned}
\tag{25.7}
$$

For $0<r<1$, let $B_H(r)$ be its unique positive root. O, Theorem 13.2,
gives $H_b(r,B_H(r))>0$ and the complete lift below. Define

$$
\begin{aligned}
L_0(s)&=-\frac{(s-1)(s-3)(s-5)}{15},&
L_1(s)&=\frac{s(s-3)(s-5)}8,\\
L_3(s)&=-\frac{s(s-1)(s-5)}{12},&
L_5(s)&=\frac{s(s-1)(s-3)}{40},\\
w_{r,b}(s)&=-L_0(s)-L_1(s)/j-L_3(s)/n-L_5(s)/V,\\
E_2(r,b)&=1+T\left(\frac15-\frac3{4j}-\frac1{2n}+\frac1{20V}\right).
\end{aligned}
\tag{25.8}
$$

On $H=0$ in the strict source domain, $E_2\ne0$, and the external world is

$$
\mathcal H_H(r)=
\left(P(r,B_H(r)),h+e_H(r)w_{r,B_H(r)},24+e_H(r)\right),
\qquad e_H(r)=-\frac{24(B_H(r)-1/8)}{5E_2(r,B_H(r))}.
\tag{25.9}
$$

Complete this family at $r=0,1$ by the labels $B_0(c_L),B_1(c_R)$ of
Definition 12.1, where

$$
16c_L^2-15=0,\quad c_L>0,\qquad
8c_R^3+16c_R^2-2c_R-5=0,\quad c_R>0.
\tag{25.10}
$$

Denote the completed parametrization by $\overline{\mathcal H}_H(r)$,
$0\le r\le1$. The endpoint uniqueness and continuity are proved below.
Intersections of the two families mean identical complete tuples and are
counted once.

## 26. Endpoint certificates and the complete closed matching relation

**Lemma 26.1 (Both added endpoints and their strict separators).**
The two positive roots in (25.10) are unique, nonpole parameters. Their
complete gains, drifts and responses have the following exact certificates.
For the lower endpoint put $q_L(c)=10(c-1)$; then

$$
\begin{aligned}
P_L(c)&=-48c^2+240c-195,\\
V_L(c)&=135c^2+375c-516,\\
M_L(c)&=1152c^2+813c-1977,\\
(p,v,m)&=(P_L,V_L,M_L)/q_L,\qquad e=3c/q_L,\\
(g(0),g(1),g(2),g(3))&=(-24-e,-e/c,27/5-e,-e/c).
\end{aligned}
\tag{26.1}
$$

For the upper endpoint put $q_R(c)=5(2c^2-1)$; then

$$
\begin{aligned}
P_R(c)&=-48c^3+144c^2+12c-90,\\
V_R(c)&=135c^3+645c^2-99c-399,\\
M_R(c)&=1152c^3+3117c^2-696c-1830,\\
(p,v,m)&=(P_R,V_R,M_R)/q_R,\qquad e=3c(c+1)/q_R,\\
(g(0),g(1),g(2),g(3))&=(-24-e,-e/c,27/5-e,-e/(c+1)).
\end{aligned}
\tag{26.2}
$$

In each row the gain is the unique polynomial of degree at most three at
the original nodes $0,1,2,3$. Both endpoints satisfy

$$
p=24,\qquad e<0,\qquad k-k_0>0,\qquad e(k-k_0)<0.
\tag{26.3}
$$

Proof. Substitution in (25.2)–(25.3) on $(r,b,c)=(0,0,c)$ or $(1,0,c)$,
followed by the interpolation rows (2.3), gives (26.1)–(26.2).
The clock-four equation is $R_0=0$ in each case. In particular these are
whole boundary lifts, not separately chosen late gain values. The
fifth-response identities are

$$
\begin{aligned}
P_L-24q_L&=-3(16c^2-15),\\
P_R-24q_R&=-6(8c^3+16c^2-2c-5).
\end{aligned}
\tag{26.4}
$$

Their rational isolating data are

$$
\begin{array}{c|c|c|c}
 &\text{open bracket}&\text{value at left}&\text{value at right}\\ \hline
16c^2-15&(24/25,97/100)&-159/625&34/625\\
8c^3+16c^2-2c-5&(27/50,11/20)&-2417/15625&71/1000.
\end{array}
\tag{26.5}
$$

The quadratic has exactly one positive root, $c_L=\sqrt{15}/4$.
The cubic coefficient signs have one change, so Descartes' rule, together
with the sign-changing bracket, gives exactly one positive root $c_R$.
The brackets give $c_L<1$ and $c_R<11/20<1/\sqrt2$, so neither
$q_L(c_L)$ nor $q_R(c_R)$ vanishes, and both displayed drifts have $e<0$.

The exact separator fractions from the same response polynomials are

$$
\begin{aligned}
(k-k_0)_{B_0(c)}&=
\frac{3(480c^2+1115c-1551)}{50(c-1)},\\
(k-k_0)_{B_1(c)}&=
\frac{3(480c^3+2075c^2-104c-674)}{25(2c^2-1)}.
\end{aligned}
\tag{26.6}
$$

Modulo the respective root polynomials, the numerators in parentheses
reduce to $1115c-1101$ and $1115c^2+16c-374$. On the isolating brackets,

$$
\begin{aligned}
1115c_L-1101&<1115\frac{97}{100}-1101=-\frac{389}{20}<0,\\
1115c_R^2+16c_R-374
&<1115\left(\frac{11}{20}\right)^2+16\frac{11}{20}-374
=-\frac{2233}{80}<0.
\end{aligned}
\tag{26.7}
$$

The denominators in (26.6) are negative at the respective roots.
Thus $k-k_0>0$ and (26.3) follows. ∎

**Theorem 26.2 (The entire finite $p=24$ closure).** The parametrization
$\overline{\mathcal H}_H$ is continuous on $[0,1]$, and, as a set of
complete tuples,

$$
\mathcal L_{24}=
\overline{\mathcal K}([0,1])\ \cup\
\overline{\mathcal H}_H([0,1]).
\tag{26.8}
$$

Proof. A strict finite source limit of parent worlds still satisfies all
original reading equations. Its gain is nonzero: a zero gain would make
the readings $0$ and $24$ equal to the same drift. When its fifth response
is $24$, O, Theorem 13.2, gives exactly the strict K/H set union in
(25.5), (25.9), including the identical-world intersections.

For a nonstrict source, the nonnegative rank-one equation
$bc=r(1-r)$ leaves the four open faces of Definition 12.1 or the two
$j=0$ corners. At an open-face pole the right side of
$e\Lambda=-(24/5)\Delta B_{\rm coef}$ is nonzero while $\Lambda=0$;
there is no finite-drift limit there. At any other open-face point,
$\Lambda\ne0$ uniquely determines the drift, and (25.3) uniquely
determines the whole gain. These are exactly the finite face labels.

Here is the complete $p=24$ filter on the $c=0$ faces. For $b>0$,
Definition 12.1 and Lemma 12.2 give

$$
\begin{aligned}
p_{C_0(b)}-24&=
\frac{-3(8b-1)(14b^2+95b+30)}{5(b^3-8b-4)},\\
p_{C_1(b)}-24&=
\frac{-6(8b-1)(7b^3+11b^2+19b+10)}{5(b+1)(b^3-4b-2)},\\
H(0,b)&=b^4(14b^2+95b+30)>0,\\
H(1,b)&=2b^3(7b^3+11b^2+19b+10)>0.
\end{aligned}
\tag{26.9}
$$

All the parenthesized positive-coefficient factors are positive for $b>0$.
Thus $b=1/8$ is the only admissible fifth-response root on each face.
Its drift is $24$ and its gain is $h$, giving exactly
$\overline{\mathcal K}(0)$ and $\overline{\mathcal K}(1)$.
Equivalently the odd-node interpolation (25.8) gives
$E_4+2E_2=-H/(10XNW)$, with $X=bj,N=bn,W=bV$ and
$E_4=1+U(-1/5+1/(2j)-1/n-3/(10V))$.
Together with $eE_2=-(24/5)\Delta$, $eE_4=2(24/5)\Delta$,
this again forces $e=0,b=1/8$ on these faces.
The $b=0$ faces are exhausted by (26.4)–(26.5), giving precisely the
two endpoints in Lemma 26.1.

At the lower corner, along a strict approach,

$$
\frac rj=\frac{bc}{(1-r)(b+c)}\longrightarrow0,\quad
\frac nj\longrightarrow1,\quad j\Lambda\longrightarrow-8,\quad
e/j\longrightarrow-3/10.
\tag{26.10}
$$

At the upper corner $n\to1$, $j\Lambda\to-4$ and $e/j\to-3/5$.
The four gain sample limits are respectively
$(-24,3/10,27/5,3/10)$ and $(-24,3/5,27/5,0)$.
Their fifth responses are $39/2$ and $18$, so neither corner lies in
$\mathcal L_{24}$. This passage uses the finite exhaustion in Lemma 14.2;
it does not assume the limiting fifth response is off $24$.
This proves exhaustion of every possible finite limit in (26.8).

To prove that the stated H endpoints are actually attained as limits,
and that the entire completed family is continuous, put
$q=r(1-r)$ and $t=b/q$. Direct expansion of (25.7) gives

$$
\begin{aligned}
H(r,qt)&=q^3G(r,t),\\
G(r,t)&=14q^3t^6+(95-73r)q^2t^5+(47r^2-39r+30)qt^4\\
&\quad+r(147r^2-232r+105)t^3
 +2(44r^2-55r+15)t^2-64rt-32,\\
G(0,t)&=30t^2-32,\\
G(1,t)&=4(5t^3+2t^2-16t-8).
\end{aligned}
\tag{26.11}
$$

F, Lemma 28.2, supplies $1<t<2$ on the entire strict H graph.
For clarity its exact degree-six Bernstein sign vectors in $r$ are

$$
\begin{aligned}
G(r,1):\;&(-2,-17/2,-343/15,-459/10,-1024/15,-227/3,-68),\\
G(r,2):\;&(88,640/3,5512/15,302,160/3,4/3,32).
\end{aligned}
\tag{26.12}
$$

The Bernstein basis functions on $[0,1]$ are nonnegative and sum to one,
so these signs, together with uniqueness of the positive H root, give
the stated derived strip. At $r=0$, the only root of $G(0,t)$ in $[1,2]$
is $4/\sqrt{15}$. At $r=1$, the cubic in (26.11) has negative and
positive values at $1,2$ and derivative
$15t^2+4t-16\ge3$ on $[1,2]$, hence exactly one root there.
Its reciprocal is $c_R$, by multiplying that cubic by $c^3$ with $t=1/c$.
Every endpoint subsequence of $t$ therefore has the same limit.
Since $b=qt\to0$ and $c=1/t$, the source limits are the two stated labels.

At those limits $\Lambda=8(c_L-1)/c_L$ and
$\Lambda=4(2c_R^2-1)/(c_R(c_R+1))$, respectively, both nonzero by
(26.5). Thus the regular formula
$e=-(24/5)\Delta B_{\rm coef}/\Lambda$ and (25.3) make the entire
gain and drift converge continuously to (26.1)–(26.2).
The strict H family is already continuous by O, Theorem 13.2.
Finally the two K endpoints are approached directly along K. All members
on the right of (26.8) are therefore finite limits of strict parent
worlds with $p=24$. This proves the reverse inclusion and continuity. ∎

**Theorem 26.3 (Every distinct matched pair in the closed fibre).**
For $X,Y\in\mathcal L_{24}$, $X\ne Y$, equality of $(v,m)$ holds if
and only if

$$
X=\overline{\mathcal K}(r),\qquad
Y=\overline{\mathcal K}(s),\qquad
r+s=9/8,\quad r\ne s,\quad r,s\in[1/8,1].
\tag{26.13}
$$

Proof. On strict H outside K, F, Theorem 25.2, gives
$e(k-k_0)<0$, and Lemma 26.1 gives the same strict separator at both
added H endpoints. All K labels have $k=k_0$. A matched pair cannot
therefore have one label in K and the other outside K.

On the entire strict H graph, F, Theorem 28.5 and (28.19), give
$d\ell(\mathcal H_H(r))/dr>0$. Theorem 26.2 supplies continuity at
both endpoints. This implies strict order on the closed interval as
well: if $0\le r<s\le1$, choose $r<a<b<s$ in $(0,1)$.
Continuity and strict interior order give
$\ell(r)\le\ell(a)<\ell(b)\le\ell(s)$.
Consequently two H labels with equal $(v,m)$ have the same parameter
and the same complete tuple. These comparisons include the K/H meetings.

The only remaining distinct pairs are both in K. By (25.6), their
response equality is exactly $n(r)=n(s)$, and

$$
n(r)-n(s)=(r-s)\{9-8(r+s)\}.
\tag{26.14}
$$

With $r,s\in[0,1]$ and $r\ne s$, this is equivalent to (26.13).
Conversely (26.13) gives equal responses by (25.6). ∎

## 27. Full-parent immersion at every noncentral strict limit

**Lemma 27.1 (An exact coprimality certificate for the K derivatives).**
In the full-parent chart $(r,e)$ along K, set

$$
\begin{gathered}
j=1/8+8r(1-r),\quad n=j+r,\qquad
D=(64r^2-72r-1)(64r^2-64r-1)=64jn,\\
\alpha(r)=\partial_ep(r,0),\qquad \eta(r)=\partial_ek(r,0).
\end{gathered}
\tag{27.1}
$$

For $0<r<1$ one has $D>0$ and

$$
\alpha=\frac{2A(r)}{21D},\qquad \eta=\frac{E(r)}{35D},
\tag{27.2}
$$

where the complete integer sextics are

$$
\begin{aligned}
A(r)={}&4194304r^6-13631488r^5+14499840r^4-4799744r^3\\
&-344608r^2+86780r+1347,\\
E(r)={}&-83886080r^6+272629760r^5-259665920r^4+31534592r^3\\
&+44367104r^2-5191448r-86605.
\end{aligned}
\tag{27.3}
$$

These two polynomials have no common complex root.

Proof. O, Lemma 16.2, gives the chart for the entire parent, with

$$
b(r,0)=1/8,\qquad b_r(r,0)=0,\qquad
b_e(r,0)=-\frac{25}{448}\Lambda(r,1/8),\qquad
(R_0)_b(r,1/8,0)=448/25.
\tag{27.4}
$$

This uses $(R_0)_b$, so it includes $\Lambda=0$ sources. Differentiating
(25.3) gives node derivatives
$(-1,-1/j,-\theta/T,-1/n)$, with
$T=9/8$, $\theta=1+(24/5)b_e=1-15\Lambda/56$ and
$\Lambda=107/15-4/j-4/n$. Applying (2.3) gives

$$
\begin{aligned}
\gamma_5:=\partial_eg(5)&=(-256+85/j+190/n)/21,\\
\gamma_6:=\partial_eg(6)&=(-185+48/j+160/n)/7,\\
\gamma_7:=\partial_eg(7)&=-48+10/j+45/n,\\
\alpha&=1+(n+5/4)\gamma_5,\\
\eta&=-27/5+(15/4+2n)\gamma_7
 -(32/5)(5/2+n)\gamma_6-(768/5)b_e\\
&=\frac{512n}{7}+\frac{8481}{35}-\frac{925}{4n}
 -\frac{836n/35+213/2}{j}.
\end{aligned}
\tag{27.5}
$$

For $\eta$ the $n_e$ terms cancel because
$(384/5)2n_e-(32/5)24n_e=0$. Clearing the positive denominators
in (27.5) gives exactly (27.2)–(27.3).

Here is a finite-field certificate with every coefficient explicit.
In $\mathbb F_{101}[r]$ put

$$
\begin{aligned}
u(r)&=27r^5+45r^4-38r^3+13r^2+21,\\
w(r)&=-34r^5-23r^4-13r^3+33r^2+28r+38.
\end{aligned}
\tag{27.6}
$$

Coefficient multiplication of (27.3) and (27.6) gives

$$
u A+w E\equiv1\pmod {101}.
\tag{27.7}
$$

For an additional determinant certificate, let $\operatorname{Syl}_{6,6}$
have first six rows the coefficient vectors of $r^5A,\ldots,A$ and
last six rows those of $r^5E,\ldots,E$, all in descending powers
$r^{11},\ldots,1$. Then

$$
\operatorname{lc}(A)\equiv77,\qquad
\operatorname{lc}(E)\equiv76,\qquad
\det\operatorname{Syl}_{6,6}(A,E)\equiv75\pmod {101}.
\tag{27.8}
$$

The leading residues preserve both degrees. Thus (27.7) certifies
coprimality of the reduced sextics, and (27.8) is the reduction of the
fixed integer Sylvester determinant. In particular that integer determinant
is nonzero. The classical resultant criterion therefore excludes a common
complex root of $A,E$. Consequently $(\alpha,\eta)\ne(0,0)$ at every
strict K source. ∎

**Theorem 27.2 (Full-parent local injectivity off the central world).**
At every strict $p=24$ world other than
$W_c=\mathcal K(9/16)$, $\Psi_M$ has rank two on the full parent and
is locally injective. This includes the singular K sources and both K/H
meetings.

Proof. At a K world, use (27.4). The derivative of $(p,k,v)$ in the
$r$ direction is

$$
\partial_r(p,k,v)(r,0)=(0,0,24(9-16r)).
\tag{27.9}
$$

For $r\ne9/16$ this is nonzero. Lemma 27.1 says that the first two
coordinates of its $e$ derivative are not simultaneously zero. These
two tangent vectors are independent. Since $(p,k,v)$ is an invertible
linear recombination of $\Psi_M$, some two-coordinate submap of
$\Psi_M$ has invertible derivative and is a local diffeomorphism.
This proves local injectivity of the whole map on the full parent.
No division by $\Lambda$ is involved at K or at a K/H meeting.

Now take a strict H world outside K. O, Theorem 13.2, implies $b\ne1/8$:
if $b=1/8$, (25.9) has $e_H=0$ and is the identical K world.
Since $B_{\rm coef}>0$, the parent equation forces $\Lambda\ne0$.
The regular formula for $e$ and (25.3) therefore parametrize every
parent world near this point by $(r,b)$.

For completeness the denominator-cleared source identity is

$$
\begin{gathered}
X=bj,\quad N=bn,\qquad
N_4=2(b^2+8b+4)XN-4bTU(X+N)=TUXN\Lambda,\\
5b(p-24)N_4+6(8b-1)H(r,b)=0.
\end{gathered}
\tag{27.10}
$$

It follows either by inserting (25.3) in the fifth response or by
O, (12.8); it is valid on the parent before any division. At the H
point under consideration $N_4\ne0$, so

$$
p-24=-\frac{6(8b-1)}{5bN_4}H(r,b).
\tag{27.11}
$$

Since $H_b>0$ on this graph, (27.11) gives $dp\ne0$ there.
Along its tangent $dp=0$, whereas F, (28.19), gives $d\ell/dr>0$.
Thus $(p,\ell)$ has rank two and is a local diffeomorphism, proving
local injectivity of $\Psi_M$. The strict K/H union exhausts all cases.
The omitted central world is treated by the full-parent saturation
F, Theorem 27.2: in one neighbourhood of $W_c$, every distinct pair
with equal $\Psi_M$ is a K mirror pair, hence has $p=24$. ∎

## 28. Isolation at every closed distinct mirror pair

**Theorem 28.1 (Closed endpoint mirror isolation).** At every ordered
pair in (26.13), there is a product neighbourhood in complete-coefficient
space such that every equal-$\Psi_M$ pair of strict parent worlds in it
has $p=24$. This includes both orderings of the endpoint pair
$\{\overline{\mathcal K}(1/8),\overline{\mathcal K}(1)\}$.

Proof. For strict pairs this is O, Theorem 16.5, with $u=v$ and
$f=m$. To include the endpoints, use the actual analytic circuit,
not an extension of source legality. At $b=1/8,e=0$ and
$r\in\{1/8,1\}$, all of $b,j,n,T,U$ stay positive.
Thus (25.2)–(25.3) extend analytically to an open ambient neighbourhood,
with $c=r(1-r)/b$. The nonzero derivative $(R_0)_b=448/25$ still
provides dependent $b=b(r,e)$. The whole-gain interpolation is analytic
there. Its inverse on tuples is coordinate extraction $(r,e)=(P_{11},d-24)$,
so every nearby strict parent world is represented in this chart.
Nonstrict ambient points are used only for local uniqueness.

Put $s=9/8-r$, $n=n(r)=n(s)$, $j_r=n-r$, $j_s=n-s$, and

$$
R(n)=-8192n^3+119952n^2-12320n-57875.
\tag{28.1}
$$

The derivatives of Lemma 27.1 can equivalently be written

$$
\begin{aligned}
\alpha&=a_0+a_1/j,&
a_0&=\frac{-512n^2-218n+475}{42n},&
a_1&=\frac{85(4n+5)}{84},\\
\eta&=e_0-c_0/j,&
e_0&=\frac{10240n^2+33924n-32375}{140n},&
c_0&=\frac{1672n+7455}{70}.
\end{aligned}
\tag{28.2}
$$

Here $e_0$ is just a rational coefficient, not the drift variable.
The exact coefficient identity

$$
\begin{aligned}
&4(-512n^2-218n+475)(1672n+7455)\\
&\quad +(340n+425)(10240n^2+33924n-32375)\\
&=57344n^3-839664n^2+86240n+405125=-7R(n)
\end{aligned}
\tag{28.3}
$$

gives $a_0c_0+a_1e_0=-R(n)/(1680n)$ and hence

$$
\alpha(r)\eta(s)-\alpha(s)\eta(r)
=\frac{(s-r)R(n)}{1680n j_rj_s}.
\tag{28.4}
$$

On closed mirrors,

$$
\begin{gathered}
n=85/32-8(r-9/16)^2,\qquad 9/8\le n\le85/32,\\
R(9/8)=273661/4,\\
R'(n)=-24576n^2+239904n-12320\\
\hphantom{R'(n)}\ge-24576(85/32)^2+239904(9/8)-12320=84172>0.
\end{gathered}
\tag{28.5}
$$

Thus $R(n)>0$ throughout the required closed interval.
Consider $F=(p-p',k-k',v-v')$ with free variable $r$ and unknowns
$(e,e',s)$. Writing $\zeta=\partial_ev$, its unknown-variable Jacobian
at the mirror is

$$
\begin{pmatrix}
\alpha(r)&-\alpha(s)&0\\
\eta(r)&-\eta(s)&0\\
\zeta(r)&-\zeta(s)&-24n'(s)
\end{pmatrix}.
\tag{28.6}
$$

The entries in the last column follow from (25.6).
For an explicit whole-gain derivative for the remaining entries one has
$\zeta=1+(n+5/2)\gamma_6+24\{5-64r(1-r)\}b_e$,
with $\gamma_6,b_e$ in (27.4)–(27.5).
Using $n'(s)=-8(s-r)$ and (28.4), the determinant is

$$
\det D_{(e,e',s)}F
=-\frac{4(s-r)^2R(n)}{35n(n-r)(n-s)}\ne0.
\tag{28.7}
$$

At $(r,s)=(1/8,1)$ this is exactly

$$
\det D_{(e,e',s)}F=-\frac{1915627}{45}.
\tag{28.8}
$$

All denominators are positive at both endpoint orderings; the same
formula also treats every distinct strict mirror.
The implicit function theorem on the open ambient chart gives a unique
nearby zero $(e,e',s)$ for each nearby $r$ and describes all nearby zeros.
The explicit curve $(e,e',s)=(0,0,9/8-r)$ is already such a zero.
Therefore it is the entire local matching curve. Restrict back to strict
parent worlds: all its members have $p=24$. The two base tuples are
distinct, so their neighbourhoods may also be chosen disjoint.
This proves endpoint isolation without admitting a boundary tuple as an
actual world. ∎

## 29. A uniform fifth-response gap for the entire actual M-pair relation

**Theorem 29.1 (P24-gap).** There exists $\epsilon>0$ such that, for
all real $p,v$,

$$
0<|p-24|<\epsilon\quad\Longrightarrow\quad
\left[W,W'\in C(p,v),\ m(W)=m(W')\ \Longrightarrow\ W=W'\right].
\tag{29.1}
$$

Equivalently, with $D_M$ exactly as in Definition 1.2,

$$
24\notin\overline{\{p\in\mathbb R:\exists v\in\mathbb R,
\ (p,v)\in D_M\}}.
\tag{29.2}
$$

The same $\epsilon$ works for every real $v$ on the entire actual child,
including all singular parent sources, zero drift, lower degrees,
repeated gain roots and sampled gain roots.

Proof. Suppose (29.1) fails for every positive $\epsilon$.
Choose $p_i\ne24$, $p_i\to24$, real $v_i$, and actual distinct pairs
$W_i,W'_i\in C(p_i,v_i)$ with $m(W_i)=m(W'_i)$.
Eventually $|p_i|\le25$. Apply the all-actual-pair cap S, Theorem 7.3:
one finite $B_*$ bounds $b$ at both endpoints of every selected pair.
Apply S, Theorem 12.1, with $L=B_*$ and $P=25$.
It bounds $c,d$ and all four padded coefficients of each entire gain,
as well as $v_i$ and the common terminal response. These are bounds
derived from the actual pairs, not imposed source or acquired-base guards.
In particular the argument includes an attempted unbounded-$v$ sequence.

Theorem 14.3, with $P=25,E=M$, gives

$$
\max\{\delta(W_i),\delta(W'_i)\}\ge\eta_{25}>0,
\qquad\delta(W)=\min\{r,1-r,b,c\}.
\tag{29.3}
$$

Relabel within each pair so that $\delta(W_i)\ge\eta_{25}$.
Only one endpoint is anchored; no individual lower bound for the other
endpoint is inferred. The theorem permits $p_i\to24$, by Lemma 14.2.
Finite-dimensional bounded-sequence compactness gives simultaneous
complete-tuple limits $W_i\to X$, $W'_i\to Y$ along a subsequence.
The anchor makes $X$ strict. The original equations, their common fifth
response and their equal $(v,m)$ pass to the limit; a zero limiting gain
is again excluded by the original unequal $0,24$ readings. Thus

$$
X,Y\in\mathcal L_{24},\qquad
\Psi_M(X)=\Psi_M(Y),\qquad X\text{ is strict}.
\tag{29.4}
$$

If $X\ne Y$, Theorem 26.3 identifies them as a closed K mirror pair.
Theorem 28.1 gives a product neighbourhood where every strict matching
pair has $p=24$. Eventually $(W_i,W'_i)$ is in it, contradicting
$p_i\ne24$.

If $X=Y$, this common tuple is strict because $X$ is the anchored limit.
Unless $X=W_c$, Theorem 27.2 gives a single neighbourhood in the full
parent on which $\Psi_M$ is injective. Eventually both endpoints are in
it, contradicting their distinctness. If $X=W_c$, F, Theorem 27.2,
gives a full-parent neighbourhood where every distinct equal-$\Psi_M$
pair is a reflected K pair and therefore has $p=24$, the same contradiction.
There is no case of two boundary limits because the anchor is strict.
These cases exhaust all finite subsequential limits and exclude the
assumed sequence. This proves a positive $\epsilon$ and (29.2). ∎

**Corollary 29.2 (The original joint relation in the same strip).**
For the same $\epsilon$,

$$
(D_J\cap D_M)\cap
\{(p,v):0<|p-24|<\epsilon,\ v\in\mathbb R\}=\varnothing.
\tag{29.5}
$$

Proof. A joint configuration in Definition 1.2 contains a distinct actual
$M$ pair in that same entire child, contradicting Theorem 29.1.
The argument imposes no additional condition on the $J$ pair: the pairs
may overlap or be disjoint, and their two common terminal values may
differ. ∎

## 30. Mathematical suppliers, useful extension and remaining incidence

**Assumption 30.1 (Exact supplier correspondence).** The symbols O, F
and S in Sections 25–29 have the following public meanings and uses.
The statements are used as ordinary mathematical premises at the listed
scopes. The source-specific conclusions here are repository-derived;
no literature-priority assertion accompanies them.

| Public mathematical supplier | Parameter correspondence and scope used |
| --- | --- |
| [O, Definitions 1.1–1.3 and Theorem 2.1](https://github.com/the-omega-institute/trureturing/blob/3350fc26dcbaf210d8ab035c7e25ab99c76e8447/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md) | Exactly the original $P(r,b)$, one whole nonzero degree-at-most-three gain, fixed drift, left products and clocks $0,\ldots,7$. Its $\epsilon$ is $e$ here; its sixth-M $u$ and terminal $f$ are $v,m$. The parent equation and whole-gain reconstruction include singular sources. |
| O, Definition 12.1, Theorem 12.3, (12.8), Definition 13.1 and Theorem 13.2 | The same $X=bj,N=bn,W=bV,N_4,H$ give (25.7), (25.8), (27.10). The strict $p=24$ fibre is exactly the K/H union, with $H_b>0,E_2\ne0$ on the strict H graph. Boundary filters and endpoint lifts are established in Section 26 rather than assumed from the strict theorem. |
| O, Lemmas 16.2–16.4 and Theorem 16.5 | Full-parent $(r,e)$ chart and the whole-gain derivatives. The mirror isolation premise itself has strict endpoint scope; (28.1)–(28.8) and the ambient uniqueness argument supply the closed endpoint extension. |
| [F, Theorem 25.2](https://github.com/the-omega-institute/trureturing/blob/3350fc26dcbaf210d8ab035c7e25ab99c76e8447/docs/develop/theory/FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md) | The strict separator is $e(k-k_0)<0$ outside K. Both additional boundary signs are (26.6)–(26.7). |
| F, Theorem 27.2 | Central saturation is on the full complete parent near $\mathcal K(9/16)$; every distinct equal-$(p,v,m)$ pair there is a K mirror pair at $p=24$. This supplies the central diagonal case, not an immersion assertion at that point. |
| F, Lemma 28.2, Theorem 28.5, (28.19) and Theorem 29.1 | Derived $1<t<2$ for H, and positive derivative of $\ell=m-(24/5)v$ on every strict H point. The strict matching classification is extended to the entire finite closed fibre in Theorem 26.3. |
| [S, Theorem 7.3](https://github.com/the-omega-institute/trureturing/blob/517e0e3f0472caff3dce0352f386789faa7407cf/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md) | One finite $B_*$ bounds $b$ at both endpoints of every actual distinct equal-terminal pair for every real off-$24$ base. It is applied to actual selected $M$ pairs, including all exceptional worlds. |
| S, Theorem 12.1, Definition 12.2 and the finite-exhaustion argument of Theorem 12.3 | For $b\le B_*$ and bounded $|p|$, $c,d$, all four padded gain coefficients and remaining responses are bounded, including $p=24$. The four finite faces and two corners are considered before intersecting with the relative off-$24$ target. |
| This volume, Lemma 14.2 and Theorem 14.3 | Finite exhaustion permits $p_i\to24$. For a bounded-$p$ distinct pair, $\max(\delta,\delta')\ge\eta(P)>0$. Precisely one endpoint is selected as strict anchor; this is not a bound for each endpoint. |

Fixed-node interpolation is used only at the displayed distinct original
nodes; its uniqueness is the classical Lagrange interpolation theorem
([Berrut–Trefethen, §2, (2.1)–(2.2)](https://doi.org/10.1137/S0036144502417715)).
The implicit and inverse function theorems apply on open Euclidean chart
domains with the displayed nonzero dependent-variable determinants
([Lebl, *Basic Analysis II*, Theorem 8.5.6](https://www.jirka.org/ra/realanal2.pdf)).
For the two degree-six polynomials, the Sylvester criterion says that a
common complex root forces a zero resultant; the fixed integer matrix and
its nonzero modular determinant are (27.8)
([Moreno Maza, *The resultant*, Definition 4 and Proposition 5](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html)).
Compactness in Theorem 29.1 is the classical bounded-subsequence theorem
in the finite-dimensional complete-tuple coordinates, after the actual-pair
bounds have been obtained. None of these classical tools by itself asserts
a collision classification or compactness of the original world domain.

**Proposition 30.2 (Extent of the new exclusion).** Theorem 29.1 excludes
all actual off-$24$ terminal-$M$ pair sequences with $p\to24$, uniformly
in their sixth response. Its additional content over the strict $p=24$
classification is the complete finite endpoint filter, the two strict
endpoint separators, the noncentral full-parent immersion certificate,
and the closed endpoint mirror isolation, combined with the actual-pair
cap, coercivity and one-endpoint anchor.

Proof. The finite filter and continuous endpoints are Theorem 26.2;
the separators and closed matching classification are Lemma 26.1 and
Theorem 26.3. Lemma 27.1 and Theorem 27.2 handle every noncentral strict
diagonal limit, while Theorem 28.1 handles distinct closed limits.
The proof of Theorem 29.1 combines these with the listed actual-pair
suppliers and the inherited central saturation, exhausting all limits.
This is stronger than isolation of an individual mirror or a fixed local
source box, because the hypothetical pairs themselves supply the finite
bounds and the same conclusion holds for every real $v$. ∎

No numerical value of $\epsilon$ is specified. The argument gives neither
a global bound on $|p|$ nor global properness nor a positive individual
lower bound on both endpoint $b,c$ entries. Outside the strip, the original
alternative (11.1), a legal shared-child joint witness or an exhaustive
all-real exclusion, remains unresolved. Strict interior components and
isolated incidences, the remaining finite-face and critical limits, and
unbounded acquired-base limits must still be treated with their actual
whole-world guards. In particular the earlier unresolved $p\to24$
mechanism in Section 24 is excluded by Theorem 29.1, while these other
parts of that original joint objective remain.

The permission for the two selected terminal pairs to overlap or be
disjoint, and for their common terminal values to differ, remains exactly
Definition 1.2. No terminal alternative is an acquired port, and no source,
gain, drift, clock or observation permission has changed. The original
complex-density and common-terminal CPTP/identity-target conditions, where
required by an ancestor statement, remain separate obligations. No physical
realization, ancestor conjunction, fifth-$M$ $L_2$, $H_4$ $L_3$, root $L_7$
or eight-versus-nine conclusion follows from this strip exclusion.

## 追加锚（本行以下为增补区）

