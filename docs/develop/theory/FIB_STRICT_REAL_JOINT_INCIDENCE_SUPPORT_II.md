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
