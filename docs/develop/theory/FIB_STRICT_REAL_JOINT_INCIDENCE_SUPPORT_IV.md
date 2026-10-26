# FIB strict-real joint incidence: finite source boundaries

## 1. Worlds, original clocks and the two conclusions

**Definition 1.1 (Complete worlds and entire children).** Let
[O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
[F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
[S](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md),
[SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md) and
[III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md) denote the preceding
owners. Use their original complete worlds

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
$$

There is one fixed drift and one whole polynomial per world. Set

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
$$

The acquired actions are $J,M,J,M,M,M$, and the readings at the original
clocks $0,\ldots,6$ are $(0,24,147/5,24,18,p,v)$. The entire child
$C(p,v)$ consists of all complete worlds with these readings. At clock
seven define the two alternatives on this same world by

$$
a(W)=d+g(7)\operatorname{tr}(JQ_6P),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
$$

Lower gain degrees, zero drift, zero gain samples, repeated roots and
singular sources are included. Distinctness always means distinct
complete triples. An original joint configuration means precisely

$$
\begin{gathered}
p\ne24,\quad W_0,W_1,W_2,W_3\in C(p,v),\\
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\end{gathered}
\tag{1.1}
$$

The pairs may overlap and their common terminal values may differ.
Worlds unused by the pairs remain members of the entire child.

**Definition 1.2 (Undivided parent coordinates).** Write

$$
\begin{gathered}
j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad e=d-24,\\
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\kappa=\frac6T-\frac2U=\frac{2(2+5b)}{TU},\\
D_b=\frac{24}{5}(b-1/8)\kappa,\qquad H=e\Lambda+D_b.
\end{gathered}
\tag{1.2}
$$

O, Theorem 2.1, and III, Definition 1.2 and Lemma 10.2, give the exact
full-parent correspondence $H=0$. Its gain is the unique polynomial of
degree at most three with values

$$
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right)
\quad\text{at }0,1,2,3.
\tag{1.3}
$$

The traces at clocks $0,\ldots,6$ are $(1,j,T,n,U,U+n,2U+n)$;
the two terminal traces are $T+2j+4r$ and $3U+2n$. Thus

$$
p=d+(U+n)g(5),\quad v=d+(2U+n)g(6),\quad
m=d+(3U+2n)g(7).
\tag{1.4}
$$

All parent equations below retain $H=0$ without dividing by $e$ or
$\Lambda$. Nonstrict source labels are auxiliary limits, not worlds.

**Definition 1.3 (Two finite faces).** For $t>0$ the labels
$B_0(t)=(r,b,c)=(0,0,t)$ and $C_0(t)=(0,t,0)$ have $j,n,T,U>0$.
A finite complete boundary tuple means such a source, a finite drift,
and the whole interpolant (1.3), satisfying the undivided parent and
original reading equations. It does not satisfy strict source positivity.

The first conclusion below excludes a strict terminal-$M$ companion
to every finite off-$24$ $C_0$ tuple. Its consumer bounds both selected
$M$ endpoints of (1.1). The second conclusion concerns every world in
every child above $K=[56,58]\times[304,305]$, independently of any pair.
It retains the face $C_1=\{r=1,b>0,c=0\}$.

## 2. The finite positive C0 circuit and original-world guards

**Definition 2.1 (Boundary response functions).** Put

$$
\begin{aligned}
q&=t^3-8t-4,\qquad q_5=5q,\\
p_n&=-3(72t^3+746t^2+465t+130),\\
v_n&=-3(375t^3+4431t^2+2486t+344),\\
m_n&=-3(1088t^3+16523t^2+9445t+1318).
\end{aligned}
\tag{2.1}
$$

For $t>0,q\ne0$ let $(p_0,v_0,m_0)=(p_n,v_n,m_n)/q_5$ and

$$
e_0=-\frac{3t(8t-1)(5t+2)}{5q},\qquad d_0=24+e_0.
\tag{2.2}
$$

The $C_0(t)$ gain is the interpolant (1.3) with
$(j,n,T,U)=(t,t,1+t,1+2t)$ and $e=e_0$. Substitution in the original
rows gives exactly $(p_0,v_0,m_0)$. In particular

$$
p_0-24=-\frac{3(8t-1)(14t^2+95t+30)}{5q}.
\tag{2.3}
$$

Thus off $24$ means $t\ne1/8$. At this face

$$
\Lambda=\frac{2q}{t(1+t)(1+2t)},\qquad
-D_b=-\frac{6(5t+2)(8t-1)}{5(1+t)(1+2t)}.
\tag{2.4}
$$

Since $q$ is coprime to $(8t-1)(5t+2)$, a zero of $q$ cannot give
a finite complete face tuple. The ordinary polynomial gcds of $q$ with
$p_n,v_n,m_n$ are all $1$.

**Definition 2.2 (Late-node interpolation and necessary equations).**
At a hypothetical actual companion put $x=n/U>0$ and
$D=x(x+1)(x+2)$. Let $\mathcal H=Ug$ be interpolated at $3,4,5,6$
from $((24-d)/x,18-d,(p-d)/(x+1),(v-d)/(x+2))$. Define

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
\begin{pmatrix}a_0\\a_1\\a_2\\a_7\end{pmatrix}
=\begin{pmatrix}
20&-45&36&-10\\10&-20&15&-4\\4&-6&4&-1\\-1&4&-6&4
\end{pmatrix}
\begin{pmatrix}z_3\\z_4\\z_5\\z_6\end{pmatrix}.
\end{gathered}
\tag{2.5}
$$

Then $\mathcal H_i=a_i/D$ for $i=0,1,2,7$. Set

$$
\begin{aligned}
z&=xa_1-D(24-d),& b_s&=(294-10d)D-5a_2,\\
A_q&=4z^2-2za_1+(2x-1)a_1^2,&
E_q&=-2za_1+2(1-x)a_1^2,\\
\mathcal Q(u,w)&=A_qu^2+E_quw-a_1^2w^2,\\
f&=5dDa_2+a_0b_s,& K_d&=\mathcal Q(-a_0,dD),\\
K_s&=25K_d+\mathcal Q(5a_2,b_s).
\end{aligned}
\tag{2.6}
$$

These names do not change the source coordinate $b$ or the base box $K$.
The original clocks zero and two give

$$
dDU=-a_0,\qquad b_sU=5a_2.
\tag{2.7}
$$

The source relation gives, by expansion,

$$
\mathcal Q(U,1)
=4a_1^2\{b(j-b)-r(1-r)\}=0.
\tag{2.8}
$$

Indeed clock one gives $j=U(24-d)D/a_1$, and $r=Uz/a_1$.
Multiplying $f$ by $U$ in (2.7), and using homogeneity in (2.8), gives

$$
f=0,\qquad K_d=(dD)^2\mathcal Q(U,1)=0,\qquad
\mathcal Q(5a_2,b_s)=b_s^2\mathcal Q(U,1)=0.
\tag{2.9}
$$

No division by $d$ or $b_s$ occurs, so their zero branches are retained.

**Definition 2.3 (Whole-world guard functions).** In the off-$24$ child
F, Lemma 30.2, gives precisely the following necessary and sufficient
conditions on $(x,d)$, with the interpolation above:

$$
\begin{gathered}
x>0,\quad d\ne24,\quad \mathcal H_1\ne0,\quad
B_*={294\over5}-2d-\mathcal H_2,\quad C_*=d^2+B_*^2>0,\\
U={-d\mathcal H_0+B_*\mathcal H_2\over C_*}>1,\quad
b={U-1\over2},\quad j={U(24-d)\over\mathcal H_1},\quad r=xU-j,\\
0<r<1,\quad j=b+{r(1-r)\over b},\quad
dU=-\mathcal H_0,\quad B_*U=\mathcal H_2.
\end{gathered}
\tag{2.10}
$$

For completeness, $d=24$ on the original parent forces $b=1/8$ and
$g(s)=\frac85(s-1)(s-3)(s-5)$, whose fifth reading is $24$.
Thus off $24$ gives $d\ne24$ and
$\mathcal H_1=U(24-d)/j\ne0$. If $d=B_*=0$, the last equation
would give $\mathcal H_2=0$, whereas the definition of $B_*$ would
give $\mathcal H_2=294/5$. Hence $C_*>0$. These facts explain all
denominators in (2.10), including at $d=0$. The reconstruction is one
entire $g=\mathcal H/U$. Polynomial equations (2.9) alone do not
replace these guards.

**Definition 2.4 (Undivided terminal equation).** Put

$$
\begin{aligned}
\phi(x)&=8x^4+29x^3+18x^2-15x-6,\\
L(t,x)&=240qx^4+(-48t^3-9973t^2-12863t-3874)x^3\\
&\quad+(-12t^3-7719t^2-11455t-2266)x^2\\
&\quad+(468t^3+6730t^2+4198t+2388)x-240q,\\
h(t,x)&=(2t+1)x-t.
\end{aligned}
\tag{2.11}
$$

Using $p=p_0,v=v_0$ in (2.5) gives the exact rational identity

$$
dD+(2x+3)a_7-m_0D=-\phi(x)d+\frac{3L(t,x)}{5q}.
\tag{2.12}
$$

It follows by collecting coefficients of $d$ and $x$ in (2.5).
The left side is $D(m-m_0)$ by the original terminal trace.
In particular when $\phi=0$, the equation is $L=0$ for every drift;
solving for $d$ is restricted to $\phi\ne0$.

## 3. Integer elimination circuits and characteristic-zero identities

**Definition 3.1 (Primitive integer F and G).** Let $N=3L$ and
$B=5q\phi$. Apply the four rows of (2.5) to

$$
\big((24B-N)(x+1)(x+2),\ (18B-N)D,\
(p_n\phi-N)x(x+2),\ (v_n\phi-N)x(x+1)\big)
$$

and call the outputs $\bar a_0,\bar a_1,\bar a_2,\bar a_7$.
They equal $Ba_i$ after substituting $d=N/B$. Define

$$
\begin{aligned}
Z&=x\bar a_1-D(24B-N),\\
B_s&=(294B-10N)D-5\bar a_2,\\
\bar A&=4Z^2-2Z\bar a_1+(2x-1)\bar a_1^2,\\
\bar E&=-2Z\bar a_1+2(1-x)\bar a_1^2,\\
F&=-{5ND\bar a_2+\bar a_0B_s\over90D^2h},\\
G&={\bar A\bar a_0^2-\bar E\bar a_0ND-\bar a_1^2N^2D^2
\over324D^4h}.
\end{aligned}
\tag{3.1}
$$

Both displayed polynomial divisions have remainder zero in
$\mathbb Z[x,t]$. The quotients have integer content $1$, coordinate
degrees $(\deg_x,\deg_t)=(6,5),(13,11)$, and leading coefficients in
lexicographic order $(x,t)$ equal to $3100856$ and
$191397636974083200$, respectively. Thus (3.1), including its signs
and scalar divisors, specifies every coefficient without a coefficient
file. In the branch $q\phi Dh\ne0$, (2.9) implies $F=G=0$.

**Definition 3.2 (Determinantal conventions).** For polynomials $P,Q$
in $x$, with nominal degrees $m\ge n$, define $\operatorname{Subres}_k(P,Q)$
as follows. Make the $(m+n-2k)$ by $(m+n-k)$ coefficient matrix of

$$
x^{n-k-1}P,\ldots,P,\quad x^{m-k-1}Q,\ldots,Q
$$

in descending powers $x^{m+n-k-1},\ldots,1$ (the last column is the
constant coefficient). If $N_k=m+n-2k$, its $x^j$ coefficient, for
$0\le j\le k$, is the determinant of the first $N_k-1$ columns
followed by column $N_k+k-1-j$, with columns indexed from zero.
For $k=0$ this is the ordinary Sylvester determinant. For $(F,G)$
use $(P,Q)=(G,F)$, nominal degrees $(13,6)$. For $(\phi,3L)$ use
that order and nominal degrees $(4,4)$. These conventions specify
polynomial combinations of the two inputs and remain fixed under
specialization, including degree drops.

For an explicit finite-root justification, if $\xi$ is a common root,
all rows of this coefficient matrix evaluate to zero at $x=\xi$.
The value of its minor polynomial at $\xi$ is the determinant whose
last column is the sum of the degree-$j$ columns times $\xi^j$ for
$0\le j\le k$. The vanishing row evaluations identify that column
with a linear combination of the first $N_k-1$ columns. Its determinant
is therefore zero. This proves the finite-common-root implication for
every specialization directly, without division by a leading coefficient.

Write

$$
S_1=A_1(t)x+B_1(t),\quad
S_2=c_2(t)x^2+c_1(t)x+c_0(t),\quad
T_1=\operatorname{Subres}_1(\phi,3L).
\tag{3.2}
$$

Here $S_i=\operatorname{Subres}_i(G,F)$. The nonzero subresultant
sequence has $x$ degrees $13,6,5,4,3,2,1,0$. The sign of
$\operatorname{Res}_x(F,G)$ equals that of
$\operatorname{Res}_x(G,F)$ because $6\cdot13$ is even.

**Definition 3.3 (Small factors and linear pole coefficients).** A
descending coefficient list means $[a_m,\ldots,a_0]$ represents
$\sum_{i=0}^m a_it^i$. The lists defining $Q_4,Q_7,Q_8,P_A,P_B$
are given below.

$$
\operatorname{coeff}_{\downarrow}(Q_4)=\big(
78,\;
271,\;
216,\;
63,\;
6\big).
$$

$$
\operatorname{coeff}_{\downarrow}(Q_7)=\big(
2248108288,\;
2116736408,\;
-116022490098,\;
2825003932935,\;
7309983134450,\;
4939059056625,\;
1498584912500,\;
142415812500\big).
$$

$$
\operatorname{coeff}_{\downarrow}(Q_8)=\big(
1174435344,\;
14858926416,\;
-350876792079,\;
-6257853655238,\;
-24562948859487,\;
-2398014791788,\;
874314177232,\;
38886384144,\;
-7117566352\big).
$$

$$
\operatorname{coeff}_{\downarrow}(P_A)=\big(
3733241472,\;
69264877464,\;
108628397766,\;
-3230457691165,\;
-11929621379757,\;
-8276192383035,\;
-1808097306619,\;
-6523197690,\;
38079735948,\;
2975203704\big).
$$

$$
\operatorname{coeff}_{\downarrow}(P_B)=\big(
633094560,\;
-34715451528,\;
-903017678544,\;
-6014484926998,\;
-11407712933622,\;
-5719623664386,\;
-765461657902,\;
51493306716,\;
15119830584,\;
689159280\big).
$$

**Definition 3.4 (The degree-forty-one quotient and its interval coordinates).**
Define $Q_{41}$ by the exact quotient

$$
Q_{41}(t)=\frac{\operatorname{Res}_x(F,G)}
 {544195584Q_4(t)^3Q_7(t)^2Q_8(t)^8}.
\tag{3.3}
$$

Polynomial division has zero remainder; the resultant has degree $131$,
the quotient has degree $41$, and its leading coefficient is

$$
425040827886114912019469507865702445684112358499105647335920976702592.
$$

This exact quotient, rather than a numerical interpolation, defines all
its coefficients. The coefficient gcd of $A_1,B_1$ in $\mathbb Z[t]$
is $3456Q_8^3$, with positive leading coefficient. Set

$$
\begin{aligned}
a^\circ&=\operatorname{rem}_{Q_{41}}\left(A_1/(3456Q_8^3)\right),\\
b^\circ&=\operatorname{rem}_{Q_{41}}\left(B_1/(3456Q_8^3)\right),\\
\mathfrak a&=a^\circ/\operatorname{lc}(a^\circ),\qquad
\mathfrak b=b^\circ/\operatorname{lc}(a^\circ).
\end{aligned}
\tag{3.4}
$$

Both have degree $40$; $\mathfrak a$ is monic. At a $Q_{41}$ root
where the linear coefficient is nonzero, $x=-\mathfrak b/\mathfrak a$.
All remainders in this section are over $\mathbb Q$ unless a finite
field is explicitly indicated.

**Theorem 3.5 (Exact model-specific elimination identities).** The
circuits above satisfy

$$
\begin{gathered}
\operatorname{Res}_x(F,G)=544195584Q_4^3Q_7^2Q_8^8Q_{41},\\
\operatorname{Res}_x(\phi,3L)=-279936Q_4Q_8,\qquad
T_1=1296(P_Ax+P_B),\\
\operatorname{rem}_{Q_8}(P_Ac_1-2P_Bc_2)=0,\qquad
\operatorname{rem}_{Q_8}(P_A^2c_0-P_B^2c_2)=0.
\end{gathered}
\tag{3.5}
$$

In particular the characteristic-zero congruence is

$$
P_A^2S_2\equiv c_2(P_Ax+P_B)^2\pmod{Q_8}.
\tag{3.6}
$$

Proof. The following finite arithmetic specifies coefficient-by-coefficient
verification of these identities. Expand the four interpolation rows in
(3.1), multiply out the two numerators, and divide by the displayed
polynomials using descending monomials in $(x,t)$. The remainders are
zero and the quotient contents and leading terms are those in Definition
3.1. Form the determinants of Definition 3.2; division of the constant
subresultant by the denominator in (3.3) gives remainder zero and the stated
leading coefficient. For the second pair of inputs the same determinants
give the second and third identities of (3.5), with the lists of
Definition 3.3. Finally extract $c_2,c_1,c_0$ from the quadratic
minor determinant. Euclidean division in $\mathbb Q[t]$ of
$P_Ac_1-2P_Bc_2$ and $P_A^2c_0-P_B^2c_2$ by the listed $Q_8$
gives the zero polynomial in each case. Thus these two equalities are
exact characteristic-zero coefficient identities. Their deterministic
inputs consist solely of (2.1), (2.5), (2.11), (3.1), the specified
minor determinants and the five short coefficient lists. No modular
agreement is used to infer a zero rational remainder. Comparing the
coefficients of $x^2,x,1$ now gives (3.6).

The quadratic subresultant here is $S_2$ of $(G,F)$. It is not the
quadratic subresultant of $(\phi,3L)$; that different polynomial is
not used in (3.6). ∎

**Definition 3.6 (Quotient norms and a unit certificate).** For a monic
polynomial $Q$ of degree $k$ over a field, write

$$
\mathcal N_Q(f)=\det\big([\operatorname{rem}_Q(t^if)]_{i=0}^{k-1}\big),
\tag{3.7}
$$

where each bracket is a column of ascending coefficients in the basis
$1,t,\ldots,t^{k-1}$. This determinant is the multiplication norm.
For reduction modulo $101$, first multiply the reduction of $Q$ by the
inverse of its leading coefficient to make it monic. The public
circuits give the following residues:

| Modulus | Leading coefficient modulo $101$ | Element | Norm modulo $101$ |
| --- | --- | --- | --- |
| $Q_{41}$ | $38$ | $A_1$ | $12$ |
| $Q_{41}$ | $38$ | $q$ | $95$ |
| $Q_8$ | $72$ | $P_A$ | $71$ |
| $Q_8$ | $72$ | $q$ | $85$ |
| $Q_8$ | $72$ | $c_2$ | $20$ |

For instance each entry is computed by reducing the indicated expression
from the coefficient circuits, multiplying successively by $t$, reducing
again, and taking the determinant (3.7) in $\mathbb F_{101}$.
Nonzero leading residues make the monic quotients finite free over
$\mathbb Z_{(101)}$. The nonzero determinants imply nonzero rational
multiplication determinants, hence units over $\mathbb Q$. In
particular $A_1,q$ are nonzero at every complex $Q_{41}$ root, and
$P_A,q,c_2$ are nonzero at every complex $Q_8$ root. This lifts
nonvanishing, not a polynomial equality inferred from a congruence.

## 4. The undivided pole branch

**Definition 4.1 (Cleared equations before drift substitution).** In
(2.5), with $p=p_n/q_5,v=v_n/q_5$, put $A_i=q_5a_i$ and define

$$
\begin{aligned}
Z_c&=xA_1-q_5D(24-d),\\
B_c&=(294-10d)Dq_5-5A_2,\\
A_c&=4Z_c^2-2Z_cA_1+(2x-1)A_1^2,\\
E_c&=-2Z_cA_1+2(1-x)A_1^2,\\
f_c&=5dDA_2q_5+A_0B_c,\\
K_c&=A_cA_0^2-E_cA_0dDq_5-A_1^2d^2D^2q_5^2,\\
K_{sc}&=25K_c+25A_cA_2^2+5E_cA_2B_c-A_1^2B_c^2.
\end{aligned}
\tag{4.1}
$$

Here $A_1=q_5a_1$ is local to this cleared circuit, not the linear
coefficient in (3.2). Equivalently
$f_c=q_5^2f$, $K_c=q_5^4K_d$ and $K_{sc}=q_5^4K_s$.
The distinction avoids any division by $d$, $b_s$ or their leading
coefficients.

**Definition 4.2 (Fixed degree-(2,4) pole determinant).** In
$\mathcal A=\mathbb Q[t]/(Q_8)$ substitute $x=-P_B/P_A$ in (4.1).
The inverse exists by Definition 3.6. Write

$$
f_c=f_2d^2+f_1d+f_0,\qquad
K_{sc}=g_4d^4+g_3d^3+g_2d^2+g_1d+g_0,
$$

and set

$$
R=\det\begin{pmatrix}
f_2&f_1&f_0&0&0&0\\
0&f_2&f_1&f_0&0&0\\
0&0&f_2&f_1&f_0&0\\
0&0&0&f_2&f_1&f_0\\
g_4&g_3&g_2&g_1&g_0&0\\
0&g_4&g_3&g_2&g_1&g_0
\end{pmatrix}.
\tag{4.2}
$$

This matrix is fixed before specialization. A finite common root $d$
annihilates its nonzero column $(d^5,d^4,d^3,d^2,d,1)^{\mathsf T}$,
including at any specialized degree drop.

The following expressions are all in $\mathbb F_{101}[t]$. Its monic
modulus and the substituted $x$ are

$$
\begin{aligned}
\bar Q&=t^8-29t^7+43t^6-5t^5-13t^4+41t^3-39t^2+23t-14,\\
\bar x&=12t^7+46t^6-7t^5-34t^4+43t^3-45t^2-35t+32.
\end{aligned}
\tag{4.3}
$$

The ascending $d$ coefficient lists of (4.1), after reduction by
$\bar Q$ and substitution of $\bar x$, are as follows. Each row is
an entire polynomial in $t$.

$$
\begin{aligned}
f_0&=19t^7+39t^6+12t^5-44t^4-27t^3-11t^2-47t+9,\\
f_1&=36t^7-47t^6+11t^5-38t^4-4t^3-43t^2-3t-41,\\
f_2&=3t^7+10t^6+46t^5+26t^4+15t^3-4t^2+43t+28,\\
g_0&=15t^7-18t^6-36t^5-23t^4-11t^3-10t^2+16t+50,\\
g_1&=46t^7+10t^6+50t^5+16t^4-t^3+13t^2+8t-7,\\
g_2&=-31t^7+22t^6-46t^5+17t^4-40t^3-33t^2+46t-17,\\
g_3&=-22t^7-17t^6-49t^5+41t^4-28t^3+28t^2+42t+22,\\
g_4&=6t^7-6t^6+47t^5+43t^4+23t^3+21t^2-45t+39.
\end{aligned}
\tag{4.4}
$$

In this display only, $f_i,g_i$ denote their reduced residues. Taking
(4.2) by determinant expansion and reducing its entries and products
modulo $\bar Q$ gives

$$
\bar R=-28t^7-9t^6+17t^5+32t^4+34t^3+19t^2+45t-49.
\tag{4.5}
$$

A polynomial Bézout certificate, before taking any quotient, is

$$
\begin{aligned}
u&=-28t^6+48t^5+25t^4+22t^3-27t^2-10t+16,\\
w&=-t^7+13t^6+8t^5-36t^4-23t^3-11t^2+43t+49,\\
u\bar Q+w\bar R&=1\quad\text{in }\mathbb F_{101}[t].
\end{aligned}
\tag{4.6}
$$

The multiplication determinants (3.7) provide the further exact values

| Element in $\mathbb F_{101}[t]/(\bar Q)$ | $P_A$ | $q$ | $D(\bar x)$ | $f_2$ | $g_4$ | $\bar R$ |
| --- | --- | --- | --- | --- | --- | --- |
| Norm | $71$ | $85$ | $52$ | $68$ | $23$ | $73$ |

**Theorem 4.3 (No finite pole companion).** If $t>0,q\ne0$ and a
finite real $x>0$ satisfies $\phi(x)=L(t,x)=0$, the original
necessary equations $f=K_s=0$ have no finite real drift solution.

Proof. The second resultant in (3.5) and the positive coefficients of
$Q_4$ give $Q_8(t)=0$. The polynomial combination $T_1$ gives
$P_Ax+P_B=0$, since $P_A$ is a unit. Thus the substitution in
Definition 4.2 applies.

To justify its characteristic-zero conclusion, take the monic form of
$Q_8$ over $\mathbb Z_{(101)}$. Its leading coefficient has residue
$72$, and the norm of $P_A$ has residue $71$. Hence $P_A$ has an
inverse in this finite free algebra already over $\mathbb Z_{(101)}$.
All scalar denominators in (4.1) and the monic division are prime to
$101$. Substitution and determinant formation therefore commute with
reduction. The coefficient rows (4.4) follow from the cleared circuit
by ordinary polynomial substitution; expanding (4.2) gives (4.5).
Multiplying the polynomials in (4.6) gives $1$ coefficient for coefficient.
The norm table is also determined by (3.7), so the norm of $R$ is a
nonzero rational number, having nonzero residue $73$.
Consequently $R$ is a unit in $\mathcal A$ and cannot vanish at any
complex $Q_8$ root. The norms of $f_2,g_4$ also preserve their exact
degrees $2,4$ there; the fixed matrix itself requires no such
specialized-degree assumption for its common-root implication.

An original solution would give $f_c=K_{sc}=0$ since $q_5\ne0$.
The column following (4.2) would force $R(t)=0$, a contradiction.
This argument covers $d=0$, $b_s=0$ and every finite drift without
solving for drift in the terminal equation. ∎

## 5. Exact positive-root and original-guard intervals

For a rational polynomial $P(t)$ define its sign-preserving primitive
Sturm chain by $P_0=\operatorname{pp}_+(P)$,
$P_1=\operatorname{pp}_+(P_0')$ and

$$
P_{i+1}=\operatorname{pp}_+\big(-\operatorname{rem}(P_{i-1},P_i)\big).
\tag{5.1}
$$

Here $\operatorname{pp}_+$ multiplies by the positive least common
multiple of coefficient denominators and divides by the positive
integer coefficient gcd; it never changes sign to make a leading
coefficient positive. Stop at zero remainder. Let $V_P(s)$ count
sign changes after zeros are deleted. At $+\infty$ use leading
coefficient signs, and at zero use constant coefficients. This specifies
all chain coefficients directly from the public polynomials. The chains
for $Q_7,Q_{41}$ have respectively $8,42$ entries and end in nonzero
constants. Their variations are

| Polynomial | $V(0)$ | $V(+\infty)$ | Number of positive roots |
| --- | --- | --- | --- |
| $Q_7$ | $2$ | $2$ | $0$ |
| $Q_{41}$ | $16$ | $11$ | $5$ |

The constant last entries also show that these roots are simple.

For clarity, endpoint signs are reproducible using only integers.
If $P=\sum_{i=0}^m c_it^i$ has integer coefficients and $t=N/B$,
start $v=c_m$ and $B_1=B$, and successively replace
$v$ by $Nv+c_iB_1$ and $B_1$ by $BB_1$, descending in $i$.
The final integer is $B^mP(N/B)$ and has its sign. Apply this to
every chain entry in (5.1).

For the following rational intervals use a mesh $S=10^{240}$. A
rational number is enclosed by rounding its two endpoints down and up
to multiples of $1/S$. Addition and negation use endpoint arithmetic;
multiplication takes the minimum and maximum of the four endpoint
products and rounds outwards. Division takes the four endpoint quotients
and rounds outwards only after the denominator interval excludes zero.
Polynomial evaluation uses descending Horner arithmetic with each
rational coefficient enclosed on this mesh. Powers use repeated
multiplication. Thus all interval operations are specified by integer
floor and ceiling division, not floating point.

The input $t$ intervals have denominator $10^{160}$. If a row has
left numerator $N_i$ and width $w_i$, it is exactly
$[N_i,N_i+w_i]/10^{160}$. The five left numerators are given separately
to avoid abbreviating any endpoint.

$$
N_1=595223049848269525903835694474010185613209628421953204257640295228930387704218594188372305766830664337406800022353170344183261419106672060169523298600093312317.
$$

$$
N_2=615308652899767922362714318304887371029197823616936109006727412869596795528077193570630493149987812956316760587882811101549719375741356322710393040905700019958.
$$

$$
N_3=1551737322754159711870171523724096973113270550505567286351285738379027967942583207550463087052056123740537966944014999041877203578055532019943054929484251055942.
$$

$$
N_4=1779893347973634001522723825175127416732001452172025859018464054140363992492683858744240261031471597346190493170316263460866232515929040992598105348855781153250.
$$

$$
N_5=39519945614478191480604197722730289434525982527519393832474336376723521872673460805110039526325398374904530613738186163809793843268553936143607377060033124795596.
$$

| Root | $w_i$ | $V(N_i/10^{160})$ | $V((N_i+w_i)/10^{160})$ | Endpoint signs of $Q_{41}$ |
| --- | --- | --- | --- | --- |
| $1$ | $2$ | $16$ | $15$ | $(-1,1)$ |
| $2$ | $2$ | $15$ | $14$ | $(1,-1)$ |
| $3$ | $1$ | $14$ | $13$ | $(-1,1)$ |
| $4$ | $2$ | $13$ | $12$ | $(1,-1)$ |
| $5$ | $1$ | $12$ | $11$ | $(-1,1)$ |

The following endpoint pairs are divided by $10^8$. Every row encloses
the indicated rational guard function on the whole corresponding input
interval, rather than only its algebraic root.

| Root | $x$ | $d$ | $U$ | $r$ | Failed original guard |
| --- | --- | --- | --- | --- | --- |
| $1$ | $[3768335,3768336]$ | $[2398942866,2398942867]$ | $[115761459,115761460]$ | $[108137144,108137145]$ | $r<1$ |
| $2$ | $[-815098,-815097]$ | $[2400466649,2400466650]$ | $[128844791,128844792]$ | $[-1918095,-1918094]$ | $x>0$ |
| $3$ | $[66065884,66065885]$ | $[2963406503,2963406504]$ | $[-28678168,-28678167]$ | $[-39076866,-39076865]$ | $U>1$ |
| $4$ | $[56906509,56906510]$ | $[1770886266,1770886267]$ | $[-405755371,-405755370]$ | $[-183210819,-183210818]$ | $U>1$ |
| $5$ | $[47430130,47430131]$ | $[-2416947654,-2416947653]$ | $[48439855,48439856]$ | $[88433067,88433068]$ | $U>1$ |

| Root | $q$ | $\phi$ | $D$ | $\mathcal H_1$ | $C_*$ |
| --- | --- | --- | --- | --- | --- |
| $1$ | $[-447596756,-447596755]$ | $[-653812176,-653812175]$ | $[7968033,7968034]$ | $[-1179239,-1179238]$ | $[60064619229,60064619230]$ |
| $2$ | $[-449201397,-449201396]$ | $[-587655521,-587655520]$ | $[-1610317,-1610316]$ | $[-69278049,-69278048]$ | $[59845785552,59845785553]$ |
| $3$ | $[-523765345,-523765344]$ | $[183300576,183300577]$ | $[291908584,291908585]$ | $[802640895,802640896]$ | $[87860862308,87860862309]$ |
| $4$ | $[-541827595,-541827594]$ | $[-252377770,-252377769]$ | $[229391867,229391868]$ | $[5352571582,5352571583]$ | $[37208623560,37208623561]$ |
| $5$ | $[2610732609,2610732610]$ | $[-556605677,-556605676]$ | $[173018740,173018741]$ | $[-3564611166,-3564611165]$ | $[579363609754,579363609755]$ |

The normalized coefficient $\mathfrak a$ in (3.4) has these additional
enclosures; this table uses the denominator displayed in its own row.

| Root | Numerator interval for $\mathfrak a$ | Denominator |
| --- | --- | --- |
| $1$ | $[-61,-60]$ | $10^{48}$ |
| $2$ | $[-54,-53]$ | $10^{48}$ |
| $3$ | $[-19,-18]$ | $10^{40}$ |
| $4$ | $[18,19]$ | $10^{39}$ |
| $5$ | $[23835670199611922667149562144,23835670199611922667149562145]$ | $10^{0}$ |

Here is the full interval evaluation order. Evaluate $\mathfrak a$ and
$\mathfrak b$ by Horner on the input $t$ interval, exclude zero from
the displayed $\mathfrak a$ interval, and put
$x=-\mathfrak b/\mathfrak a$. Evaluate $q$ by its polynomial,
$\phi$ by (2.11), then $L$ by (2.11), and put
$d=3L/(5q\phi)$, $p=p_n/(5q)$, $v=v_n/(5q)$. Form $D$ and the
four $z_i$ of (2.5), and use its rows to form
$\mathcal H_0,\mathcal H_1,\mathcal H_2$ after division by $D$.
Finally compute $B_*,C_*,U$ by (2.10) and
$r=xU-U(24-d)/\mathcal H_1$. Every inversion is justified by the
zero exclusions in the two denominator tables. The $D$ intervals also
exclude $x=0,-1,-2$; $\mathcal H_1$ excludes $a_1=0$.
For a printed interval with denominator $10^k$, coarsen a mesh interval
$[l,u]/10^{240}$ to
$[\lfloor l/10^{240-k}\rfloor,\lceil u/10^{240-k}\rceil]/10^k$.
These rules, the polynomial circuits and the exact ten root endpoints
specify all arithmetic in the tables.

**Theorem 5.1 (No guarded Q41 companion).** Every positive root of
$Q_{41}$ fails an original-world guard when used as a possible terminal
companion in the branch $q\phi h\ne0$.

Proof. The sign-preserving remainder recurrence (5.1), applied to the
public quotient (3.3), gives the variation counts shown above. The five
input intervals are disjoint and each has variation drop one. The
variation drop from zero to infinity is five, so they exhaust all
positive roots. At a common $F,G$ root, the determinantal polynomial
combination $S_1$ vanishes. Definition 3.6 makes $A_1$ a unit; also
$Q_8$ cannot vanish at a $Q_{41}$ root because $A_1$ contains its
cube. Thus (3.4) gives the only possible finite $x$.

Apply the outward rules in the stated order. The resulting numerator
pairs are the tables. Row one has $r>1$; row two has $x<0$; rows
three through five have $U<1$. Each contradicts (2.10). The exclusions
apply on entire rational intervals, and the nonzero-denominator tables
make every evaluation valid even for rows already failing positivity.
Therefore no unguarded polynomial root has been counted as an actual
world. ∎

## 6. Entire finite-positive off-24 C0 exclusion

**Theorem 6.1 (No actual terminal-M companion to C0).** For every real
$t>0$ with $q(t)\ne0$ and $p_0(t)\ne24$, there is no actual world
$W\in C(p_0(t),v_0(t))$ satisfying $m(W)=m_0(t)$.

Proof. Suppose such a world exists. Its $x>0$ and whole-world guards
are those of Section 2. We split before dividing the terminal equation.

If $h=0$, then $x=t/(1+2t)$ and direct substitution gives

$$
\phi\left(\frac{t}{1+2t}\right)
=-\frac{Q_4(t)}{(1+2t)^4}<0.
\tag{6.1}
$$

The undivided terminal equation (2.12) fixes $d=d_0$. The late-node
interpolant $\mathcal H$ is then exactly that of the complete boundary
tuple: its four nodes use the same $x,d,p,v$. At fixed $d$ and
$\mathcal H$, clocks zero and two uniquely fix $U$ through (2.10),
because $d$ and $B_*$ cannot both vanish. Hence $U=1+2t$.
By (2.3), $d_0\ne24$, so clock one uniquely fixes $j=t$.
Consequently $r=xU-j=0$, contrary to strictness. This step divides
neither by drift nor by a possibly zero second-clock equation.

Now take $h\ne0$. If $\phi=0$, equation (2.12) forces $L=0$;
Theorem 4.3 excludes the finite drift solution. This includes zero
drift and the zero-$b_s$ branch.

It remains that $h\phi\ne0$. Here and only here substitute
$d=3L/(5q\phi)$. The nonzero quantities $q,\phi,D,h$ justify
all removed factors in (3.1), and (2.9) yields $F=G=0$.
The resultant (3.5) vanishes. Since $Q_4(t)>0$ and $Q_7$ has no
positive roots by (5.1), either $Q_8(t)=0$ or $Q_{41}(t)=0$.
The latter case is impossible by Theorem 5.1.

If $Q_8(t)=0$, the polynomial combination $S_2$ vanishes at the
common root. The exact characteristic-zero congruence (3.6), together
with the units $P_A,c_2$, forces $x=-P_B/P_A$. At this $t$,
$\operatorname{Res}_x(\phi,3L)=0$. Both polynomials retain degree four:
their leading coefficients are $8$ and $720q$, with $q$ a unit.
They therefore have a finite common complex root. The polynomial
combination $T_1=1296(P_Ax+P_B)$ forces that root to be
$-P_B/P_A$. Thus $\phi(-P_B/P_A)=L(t,-P_B/P_A)=0$, contradicting
the present $\phi\ne0$ branch.

All finite positive $t$ are covered. No division by drift, $b_s$,
$\Lambda$, a leading gain coefficient or a root
separation was used. The division by $\mathcal H_1$ in (2.10)
is justified by its nonvanishing on every actual off-$24$ world,
proved immediately after (2.10), and imposes no additional nonzero
gain-sample assumption. The determinants were defined at fixed degrees
before specialization, and all actual-world tests were the original
guards. Thus degree drops and every allowed whole-gain degeneracy remain
in the theorem. ∎

## 7. A uniform r floor at both selected M endpoints

**Assumption 7.1 (Exact published suppliers).** The following statements
are used with their original quantifiers. Write
$\delta(W)=\min\{r,1-r,b,c\}$ and let $D_J$ mean the set of bases
with a distinct equal-$a$ pair in the entire off-$24$ child.

1. III, Theorem 7.1, supplies $P_J>0$ such that, for every real
   $p\ne24,v$ and $W\ne W'\in C(p,v)$ with $a(W)=a(W')$,
   $|p|\le P_J$.
2. III, Corollary 8.1, supplies finite $V_J,C_J>0$ such that every
   $(p,v)\in D_J$ has $|v|\le V_J$, and every world of its entire
   child has $b,c,|d|$ and all four padded whole-gain coefficients
   bounded by $C_J$. The same enlarged bound controls both terminal
   responses, including those of unused companions.
3. SII, Theorem 29.1, supplies one $\epsilon>0$, uniform in $v$,
   such that $0<|p-24|<\epsilon$ admits no distinct equal-$m$ pair.
   Hence every (1.1) has $|p-24|\ge\epsilon$.
4. SII, Theorem 23.1, supplies $\eta>0$ such that for every real
   $p\ne24,v$ and every distinct equal-$m$ pair in $C(p,v)$,
   both endpoints have $b+c\ge\eta$. It assumes no bound on $p$.
5. SII, Theorem 14.3, gives, for every $P>0$, one
   $\varepsilon(P)>0$ for both actions and all $|p|\le P,p\ne24,v$,
   such that every selected distinct equal-terminal pair obeys
   $\max\{\delta(W),\delta(W')\}\ge\varepsilon(P)$.
   SII, Theorem 15.1, puts the chosen endpoint of each pair of a joint
   configuration into one compact strict-parent set; over a compact
   off-$24$ base set it lies in a compact strict off-$24$ parent set.
6. SII, Theorem 21.2, excludes convergence of either selected $M$
   endpoint of original joint configurations, whose bases have a finite
   off-$24$ limit, to a complete $B_0(t)$ tuple for $t>0,t\ne1$.
   Its $L(t)$ is exactly the face $B_0(t)$ of Definition 1.3.

These are supplied conclusions, not a hypothesis that the joint locus
itself is compact or closed. Theorem 21.2 uses the original selected
$J$ pair at the same bases and does not require a cross-pair equality.

**Theorem 7.2 (Global selected-M r floor in the original joint locus).**
There exists one $\rho>0$ such that every original joint configuration
(1.1) satisfies

$$
r(W_2)\ge\rho,\qquad r(W_3)\ge\rho.
\tag{7.1}
$$

Proof. Suppose no positive uniform bound exists. Choose configurations
(1.1) and one of their two selected $M$ endpoints, denoted $V_k$,
with $r(V_k)\to0$. Its paired endpoint is $V'_k$. The selected $J$
pair supplies $|p_k|\le P_J$ by supplier 1. Supplier 2 bounds both
base coordinates and the complete coordinates of every companion, in
particular of $V_k,V'_k$. Supplier 3 separates all these bases from
$p=24$. After simultaneous subsequences the base tends to a finite
$(p_*,v_*)$ with $p_*\ne24$, and both complete-coordinate sequences
converge. Here complete coordinates comprise the source, the fixed
drift and all four padded coefficients of the whole polynomial.

The rank relation gives $b(V_k)c(V_k)\to0$. Supplier 4 keeps their
sum at least $\eta$. Consequently the first source limit is exactly
one of $B_0(t)$ or $C_0(t)$ with a finite $t>0$. All of $j,n,T,U$
are positive at either limit, so the parent and fixed-node interpolation
pass continuously to the limit. This identifies the entire limiting
polynomial, not merely its late samples.

At $B_0(t)$, $\Lambda=8(t-1)/t$ and $-D_b=12/5$; thus $t=1$
is incompatible with finite drift. Supplier 6 excludes every remaining
$B_0(t)$ limit of such configurations.

At $C_0(t)$, (2.4) excludes $q(t)=0$ without dividing the parent
equation by $\Lambda$. The identified complete boundary tuple is
therefore exactly Definition 2.1. In particular
$(p_*,v_*)=(p_0(t),v_0(t))$, and $p_*\ne24$ gives $t\ne1/8$.
Since $\delta(V_k)\le r(V_k)\to0$, supplier 5 implies
$\delta(V'_k)\ge\varepsilon(P_J)$ for all sufficiently large $k$.
Its complete-coordinate limit $V'$ has a strict source. Its gain is
nonzero: a zero whole polynomial would make the original readings at
zero and one equal to the same drift. Continuity gives

$$
V'\in C(p_0(t),v_0(t)),\qquad m(V')=m_0(t),
$$

contradicting Theorem 6.1. Both finite-face alternatives are impossible.
The infimum of $r$ over the two selected $M$ labels of all original
joint configurations is consequently positive. If there are no such
configurations, any $0<\rho<1$ satisfies (7.1). ∎

The quantifier in (7.1) is over both selected $M$ labels in every
original joint configuration. The proof uses the $J$ pair only to supply
its bounded fifth reading and uses the original joint lower-face
exclusion where needed. It gives no $M$-only bound on $p$, no selected
$J$ endpoint floor, no floor for every unused companion and no uniform
positive lower bound for $1-r$. Neither closedness nor compactness of
the entire original joint relation follows.

## 8. Exact response identities for the entire child above K

**Definition 8.1 (The rectangular base region).** In this section and
below let

$$
K=[56,58]\times[304,305],\qquad
\mathcal S_K=\bigcup_{(p,v)\in K}C(p,v).
\tag{8.1}
$$

Every assertion about $\mathcal S_K$ quantifies over every actual
complete world, including worlds unused by any selected pair. The
symbol $K$ in (8.1) is unrelated to the auxiliary quadratic expression
$K_d$ of Section 2.

At any source with $b\ge0,j,n>0$, retain (1.2) and put

$$
\begin{aligned}
C_5&=\frac{3(8b-1)(b+2)}{2TU},&
A_5&=\frac{b^2-16b-12}{2TU},\\
C_6&=\frac{3(80b^2+192b+31)}{5TU},&
A_6&=\frac{2b^2-24b-17}{TU},\\
F_b&=\frac{6(8b-1)}{5TU},&
Q_b&=32-\frac{5(b+2)}j-\frac{10(3b+2)}n.
\end{aligned}
\tag{8.2}
$$

Here $A_5,A_6$ are the explicit coefficients in (8.2), not the
infinite-drift coefficients with those names in III, Section 2.

**Theorem 8.2 (Undivided response identities on this parent).** The
original gain and responses on $H=0$ obey

$$
\begin{gathered}
g(5)=C_5+e(A_5+5/n),\qquad
g(6)=C_6+e(A_6+16/n),\\
D_b=(5b+2)F_b,\qquad \Lambda g(5)=F_bQ_b,\\
24\Lambda-D_b=\frac{972+1854b}{5TU}-\frac{96}j-\frac{96}n.
\end{gathered}
\tag{8.3}
$$

Proof. Apply fixed-node interpolation to (1.3). The rows at clocks
$4,5,6$ are $(-1,4,-6,4)$, $(-4,15,-20,10)$ and
$(-10,36,-45,20)$. Direct collection gives

$$
g(4)-\frac{-6-e}{U}=H.
\tag{8.4}
$$

Alternatively interpolate at nodes $0,2,3,4$ with values
$(-24-e,(27/5-e)/T,-e/n,(-6-e)/U)$. Evaluating this interpolant at
$5,6$ gives respectively the first two expressions of (8.3).
For the interpolant from (1.3), without assuming $H=0$, the differences
are exactly $(15/4)H$ and $9H$. Thus these formulas use the actual
whole gain on the entire parent. No exact-degree or nonzero-sample
condition enters.

The identity $D_b=(5b+2)F_b$ follows from the explicit $\kappa$.
Multiplication and collection in (1.2), (8.2) and the original
fifth-clock interpolation row gives the ambient identity

$$
\Lambda g(5)-F_bQ_b
=\left(4+\frac{20}T-\frac{15}j-\frac{10}n\right)H.
\tag{8.5}
$$

Finally expand $24\Lambda-D_b$ to obtain the last identity of (8.3).
All of these are rational identities on the domain $T,U,j,n>0$;
none is obtained by division by $\Lambda$. ∎

**Theorem 8.3 (Explicit source bounds throughout this base region).**
Every world in $\mathcal S_K$ has

$$
b<30,\qquad c<10,\qquad j>1/16.
\tag{8.6}
$$

Proof. First consider any strict parent world with $b\ge30$. Since
$bc=r(1-r)\le1/4$, we have $j<b+1,n<b+2$ and
$\Lambda>1-8/b>0$. Also

$$
Q_b<-3-\frac5{b+1}+\frac{40}{b+2}<0.
$$

Since $F_b>0$, (8.3) gives $g(5)<0$. The right side of its last
identity is less than

$$
\frac{972+1854b}{5TU}-\frac{192}{b+2}.
$$

After multiplication by $5TU(b+2)>0$, its numerator is
$-66b^2+1800b+984$. This is $-4416$ at $30$ and decreases thereon,
because its derivative is $-132b+1800<0$. Now that $\Lambda>0$ is
proved, the parent equation yields
$d=(24\Lambda-D_b)/\Lambda<0$. Thus
$p=d+(U+n)g(5)<0$. A world with $p\ge0$ cannot have $b\ge30$.

If instead $c\ge10$, the rank relation gives $b\le1/40$,
$T\le41/40,U\le21/20$ and $j,n\ge c$. The explicit functions give

$$
6<\Lambda<8,\quad F_b<0,\quad
\frac45<|F_b|<\frac65,\quad
Q_b\ge32-\frac{247}{8c}>28.
$$

For example the lower bound on $\Lambda$ follows from
$1+240/41+20/21-8/10>6$; the bounds on $F_b$ follow by clearing
$5TU$ on $0\le b\le1/40$. It follows that

$$
g(5)<-14/5,\qquad
0<e=-\frac{F_b(5b+2)}\Lambda<17/40<1/2.
$$

Consequently $p<49/2-(14/5)c\le-7/2$. Thus $p\ge0$ forces both
upper bounds in (8.6).

For the remaining bound suppose $j\le1/16$. Then $b\le1/16$,
$D_b<0$ and $\Lambda<0$. Put $h_e=-e>0$ and
$\ell=1+6/T+1/U<8$. The undivided parent gives

$$
h_e(4/j+4/n-\ell)=|D_b|\le12/5.
$$

Indeed $|D_b|=6(1-8b)(5b+2)/(5TU)\le12/5$ on this interval.
Since $4/j-\ell>56$, it follows that

$$
h_e<3/70,\qquad
\frac{15h_e}j+\frac{10h_e}n
\le\frac{15}{4}(h_e\ell+|D_b|)<30h_e+9.
$$

The original fifth-clock interpolation row, with $e=-h_e$, now gives

$$
\begin{aligned}
g(5)&=96-4h_e+15h_e/j-20(27/5+h_e)/T+10h_e/n\\
&<105-108/T+h_e(26-20/T)\\
&\le57/17+(3/70)(122/17)=2178/595<4.
\end{aligned}
$$

Here $T\le17/16$. Directly from the strict source,
$n=j+r<j+1$, $U=1+2b\le1+2j$, so
$U+n<2+3j\le35/16$. Since $d<24$,

$$
p<24+\frac{35}{16}\max\{g(5),0\}<131/4<33.
$$

Therefore $p\ge33$ forces $j>1/16$. All bases in (8.1) have
$p\ge56$, proving (8.6). ∎

## 9. Drift separation with every gain stratum retained

Set $x_K=p-24$, $y_K=v-24$; these are distinct from the late-node
coordinate $x$ used in Sections 2–6. Define, for all $b\ge0,n>0$,

$$
\begin{aligned}
P_0&=(U+n)C_5,& A&=6+(U+n)A_5+5U/n,\\
V_0&=(2U+n)C_6,& B&=17+(2U+n)A_6+32U/n.
\end{aligned}
\tag{9.1}
$$

Equation (8.3) and the original response traces imply

$$
x_K=P_0+eA,\qquad y_K=V_0+eB.
\tag{9.2}
$$

**Theorem 9.1 (Model-specific coefficient separation and drift bound).**
For every $b\ge0,n>0$,

$$
\max\{|A|,|B|\}>1/100.
\tag{9.3}
$$

Every world in $\mathcal S_K$ consequently has $|e|<655000$.

Proof. Put $z=n/U>0$ and

$$
u=UA_5=(T+5/T-18)/2,\qquad w=8-1/T.
$$

Then $UA_6=4u+w$ and the definitions give

$$
A=6+(1+z)u+5/z,\qquad
B=17+(2+z)(4u+w)+32/z.
$$

Define the two rational functions

$$
\varphi(z)=\frac{6z+5}{z(z+1)},\qquad
\mathcal W(z)=\frac{7z^2+19z+8}{z(z+1)(z+2)}.
$$

Solving these two linear relations gives exactly

$$
u=-\varphi(z)+\frac A{z+1},\qquad
w=\mathcal W(z)+\frac B{z+2}-\frac{4A}{z+1}.
\tag{9.4}
$$

The derivative numerators, with positive denominators
$z^2(z+1)^2$ and $z^2(z+1)^2(z+2)^2$, are respectively

$$
-(6z^2+10z+5),\qquad
-(7z^4+38z^3+67z^2+48z+16).
$$

Thus both functions strictly decrease on $z>0$. Since $T\ge1$,
$w\ge7$. Also

$$
T^2-\frac{40}{9}T+5=(T-20/9)^2+5/81>0
$$

implies $u>-61/9$. If $|A|,|B|\le1/100$ and $z\ge4/5$,
(9.4) would give

$$
w\le\frac{865}{126}+\frac{325}{12600}=\frac{3473}{504}<7.
$$

If $z<4/5$, it would give

$$
u<-\frac{245}{36}+\frac1{100}=-\frac{1529}{225}<-\frac{61}{9}.
$$

Both alternatives contradict the preceding bounds, proving (9.3).

For all $b\ge0$, clearing the positive denominator $TU$ gives
$|C_5|\le12$ and $0<C_6\le192/5$. More explicitly, with
$q_b=TU=2b^2+3b+1$, the numerator of $C_5$ is
$24b^2+45b-6$ over $2q_b$. Its absolute value is at most $24q_b$:
the two differences are $24b^2+27b+30$ and
$72b^2+117b+18$. The numerator of $C_6$ is
$240b^2+576b+93$ over $5q_b$, and its difference from $192q_b$
is $144b^2+99>0$.

By (8.6), $U<61$ and $n<41$. Hence
$|P_0|<1224$ and $|V_0|<31296/5$. Above $K$ one has
$|x_K|\le34$, $|y_K|\le281$. From (9.2)–(9.3),

$$
|e|<100\max\{34+1224,\ 281+31296/5\}
=654020<655000.
\tag{9.5}
$$

The estimate includes $e=0$, zero drift $d=0$, and any allowed gain
samples or lower degrees, since (9.2) divided by none of them. ∎

## 10. Explicit exclusion of the entire singular-source neighbourhood

**Theorem 10.1 (Full-child Lambda separation over K).** Every world in
$\mathcal S_K$ satisfies $|\Lambda|>10^{-12}$.

Proof. Suppose $|\Lambda|\le10^{-12}$. On $b\ge0$,

$$
\kappa'=-\frac{2(10b^2+8b+1)}{T^2U^2}<0.
$$

Using $b<30$ gives $\kappa>304/1891>4/25$. The parent equation
and (9.5) imply

$$
|b-1/8|=\frac{5|e\Lambda|}{24\kappa}
<10^6|\Lambda|\le10^{-6}.
\tag{10.1}
$$

In particular $3/25\le b\le13/100$. On this interval the decreasing
function $\ell=1+6/T+1/U$ obeys

$$
\frac{50569}{7119}\le\ell\le\frac{3109}{434},\qquad
7<\ell,\qquad \ell+10^{-12}<36/5.
$$

Since $j\le n$, $\Lambda\le\ell-8/n$, and thus $n>10/9$.
If $n\ge2$, the strict relation $j=n-r>n-1\ge1$ would give
$\Lambda>\ell-6>1$, a contradiction. Hence

$$
10/9<n<2.
\tag{10.2}
$$

Treat $b,n$ as independent variables for the rational functions in
(9.1); their actual values still satisfy all original source equations.
At $\beta=1/8$ direct substitution gives

$$
\begin{aligned}
A_\beta&=-\frac{716n^2+31n-900}{144n}<-149/1296,\\
(B-5A)_\beta&=\frac{7676n^2-12545n+6300}{720n}>2977/1296,\\
P_{0,\beta}&=0,\qquad V_{0,\beta}=60+24n.
\end{aligned}
\tag{10.3}
$$

For the first inequality, the derivative of
$-(716n+31-900/n)/144$ is negative. For the second, the derivative
of $(7676n-12545+6300/n)/720$ is positive on $n\ge10/9$, because
$7676-6300/n^2\ge7676-5103>0$. Evaluation at $10/9$ gives the
displayed constants.

Here are explicit derivative bounds on the closed rectangle
$\mathcal R=[3/25,13/100]\times[10/9,2]$. Set $q_b=TU$; then
$q_b\ge1$ and $q_b'=4b+3<4$. The four numerator circuits and their
bounds on the $b$ interval are

| Function | Numerator $N$ | Denominator | Bound on $|N|$ | Bound on $|N'|$ |
| --- | --- | --- | --- | --- |
| $C_5$ | $24b^2+45b-6$ | $2q_b$ | $<1$ | $<52$ |
| $A_5$ | $b^2-16b-12$ | $2q_b$ | $<15$ | $<16$ |
| $C_6$ | $240b^2+576b+93$ | $5q_b$ | $<172$ | $<640$ |
| $A_6$ | $2b^2-24b-17$ | $q_b$ | $<21$ | $<24$ |

For example the first numerator is increasing and lies between its
endpoint values $-159/625$ and $639/2500$, both of magnitude less
than one. The other bounds follow by their displayed quadratics and
linear derivatives at the rational endpoints. The quotient rule now
gives, without cancellation assumptions,

$$
\begin{array}{c|rrrr}
& C_5&A_5&C_6&A_6\\ \hline
|\text{function}|&<1&<15/2&<35&<21\\
|\partial_b\text{function}|&<30&<38&<268&<108.
\end{array}
\tag{10.4}
$$

Indeed the derivative bounds follow from
$(52+4)/2<30$, $(16+60)/2=38$,
$(640+688)/5<268$, and $24+84=108$; inequalities remain strict.
On $\mathcal R$, $U+n<4$, $2U+n<5$ and $1/n\le9/10$.
Differentiating (9.1) at fixed $n$ therefore gives

$$
\begin{aligned}
|A_b|&<2(15/2)+4(38)+9=176,\\
|B_b|&<4(21)+5(108)+64(9/10)<682,\\
|(P_0)_b|&<2+4(30)=122,\\
|(V_0)_b|&<4(35)+5(268)=1480.
\end{aligned}
\tag{10.5}
$$

In particular these are strictly below $(200,700,200,1700)$.
Apply the mean value theorem along the horizontal segment joining
$(\beta,n)$ to $(b,n)$. Equations (10.1), (10.3) and (10.5) give

$$
A<0,\qquad B-5A>0,\qquad |P_0|<0.0002,
\qquad |V_0-(60+24n)|<0.0017.
$$

For the second sign the error is less than
$(700+5\cdot200)10^{-6}=0.0017<2977/1296$; for the first it is
less than $0.0002<149/1296$. Since $x_K\ge32$, (9.2) now forces
$e<0$. Consequently

$$
\begin{aligned}
v-5p-12&=V_0-5P_0-108+e(B-5A)\\
&<24(n-2)+0.0027<0.0027.
\end{aligned}
$$

But throughout the closed box $K$, $v-5p-12\ge304-5(58)-12=2$.
This contradiction proves the theorem. It excludes $\Lambda=0$ before
any division by $\Lambda$, and uses every companion in (8.1). ∎

## 11. Three exact finite-face exclusions over the closed box

In this section finite boundary tuples satisfy the closed rank relation
$bc=r(1-r)$ and the original whole-gain equations, with $j,n>0$.
These are auxiliary limits; strict actual worlds remain as in Definition
1.1. The identities below follow from (1.2)–(1.4) at the specified face.

**Theorem 11.1 (Neither b-zero face meets K).** No finite complete
boundary tuple with $b=0$ and $c>0$ has its acquired base in $K$.

Proof. If $r=0,c=s>0$, then $T=U=1,j=n=s$ and
$\Lambda=8(s-1)/s$, $D_b=-12/5$. Thus $s=1$ is inconsistent
with $H=0$. At every other $s$ the original parent and response rows
give

$$
\begin{gathered}
e=\frac{3s}{10(s-1)},\qquad
p=-\frac{3(16s^2-80s+65)}{10(s-1)},\\
v-2p=\frac{231s+126}{10}.
\end{gathered}
\tag{11.1}
$$

For $s>1$ one can rewrite

$$
p=\frac{72}{5}-\frac{3}{10(s-1)}-\frac{24}{5}(s-1)<24.
$$

Thus $p\ge56$ forces $s<1$. Then
$v<2p+357/10\le1517/10<304$, contrary to $K$.

For the other face put $r=1,c=s>0$ and $Q_s=2s^2-1$. Here
$\Lambda=4Q_s/(s(s+1))$ and again $D_b=-12/5$. A zero of $Q_s$
is inconsistent with the parent. Otherwise direct interpolation gives

$$
\begin{aligned}
e&=\frac{3s(s+1)}{5Q_s},\\
p&=\frac{-48s^3+144s^2+12s-90}{5Q_s},\\
v&=\frac{135s^3+645s^2-99s-399}{5Q_s}.
\end{aligned}
\tag{11.2}
$$

If $s>1/\sqrt2$, then

$$
p-24=-\frac{6\{2s(4s^2-1)+(16s^2-5)\}}{5Q_s}<0.
$$

Both terms inside braces are positive in this range. A base in $K$
therefore requires $0<s<1/\sqrt2<3/4$. Subtracting the original
responses gives

$$
v-5p-12=\frac{3f_s(s)}{5Q_s},\qquad
f_s(s)=125s^3-65s^2-53s+37.
$$

There is the exact Bernstein identity, with $u=4s/3$,

$$
f_s(s)=\sum_{i=0}^4\beta_i\binom4i u^i(1-u)^{4-i},\qquad
(\beta_0,\ldots,\beta_4)
=\left(37,\frac{433}{16},\frac{353}{32},
\frac{535}{256},\frac{859}{64}\right).
\tag{11.3}
$$

Expansion checks the identity even though $f_s$ has degree three.
All coefficients are positive and the basis sums to one on $0\le u\le1$.
Thus $f_s>0$ on $[0,3/4]$. Since $Q_s<0$ in the remaining
range, $v<5p+12\le302<304$. This excludes the second face. ∎

**Theorem 11.2 (The C0 face does not meet K).** No finite complete
$C_0(t)$ boundary tuple, $t>0$, has acquired base in $K$.

Proof. This conclusion uses the boundary base formulas alone; it needs
no terminal companion. Put

$$
N_t=(8t-1)(14t^2+95t+30),\qquad
Z_t=(5t+2)(83t^2+853t+92).
$$

The parent and original responses give

$$
p-24=-\frac{3N_t}{5q},\qquad v-24=-\frac{3Z_t}{5q}.
\tag{11.4}
$$

By (2.4), $q=0$ is inconsistent with a finite tuple. If $p>24$,
then $t>1/8$ and $q<0$: for $0<t\le1/8$ one has $q<0$ and
$N_t\le0$, so $p\le24$; for $t>1/8$ the numerator $N_t$ is
positive. Define

$$
F_t=3N_t+170q=506t^3+2238t^2-925t-770.
$$

One has $F_t(3/4)=275/32>0$,
$F_t'(3/4)=26287/8>0$, and
$F_t''(t)=3036t+4476>0$ for $t\ge3/4$. Thus $F_t>0$ for
$t\ge3/4$. But $p-58=-F_t/(5q)$, so $p\le58$ with $q<0$
requires $F_t\le0$ and consequently $t<3/4$.

Finally put

$$
S_t=Z_t-4N_t+240q=207t^3+1447t^2-334t-656.
$$

Its second derivative is $1242t+2894>0$ on $[0,3/4]$, and its
endpoint values are $S_t(0)=-656$, $S_t(3/4)=-335/64$.
Convexity bounds the polynomial above by its endpoint chord, which is
strictly negative. Hence $S_t<0$ throughout this interval. It follows
that

$$
v-4p-72=-\frac{3S_t}{5q}<0.
$$

In particular $24<p\le58$ on this face implies $v<4p+72\le304$.
This contradicts the closed box $K$. This proof is independent of the
terminal-$M$ elimination in Sections 3–6. ∎

## 12. Full-child compact closure with only C1 retained

**Theorem 12.1 (Entire-child localization over K).** Every actual world
in $\mathcal S_K$ satisfies

$$
b<30,\quad c<10,\quad j>1/16,\quad
|e|<655000,\quad |\Lambda|>10^{-12}.
\tag{12.1}
$$

Its closure in $(r,b,c,e)$ and all four padded coefficients of the
whole gain is compact. Every gain in that closure is nonzero. There
exist $\varepsilon_b,\varepsilon_r>0$ such that all its actual worlds
satisfy

$$
b\ge\varepsilon_b,\qquad r\ge\varepsilon_r.
\tag{12.2}
$$

Every point of this closure at which the source ceases to be strict
belongs to

$$
C_1=\{r=1,\ b>0,\ c=0\}.
\tag{12.3}
$$

Proof. The explicit bounds are Theorems 8.3, 9.1 and 10.1. They bound
all four source/drift coordinates. The lower bound on $j$ also gives
$n\ge j>1/16$, and $T,U\ge1$. The four samples (1.3) are therefore
uniformly bounded. Fixed-node interpolation bounds all four padded
coefficients, with no assumption about exact degree. This places
$\mathcal S_K$ in a bounded subset of a finite-dimensional real
coordinate space. Its closure is closed and bounded, hence compact.

The original equations, including the seven reading equations, the
closed rank relation and membership of the base in the closed $K$,
pass continuously to every limit. In particular the original clocks
zero and two imply the identity

$$
Tg(2)-g(0)=147/5
\tag{12.4}
$$

in the closure. Thus no limiting whole polynomial is identically zero.
The lower bound $j\ge1/16$ keeps the interpolation interface defined
there, independently of drift or gain degeneracies.

In the closed source domain, $0\le r\le1,b,c\ge0$ and
$bc=r(1-r)$. Losing strict positivity therefore forces $r=0$ or
$r=1$, and $b=0$ or $c=0$. If $b=c=0$, the $j$ floor excludes
the point. All other possibilities are precisely the four open faces

$$
(r,b,c)=(0,0,s),\quad(1,0,s),\quad(0,t,0),\quad(1,t,0),
\qquad s,t>0.
$$

The first two are excluded by Theorem 11.1, and the third by Theorem
11.2. These exclusions apply to finite complete tuples with their whole
gains, as supplied by the limiting original equations. Only the last
face, (12.3), remains. Every point of the compact closure consequently
has $b>0$ and $r>0$. If it is nonempty, these two continuous
coordinates attain strictly positive minima, proving (12.2). If it is
empty, any positive constants satisfy the assertion. ∎

The closure in Theorem 12.1 includes all companions, not only chosen
strict anchors of selected pairs. Its possible $C_1$ points are
auxiliary boundary tuples; the theorem does not assert that such a point
occurs. It does not imply nonemptiness of $\mathcal S_K$, a uniform
positive lower bound for $1-r$, or any extension of (12.1)–(12.3)
outside this specified box. In particular it does not apply the
terminal-$M$ exclusion of Theorem 6.1 to companions lacking its terminal
equality. Its three finite-face exclusions are instead the base-only
identities of Section 11.

## 13. Mathematical sources and remaining scope

Sections 6, 7 and 12 establish the entire finite-positive off-$24$
$C_0$ terminal-companion exclusion, its original-joint selected-$M$
$r$ floor, and the all-companion localization over the specified $K$.
The coefficient identities, exact rational intervals and finite-face
inequalities refer to the FIB model of Definition 1.1. Interpolation,
resultant and Sturm criteria, interval enclosure, the mean value theorem,
Bernstein positivity and finite-dimensional compactness are classical
intermediate methods.

| Mathematical source | Use and parameter correspondence |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorem 2.1 | Original worlds, fixed drift, entire degree-at-most-three gain, left products, literal clocks, full-parent converse; its drift displacement is $e=d-24$ here. |
| F, Lemma 30.2 | The faithful late-node coordinates $(x,d)$ and all guards (2.10), with $x=n/U$ and normalized entire gain $\mathcal H=Ug$. |
| III, Definition 1.2, Theorem 7.1, Corollary 8.1 and Lemma 10.2 | The undivided parent, selected-$J$ fifth-response bound, all-companion coercivity over $D_J$, and the original whole-gain correspondence. |
| SII, Theorems 14.3, 15.1, 21.2, 23.1 and 29.1 | Exactly the selected-pair and joint-sequence suppliers in Assumption 7.1; its lower face $L(t)$ is this volume's $B_0(t)$. |
| Berrut–Trefethen, *Barycentric Lagrange Interpolation*, §2, [DOI](https://doi.org/10.1137/S0036144502417715) | Classical fixed-node interpolation; distinct nodes, not exact gain degree or nonzero sampled values, are required. |
| Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, second edition, [DOI](https://doi.org/10.1007/3-540-33099-2) | Classical subresultants, Sturm signs and real-root determination, used only on the explicit model-specific polynomial circuits. |
| Cox–Little–O'Shea, *Ideals, Varieties, and Algorithms*, fourth edition, [DOI](https://doi.org/10.1007/978-3-319-16721-3) | Classical elimination and resultant criteria, used with the fixed degrees, zero exclusions and characteristic-zero lifting stated above. |

The original joint existence-or-exclusion question remains (1.1), with
all four worlds in one entire child, separate terminal common values and
only within-pair distinctness. The new conclusions do not construct such
a configuration or exclude all of them. The bounded ambient base set
supplied by III is not the explicit rectangle $K$ of (8.1); no inclusion
of all original joint bases in that rectangle is asserted. The global
selected-$M$ bound in Theorem 7.2 and the local all-companion bounds in
Theorem 12.1 have their respective quantifiers and require their
respective proofs.

## 追加锚（本行以下为增补区）
## 14. The acquired history excludes constant and affine whole gains

**Definition 14.1 (Original observations for the degree test).** Retain
exactly the complete worlds of Definition 1.1 and
[O, Definitions 1.1–1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md#1-complete-worlds-and-the-equal-odd-read-parent):

$$
\begin{gathered}
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
c=\frac{r(1-r)}b,\quad b>0,\quad0<r<1,\\
0\ne g\in\mathbb R[s],\qquad\deg g\le3,\qquad d\in\mathbb R.
\end{gathered}
\tag{14.1}
$$

The gain is one whole polynomial and the drift is fixed within each
world. With the same matrices

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP),
$$

the acquired actions are $(E_1,\ldots,E_6)=(J,M,J,M,M,M)$ and
$(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v)$. Put, as in (1.2),
$j=b+c$, $n=j+r$, $T=1+b$ and $U=1+2b$. The actual left products
from O, Definition 1.3, give the following observation equations.

| Clock $i$ | Product $Q_i$ | Reading equation |
| --- | --- | --- |
| $0$ | $\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$ | $0=d+g(0)$ |
| $1$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $24=d+jg(1)$ |
| $2$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $147/5=d+Tg(2)$ |
| $3$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $24=d+ng(3)$ |
| $4$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $18=d+Ug(4)$ |
| $5$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $p=d+(U+n)g(5)$ |
| $6$ | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $v=d+(2U+n)g(6)$ |

Thus $C(p,v)$ continues to mean the entire set of these complete worlds,
with $p,v\in\mathbb R$ arbitrary. At clock seven the alternatives are

$$
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7).
\tag{14.2}
$$

They are alternative responses of the same world, not two acquired
readings. No degree label, gain sample, drift or source coordinate is
acquired.

**Theorem 14.2 (Constant gains contradict the acquired even clocks).**
No world satisfying (14.1) and the acquired readings through clock four
has $\deg g=0$.

Proof. Suppose $g(s)=k$ for a nonzero real constant $k$. The initial
reading forces $d=-k$. The actual traces at clocks two and four then
force

$$
\frac{147}{5}=-k+(1+b)k=bk,\qquad
18=-k+(1+2b)k=2bk.
$$

Consequently $18=294/5$, a contradiction. This uses neither the odd
readings nor the later readings $p,v$. ∎

**Theorem 14.3 (Affine gains contradict the strict source relation).**
No world satisfying (14.1) and the acquired readings through clock four
has $\deg g=1$.

Proof. Every nonconstant affine real polynomial has a unique expression
$g(s)=q(s-\xi)$ with $q\ne0$ and $\xi\in\mathbb R$. The initial
reading gives $d=q\xi$. Substitution into the actual clock-two and clock-four rows
of Definition 14.1 yields

$$
\begin{aligned}
\frac{147}{5}&=q\{2+(2-\xi)b\},\\
18&=q\{4+2(4-\xi)b\}.
\end{aligned}
\tag{14.3}
$$

Subtracting twice the first equation from the second gives
$4qb=18-294/5=-204/5$. Since $b>0$, it follows that

$$
q=-\frac{51}{5b},\qquad
2+(2-\xi)b=-\frac{49b}{17},\qquad
\xi=\frac{83}{17}+\frac2b>\frac{83}{17}>3.
\tag{14.4}
$$

Define the following polynomials in this positive $b$:

$$
\mathcal A=40b^2+83b+34,\qquad
L_0=66b+34>0,\qquad R_0=32b+34>0.
\tag{14.5}
$$

The clock-one and clock-three equations are
$24=q\{\xi+(1-\xi)j\}$ and
$24=q\{\xi+(3-\xi)n\}$. Formula (14.4) gives

$$
\frac{24}{q}-\xi=-\frac{\mathcal A}{17b},\qquad
1-\xi=-\frac{L_0}{17b},\qquad
3-\xi=-\frac{R_0}{17b}.
$$

Both odd sample factors are nonzero. Therefore these two acquired rows,
together with $r=n-j$ and $c=j-b$, force

$$
j=\frac{\mathcal A}{L_0},\qquad
n=\frac{\mathcal A}{R_0},\qquad
r=\frac{34b\mathcal A}{L_0R_0},\qquad
c=\frac{\mathcal A}{L_0}-b.
\tag{14.6}
$$

All variable denominators are justified by $q\ne0$, $b>0$,
$L_0>0$ and $R_0>0$. In particular, no branch with a zero odd gain
sample has been discarded: (14.4) rules out such a sample for every
hypothetical affine solution of the even rows.

The source determinant relation is $bc-r(1-r)=0$. On substituting
(14.6), multiplication by the positive denominator $(L_0R_0)^2$
gives the exact identity

$$
\begin{aligned}
(L_0R_0)^2\{bc-r(1-r)\}
&=b(\mathcal A-bL_0)L_0R_0^2
  -34b\mathcal A L_0R_0+(34b\mathcal A)^2\\
&=b^2\Pi(b),\\
\Pi(b)&=92416b^4+3475904b^3+7750164b^2\\
&\hspace{1.8em}+5516432b+1257728.
\end{aligned}
\tag{14.7}
$$

This identity follows by multiplication of the three polynomials in
(14.5); in particular $\mathcal A-bL_0=-26b^2+49b+34$ specifies
its first factor explicitly. Every coefficient of $\Pi$ is strictly
positive. Thus $b>0$ implies $b^2\Pi(b)>0$, contradicting the zero
determinant. No later reading or terminal equality is used. ∎

**Corollary 14.4 (Degree scope for the entire original child).** For all
real $p,v$ and every complete world $W=(P,g,d)\in C(p,v)$,

$$
\deg g\in\{2,3\}.
\tag{14.8}
$$

In particular this conclusion also applies at $p=24$. The original joint
condition retains exactly the quantifiers and responses of (1.1):

$$
\begin{gathered}
\exists p,v\in\mathbb R,\quad p\ne24,\\
\exists W_0,W_1,W_2,W_3\in C(p,v),\\
W_0\ne W_1,\qquad a(W_0)=a(W_1),\\
W_2\ne W_3,\qquad m(W_2)=m(W_3).
\end{gathered}
\tag{14.9}
$$

Requiring (14.8) for each of these worlds is an equivalent formulation
of (14.9). Quadratic gains remain in this formulation, the pairs may
overlap, and their two common terminal values are independent. The
corollary supplies a necessary degree condition; it asserts neither the
existence nor the exclusion of a configuration in (14.9).

Proof. Every world in $C(p,v)$ satisfies the first five acquired rows
in Definition 14.1. Theorems 14.2 and 14.3 exclude degrees zero and one.
A nonzero polynomial of degree at most three has a degree in
$\{0,1,2,3\}$, proving (14.8). This implication holds for every member
of the entire child, so it applies to any selected worlds in (14.9)
without adding a hypothesis on $p,v$, on either pair, or on either
terminal common value. Conversely, (14.9) with this necessary degree
condition implies (14.9) by forgetting the condition. ∎

## 追加锚（本行以下为增补区）

## 15. The finite positive C1 face and its complete lift

**Definition 15.1 (C1 notation and boundary tuples).** Retain the complete
worlds, left products, entire children and terminal responses of
Definitions 1.1–1.2, equivalently
[III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Definitions 1.1–1.2.
The symbols introduced in Sections 15–21 are local to the C1 face; in
particular its polynomials $Q_4,F,G$ below are different from the C0
polynomials of Sections 2–5. For a finite real $t>0$ put

$$
\begin{gathered}
C_1(t)=(r,b,c)=(1,t,0),\qquad
q=(t+1)(t^3-4t-2),\qquad q_d=5q,\\
P_1=-6(36t^4+61t^3+221t^2+181t+30),\\
V_1=-3(375t^4+881t^3+2486t^2+1706t+266),\\
T_1=-3(1088t^4+3483t^3+9978t^2+7102t+1220).
\end{gathered}
\tag{15.1}
$$

When $q\ne0$ define

$$
\begin{gathered}
d_1=-\frac{3(11t^2+158t+80)}{5(t^3-4t-2)},\qquad
(p_1,v_1,m_1)=\frac{(P_1,V_1,T_1)}{q_d},\\
g_1=\operatorname{Interp}_{0,1,2,3}
\left(-d_1,\frac{24-d_1}{t},
\frac{147/5-d_1}{1+t},\frac{24-d_1}{1+t}\right).
\end{gathered}
\tag{15.2}
$$

Here interpolation means the unique polynomial of degree at most three
at the four displayed distinct nodes, using the Lagrange formula of
Berrut–Trefethen, [§2](https://doi.org/10.1137/S0036144502417715).
Write $\widehat W_1(t)=(P(1,t,0),g_1,d_1)$ for this complete auxiliary
tuple. Its source is nonstrict, so $\widehat W_1(t)$ is not an actual
world. Its gains are whole polynomials, not independently variable
samples. These are the C1 tuples of
[SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Definition 12.1
and Lemma 12.2, with the same original clocks.

**Theorem 15.2 (Finite face domain and exact responses).** A finite
complete C1 tuple with the first five acquired readings exists precisely
when $q\ne0$, and is then $\widehat W_1(t)$. Its fifth, sixth and
terminal-$M$ responses are $p_1,v_1,m_1$. For positive $t$ in this
domain,

$$
p_1\ne24\quad\Longleftrightarrow\quad t\ne\frac18.
\tag{15.3}
$$

Proof. At C1 the positive traces $j,n,T,U$ are
$t,t+1,t+1,2t+1$. The undivided parent equation of Definition 1.2 is

$$
\frac{2(t^3-4t-2)}{t(t+1)(2t+1)}(d-24)
=-\frac{6(5t+2)(8t-1)}{5(t+1)(2t+1)}.
\tag{15.4}
$$

The polynomial $t^3-4t-2$ is coprime to $(5t+2)(8t-1)$.
Consequently its positive zeros cannot satisfy (15.4) with finite $d$.
The factor $t+1$ of $q$ has no positive zero. Elsewhere (15.4) has
the unique solution $d=d_1$. The first four original readings then
give exactly the whole interpolant in (15.2). Substitution at clocks
$5,6,7$, with respective traces $U+n,2U+n,3U+2n$, gives (15.1)–(15.2).
Finally multiplication gives

$$
P_1-24q_d=-6(8t-1)(7t^3+11t^2+19t+10).
\tag{15.5}
$$

The last factor is positive for $t>0$, proving (15.3). In particular
the exclusion of a zero of $q$ removes no finite complete C1 tuple. ∎

**Definition 15.3 (Late interpolation and full-world coordinates).**
For real $x,d,p,v$ with $D=x(x+1)(x+2)\ne0$, let $H$ interpolate

$$
\begin{aligned}
h_3&=(24-d)/x,& h_4&=18-d,\\
h_5&=(p-d)/(x+1),& h_6&=(v-d)/(x+2)
\end{aligned}
\tag{15.6}
$$

at $3,4,5,6$. Thus, writing $H_i=H(i)$,

$$
\begin{pmatrix}H_0\\H_1\\H_2\\H_7\end{pmatrix}
=R\begin{pmatrix}h_3\\h_4\\h_5\\h_6\end{pmatrix},\qquad
R=\begin{pmatrix}
20&-45&36&-10\\
10&-20&15&-4\\
4&-6&4&-1\\
-1&4&-6&4
\end{pmatrix}.
\tag{15.7}
$$

Put

$$
\begin{gathered}
B_0=294/5-2d-H_2,\qquad C_0=d^2+B_0^2,\\
U=\frac{-dH_0+B_0H_2}{C_0},\qquad
b=(U-1)/2,\qquad j=\frac{U(24-d)}{H_1},\qquad r=xU-j.
\end{gathered}
\tag{15.8}
$$

The domain of these last formulas requires $H_1\ne0,C_0>0$.
The faithful inverse of [F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
Lemma 30.2, applies with $x=n/U$ and $H=Ug$. Its additional actual-world
conditions are

$$
\begin{gathered}
x>0,\quad d\ne24,\quad U>1,\quad0<r<1,\\
j=b+\frac{r(1-r)}b,\qquad
dU=-H_0,\qquad B_0U=H_2.
\end{gathered}
\tag{15.9}
$$

When they hold, $c=r(1-r)/b$ and $g=H/U$ give the unique complete
world for $(x,d,p,v)$. The formula for $U$ in (15.8) is used even at
$d=0$; the inverse is not defined by division by drift.

## 16. Zero-safe source equations and the C1 self branch

**Definition 16.1 (Undivided source forms).** In (15.6)–(15.7) put

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\qquad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\qquad z_6=(v-d)x(x+1),\\
(a_0,a_1,a_2,a_7)^{\mathsf T}=R(z_3,z_4,z_5,z_6)^{\mathsf T},\\
z=xa_1-D(24-d),\qquad b_s=(294-10d)D-5a_2,\\
A_s=4z^2-2za_1+(2x-1)a_1^2,\qquad
E_s=-2za_1+2(1-x)a_1^2,\\
\mathcal Q(u,w)=A_su^2+E_suw-a_1^2w^2,\\
f_0=5dDa_2+a_0b_s,\qquad
K_0=\mathcal Q(-a_0,dD),\qquad
K_s=25K_0+\mathcal Q(5a_2,b_s).
\end{gathered}
\tag{16.1}
$$

These are polynomial expressions before any terminal equation is solved.
In particular $a_i=DH_i$.

**Assumption 16.2 (Owning whole-world necessity interface).** Every actual
$W\in C(p,v)$ with $p\ne24$ satisfies (15.8)–(15.9), $H_1\ne0,C_0>0$,
and

$$
f_0=K_0=K_s=0.
\tag{16.2}
$$

This is the existing interface of Definition 2.2, equations (2.7)–(2.9),
Definition 2.3 and F, Lemma 30.2, with the correspondence
$\mathcal H=H$, $a_i=DH_i$, and the same $x=n/U$, drift $d$ and
acquired $p,v$. It includes zero drift, vanishing gain samples, degree
drops and singular sources of the undivided parent. Its source identities,
in the present notation, are

$$
dDU=-a_0,\qquad b_sU=5a_2.
\tag{16.3}
$$

$$
\mathcal Q(U,1)
=4a_1^2\{b(j-b)-r(1-r)\}=0.
\tag{16.4}
$$

The correspondence uses $j=U(24-d)D/a_1$ and $r=Uz/a_1$.
In particular these supplied identities divide by neither $d$ nor
$b_s$, a gain value, a leading gain coefficient or $\Lambda$.

**Definition 16.3 (C1 terminal polynomials).** From now on set
$(p,v)=(p_1(t),v_1(t))$. Define integer polynomials

$$
\begin{gathered}
K=8x^4+29x^3+18x^2-15x-6,\qquad B=q_dK,\\
v_3=24q_d(x+1)(x+2),\quad v_4=18q_dD,\\
v_5=P_1x(x+2),\quad v_6=V_1x(x+1),\\
N=(2x+3)(-v_3+4v_4-6v_5+4v_6)-T_1D,\\
h=(2t+1)x-t-1.
\end{gathered}
\tag{16.5}
$$

The source polynomial $K$ is distinct from the rectangle
$[56,58]\times[304,305]$, denoted $\mathcal K$ below.

**Theorem 16.4 (Terminal equation and self-branch exclusion).** On the
domain of Definition 15.3,

$$
q_dD\{d+(2x+3)H_7-m_1\}=N-Bd.
\tag{16.6}
$$

An actual terminal-$M$ companion must satisfy $N-Bd=0$. If $h=0$ and
$K\ne0$, no such companion is strict.

Proof. Substitute the last row of (15.7) into the left side of (16.6)
and collect its drift coefficient; it is $-q_dK$. The remaining term
is the definition of $N$. For an actual world the terminal trace is
$3U+2n$, so its reading is $d+(2x+3)H_7$.

At $h=0$ one has $x=(t+1)/(2t+1)$, and multiplication gives

$$
\begin{gathered}
K=-\frac{Q_4(t)}{(2t+1)^4},\qquad
N=\frac{3(t+1)(11t^2+158t+80)Q_4(t)}{(2t+1)^4},\\
Q_4=78t^4+41t^3-129t^2-132t-34.
\end{gathered}
\tag{16.7}
$$

If $K\ne0$, (16.6) fixes $d=N/B=d_1$. The four tail values in
(15.6) now fix $H=(2t+1)g_1$. Substitution in the zero-safe projection
(15.8) gives $U=2t+1$, $j=t$ and $r=xU-j=1$. This violates strictness.
The part $h=K=0$ is retained in the exceptional-pole analysis below. ∎

## 17. The C1 integer elimination and its exact algebraic factors

**Definition 17.1 (Ordinary elimination circuit).** Apply the first
three rows of $R$ to the column

$$
\begin{pmatrix}
(24B-N)(x+1)(x+2)\\
(18B-N)D\\
(P_1K-N)x(x+2)\\
(V_1K-N)x(x+1)
\end{pmatrix}
\tag{17.1}
$$

and call the outputs $A_0,A_1,A_2$. Put

$$
\begin{gathered}
Z=xA_1-D(24B-N),\qquad \mathfrak b=(294B-10N)D-5A_2,\\
A_q=4Z^2-2ZA_1+(2x-1)A_1^2,\qquad
E_q=-2ZA_1+2(1-x)A_1^2,\\
F=-\frac{5NDA_2+A_0\mathfrak b}{90D^2h},\\
G=\frac{A_qA_0^2-E_qA_0ND-A_1^2N^2D^2}{324D^4h}.
\end{gathered}
\tag{17.2}
$$

These exact polynomial quotients, with the signs and scalar divisors
shown, define $F,G\in\mathbb Z[t,x]$. Their coordinate degrees
$(\deg_x,\deg_t)$ are $(6,7)$ and $(13,15)$.

**Definition 17.2 (Determinants, fixed factors and linear coordinate).**
Use the fixed coefficient-minor convention of Definition 3.2 for
$\operatorname{Subres}_k(G,F)$ with nominal degrees $(13,6)$, and for
$\operatorname{Subres}_k(K,N)$ with nominal degrees $(4,4)$. In particular
the index-zero member is the fixed Sylvester determinant, without
specializing or trimming degrees first. Define $Q_9,Q_{12}$ by their
descending coefficient lists:

$$
\begin{aligned}
\operatorname{coeff}_{\downarrow}(Q_9)=(&2248108288,
12765068132,-8911595079,55889179310,\\
&-127755649252,367729251274,709892709460,\\
&482515359696,207188455720,32969082600),\\[2mm]
\operatorname{coeff}_{\downarrow}(Q_{12})=(&3523306032,
14115530736,35825657643,-25329237978,\\
&-354487843712,-1131571865850,-2280936182284,\\
&-2531589902408,-2219920526928,-344577128440,\\
&71276236896,9034745760,-782114304).
\end{aligned}
\tag{17.3}
$$

Here $Q_4$ is (16.7). Define the degree-fifty-five polynomial by the
exact quotient

$$
Q_{55}=\frac{\operatorname{Res}_x(G,F)}
 {331776Q_4^3Q_9^2Q_{12}^8}.
\tag{17.4}
$$

This is an integer polynomial, with its normalization and sign fixed
by the displayed quotient. Define

$$
\begin{gathered}
S_1=\operatorname{Subres}_1(G,F)=\alpha(t)x+\beta(t),\\
S_2=\operatorname{Subres}_2(G,F)=c_2x^2+c_1x+c_0,\\
\ell=\operatorname{Subres}_1(K,N)=\pi_a(t)x+\pi_b(t).
\end{gathered}
\tag{17.5}
$$

Divide $S_1$ by the monic gcd of $\alpha,\beta$ in $\mathbb Q[t]$;
clear coefficient denominators by their positive least common multiple;
then divide by the positive integer coefficient gcd. The resulting
polynomial is

$$
L=A(t)x+C(t),\qquad \deg_t L=123.
\tag{17.6}
$$

Thus no sign is changed merely to make a leading coefficient positive.
All these polynomials are specified by integer arithmetic from
(15.1), (16.5), (17.1)–(17.5), without a supplementary coefficient table.

**Theorem 17.3 (C1 factor identities and specialization units).**
The exact quotient and subresultants above satisfy

$$
\begin{gathered}
\operatorname{Res}_x(F,G)=331776Q_4^3Q_9^2Q_{12}^8Q_{55},\\
\operatorname{Res}_x(K,N)=-93312Q_4Q_{12}.
\end{gathered}
\tag{17.7}
$$

For each $Q$ in the following table, every entry in its second column
has monic gcd $1$ with $Q$ in $\mathbb Q[t]$.

| $Q$ | Polynomials coprime to $Q$ |
| --- | --- |
| $Q_4$ | $q_d,\ [x^6]F,\ [x^{13}]G,\ \pi_a,\ \alpha,\ A$ |
| $Q_9$ | $q_d,\ [x^6]F,\ [x^{13}]G,\ \pi_a$ |
| $Q_{12}$ | $q_d,\ [x^6]F,\ [x^{13}]G,\ \pi_a,\ c_2$ |
| $Q_{55}$ | $q_d,\ [x^6]F,\ [x^{13}]G,\ \pi_a,\ \alpha,\ A$ |

The following coefficient congruences also hold:

$$
\begin{aligned}
(t+1)\alpha+(2t+1)\beta&\equiv0\pmod{Q_4},\\
\pi_ac_1-2\pi_bc_2&\equiv0\pmod{Q_{12}},\\
\pi_a^2c_0-\pi_b^2c_2&\equiv0\pmod{Q_{12}},\\
\operatorname{prem}_x(K,\ell)&\equiv0\pmod{Q_e}\quad(e=4,12),\\
\operatorname{prem}_x(N,\ell)&\equiv0\pmod{Q_e}\quad(e=4,12).
\end{aligned}
\tag{17.8}
$$

In the last two lines congruence is coefficientwise in $x$. The
integer polynomial gcd of $\pi_a,\pi_b$ in $\mathbb Z[t]$, with
positive normalization, is the constant $1296$.

Proof. The finite polynomial operations determining the identities can
be written explicitly. For $P,Q\in\mathbb Z[t][x]$ of degrees $m\ge n$
put

$$
\operatorname{prem}_x(P,Q)
=\operatorname{lc}_x(Q)^{m-n+1}
  \operatorname{rem}_{\mathbb Q(t)[x]}(P,Q).
\tag{17.9}
$$

For the pair $(G,F)$ set $R_0=G,R_1=F$, $m=6$,
$a=\operatorname{lc}_x(F)$ and $c=-a^7$, and start with
$R_2=\operatorname{prem}_x(G,F)$. For each subsequent nonzero $R_i$,
let $k=\deg_xR_i$, $\delta=m-k$, and form

$$
\begin{gathered}
R_{i+1}=\frac{\operatorname{prem}_x(R_{i-1},R_i)}{-ac^\delta},\\
a_{\rm new}=\operatorname{lc}_x(R_i),\qquad
c_{\rm new}=
\begin{cases}
(-a_{\rm new})^\delta/c^{\delta-1},&\delta>1,\\
-a_{\rm new},&\delta=1,
\end{cases}\qquad m_{\rm new}=k.
\end{gathered}
\tag{17.10}
$$

The values of $(m,a,c)$ on the right are the preceding values; the
three new values replace them after the quotient is taken. Polynomial
multiplication in (17.2) cancels exactly $90D^2h$ and $324D^4h$,
giving the stated integer degrees. The divisions in (17.10) have
zero remainder. Their successive $x$ degrees are

$$
13,6,5,4,3,2,1,0.
\tag{17.11}
$$

The last three members are $S_2,S_1$ and
$331776Q_4^3Q_9^2Q_{12}^8Q_{55}$, respectively; the remainder after
the constant member is zero. These are the subresultants with the
fixed minor convention in Definition 17.2. Thus (17.10), or equivalently
those finite minors, specifies the exact quotient (17.4). The symmetry
sign for the resultant is $(-1)^{6\cdot13}=1$.

For the smaller pair use the same coefficient minors with degrees
$(4,4)$; its constant member is $-93312Q_4Q_{12}$. Reducing the two
coefficients of its linear member gives their integer scalar content
$1296$. Reducing the coefficients of $S_1,S_2$ and the two
pseudo-remainders by the explicitly listed $Q$'s gives (17.8).
Euclidean division in $\mathbb Q[t]$ gives the gcd table. These are
finite rational polynomial identities: (17.9)–(17.10), the coefficient
lists and the specified monic reductions determine each entry.

The algebraic tools here are the classical subresultant and resultant
identities of Basu–Pollack–Roy,
[*Algorithms in Real Algebraic Geometry*, second edition](https://doi.org/10.1007/3-540-33099-2),
and Cox–Little–O'Shea,
[*Ideals, Varieties, and Algorithms*, fourth edition](https://doi.org/10.1007/978-3-319-16721-3).
They are used on these particular C1 circuits. In particular a finite
common root annihilates every fixed subresultant even when a specialized
degree drops, by the coefficient-minor argument of Definition 3.2.
The gcd table additionally preserves degrees $6,13$ at every root of
the four displayed factors. ∎

## 18. Exceptional terminal poles with the original drift retained

**Definition 18.1 (Scaled original pole equations).** Keep $d$ as an
indeterminate, and multiply the four $z_i$ of (16.1) by $q_d$ before
applying $R$. Denote the outputs by $\widetilde a_i=q_da_i$, and put
$\Delta=q_dD$. Define

$$
\begin{gathered}
\widetilde z=x\widetilde a_1-\Delta(24-d),\qquad
\widetilde b_s=(294-10d)\Delta-5\widetilde a_2,\\
\widetilde A_s=4\widetilde z^2-2\widetilde z\widetilde a_1
 +(2x-1)\widetilde a_1^2,\\
\widetilde E_s=-2\widetilde z\widetilde a_1
 +2(1-x)\widetilde a_1^2,\\
\widetilde{\mathcal Q}(u,w)=
\widetilde A_su^2+\widetilde E_suw-\widetilde a_1^2w^2,\\
\widetilde f=5d\Delta\widetilde a_2+
 \widetilde a_0\widetilde b_s=q_d^2f_0,\\
\widetilde K_s=25\widetilde{\mathcal Q}(-\widetilde a_0,d\Delta)
 +\widetilde{\mathcal Q}(5\widetilde a_2,\widetilde b_s)=q_d^4K_s.
\end{gathered}
\tag{18.1}
$$

All terms are polynomials in $t,x,d$. For $e\in\{4,12\}$ work in
$\mathcal A_e=\mathbb Q[t]/(Q_e)$ and substitute
$x=-\pi_b/\pi_a$. This inverse exists by Theorem 17.3. The same
theorem gives $K=N=0$ there. Write

$$
\widetilde f=f_2d^2+f_1d+f_0^{\flat}
\quad\hbox{in }\mathcal A_e[d].
\tag{18.2}
$$

The superscript distinguishes its constant coefficient from the source
polynomial $f_0$ of (16.1). For an element $u$ of a finite free algebra,
its norm means the determinant of multiplication by $u$ on its stated
power basis.

**Theorem 18.2 (Q4 pole exclusion).** At a positive $Q_4$ root the only
possible drift satisfying both original pole source equations
$\widetilde f=\widetilde K_s=0$ is $d=d_1$. Its source reconstruction
has $r=1$, so it gives no strict companion.

Proof. In $\mathcal A_4$, the pole coordinate is
$x=(t+1)/(2t+1)$ and the quadratic has the exact factorization

$$
\begin{gathered}
\widetilde f=f_2(d-d_1)(d-d_o),\\
d_o=\frac{-3286744321946172282t^3+4749234502781385t^2
 +5146526094595587693t+3318426590487962019}
 {27062287663495765},\\
\widetilde K_s(d_1)=0.
\end{gathered}
\tag{18.3}
$$

These identities use the unreduced circuits (18.1), followed by monic
reduction in $t$. For completeness, the following norms give exact
nonvanishing data. Use the monic $Q_4$ over $\mathbb Z_{(103)}$ and
reduce the multiplication determinants modulo $103$:

| Element | $q_d$ | $2t+1$ | $f_2$ | $d_o-d_1$ | $\widetilde K_s(d_o)$ |
| --- | --- | --- | --- | --- | --- |
| Norm modulo $103$ | $87$ | $58$ | $78$ | $49$ | $75$ |

All denominators in (18.1)–(18.3) are units in this localization;
the leading coefficient $78$ of $Q_4$ is also a unit. The table is
determined by reducing each product $ut^i$ in the basis $1,t,t^2,t^3$
and taking the resulting $4$ by $4$ determinant. Its nonzero residues
imply that the rational norms are nonzero, hence the five elements are
units in $\mathcal A_4$. In particular (18.3) has distinct roots and
the second root cannot satisfy the other original source equation.

At the remaining drift $d_1$, the tail interpolant is again
$H=(2t+1)g_1$. Its projection gives $U=2t+1,j=t,r=1$, as in
Theorem 16.4. The off-$24$ guard ensures that the projection is defined.
This treats the self pole as well as every other possible actual
specialization over $Q_4$. ∎

**Theorem 18.3 (Q12 pole exclusion).** No complex specialization over
a $Q_{12}$ root satisfies the two original pole source equations.
In particular no finite real drift, including zero, gives an actual
companion there.

Proof. Use the monic polynomial $\overline Q_{12}$ over
$\mathbb Z_{(101)}$. Its leading coefficient before normalization is
$14$ modulo $101$. Norms in its rank-twelve algebra are

| Element | $\pi_a$ | $q_d$ | $D$ | $f_2$ |
| --- | --- | --- | --- | --- |
| Norm modulo $101$ | $81$ | $70$ | $4$ | $21$ |

Thus all inverses defining the pole coordinate and the monic quadratic
$d^2+(f_1/f_2)d+f_0^{\flat}/f_2$ exist over this local base. In the
rank-twenty-four algebra

$$
\mathcal B=
\mathbb Z_{(101)}[t,d]\big/
\left(\overline Q_{12},\ d^2+(f_1/f_2)d+f_0^{\flat}/f_2\right)
\tag{18.4}
$$

use the ordered basis
$(1,t,\ldots,t^{11},d,dt,\ldots,dt^{11})$.
Multiplication by $\widetilde K_s$ has determinant congruent to $5$
modulo $101$. The following smaller description specifies its entire
reduced matrix, including column order. Over $\mathbb F_{101}$ let
$T$ be multiplication by $t$ in the power basis of the monic reduction
of $Q_{12}$, and put $\mathcal T=\operatorname{diag}(T,T)$. The matrix is

$$
\mathcal M=(u,\mathcal Tu,\ldots,\mathcal T^{11}u,
             w,\mathcal Tw,\ldots,\mathcal T^{11}w),
\qquad \det\mathcal M=5\ \text{in }\mathbb F_{101},
\tag{18.5}
$$

where the columns $u,w$ are specified by their upper and lower halves:

$$
\begin{aligned}
u_{0:11}&=(100,33,77,31,64,11,16,34,89,76,79,21)^{\mathsf T},\\
u_{12:23}&=(35,68,22,57,83,56,23,18,55,30,28,43)^{\mathsf T},\\
w_{0:11}&=(80,62,79,69,16,36,10,20,10,23,77,19)^{\mathsf T},\\
w_{12:23}&=(43,68,85,16,3,72,80,55,94,4,2,85)^{\mathsf T}.
\end{aligned}
\tag{18.6}
$$

For direct polynomial reduction, the ascending coefficients of the
pole coordinate modulo $101$ are

$$
x=(89,69,78,37,13,28,56,10,63,2,14,1)_{\uparrow}.
\tag{18.7}
$$

Equations (18.1)–(18.2), reduction of $d^2$ by (18.4), and this power
basis give the columns (18.6). Multiplication by $t$ gives all remaining
columns, so (18.5) is a determinant of an explicitly specified finite
matrix. The norm of the primitive pole slope is $88$ modulo $101$;
the raw slope $\pi_a$ used here retains scalar content $1296$, and
$1296^{12}\cdot88=81$ in $\mathbb F_{101}$. This accounts for both
normalizations without changing the pole root.

Since its reduction is nonzero, the characteristic-zero determinant
of multiplication by $\widetilde K_s$ is nonzero. This element is
therefore a unit in $\mathcal B\otimes\mathbb Q$. A simultaneous root
of $Q_{12},\widetilde f,\widetilde K_s$ would define an evaluation of
this algebra into $\mathbb C$ sending a unit to zero, which is
impossible. The finite field is used only to prove rational
nonvanishing; no ordering or positivity assertion is transferred from
it. ∎

**Corollary 18.4 (Exhaustion of terminal poles).** There is no strict
terminal-$M$ companion at any $t>0,q\ne0,p_1\ne24$ for which its
coordinate satisfies $K=0$.

Proof. The undivided terminal equation then gives $N=0$.
The second resultant in (17.7) forces $Q_4Q_{12}=0$.
The unit slope $\pi_a$ forces $x=-\pi_b/\pi_a$ in either case.
Theorems 18.2 and 18.3 apply to the original source equations, which
are necessary by the owning interface in Assumption 16.2. ∎

## 19. All positive ordinary roots and the strict-world filter

**Definition 19.1 (Exact root intervals).** Use the sign-preserving
primitive Sturm chain of (5.1) for the C1 polynomials $Q_9,Q_{55}$.
Equivalently, start with the primitive polynomial and its derivative,
then take the negative rational remainder at every step, clearing
denominators by a positive multiplier and dividing by the positive
integer coefficient gcd. Let $V_Q$ delete zero signs and count sign
changes. Define $I_i=[n_i,n_i+1]/10^{100}$ by the following integers:

$$
n_1=331870885647581929578614662915535274627868308379774186451433773199910925757925405068055394263716320.
$$

$$
n_2=592871025766250080129037854655456855516932898909293518832115892542554220181550964887860129081740667.
$$

$$
n_3=1169282097378496760713331273949662713954637119564189174284877330075796164866942628660929045301821974.
$$

$$
n_4=8987958556003912054324118136694659655357123575765489192788689281953416191283400770034988723262128126.
$$

$$
n_5=11548090705409620030003314835248813519914394588703630543117437290841128378573523374544086557791888306.
$$

$$
n_6=15591356173773691330841311300703417302600643714552045485796096233616031468101479653830193596467972446.
$$

$$
n_7=21278854472701899683249315606910112840090662363569897315270046510110507873777556532008976233389443732.
$$

$$
n_8=26394748321178503158178113041026686437960387687932084605809141439086335171102877686435207724799660984.
$$

**Theorem 19.2 (Positive-root exhaustion).** The polynomial $Q_9$ has
no positive real roots. The polynomial $Q_{55}$ has exactly eight
positive real roots, all simple, with exactly one in the interior of
each $I_i$.

Proof. The chains have respectively $10,56$ entries and end in
nonzero constants. Their signs and variations are

| Polynomial | Chain signs at $0$ | Chain signs at $+\infty$ | $V(0)$ | $V(+\infty)$ |
| --- | --- | --- | --- | --- |
| $Q_9$ | `++--+++---` | `+++-+++---` | $3$ | $3$ |
| $Q_{55}$ | `++-++-++++-++--+-++---++--+---++--++--+----+-++-+++-----` | `++----++--+++---+++--+++---++++--++++-++++--+++--++-----` | $27$ | $19$ |

The endpoint variations on the eight intervals are

| $i$ | $V_{Q_{55}}(n_i/10^{100})$ | $V_{Q_{55}}((n_i+1)/10^{100})$ |
| --- | --- | --- |
| $1$ | $27$ | $26$ |
| $2$ | $26$ | $25$ |
| $3$ | $25$ | $24$ |
| $4$ | $24$ | $23$ |
| $5$ | $23$ | $22$ |
| $6$ | $22$ | $21$ |
| $7$ | $21$ | $20$ |
| $8$ | $20$ | $19$ |

None of the endpoints is a root, and the two endpoint signs of
$Q_{55}$ in every row are opposite. All signs in these tables are
integer signs determined by the chain recurrence. More explicitly,
for an integer coefficient polynomial $\sum_{j=0}^mc_jt^j$ at $n/B$,
initialize $v=c_m$, then successively replace $v$ by
$nv+c_{m-k}B^k$ for $k=1,\ldots,m$. The result is
$B^mQ(n/B)$, with the same sign. At $+\infty$ the sign is the
leading coefficient sign. This determines the tables directly from
the exact quotient (17.4), including its normalization.

Sturm's theorem, in the classical form cited in Theorem 17.3,
now gives zero positive roots for $Q_9$ and eight for $Q_{55}$.
The intervals are disjoint, each has variation drop one, and the
constant last chain member makes $Q_{55}$ squarefree. Hence these
intervals exhaust its positive roots. ∎

**Theorem 19.3 (Exact all-root guard intervals).** At the $Q_{55}$ root
in $I_i$ define

$$
x=-C/A,\qquad d=N/(q_dK),\qquad p=P_1/q_d,\quad v=V_1/q_d,
\tag{19.1}
$$

and then use (15.6)–(15.8). All these inverses are defined. The
following pairs $(l,u)$ denote closed enclosures $[l,u]/10^6$ of the
indicated values:

| $i$ | $x$ | $d$ | $U$ | $r$ | Sign of $A$ |
| --- | --- | --- | --- | --- | --- |
| $1$ | $(337088,337089)$ | $(22264146,22264147)$ | $(2553625,2553626)$ | $(1739303,1739304)$ | $-$ |
| $2$ | $(-275769,-275768)$ | $(25794799,25794800)$ | $(6153645,6153646)$ | $(-1981371,-1981370)$ | $-$ |
| $3$ | $(623082,623083)$ | $(2589088,2589089)$ | $(-21167671,-21167670)$ | $(-6485979,-6485978)$ | $-$ |
| $4$ | $(684103,684104)$ | $(28981230,28981231)$ | $(2741528,2741529)$ | $(927577,927578)$ | $+$ |
| $5$ | $(884506,884507)$ | $(39535195,39535196)$ | $(-221154,-221153)$ | $(-344993,-344992)$ | $-$ |
| $6$ | $(791099,791100)$ | $(59633693,59633694)$ | $(246669,246670)$ | $(870698,870699)$ | $+$ |
| $7$ | $(619987,619988)$ | $(72429881,72429882)$ | $(-708228,-708227)$ | $(-526888,-526887)$ | $+$ |
| $8$ | $(619308,619309)$ | $(-21954173,-21954172)$ | $(338347,338348)$ | $(873767,873768)$ | $+$ |

| $i$ | $q$ | $K$ | $H_1$ | $C_0$ |
| --- | --- | --- | --- | --- |
| $1$ | $(-2203491,-2203490)$ | $(-7796937,-7796936)$ | $(-5045747,-5045746)$ | $(511821278,511821279)$ |
| $2$ | $(-2369562,-2369561)$ | $(-1056511,-1056510)$ | $(-38836358,-38836357)$ | $(666387605,666387606)$ |
| $3$ | $(-2754473,-2754472)$ | $(-137151,-137150)$ | $(67612034,67612035)$ | $(13772601,13772602)$ |
| $4$ | $(-9245438,-9245437)$ | $(3199189,3199190)$ | $(-14406591,-14406590)$ | $(839961823,839961824)$ |
| $5$ | $(-10944710,-10944709)$ | $(19779203,19779204)$ | $(22999402,22999403)$ | $(2240393536,2240393537)$ |
| $6$ | $(-11379027,-11379026)$ | $(10889881,10889882)$ | $(13011052,13011053)$ | $(5908733735,5908733736)$ |
| $7$ | $(-2742208,-2742207)$ | $(-287806,-287805)$ | $(390674033,390674034)$ | $(92244580080,92244580081)$ |
| $8$ | $(21221290,21221291)$ | $(-320618,-320617)$ | $(-23408366,-23408365)$ | $(6371424697,6371424698)$ |

| $i$ | $p_1$ | $v_1$ | $m_1$ |
| --- | --- | --- | --- |
| $1$ | $(19742791,19742792)$ | $(88601579,88601580)$ | $(399406232,399406233)$ |
| $2$ | $(21027143,21027144)$ | $(95225259,95225260)$ | $(424602206,424602207)$ |
| $3$ | $(23651633,23651634)$ | $(109120092,109120093)$ | $(477612384,477612385)$ |
| $4$ | $(56979139,56979140)$ | $(304497370,304497371)$ | $(1226730635,1226730636)$ |
| $5$ | $(75840336,75840337)$ | $(415273644,415273645)$ | $(1646101990,1646101991)$ |
| $6$ | $(136394565,136394566)$ | $(765839664,765839665)$ | $(2962228760,2962228761)$ |
| $7$ | $(1199736273,1199736274)$ | $(6854846482,6854846483)$ | $(25682035998,25682035999)$ |
| $8$ | $(-278010371,-278010370)$ | $(-1597176238,-1597176237)$ | $(-5833854433,-5833854432)$ |

In every row $h\ne0$, $d\ne0,24$, $p_1\ne24$ and
$x(x+1)(x+2)q_dKH_1\ne0$, with $C_0>0$. Exactly row $4$ has
all of $x>0,U>1,0<r<1$. At that row,

$$
\begin{gathered}
\frac{870764}{10^6}\le b\le\frac{870765}{10^6},\qquad
\frac{77148}{10^6}\le c\le\frac{77149}{10^6},\\
\frac{898795}{10^6}<t<\frac{898796}{10^6}.
\end{gathered}
\tag{19.2}
$$

Proof. The enclosures have a purely rational specification. For
$S=10^{220}$ enclose a rational interval $[a,b]$ after an addition
or multiplication by
$[\lfloor Sa\rfloor/S,\lceil Sb\rceil/S]$.
Negation exchanges and negates endpoints. Multiplication first takes
the minimum and maximum of its four endpoint products. An inverse
is $[1/b,1/a]$ and is used only when $ab>0$. Repeated multiplication
defines positive integer powers. Evaluate a polynomial by descending
Horner, enclosing exact rational coefficients as singleton intervals;
for a polynomial in $(x,t)$ first evaluate each $x$ coefficient in $t$.

Starting from $I_i$, evaluate $A,C$ from (17.6), then $x=-C/A$,
$q,K,N$, and $d=N/(q_dK)$. Evaluate $P_1,V_1,T_1$ in $t$, and then
$p_1,v_1,m_1$. Apply (15.6), (15.7), and finally (15.8) in that order.
Rounding the resulting rational endpoints outward to $10^{-6}$ gives
the three tables. Every inverse in this order has a denominator
interval excluding zero. This includes the slope $A$, whose signs
are displayed, and $C_0$, whose positive enclosures are displayed.
For $h$ use (16.5), retaining the original $I_i$ and the enclosed $x$;
its interval excludes zero. The other stated nonvanishing conditions
follow from the same enclosures, or directly from the displayed coarse
intervals. For $c$ in row $4$ evaluate $r(1-r)/b$ after $b=(U-1)/2$;
this gives (19.2).

These are exact rational containments for the functions on $I_i$,
not substitutions of approximate roots. Row $1$ has $r>1$, row $2$
has $x<0$, and rows $3,5,6,7,8$ have $U<1$. Each violates a necessary
actual-world condition from (15.9). Row $4$ satisfies all three strict
inequalities. The remaining source equality and the original readings
for that row are proved next; they do not follow from inequalities
alone. ∎

## 20. The unique strict companion in the full finite C1 problem

**Definition 20.1 (The surviving complete world).** Let $t_*$ be the
fourth positive root of the exact polynomial $Q_{55}$, equivalently
the unique root in the interior of $I_4$. Put

$$
\begin{gathered}
x_*=-C(t_*)/A(t_*),\qquad
d_*=N(t_*,x_*)/(q_d(t_*)K(x_*)),\\
p_*=p_1(t_*),\quad v_*=v_1(t_*),\quad m_*=m_1(t_*).
\end{gathered}
\tag{20.1}
$$

Use (15.6)–(15.8) at these values to define $H_*,U_*,b_*,j_*,r_*$,
and put

$$
c_*=r_*(1-r_*)/b_*,\qquad
W_*=\left(
\begin{pmatrix}r_*&b_*\\c_*&1-r_*\end{pmatrix},
H_*/U_*,d_*\right).
\tag{20.2}
$$

**Theorem 20.2 (Complete finite-positive C1 classification).** For
every finite $t>0$ with $q(t)\ne0$ and $p_1(t)\ne24$, and for every
actual strict complete world in the entire child,

$$
W\in C(p_1(t),v_1(t)),\qquad
m(W)=m_1(t)\quad\Longleftrightarrow\quad
t=t_*\ \hbox{and}\ W=W_*.
\tag{20.3}
$$

The tuple $W_*$ is an actual world. Its gain is one nonzero polynomial
of degree at most three, and all of its original readings, including
the terminal $M$ reading, are

$$
(0,24,147/5,24,18,p_*,v_*,m_*).
\tag{20.4}
$$

Proof. First take any actual companion in the stated domain. The owning
interface in Assumption 16.2 and Theorem 16.4 give the zero-safe source
equations and $N-Bd=0$.
Corollary 18.4 excludes $K=0$, and Theorem 16.4 excludes $h=0$ when
$K\ne0$. Hence $B,D,h\ne0$ and $d=N/B$ is now justified. Under this
substitution $A_i=Ba_i$, and (17.2) gives

$$
F=-\frac{B^2f_0}{90D^2h},\qquad
G=\frac{B^4K_0}{324D^4h}.
\tag{20.5}
$$

Thus $F=G=0$ at the actual coordinate. The fixed resultant vanishes
even under any specialization or degree drop. Its factorization
leaves $Q_4,Q_9,Q_{12},Q_{55}$.

The first congruence in (17.8), with the unit slope $\alpha$, implies
that any common root over $Q_4$ has $h=0$. It is already excluded.
Over $Q_{12}$ the next two congruences and the units $c_2,\pi_a$ give

$$
S_2=c_2\left(x+\frac{\pi_b}{\pi_a}\right)^2.
\tag{20.6}
$$

A common root of $F,G$ annihilates $S_2$, so it has
$x=-\pi_b/\pi_a$. The last two congruences in (17.8) then give
$K=N=0$, again already excluded. Theorem 19.2 excludes positive
$Q_9$ roots. It follows that $Q_{55}(t)=0$.

The preserved degrees and the unit slope of $S_1$ force
$x=-\beta/\alpha=-C/A$. Theorem 19.2 puts $t$ in one of the eight
intervals, and Theorem 19.3 excludes all but row $4$ by necessary
strict guards. Hence $t=t_*$ and $x=x_*,d=d_*$. The faithful
projection (15.8) then fixes the source and the entire gain uniquely,
so $W=W_*$.

For existence, at $t_*$ the resultant is zero and the leading
coefficients of $F,G$ are nonzero. The classical resultant criterion
therefore gives a finite common complex root. Its linear subresultant
has nonzero slope, so every common root is the real number $x_*$.
In particular $F(t_*,x_*)=G(t_*,x_*)=0$. Theorem 19.3 gives
$B,D,h\ne0$, so (20.5) reverses to $f_0=K_0=0$.

In this row $d_*\ne0$ is a consequence of the rational bounds, not
a restriction imposed on the original domain. From (16.1),

$$
f_0=5D^2(dH_2+B_0H_0)=0.
\tag{20.7}
$$

Consequently $H_2=-B_0H_0/d$ and the projection gives
$U=-H_0/d$, hence $dU=-H_0$ and $B_0U=H_2$. Now

$$
K_0=(dD)^2\mathcal Q(U,1)=0.
\tag{20.8}
$$

The nonzero $a_1=DH_1$ and identity (16.4), used with the projected
$j,r,b$, imply $b(j-b)=r(1-r)$. The bounds $U>1$ and $0<r<1$
give $b>0$ and $c=r(1-r)/b>0$, as well as $j=b+c$. Thus the
constructed source is strict and has determinant zero.

The retained source equations can also be expressed without replacing
the original form $K_s$. Their universal polynomial identity is

$$
\begin{aligned}
d^2D^2K_s-(25d^2D^2+b_s^2)K_0
=f_0\{A_s(5dDa_2-a_0b_s)+E_sdDb_s\}.
\end{aligned}
\tag{20.9}
$$

It follows by expansion of (16.1). Since $dD\ne0$ in this row,
(20.7)–(20.8) imply the original $K_s=0$ as well.

Set $g=H/U$, $T=(U+1)/2$ and $n=xU=j+r$.
The clock-zero reading is zero because $dU=-H_0$, and clock one is
$24$ by $jH_1/U=24-d$. The clock-two reading is

$$
d+\frac{TH_2}{U}
=d+\frac{H_2+B_0}{2}=\frac{147}{5}.
\tag{20.10}
$$

The four interpolation samples give successively
$d+xH_3=24$, $d+H_4=18$, $d+(x+1)H_5=p_*$ and
$d+(x+2)H_6=v_*$. Finally $d=N/B$ in (16.6) gives
$d+(2x+3)H_7=m_*$. These are exactly the original trace readings,
not a changed set of nodes. The polynomial $g$ has degree at most
three and cannot be zero because its first two readings differ.
This proves (20.4) and actual existence. The preceding necessity
proves uniqueness in the entire original child and the equivalence
(20.3). ∎

## 21. The original-joint finite-end consequence

**Corollary 21.1 (C1 companions and the whole-child J rectangle).**
The unique companion base satisfies

$$
\begin{gathered}
(p_*,v_*)\in\operatorname{int}\mathcal K,\qquad
\mathcal K=[56,58]\times[304,305],\\
p_*\in[56979139,56979140]/10^6,\qquad
v_*\in[304497370,304497371]/10^6.
\end{gathered}
\tag{21.1}
$$

No distinct equal-$J$ pair exists anywhere in $C(p_*,v_*)$.
In particular a C1 terminal-$M$ companion relation cannot coexist
with an independently selected actual equal-$J$ pair in its child,
even when cross-pair overlap is permitted.

Proof. The bounds are row $4$ of Theorem 19.3 and are strictly
inside $\mathcal K$. Apply
[SV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md), Theorem 1.1,
which gives terminal-$J$ injectivity on every entire actual child
above $\mathcal K$. Theorem 20.2 says that this is the only base
where the C1 mixed companion relation occurs. The cited theorem
concerns all actual companions, so the selection and overlap of
the four original labels do not affect the conclusion.
The auxiliary tuple $\widehat W_1(t_*)$ has $r=1$ and is outside
$C(p_*,v_*)$; its relation to $W_*$ is consequently not itself a
distinct strict equal-$M$ pair. ∎

**Theorem 21.2 (Exclusion of a finite C1 end with a strict other end).**
There is no sequence of original joint configurations (1.1) with
selected terminal-$M$ endpoints $Z_k,Z'_k$ such that, in complete
source, drift and padded polynomial-coefficient coordinates,

$$
Z_k\longrightarrow\widehat W_1(t),\qquad
Z'_k\longrightarrow W_\infty,
\tag{21.2}
$$

where $t$ is finite, $t>0$, $q(t)\ne0$, $p_1(t)\ne24$, and
$W_\infty$ is a strict complete world. The same statement holds
after interchanging the two selected $M$ endpoints.

Proof. Matrix products and evaluation of a degree-at-most-three
polynomial at each fixed original clock are polynomial in the
complete coordinates. The common acquired bases therefore converge
to $(p_1(t),v_1(t))$, and the terminal equality passes to the limit.
The strict complete limit satisfies

$$
W_\infty\in C(p_1(t),v_1(t)),\qquad
m(W_\infty)=m_1(t).
\tag{21.3}
$$

Theorem 20.2 forces $t=t_*$ and $W_\infty=W_*$. The limiting
base is in the interior of $\mathcal K$ by (21.1), so sufficiently
late bases lie in $\mathcal K$. At each such base the original
joint configuration includes a distinct actual equal-$J$ pair,
contradicting the whole-child injectivity of SV, Theorem 1.1.
This argument uses exactly the two complete convergences (21.2);
it does not infer their existence from boundedness. ∎

**Definition 21.3 (Remaining global incidence question).** The global
question is whether $D_J\cap D_M$ is empty over all real $p\ne24,v$,
with independently distinct pairs as in (14.9). It remains open.
The finite-positive C1 classification and Theorem 21.2 concern only
the face domain (15.1)–(15.3) and the complete limits (21.2);
they impose no global compactness hypothesis, no uniform bound away
from $r=1$, and no relation between the two common terminal values
of an original joint configuration.

## 追加锚（本行以下为增补区）
## 22. The original joint domain and its uniform suppliers

**Definition 22.1 (The selected-endpoint domain).** Retain the complete
worlds of Definition 1.1, the entire children of Definitions 1.1 and
14.1, and the original left products of
[O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions
1.1–1.3. Thus

$$
\begin{gathered}
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\\
g(s)=\sum_{\ell=0}^3\gamma_\ell s^\ell\ne0,\qquad d\in\mathbb R.
\end{gathered}
\tag{22.1}
$$

The coefficient vector is padded by zeros when the degree is below
three. Each world has this one whole gain and this fixed drift. With
$J,M,Q_i$ as in Definition 1.1, its acquired equations are

$$
\bigl(d+g(i)\operatorname{tr}(Q_iP)\bigr)_{i=0}^6
=(0,24,147/5,24,18,p,v),
\qquad (E_1,\ldots,E_6)=(J,M,J,M,M,M).
\tag{22.2}
$$

At the same original clock seven, the alternatives are

$$
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7),
\tag{22.3}
$$

where $j=b+c$, $n=j+r$, $T=1+b$, $U=1+2b$. In O's notation these
are $f_{MJ},f_{MM}$, respectively. Write $\mathscr Q$ for the set of
all tuples $Q=(p,v,W_0,W_1,W_2,W_3)$ satisfying

$$
\begin{gathered}
p,v\in\mathbb R,\quad p\ne24,\quad W_i\in C(p,v)\quad(0\le i\le3),\\
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\end{gathered}
\tag{22.4}
$$

Distinctness is distinctness of complete worlds. The two pairs are
independent, cross-pair overlap is allowed, and their common terminal
values are independent. Put

$$
\delta(W)=\min\{r(W),1-r(W),b(W),c(W)\},\qquad
\mathscr E_M=\{W_i:Q\in\mathscr Q,\ i\in\{2,3\}\}.
\tag{22.5}
$$

The second set records occurrence at a selected $M$ label. Zero drift,
vanishing gain samples, degree drops, repeated roots and singular
parent strata retain the domain (22.1)–(22.4).

**Lemma 22.2 (Uniform data on the original domain).** There are finite
$P_J,V_J>0$, $C_J\ge1$ and positive $\epsilon,\eta,\alpha$, independent
of $Q\in\mathscr Q$ and of its labels, such that

$$
|p|\le P_J,\qquad |v|\le V_J,\qquad |p-24|\ge\epsilon,
\tag{22.6}
$$

and every actual companion $W\in C(p,v)$ of such a base satisfies

$$
0<b(W),c(W)\le C_J,\qquad |d(W)|\le C_J,\qquad
\max_{0\le\ell\le3}|\gamma_\ell(W)|\le C_J.
\tag{22.7}
$$

The selected $M$ endpoints satisfy

$$
\begin{gathered}
j(W_i)\ge\eta\quad(i=2,3),\qquad
\max\{\delta(W_2),\delta(W_3)\}\ge\alpha,\\
r(W_i)\ge\rho_0\quad(i=2,3)
\end{gathered}
\tag{22.8}
$$

for a choice $0<\rho_0\le1/4$ independent of the configuration.

Proof. The pair $W_0,W_1$ in (22.4) places the base in $D_J$.
[III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Theorem 7.1,
therefore gives $P_J$, uniformly in $v$. III, Corollary 8.1, gives
$V_J$ and (22.7) for every companion of that entire child; enlarge
$C_J$ to at least one. These bounds control $c$ and every padded
coefficient, as well as $b$ and drift.

The independently selected distinct $M$ pair permits application of
[SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Theorem 29.1.
Since $p\ne24$, its gap gives $|p-24|\ge\epsilon$. Thus the bases lie
in III, Corollary 8.2's closed bounded ambient base set. SII, Theorem
23.1, applies to this same $M$ pair for every real $v$ and gives both
$j$ bounds, without a further bound on $p$.

At $|p|\le P_J$, SII, Theorem 14.3, gives the maximum bound in
(22.8) with $\alpha=\varepsilon(P_J)>0$. It chooses at least one
endpoint of this pair. SII, Theorem 15.1, places such an endpoint in
a compact strict-parent set, refined to the off-$24$ parent over
the base enclosure (22.6). These are precisely the anchor suppliers
used in Assumption 7.1; they do not assert two strict anchors in the
selected $M$ pair.

For its lower-face supplier, SII, Theorem 21.2, concerns exactly
sequences of (22.4) with a finite off-$24$ base limit. Its label
$L(t)$ is $B_0(t)=(0,0,t)$ of Definition 1.3. At this face the
undivided original parent is

$$
e\,\frac{8(t-1)}t=\frac{12}{5}.
\tag{22.9}
$$

Thus a finite drift excludes $t=1$ before any division, and SII,
Theorem 21.2, supplies exactly the remaining $t>0,t\ne1$ exclusion.
The bounds (22.7) give the required finite complete limits whenever
subsequences are taken. The other possible lower face is the $C_0$
face of Definition 2.1, excluded with a strict $M$ mate by Theorem
6.1. All six suppliers of Assumption 7.1 consequently hold on
(22.4), with their original quantifiers. Theorem 7.2 gives a common
positive lower bound for both selected $r$ coordinates; reduce it to
at most $1/4$ and call it $\rho_0$. When $\mathscr Q$ is empty one
may instead choose $\rho_0=1/4$. This proves (22.6)–(22.8) without an
additional condition on the joint locus. ∎

## 23. Finite whole-world limits at the upper source faces

**Definition 23.1 (Upper-face notation).** For finite $t>0$ write

$$
\begin{gathered}
B_1(t)=(1,0,t),\qquad C_1(t)=(1,t,0),\\
q_B(t)=5(2t^2-1),\qquad f_C(t)=t^3-4t-2,\qquad
q_C(t)=(t+1)f_C(t).
\end{gathered}
\tag{23.1}
$$

Here $q_C=q$ of Definition 15.1 and $q_d=5q_C$ there. The complete
$B_1$ label $R(t)$ means exactly
[S](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md), Definition 19.1,
with denominator $q_B$. The complete $C_1$ label
$\widehat W_1(t)$ means (15.1)–(15.2). Both labels are nonstrict
auxiliary tuples. Their drifts and gains are part of the labels;
their source triples alone do not specify a different gain fit.

**Lemma 23.2 (Undivided finite upper-face identification).** Suppose a
finite tuple $(P,g,d)$, with a degree-at-most-three whole polynomial,
satisfies the original acquired equations and has source

$$
r=1,\qquad b,c\ge0,\qquad bc=0,\qquad b+c>0.
\tag{23.2}
$$

Then exactly one of the following holds:

1. Its source is $B_1(t)$ for a finite $t>0$, $q_B(t)\ne0$, and
   the complete tuple is $R(t)$.
2. Its source is $C_1(t)$ for a finite $t>0$, $q_C(t)\ne0$, and
   the complete tuple is $\widehat W_1(t)$.

In the second case its acquired base and terminal-$M$ response are
$(p_1(t),v_1(t),m_1(t))$ of Definition 15.1, and

$$
p_1(t)=24\quad\Longleftrightarrow\quad t=1/8.
\tag{23.3}
$$

Proof. In (23.2), exactly one of $b,c$ is positive. Denote it by
$t$. The original traces $j,n,T,U$ are positive on either resulting
face, so the undivided parent and first four samples of Definition
1.2 apply. With $e=d-24$, they are

$$
\begin{gathered}
e\Lambda=-\frac{24}{5}(b-1/8)\kappa,\qquad
\kappa=\frac{2(2+5b)}{(1+b)(1+2b)},\\
(g(0),g(1),g(2),g(3))
=\left(-24-e,-\frac ej,\frac{27/5-e}{T},-\frac en\right).
\end{gathered}
\tag{23.4}
$$

These are necessary identities before division by $\Lambda$. They
also hold at finite limits of actual worlds, since $j,n,T,U$ have
positive limits there.

At $B_1(t)$ the traces are $j=t,n=t+1,T=U=1$. The first equation
of (23.4) is

$$
e\,\frac{4(2t^2-1)}{t(t+1)}=\frac{12}{5}.
\tag{23.5}
$$

If $2t^2-1=0$ this is impossible for finite $e$. Otherwise it forces

$$
e=\frac{3t(t+1)}{q_B},\qquad
(g(0),g(1),g(2),g(3))
=\left(-24-e,-\frac{3(t+1)}{q_B},
\frac{27}{5}-e,-\frac{3t}{q_B}\right).
\tag{23.6}
$$

These are precisely the drift and four original samples of S,
Definition 19.1. Uniqueness of degree-at-most-three interpolation at
$0,1,2,3$ identifies the entire polynomial with $g_R$, hence the
complete tuple with $R(t)$. All late responses are consequently
the responses of that same label.

At $C_1(t)$ the traces are $j=t,n=T=t+1,U=2t+1$, and the undivided
parent instead reads

$$
e\,\frac{2f_C(t)}{t(t+1)(2t+1)}
=-\frac{6(8t-1)(5t+2)}{5(t+1)(2t+1)}.
\tag{23.7}
$$

All displayed denominators are positive. If $q_C(t)=0$, then
$f_C(t)=0$. A finite $e$ would require $(8t-1)(5t+2)=0$.
For $t>0$ this requires $t=1/8$, whereas

$$
f_C(1/8)=-1279/512\ne0.
\tag{23.8}
$$

Thus no finite tuple occurs at the pole. Away from it (23.7) forces

$$
e_C=-\frac{3t(8t-1)(5t+2)}{5f_C(t)},\qquad d=24+e_C=d_1,
\tag{23.9}
$$

and the four original samples are

$$
\left(-24-e_C,-e_C/t,
\frac{27/5-e_C}{t+1},-\frac{e_C}{t+1}\right).
\tag{23.10}
$$

They determine exactly $g_1$ of (15.2). In particular the late
readings do not introduce independent samples. For these four fixed
nodes the evaluation rows at clocks $5,6,7$ are respectively

$$
(-4,15,-20,10),\qquad
(-10,36,-45,20),\qquad
(-20,70,-84,35).
\tag{23.11}
$$

Multiplying them by (23.10) and using the original trace factors
$3t+2,5t+3,8t+5$ gives exactly $p_1,v_1,m_1$ of (15.1)–(15.2).
This is the fixed-node Lagrange interpolation formula; see
Berrut–Trefethen, [§2](https://doi.org/10.1137/S0036144502417715).

The identity (15.5), in the present notation, is

$$
p_1(t)-24
=-\frac{6(8t-1)(7t^3+11t^2+19t+10)}{5q_C(t)}.
\tag{23.12}
$$

Its cubic factor is positive for $t>0$. At $t=1/8$ the parent has
$\Lambda\ne0$ and forces $e_C=0$, giving the original samples
$(-24,0,24/5,0)$. The first row of (23.11) then gives $g_1(5)=0$
and hence $p_1=24$. This includes the zero-$e$ and sampled-zero
branch rather than dividing it away, and proves (23.3).

The interpolating gain in either case is nonzero: an identically
zero gain would make the original readings at clocks zero and one
both equal to $d$, contrary to $0\ne24$. The argument divides by
neither drift, $e$, a gain value, a leading gain coefficient nor a
degree condition. It therefore identifies whole gains even at degree
drops and all allowed sampled zeros. ∎

## 24. A uniform upper-face floor for both selected M labels

**Theorem 24.1 (Global selected-M upper-face floor).** There is one
$0<\rho_1\le1/4$ such that

$$
\forall Q\in\mathscr Q\quad\forall i\in\{2,3\},\qquad
1-r(W_i)\ge\rho_1.
\tag{24.1}
$$

Proof. If $\mathscr Q$ is empty choose $\rho_1=1/4$. Otherwise suppose
there is no common positive lower bound. For each positive integer
$k$ choose an original tuple $Q_k$ and one of its selected $M$
endpoints with $1-r<1/k$. Call this endpoint $X_k$ and its selected
$M$ mate $Y_k$. This merely relabels within that pair; it preserves
both within-pair distinctness conditions in (22.4), the independently
chosen $J$ pair and all allowed cross-pair overlap.

Lemma 22.2 bounds the bases and both complete coordinate vectors

$$
\xi(W)=(r,b,c,d,\gamma_0,\gamma_1,\gamma_2,\gamma_3).
\tag{24.2}
$$

Finite-dimensional bounded-sequence extraction gives simultaneous
subsequences with

$$
(p_k,v_k)\longrightarrow(p_\infty,v_\infty),\qquad
\xi(X_k)\longrightarrow\xi(X),\qquad
\xi(Y_k)\longrightarrow\xi(Y).
\tag{24.3}
$$

Here the limits include $c$, each fixed drift and all four padded
coefficients of each original whole gain. This is the classical
Bolzano–Weierstrass theorem in a finite Euclidean product, applied
to these bounded coordinates, not to an assumed closed joint locus.
The source relations and the closed inequalities (22.6) pass to the
limit. In particular

$$
\begin{gathered}
p_\infty\ne24,\qquad |p_\infty-24|\ge\epsilon,\qquad r(X)=1,\\
b(X)c(X)=0,\qquad
b(X)+c(X)\ge\eta,\qquad 0\le b(X),c(X)\le C_J.
\end{gathered}
\tag{24.4}
$$

Consequently exactly one of $b(X),c(X)$ is positive. Its value
$t$ satisfies $\eta\le t\le C_J$. Thus $X$ has precisely source
$B_1(t)$ or $C_1(t)$, with finite $t>0$. The corner $b=c=0$,
a zero face parameter and an infinite face parameter are excluded
by these derived inequalities.

Since $\delta(X_k)\le1-r(X_k)\longrightarrow0$, the maximum bound
in (22.8) forces $\delta(Y_k)\ge\alpha$ for all sufficiently large
$k$. Its limiting source is therefore strict. For each original
clock, matrix multiplication, trace and evaluation of a padded
polynomial are polynomial functions of (24.2). The seven original
acquired equations and the terminal-$M$ equality pass continuously
to the limits. Neither limiting gain is zero, because that would
make its clock-zero and clock-one readings equal to the same drift.
It follows that

$$
Y\in C(p_\infty,v_\infty),\qquad m(Y)=m(X),
\tag{24.5}
$$

where $Y$ is an actual strict complete world. At $X$ all four traces
$j,n,T,U$ have positive limits. Thus (23.4) identifies the limiting
whole gain from the same four original samples, without any
late-clock refitting.

If $X$ has source $B_1(t)$, Lemma 23.2 first excludes $q_B(t)=0$
by the undivided equation (23.5), and then identifies $X=R(t)$.
The bases converge to a finite off-$24$ point, the first endpoint
converges entrywise in its entire source including $c$ and
coefficientwise in its whole gain, and the other endpoint converges
to the strict complete $Y$. These are exactly the hypotheses of S,
Corollary 21.3. That corollary excludes this sequence of original
joint configurations.

If $X$ has source $C_1(t)$, Lemma 23.2 first excludes $q_C(t)=0$
using the undivided equation (23.7), and then identifies

$$
X=\widehat W_1(t),\qquad
(p_\infty,v_\infty)=(p_1(t),v_1(t)).
\tag{24.6}
$$

The off-$24$ gap supplies $p_1(t)\ne24$ and, by (23.3), excludes
the $t=1/8$ branch. The two complete convergences (24.3) now satisfy
every hypothesis of Theorem 21.2, which excludes this sequence.
In particular its classification premise is exactly Theorem 20.2
on all finite positive nonpole off-$24$ C1 parameters and all
actual strict companions in the entire child. Equation (24.5)
is such a companion relation; no regularity or gain-sample condition
has been inserted.

The open-neighbourhood implication in this C1 exclusion can also
be read directly from the classification. Theorem 20.2 forces
$t=t_*$ and $Y=W_*$, and Corollary 21.1 puts the limiting base in
the closed rectangle

$$
\mathcal R_*=
\frac{[56979139,56979140]}{10^6}
\times\frac{[304497370,304497371]}{10^6}
\subset\operatorname{int}\mathcal K,
\qquad \mathcal K=[56,58]\times[304,305].
\tag{24.7}
$$

Its four margins to the boundary of $\mathcal K$ are all greater
than $1/4$. Hence the open sup-norm ball of radius $1/4$ about
each point of $\mathcal R_*$ is contained in
$\operatorname{int}\mathcal K$. All sufficiently late actual
bases $(p_k,v_k)$ therefore lie in $\mathcal K$.
[SV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md), Theorem 1.1,
makes $J$ injective on each entire actual child above those bases.
This contradicts its selected distinct equal-$a$ pair in (22.4).
The contradiction occurs at the actual bases and does not require
limits of the $J$ endpoints or distinctness of any such limits.

Both exhaustive upper-face alternatives are impossible. If the
infimum of $1-r$ on $\mathscr E_M$ were zero, the sequence just
excluded would exist. That infimum is therefore positive. Reducing
a positive lower bound to at most $1/4$ proves (24.1) for both
selected labels simultaneously. ∎

**Definition 24.2 (A qualitative choice of the upper floor).** For
$\mathscr Q\ne\varnothing$ put

$$
h_M=\inf\{1-r(W_i):Q\in\mathscr Q,\ i\in\{2,3\}\},\qquad
\rho_1=\min\{1/4,h_M\}.
\tag{24.8}
$$

Theorem 24.1 gives $h_M>0$. This choice depends only on the original
joint domain, and not on a configuration or an endpoint label. The
proof establishes existence from the uniform complete-coordinate
bounds, the off-$24$ gap, the selected-pair sum floor and maximum
anchor, S's B1 end exclusion, and Theorems 20.2–21.2 with SV,
Theorem 1.1. It supplies no numerical value or computable modulus
for $h_M$ or $\rho_1$. For $\mathscr Q=\varnothing$ define
$\rho_1=1/4$.

## 25. The full source collar and a strict endpoint enclosure

**Theorem 25.1 (Global source collar at both selected M endpoints).**
Choose $C_J\ge1$ and $0<\rho_0,\rho_1\le1/4$ as in Lemma 22.2
and Theorem 24.1, and set

$$
\beta=\frac{\rho_0\rho_1}{C_J}>0.
\tag{25.1}
$$

For every $Q\in\mathscr Q$ and each $i\in\{2,3\}$,

$$
\begin{gathered}
r(W_i)\ge\rho_0,\qquad 1-r(W_i)\ge\rho_1,\\
\beta\le b(W_i),c(W_i)\le C_J,\qquad
\delta(W_i)\ge\beta.
\end{gathered}
\tag{25.2}
$$

If $\mathscr Q=\varnothing$, valid choices are
$\rho_0=\rho_1=1/4$ and $\beta=1/(16C_J)$.

Proof. The two diagonal floors follow from Lemma 22.2 and Theorem
24.1. The original source relation gives

$$
bc=r(1-r)\ge\rho_0\rho_1.
\tag{25.3}
$$

Divide this inequality by the positive upper bound $C_J$ for the
other off-diagonal entry to obtain $b,c\ge\beta$. Their upper
bounds are (22.7). Since $C_J\ge1$ and both diagonal floors are
at most $1/4$, $\beta\le\rho_0,\rho_1$. This proves the $\delta$
bound. On an empty domain the displayed universal statements hold
for the stated choices. The dependence (25.1) is explicit in these
qualitative constants and asserts no computed modulus. ∎

**Corollary 25.2 (Compact enclosures of individual selected endpoints).**
The source of each $W\in\mathscr E_M$ lies in the compact set

$$
\mathcal S_M=\left\{(r,b,c):
\rho_0\le r\le1-\rho_1,\quad
\beta\le b,c\le C_J,\quad bc=r(1-r)\right\}.
\tag{25.4}
$$

There is also a compact enclosure of these individual endpoints
in the strict off-$24$ complete parent, including each fixed drift
and each whole gain.

Proof. The set (25.4) is closed and bounded in $\mathbb R^3$ and is
contained in the strict source domain. Let

$$
\mathcal K_{\rm base}=
\{(p,v):|p|\le P_J,\ |v|\le V_J,\ |p-24|\ge\epsilon\}.
\tag{25.5}
$$

In the finite coordinate space of $(p,v,\xi(W))$, impose
$(p,v)\in\mathcal K_{\rm base}$, $(r,b,c)\in\mathcal S_M$,
$|d|\le C_J$, $|\gamma_\ell|\le C_J$ for $0\le\ell\le3$, and
all seven original acquired equations (22.2). Denote the resulting
set by $\mathcal B_M$. All of these are closed conditions in a
bounded Euclidean box: the acquired equations are polynomial in
these complete coordinates. Hence $\mathcal B_M$ is compact by the
finite-dimensional closed-and-bounded criterion.

Every point of $\mathcal B_M$ has a strict source, degree at most
three, and a fixed drift. Its gain cannot be identically zero,
because the first two acquired equations would then give $d=0$
and $d=24$. It is therefore an actual complete world, with its
base separated from $p=24$. Projection to $\xi(W)$ is continuous,
so its image is a compact subset of the strict off-$24$ full
parent. Lemma 22.2 and Theorem 25.1 put every member of
$\mathscr E_M$ in this image. The construction uses only the
original polynomial equations and finite-dimensional compactness;
it imposes no inequality on a sampled gain, no exact-degree
condition and no regular-source condition. ∎

## 26. The remaining original interior incidence problem

**Definition 26.1 (Incidence inside the endpoint enclosure).** The
remaining existence question is whether there are real $p\ne24,v$
and four actual complete worlds satisfying (22.4), with the two
selected $M$ endpoints in the enclosure of Corollary 25.2. By
Theorem 25.1 this is equivalent to the original question
$\mathscr Q\ne\varnothing$, or $D_J\cap D_M\ne\varnothing$.
Its existence or nonexistence remains open.

The collar is quantified by occurrence at a selected $M$ label.
A world occupying both an $M$ and a $J$ label inherits it through
its $M$ role. No lower collar for a world in only a $J$ role or
for an unused companion is asserted. The all-companion upper
bounds (22.7) have their separate entire-child quantifier.

The set $\mathcal B_M$ encloses individual endpoints. It does not
impose the condition that an endpoint has a distinct equal-$m$
mate or that the same base has a distinct equal-$a$ pair. Those
distinctness conditions are not closed conditions in the complete
coordinates. The enclosure thus proves neither closedness nor
compactness of the selected-pair or joint relation. It gives no
uniform pair separation, no global augmented-$M$ immersion and
no construction or exclusion of the remaining strict interior
incidence.

The separate compact regions of III, Theorem 23.2, concern its
specified $10\le p\le34$ output region and actual $J$ arc.
[SVI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md), Theorem 11.2,
gives an all-companion collar only over its region
$10\le p\le34$, $0\le v\le200$,
$v\ge(37p+426)/10$. SVI, Theorem 6.2, concerns regular worlds with
$10\le p\le34$. None of these restricted domains is substituted
for the arbitrary bounded ambient joint base set (25.5). The
global conclusion here is precisely (24.1) and its source
consequence (25.2), with the unchanged joint quantifiers (22.4).

## 追加锚（本行以下为增补区）
