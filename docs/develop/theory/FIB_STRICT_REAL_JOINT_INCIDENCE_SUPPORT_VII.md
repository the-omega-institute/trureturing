# FIB strict-real joint incidence: fixed-b separation and a faithful crossing chart

## 1. Complete worlds and the original joint question

This volume uses the complete worlds of
[O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3.
Write [F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
[S](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md),
[SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md),
[SIII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
[SIV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md), and
[SV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md) for the related suppliers.


**Definition 1.1 (Original complete world).** A world is a triple

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\qquad 0<r<1,\quad b>0,
$$

where $0\ne g\in\mathbb R[s]$, $\deg g\le3$, and $d\in\mathbb R$.
Put

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
$$

The acquired actions are $J,M,J,M,M,M$, and the original clocks $0,\ldots,6$
have readings

$$
(0,24,147/5,24,18,p,v).
\tag{1.1}
$$

Let $\mathcal H$ be the entire parent with the first five readings, and let
$C(p,v)$ contain every world realizing (1.1). At clock seven set

$$
a(W)=d+g(7)\operatorname{tr}(JQ_6P),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
$$

Each world uses one fixed source, one entire polynomial and one fixed drift in
all these expressions. Lower degrees, sampled zeros, repeated gain roots, zero
drift and singular parent sources are retained. Distinctness is distinctness of
complete triples. No source boundary is an actual world.

The original question is whether there exist real $p\ne24,v$ and

$$
\begin{gathered}
W_{J0}\ne W_{J1},\quad W_{M0}\ne W_{M1},\qquad
W_{J0},W_{J1},W_{M0},W_{M1}\in C(p,v),\\
a(W_{J0})=a(W_{J1}),\qquad m(W_{M0})=m(W_{M1}).
\end{gathered}
\tag{1.2}
$$

The two pairs are independently chosen in the same entire child. They may
share endpoints, and their two common terminal values may differ. Equivalently,
with $D_J,D_M$ the actual pair images defined by these separate equalities,
the question is whether $D_J\cap D_M$ is nonempty. The results below leave this
question open.

## 2. The inherited full-parent interface and a regular polynomial circuit

Set

$$
\begin{gathered}
c=r(1-r)/b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
e=d-24,\quad L=b^2+8b+4,\quad A=(8b-1)(5b+2),\\
\Lambda=\frac{2L}{TU}-\frac4j-\frac4n
=1+\frac6T+\frac1U-\frac4j-\frac4n,\\
\mathcal P=e\Lambda+\frac{6A}{5TU}.
\end{gathered}
\tag{2.1}
$$

The full-parent converse is O, Theorem 2.1, at $\beta=1/8$: strict
$(r,b,e)$ gives an actual parent world if and only if $\mathcal P=0$.
Its complete gain is the unique interpolant at nodes $0,1,2,3$ with samples

$$
(q_0,q_1,q_2,q_3)
=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right),
\qquad
g(s)=\sum_{k=0}^3q_k\prod_{\substack{0\le l\le3\\l\ne k}}
\frac{s-l}{k-l}.
\tag{2.2}
$$

To fix the correspondence explicitly, the original traces at clocks $0,\ldots,6$
are $(1,j,T,n,U,U+n,2U+n)$, and the terminal traces are
$T+2j+4r$ and $3U+2n$. The interpolation rows at $4,5,6,7$ are

$$
\begin{array}{c|rrrr}
4&-1&4&-6&4\\
5&-4&15&-20&10\\
6&-10&36&-45&20\\
7&-20&70&-84&35
\end{array}.
\tag{2.3}
$$

In particular

$$
g(4)-\frac{-6-e}{U}=\mathcal P.
\tag{2.4}
$$

Thus the parent equation is sufficient as well as necessary. The original
unequal readings $0,24$ exclude the zero polynomial. This interface divides
only by the positive source factors $T,U,j,n$ and the fixed nonzero node
differences. It includes $\Lambda=0$, where the parent forces $A=0$, hence
$b=1/8$, while the drift can remain free. We use this inherited correspondence
throughout, without restricting its gain strata.

For a regular source define the following polynomial circuit, initially in
independent $b,j,n$ (and $r$ for $N_a$):

$$
\begin{aligned}
D&=5\bigl(Ljn-2TU(j+n)\bigr),\\
C_0&=-24D+3Ajn,& C_1&=3An,\\
C_2&=3(49b+34)jn-54U(j+n),& C_3&=3Aj,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
B_7&=-20C_0+70C_1-84C_2+35C_3,\\
N_p&=-C_0+(U+n)B_5,&N_v&=-C_0+(2U+n)B_6,\\
N_a&=-C_0+(T+2j+4r)B_7,&N_m&=-C_0+(3U+2n)B_7.
\end{aligned}
\tag{2.5}
$$

The exact normalization is

$$
D=\frac52TUjn\Lambda.
\tag{2.6}
$$

For $D\ne0$, substitution in (2.1)–(2.2) gives

$$
d=-C_0/D,\qquad q_k=C_k/D,\qquad
(p,v,a,m)=(N_p,N_v,N_a,N_m)/D.
\tag{2.7}
$$

Conversely a strict source with $D\ne0$ has precisely this whole-world lift.
The circuit is another denominator choice for SII, Definitions 2.1–2.2 and
Proposition 2.3; the identification follows directly from the displayed gain
samples, rather than from equality of projected images alone. We use (2.5)
only with its regular guard. The parent equation (2.1) remains the interface
on $D=0$.

## 3. Two global residual identities and the exact M comparator

**Theorem 3.1 (Zero-safe residual packaging).** Define

$$
\begin{aligned}
S={}&(-29b-10-32n)jn+5(b+2)(U+n)n+10(3b+2)Uj,\\
C={}&(5235b+2526+960n)jn\\
&-\bigl[U(530b+1052)+n(140b+296)\bigr]n
-U(3025b+2050)j.
\end{aligned}
\tag{3.1}
$$

Every actual strict parent world, including $\Lambda=D=0$, satisfies

$$
p-24=\frac{eS}{(5b+2)jn},\qquad
5m-32v+1128=\frac{eC}{(5b+2)jn}.
\tag{3.2}
$$

Proof. Temporarily let $b,j,n,e$ be independent with $T,U,j,n>0$, use
(2.2)–(2.3), and form $p,v,m$ from their original traces. Before imposing
the parent equation, the exact residual identities are

$$
\begin{aligned}
(5b+2)jn(p-24)-eS
 &=10U(U+n)jn\mathcal P,\\
(5b+2)jn(5m-32v+1128)-eC
 &=-10U(170b+89+30n)jn\mathcal P.
\end{aligned}
\tag{3.3}
$$

These are rational identities in the four independent variables. Substituting the three interpolation rows and collecting the
constant term and the coefficient of $e$ separately gives both identities. For example,
$g(5)=96-108/T+e(4-15/j+20/T-10/n)$; the analogous clock-six and
clock-seven rows give the second identity. Multiplication by $TU$ leaves
ordinary polynomial identities, so no parent or source relation is hidden
in this expansion. Set $\mathcal P=0$ and divide by the positive
$(5b+2)jn$ to obtain (3.2). There was no division by $\Lambda$ or $D$.
The normalization in (2.5) also gives

$$
N_p-24D=-3(8b-1)S,\qquad
5N_m-32N_v+1128D=-3(8b-1)C.
\tag{3.4}
$$

Both are polynomial identities before any source substitution. ∎

**Corollary 3.2 (Exact comparator on the full off-24 child).** In every actual
$C(p,v)$ with $p\ne24$, each world's $e,S$ is nonzero. Put
$\Theta=C/(5S)$. Then

$$
m=\frac{32v}{5}-\frac{1128}{5}+(p-24)\Theta.
\tag{3.5}
$$

For any two worlds $W_2,W_3$ in this same child,

$$
m(W_2)=m(W_3)
\quad\Longleftrightarrow\quad
C(W_2)S(W_3)-C(W_3)S(W_2)=0.
\tag{3.6}
$$

Proof. The first identity of (3.2) forces $eS\ne0$. Divide the second
by the first and use the common $p,v$. The multiplier $p-24$ is nonzero,
so equality of $m$ is equality of $C/S$. ∎

The corollary does not require regularity, a selected $J$ pair, any constraint
on cross-pair overlap, or an equality between the $J$ and $M$ common values.
The earlier mirror nonaccumulation and uniform off-24 gap are reused in
Section 11; they are not additional conclusions claimed from this packaging.

## 4. Global fixed-b separation

**Theorem 4.1 (Complete-world injectivity at fixed b).** Let $W_1,W_2$ be any
two actual strict parent worlds. If

$$
b(W_1)=b(W_2),\qquad
p(W_1)=p(W_2)\ne24,\qquad
v(W_1)=v(W_2),\qquad m(W_1)=m(W_2),
\tag{4.1}
$$

then $W_1=W_2$ as complete triples.

Consequently every distinct actual terminal-$M$ pair in an off-24 child has
different $b$ coordinates. The theorem is global in $b>0$ and $0<r<1$; it
requires neither regularity nor fixed gain degree, nonzero drift, gain
positivity, nonzero gain samples, simple roots, or endpoint separation.
Its proof occupies Sections 5–8.

The condition $p\ne24$ is essential. Reuse the mirror family of O,
Definition 16.1: take $b=1/8$, $r_1=1/4$, $r_2=7/8$,
$d_1=d_2=24$, and

$$
g_1(s)=g_2(s)=\frac85(s-1)(s-3)(s-5).
\tag{4.2}
$$

Both complete worlds have exact readings
$(0,24,147/5,24,18,24,129)$ and terminal $M=600$. They are distinct,
strict, and have the same $b$. This is a reused $p=24$ counterexample,
not a witness for (1.2).

## 5. Rank, exceptional cases and a necessary involution

In this section $b$ is common to the two worlds. The undivided parent gives

$$
\frac e j=\frac{Le}{2TU}-\frac e n+\frac{3A}{10TU}.
\tag{5.1}
$$

Use the coefficients

$$
\begin{array}{lll}
K=\dfrac{3(8b-1)(b+2)}{2TU},&&
\alpha=\dfrac{b^2-16b-12}{2TU},\\
V_0=\dfrac{3(80b^2+192b+31)}{5TU},&&
\beta=\dfrac{2b^2-24b-17}{TU},\\
M_0=\dfrac{3(200b^2+503b+114)}{5TU},&&
\gamma=\dfrac{5b^2-52b-36}{TU}.
\end{array}
\tag{5.2}
$$

Substitute (5.1) into the fixed-node response rows. The resulting identities
on the entire parent are

$$
\begin{aligned}
p-24&=K(U+n)+e\left[6+\alpha(U+n)+\frac{5U}{n}\right],\\
v-24&=V_0(2U+n)+e\left[17+\beta(2U+n)+\frac{32U}{n}\right],\\
m-24&=M_0(3U+2n)+e\left[71+\gamma(3U+2n)+\frac{105U}{n}\right].
\end{aligned}
\tag{5.3}
$$

The first two reductions reuse the undivided interpolation identities of
SIV, Theorem 8.2. The last follows by the same clock-seven row. Equation
(5.1), not division by $\Lambda$, justifies all three globally.

For differences $\Delta f=f(W_2)-f(W_1)$ form

$$
\mathsf M=10TU
\begin{pmatrix}
K&6+\alpha U&\alpha&5U\\
V_0&17+2\beta U&\beta&32U\\
2M_0&71+3\gamma U&2\gamma&105U
\end{pmatrix}.
\tag{5.4}
$$

Equality of the three responses says that
$(\Delta n,\Delta e,\Delta(en),\Delta(e/n))$ lies in its kernel. Define

$$
\begin{aligned}
k_0&=5U(50b^4-1137b^3-842b^2-1442b-1262),\\
k_1&=3TU(11209b+37242),\\
k_2&=3U(-2000b^4+13092b^3+74938b^2+88421b+33300),\\
k_3&=3(-1289b^3+12511b^2+66211b+38698).
\end{aligned}
\tag{5.5}
$$

Direct multiplication and a minor expansion give the exact certificates

$$
\mathsf M k=0,\qquad
\det\mathsf M_{[:,\{0,2,3\}]}=-100TU^2k_1<0.
\tag{5.6}
$$

Here the removed column is the $\Delta e$ column, and the remaining columns
retain their order. All entries are polynomials after the stated scaling.
Thus $\operatorname{rank}\mathsf M=3$ for every $b>0$, and for one real
$\lambda$

$$
(\Delta n,\Delta e,\Delta(en),\Delta(e/n))=\lambda(k_0,k_1,k_2,k_3).
\tag{5.7}
$$

We now handle the equal-$n$ case before dividing by any of these quantities.
Suppose two distinct worlds satisfying (4.1) had $n_1=n_2$. If $r_1\ne r_2$,
the source identity

$$
n=b+\frac{r(1+b-r)}b
\tag{5.8}
$$

gives $r_1+r_2=1+b$; strict $r_i<1$ then implies $b<1$. If $r_1=r_2$,
the source is the same. Distinct worlds must have different $e$, since
(2.2) fixes the entire gain from source and $e$. The parent then forces
$\Lambda=A=0$, giving $b=1/8<1$. Hence either kind of distinct equal-$n$
pair requires $0<b<1$.

On this range $k_0<0$: use $50b^4<50b^3$ in its displayed polynomial.
The first coordinate of (5.7) forces $\lambda=0$, then $\Delta e=0$.
Corollary 3.2 gives $e\ne0$; (5.1) therefore determines the same $j$ from
common $b,n,e$, hence the same $r=n-j$. The whole gain and drift are equal
by (2.2), a contradiction. We have proved that any hypothetical distinct
collision has

$$
\Delta n\ne0,\qquad \lambda\ne0,\qquad k_0\ne0.
\tag{5.9}
$$

Write $x=n_1$, $y=n_2$. The identities

$$
\begin{aligned}
\Delta(en)&=y\Delta e+e_1\Delta n,\\
\Delta(e/n)&=\frac{x\Delta e-e_1\Delta n}{xy}
\end{aligned}
$$

and (5.7) give, without a further rank assumption,

$$
\begin{gathered}
k_3xy-k_1(x+y)+k_2=0,\\
e_1=\frac{x(k_1-k_3y)}{k_0},\qquad
e_2=\frac{y(k_1-k_3x)}{k_0}.
\end{gathered}
\tag{5.10}
$$

For example the two difference identities first give
$k_2-yk_1=k_0e_1$ and $k_3xy=xk_1-k_0e_1$; their sum gives the first
line, which converts the first expression for $e_1$ to the displayed one.
Because $e_i\ne0$ and $x,y>0$, both $k_3x-k_1$ and $k_3y-k_1$ are
nonzero. Put

$$
L_k=k_2k_3-k_1^2,\qquad H_b(n)=\frac{k_1n-k_2}{k_3n-k_1}.
\tag{5.11}
$$

Then

$$
y=H_b(x),\quad x=H_b(y),\qquad
e_1=\frac{xL_k}{k_0(k_3x-k_1)},\quad
 e_2=\frac{yL_k}{k_0(k_3y-k_1)}.
\tag{5.12}
$$

In particular $L_k\ne0$. The matrix
$\left(\begin{smallmatrix}k_1&-k_2\\k_3&-k_1\end{smallmatrix}\right)$
has square $-L_k I$, which also verifies the involution.
All nonzero denominators in (5.10)–(5.12) have been derived from the
hypothetical distinct off-24 collision.

## 6. Exclusion for b at least five halves

For $b\ge1$, (5.8) and $0<r<1$ give

$$
b<n<b+1,
$$

because $b-r(1+b-r)=(1-r)(b-r)>0$. Define the symmetric bilinear polynomial

$$
F_b(x,y)=k_3xy-k_1(x+y)+k_2.
$$

The following arrays are its corner-polynomial coefficients in ascending
powers of $b$:

$$
\begin{aligned}
F_b(b,b):\;&(99900,241611,133824,38871,-24423,-15867),\\
F_b(b,b+1):\;&(-11826,-11100,8124,9150,-28290,-15867),\\
F_b(b+1,b+1):\;&(-7458,-65178,-80043,-24438,-32157,-15867).
\end{aligned}
\tag{6.1}
$$

The third is negative for $b>0$. For the other two, exact shifts give

$$
\begin{aligned}
F_{1+z}(1+z,2+z):\;&
(-49809,-159897,-292836,-262680,-107625,-15867),\\
32F_{5/2+z}(5/2+z,5/2+z):\;&
(-11387145,-95548758,-95031192,-38305488,-7128336,-507744),
\end{aligned}
\tag{6.2}
$$

again in ascending powers of $z$. Hence all four corners of
$[b,b+1]^2$ are strictly negative for $b\ge5/2$. A bilinear function on
this rectangle is the convex combination of its four corner values, so
$F_b(n_1,n_2)<0$. This contradicts (5.10). In particular this part does
not divide by $k_3$ or discard its possible zeros.

## 7. Small-b elimination without losing exceptional strata

For $0<b<5/2$ one has

$$
\frac{k_3}3=b^2(12511-1289b)+66211b+38698>0.
\tag{7.1}
$$

Put $G=45TU^2$ and define integer polynomials $a_b,c_b,h_b$ by

$$
\begin{aligned}
Ga_b&=5LL_k+3Ak_0k_3,\\
Gc_b&=-10TUL_k-3Ak_0k_1,\\
Gh_b&=10TUL_k.
\end{aligned}
\tag{7.2}
$$

These divisions are exact in $\mathbb Z[b]$. Explicitly,
their ascending coefficient arrays are

$$
\begin{aligned}
a_b:\;&(-295618904,-3183073656,-4122449598,-2456556092,\\
&\hspace{12mm}-2576400048,-551951598,30831591),\\
c_b:\;&(102647520,1893726508,4989328358,4971697312,\\
&\hspace{12mm}3818639378,2825126907,512931546,-27574000),\\
h_b:\;&(-196646328,-1512430508,-2458058540,-1838580134,\\
&\hspace{12mm}-1369955312,-633012864,-83795176,5156000).
\end{aligned}
\tag{7.3}
$$

For either member of a hypothetical collision, substitute (5.12) into
the undivided parent. Exact collection gives

$$
j(a_bn+c_b)=h_bn.
\tag{7.4}
$$

More explicitly, after that substitution the ambient residual obeys

$$
\frac{5TU k_0(k_3n-k_1)j}{2}\mathcal P
=G\bigl[j(a_bn+c_b)-h_bn\bigr].
\tag{7.5}
$$

The multipliers used here are nonzero by Section 5 and strict source
positivity. Also $L_k\ne0$ implies $h_b\ne0$, so (7.4), with $n>0$,
forces $a_bn+c_b\ne0$. The original source relation gives the exact identity

$$
j^2+(1+b-2n)j+n^2-n-b^2=0.
\tag{7.6}
$$

Indeed substitute $r=n-j$ into $b(j-b)=r(1-r)$. Multiply (7.6) by
$(a_bn+c_b)^2$ and use (7.4). Both $n_1,n_2$ are roots of

$$
\begin{aligned}
Q_b(n)={}&(h_bn)^2+(1+b-2n)(h_bn)(a_bn+c_b)\\
&+(n^2-n-b^2)(a_bn+c_b)^2
=\sum_{j=0}^4Q_j(b)n^j.
\end{aligned}
\tag{7.7}
$$

This is a necessary equation on actual worlds; no claim that every root
lifts to a strict source is needed.

Set

$$
u_i=k_i/3\quad(i=1,2,3),\qquad
\Delta=u_1^2-u_2u_3=-L_k/9\ne0.
$$

By (7.1), $u_3>0$. For $w=u_3n_1-u_1$ the involution gives

$$
w\ne0,\qquad u_3n_2-u_1=\Delta/w,\qquad w\ne\Delta/w.
\tag{7.8}
$$

The last inequality is exactly the already established $n_1\ne n_2$.
Define

$$
q_i=\sum_{j=i}^4\binom ji Q_j u_1^{j-i}u_3^{4-j},\qquad
q(w)=\sum_{i=0}^4q_iw^i
=u_3^4Q_b\bigl((w+u_1)/u_3\bigr).
\tag{7.9}
$$

Thus $q(w)=q(\Delta/w)=0$. Write

$$
\begin{aligned}
B&=q_4\Delta^2-q_0,&D_q&=q_3\Delta^2-q_1\Delta,\\
E&=q_4\Delta^2+q_0,&C_q&=q_3\Delta^2+q_1\Delta,\\
F_q&=2q_2\Delta^2.
\end{aligned}
\tag{7.10}
$$

Divide the two root equations only by their respective nonzero roots
squared. Subtract and add the resulting equations after multiplying by
$\Delta^2$. With $s_*=w+\Delta/w$, the subtraction, divided by the
nonzero $w-\Delta/w$, and the addition give

$$
Bs_*+D_q=0,\qquad
E(s_*^2-2\Delta)+C_qs_*+F_q=0.
\tag{7.11}
$$

Multiplying the second equation by $B^2$, and replacing $Bs_*$ by $-D_q$,
gives the necessary polynomial condition

$$
R_0=E(D_q^2-2\Delta B^2)-C_qD_qB+F_qB^2=0.
\tag{7.12}
$$

This final operation does not divide by $B$. If $B=0$, (7.11) also gives
$D_q=0$, and (7.12) remains necessary. It does not divide by $q_4$, or by
any other coefficient of $q$ or $Q_b$. Quartic-to-cubic and all further
leading-degree drops are therefore included. The only divisions in this
part use source-positive quantities or quantities forced nonzero by the
hypothetical distinct collision. In particular no division by a coefficient
of the original gain, a gain sample, drift, $\Lambda$, or $D$ occurs.

## 8. The degree-92 positive certificate and completion of Theorem 4.1

The integer definitions (5.5), (7.2), (7.7), (7.9), (7.10), (7.12) yield

$$
R_0=2R,\qquad R\in\mathbb Z[b],\qquad\deg R=92.
\tag{8.1}
$$

The integer content of $R_0$ is exactly $2$, and its leading coefficient
is positive. No polynomial factor in $b$ is removed. Endpoint coefficients
of the complete generated polynomial are

$$
\begin{aligned}
r_0={}&87638508218840276800245168242602036600144402550307611599902994577381468445139467759323813414118663471979560960,\\
r_{92}={}&68618903888505443911344102295197322738023023417035780346418101901916000000000000000000000000,
\end{aligned}
$$

where $R(b)=\sum_{i=0}^{92}r_ib^i$. Define all $93$ integers

$$
T_j=\sum_{i=0}^j r_i5^i2^{92-i}\binom{92-i}{j-i},
\qquad 0\le j\le92.
\tag{8.2}
$$

They are all strictly positive, with their minimum at $j=0$:

$$
\min_jT_j=
433964873229373017456432378536322088353910786730182968417113138867981003087292152881908560946357151427405421011451319229301086128082780160.
\tag{8.3}
$$

Proposition 12.1 gives the complete ordered $93$-integer array and its
coefficient derivation.
The coefficient degrees of $(Q_0,\ldots,Q_4)$ are $(16,15,14,13,12)$;
those of $(q_0,\ldots,q_4)$ are $(28,24,20,16,12)$. These are degree
identities before specialization; they impose no nonvanishing assumption
after specializing $b$.

The binomial theorem gives

$$
\sum_{j=0}^{92}T_jx^j
=2^{92}(1+x)^{92}R\left(\frac{5x}{2(1+x)}\right).
\tag{8.4}
$$

For $0<b<5/2$ take $x=2b/(5-2b)>0$. The left side is positive; the
factor outside $R$ is positive; hence $R(b)>0$. This contradicts the
necessary $R_0(b)=0$. Section 6 excluded $b\ge5/2$, and Section 5
settled the equal-$n$ case, so every hypothetical distinct pair in (4.1)
has been excluded. This proves Theorem 4.1.

The proof applies to any two actual complete worlds. It does not assert
an upper bound on the cardinality of $C(p,v)$, nor exclude pairs with
different $b$. Singular worlds and degree drops have stayed in its domain.
The positivity certificate proves a universal interval statement through
(8.4); it is not inference from finitely many sampled values of $b$.

## 9. An exact negative-p J seed with whole-world lifts

**Theorem 9.1 (Actual J pair at p=-11).** There exist two distinct strict
regular complete worlds $W_0,W_1\in C(-11,v_*)$ with
$a(W_0)=a(W_1)=a_*$. The common values and the two terminal-$M$ values
have the strict enclosures

$$
\begin{gathered}
-8.215078<v_*<-8.215077,\qquad
96.245820<a_*<96.245821,\\
102.260466<m(W_0)<102.260467,\\
107.408353<m(W_1)<107.408354.
\end{gathered}
\tag{9.1}
$$

There is a local real-analytic actual $J$ branch through this pair,
parameterized by $p$ near $-11$. No explicit continuation interval,
exhaustion of $J$ branches, or assertion of a different global connected
component is part of the theorem.

Proof. Use $t=r/b$, so

$$
r=tb,\qquad j=t+b(1-t^2),\qquad n=j+tb.
\tag{9.2}
$$

On $D\ne0$ evaluate (2.5)–(2.7) in these coordinates, and set

$$
F(z)=(p_0+11,p_1+11,v_0-v_1,a_0-a_1),\qquad
z=(t_0,b_0,t_1,b_1).
\tag{9.3}
$$

The exact center and radius are

$$
\bar z=10^{-24}
\begin{pmatrix}
10504686942715102009569284\\
88666866113376049686925\\
5156906641684654809138004\\
167936210357531086294279
\end{pmatrix},\qquad
\rho=10^{-16},\qquad
\mathcal Q=\{z:\|z-\bar z\|_\infty\le\rho\}.
\tag{9.4}
$$

Use the following exact rational preconditioner:

$$
Y=10^{-12}
\begin{pmatrix}
74317654135440&-97353116212496&-85945879326012&20330257536319\\
-583841728296&764803004244&675188111775&-159713860693\\
-27730856875100&34069982371636&25456366786943&-5564302263316\\
770570055051&-946704119133&-707367754439&154617822330
\end{pmatrix}.
\tag{9.5}
$$

All endpoints in the finite certificate are rounded outward to the
$10^{-60}$ grid. Addition and subtraction use endpoint arithmetic;
multiplication takes the minimum and maximum of four endpoint products;
division takes the four endpoint quotients only when the denominator
interval excludes zero. After each operation round the lower endpoint
down and the upper endpoint up. For derivative enclosures use the product rule and

$$
(a/b)'=\frac{a'-(a/b)b'}{b}.
\tag{9.6}
$$

Section 13 defines the rational interval operations, their expression order
on the factorized circuit (2.5), and the exact finite data proving the bounds

$$
\begin{aligned}
\|YF(\bar z)\|_\infty&\le\eta_0,\\
\sup_{z\in\mathcal Q}\|I-YDF(z)\|_\infty&\le q_0,
\end{aligned}
$$

where

$$
\begin{aligned}
\eta_0&=\frac{973789251791947370114393715220755890}{10^{60}}
<10^{-24},\\
q_0&=\frac{5144072038985496620415930974177109689174603232758782855326}{10^{60}}
<\frac{5145}{10^6}<1.
\end{aligned}
\tag{9.7}
$$

Every division has denominator excluding zero. Proposition 13.2 also
proves the following strict bounds on the entire box; every table
entry $(l,u)$ means $l/10^6<f<u/10^6$:

| Quantity | World 0 | World 1 |
| --- | --- | --- |
| $b$ | $(88666,88667)$ | $(167936,167937)$ |
| $r$ | $(931417,931418)$ | $(866031,866032)$ |
| $D$ | $(536056,536058)$ | $(-525133,-525131)$ |
| $v$ | $(-8215078,-8215077)$ | $(-8215078,-8215077)$ |
| $a$ | $(96245820,96245821)$ | $(96245820,96245821)$ |
| $m$ | $(102260466,102260467)$ | $(107408353,107408354)$ |

For completeness, the self-map inequality follows already from the simpler
bounds:

$$
\eta_0+q_0\rho
<10^{-24}+\frac{5145}{10^6}10^{-16}<10^{-16}=\rho.
\tag{9.8}
$$

The map $G(z)=z-YF(z)$ therefore maps the complete closed box strictly
into itself, with Lipschitz constant at most $q_0<1$. Banach's fixed-point
theorem gives a unique fixed point $z_*$ in its interior. Since
$\|I-YDF(\bar z)\|<1$, the Neumann series makes $YDF(\bar z)$ invertible;
as square matrices this forces $Y$ invertible. Consequently the fixed-point
equation is $F(z_*)=0$. In particular the equalities of the responses come
from an exact zero, not merely from overlapping response intervals.

The table gives $b_i>0$, $0<r_i<1$, and $D_i\ne0$. At this zero take

$$
\begin{aligned}
P_i&=\begin{pmatrix}r_i&b_i\\r_i(1-r_i)/b_i&1-r_i\end{pmatrix},\\
d_i&=-C_{0,i}/D_i,\\
g_i(s)&=\sum_{k=0}^3\frac{C_{k,i}}{D_i}
\prod_{\substack{0\le l\le3\\l\ne k}}\frac{s-l}{k-l}.
\end{aligned}
\tag{9.9}
$$

Equations (2.1)–(2.7) give the exact original readings
$(0,24,147/5,24,18,-11,v_*)$. These use the single entire $g_i$ and
fixed $d_i$ of (9.9), including at both terminal alternatives. Each $g_i$
has degree at most three and is nonzero by the first two readings.
The disjoint $r$ intervals show distinct sources, hence distinct complete
worlds. Equations (9.3) and (9.1) now establish the asserted $J$ pair.
They also give

$$
m(W_1)-m(W_0)>5.147886,
\tag{9.10}
$$

so these two endpoints do not themselves form an $M$ pair.

Finally replace the first two entries of (9.3) by $p_0-p,p_1-p$.
The equations are real analytic near $(z_*,-11)$, and (9.7) makes their
$z$ derivative invertible there. The analytic implicit-function theorem
gives $z=z(p)$ on some open interval about $-11$. Shrink it to preserve
all strict guards and endpoint distinctness. The formulas (9.9) then give
analytic gain coefficients and drift, and $v_J(p)=v_0(z(p))$ is analytic.
This is only a local continuation assertion. ∎

Theorem 9.1 puts $(-11,v_*)$ in $D_J$. Its unequal $M$ readings do not
exclude a different $M$ pair elsewhere in the same entire child, and do
not establish such a pair. It is not a joint witness.

## 10. One faithful positive-h chart over an actual J branch

**Definition 10.1 (Actual J branch and its chart).** Let $I$ be an interval
on which two specified real-analytic complete-world maps
$W_{J0}(p),W_{J1}(p)$ are actual strict worlds satisfying

$$
W_{J0}(p)\ne W_{J1}(p),\qquad
W_{Ji}(p)\in C(p,v_J(p)),\qquad
a(W_{J0}(p))=a(W_{J1}(p)).
\tag{10.1}
$$

The function $v_J$ is part of this given branch, with its actual-world hypotheses. The local branch of Theorem 9.1 is one
such branch. We require
$p\in I\setminus\{24\}$ below; no claim is made that $I$ exhausts any
whole component or all $J$ branches.

For variables $(p,t,b,h,s)$ use the two source labels

$$
x=(t,b),\qquad y=(t+hs,b+h),\qquad s\in\mathbb R.
\tag{10.2}
$$

In (2.5) and (3.1) substitute $r=tb$, $j=t+b(1-t^2)$, $n=j+tb$.
All of $D,N_p,N_v,N_a,N_m,S,C$ are then integer polynomials in $(t,b)$.
Define the reduced differences

$$
\begin{aligned}
R_p&=\frac{N_p(y)D(x)-N_p(x)D(y)}h,\\
R_v&=\frac{N_v(y)D(x)-N_v(x)D(y)}h,\\
R_\Theta&=\frac{C(y)S(x)-C(x)S(y)}h.
\end{aligned}
\tag{10.3}
$$

Each numerator vanishes identically at $h=0$, since then $y=x$.
The polynomial factor theorem therefore defines all three quotients in
$\mathbb Z[t,b,h,s]$ by exact division, including their polynomial
extensions at $h=0$. The actual chart will retain $h>0$.

The five equations are

$$
\begin{aligned}
N_p(x)-pD(x)&=0,\\
N_v(x)-v_J(p)D(x)&=0,\\
R_p=R_v=R_\Theta&=0.
\end{aligned}
\tag{10.4}
$$

Their full guards are

$$
\begin{gathered}
p\in I,\quad p\ne24,\quad h>0,\\
t>0,\quad b>0,\quad tb<1,\\
t+hs>0,\quad b+h>0,\quad(t+hs)(b+h)<1,\\
D(x)D(y)\ne0.
\end{gathered}
\tag{10.5}
$$

These are precisely the strict source conditions in the $t=r/b$
coordinates, together with regular selected endpoints and positive
$b$ difference. There is no additional sign or size condition on $s$.

**Theorem 10.2 (Faithful correspondence over the stated branch).** For
each fixed $p\in I\setminus\{24\}$, guarded solutions of (10.4) are in
bijection with unordered distinct actual $M$ pairs in the entire
$C(p,v_J(p))$. The bijection orders each pair by increasing $b$ and
uses (2.7) to reconstruct its complete worlds. Together with the given
$J$ pair in (10.1), every such solution satisfies the original joint
predicate (1.2).

Proof of the forward direction. The first two equations and $D(x)\ne0$
put the whole-world lift of $x$ in the stated child. Since $h>0$,
$R_p=R_v=0$ and $D(y)\ne0$ give the same $p,v_J(p)$ for the lift of
$y$. Strict source guards and (2.7) make both actual complete worlds.
Corollary 3.2 gives $S(x)S(y)\ne0$. Hence $R_\Theta=0$ is equivalent
to equality of their terminal-$M$ values. Finally $b_y-b_x=h>0$
makes the two worlds distinct. The independently supplied $J$ endpoints
need not be either of these worlds, or disjoint from them. No equation
has identified the two terminal common values.

Proof of the converse. Start with any distinct actual $M$ pair in this
same entire child. By S, Corollary 18.2, the presence of the actual $J$
pair (10.1) excludes a singular selected $M$ endpoint: both endpoints
have $\Lambda\ne0$, equivalently $D\ne0$ by (2.6). This is a statement
about the two selected $M$ endpoints, not about unused worlds in the child.
By Theorem 4.1 their $b$ coordinates are different. Order the pair so
$b_y>b_x$ and define uniquely

$$
h=b_y-b_x>0,\qquad t=r_x/b_x,\qquad
s=\frac{r_y/b_y-r_x/b_x}{h}.
\tag{10.6}
$$

This gives exactly (10.2), all strict guards (10.5), and the first two
equations of (10.4). Common acquired values give $R_p=R_v=0$;
Corollary 3.2 gives $R_\Theta=0$. The ordering is unique, and the
regular source lifts are unique, proving the claimed bijection. ∎

Only the three reduced differences in (10.3) are asserted to be polynomials
in $(t,b,h,s)$. The full system (10.4) is generally real analytic in
$(p,t,b,h,s)$ because it contains the branch function $v_J(p)$.
Replacing that function by its defining $J$ equations is an alternative
augmented system; it is not a proof that an eliminated branch function
is polynomial.

A zero with $h=0$ in the polynomial extension is not a distinct $M$ pair.
There is no assumed uniform lower bound on $h$, no upper bound on $|s|$,
and no exclusion of sequences with $h\to0$ and unbounded slope. The
converse covers every actual $M$ pair above the chosen $J$ branch, while
making no exhaustion claim about other $J$ branches. Theorem 4.1 supplies
the different-$b$ premise needed for the converse; it remains unnecessary
for the forward construction of a guarded joint witness.

## 11. Supplier correspondence, classical methods and the remaining gap

The following interfaces are used with their original quantifiers.

| Supplier | Correspondence and precise scope |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorem 2.1 | Original actions, clocks and complete triples; its $\epsilon$ is $e$, its $\beta$ is $1/8$, and its sixth-$M$ response $u_M$ is $v$. Equation (2.1) is its full undivided parent, with its singular branch retained. |
| F, Section 2 and its cited zero-safe source interface | The same complete-world semantics and singular strata; no finite-fibre count is substituted for the fixed-$b$ proof or used to enumerate a child here. |
| SII, Definitions 2.1–2.2 and Proposition 2.3 | Original regular gain-sample lift and integer response circuit. Equation (2.5) uses a different common denominator but exactly the same four samples and original responses. |
| SIII, Definitions 1.1–1.2 | The identical acquired word, traces, full-parent correspondence and independent-pair quantifiers. No tail or continuation claim is needed for the negative-$p$ seed. |
| SIV, Theorem 8.2 | Undivided interpolation reductions for the actual entire gain; (5.3) uses these algebraic identities, without importing regional estimates as global bounds. |
| S, Corollary 18.2 | If an actual off-24 child has a distinct $J$ pair, every selected distinct equal-$M$ pair has two regular endpoints, regardless of pair overlap. Used only in the converse of Theorem 10.2. |
| O, Theorem 16.5; SII, Theorem 28.1 | Isolation of distinct strict mirror pairs, with SII also treating their closed endpoint extension; in particular distinct strict mirror pairs do not accumulate on their diagonal. |
| SII, Theorem 29.1 | A uniform $\epsilon>0$ excludes all distinct actual $M$ pairs for $0<|p-24|<\epsilon$, uniformly over all real $v$. This implies mirror nonaccumulation. |
| SV, Theorems 1.1–1.2 and Sections 6–7 | On $K=[56,58]\times[304,305]$, terminal $J$ is injective on every entire actual child, and there is an actual $M$ point in $K$. Those regional facts do not assert global fixed-$b$ injectivity or provide a joint witness. |

Fixed-node polynomial interpolation is classical; its formula and node
conditions are stated in Section 2, with a reference also used by O:
J.-P. Berrut and L. N. Trefethen, “Barycentric Lagrange Interpolation,”
*SIAM Review* 46 (2004), 501–517,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
The null-vector and minor calculation, rational involution, polynomial factor
theorem, binomial coefficient transform, Neumann-series invertibility,
Banach contraction principle and real-analytic implicit-function theorem
are classical methods. Their hypotheses and their exact application are
shown above. The rational interval inclusions in Sections 13 and 20 prove the
contraction bounds used here. The coefficient identities and these
bounds imply the stated universal and existential conclusions.

The original gap is still exactly (1.2): exhibit independently chosen
actual distinct equal-$J$ and equal-$M$ pairs in one entire off-24 child,
or exclude all such configurations over the full original real domain.
Theorem 10.2 reduces the positive task over a specified actual $J$ branch
to a guarded zero of all five equations. No such zero is supplied here.
Theorem 9.1 supplies a local $J$ branch, and its two endpoints have
unequal $M$ values. Theorem 4.1 only excludes same-$b$ $M$ pairs; different-$b$
partners remain possible. A full-domain negative conclusion would also
have to cover other $J$ branches, parameter turns, near-diagonal and
unbounded-slope limits, and the relevant source or deleted-base limits.
Neither finite-box absence on one branch nor the separate regional
facts from SV settle that global question.


## 12. Exact coefficient data for the small-b exclusion

For a polynomial $P$ write $[P]_i=[b^i]P$, with $[P]_i=0$ outside its
coefficient range. Addition and multiplication of coefficient arrays mean

$$
[P+Q]_i=[P]_i+[Q]_i,\qquad
[PQ]_i=\sum_{k=0}^i[P]_k[Q]_{i-k}.
\tag{12.1}
$$

Together with the arrays (7.3), these finite sums specify every integer in
(7.7)–(8.2). In particular expansion of (7.7) gives, writing $a=a_b$,
$c=c_b$, $h=h_b$,

$$
\begin{aligned}
Q_0&=-b^2c^2,\\
Q_1&=Thc-c^2-2b^2ac,\\
Q_2&=h^2+Tha-2hc+c^2-2ac-b^2a^2,\\
Q_3&=-2ha+2ac-a^2,\\
Q_4&=a^2.
\end{aligned}
\tag{12.2}
$$

**Proposition 12.1 (Complete positive coefficient array).** The $93$
integers $T_j$ of (8.2), in their index order, are the following. Each
entry is a decimal integer, without a suppressed scale factor.

| $j$ | $T_j$ |
| --- | --- |
| 0 | $433964873229373017456432378536322088353910786730182968417113138867981003087292152881908560946357151427405421011451319229301086128082780160$ |
| 1 | $181164053530431579619735759283617558998026334105294531418205478320069455668286594035400221968491562588399848701795655111642453416630980444160$ |
| 2 | $35039063772030824411997220194056421508971184880612864360647482000108892157837527952528372769693117383924627576355570288357320224739106698035200$ |
| 3 | $4255771684569169468902961723149031547140496033241816243589309797265623844155260519472540538357116097346495913635937154145934626778300062210457600$ |
| 4 | $368639461745433209077683582914021730483090586558500260616946425750150318990367536169067505521792910471388003272364064423797920956937721005421363200$ |
| 5 | $24436500810656264978116182047219869206282666868106905185200707504078951782968750999906303176235460127244830568685258880486474823442331907332012769280$ |
| 6 | $1296495733456246207918359640865807665604482339762651953087950250342022966142120208126097998273195035396232690812941238093804717276432794038124916244480$ |
| 7 | $56792078569790416191340119100155366969636869269240392994681045510583144293482202124073452062649161333318467176428204786157260843288734019753626461798400$ |
| 8 | $2101287448312587546674922373405706206082125911527657951482114234961111832178259594854220393205673500017797335914495083267035822924666708923096056935219200$ |
| 9 | $66824850478582847008724884444205952499574177076008358839816008058931234872926095368397409505945274742627250557206509201370823187250494916101960139957862400$ |
| 10 | $1851963974280240510194673829459026074972579343315919816502325780619480996753939150605088292565889090962624544323136323800548190588805807514968206460877537280$ |
| 11 | $45229850463167175033987935764823895158320390930176798991156735041883320388739459197275227042730465979533976100792892518786884720636974980819863467235926343680$ |
| 12 | $982511234839896151466721118296972534062389008743990054192860602033993434166274114999918602574558605377766117573723173348767018528289652673106471643958686515200$ |
| 13 | $19131908926326042844235310917565557978764627443227993339146089485945985855694573387028949399206412013352556725610925656360525601000280761327722788233594640793600$ |
| 14 | $336189727727810889841871345013647145394596528182137847885559042361353194085476177564474095814246372973329177786228382975314743910946932716162564192486024229683200$ |
| 15 | $5361955177642500310742666868844440387477174606400003215856509592782834834941866994491116325585643710832625340547202909734969866805283154358446439887098319166504960$ |
| 16 | $78013089031257506703347325130524042059480638548216625171634316290603862454105749278335577535813464049475884981972197019911700223507569337799408090559286652079964160$ |
| 17 | $1040046751120383103864419833507892890855716791864215587070949108807182691152104305503696384580026700164234491123923077440450946471518261523192184270837634515861504000$ |
| 18 | $12755607572587638496527673444275506407984420925156966470142981566022989109678564800421112926632820281848488630366413823309716361296066031326369509343218149535776768000$ |
| 19 | $144429032282324803520099001700923215631633455725229990220600900846982507491626648838034160547914007415642784734877532089785318624448495849539416231893886018556788736000$ |
| 20 | $1514615460216135627776890238166635834039947201147372528403340436717271750457923573159126567001660863143070654790451604104521601997603829824938243555616285756963264921600$ |
| 21 | $14753774950026399434972959142570031319161507179207743742154941364067694847928888681071418422749038485791990106572468691156036187604407172255927335164106041187544701337600$ |
| 22 | $133844801536772055125068102273442928100559660452558671480965595253523086292040958415788825874463513409354410781822487649649982876286145097775734180959933929425192615936000$ |
| 23 | $1133555437700605164915351020840349367669551235523926985689205387077522340551738773469385179086872320595754285738531073733517197188306143004363531532462539433548697305088000$ |
| 24 | $8982239440687200021782723768071971067461670412328803025946187811334409554712771253237127290784397588965419147033342363132807226216879448619640274266977180103654397444096000$ |
| 25 | $66727824280095140527144517755311182165764013236492066926645932282655576536789680422585398802748032784214579008444667454668062877545061857538722630490744836617717507036282880$ |
| 26 | $465607521229364989023369454759241202231755426961768825288473829340993876819434001567746973953008409518289827046752334971701009592439732528543101063925908778589980306838650880$ |
| 27 | $3056829030044609508839336604020367953762447107703569188544849247178727676684530476626672010177342486826406604805040082470763532091973563681618777763923556614631521965939097600$ |
| 28 | $18912589151812367849114434330418632893933494889023376136640395221822327514973334518022982586627713628349351935165071160021858439323818263408616196922076432510941278575054028800$ |
| 29 | $110432805946420591322151828457146571845346903989185378755600115772749360110921016542337999980578770607305196598163218456067901632584685655719146903390736234176634938533190041600$ |
| 30 | $609401389045070735056221433224806729628866940050753782683052381216079638480131740751237796846131974189359957205969259749273014736866706829219575695970657915461742379281091133440$ |
| 31 | $3182100737594255865562890556983553880269108336592008871303938945877965241522689149122204783814868775723910442578875059406562950728173180661595154498521169382412826784797074391040$ |
| 32 | $15741121718286287346964271097465321925525177563600063657241041134817501421657544394898359910168211715383498498595136697681761191978664346995618709620568233100196739016509567795200$ |
| 33 | $73847661800912924012194845241652039440856433067662581157723254918462290338218827303656138263916370220459646304140093452964249206021570959535433826911452503421054230544313325977600$ |
| 34 | $328889133026869599190987474061509802318976682662220915517566074209721871716991872340005390212125582618169733631921247750347421934218402907710678561721635065766882855871428375347200$ |
| 35 | $1391787126814494688049620976868676429084974361941839280654129728876245607752826610875208470221904892067479491357062842767889644205632671354481885911324343283052432768112747861770240$ |
| 36 | $5601104814209814984284674119279689434555405684315719717126141184575861806399965027878897833046915233818679719447543658356508371794984995868361843410725210034647446290710650096189440$ |
| 37 | $21453054061153219793240418885357605216368795110769021453415765714127264419235306900649176729662740075199237912260015921272265804186367243847264231811570492656510699204985910565273600$ |
| 38 | $78257745210869585206148944467687044108236590725332208260905361140319102127855424897625661625891224229197063928738715858098957321666703687936768625449644397022406452466496647777484800$ |
| 39 | $272062738038663267041381502526827721690817983637027166228399764969186744901445390579036730672022292151126490825483201745887422912478263305832816100046318747192123556406573858920857600$ |
| 40 | $901921388423256074973579702463464455762569017607599801239647260541496373137152832231814809041160983607888467446628586406776219813940695336992330480298831095546523037261885346393620480$ |
| 41 | $2852693414128903651108234028246474557709648327385564095405623354525158286054560506206326273096716047834189101624682932033078602688455179853322895063765108236708166979466057880782766080$ |
| 42 | $8612566180402869438831765831393794817214234467729031469085047453517362019578783833791285809769878063330778165677811159449674613344024871722552157183932030796780131973933536741687296000$ |
| 43 | $24830269544849676078498707288390137620997651718139832947450543510849481623265119318289901971856361521206070372195547437525437906206011525156112633104345962745980961137595525634195456000$ |
| 44 | $68384656348722002357890040382122163533521154272053624525295155228347639623325846640773102546599920085108584981214352978413047048296613392416882383339469102711197590075305671903936512000$ |
| 45 | $179969288758234721911153639062683657831207270726765854762835689432274686166449857613183845463929707255147842186068652770126939642206881039000567983032853749694823672525262408262038323200$ |
| 46 | $452701861580519318459284396646284944085242448016509616430886097539496394056419201817201486824453511633086672423209185675688366520334612215989642268384413938217644928127268400403788595200$ |
| 47 | $1088653764826087402346102863585382721104652737452091492229931557026620415355663542314011801234370753330689265107364003456241001811021777674349899666479055289207920866627205528270405632000$ |
| 48 | $2503216292747402456045569324422617220919128410707294561105772444791963114544136830081782535085476312200370771680107867346267028933021582057040652254973902723021677044101195857192288256000$ |
| 49 | $5504066385016920019534200434915091325180294428383696486148814074898744640827097093255768838266205509505305011419042075942334458757006300852342553856706736132725084406963315925164490752000$ |
| 50 | $11573622982746529537414765012517595713212379494458057837507434726957945147789864154397636566907700017426107003074701313827517380523304151090311041877576579865069142866502871344825531105280$ |
| 51 | $23273251821020561586065206277943636569163459056910898321727960108163089580606612848925994293640659774245591948877087433306908714920988841248263712885894492723576193645485368797910301409280$ |
| 52 | $44753432038641849068814859746430972929617507137837657359454951906273888372226939959357072984399264918451723816841915675592298984030646317830630335762588153709111549440256805010469919129600$ |
| 53 | $82287539951981656370298632703721674469173477707631265902710052399094318801551984410174093653134425356781454906523081664099947151966704554848922974677984862291016261708777492282652544204800$ |
| 54 | $144648579098917122452187554959441292851642356338470066685381330214872333437359681510103397403080156340769397802907510495237426304312960485367905112133958154393727988171241452885417499033600$ |
| 55 | $243039532290200984551435819367020495499701972047563153809288117881883509677634459836989869496052506246324607770376132418133245570969120462252547467077224006075317880640571003518143472599040$ |
| 56 | $390218868850605628119203254643391650835684781137329808250101358056005520932806022742251730493869979469021895015334837795012167045308849926472830005025120536403490596303170680389884329328640$ |
| 57 | $598506504919114509657829619122774534747348808948746459489386546191866502406401298253212454081274505819547912565162837764271854435284238095750293797646114528731855873504403310349558952755200$ |
| 58 | $876582994540976885398004423016677738009704195030357311935097196396366595551301251575719551928383665118413012641986403769025088449971576943654708476776623240499886454404780055899624020377600$ |
| 59 | $1225426777627288204497918149734248989791879203374505537736959301450354825346370414600542407825738982551855209950668350535485107594078100997389582207109845401126277381871433437751675138867200$ |
| 60 | $1634290311180289607045174733106218929266902228707534773187295386451215993269761250359505029617218268901770327851246458857097162027282556048651812080929783674009912317153974230066313969008640$ |
| 61 | $2078092360970892003449206385801035176595203887543853716257507383389201649538823301023629639365852861858350853628289880292010475304966109548654312074449013718182123372396295282609104973987840$ |
| 62 | $2517719625602373725924792551197760505928157253821780225332673630954669428130421934326511348911094750198166839039643385574942595025396472523145253535250291666116621242277823583923755129241600$ |
| 63 | $2904251018407715634938433413588862937520020888973632804370438997191560954877763318541832402535480552516207758658204945700898824337200703055553371405042101340395413491970468523053048188108800$ |
| 64 | $3187014230195005382176739659072635338759018863903075370095678261254324243608790656187100229083801269207624323215715846916567436787778332782519582121072249097008495721270657123116631300505600$ |
| 65 | $3323944642555788371249649053987331463345350524205661938821059119133552513871581843319726931360935927531560110474578159001149967250889209525186234702415594377260374007736611845746962024366080$ |
| 66 | $3291504975072253222674167255221798548752083785079654694355531675326205290023725398510444492112591885812509619261554614884099694727214315915971160226858290326932368363258291199181233774919680$ |
| 67 | $3091056057865234002044358051745729883718921941905350337554868018558832422483937867999888509632711083242336127004611294381210829563815427796954455774393761541089923015509046213121346109440000$ |
| 68 | $2749387601507542521251534982927975856020193701746409559977804332385295835500124943414881399005285582146965481562440281253334119130876849190834906204240318737502892585558301393137264754688000$ |
| 69 | $2312944416681836545833848388294980051679301049418755046694075362069027177419860349375988024556019401238959997522058532813934873565710276638537566220402737837981685990549957222963165003776000$ |
| 70 | $1837423222240578015512789503626079347206524893013178749430700059374325631324055513168451349415188696992325405421048170971065333659916504975557945772173231976487332453245450968360688392601600$ |
| 71 | $1375959172386757226384713940788430623237995723745603164934432838954482014026926595681198666842015119397751567720313716885699818763531005370725209401571502672690973147790088255842064898457600$ |
| 72 | $969404340695622658261451523851534381802947909379219456344479364415244253496445314524752774297295101714357464644334170058873545048899712375612388355166437166763968446793742978938302365696000$ |
| 73 | $641150177171699789986318657021788637388445591200575183835649600044234253864312708813961587719483936631375778250183567079117247773805634199564719533275360104250361119900145650007873159168000$ |
| 74 | $397109352345418099866543340239309258423194466151945320185798282282522226314685917194645402249716798300387170949083975436403575393032514161665909307761041809886912552428709568504875974656000$ |
| 75 | $229703369912019685694186720945822635384445786818974672708570938802177043072359638039096248190049221770355924776114359725372933293814005457882803082487003633909648786628284561765853361602560$ |
| 76 | $123706882799628795561957567543184210966097767601386263895260736294714663055113204069098268017463256573194982351738842416099587146141471339579131365689464112725917827259566195654787659202560$ |
| 77 | $61812735961602579416123277786680322534461155195148107623829255470045868545029593305621224697007978369768874139154870625240481212444006677389064680606314393359107338954875849402825782067200$ |
| 78 | $28543209238935060381266122170320855699946567274787831174391817564735667363474852019942830685604047086595573362759532923033150076016450171377134279579030531739947809848866646295132084633600$ |
| 79 | $12125690898557549358287856544294913249516860875737380981182359768465444501431378241936418958255536202664991178427716898921320652657074691673800859192377503217816724395280535893065282355200$ |
| 80 | $4714446116575062868595030315863760600155383377269640691494786726955440219836845378195630662813914815547040705758178153236479672344725701133319284004096797744679557928763680709320512634880$ |
| 81 | $1667448656031314409491944364547509768754615916788305089329816777749691154229733957960589335473219093588418562610240364833677284330749458211153027827399350277587448620220873400840177582080$ |
| 82 | $532712171069666218152045045601766038921190639380376288598076999896535380131255847474835138229504604658082460665761970937115001855162383812165005143734804944030894331228249762998150758400$ |
| 83 | $152436257005984055171627185919278162952913227656117085949499553534218422380537896744930034924256201067177182336247082874901320051628674942453629392667546225911816041665953610771149619200$ |
| 84 | $38673332142279453116819238020909475732390928086424921071740275046297454631273534939670756336356943829605504457084323557900432147909359353312363032423637338275111320487005190002337382400$ |
| 85 | $8590173475655241419669553474010651409003422177508779079929130060188994060050544564377161607038610326396074981620007243912290254125536500647775267465341001064021981716296072902402375680$ |
| 86 | $1644195987441960680441732844624368797398982930168136150063422747587445609068793542503592913209608689780300034302545295006007745666368763012730252764226421980471601623035092582221742080$ |
| 87 | $265611370154615267450824823515860077555634685998669828047357533230791744685913372394408293778005867353858153692192421110628063278636393176861072972625295156075142518165054468338483200$ |
| 88 | $35203423363225324777317376716305102459534044130701870810632735751295673648289986407825999921154195791820079952412024439751963774778604873739660959001754394288669573604896618027417600$ |
| 89 | $3674369983761827764481645214155768525357122882545586623671808947003538164960722287106018450425301235626404250608821076953707454078907274069237745590364974270838077003077527745331200$ |
| 90 | $283114629064580258173453859501947281311775344381339531951446775432242806171150558621136564726070385326704048615040131992248829407281184864343715490951596810023809264552701261250560$ |
| 91 | $14312974557070563737100491554003334060030409941055629276917926915930611277792485442737700226775930774438818877609131498914573891830072706045218973430010252820976181170615888117760$ |
| 92 | $356054610433494346214595081146103743302988902646211044471889172124568449811581746117031500282946072265629542940685559122735671601043580338627437335265125052206521355453595648000$ |

Proof. Expand (12.2) by (12.1), using the three arrays (7.3).
For each $i=0,\ldots,4$, apply the finite binomial sum (7.9); form the
five expressions (7.10); then form (7.12) by (12.1). The resulting
coefficient arrays have degrees

$$
(\deg Q_i)_{i=0}^4=(16,15,14,13,12),\qquad
(\deg q_i)_{i=0}^4=(28,24,20,16,12).
$$

Their last combination has $93$ coefficients, all divisible by $2$,
with greatest common divisor $2$ and positive leading coefficient.
Dividing each coefficient by $2$ gives the $r_i$ of (8.1), with the
endpoint values displayed there. Finally the coefficient of $X^j$ in

$$
\sum_{i=0}^{92}r_i5^i2^{92-i}X^i(1+X)^{92-i}
$$

is exactly the finite sum (8.2); its expansion is the array above.
These coefficient operations are identities in $\mathbb Z[b]$ and
$\mathbb Z[X]$: they involve no specialization or polynomial-factor
cancellation. Every displayed integer is positive; comparison of the
$93$ entries gives the minimum (8.3) at $j=0$. This proves all the
coefficient assertions used in Section 8. ∎

## 13. Rational interval proof data for the negative-p J pair

**Definition 13.1 (Outward rational intervals).** For a positive integer
$H$ and a closed real interval $A=[l,u]$, put

$$
\mathcal E_H(A)=
[\lfloor Hl\rfloor/H,\lceil Hu\rceil/H],\qquad
\langle q\rangle_H=\mathcal E_H([q,q]).
\tag{13.1}
$$

For two such intervals, addition and negation are endpoint addition and
negation. Define their product and, when $0\notin B$, their quotient by

$$
\begin{aligned}
A\mathbin{\odot_H}B
 &=\mathcal E_H\left(
 [\min_{a\in\partial A,\,b\in\partial B}ab,
  \max_{a\in\partial A,\,b\in\partial B}ab]\right),\\
A\mathbin{\oslash_H}B
 &=\mathcal E_H\left(
 [\min_{a\in\partial A,\,b\in\partial B}a/b,
  \max_{a\in\partial A,\,b\in\partial B}a/b]\right).
\end{aligned}
\tag{13.2}
$$

Here $\partial[l,u]=\{l,u\}$. Subtraction means addition of the
negative. For $A=[l,u]$ let $|A|_{\max}=\max(|l|,|u|)$.
The extremum formulas and the definitions of floor and ceiling prove
that these intervals contain every corresponding exact scalar result.

For a value interval $A$ with four derivative intervals $A'_k$, lift
these operations by the sum rule, the product rule
$A'_kB+AB'_k$, and the quotient rule

$$
V=A\oslash_H B,\qquad V'_k=(A'_k-VB'_k)\oslash_H B.
\tag{13.3}
$$

Products in (13.3) mean $\odot_H$. Induction on an expression proves
simultaneous containment of its values and all four exact partial
derivatives. The identity underlying the last rule is
$(a/b)'=(a'-(a/b)b')/b$; the interval $V$ contains $a/b$, so dependency
between value and derivative does not invalidate the enclosure.

For the seed take $H=10^{60}$. In (9.2) form $r,j,n,T,U$ in that order,
with $t^2$ evaluated as $t\odot_H t$; then form
$L,A,D,C_0,C_1,C_2,C_3,B_5,B_6,B_7$ in the order (2.5).
Finally form the four response numerators and divide each by $D$.
Every displayed sum is evaluated from left to right, and products of
more than two factors are associated to the left; scalar coefficients
are included as the leftmost factors. Thus, for example,
$3Ajn=((3A)j)n$ and
$C_2=((3(49b+34))j)n-(54U)(j+n)$.
Constants are enclosed by (13.1). This specifies a finite sequence of
rational interval operations, including its rounding at every product
and quotient.

At the centre enclose each coordinate by $\langle\bar z_i\rangle_H$.
For the derivative enclosure start with the coordinate intervals
$[\bar z_i-\rho,\bar z_i+\rho]$ and the derivative vectors
$(\langle\delta_{ik}\rangle_H)_{k=0}^3$. Form $F$ in the order (9.3).
Multiply by the rational $Y$ from (9.5), summing over $k=0,1,2,3$
from an initial zero interval. Denote the resulting four centre intervals
by $V_i$ and the sixteen intervals for $I-YDF$ by $E_{ij}$.

**Proposition 13.2 (Exact displacement and derivative enclosures).** In
these definitions $H|V_i|_{\max}$, for $i=0,1,2,3$, are

$$
\begin{pmatrix}
338966824265795008357905275803899557\\
973789251791947370114393715220755890\\
177795360310281989937252073493405565\\
93547459601986909824855730251270564
\end{pmatrix}.
\tag{13.4}
$$

The integers $H|E_{ij}|_{\max}$ are the following four rows.

| $i$ | $j=0$ | $j=1$ | $j=2$ | $j=3$ |
| --- | --- | --- | --- | --- |
| 0 | $36615031545838584104784112806117146775273520730140824906$ | $4665500393481296553653074981766616011572470678514771447458$ | $11895925729627738368986108191533000528599160052716878516$ | $430060688228733744289085771412843530298259873461153704446$ |
| 1 | $294689238745658795743745434675021789415447964164996433$ | $37549254557355489886640933776903589937776198628205191941$ | $102546280789074016366222721628443814053943985808700856$ | $3705782341591738185699190561416511064109646582998629532$ |
| 2 | $10913714330583508258365504349915152262824995620166684213$ | $1390627720516803142409353949396066483087721321428180675298$ | $3551248428158717282816734247983206990265688356598139055$ | $128383251887586614615819261424087188499414045611436805352$ |
| 3 | $311280803675412437958251039764013002005507053051642743$ | $39662463927825453974872842216931865835188257987027241119$ | $105941584569979733149032480700561479437527598663981608$ | $3828839800416140708530680926900809096588701891592384210$ |

All denominators in these interval expressions exclude zero. On the
whole box the strict source and response enclosures are precisely those
in the table following (9.7).

Proof. Apply (13.1)–(13.3) to the rational centre, radius and matrix
(9.4)–(9.5), in the stated expression order. If endpoints are represented
as integers $[L,U]/H$, multiplication produces endpoints

$$
\frac1H\left\lfloor\frac{\min(L_AL_B,L_AU_B,U_AL_B,U_AU_B)}H\right\rfloor,
\quad
\frac1H\left\lceil\frac{\max(L_AL_B,L_AU_B,U_AL_B,U_AU_B)}H\right\rceil;
\tag{13.5}
$$

For the quotient put

$$
q_-=\min\left\{\frac{HL_A}{L_B},\frac{HL_A}{U_B},
                    \frac{HU_A}{L_B},\frac{HU_A}{U_B}\right\},\qquad
q_+=\max\left\{\frac{HL_A}{L_B},\frac{HL_A}{U_B},
                    \frac{HU_A}{L_B},\frac{HU_A}{U_B}\right\}.
$$

Its endpoints are $\lfloor q_-\rfloor/H$ and
$\lceil q_+\rceil/H$. These integer formulas give (13.4) and the four
displayed rows.
The same operations on $b,r,D,v,a,m$ give the table following (9.7).
In particular its two $D$ intervals avoid zero, which justifies the
response divisions and derivative divisions; there are no other
variable denominators in this circuit.

Taking the largest entry in (13.4) gives $\eta_0$. Summing each of the
four derivative rows and taking the largest sum gives $Hq_0$, with
maximum at row $0$. Thus the interval containment induction proves
exactly the two norm inequalities (9.7). The bounds $q_0<5145/10^6$
and $\eta_0<10^{-24}$ give (9.8), and the contraction and whole-world
inverse argument in Section 9 proves Theorem 9.1. ∎

## 追加锚（本行以下为增补区）

## 14. A closed negative-base rectangle with no actual M collision

Retain exactly the complete worlds, acquired history and terminal responses of
Definition 1.1. Define the closed rectangle

$$
\mathcal B_-=
\left\{(p,v)\in\mathbb R^2:
 |p+11|\le10^{-5},\quad
 \left|v+\frac{8215077071969}{10^{12}}\right|\le10^{-5}\right\}.
\tag{14.1}
$$

All its bases have $p\ne24$. For any actual world put
$x=(j+r)/(1+2b)=n/U>0$. The root labels below refer to the exact rational
centres in Section 17. They are mathematical coordinates, with no additional
acquired observation.

**Theorem 14.1 (Uniform entire-child M injectivity).** For every real
$(p,v)\in\mathcal B_-$ the entire actual child $C(p,v)$ has at most two
complete worlds. Every actual world has carrier-root label $13$ or $15$.
There is at most one complete world at each of those labels, and

$$
\begin{array}{c|c}
\text{label}&\text{terminal }m(W)\\ \hline
13&107<m(W)<108\\
15&100<m(W)<104
\end{array}.
\tag{14.2}
$$

Consequently $m:C(p,v)\to\mathbb R$ is injective, and

$$
D_M\cap\mathcal B_-=\varnothing,
\qquad (D_J\cap D_M)\cap\mathcal B_-=\varnothing.
\tag{14.3}
$$

This includes every actual companion, whether selected for either pair or
unused. No regularity, exact-cubic degree, gain positivity, nonzero drift,
nonzero gain sample or separation between selected endpoints is assumed.
At arbitrary bases of the rectangle this is only an upper bound on
cardinality; a surviving algebraic root is not asserted to be actual.

**Corollary 14.2 (Entire child at the actual negative J seed).** Let
$W_0,W_1,v_*$ be the exact worlds and common acquired value of Theorem 9.1.
Then $(-11,v_*)$ is strictly inside $\mathcal B_-$ and

$$
C(-11,v_*)=\{W_0,W_1\}.
\tag{14.4}
$$

These worlds have labels $15,13$, respectively, equal terminal $J$ responses
and unequal terminal $M$ responses as in (9.1). This seed child has exactly
two worlds and no distinct equal-$M$ pair, including any independently
selected or overlapping pair. Exact-two cardinality is asserted here at
this certified seed, not throughout the rectangle.

Sections 15–18 prove the theorem; Section 19 proves containment and
exhaustion at the seed. Section 20 specifies the finite coefficient
relations and rational interval calculations used in these proofs.

## 15. Zero-safe late-node reconstruction for every companion

Write $\mathscr D=x(x+1)(x+2)$ and $\mathscr R$ for the degree-eighteen
carrier of F, Definition 31.1 and Lemma 31.2. These differ from the source
$D$ of (2.5) and the degree-92 polynomial of Section 8. The following is the
faithful interface of F, Lemma 30.2, with the same whole gain and clocks.
For a possible $(x,d)$ at an off-$24$ base put

$$
\begin{gathered}
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H(s)=\sum_{i=3}^6h_i
 \prod_{\substack{3\le k\le6\\k\ne i}}\frac{s-k}{i-k},\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\quad
H_2=4h_3-6h_4+4h_5-h_6,\\
H_7=-h_3+4h_4-6h_5+4h_6,\\
B_0=294/5-2d-H_2,\qquad C_0=d^2+B_0^2,\\
U=\frac{-dH_0+B_0H_2}{C_0},\quad
b=(U-1)/2,\quad j=\frac{U(24-d)}{H_1},\quad r=xU-j.
\end{gathered}
\tag{15.1}
$$

The letters $B_0,C_0$ in this late-node circuit are local; they are not
$C_k$ of (2.5). An actual world satisfies all of

$$
\begin{gathered}
x>0,\quad d\ne24,\quad H_1\ne0,\quad C_0>0,\quad U>1,\quad0<r<1,\\
j=b+r(1-r)/b,\qquad dU=-H_0,\qquad B_0U=H_2.
\end{gathered}
\tag{15.2}
$$

Conversely these guards reconstruct precisely one complete world, with
$g=H/U$, drift $d$, and

$$
m=d+(3+2x)H_7.
\tag{15.3}
$$

Indeed the original traces in Section 2 make $H=Ug$ have the four samples
in (15.1), even at degree drops or sampled zeros. If $d=24$, the parent
forces $b=1/8$ and the unique mirror gain (4.2), giving $p=24$; hence this
case cannot occur off $24$. Clock one gives $H_1=U(24-d)/j\ne0$.
Clocks zero and two give the last two equations of (15.2). If $d=B_0=0$,
they imply $H_2=0$, whereas the definition of $B_0$ implies $H_2=294/5$.
Thus $C_0>0$, and their scalar product with $(d,B_0)$ gives the displayed
$U$ without dividing by $d$. All source coordinates and the entire gain
are forced. Conversely the guards verify every original clock through six;
the first two unequal readings exclude $g=0$. Formula (15.3) uses this same
whole gain at clock seven. In particular $W\mapsto(x,d)$ is injective.

For a complete denominator-free specification set

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)\mathscr D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\quad
 a_2=4z_3-6z_4+4z_5-z_6,\quad z_*=xa_1-\mathscr D(24-d),\\
f=5d\mathscr D a_2+a_0((294-10d)\mathscr D-5a_2),\\
K=4a_0^2z_*^2+2a_0(d\mathscr D-a_0)z_*a_1
 -(a_0+d\mathscr D)(d\mathscr D+(1-2x)a_0)a_1^2,\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\end{gathered}
\tag{15.4}
$$

The exact fixed-size Sylvester identity is

$$
\operatorname{Res}_d(f,K)=256\mathscr D^8F_0^2\mathscr R,
\qquad(\deg_x,\deg_p,\deg_v)\mathscr R=(18,6,6).
\tag{15.5}
$$

The quotient is in $\mathbb Z[x,p,v]$ and has $512$ nonzero monomials.
No primitive factor is removed. Equivalently use rows
$d^3f,d^2f,df,f,dK,K$ and columns $d^5,d^4,\ldots,1$, retaining their
size under specialization. The normalization also gives

$$
[x^0]\mathscr R=10^6(32p-5v-366)^2
 (120p^2-38pv-3360p+3v^2+522v+23112)^2.
\tag{15.6}
$$

**Lemma 15.1 (All-world carrier necessity).** Every actual world of every
off-$24$ child satisfies $f=K=\mathscr R=0$, including $d=0$,
$F_0=0$, $\Lambda=0$ and all leading-degree drops.

Proof. These are the implications of F, Definition 31.1, and S, Theorem 4.1,
in the normalization (15.5). Their zero-safe mechanisms are as follows.
Since $a_i=\mathscr D H_i$,

$$
f=5\mathscr D^2(dH_2+H_0B_0)=0.
\tag{15.7}
$$

For $d\ne0$, substitution of $U=-H_0/d$ and
$r=U(xH_1-(24-d))/H_1$ in
$r^2-(1+b)r+b(xU-b)=0$ and clearing denominators gives $K=0$.
More explicitly the substitutions $a_i=\mathscr D H_i$,
$H_0=-dU$ and
$xa_1-\mathscr D(24-d)=\mathscr D rH_1/U$ give

$$
K=4\mathscr D^4d^2H_1^2
 \bigl(r^2-(1+b)r+b(xU-b)\bigr)=0.
\tag{15.10}
$$

Here $U=1+2b>0$, and the last factor vanishes by the original source
relation. At $d=0$, clock zero gives $H_0=0$, also making every term
of $K$ vanish directly. Thus no zero-drift point is removed by
cancellation.

When $F_0\ne0$ the resultant gives $\mathscr R=0$ immediately.
At an actual $F_0=0$ point one must not cancel $F_0$. On regular strict
sources $x,p,v$ are rational functions of $(r,b)$ by (2.5)–(2.7).
Their $F_0$ pullback has a nonzero numerator polynomial, as witnessed by

$$
(r,b)=(1/2,1/4),\qquad
(x,p,v,F_0)=\left(\frac76,\frac{19224}{515},
 \frac{464403}{2575},\frac{5736351}{4120}\right).
\tag{15.8}
$$

A nonzero polynomial has no open zero set, so the complement is dense
in every regular source neighbourhood. Continuity includes $F_0=0$.
At a singular actual source the parent forces $b=1/8$, and

$$
\begin{gathered}
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853,\\
\Lambda(r,1/8)=\Phi(r)/(960jn),\qquad
\operatorname{disc}\Phi=3648425367354069653778543411200\ne0.
\end{gathered}
\tag{15.9}
$$

Thus $\Lambda_r\ne0$. Also $e=d-24\ne0$, since $e=0$ gives $p=24$.
The undivided parent's $r$ derivative is $e\Lambda_r\ne0$. Fixing this
$e$, the implicit-function theorem supplies nearby strict parent worlds
with $b\ne1/8$ and therefore $\Lambda\ne0$. Their whole fixed-node gains
and bases vary continuously, and $p$ stays off $24$ locally. Hence
$\mathscr R=0$ passes to the singular limit. There was no division by
$F_0$ at an exceptional point or by $\Lambda$ at a singular point. ∎

## 16. A linear drift constraint without a quadratic-degree assumption

Write polynomially $f=A_fd^2+B_fd+C_f$ and $K=\sum_{i=0}^4K_id^i$.
Define exactly the coefficients of SII, Definition 5.2,

$$
\begin{aligned}
\alpha={}&K_4(-B_f^3+2A_fB_fC_f)
 +K_3A_f(B_f^2-A_fC_f)-K_2A_f^2B_f+K_1A_f^3,\\
\zeta={}&K_4(-B_f^2C_f+A_fC_f^2)
 +K_3A_fB_fC_f-K_2A_f^2C_f+K_0A_f^3.
\end{aligned}
\tag{16.1}
$$

Their expansions have $280$ and $405$ nonzero monomials. With

$$
Q=K_4(A_f^2d^2-A_fB_fd+B_f^2-A_fC_f)
  +K_3A_f(A_fd-B_f)+K_2A_f^2
$$

exact polynomial expansion gives

$$
A_f^3K-\alpha d-\zeta=fQ.
\tag{16.2}
$$

Every actual world therefore satisfies $\alpha d+\zeta=0$, even if
$A_f=0$. Wherever $\alpha\ne0$ its drift is forced:

$$
d=-\zeta/\alpha.
\tag{16.3}
$$

This is necessity at actual common roots, without a converse. No quadratic
formula or division by $A_f$ is used, and the specialized degrees of
$f,K$ are not assumed to stay two and four.

## 17. All eighteen carrier roots uniformly over the closed rectangle

Set $p_c=-11$, $v_c=-8215077071969/10^{12}$, $\delta=10^{-5}$ and
$\rho=10^{-4}$. The following centres are the exact Gaussian rationals
$c_i=(u_i+\mathrm i w_i)/10^{60}$. These exact rational coordinates
define the domains used in the proof.

| Label | $u_i$ | $w_i$ |
| --- | --- | --- |
| 0 | -2566651740089873802558961611116998361064043317266727026593154 | 0 |
| 1 | -2488256067754961262325253267547922037066061162427561700643890 | 0 |
| 2 | -2398282646064128690056667223037546435382446711027161580913045 | 0 |
| 3 | -2253614772749201210358016945669058656499587992729798853866355 | 0 |
| 4 | -2252626768029364415579697482419480958426371685284207315544168 | 0 |
| 5 | -2184327282123042597392334337114778818666093044664055281709777 | 0 |
| 6 | -385121109334004451450104015203478788150898573648732235199962 | 0 |
| 7 | 327012843307482581727938913901418823375830440876425286249326 | 0 |
| 8 | 499330948634637916987203941699780064294575742268491893596777 | 0 |
| 9 | 688914854153533970918949706527175689791178031035269440088934 | -99781436072170823545768407807753388134017826984639043874043 |
| 10 | 688914854153533970918949706527175689791178031035269440088934 | 99781436072170823545768407807753388134017826984639043874043 |
| 11 | 1089365608486293207913152831232653177904114251469431075943379 | 0 |
| 12 | 1228632880812453051104584087024888954984266181269074315374397 | 0 |
| 13 | 1291164724219101032355101727757188970647736976730287977692312 | 0 |
| 14 | 1311181683741030341929257994409657323129246507311517404455403 | 0 |
| 15 | 1478357740164785651714789709792381574413887570456758534609180 | 0 |
| 16 | 2166512041280199954483151592637154760323376849658401764138494 | 0 |
| 17 | 2853192397408804809598593441466492457861449208333382059958303 | 0 |

For real centres use $I_i=[c_i-\rho,c_i+\rho]\subset\mathbb R$.
For nonreal centres use the closed complex rectangle with each component
within $\rho$ of its centre. All eighteen domains are pairwise disjoint.
Domains $0,\ldots,6$ are strictly negative, domains
$7,8,11,12,13,14,15,16,17$ are strictly positive real intervals, and
$9,10$ avoid the real axis.

Translate exactly by the binomial theorem:

$$
\mathscr R(c_i+z,p_c+u,v_c+w)
 =\sum_{\ell,j,k} A^{(i)}_{\ell jk}z^\ell u^jw^k.
\tag{17.1}
$$

For Gaussian rationals use $\nu(a+\mathrm i b)=|a|+|b|$, the
multiplication-operator norm on the component maximum norm. It is ordinary
absolute value on real coefficients. Let
$\operatorname{Round}_{100}(a)=10^{-100}\lfloor10^{100}a+1/2\rfloor$
and apply it componentwise for complex arguments. Define

$$
\begin{gathered}
\gamma_i=\operatorname{Round}_{100}
 (1/\mathscr R_x(c_i,p_c,v_c)),\qquad
s_i=\begin{cases}\rho&c_i\in\mathbb R,\\2\rho&c_i\notin\mathbb R,\end{cases}\\
\eta_i=\sum_{j,k}\nu(\gamma_iA^{(i)}_{0jk})\delta^{j+k},\\
q_i=\nu(1-\gamma_iA^{(i)}_{100})+
\sum_{\substack{\ell\ge1\\(\ell,j,k)\ne(1,0,0)}}
 \nu(\gamma_i\ell A^{(i)}_{\ell jk})s_i^{\ell-1}\delta^{j+k}.
\end{gathered}
\tag{17.2}
$$

Every inverse defining $\gamma_i$ exists by exact evaluation. The table
lists the exact ceilings $E_i=\lceil10^{15}\eta_i\rceil$,
$Q_i=\lceil10^{12}q_i\rceil$ and, for real centres,
$S_i=\lceil2\cdot10^{15}\eta_i\rceil$.

| Label | $E_i$ | $Q_i$ | $S_i$ |
| --- | --- | --- | --- |
| 0 | 721909106 | 6272996575 | 1443818211 |
| 1 | 557182077 | 2744986374 | 1114364154 |
| 2 | 387044598 | 1012121942 | 774089196 |
| 3 | 165990891 | 203648161630 | 331981781 |
| 4 | 165209397 | 202067154217 | 330418793 |
| 5 | 65947751 | 7174020552 | 131895501 |
| 6 | 14325870 | 1011764684 | 28651740 |
| 7 | 15072025 | 2720596422 | 30144049 |
| 8 | 54594931 | 1369419267 | 109189861 |
| 9 | 24578373 | 3938457924 | nonreal |
| 10 | 24578373 | 3938457924 | nonreal |
| 11 | 167601053 | 2119294793 | 335202106 |
| 12 | 138846557 | 3697194846 | 277693113 |
| 13 | 5287786523 | 5798853285 | 10575573045 |
| 14 | 242340525 | 13600452720 | 484681049 |
| 15 | 7395594491 | 4579822343 | 14791188981 |
| 16 | 1408136604 | 1715507345 | 2816273208 |
| 17 | 2987593861 | 1599537955 | 5975187722 |

All eighteen satisfy

$$
\eta_i<10^{-5},\quad q_i<3/10,\quad
\eta_i+q_i\rho<1/25000<\rho.
\tag{17.3}
$$

**Lemma 17.1 (Complete uniform root cover).** For each fixed real base in
$\mathcal B_-$ there is one root in each displayed domain. They are sixteen
distinct real roots and two distinct nonreal roots, all simple, exhausting
all complex roots of $\mathscr R$. Its degree is exactly eighteen at every
base in the rectangle. Each real root satisfies

$$
|x_i-c_i|\le\frac{\eta_i}{1-q_i}<2\eta_i
 \le\sigma_i:=S_i/10^{15}.
\tag{17.4}
$$

Proof. At a fixed base use $G_i(x)=x-\gamma_i\mathscr R(x,p,v)$.
Its centre displacement is at most $\eta_i$, and (17.2) bounds its
derivative operator norm by $q_i$ on the domain. For a complex rectangle
$\nu(z)\le2\rho$, explaining $s_i$; convexity gives the Lipschitz bound
in the component maximum norm. Inequality (17.3) gives a strict self-map
and contraction. Banach on a real interval gives a real fixed point for
real $c_i,\gamma_i$; on a complex rectangle it applies in $\mathbb R^2$.
The derivative bounds force $\gamma_i\ne0$, so each fixed point is a root.
They also force $\mathscr R_x\ne0$ at a fixed point, since otherwise
$G_i'$ would be the identity, contradicting $q_i<1$.

The disjoint domains give eighteen distinct roots; the nonreal domains
avoid the real axis. Every specialized $\mathscr R$ has degree at most
eighteen. A zero-polynomial specialization would make $G_i'$ the identity
and contradict $q_i<1$. The degree bound now forces degree exactly
eighteen and exhausts all roots and multiplicities. This rules out any
omitted large root or specialized leading-degree drop. The fixed-point
inequality $|x_i-c_i|\le\eta_i+q_i|x_i-c_i|$ proves (17.4). ∎

## 18. Full positive-root filtering and proof of the uniform theorem

Only the nine positive real domains can contain an actual $x=n/U>0$.
Use their sharpened radii $\sigma_i$. For $P=\alpha,\zeta$, translate
at the real centre as in (17.1), and enclose it by its constant coefficient
plus and minus

$$
\sum_{(\ell,j,k)\ne(0,0,0)}
 |[z^\ell u^jw^k]P(c_i+z,p_c+u,v_c+w)|
 \sigma_i^\ell\delta^{j+k}.
\tag{18.1}
$$

Evaluate (16.3), then (15.1) and (15.3), in that order by closed
rational interval arithmetic. Products take the extrema of four endpoint
products; quotients take the extrema of four endpoint quotients only when
the denominator excludes zero. After every elementary operation round lower
endpoints down and upper endpoints up to the $10^{-80}$ grid. This also
applies to initial conversion of the exact enclosures (18.1).

The next tables give all $63$ interval pairs. Each pair $[L,U]$ means the
closed enclosure $[L,U]/10^9$, rounded outward once more only for display.
Their defining endpoint relations and sign inequalities are proved in
Proposition 20.2.

| Label | $d$ | $r$ | $b$ | $m$ |
| --- | --- | --- | --- | --- |
| 7 | $[14586594191,14586999554]$ | $[7586943746,7595671844]$ | $[5463267752,5467513771]$ | $[238792206797,238812815508]$ |
| 8 | $[-3036495092,-3036431507]$ | $[544124069,551703437]$ | $[-6137104775,-6133719207]$ | $[211213381692,211216983401]$ |
| 11 | $[39513470013,39514629802]$ | $[-91626657,-81987651]$ | $[-88641257,-87278639]$ | $[98770035747,98826561390]$ |
| 12 | $[36201152843,36209078125]$ | $[757691172,978022921]$ | $[-443634329,-435131285]$ | $[86042866710,86429707327]$ |
| 13 | $[32246783527,32261594590]$ | $[807665996,923094076]$ | $[157813654,178076524]$ | $[107040468731,107776226942]$ |
| 14 | $[34524252484,34593841383]$ | $[-596055426,-78395912]$ | $[-591122081,-514795708]$ | $[80183940220,83606155556]$ |
| 15 | $[29571620853,29622754453]$ | $[674743704,1158097067]$ | $[54147348,123344563]$ | $[100973365722,103547335728]$ |
| 16 | $[25236384389,25240768644]$ | $[-543269580,66590]$ | $[-158465814,-152043824]$ | $[85003817129,85245159290]$ |
| 17 | $[23340043727,23346144545]$ | $[1072293693,1154384911]$ | $[-273034793,-264520342]$ | $[74218684287,74584918532]$ |

| Label | $\alpha$ | $H_1$ | $C_0$ |
| --- | --- | --- | --- |
| 7 | $[-1599970973261913641111903,-1599945587307695614140967]$ | $[-30450272111,-30424162427]$ | $[217995933763,218052167743]$ |
| 8 | $[-8228122901268666205511242,-8228052647541463959147837]$ | $[49339735826,49343499999]$ | $[49106062687,49123786293]$ |
| 11 | $[-410691884994911143352237775977,-410685543386262384945660220184]$ | $[-13007790616,-12963733491]$ | $[1684110802767,1684562797208]$ |
| 12 | $[-592137278411754102768899479158,-592072187899756666311418888499]$ | $[1934924860,2221388818]$ | $[1456588903086,1459735383010]$ |
| 13 | $[1303956819604596619017640595028,1304239921607934064415551651976]$ | $[-13104487955,-12574455711]$ | $[1045357858003,1047271099185]$ |
| 14 | $[433383498874980159661093991820,433827360063689078526846688806]$ | $[5406510871,7865085933]$ | $[1314537168863,1340341580545]$ |
| 15 | $[-2054720351871524790332466319802341,-2052934866250343879811866504921451]$ | $[-9014939004,-7273898842]$ | $[874409293482,877761691522]$ |
| 16 | $[-1444619946505211843744923262684895182897,-1444493617894147092855184632939788081866]$ | $[-560171046,-426794350]$ | $[660897981930,661610803477]$ |
| 17 | $[-7820420505712346074209196724238491323742763,-7819393457382634358289515809599383839002782]$ | $[1394688884,1567448357]$ | $[612832816789,614196214705]$ |

All $\alpha,H_1,C_0$ intervals exclude zero, with $C_0>0$; positive $x$
also makes $x+1,x+2$ positive. Thus all divisions are justified before
source rejection. Uniform absolute unit bounds across the nine labels are

$$
|\alpha|\ge\frac{1599945587307695614140967}{10^9},\quad
|H_1|\ge\frac{8535887}{20000000},\quad
C_0\ge\frac{49106062687}{10^9}.
\tag{18.2}
$$

Proof of Theorem 14.1. Take any actual complete world over $\mathcal B_-$.
Lemma 15.1 puts its positive $x$ on the carrier. Lemma 17.1 puts it in
exactly one positive domain and its sharpened interval. Identity (16.2)
and the certified $\alpha$ unit force its drift by (16.3). The faithful
reconstruction forces its source, entire gain and $m$ into the intervals
above. Label $7$ has $r>1$; labels $8,11,12,14,16,17$ have $b<0$.
These contradict the original strict source conditions. Only $13,15$
remain possible.

At a fixed base each surviving domain has only one carrier root. At each
root $\alpha\ne0$ forces at most one $d$, and the injective whole-world
reconstruction forces at most one complete world. Thus there are at most
two. Label $13$ has $m$ in
$[107040468731,107776226942]/10^9\subset(107,108)$; label $15$ has it in
$[100973365722,103547335728]/10^9\subset(100,104)$. These intervals are
disjoint, so distinct worlds cannot have equal $m$. Whenever both labels
are actual their $M$ gap exceeds $3$. This proves the theorem. ∎

This uses necessary equations and injective reconstruction at actual points.
It does not replace the remaining actual guards (15.2) by $\mathscr R=0$,
or assert that surviving labels lift at every base. Singular and unused
companions were included before any filtering. No gain coefficient, gain
sample, drift, $F_0$, $A_f$ or $\Lambda$ was inverted in this filter.

## 19. Exact containment and exhaustion at the given J seed

Use the exact fixed point $z_*$ of Theorem 9.1 and the
$\bar z,Y,\eta_0,q_0$ of (9.4)–(9.7). The contraction estimate gives

$$
\|z_*-\bar z\|_\infty\le\eta_0/(1-q_0)<2\cdot10^{-24}.
\tag{19.1}
$$

This is the fixed point of Theorem 9.1. Evaluate (9.2), (2.5)–(2.7) on the full
radius-$2\cdot10^{-24}$ cube about its four-coordinate centre. Exact
outward arithmetic gives for both worlds

$$
\frac{-8215077071983784}{10^{15}}<v_*<
\frac{-8215077071983783}{10^{15}}.
\tag{19.2}
$$

These bounds are strictly inside $[v_c-10^{-5},v_c+10^{-5}]$, while
$p=-11$ exactly by (9.3). The same source evaluation puts $x(W_0)$
strictly in domain $15$ and $x(W_1)$ strictly in domain $13$. Both
sources retain $b>0$, $0<r<1$ and $D\ne0$. The full actual lifts and
distinctness are those of Theorem 9.1, with the separated values

$$
102.260466<m(W_0)<102.260467,\qquad
107.408353<m(W_1)<107.408354.
$$

Theorem 14.1 gives at most two actual worlds at this exact common base.
The two supplied distinct actual worlds give at least two, so exhaust
the entire child. This proves Corollary 14.2. ∎

Every independently selected distinct $M$ pair in this child is therefore
excluded. The conclusion does not cover the whole analytic $J$ branch of
Theorem 9.1. The original global question (1.2) remains open outside this
local exclusion: there is no global negative-branch or global
nonexistence conclusion here.

## 20. Finite coefficient and interval relations for the rectangle

**Definition 20.1 (Coefficient operations for the carrier).** A polynomial
in $(x,p,v)$ is identified with its integer coefficients $P_{ijk}$,
extended by zero to all other triples. Its product is the convolution

$$
(PQ)_{ijk}=\sum_{a=0}^i\sum_{b=0}^j\sum_{c=0}^k
 P_{abc}Q_{i-a,j-b,k-c}.
\tag{20.1}
$$

Form the six-by-six matrix $\mathsf S$ whose rows are the coefficients
of $d^3f,d^2f,df,f,dK,K$ in descending powers $d^5,\ldots,1$.
Then (15.5) specifies $\mathscr R$ by the exact identity

$$
256\mathscr D^8F_0^2\mathscr R
 =\sum_{\pi\in\mathfrak S_6}\operatorname{sgn}(\pi)
   \prod_{a=1}^6\mathsf S_{a,\pi(a)}.
\tag{20.2}
$$

This determines a unique polynomial over $\mathbb Q[x,p,v]$ because
the factor on its left is a nonzero polynomial. Expanding the right
side by (20.1), and collecting powers of $x$, gives exact division by
$256\mathscr D^8F_0^2$ with zero remainder and integer quotient.
It has the $512$ nonzero terms, degrees and constant coefficient
stated in (15.5)–(15.6). Thus (15.4), (20.1), (20.2) are a complete
finite specification of its coefficients, including normalization.
The coefficients of $\alpha,\zeta$ are specified by the same
convolution and (16.1); expansion gives (16.2) term by term. None of
these coefficient definitions changes the matrix size at a
specialized base.

For any $P(x,p,v)=\sum P_{abc}x^ap^bv^c$, its translated coefficients
at $(c_i,p_c,v_c)$ are explicitly

$$
\mathcal T^{(i)}_{\ell jk}(P)=
\sum_{\substack{a\ge\ell,\,b\ge j,\,c\ge k}}
 P_{abc}\binom a\ell\binom bj\binom ck
 c_i^{a-\ell}p_c^{b-j}v_c^{c-k}.
\tag{20.3}
$$

Only finitely many terms are nonzero. In particular
$A^{(i)}_{\ell jk}=\mathcal T^{(i)}_{\ell jk}(\mathscr R)$ in (17.1),
and the coefficient sum in (18.1) uses this same formula for
$P=\alpha,\zeta$.

**Proposition 20.2 (Exact rectangle bounds).** The tables in Sections
17–18 satisfy the following finite rational relations. At each of the
eighteen centres, $A^{(i)}_{100}\ne0$. Put
$\gamma_i=\operatorname{Round}_{100}(1/A^{(i)}_{100})$ as in (17.2).
Then their displayed integers satisfy

$$
\begin{gathered}
 E_i-1<10^{15}\eta_i\le E_i,\qquad
 Q_i-1<10^{12}q_i\le Q_i,\\
 S_i-1<2\cdot10^{15}\eta_i\le S_i
 \quad(c_i\in\mathbb R).
\end{gathered}
\tag{20.4}
$$

The eighteen domains have all $153$ pairwise separations asserted in
Section 17. The sixteen real-root radii satisfy (17.4). For the nine
positive labels, the $63$ intervals of Section 18 contain the entire
late-node reconstruction on the corresponding sharpened interval and
the full base rectangle. Every quotient used there has denominator
excluding zero.

Proof. Formula (20.3), the exact centres of Section 17, and (20.2)
reduce (17.2) to finite sums of Gaussian rationals. For $z=a+\mathrm i b$,
use $z^{-1}=(a-\mathrm i b)/(a^2+b^2)$, and
$\nu(z)=|a|+|b|$. Substitution into these finite sums gives (20.4).
For rounding, the precise relation is

$$
\operatorname{Round}_{100}(t)=k10^{-100}
\quad\Longleftrightarrow\quad
 k-\tfrac12\le10^{100}t<k+\tfrac12,
\qquad k\in\mathbb Z.
\tag{20.5}
$$

Thus all inverse, absolute-value and rounding statements are rational
identities or rational inequalities, with no choice of an approximate
root. The largest $E_i$ is $7395594491$ and the largest $Q_i$ is
$203648161630$. In particular, uniformly in $i$,

$$
\eta_i+q_i\rho
\le\frac{7395594491}{10^{15}}
 +\frac{203648161630}{10^{12}}\frac1{10^4}
 =\frac{27760410654}{10^{15}}<\frac1{25000}.
\tag{20.6}
$$

These maxima also give $\eta_i<10^{-5}$ and $q_i<3/10$.
For two centres $c_i=a_i+\mathrm i b_i$, $c_j=a_j+\mathrm i b_j$,
separation is witnessed by

$$
|a_i-a_j|>2\rho\quad\hbox{or}\quad
|b_i-b_j|>w_i+w_j,
\qquad
w_i=\begin{cases}0&b_i=0,\\\rho&b_i\ne0.\end{cases}
\tag{20.7}
$$

The centre table gives this alternative for every $i<j$. It also gives
$a_i+\rho<0$ for $0\le i\le6$,
$a_i-\rho>0$ for the nine positive labels, and
$|b_i|>\rho$ for $i=9,10$.
Since $q_i<3/10$, (20.4) gives
$\eta_i/(1-q_i)<2\eta_i\le S_i/10^{15}$ for each real centre;
(17.4) follows once Lemma 17.1 supplies the root.

For a positive label put $X_i=[c_i-\sigma_i,c_i+\sigma_i]$.
For $P=\alpha,\zeta$, take its constant translated coefficient and
radius (18.1), using (20.3), and enclose the resulting rational
interval by $\mathcal E_{10^{80}}$ from (13.1). Form
$d=-\zeta/\alpha$ by (13.2), then form
$h_3,h_4,h_5,h_6,H_0,H_1,H_2,H_7,B_0,C_0,U,b,j,r,m$
in that order from (15.1), (15.3), with base intervals
$[p_c-\delta,p_c+\delta]$, $[v_c-\delta,v_c+\delta]$.
Use the same left association and sum order as Section 13, with
$H=10^{80}$ at each product and quotient. If $V$ is any of the
resulting seven intervals $(d,r,b,m,\alpha,H_1,C_0)$, its table pair is
exactly

$$
\left(\left\lfloor10^9\inf V\right\rfloor,
      \left\lceil10^9\sup V\right\rceil\right).
\tag{20.8}
$$

The endpoint formulas (13.5) and their quotient counterparts give the
$63$ displayed pairs by finite rational arithmetic. Positive $X_i$
justify division by $x,x+1,x+2$; the displayed $\alpha,H_1,C_0$
intervals justify the remaining divisions. The sign inequalities are
visible in their endpoints. Their smallest absolute bounds are
exactly (18.2). In particular label $7$ fails $r<1$, six labels fail
$b>0$, and the two remaining $m$ intervals are disjoint. The interval
containment induction of Section 13 applies at every step, so these
bounds hold for every actual root in the sharpened intervals, not
only at their centres. This proves the finite assertions used in
Lemmas 17.1 and Theorem 14.1. ∎

**Proposition 20.3 (Seed containment in the rectangle).** Evaluate the
source response circuit on the radius-$2\cdot10^{-24}$ cube about
$\bar z$, using (13.1)–(13.3) with $H=10^{80}$. Both source intervals
satisfy $b>0$, $0<r<1$, $0\notin D$, and their $v$ intervals lie
strictly between the two rationals (19.2). The $x=n/U$ interval of
world $0$ is strictly inside domain $15$, and that of world $1$ is
strictly inside domain $13$.

Proof. The same endpoint substitutions as in Proposition 13.2, with
this smaller radius and finer grid, give (19.2) and

$$
\begin{aligned}
1478357740/10^9&<x(W_0)<1478357741/10^9,\\
1291164724/10^9&<x(W_1)<1291164725/10^9.
\end{aligned}
\tag{20.9}
$$

These intervals are strictly inside the respective radius-$10^{-4}$
domains around the displayed exact centres. The bounds (19.2) lie
strictly inside $[v_c-\delta,v_c+\delta]$ by cross multiplication,
and $p=-11$ follows from the exact equations, rather than an interval
substitution. The terminal $M$ intervals remain those of (9.1).
Together with (19.1) this proves the containment of the already
existing fixed point, and Section 19 then proves Corollary 14.2. ∎

The late-node and carrier arguments use the following mathematical
correspondences with the references of Section 1:

| Source | Mathematical use and boundary |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorems 2.1–2.2 | Original strict complete worlds, left products, clocks, undivided parent and the $d=24$ mirror case. |
| F, Definition 30.1, Lemma 30.2, (30.3)–(30.9) | Whole late-node interpolant, full faithful guards, injective $(x,d)$ reconstruction and original terminal $M$. |
| F, Definition 31.1 and Lemma 31.2; SII, Definitions 5.1–5.2 | Fixed integer carrier, its normalization and the zero-safe linear drift identity; these are reused tools. |
| S, Theorem 4.1 | Necessity on all actual worlds, including zero drift, $F_0=0$ and singular sources. |
| SIII, Definitions 1.1–1.2; SIV, Theorem 8.2 | The same full-parent semantics and undivided interpolation reductions; no global tail or regularity premise is used. |
| SV, Theorems 1.1–1.2 | A separate region $[56,58]\times[304,305]$ with $J$ injectivity and an actual $M$ point; no conclusion there is extended to this negative-base rectangle. |
| This volume, Theorem 9.1 and Section 13 | Actual $p=-11$ $J$ seed, its whole-world lifts, exact fixed-point bounds and unequal $M$ values. |

Fixed-node interpolation is the classical distinct-node theorem, as in
Berrut–Trefethen, *Barycentric Lagrange Interpolation*, §2,
[equations (2.1)–(2.2)](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf).
The Sylvester construction is the classical resultant over the polynomial
coefficient ring, as in Moreno Maza,
[Definition 4 and Propositions 5–7](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html).
Banach contraction, the implicit-function theorem and continuity are applied
with the explicit hypotheses above. The substantive result here is the
uniform negative-base entire-child exclusion and exact seed exhaustion,
with the finite coefficient and interval relations stated above.

## 追加锚（本行以下为增补区）
## 21. The original augmented-J map and its regular critical equations

Retain the entire parent $\mathcal H$ and complete worlds of Definition 1.1,
with one nonzero real gain of degree at most three, one real drift per world,
and the original clocks $0,\ldots,7$. Define

$$
\Psi_J:\mathcal H\longrightarrow\mathbb R^3,\qquad
\Psi_J(W)=(p(W),v(W),a(W)).
\tag{21.1}
$$

Its differential is taken on the full two-dimensional analytic parent.
The singular-source rank assertion used below is [SIII], Theorem 13.1,
for this same map, rather than for a fixed-source or fixed-drift slice.
Write [SVI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md) for the
regular-critical support volume.

In the regular chart put

$$
t=r/b,\quad r=tb,\quad j=t+b(1-t^2),\quad n=j+tb,\quad
T=1+b,\quad U=1+2b.
\tag{21.2}
$$

The strict source conditions are precisely $t>0$, $b>0$, $tb<1$.
In this section $D,C_0,\ldots,C_3,B_5,B_6,B_7,N_p,N_v,N_a$ mean exactly
the integer circuit (2.5) after (21.2). In particular its terminal-$J$
numerator is $N_a=-C_0+(T+2j+4tb)B_7$.
The original left products in O, Definition 1.3, have traces

$$
(1,j,T,n,U,U+n,2U+n),\qquad
\operatorname{tr}(JQ_6P)=T+2j+4tb,\quad
\operatorname{tr}(MQ_6P)=3U+2n.
\tag{21.3}
$$

Thus the $a$ in (21.1) is exactly the original clock-seven alternative.
For clarity, the regular whole-world correspondence (2.7) uses

$$
d=-\frac{C_0}{D},\qquad
 g(s)=\sum_{k=0}^3\frac{C_k}{D}
       \prod_{\substack{0\le l\le3\\l\ne k}}\frac{s-l}{k-l},
\qquad (p,v,a)=\frac{(N_p,N_v,N_a)}{D}.
\tag{21.4}
$$

This is the unique actual parent world over a strict source with $D\ne0$.
Indeed, besides the tautological clock-zero equality, direct substitution
in (2.5) gives the polynomial identities

$$
\begin{aligned}
-C_0+jC_1&=24D,&-C_0+TC_2&=(147/5)D,\\
-C_0+nC_3&=24D,&
-C_0+U(-C_0+4C_1-6C_2+4C_3)&=18D.
\end{aligned}
\tag{21.5}
$$

The interpolation rows (2.3) give $g(5)=B_5/D$, $g(6)=B_6/D$,
$g(7)=B_7/D$, proving every remaining response in (21.4) with the
same entire gain and drift. Conversely the first four clocks determine
this interpolant, and (2.1), (2.6) determine the drift when $D\ne0$.
The first two readings $0,24$ force $g\ne0$. This is the inherited
full-parent converse of O, Theorem 2.1, in the circuit normalization
of Section 2.

**Definition 21.1 (Fixed ordered regular minors).** For $f\in\{p,v,a\}$
write $N_f$ for the corresponding numerator and set

$$
L_{f,t}=D\partial_tN_f-N_f\partial_tD,\qquad
L_{f,b}=D\partial_bN_f-N_f\partial_bD,
\qquad
M_{fh}=L_{f,t}L_{h,b}-L_{f,b}L_{h,t}.
\tag{21.6}
$$

The ordered pairs are $(p,v),(p,a),(v,a)$, in that order. Define
$E_0,E_1,E_2$ by the exact polynomial divisions

$$
E_{fh}(r,b)=\frac{b^7}{45}
       \left(\frac{M_{fh}}D\right)(r/b,b),\qquad
(E_0,E_1,E_2)=(E_{pv},E_{pa},E_{va}).
\tag{21.7}
$$

These formulas specify their coefficients without choosing primitive
associates or changing signs. Coefficient addition is ordinary addition,
and multiplication of bivariate arrays is

$$
[PQ]_{uv}=\sum_{i=0}^u\sum_{j=0}^v
 [P]_{ij}[Q]_{u-i,v-j};\qquad
[\partial_tP]_{uv}=(u+1)[P]_{u+1,v}.
\tag{21.8}
$$

Use the analogous rule for $\partial_b$. Under $t=r/b$ each monomial
$t^ub^v$ becomes $r^ub^{v-u}$. Divisions by a nonzero polynomial mean
its unique exact quotient in the indicated polynomial ring; the
zero-remainder identities in Lemma 21.2 make (21.7) unambiguous.

**Lemma 21.2 (Integral equations for the regular critical locus).** Each
$M_{fh}/D$ is a polynomial in $\mathbb Z[t,b]$. Each $E_i$ is in
$\mathbb Z[r,b]$, has content one, exactly $134$ nonzero monomials, and

$$
(\deg_rE_i,\deg_bE_i,\deg E_i)=(15,17,17).
\tag{21.9}
$$

The exact identities and the original-coordinate Jacobian minors are

$$
M_{fh}(t,b)=\frac{45D(t,b)}{b^7}E_{fh}(tb,b),\qquad
\det\frac{\partial(f,h)}{\partial(r,b)}
 =\frac{45E_{fh}(r,b)}{b^8D(r/b,b)^3}.
\tag{21.10}
$$

Consequently, at every strict regular world,

$$
\operatorname{rank}d\Psi_J<2
\quad\Longleftrightarrow\quad E_0(r,b)=E_1(r,b)=E_2(r,b)=0.
\tag{21.11}
$$

Proof. Expand (21.6) using (2.5), (21.2), (21.8). Division of each
$M_{fh}$ by $D$ has zero remainder and integer quotient. Substituting
$t=r/b$ and multiplying by $b^7/45$ leaves integer coefficients;
collecting them gives (21.9) and content one. These are finite coefficient
identities specified by the displayed circuit, not values at selected
sources. The quotient rule gives $\partial_t f=L_{f,t}/D^2$ and
$\partial_b f=L_{f,b}/D^2$, hence the first minor in $(t,b)$ is
$M_{fh}/D^4$. The coordinate change has determinant
$\det\partial(t,b)/\partial(r,b)=1/b$, giving (21.10).
Strict $b>0$ and regular $D\ne0$ make its denominator nonzero.
A three-by-two matrix has rank less than two exactly when all three
ordered two-by-two minors vanish, proving (21.11). ∎

**Definition 21.3 (Fixed elimination determinants).** For $k=1,2$ form
the $30$-by-$30$ coefficient matrix with rows

$$
r^{14}E_0,r^{13}E_0,\ldots,E_0,\quad
r^{14}E_k,r^{13}E_k,\ldots,E_k
\tag{21.12}
$$

and columns $r^{29},r^{28},\ldots,1$. Its determinant is $R_k(b)$.
For the ordered pair $(E_0,E_1)$ form the $28$-by-$29$ matrix with rows

$$
r^{13}E_0,r^{12}E_0,\ldots,E_0,\quad
r^{13}E_1,r^{12}E_1,\ldots,E_1
\tag{21.13}
$$

and columns $r^{28},r^{27},\ldots,1$. Let $a_0$ be the determinant
retaining, in order, the first $27$ columns $r^{28},\ldots,r^2$
and the $r$ column. Let $c_0$ retain those same first $27$ columns
and the constant column. Thus the ordered linear subresultant is
$a_0r+c_0$. Every matrix retains its stated size under specialization.

For a nonzero rational polynomial let $\operatorname{pp}_+$ be its
primitive integer associate with positive leading coefficient. Equivalently,
clear rational denominators, divide by the positive gcd of the integer
coefficients, and choose the sign making the leading coefficient positive.
Put

$$
G_J=\operatorname{pp}_+(\gcd(R_1,R_2)),\qquad
h_J=\operatorname{pp}_+(\gcd(a_0,c_0)),\qquad
 a_J=a_0/h_J,\quad c_J=c_0/h_J.
\tag{21.14}
$$

All subsequent gcds, unless $\operatorname{pp}_+$ is explicit, are monic
gcds in $\mathbb Q[b]$. In particular no sign of $a_0$ or $c_0$ is
changed separately.

## 22. The degree-eighty-three factor and all specialization guards

Define $F_J(b)=\sum_{j=0}^{83}f_jb^j$ by the following complete
coefficient array. Every entry is an unscaled integer; the order is
descending degree.

| $j$ | $f_j$ |
| --- | --- |
| 83 | $100311603656333885113230108998811141160760582652247501247152795415972941811959466888217636753139735040000$ |
| 82 | $-1613622319206475406327345863441035572434460644345245052018162940522609584246899967379519466519980191161600$ |
| 81 | $-28594507757015602648150864574440729131734851457344834717502492059592015911002930045861567010640224854800960$ |
| 80 | $5192990237444481741589646603531958667280170086925583721482978683611041527960137141857169410162608894775892$ |
| 79 | $2549073882483502728197770886793719485939630455361443469682752286310300909027329823669225028525918863461773768$ |
| 78 | $22261549170455576613613598063016672267438337569379772922226720370683849565099777221060899352611498124319470603$ |
| 77 | $64981622358629771139500175092606033443036125789910740358160140760792789171075861570484642691580741378960016324$ |
| 76 | $-435236810641485774643757669835233065518257611166299231111822349113300809205836127574362090144751045092920360825$ |
| 75 | $-6911907641267553105179851209041805192677999369893321689095321684541310413430578958801488675685572112087510714556$ |
| 74 | $-51783758415279758492377408263035849709864382048208481801446270210585158459932057471929398881051702675638260085960$ |
| 73 | $-283303217606992334706120157759298208637526792612103005197216591801189714470274880478799979712913509950318149594596$ |
| 72 | $-1261543706897124351441340936695656141112203317584570532439930610242317949793156394881823979941213983468122566280752$ |
| 71 | $-4805121946352300569281965069709476473436460177130276912534233119510190818676254825395596261782015879397238322802394$ |
| 70 | $-16117315641593603019838108723563043420284750953269879669430610140511307676197594363451804849445752722372580219455402$ |
| 69 | $-48530677815938975004813643473362640173057434245010842207181979579168622014128329879855509866871374860842602910065590$ |
| 68 | $-132947894814386460209492260769412621940034651561178761923867785088590131388750728109693149966046352034014862503195265$ |
| 67 | $-334483005010260265611048354094183766550126920790307096746107423200318690681115795559899514195137578456415809028939066$ |
| 66 | $-777946666396523562032230996420477428137921511999723843580201693298730428231680599751183870928096439476894641529891875$ |
| 65 | $-1680269623911176735941818969609973294690541027054970861686333328983716616401831097794349485992229988844235996080618678$ |
| 64 | $-3380623331660614056501860121335257533369168145977444871329983967456516529287413691541188575688751119082851305503144540$ |
| 63 | $-6348494068417555960144454934962259510219256194984249690005538978038166427510445941236332583160717230828722254213952466$ |
| 62 | $-11140292909994726929845389830252730203751231625040201282920423606239133187684116687281170199979167549417915552886169169$ |
| 61 | $-18274616768308239858878353872813455419340308021077585405445414235547709966240832547024280890424312247023854246454180120$ |
| 60 | $-28016263895362144461642402569798772638719189128861541715835570232174235017021810468194400654957643899511272224262820716$ |
| 59 | $-40106582506834424824646462048119386512286770620694718851595516234412771416553794156395446573846879780737743489834113806$ |
| 58 | $-53541991380457213797351013418515042503059140089459085452060785517763898497955582642369200345267520927493409551536541233$ |
| 57 | $-66544450816598404665446211713834240845737632331174356685950765690845568875219861970554606207029506988070854839633287526$ |
| 56 | $-76832643642140759149462210337490074860515385911767040543068913376237240207878323543777897154557825422084538949025585208$ |
| 55 | $-82167981719986561118308085778709140661871218577969085129968751122322213356237962182511968425752807774066287857249684156$ |
| 54 | $-80976046039583601452622820431514675202657965325619880791065481445074949395197569786723885881815870894879384567926159614$ |
| 53 | $-72764364150906352326224919232666032071947596389626882617447426979487052372538743706933381101196319458530975654948770314$ |
| 52 | $-58170072358583939580389358247381160652803739321599223806352468833507207287949421325242216141511335484042784706334194380$ |
| 51 | $-38717284183837494436088672556802928034943841139466933698908639465738704259905540794399449374162888720422385240518510716$ |
| 50 | $-16533465780603627738799128893543938194392285364090791103882012524026395955499099538111721686480637277259954687531277434$ |
| 49 | $5809776285297166318697130970383041661849467217786350755765635893545096952113471388333715173200161029358602421169954924$ |
| 48 | $25437426890960608970255251033608995931101067944193018195868144277415047598462440947140005545275319182549957553550698150$ |
| 47 | $39564243115105326114122434697235291715458255061115394312890276511352335972912788089415980628138566719092754824757412656$ |
| 46 | $46236262604344444636723968447739226516090912644805999838028694523593544090282604761143092669876334234623506181273337604$ |
| 45 | $45113438311194119377936161859775293740115447322488867925077217741385867465411132606538478249122688471595653214974340936$ |
| 44 | $37753360691255472931115656159739775803170710550520796280482316077672980524955746592586482804702807618847189938198713924$ |
| 43 | $27080535696676954464785423258789171641615244178966685742102407800870410548805138081493785478681941864192596183997077456$ |
| 42 | $16262583426044981899233568503248027676463195156892056362727332809907266806845589415819132579715494254878639113734738464$ |
| 41 | $7610161219506404022483194964945469987734090853928945026918364359484697776620054573586128091305519328859292642004650912$ |
| 40 | $2051771502071278133901601570980421631812491974151630086517753584185710437017438647427576556776791578654014940744892328$ |
| 39 | $-692191823412564970196469061577062316535193227979022026729329015751733049755594769676007644364910278233892344024932384$ |
| 38 | $-1526031522038313716422636628945300713469460789576769795846365474120413293470912077326756658989620425035146764534275424$ |
| 37 | $-1397497360713853980538694519124054495586519335315347047269470984599823659605934084930802283736144128244148874568660416$ |
| 36 | $-971952517854067033523352334582633324115459156123959110246910025149659950674976506817572521141079996281645332817339952$ |
| 35 | $-579740450116061802198275257476018501387295241808907870517785076646395655057750255514690538939494499479390173024628224$ |
| 34 | $-315998229032578159619176770065924787086069708754484109344917677675076759842188790980635934260889620923528880250666112$ |
| 33 | $-165452647992296147980925956646437898651479475770498201858093057107062283290204361957972157853658348105470639582878336$ |
| 32 | $-86186640678081191462942283254257225602818634289531563270846051269401804529626693596477906970668012093495223362461184$ |
| 31 | $-44960236475213389827598190508504863167990788475917244367915456098223451514901358524809992561425862848288084409602816$ |
| 30 | $-22951328827583682487608719022601021456387642717627324728160771409431685029526954349434008146781363384169797304869376$ |
| 29 | $-11055013348624279001095220668920167174393196210211352121357831365379517631676790425739337547170779272265239538246144$ |
| 28 | $-4852068489216624963520305573628531417192963327259818236617931203655061983725170776332121562879219142240566828743424$ |
| 27 | $-1881763736597275858624059014340828344585112202569919219495944596695590113542529444225402716555444460152999119434752$ |
| 26 | $-623620876794705071888247355857195283211255195434938512139748165231913259021156936916163301021382697740793173510144$ |
| 25 | $-167316262461911514816945480669711259854144171696953664278326877138325614082719824529593141447229135967785907007488$ |
| 24 | $-31677753550047246133793447107462566024016094405543839125390129757031685622742581316798210257736425354553641734144$ |
| 23 | $-1654056972086950682419832122850164759216190211300339127924658908632196960816977154886096386313357468258218180608$ |
| 22 | $1632852839002767593130725724831484447756380467607237821751524895189310731057494934105868074670679008557923860480$ |
| 21 | $784272296746633912768123124197069942651507126488673866715360497399006590225342473465001446288274708273644830720$ |
| 20 | $186752235219138715592436550979101463291916585718444376419746949084791217153171130380970182262311565927959887872$ |
| 19 | $11647807747916358780579248243925507395938912297283568188696502701049754380103000535314957226707384256401244160$ |
| 18 | $-11257639213579259087062776740363113795002547380915357051774086842820530159168663097832016524566432086334898176$ |
| 17 | $-6170067337757776719943357343874668329395387241897352310982579284485245223788566617090586936558993303798808576$ |
| 16 | $-1966934879127151329076639332629031143646761499003656526331238162637873128479957332981756159909918020800086016$ |
| 15 | $-461662532177977054709363505445974553360237630935008542305330783914965398263892223055984867135151623160987648$ |
| 14 | $-83452318120448139452865787622686118805463526800169315849601709325922233479003609849608181400985759689736192$ |
| 13 | $-11355238814817636934651418799296104601750380039341922489546621816656917336724715483238212474181957764251648$ |
| 12 | $-1012334650665159639859725747220133780956241177494365623819411259280170332155155522811327490389400449187840$ |
| 11 | $-12413169742769952522120872727825237563894632815255310927298440648415531164385243699445109822026017669120$ |
| 10 | $15029967151178264511197661487704750518654635091937144497879348981786302228130093249778136241656368726016$ |
| 9 | $3253643726102923225372643765456862744801862249888238878665301578344943260155441740371267733361497473024$ |
| 8 | $419864922179100265814502854659659679511417393526063388525205052410544420419278521820162318012740796416$ |
| 7 | $37986300763617560699941773004230173922361614558363060424081745942713969767328868459847005393345576960$ |
| 6 | $2389928171039685273724774961591547086139821992637767468122492013072364371683806692372998493569024000$ |
| 5 | $89037878371506646133882358276854824074030563300842931304515795659641719515147827602139943796736000$ |
| 4 | $57241143986202859176954729575067962089561381769224927364265948314981546391129727301037588480000$ |
| 3 | $-216308085393290249765685000166269473388181743843097128393133901495267311145271575231594496000000$ |
| 2 | $-13328067254921548503520654741704119715981615194224547637185726750122861988812831693209600000000$ |
| 1 | $-388154939850182134613933519339299407448942781937139709753095588220740568404994293760000000000$ |
| 0 | $-4776971495279247690991338308952519740985137913069141824440033951108179148406784000000000000$ |

**Lemma 22.1 (Exact determinant, gcd and lift relations).** The fixed
polynomials of Definition 21.3 satisfy

$$
\begin{aligned}
G_J&=b^{108}(5b+2)^{16}(8b-1)^{16}(b^2+8b+4)F_J,\\
h_J&=b^{89}(5b+2)^{13}(8b-1)^{19}(b^2+8b+4),\\
\deg R_1&=\deg R_2=285,\qquad \deg G_J=225,\\
(\deg a_0,\deg c_0,\deg h_J,\deg a_J,\deg c_J)
  &=(252,253,123,129,130).
\end{aligned}
\tag{22.1}
$$

In particular $F_J$ is primitive of degree $83$ and has positive leading
coefficient. The exact quotients $R_k/G_J$ have degree $60$, and

$$
\gcd(R_1/G_J,R_2/G_J)=1.
\tag{22.2}
$$

For $i=0,1,2$ write $\ell_i(b)=[r^{15}]E_i(r,b)$ and define

$$
\begin{gathered}
J_*(r,b)=b^2+r-r^2,\qquad N_*(r,b)=J_*(r,b)+br,\\
\overline D(r,b)=b^2D(r/b,b)
 =5\bigl((b^2+8b+4)J_*N_*-2TU b(J_*+N_*)\bigr),\\
\overline N_p(r,b)=b^3N_p(r/b,b),\\
H_i(b)=\sum_{u=0}^{15}[r^u]E_i(r,b)(-c_J)^u a_J^{15-u},\\
H_D(b)=\sum_{u=0}^4[r^u]\overline D(r,b)(-c_J)^u a_J^{4-u}.
\end{gathered}
\tag{22.3}
$$

Both barred expressions are integer polynomials, with $r$ degrees four
and six respectively. All necessary specialization relations are

$$
\begin{array}{c|c}
V&\gcd(F_J,V)\\ \hline
h_J&1\\
a_J&1\\
F'_J&1\\
b(5b+2)(8b-1)(b^2+8b+4)&1\\
\ell_0&1\\
\ell_1&1\\
\ell_2&1\\
H_D&1
\end{array}
\qquad
\operatorname{rem}_{F_J}H_0=
\operatorname{rem}_{F_J}H_1=
\operatorname{rem}_{F_J}H_2=0.
\tag{22.4}
$$

Here the $H_i$ are local lift polynomials, distinct from the late-node
samples $H_i$ of (15.1).

Proof. All equalities in (22.1)–(22.4) are finite coefficient relations.
Here are explicit coefficient operations determining them. Expand (2.5)
by (21.8), take the derivatives (21.6), and use the exact divisions
(21.7). For a square coefficient matrix $B$, expand

$$
\det B=\sum_{\pi\in\mathfrak S_N}\operatorname{sgn}(\pi)
                 \prod_{u=1}^N B_{u,\pi(u)}.
\tag{22.5}
$$

Apply this formula to (21.12) and the two ordered minors of (21.13).
For rational polynomials $V\ne0$, obtain $\operatorname{rem}_V U$ by
repeatedly subtracting

$$
\frac{\operatorname{lc}U}{\operatorname{lc}V}
       b^{\deg U-\deg V}V
\tag{22.6}
$$

from a current nonzero $U$ whenever $\deg U\ge\deg V$.
A gcd is the last nonzero member of the successive pairs
$(U,V)\mapsto(V,\operatorname{rem}_V U)$, normalized as stated in
Definition 21.3. These operations on $R_1,R_2$ give the first product
in (22.1), with the displayed $84$ coefficients as its remaining
primitive factor. They give the second product from $a_0,c_0$.
Exact division by those products leaves the degrees in (22.1), (22.2).
Applying the same remainder recurrence to the eight pairs in (22.4)
leaves a nonzero constant in each case; monic normalization is $1$.
Expansion of the three sums $H_i$ leaves zero remainder upon division
by $F_J$. Thus the quotient, remainder and terminal-degree relations
are specified entirely over $\mathbb Q$, without a choice of an algebraic
root or a suppressed determinant normalization.

The finite degree bounds can also be read directly from (21.9).
For the coefficient of $r^j$ in $r^kE_i$, the $b$ degree is at most
$17+k-j$. Hence a determinant term in (21.12) has degree at most

$$
30\cdot17+2\sum_{k=0}^{14}k-\sum_{j=0}^{29}j=285.
\tag{22.7}
$$

For (21.13) the two bounds are
$28\cdot17+2\sum_{k=0}^{13}k-(\sum_{j=2}^{28}j+1)=252$
and $253$ when the last column is constant. The nonzero top coefficients
in their expansions give equality in these bounds. The formulas for
$J_*,N_*$ give the expression for $\overline D$; expanding $\overline N_p$
by the same circuit gives the asserted integer polynomial and degree.
Finally the coefficient gcd of the displayed array is one, its first
entry is positive, and its last entry is nonzero. This proves the
normalization, simplicity and nonzero-constant assertions used below. ∎

**Lemma 22.2 (Unique guarded algebraic lift).** For every complex root
$\beta$ of $F_J$, the three polynomials $E_i(r,\beta)$ have exactly
one common root,

$$
\rho=-c_J(\beta)/a_J(\beta),\qquad
\overline D(\rho,\beta)\ne0.
\tag{22.8}
$$

In particular this lift is real for real $\beta$.

Proof. The gcd relations (22.4) imply that $a_J(\beta)$,
$h_J(\beta)$ and every $\ell_i(\beta)$ are nonzero. Thus the three
initial $r$ degrees remain $15$. Equation (22.1) makes
$R_1(\beta)=0$, and the fixed linear subresultant has nonzero
$r$ coefficient $a_0(\beta)=h_J(\beta)a_J(\beta)$.
The classical subresultant gcd criterion, with these preserved initial
degrees, makes the gcd of $E_0(r,\beta),E_1(r,\beta)$ have degree
exactly one and root $-c_0(\beta)/a_0(\beta)=\rho$.
This is precisely the criterion used in SVI, Lemma 12.3, applied here
to the polynomials of (21.7). It concerns the fixed ordered minors,
not a matrix resized after specialization.

The three zero remainders in (22.4), together with $a_J(\beta)\ne0$,
give $E_i(\rho,\beta)=0$ for all $i$. They identify a common root of
all three, rather than merely separate roots supplied by two resultants.
Uniqueness follows already from the degree-one gcd of the first pair.
The last gcd in (22.4) gives $H_D(\beta)\ne0$, whence
$\overline D(\rho,\beta)=H_D(\beta)/a_J(\beta)^4\ne0$.
Real coefficients give the final assertion. ∎

## 23. All positive roots and their strict-world filtering

Use $\operatorname{pp}(P)=P/\operatorname{cont}(P)$ for a nonzero
integer polynomial, where its content is positive. This operation
preserves its sign, including the sign of its leading coefficient.
For $\deg P=m\ge n=\deg Q$, define the integer pseudo-remainder by

$$
\operatorname{prem}(P,Q)
 =\operatorname{lc}(Q)^{m-n+1}\operatorname{rem}_Q P.
\tag{23.1}
$$

For the displayed $F_J$ define the signed primitive Sturm chain

$$
\begin{gathered}
S_0=F_J,\qquad S_1=\operatorname{pp}(F'_J),\\
\delta_i=\deg S_{i-1}-\deg S_i+1,\qquad
S_{i+1}=\operatorname{pp}\left(
 -\operatorname{prem}(S_{i-1},S_i)
       \operatorname{sign}(\operatorname{lc}S_i)^{\delta_i}\right).
\end{gathered}
\tag{23.2}
$$

Stop at the last nonzero constant. The sign multiplier makes each
successor a positive multiple of the negative ordinary rational
remainder, so this is a Sturm chain. For a real argument $z$ let
$V(z)$ be the number of variations in the ordered signs of
$S_0(z),S_1(z),\ldots$, with zeros deleted. At $+\infty$ use the
signs of their leading coefficients.

**Lemma 23.1 (Complete positive-root signs).** The degrees of (23.2)
are $83,82,\ldots,0$. The following are its full ordered sign words,
with each character representing one sign. All finite-argument signs
in the table are nonzero. In the row labels put

$$
(q_1,q_2,q_3,q_4,q_5)
 =(4632607,12856673,64878432,90481370,2515351400),\qquad
L_i=q_i/10^8,\quad U_i=(q_i+1)/10^8.
\tag{23.3}
$$

| Argument | Sign word of $S_0,\ldots,S_{83}$ | $V$ |
| --- | --- | --- |
| $0$ | `--+-++++---++-+---+----+-+---+---+++--++--++---++--+++---++-+++++--++------+++++--++` | 35 |
| $+\infty$ | `+++++-++---+++---++--++-++----++++-+--+++---++----+-----+++-+++++--+-------+++++--++` | 30 |
| $L_1$ | `-+--++----++--+---+---+--+---+---+++--+--++--++++--++----++-+++++--+-------+++++--++` | 35 |
| $U_1$ | `++--++----++--+---+---+--+---+---+++--+--++--++++--++----++-+++++--+-------+++++--++` | 34 |
| $L_2$ | `+-++--++++--++-+++-+++-++-+++-+++---++-+++-++----+++----+++-+++++--+-------+++++--++` | 34 |
| $U_2$ | `--++--++++--++-+++-+++-++-+++-+++---++-+++-++----+++----+++-+++++--+-------+++++--++` | 33 |
| $L_3$ | `-++-++----++--+---++---+-+----+++--+--++++--+-----+-----+++-+++++--+-------+++++--++` | 33 |
| $U_3$ | `+++-++----++--+---++---+-+----+++--+--++++--+-----+-----+++-+++++--+-------+++++--++` | 32 |
| $L_4$ | `+--+--++++--++-+++--+++--+----+++--+--++++--+-----+-----+++-+++++--+-------+++++--++` | 32 |
| $U_4$ | `---+--++++--++-+++--+++--+----+++--+--++++--+-----+-----+++-+++++--+-------+++++--++` | 31 |
| $L_5$ | `-++++-++---+++---++--++-++----++++-+--+++---++----+-----+++-+++++--+-------+++++--++` | 31 |
| $U_5$ | `+++++-++---+++---++--++-++----++++-+--+++---++----+-----+++-+++++--+-------+++++--++` | 30 |

There are exactly five positive roots of $F_J$, all simple, with exactly
one root $\beta_i$ in each open interval $(L_i,U_i)$.

Proof. Recurrence (23.2), starting with the complete integer array in
Section 22, gives one nonzero polynomial of each degree down to zero.
All its coefficients are determined by (23.1), polynomial division
(22.6), and division by positive integer content. Evaluate each
polynomial by descending Horner at the displayed rational arguments;
the resulting signs are exactly the words in the table. Thus its
entries and variation counts are finite rational sign relations.
The chain has $84$ entries; in particular it has no zero polynomial
before the final constant. The gcd relation with $F'_J$ in (22.4)
also excludes a repeated root.

Sturm's theorem gives $V(0)-V(+\infty)=35-30=5$ positive roots.
The five disjoint intervals have the respective variation drops
$(35,34),(34,33),(33,32),(32,31),(31,30)$, so each contains one.
Their total is five and exhausts the positive roots. ∎

The following finite rational interval definitions specify the lifts,
including the denominator guards and strict comparisons. They use exact
rational endpoints, without a rounding grid. For intervals $A=[l,u]$,
$B=[v,w]$, use endpoint addition and negation, and

$$
\begin{aligned}
AB&=[\min(lv,lw,uv,uw),\max(lv,lw,uv,uw)],\\
A/B&=[\min(l/v,l/w,u/v,u/w),\max(l/v,l/w,u/v,u/w)]
               \quad(0\notin B).
\end{aligned}
\tag{23.4}
$$

For a univariate polynomial $P=\sum_{j=0}^m p_jb^j$, define its interval
Horner value on $I$ from $Z_m=[p_m,p_m]$ by
$Z_j=Z_{j+1}I+[p_j,p_j]$, descending to $j=0$.
For $P(r,b)=\sum_{u=0}^m P_u(b)r^u$, first form the Horner value
of each $P_u$ on $I$, then use those intervals as the coefficients
of descending Horner in the interval for $r$. Denote these fixed
finite expressions by $\mathfrak H(P;I)$ and $\mathfrak H(P;R,I)$,
respectively. Induction using (23.4) proves containment of the exact
polynomial values for every argument in the intervals.

Starting with $I_i^{(0)}=[L_i,U_i]$, define exactly $400$ dyadic
refinements. If $I_i^{(j)}=[l,u]$ and $z=(l+u)/2$, set

$$
I_i^{(j+1)}=
\begin{cases}
[l,z],&F_J(l)F_J(z)<0,\\
[z,u],&F_J(z)F_J(u)<0.
\end{cases}
\quad(0\le j<400).
\tag{23.5}
$$

The finite guards for this rule are $F_J(z)\ne0$ at every one of its
$2000$ midpoints and opposite nonzero endpoint signs at every step.
Let $I_i=I_i^{(400)}$ and form

$$
\begin{gathered}
A_i=\mathfrak H(a_J;I_i),\qquad C_i=\mathfrak H(c_J;I_i),\qquad
\mathcal R_i=-C_i/A_i,\\
\mathcal D_i=\mathfrak H(\overline D;\mathcal R_i,I_i),\qquad
\mathcal N_i=\mathfrak H(\overline N_p;\mathcal R_i,I_i),\qquad
\mathcal P_i=\mathcal N_i/(I_i\mathcal D_i).
\end{gathered}
\tag{23.6}
$$

The factor $I_i$ in the last denominator is essential:
$p=\overline N_p/(b\overline D)$ in the original model.

**Lemma 23.2 (All guarded lift bounds).** Every refinement (23.5) is
well defined, retains its unique root, and has final width
$1/(10^8 2^{400})$. In (23.6), $0\notin A_i$, $0\notin\mathcal D_i$
and $0\notin I_i$ for all five labels. The following are strict
rational enclosures. An entry $(u,v)/10^k$ means that the entire
corresponding interval is contained in the indicated open interval.

| $i$ | $q_i$ | $\mathcal R_i$ | Sign of every element of $\mathcal D_i$ | $\mathcal P_i$ |
| --- | --- | --- | --- | --- |
| 1 | 4632607 | $(4749917,4749918)/10^8$ | $+$ | $(-533512131,-533512130)/10^6$ |
| 2 | 12856673 | $(89953167,89953168)/10^8$ | $-$ | $(-10890382,-10890381)/10^6$ |
| 3 | 64878432 | $(121975351,121975352)/10^8$ | $-$ | unrestricted |
| 4 | 90481370 | $(-39521073,-39521072)/10^8$ | $-$ | unrestricted |
| 5 | 2515351400 | $(-2094185026,-2094185025)/10^8$ | $-$ | unrestricted |

Here unrestricted means only that no numerical bound for
$\mathcal P_i$ is asserted in that table entry.

Proof. Evaluate $F_J$ by rational Horner at the midpoints defined in
(23.5). At each of the $400$ refinements for each label its value is
nonzero; exactly one of the two displayed products is negative.
These are finite rational inequalities determined by the Section 22
coefficient array and (23.3), (23.5). The unique root is in the selected
half by the intermediate-value theorem and Lemma 23.1. The width is
halved each time.

For completeness the rational comparisons defining the second table
can be expressed without approximate algebraic arguments. If the
$r$ entry is $(u_i,v_i)/10^8$, the exact endpoint relations are

$$
\begin{gathered}
0\notin A_i,\qquad
u_i/10^8<\inf\mathcal R_i\le\sup\mathcal R_i<v_i/10^8,\\
\inf\mathcal D_1>0,\qquad
\sup\mathcal D_i<0\quad(2\le i\le5),\\
-533512131/10^6<\inf\mathcal P_1
 \le\sup\mathcal P_1<-533512130/10^6,\\
-10890382/10^6<\inf\mathcal P_2
 \le\sup\mathcal P_2<-10890381/10^6.
\end{gathered}
\tag{23.7}
$$

Substitution of (22.3), (21.14) in the finite descending Horner
recurrences, with products and quotients as in (23.4), gives these
relations by rational endpoint arithmetic. In particular the quotient
by $A_i$ is guarded before forming $\mathcal R_i$, and the displayed
$\mathcal D_i$ signs guard the last quotients; all $I_i$ are positive.
These formulas determine every rational endpoint even though their
large numerators and denominators need not be expanded. The
containment induction for (23.4) consequently places the exact
$\rho_i=-c_J(\beta_i)/a_J(\beta_i)$, $\overline D(\rho_i,\beta_i)$
and the lifted response
$\overline N_p(\rho_i,\beta_i)/(\beta_i\overline D(\rho_i,\beta_i))$
in the displayed enclosures. ∎

For $i=1,2$ define the complete triples

$$
\begin{gathered}
\rho_i=-c_J(\beta_i)/a_J(\beta_i),\qquad \tau_i=\rho_i/\beta_i,\\
P_i^J=\begin{pmatrix}
\rho_i&\beta_i\\
\rho_i(1-\rho_i)/\beta_i&1-\rho_i
\end{pmatrix},\qquad
 d_i^J=-C_0(\tau_i,\beta_i)/D(\tau_i,\beta_i),\\
g_i^J(s)=\sum_{k=0}^3
 \frac{C_k(\tau_i,\beta_i)}{D(\tau_i,\beta_i)}
 \prod_{\substack{0\le l\le3\\l\ne k}}\frac{s-l}{k-l},\qquad
\mathcal W_i^J=(P_i^J,g_i^J,d_i^J).
\end{gathered}
\tag{23.8}
$$

These definitions specify each entire real gain and its own real drift,
rather than only projected coordinates or selected samples. The two
$\rho_i$ intervals lie in $(0,1)$ and the $\beta_i$ intervals are
positive. Their $D$ signs are respectively $+$ and $-$, because
$D(\tau_i,\beta_i)=\overline D(\rho_i,\beta_i)/\beta_i^2$.
Equations (21.4)–(21.5) therefore make both triples actual strict
regular complete worlds. Their gains are nonzero by their unequal
clock-zero and clock-one readings. The two disjoint source boxes give
distinct complete worlds. For the remaining three roots, Lemma 23.2
gives respectively $\rho_3>1$, $\rho_4<0$, $\rho_5<0$; each violates
the original strict source condition.

## 24. Complete augmented-J critical classification and the nonnegative-p consequence

The positive exceptional factor $8b-1$ must be treated before the
regular classification. Put

$$
S_*(r)=438272r^4-931328r^3+540800r^2-50728r-853.
\tag{24.1}
$$

The exact specialization relations, with the gcd monic in $\mathbb Q[r]$,
are

$$
\begin{gathered}
\gcd\bigl(E_0(r,1/8),E_1(r,1/8),E_2(r,1/8)\bigr)
       =\frac{S_*(r)^2}{438272^2},\\
D(8r,1/8)=\frac{15}{4096}S_*(r),\qquad
N_p(8r,1/8)-24D(8r,1/8)=0.
\end{gathered}
\tag{24.2}
$$

They follow by substituting $b=1/8$ in the coefficient definitions
(21.6)–(21.8), (2.5) and applying rational polynomial division (22.6)
with variable $r$. In particular every simultaneous minor zero on
$b=1/8$ has $D=0$. This exceptional branch supplies no regular critical
world. Its regular worlds have $p=24$.

**Theorem 24.1 (Entire strict augmented-J critical locus).** For every
actual strict complete world $W\in\mathcal H$,

$$
\operatorname{rank}d\Psi_J(W)<2
\quad\Longleftrightarrow\quad
 W\in\{\mathcal W_1^J,\mathcal W_2^J\}.
\tag{24.3}
$$

Both worlds are regular and have negative $p$; more precisely

$$
\begin{aligned}
-533512131/10^6&<p(\mathcal W_1^J)<-533512130/10^6,\\
-10890382/10^6&<p(\mathcal W_2^J)<-10890381/10^6.
\end{aligned}
\tag{24.4}
$$

Proof. Suppose first that $D(W)\ne0$ and the rank is less than two.
Lemma 21.2 makes its source a common zero of $E_0,E_1,E_2$.
Each fixed matrix (21.12), specialized at this source, annihilates

$$
(r^{29},r^{28},\ldots,r,1)^{\mathsf T}.
\tag{24.5}
$$

The column is nonzero, and the row evaluations are the corresponding
shifted $E_0,E_k$, all zero. Thus $R_1(b)=R_2(b)=0$, including any
specialized leading-degree drop. The univariate gcd identity (22.1)
then forces one of its displayed factors to vanish. For $b>0$ the
factors $b$, $5b+2$ and $b^2+8b+4$ are positive. The sole remaining
positive exceptional branch $b=1/8$ has already been excluded for
regular worlds by (24.2). Hence $F_J(b)=0$.

Lemma 23.1 gives exactly the five possibilities $b=\beta_i$.
All specialization guards in (22.4) hold at every such root, so
Lemma 22.2 forces $r=\rho_i$. Three violate $0<r<1$ by Lemma 23.2.
The two surviving strict sources have $D\ne0$ and their unique
whole-world lifts are exactly (23.8), by the original correspondence
(21.4). This proves necessity on the regular parent.

Conversely Lemma 22.2 makes all three $E_i$ vanish at each surviving
source. Its $D\ne0$, strictness and actual complete-world lift were
proved after (23.8). Lemma 21.2 therefore gives rank less than two
at both $\mathcal W_i^J$. Lemma 23.2 gives (24.4).

Finally $D=0$ is equivalent to $\Lambda=0$ at a strict source by
(2.6). At every such actual world [SIII], Theorem 13.1, gives rank
two for the same $\Psi_J$ on the full analytic parent. This includes
both entire singular lines and every real drift; it is not obtained
by continuing the regular quotient through its zero denominator.
It rules out any further singular critical world and completes
(24.3). ∎

**Corollary 24.2 (Full-parent rank at every nonnegative fifth response).**
For every actual strict world $W\in\mathcal H$ with $p(W)\ge0$,

$$
\operatorname{rank}d(p,v,a)_W=2.
\tag{24.6}
$$

This includes every complete world, selected or unused, in every
entire child $C(p,v)$ with $p\ge0$.

Proof. The two worlds in (24.3) have strictly negative $p$ by
(24.4), so neither can be $W$. The differential has two-dimensional
domain and therefore rank at most two. The theorem excludes rank
less than two, proving (24.6). ∎

In particular, let $W_1$ be the exact first $M$-critical world of
SVI, Definition 13.1 and Theorem 13.3, and put
$y_1=(p(W_1),v(W_1))$. Its exact algebraic source has

$$
\begin{gathered}
0.0084901253<r(W_1)<0.0084901254,\qquad
0.0084574469<b(W_1)<0.0084574470,\qquad D(W_1)\ne0,\\
690.595905<p(W_1)<690.595906
\end{gathered}
\tag{24.7}
$$

by SVI, Lemma 13.2. These finite decimals denote exact rational
endpoints; $W_1$ and $y_1$ retain their algebraic definitions there.
Every $W\in C(y_1)$ has the same positive $p(W_1)$, so (24.6) applies
to every such world. In particular there is no different regular
rank-drop companion of the kind in SVI, Theorem 19.3(b), at this
base. This includes every unused or singular companion in that entire
child.

The regular proof divides only by $b>0$, $D\ne0$, fixed nonzero
interpolation-node differences, and the guarded algebraic units in
(22.4), (23.6). It divides by no drift, $d-24$, gain sample, leading
gain coefficient, gain-root difference or auxiliary response. Zero
drift, lower gain degrees, sampled zeros, repeated roots, arbitrary
gain signs and all unused strata therefore remain in its domain.
The singular part is covered separately on the full parent by SIII.

Rank two yields a locally injective two-coordinate submap near each
world, by the inverse-function theorem. It does not identify worlds
in different such neighborhoods. In particular (24.6) alone does not
decide whether a child contains distinct worlds with equal $a$.
The independently selected $J$ and $M$ pairs in (1.2) still use the
same entire child, may share endpoints, and may have different common
terminal values. The global existence-or-exclusion question (1.2)
remains unresolved.

The model correspondence in (21.3)–(21.5) is O, Definitions 1.1–1.3
and Theorem 2.1, with O's sixth-$M$ response identified with $v$.
The regular circuit and whole-gain reconstruction are (2.5)–(2.7);
the full singular supplier is SIII, Theorem 13.1. Fixed-node
interpolation is the classical distinct-node formula cited in
Section 11, Berrut–Trefethen, §2. The fixed Sylvester construction
and subresultant gcd criterion are classical; see Basu, Pollack and
Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 8, [DOI 10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2),
and the same criterion in SVI, Lemma 12.3. Sturm's real-root theorem
and sign variation are used with the full chain (23.2); see the
same book, Chapters 2 and 8. The source-specific factor (22.1),
its guarded lifts and the five-root filtering give the complete
original-model critical locus (24.3).

## 追加锚（本行以下为增补区）

## 25. Two exact J-critical singleton children

Write $\operatorname{base}(W)=(p(W),v(W))$. Continue with the complete worlds of
Definition 1.1 and the exact algebraic worlds $\mathcal W_i^J$ of (23.8), for $i=1,2$. Put

$$
z_i=(\rho_i,\beta_i),\qquad
q_i=(p_i,v_i)=(p(\mathcal W_i^J),v(\mathcal W_i^J)),\qquad
x_i=\frac{j(z_i)+\rho_i}{1+2\beta_i}.
\tag{25.1}
$$

The algebraic definitions in (23.8) are retained. In particular the
rational centres below are data for enclosing these exact sources;
none replaces $z_i$, $q_i$ or a complete world.

**Theorem 25.1 (The two entire-child inventories).** At both exact bases,

$$
C(q_1)=\{\mathcal W_1^J\},\qquad
C(q_2)=\{\mathcal W_2^J\}.
\tag{25.2}
$$

There are no other actual worlds, singular or regular, in either child.
Consequently each child has zero unordered distinct equal-$M$ pairs.

**Theorem 25.2 (Open complete-child M exclusions).** For each $i=1,2$
there is an open neighborhood $V_i\subset\{(p,v):p\ne24\}$ of $q_i$ such
that $m:C(p,v)\to\mathbb R$ is injective for every $(p,v)\in V_i$.
Neither a numerical radius nor constant singleton cardinality on $V_i$
is asserted.

**Theorem 25.3 (No strict J-diagonal joint limit).** There is no sequence
of configurations (1.2) whose two selected $J$ endpoints both converge,
as complete worlds, to a single strict world $Z\in\mathcal H$.
Convergence of complete worlds means convergence of $(r,b,d)$ and all
four coefficients of the entire gain polynomial. The selected $M$
endpoints need not converge. The two independent pairs may overlap,
and their common terminal values may differ.

Sections 26–29 give the finite data and prove (25.2). Section 30 proves
the two local consequences. No assertion of global disjointness of
$D_J,D_M$ follows.

## 26. Exact source boxes and evaluated differential units

Here is a polynomial version of (2.5), in original source coordinates.
It also fixes the normalization for all differential evaluations below:

$$
\begin{gathered}
X=b^2+r-r^2,\quad N=X+br,\quad T=1+b,\quad U=1+2b,\\
L=b^2+8b+4,\quad A=(8b-1)(5b+2),\\
\Delta=5\{LXN-2bTU(X+N)\},\qquad \ell=b\Delta,\\
\bar C_0=-24\Delta+3AXN,\quad
\bar C_1=3ANb,\\
\bar C_2=3(49b+34)XN-54Ub(X+N),\quad
\bar C_3=3AXb,\\
\bar B_5=-4\bar C_0+15\bar C_1-20\bar C_2+10\bar C_3,\\
\bar B_6=-10\bar C_0+36\bar C_1-45\bar C_2+20\bar C_3,\\
\bar B_7=-20\bar C_0+70\bar C_1-84\bar C_2+35\bar C_3,\\
P=-b\bar C_0+(Ub+N)\bar B_5,\quad
V=-b\bar C_0+(2Ub+N)\bar B_6,\\
A_J=-b\bar C_0+(Tb+2X+4rb)\bar B_7,\quad
M_M=-b\bar C_0+(3Ub+2N)\bar B_7.
\end{gathered}
\tag{26.1}
$$

The letters $P,V,A_J,M_M$ in this circuit are polynomials; $P$ here is
not the source matrix. Precisely,
$\Delta=b^2D(r/b,b)$ and $\bar C_k=b^2C_k(r/b,b)$. Thus

$$
(p,v,a,m)=(P,V,A_J,M_M)/\ell,\qquad
 d=-\bar C_0/\Delta,\qquad g(k)=\bar C_k/\Delta\quad(0\le k\le3).
\tag{26.2}
$$

The gain is the same fixed-node interpolant (2.2). These are whole-world
identities with the original clocks, rather than a change of model.
For a numerator $F$ define
$L_{F,r}=\ell F_r-F\ell_r$ and $L_{F,b}=\ell F_b-F\ell_b$.
For the ordered pairs $(P,V),(P,A_J),(V,A_J)$ the coefficient identities
are

$$
L_{F,r}L_{G,b}-L_{F,b}L_{G,r}
 =45b^2\Delta E_{fh}(r,b),
\quad (f,h)=(p,v),(p,a),(v,a),
\tag{26.3}
$$

with exactly the $E_{fh}$ of (21.7), including signs and scalars.
Indeed the determinant on the left is $\ell^4$ times the corresponding
rational Jacobian minor; substituting (21.10) and
$D=\Delta/b^2$ gives (26.3). Each $E_{fh}$ has the $134$ terms and
degrees (21.9). Formula (26.3) or (21.7), with convolution (21.8),
is a finite coefficient specification, not an additional eliminant.

All finite decimals in the following source and root tables denote
exact rational numbers. Define $\widehat z_i=(\widehat r_i,\widehat b_i)$
by the complete entries in this table:

| $i$ | $\widehat r_i$ | $\widehat b_i$ |
| --- | --- | --- |
| 1 | $0.0474991739156158648087872696795839340094732632129244067254357987$ | $0.04632607241297142362371158699116141188135188088603214209272150218$ |
| 2 | $0.8995316741215982684097269764207819803504111050038539630302674411$ | $0.12856673030826475721724380187978394414949243099439809190709327953$ |

Set $h=10^{-55}$ and
$K_i=\widehat z_i+[-h,h]^2$. The following interval convention specifies
all remaining finite calculations. For $H=10^{120}$ let

$$
\mathcal E([l,u])=
 [\lfloor Hl\rfloor/H,\lceil Hu\rceil/H].
\tag{26.4}
$$

Enclose an input rational by $\mathcal E([t,t])$. After every elementary
addition, subtraction, multiplication or reciprocal, apply $\mathcal E$
to the ordinary endpoint interval. Multiplication uses the minimum and
maximum of the four endpoint products. A reciprocal is formed only
when zero is excluded, and uses $[1/u,1/l]$; division means
multiplication by this reciprocal. Negation is endpoint reversal.
All these operations contain the exact real operation.

For a sparse polynomial in a specified variable order, form each power
table from power zero upward by successive multiplication. Sum nonzero
monomials in increasing lexicographic exponent order, starting from
zero; for each monomial multiply its coefficient by the powers in
variable order. Use order $(r,b)$ for (26.1), $E_{fh}$ and their
polynomial derivatives, order $(x,p,v)$ for the carrier and drift
polynomials, and order $(p,v)$ for a fixed $x$ coefficient. All quotient
rule expressions use their displayed polynomial derivatives before
interval evaluation. This removes any ambiguity from cancellation or
choice of evaluation order.

Put $E=(E_{pv},E_{pa})^{\mathsf T}$. Compute the rational matrix
$J_i=DE(\widehat z_i)$ exactly, and set

$$
(Y_i)_{uv}=10^{-90}\lfloor10^{90}(J_i^{-1})_{uv}\rfloor,
\quad
\eta_i=\|Y_iE(\widehat z_i)\|_\infty,\quad
\theta_i=\sup_{z\in K_i}\|I-Y_iDE(z)\|_\infty.
\tag{26.5}
$$

Here an upper bound for $\eta_i$ uses (26.4) and the polynomial rule;
an upper bound for $\theta_i$ is the largest row sum of the component
absolute interval bounds for $I-Y_iDE(K_i)$. The inverse defining $Y_i$
is the exact two-by-two rational inverse before downward rounding.
Both $\det J_i$ and $\det Y_i$ are nonzero. The finite bounds are

| $i$ | Upper bound for $\eta_i$ | Upper bound for $\theta_i$ | Sign of $\ell(K_i)$ |
| --- | --- | --- | --- |
| 1 | $2943\,10^{-69}$ | $2\,10^{-45}$ | $+$ |
| 2 | $223\,10^{-68}$ | $10^{-40}$ | $-$ |

All upper comparisons in this and subsequent bound tables are strict.
In particular

$$
\eta_i+\theta_i h<h,\qquad
\frac{\eta_i}{1-\theta_i}<3\,10^{-66}.
\tag{26.6}
$$

For reproducible differential bounds, evaluate

$$
p_r=\frac{L_{P,r}}{\ell^2},\qquad
k=(-p_b,p_r),\qquad \kappa=dx(k),\qquad
\mu=p_rm_b-p_bm_r,\qquad x=\frac{N}{bU}.
\tag{26.7}
$$

The derivatives of $x$ are obtained from this last rational formula.
The following enclosures hold on the entire $K_i$; thus they hold at
the exact source as well.

| $i$ | $p_r$ | $\kappa$ | $\mu=\det D_{(r,b)}(p,m)$ |
| --- | --- | --- | --- |
| 1 | $(32013849,32013850)$ | $(-12774005,-12774004)$ | $(2250469535,2250469536)$ |
| 2 | $(160908,160909)$ | $(-376697,-376696)$ | $(10415315,10415316)$ |

**Lemma 26.1 (Source enclosure and identification).** Each $K_i$ contains
one zero of $E$, lying within $3\,10^{-66}$ of its centre in maximum
norm. This zero is exactly $z_i$ of (25.1). The source is strict and
regular, and (26.2) gives precisely $\mathcal W_i^J$.

Proof. The endpoint operations and the integer coefficient recurrences
(21.8), (26.1), (26.3) give the bounds in (26.5)–(26.7) by rational
arithmetic. More explicitly, every lower comparison is a comparison
with the minimum endpoint of its prescribed interval and every upper
comparison is with the maximum endpoint; after clearing positive powers
of $10$, they are integer inequalities. Invert $J_i$ exactly by its
adjugate and determinant, round its four entries as in (26.5), evaluate
$E$ at the centre and $DE$ on $K_i$, and take the two row sums. These
finite operations give respectively the first two columns of the
bound table. Evaluation of (26.7) by its quotient rule gives the three
integer-interval enclosures. No algebraic-root approximation enters
these comparisons.

The map $z\mapsto z-Y_iE(z)$ has Lipschitz constant at most
$\theta_i<1$ on the convex cube, and its displacement from the centre
is at most $\eta_i+\theta_i h<h$. It therefore maps $K_i$ strictly
into itself. The contraction theorem gives a unique fixed point and,
since $Y_i$ is invertible, a unique zero of $E$ there. The usual
geometric-series bound gives (26.6).

The displayed cubes are strict source cubes, and their $\ell$ signs
make them regular. Their $r$ coordinates are in the corresponding
$r$ intervals of Lemma 23.2, and their $b$ coordinates are in the
corresponding intervals (23.3). At the zero, $p_r\ne0$ and the two
minors $(p,v),(p,a)$ vanish. The determinant identity

$$
p_r\det D(v,a)-v_r\det D(p,a)+a_r\det D(p,v)=0
\tag{26.8}
$$

forces the third minor to vanish. The full-parent classification
Theorem 24.1 now identifies its unique whole-world lift with the
corresponding world (23.8). The cubes cannot interchange the two
worlds because their source intervals are disjoint. The whole gain
and the drift are forced by (26.2), not chosen anew. ∎

The following open enclosures record the exact bases and the critical
carrier and terminal values; each entire interval evaluation of the
corresponding expression on $K_i$ is inside the displayed interval.
For $d,m$ the forced lift in Section 28 supplies these bounds.

| Quantity | $i=1$ | $i=2$ |
| --- | --- | --- |
| $p$ | $(-533512131/1000000,-53351213/100000)$ | $(-5445191/500000,-10890381/1000000)$ |
| $v$ | $(-203835443/200000,-509588607/500000)$ | $(-509599/62500,-8153583/1000000)$ |
| $x$ | $(244919203169/250000000000,979676812677/1000000000000)$ | $(688485537633/500000000000,1376971075267/1000000000000)$ |
| $d$ | $(76059941/125000,608479529/1000000)$ | $(3850713/125000,6161141/200000)$ |
| $m$ | $(-1817532459/1000000,-908766229/500000)$ | $(104587403/1000000,26146851/250000)$ |

## 27. Exact double roots and the thirty-two remaining root locations

Use exactly the all-world carrier $\mathscr R(x;p,v)$ of (15.4)–(15.6),
with its coefficient construction (20.1)–(20.2). In particular its
normalization is the fixed six-by-six determinant, not a primitive or
squarefree associate. Every actual off-$24$ complete world is covered
by Lemma 15.1, including singular sources, $F_0=0$, zero drift and all
specialized degree drops. The coefficients of $\alpha,\zeta$ are
exactly (16.1), and the fixed-degree identity is

$$
A_f^3K-\alpha d-\zeta=f\bigl\{
 K_4(A_f^2d^2-A_fB_fd+B_f^2-A_fC_f)
 +K_3A_f(A_fd-B_f)+K_2A_f^2\bigr\}.
\tag{27.1}
$$

Neither this identity nor the all-world carrier necessity assumes
that the specialized $d$ degrees of $f,K$ remain two and four. The
identity is used without dividing by $A_f$.

**Lemma 27.1 (The exact critical multiplicity).** At $q_i$, $x_i$ is a
root of $\mathscr R_i(x)=\mathscr R(x;p_i,v_i)$ of multiplicity exactly
two. The remaining factor

$$
Q_i(x)=\mathscr R_i(x)/(x-x_i)^2
\tag{27.2}
$$

has degree sixteen.

Here is a finite definition of $Q_i$ before using the claimed exact
divisibility. Write $\mathscr R_i=\sum_{j=0}^{18}a_jx^j$ and perform
two monic synthetic divisions:

$$
\begin{aligned}
b_{17}&=a_{18},&b_j&=a_{j+1}+x_i b_{j+1}\quad(j=16,\ldots,0),\\
c_{16}&=b_{17},&c_j&=b_{j+1}+x_i c_{j+1}\quad(j=15,\ldots,0),\\
Q_i(x)&=\sum_{j=0}^{16}c_jx^j.
\end{aligned}
\tag{27.3}
$$

For interval coefficient enclosures, first evaluate $p,v,x$ from
(26.1)–(26.2) on $K_i$, evaluate each coefficient $[x^j]\mathscr R$
in order $(p,v)$, and then apply exactly the descending recurrences
(27.3) with the enclosed $x_i$. The following deliberately coarse
open unit intervals suffice:

| $i$ | $[x^{16}]Q_i$ | $Q_i(x_i)$ |
| --- | --- | --- |
| 1 | $(4152,4154)10^{18}$ | $(7543,7545)10^{25}$ |
| 2 | $(-1912,-1911)10^{16}$ | $(-1338,-1337)10^{17}$ |

Proof. On a regular source neighborhood of $z_i$ the all-world identity
is
$\mathscr R(x(r,b);p(r,b),v(r,b))=0$.
At $z_i$, $dp(k)=0$ by definition, and $dv(k)=0$ because
$\det D(p,v)=0$. Differentiating this identity in the direction $k$
therefore gives

$$
\mathscr R_x(x_i;p_i,v_i)\,\kappa(z_i)=0.
\tag{27.4}
$$

The nonzero $\kappa$ in (26.7) implies $\mathscr R_x=0$ exactly.
Also $\mathscr R_i(x_i)=0$ by actual-world necessity. Hence both
synthetic remainders in (27.3) vanish, proving exact divisibility;
there is no numerical repeated-root inference. The leading-coefficient
and $Q_i(x_i)$ bounds follow by the coefficient evaluation and
synthetic recurrences just specified. They show degree eighteen for
$\mathscr R_i$, degree sixteen for $Q_i$, and that the multiplicity
at $x_i$ is exactly two. ∎

The complete Gaussian-rational centres for the sixteen roots of each
$Q_i$ follow. A row $(u,w)$ denotes $u+\mathrm i w$. Every digit belongs
to the exact rational centre.

| $i$ | Label | Real part | Imaginary part |
| --- | --- | --- | --- |
| 1 | 0 | $-17.204912539881110005435168966517538531622671160935998655784525$ | $0$ |
| 1 | 1 | $-6.802983073768707865951316192934942789250956376898648282476451$ | $0$ |
| 1 | 2 | $-5.61613902288354458466562786106590383170924856039622755808893$ | $0$ |
| 1 | 3 | $-4.663736772855965715928291773890655630268800710574345883333303$ | $0$ |
| 1 | 4 | $-3.192214458821642688222121697800181720558715689102684156124976$ | $0$ |
| 1 | 5 | $-3.183280190053983336179958104891621994191873793675236630634401$ | $0$ |
| 1 | 6 | $-2.484770248851014631709182134124342692956858535589877043486206$ | $0$ |
| 1 | 7 | $-0.41117975645377918541109012195977864573523459235718552011354$ | $0$ |
| 1 | 8 | $0.343570947835516740115217276126420708680798015352502896724819$ | $0$ |
| 1 | 9 | $0.40731123039692087494796549316233885064760309617249612055874$ | $0$ |
| 1 | 10 | $0.723726015262573419654769046589890407887009286413610994503756$ | $-0.113158669004540093770039863290588680702219718407116641041479$ |
| 1 | 11 | $0.723726015262573419654769046589890407887009286413610994503756$ | $0.113158669004540093770039863290588680702219718407116641041478$ |
| 1 | 12 | $1.925673504107261411174176685611727724250808228457016190398161$ | $0$ |
| 1 | 13 | $2.516873089789538395407096030937636043496254284256593437548574$ | $0$ |
| 1 | 14 | $32.48034958720553701414877617862974008774014564450660425743932$ | $0$ |
| 1 | 15 | $32.526854386828547340402539824989737349096410902936134109173758$ | $0$ |
| 2 | 0 | $-2.568000509276987398066592277385676880613833457712876975492048$ | $0$ |
| 2 | 1 | $-2.489213582346254040998703115653978309992649685198896857326866$ | $0$ |
| 2 | 2 | $-2.398848096540993579325818318318788845350957634321972536867227$ | $0$ |
| 2 | 3 | $-2.25376330935195395140302889973730079455225641322784439647741$ | $0$ |
| 2 | 4 | $-2.252775740793204607208846251947533387584596161812667986665717$ | $0$ |
| 2 | 5 | $-2.184353310178111271728025273058080536458834101378295370375374$ | $0$ |
| 2 | 6 | $-0.38499495317989164002131318832906298594957433990051768506322$ | $0$ |
| 2 | 7 | $0.326907090497820223955774717126803340691185532462639816278445$ | $0$ |
| 2 | 8 | $0.49982143061345030060953466687918806432126982270502533362085$ | $0$ |
| 2 | 9 | $0.688814923200144174323568061802979306925406376378754700057885$ | $-0.099673423662482223204658511383522417083194755184880009523756$ |
| 2 | 10 | $0.688814923200144174323568061802979306925406376378754700057885$ | $0.099673423662482223204658511383522417083194755184880009523755$ |
| 2 | 11 | $1.090403006257325102335291532501916287741031481071114143395378$ | $0$ |
| 2 | 12 | $1.227258007013282484865144707446261495108078963610857708422573$ | $0$ |
| 2 | 13 | $1.309019007410061783728028260320496291409098044096286368455698$ | $0$ |
| 2 | 14 | $2.155439292164872086956791732010645428122210978027988998411327$ | $0$ |
| 2 | 15 | $2.831373015960780199190057215891874303274860371529190515411766$ | $0$ |

For each centre $c_{ij}$ let $B_{ij}$ be the closed complex rectangle
of component radius $\rho=10^{-18}$. Extend (26.4) to complex
rectangles by representing real and imaginary intervals separately;
complex multiplication uses
$(a+\mathrm ib)(c+\mathrm id)=(ac-bd)+\mathrm i(ad+bc)$ with those real
interval operations. Complex polynomial evaluation is descending
Horner, starting with zero; derivative coefficients are formed from
the real coefficient intervals by multiplication by their positive
integer indices.

Let $\mathcal D_{ij}$ be the resulting rectangle enclosure of
$Q_i'(c_{ij})$, and let $\jmath_{ij}$ be its exact complex midpoint.
Define the Gaussian rational

$$
\gamma_{ij}=\frac{\overline{\jmath_{ij}}}{|\jmath_{ij}|^2}.
\tag{27.5}
$$

The midpoint is nonzero for every row. It is formed before enclosing
$\gamma_{ij}$ on the grid (26.4). For a complex rectangle
$Z=Z_R+\mathrm iZ_I$ put
$\|Z\|_{\max}=\max(|Z_R|_{\max},|Z_I|_{\max})$ and
$\nu(Z)=|Z_R|_{\max}+|Z_I|_{\max}$, where
$|[l,u]|_{\max}=\max(|l|,|u|)$. Form the exact rational upper bounds

$$
\begin{gathered}
\epsilon_{ij}=\|\gamma_{ij}Q_i(c_{ij})\|_{\max},\qquad
\omega_{ij}=\nu\bigl(1-\gamma_{ij}Q_i'(B_{ij})\bigr),\\
\text{using the interval coefficient enclosures (27.3) in both expressions.}
\end{gathered}
\tag{27.6}
$$

This defines each entry without storing a choice of a numerical
inverse. The bounds below apply to every one of the sixteen labels
in the indicated row, with no omitted complex or negative root.

| $i$ | Labels | Upper bound for $\epsilon_{ij}$ | Upper bound for $\omega_{ij}$ |
| --- | --- | --- | --- |
| 1 | $0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15$ | $6\,10^{-40}$ | $2\,10^{-13}$ |
| 2 | $0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15$ | $4\,10^{-38}$ | $8\,10^{-10}$ |

In particular the weaker common bounds
$\epsilon_{ij}<10^{-37}$, $\omega_{ij}<10^{-8}$ hold, and

$$
\epsilon_{ij}+\omega_{ij}\rho<\rho.
\tag{27.7}
$$

**Lemma 27.2 (Complete root and multiplicity budgets).** Each $B_{ij}$
contains exactly one root of $Q_i$, and that root is simple. The boxes
are pairwise disjoint for fixed $i$ and avoid $x_i$. The full budgets
for $\mathscr R_i$, with multiplicity, are

| $i$ | Negative simple | Other positive simple | Critical positive multiplicity | Nonreal simple | Total degree |
| --- | --- | --- | --- | --- | --- |
| 1 | 8 | 6 | 2 | 2 | 18 |
| 2 | 7 | 7 | 2 | 2 | 18 |

There are seventeen distinct complex root locations for each carrier,
seven and eight positive locations respectively, and no zero root.

Proof. Apply the finite interval rules (26.4), (27.3), (27.5)–(27.6)
to every literal centre in the table. Their upper endpoints give the
two bound rows. All comparisons are rational: coefficient construction
is (15.4), (20.1)–(20.2); midpoint and conjugate division are rational;
and absolute values use endpoint maxima. Thus these rules specify
all finite input data and all comparisons in (27.7).

For fixed exact $Q_i$, the map $z\mapsto z-\gamma_{ij}Q_i(z)$ has
operator bound at most $\omega_{ij}$ in the real maximum norm: complex
multiplication by $u+\mathrm iv$ has that operator norm $|u|+|v|$.
The derivative estimate on the convex rectangle and (27.7) make the
map a strict contraction into the same rectangle. Its fixed point
is a root, and $\gamma_{ij}\ne0$. At this root,
$\nu(1-\gamma_{ij}Q_i')<1$ excludes $Q_i'=0$, proving simplicity.

The centre table gives, for every two different labels, a real or
imaginary coordinate separation greater than $2\rho$. It also separates
every real-centred box from zero and from the corresponding $x_i$
interval in Section 26. At $i=1$ precisely labels $10,11$ are nonreal;
at $i=2$ they are $9,10$. Their imaginary intervals exclude zero.
For a real centre the box is invariant under conjugation. The real
coefficients and uniqueness make its root real. The other real boxes
have the indicated strict signs. There are sixteen distinct simple
roots of a degree-sixteen $Q_i$, so these exhaust it. Adding the exact
double root gives the budgets. In particular no unlisted finite root,
root at zero, higher multiplicity or missing large root is possible. ∎

## 28. All fifteen positive locations and their forced lifts

For clarity, the late-node reconstruction used here is precisely
(15.1)–(15.3), with the drift forced by (16.3). At a possible positive
$x$ at a fixed off-$24$ base form

$$
\begin{gathered}
d=-\zeta(x,p,v)/\alpha(x,p,v),\\
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\quad
H_2=4h_3-6h_4+4h_5-h_6,\\
H_7=-h_3+4h_4-6h_5+4h_6,\quad
B_0=294/5-2d-H_2,\quad C_0=d^2+B_0^2,\\
U=(-dH_0+B_0H_2)/C_0,\quad b=(U-1)/2,\quad
j=U(24-d)/H_1,\quad r=xU-j,\\
m=d+(3+2x)H_7.
\end{gathered}
\tag{28.1}
$$

These local $B_0,C_0$ are those of (15.1). They are not the source
numerators $\bar C_k$. Let $H(s)$ be the unique degree-at-most-three
interpolant of $h_3,h_4,h_5,h_6$ at the fixed nodes $3,4,5,6$.
At an actual lift $g(s)=H(s)/U$, with the same drift $d$.

For a positive simple-root label use the real interval
$I_{ij}=[c_{ij}-\rho,c_{ij}+\rho]$. For the critical label, written
$*$, use the interval enclosure of $x_i=N/(bU)$ on $K_i$. In both
cases use the enclosures of $p_i,v_i$ on $K_i$, rather than the much
wider displayed response intervals. Evaluate (28.1) in its displayed
order with (26.4), evaluating $\alpha,\zeta$ by the polynomial rule
in order $(x,p,v)$ before the drift quotient.

The following table gives all fifteen lift locations. In its last
four columns each entry $(L,U)$ means the open enclosure
$(L,U)/10^6$, including both entire endpoint calculations. The
$\alpha$ column instead gives its signed interval with the explicitly
printed multiplier.

| $i$ | Label | $\alpha$ | $H_1$ | $C_0$ | $d$ | $m$ |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | $*$ | $(4153,4156)\,10^{21}$ | $(-624306967,-624306964)$ | $(676544044877,676544044880)$ | $(608479527,608479530)$ | $(-1817532460,-1817532457)$ |
| 1 | $8$ | $(-6773,-6770)\,10^{15}$ | $(-690321401,-690321398)$ | $(30003494795,30003494799)$ | $(-171728037,-171728034)$ | $(1149833291,1149833294)$ |
| 1 | $9$ | $(-2024,-2021)\,10^{17}$ | $(502203171,502203174)$ | $(197275971364,197275971368)$ | $(-314874780,-314874777)$ | $(682252559,682252562)$ |
| 1 | $12$ | $(7762,7765)\,10^{29}$ | $(12686736,12686739)$ | $(115817032841,115817032844)$ | $(181785729,181785732)$ | $(-2078928511,-2078928508)$ |
| 1 | $13$ | $(6193,6196)\,10^{32}$ | $(31043569,31043572)$ | $(63693397588,63693397591)$ | $(131937694,131937697)$ | $(-2253748524,-2253748521)$ |
| 1 | $14$ | $(-2551,-2548)\,10^{62}$ | $(-18094,-18091)$ | $(656203596,656203599)$ | $(24451634,24451637)$ | $(-3160837724,-3160837721)$ |
| 1 | $15$ | $(-2680,-2677)\,10^{62}$ | $(-11685,-11682)$ | $(656055115,656055118)$ | $(24442468,24442471)$ | $(-3161112356,-3161112353)$ |
| 2 | $*$ | $(-6877,-6874)\,10^{19}$ | $(-10289394,-10289391)$ | $(950542872,950542875)$ | $(30805703,30805706)$ | $(104587402,104587405)$ |
| 2 | $7$ | $(-1623,-1620)\,10^{12}$ | $(-30254268,-30254265)$ | $(219551203,219551206)$ | $(14637470,14637473)$ | $(237753213,237753216)$ |
| 2 | $8$ | $(-7994,-7991)\,10^{12}$ | $(49270209,49270212)$ | $(47583520,47583523)$ | $(-2969575,-2969572)$ | $(210258863,210258866)$ |
| 2 | $11$ | $(-4238,-4235)\,10^{17}$ | $(-12822106,-12822103)$ | $(1667073635,1667073638)$ | $(39344668,39344671)$ | $(98421693,98421696)$ |
| 2 | $12$ | $(-7932,-7929)\,10^{17}$ | $(2071484,2071487)$ | $(1451118491,1451118494)$ | $(36144586,36144589)$ | $(85887671,85887674)$ |
| 2 | $13$ | $(-5521,-5518)\,10^{17}$ | $(6619010,6619013)$ | $(1322546117,1322546121)$ | $(34519694,34519697)$ | $(81552189,81552192)$ |
| 2 | $14$ | $(-1248,-1245)\,10^{27}$ | $(-498673,-498670)$ | $(661518618,661518621)$ | $(25245411,25245414)$ | $(84886967,84886970)$ |
| 2 | $15$ | $(-6251,-6248)\,10^{30}$ | $(1468028,1468031)$ | $(613736823,613736826)$ | $(23360645,23360648)$ | $(74280366,74280369)$ |

Every entry has the common strict guards

$$
|\alpha|>\frac{16}{10}10^{15},\qquad
|H_1|>\frac{11}{1000},\qquad C_0>\frac{95}{2}.
\tag{28.2}
$$

The weaker bounds $|\alpha|>10^{15}$, $|H_1|>1/100$, $C_0>47$ also
suffice for all arguments. The positive $x$ intervals guard division
by $x,x+1,x+2$. In particular every quotient in (28.1) is guarded
before use. The common bounds include both critical roots; the
critical multiplicity does not introduce an extra drift.

Here is the full source filtering table. The thirteen noncritical
rows use the exact rational open enclosures printed below; there is
no rounding convention attached to these $b,r$ entries. The critical
rows enclose the exact critical source by Lemma 26.1; they do not
assert containment of the independent interval lift in that tiny cube.

| $i$ | Label | $b$ | $r$ | Strict-source conclusion |
| --- | --- | --- | --- | --- |
| 1 | $*$ | $\widehat b_1+[-h,h]$ | $\widehat r_1+[-h,h]$ | actual $\mathcal W_1^J$ |
| 1 | 8 | $(-988022267/100000000,-494011133/50000000)$ | $(-73529537/6250000,-1176472591/100000000)$ | $b<0$ |
| 1 | 9 | $(-209901761/100000000,-655943/312500)$ | $(42768129/50000000,85536259/100000000)$ | $b<0$ |
| 1 | 12 | $(-5879127/12500000,-9406603/20000000)$ | $(85228031/100000000,332922/390625)$ | $b<0$ |
| 1 | 13 | $(-10467881/20000000,-13084851/25000000)$ | $(-28044063/100000000,-14022031/50000000)$ | $b<0$ |
| 1 | 14 | $(-35203919/100000000,-17601959/50000000)$ | $(55616403/25000000,222465613/100000000)$ | $b<0$ |
| 1 | 15 | $(-17625021/50000000,-35250041/100000000)$ | $(-78831603/50000000,-31532641/20000000)$ | $b<0$ |
| 2 | $*$ | $\widehat b_2+[-h,h]$ | $\widehat r_2+[-h,h]$ | actual $\mathcal W_2^J$ |
| 2 | 7 | $(135377069/25000000,541508277/100000000)$ | $(94104309/12500000,752834473/100000000)$ | $r>1$ |
| 2 | 8 | $(-38743481/6250000,-123979139/20000000)$ | $(1693997/3125000,10841581/20000000)$ | $b<0$ |
| 2 | 11 | $(-8864417/100000000,-277013/3125000)$ | $(-874811/10000000,-8748109/100000000)$ | $b<0$ |
| 2 | 12 | $(-21964373/50000000,-8785749/20000000)$ | $(86090401/100000000,86090403/100000000)$ | $b<0$ |
| 2 | 13 | $(-55258217/100000000,-6907277/12500000)$ | $(-3810017/12500000,-15240067/50000000)$ | $b<0$ |
| 2 | 14 | $(-15524661/100000000,-776233/5000000)$ | $(-4716501/20000000,-2947813/12500000)$ | $b<0$ |
| 2 | 15 | $(-669281/2500000,-26771239/100000000)$ | $(22261099/20000000,13913187/12500000)$ | $b<0$ |

**Lemma 28.1 (Exhaustive positive-root filtering).** Every noncritical
positive location fails the strict source conditions, while at $x_i$
there is at most one possible actual complete world.

Proof. Polynomial evaluation of (16.1), followed by (28.1) on the
specified intervals, gives (28.2), the first table and all
noncritical rows of the second table. Its critical source rows follow
from Lemma 26.1. The integer pairs
in the first table are outward enclosures with strict margin. For
the second table the endpoint comparisons are the displayed rational
comparisons themselves. Together with the finite definitions of the
carrier, $\alpha,\zeta$ and the literal centres, these are complete
source-specific finite inequalities, requiring no additional
coefficient or root files.

For necessity, (27.1) at any actual common root $f=K=0$ gives
$\alpha d+\zeta=0$, even if $A_f=0$. At every positive location
(28.2) forces its one drift. The fixed-node interpolation and the
zero-safe reconstruction of Section 15 then force its $U,b,j,r$;
these implications do not presume that an eliminant root is actual.
At $i=1$, all six other positive roots have $b<0$. At $i=2$, six
other positive roots have $b<0$ and label $7$ has $r>1$.
All these violations have a strict margin from the closed admissible
conditions $b\ge0$, $0\le r\le1$.

At $x_i$ the same drift and source uniqueness applies. The strict
critical lift has $U>1$ and its whole polynomial is $H/U$, so there
is at most one complete world there. No division by $d$, $d-24$,
$\Lambda$, a gain sample, a gain leading coefficient or a gain-root
difference has been introduced in this filter. ∎

## 29. Proof of the singleton inventories and their precise scope

Proof of Theorem 25.1. Fix either $i$. The bounds in Section 26 place
$p_i$ strictly below zero and hence off $24$. If $W\in C(q_i)$ is
any actual complete world, its $x=n/U$ is positive. By Lemma 15.1,
$\mathscr R_i(x)=0$, including when the source is singular or any
drift or gain degree has dropped. Lemma 27.2 exhausts all roots and
Lemma 28.1 rejects every positive location except $x_i$. At $x_i$,
(27.1), (28.2) force the unique drift, and (15.1) forces the unique
source and whole gain. This gives at most one complete world.
Lemma 26.1 and (23.8) already supply the actual $\mathcal W_i^J$ in
that child. Thus (25.2) holds. Its regularity also proves that there
is no actual singular companion in either inventory. ∎

The retained domain is all of Definition 1.1: strict $0<r<1$, $b>0$,
any nonzero entire real gain of degree at most three, and its own
fixed real drift. The acquired actions are $J,M,J,M,M,M$ at original
clocks $0,\ldots,6$, with the original alternatives at clock seven.
Nothing has required exact cubic degree, positive gain, nonzero gain
samples, distinct gain roots or nonzero drift. In particular a double
carrier root is a single possible world, rather than two choices of a
gain polynomial. The lift uses the whole interpolant.

The fixed Sylvester construction and (27.1) retain all specialized
leading-degree drops. Lemma 15.1 supplies the removed $F_0=0$ factor
by its regular density argument and covers $\Lambda=0$ by the
undivided full-parent continuation. Thus these strata are retained
before filtering; they are not inferred absent from the regular
source boxes alone. The numerical root budget is eighteen with
multiplicity, not a count of eighteen actual worlds.

At either exact base there are zero distinct actual $M$ pairs.
Accordingly any set of tangent tests indexed by such pairs is empty;
no pair determinant or $J$ jet is needed for (25.2). The targets
remain exactly the algebraic worlds (23.8).

## 30. Complete-child concentration and the strict diagonal exclusion

**Lemma 30.1 (All-world concentration at each exact base).** If actual
complete worlds $W_n$ have bases $\operatorname{base}(W_n)\to q_i$, then
$W_n\to\mathcal W_i^J$ as complete worlds.

Proof. Since $q_i$ is off $24$, all sufficiently late bases are off
$24$. The leading coefficient of $\mathscr R_i$ is nonzero by
Lemma 27.1, and its constant coefficient is nonzero by the complete
root budget. Coefficients vary polynomially with $(p,v)$. Thus on
some base neighborhood all coefficients have absolute value at most
$M$, while the leading and constant coefficients have absolute
values at least $\varepsilon_{18}>0$ and $\varepsilon_0>0$.
Cauchy's elementary root estimate, applied also to the reversed
polynomial, gives for every nonzero root there

$$
\frac1{1+M/\varepsilon_0}\le |x|
 \le1+M/\varepsilon_{18}.
\tag{30.1}
$$

For completeness, the upper estimate follows because for
$|x|>1+M/\varepsilon_{18}$ the leading term strictly exceeds the
sum of the others, using the finite geometric sum. The reversed
polynomial gives the lower estimate. Hence the positive carrier
coordinates of any such actual sequence have convergent
subsequences with strictly positive limits. Polynomial continuity
places each limit among the positive locations tabulated for its
target: seven locations for $i=1$ and eight for $i=2$.

At every such location $\alpha,H_1,C_0$ are units by (28.2), so the
forced expressions (28.1) are continuous on a neighborhood of that
location and base. Along an actual subsequence its drift and source
must equal these expressions. A noncritical limit would therefore
have one of the strictly rejected source coordinates in the second
Section 28 table. This is incompatible with $b_n>0$, $0<r_n<1$,
whose finite limits satisfy $b\ge0$, $0\le r\le1$.
Thus every subsequential carrier limit is $x_i$, forcing $x_n\to x_i$.

The same continuous forced lift now gives
$(r_n,b_n,d_n)\to(\rho_i,\beta_i,d_i^J)$. At this limit $U>1$.
The interpolant of the four late samples depends linearly on those
samples, and $g_n=H_n/U_n$ for the entire polynomial. Hence all four
gain coefficients converge to those of $g_i^J$. This also rules out
unbounded drift, source or gain coefficients along such a sequence;
no compactness of the whole parent was assumed. ∎

Proof of Theorem 25.2. The evaluated determinant $\mu(z_i)>0$ in
(26.7) and the inverse-function theorem give a parent neighborhood
$N_i$ of $\mathcal W_i^J$ on which $(p,m)$ is injective. It may be
chosen in its regular source chart. Lemma 30.1 puts every entire
child over sufficiently nearby bases inside $N_i$: otherwise choose
bases within $1/n$ of $q_i$ and actual worlds outside $N_i$, contrary
to their complete-world convergence to its interior point.
Choose such an open base neighborhood $V_i$ off $24$. Two worlds in
a child over $V_i$ with equal $m$ have equal $(p,m)$ in $N_i$, so
they coincide. This proves entire-child $M$ injectivity. It does not
assert global injectivity of $(p,m)$ or singleton cardinality for
every nearby child. ∎

Proof of Theorem 25.3. Suppose both selected distinct $J$ endpoints
of a sequence (1.2) converge to a strict complete parent world $Z$.
If $\operatorname{rank}d(p,v,a)_Z=2$, some two output coordinates
have invertible differential on the two-dimensional parent. The
inverse-function theorem makes that submap, and hence $(p,v,a)$,
injective on a neighborhood of $Z$. Both endpoints eventually lie
there and have the same $(p,v,a)$, contradicting their distinctness.

The full-parent classification (24.3), including its separate
singular-source assertion, leaves only
$Z=\mathcal W_1^J$ or $Z=\mathcal W_2^J$. Their common bases then
tend to $q_i$. They eventually lie in $V_i$ of Theorem 25.2, where
no distinct equal-$M$ pair exists anywhere in the entire child.
This contradicts the independently selected $M$ pair of (1.2).
No relation between the two terminal common values, no disjointness
between the pairs, and no convergence of the $M$ endpoints was used. ∎

The target-specific contributions are the two complete inventories,
their exact multiplicity and root covers, all strict companion
rejections, and the evaluated $(p,m)$ differential units that yield
these local exclusions. The full-parent and whole-gain correspondence
is O, Theorem 2.1, in (2.1)–(2.7); the all-world carrier and linear
drift identity are Lemma 15.1 and (16.2); the full augmented-$J$
critical classification is Theorem 24.1. These mechanisms are reused.
Fixed-node interpolation is the classical formula of J.-P. Berrut
and L. N. Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review
46 (2004), 501–517, §2, equations (2.1)–(2.2),
[author-hosted primary text](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf),
[DOI 10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
Only interpolation is attributed to that reference, not these
source-specific inventories.

The global question (1.2) remains unresolved. The results exclude
these two exact bases, some unspecified open neighborhoods of them,
and every strict complete-world $J$-diagonal limiting route. Reusing
SIII, Theorem 7.1, Corollaries 8.1–8.3 and Proposition 9.1, every
original joint base lies in the compact ambient $K$ of SIII, (8.3),
separated from $p=24$, and every actual companion above such a base
has bounded original source coordinates, drift and all four whole-gain
coefficients, including worlds unused by either selected pair. One
endpoint per selected pair can be chosen in SIII's compact strict
anchor set; this gives no uniform interior margin for all endpoints
or companions. The remaining analysis concerns actual separated strict
$J/M$ incidences over the remaining part of $K$ and finite
source-boundary or interior limiting routes not already excluded under
their owning suppliers' hypotheses, as in SIII, Definition 9.2.
The pairs remain independently chosen, may overlap and may have
different common terminal values. Boundary limits are necessary
limiting configurations, not actual collisions. Auxiliary chart ratios
or slopes may diverge at a finite boundary without an unbounded
original source or base regime. The bounds do not assert closedness
of the strict incidence loci or properness of their projections,
and no global incidence classification is supplied here.

## 追加锚（本行以下为增补区）
