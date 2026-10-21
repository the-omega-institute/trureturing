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
