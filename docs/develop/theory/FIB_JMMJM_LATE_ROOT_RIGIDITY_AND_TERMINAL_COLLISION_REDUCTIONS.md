# FIB JMMJM Late-Root Rigidity and Terminal Collision Reductions

## 1. Complete worlds on one literal ancestor

A complete world is $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and $\delta\in\mathbb R$.
The source may be nonsymmetric. All gain signs, degree drops, real
root patterns and repeated roots are initially allowed. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
$$

The reading at original clock $i$ is
$g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts.
Every atom is immediately read on one unresettable, uncopyable
trajectory. A chronological word $EF$ means first $E$ and its reading,
then $F$ and its reading, with cumulative matrix $FEA$. No clock is
renumbered and no intermediate reading is omitted. A deterministic
policy may depend on the entire actual history.

For arbitrary $D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, fix the one
literal history

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
                 M,D_0+312\lambda/5,J,Y,M,z).                    \tag{1.1}
$$

All worlds considered together must satisfy all six readings of this
same $JMMJM$ ancestor. In particular, $D_0$ is a history parameter,
not a drift promise. Normalize by

$$
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
\widehat Y=(Y-D_0)/\lambda,\qquad \widehat z=(z-D_0)/\lambda.
                                                                    \tag{1.2}
$$

The ancestor matrices and readings are

$$
\begin{gathered}
(A_0,A_1,A_2,A_3,A_4,A_5)=(I,J,L,J+L,C,Q),\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
C=J(J+L)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix},\\
(c_0,c_1,c_2,c_3,c_4,c_5)=(0,24,48,312/5,\widehat Y,\widehat z).
\end{gathered}                                                       \tag{1.3}
$$

Membership in the actual fiber $\mathcal F(H)$ means

$$
f(i)\operatorname{tr}(A_iP)+d=c_i\qquad(0\le i\le5).           \tag{1.4}
$$

Every trace factor is strictly positive: every $A_i$ is nonzero and
entrywise nonnegative, and $P$ is strictly entrywise positive.
The invertible affine change of every response
$w\mapsto(w-D_0)/\lambda$ preserves response equalities, actual
children and complete-world distinction for both signs of $\lambda$.
It also preserves each predicate in the recursion below, by induction
using the bijection of real response values for each action.
The original target is recovered by

$$
g=\lambda f,\qquad \delta=D_0+\lambda d,                     \tag{1.5}
$$

with the same $P$.

For a known candidate set $K\subseteq\mathcal F(H')$ at a literal
history $H'$, define

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists w\in\mathbb R:
 L_r(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}                                                       \tag{1.6}
$$

A child retains the same fixed worlds and their entire common
ancestor. Counterfactual response functions are used in proofs;
they are not extra observations. In normalized coordinates write

$$
v_E(W)=d+f(6)\operatorname{tr}(EQP),\qquad
r_{EF}(W)=d+f(7)\operatorname{tr}(FEQP),\quad E,F\in\{J,M\}.    \tag{1.7}
$$

Their raw values are $D_0+\lambda v_E$ and
$D_0+\lambda r_{EF}$, respectively.

Write the source as

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix}.
$$

Its legality is equivalent to

$$
0<r<1,\quad u>0,\quad v>0,\quad uv=r(1-r)\le1/4.             \tag{1.8}
$$

Indeed zero determinant and nonzero trace give rank one. Direct trace
multiplication gives, without assuming $u=v$,

$$
\begin{aligned}
j&=\operatorname{tr}(JP)=u+v,&
\ell&=\operatorname{tr}(LP)=1+u,\\
\operatorname{tr}((J+L)P)&=j+\ell,&
\operatorname{tr}(CP)&=1+r+u+v,\\
\operatorname{tr}(QP)&=2-r+3u+v.&
\end{aligned}                                                       \tag{1.9}
$$

The model, normalization, recursion and literal ancestor are those of
[FIB self-calibrating relation mathematics VII, Definitions 1.1–1.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md).
The source coordinates retain the full positive nonsymmetric class.

## 2. The ancestor-root exclusion used below

**Lemma 2.1.** No legal world on (1.1) has three distinct gain roots
among original clocks zero through five.

This is Theorem 3.1 of
*FIB JMMJM Whole-Class Affine Decoders*.
Its complete elementary proof is included here.

**Proof.** A nonzero polynomial of degree at most three has at most
three distinct roots, by successive division by their linear factors.
At every sampled root, (1.4) says $c_i=d$. The four readings
$0,24,48,312/5$ are distinct. Thus three ancestor roots would be
exactly $q,4,5$ for one $q\in\{0,1,2,3\}$, and necessarily

$$
d=c_q=\widehat Y=\widehat z,\qquad
f(T)=a(T-q)(T-4)(T-5),\quad a\ne0.                            \tag{2.1}
$$

If $q=0$, then $d=0$ and the gains at one, two and three are
$12a,12a,6a$. Equations (1.4) require

$$
j=2/a,\quad \ell=4/a,\quad j+\ell=52/(5a).
$$

The first two sum to $6/a$, a contradiction.

If $q=1$, the initial reading gives $-20a=-24$, hence $a=6/5$.
The gains at two and three are $36/5,24/5$. Therefore

$$
\ell=10/3,\quad j+\ell=8,\quad j=14/3,\quad u=v=7/3,
$$

contrary to $uv\le1/4$.

If $q=2$, then $d=48$ and $-40a=-48$ gives $a=6/5$.
The gains at one and three are $-72/5,12/5$, so

$$
j=5/3,\quad j+\ell=6,\quad \ell=13/3,\quad
u=10/3,\quad v=-5/3,
$$

contrary to positivity.

If $q=3$, then $d=312/5$ and $-60a=-312/5$ gives $a=26/25$.
The gains at one and two are $-624/25,-156/25$, giving

$$
j=20/13,\quad \ell=30/13,\quad u=17/13,\quad v=3/13.
$$

Now $uv=51/169>1/4$, since $204>169$. These exhaust the possibilities.
Three distinct roots already force the cubic (2.1); no lower-degree
or repeated-root alternative with those three roots is omitted.
Both late readings are retained as the common drift in every case. ∎

## 3. Rigidity of the entire late-double-root class

Define the known-candidate root class

$$
\mathcal Z_{45}=\{W\in\mathcal F(H): f(4)=f(5)=0\}.            \tag{3.1}
$$

**Theorem 3.1.** If $\widehat Y\ne\widehat z$, this class is empty.
If it is nonempty, it has one common normalized drift
$d=\widehat Y=\widehat z>0$ and one common gain

$$
f(T)=-\frac d{20}(T-4)(T-5)(1+\mu T).                         \tag{3.2}
$$

The parameter $\mu$ is unique among legal candidates and satisfies
$\mu<-1/3$ or $\mu>0$. Thus the gain is exactly cubic, with distinct
simple roots $4,5,\rho$, where $\rho=-1/\mu<3$ and
$\rho\notin\{0,1,2\}$. The off-diagonal source entries are fixed;
there are at most two complete worlds. The sixth $J$ response is
injective on the whole class and every known subset, and recovers the
complete target with one further immediate read. In particular
$\neg L_1(\mathcal Z_{45},H)$ and $\neg L_2(\mathcal Z_{45},H)$.

**Proof, forced form and nonzero denominators.** The roots at four
and five make their actual readings equal to $d$. Lemma 2.1 excludes
any root at zero, one, two or three. Positivity of all six traces
therefore gives

$$
d\notin\{0,24,48,312/5\},\qquad f(0)f(1)f(2)f(3)\ne0.        \tag{3.3}
$$

Factor $f(T)=(T-4)(T-5)(a+bT)$. This includes a possible quadratic.
The initial equation is $20a=-d$, so $a\ne0$. Set $\mu=b/a$ to
obtain (3.2). In particular $1+\mu$, $1+2\mu$ and $1+3\mu$
are nonzero. The next three ancestor equations give

$$
\begin{aligned}
j&=\frac{5(d-24)}{3d(1+\mu)},\\
\ell&=\frac{10(d-48)}{3d(1+2\mu)},\\
j+\ell&=\frac{10(d-312/5)}{d(1+3\mu)}.
\end{aligned}                                                       \tag{3.4}
$$

All divisions so far are by the nonzero quantities just established.

**Proof, the gain quadratic.** Equating the sum of the first two
expressions in (3.4) to the third gives

$$
\begin{aligned}
0={}&(d-24)(1+2\mu)(1+3\mu)
 +2(d-48)(1+\mu)(1+3\mu)\\
 &-6(d-312/5)(1+\mu)(1+2\mu).
\end{aligned}                                                       \tag{3.5}
$$

Its coefficients at powers zero, one and two are respectively
$(1272-15d)/5$, $(3096-25d)/5$ and $1584/5$. Thus

$$
Q_d(\mu)=1584\mu^2+(3096-25d)\mu+1272-15d=0.                 \tag{3.6}
$$

Put

$$
K=66\mu^2+129\mu+53,\qquad h=25\mu+15.
$$

Then $Q_d=24K-dh$ and

$$
Q_d(-3/5)=-384/25.                                           \tag{3.7}
$$

Consequently $h\ne0$ at a root of $Q_d$. Since $d\ne0$,
also $K\ne0$, and $d=24K/h$. The identities

$$
K-h=2(\mu+1)(33\mu+19),\qquad
K-2h=(2\mu+1)(33\mu+23)
$$

now turn (3.4) into

$$
\begin{aligned}
j&=\frac{10(33\mu+19)}{3K},&
\ell&=\frac{10(33\mu+23)}{3K},\\
u&=\ell-1=\frac{-198\mu^2-57\mu+71}{3K},&
v&=j-\ell+1=\frac{198\mu^2+387\mu+119}{3K}
             =1-\frac{40}{3K}.
\end{aligned}                                                       \tag{3.8}
$$

The canceled factors are only $1+\mu$ and $1+2\mu$, already
nonzero. Here $h$ is an auxiliary linear polynomial, not a fixed
shape promise.

**Proof, only one quadratic branch can be legal.** Since $Q_d$ has
positive leading coefficient and is negative at $-3/5$, it has two
distinct real roots

$$
\mu_-<-3/5<\mu_+ .                                           \tag{3.9}
$$

At $\mu_-$, the numerator $33\mu+19$ in $j$ is negative.
Thus $j>0$ forces $K<0$. Also $h<0$, so $d=24K/h>0$.
The further condition $\ell>0$ forces $\mu_-<-23/33$.
The point $-23/33$ lies strictly between the two roots, so

$$
Q_d(-23/33)=\frac{80}{33}(d-48)<0.
$$

A legal lower root therefore requires $d<48$.

At $\mu_+$ the numerator $33\mu+23$ is positive, so $\ell>0$
forces $K>0$. Now $h>0$, and again $d>0$. Positivity of $j$ gives
$\mu_+>-19/33$, while positivity of $v$ in (3.8) gives $K>40/3$.
For $\mu>-19/33$,

$$
K'(\mu)=132\mu+129>53>0,\qquad K(-1/2)=5<40/3.
$$

Hence $\mu_+>-1/2$. This point is strictly above $\mu_-$, so
$-1/2$ lies strictly between the roots. Thus

$$
Q_d(-1/2)=\frac52(48-d)<0,
$$

and a legal upper root requires $d>48$. For the one fixed drift
$d$, both branches cannot be legal; each branch contains only its
one quadratic root. This proves uniqueness of the legal $\mu$ and
also $d>0$. No source or gain shape has been fixed in this argument.

**Proof, the small quartic obstruction and all five coefficients.**
Define

$$
U=-198\mu^2-57\mu+71,\qquad V=198\mu^2+387\mu+119.
$$

By (3.8) and (1.8), $uv=UV/(9K^2)\le1/4$, hence
$9K^2-4UV\ge0$. Complete coefficient multiplication is

$$
\begin{array}{c|rrrrr}
 &\mu^0&\mu^1&\mu^2&\mu^3&\mu^4\\ \hline
9K^2&25281&123066&212733&153252&39204\\
4UV&33796&82776&-126252&-351648&-156816\\
9K^2-4UV&-8515&40290&338985&504900&196020
\end{array}
$$

It follows that

$$
\begin{aligned}
9K^2-4UV&=5R(\mu),\\
R(\mu)&=39204\mu^4+100980\mu^3+67797\mu^2+8058\mu-1703.
\end{aligned}                                                       \tag{3.10}
$$

For $-1/3\le\mu\le0$, put $X=-3\mu\in[0,1]$. Exactly

$$
R(-X/3)=484X^4-3740X^3+7533X^2-2686X-1703.                   \tag{3.11}
$$

Let $B_{i,4}(X)=\binom4iX^i(1-X)^{4-i}$. The complete Bernstein
identity is

$$
\begin{aligned}
R(-X/3)={}&-1703B_{0,4}(X)-\frac{4749}{2}B_{1,4}(X)
 -\frac{3581}{2}B_{2,4}(X)\\
 &-886B_{3,4}(X)-112B_{4,4}(X).
\end{aligned}                                                       \tag{3.12}
$$

For an explicit verification, if $(p_0,p_1,p_2,p_3,p_4)
=(-1703,-2686,7533,-3740,484)$, the Bernstein coefficient at index
$i$ is $\sum_{a=0}^ip_a\binom ia/\binom4a$. All five evaluations are

$$
\begin{array}{c|l|r}
i&\text{coefficient sum}&\text{value}\\ \hline
0&-1703&-1703\\
1&-1703-2686/4&-4749/2\\
2&-1703-2686/2+7533/6&-3581/2\\
3&-1703-3(2686)/4+7533/2-3740/4&-886\\
4&-1703-2686+7533-3740+484&-112
\end{array}                                                       \tag{3.13}
$$

The conversion follows directly from

$$
X^a=\sum_{i=a}^4\frac{\binom ia}{\binom4a}B_{i,4}(X):
$$

indeed $\binom4i\binom ia/\binom4a=\binom{4-a}{i-a}$,
and the sum is $X^a(X+1-X)^{4-a}$. Thus (3.13) proves every
coefficient in (3.12) from (3.11), without an omitted array.
The Bernstein terms are nonnegative on $[0,1]$ and sum to one.
Every displayed coefficient is strictly negative. The endpoints
are included: the value is $-1703$ at zero and $-112$ at one.
Therefore $R(\mu)<0$ throughout the closed interval $[-1/3,0]$,
contradicting (3.10) and $9K^2-4UV\ge0$.

Consequently $\mu<-1/3$ or $\mu>0$. In particular $b=a\mu\ne0$,
so the gain is exactly cubic. Its third root is negative when
$\mu>0$, and is in $(0,3)$ when $\mu<-1/3$. It cannot be zero;
Lemma 2.1 excludes one and two. This root is distinct from four
and five, so all three roots are simple. The initially permitted
quadratic, repeated-root and later-third-root cases in this class
have been excluded by deductions, rather than additional promises.
In particular

$$
f(6)=-\frac d{10}(1+6\mu)\ne0,\qquad
f(7)=-\frac{3d}{10}(1+7\mu)\ne0.                             \tag{3.14}
$$

They have the same sign. Also $f(3)=-d(1+3\mu)/10$ has this sign.
The clock-three equation therefore gives $d<312/5$ when $\mu<0$
and $d>312/5$ when $\mu>0$. These are necessary conditions on
$\mathcal Z_{45}$ alone.

**Proof, all sources and the full-target inverse.** The unique $d$
and $\mu$ fix $u,v$ by (3.8). The only possible diagonal parameters are

$$
r_\pm=\frac{1\pm\sqrt{1-4uv}}2.                              \tag{3.15}
$$

There are no candidates if the legality conditions fail. When a
candidate exists, $0<uv\le1/4$, so both displayed values are in
$(0,1)$; they coincide if $uv=1/4$. Every remaining ancestor
equation still applies. At clocks four and five it is exactly the
zero-gain equation with reading $d$, so it imposes no further
restriction on $r$. There are at most two sources and hence at
most two complete worlds.

Direct multiplication gives

$$
JQ=\begin{pmatrix}3&2\\1&1\end{pmatrix},\qquad
\operatorname{tr}(JQP)=1+2r+u+2v.                            \tag{3.16}
$$

The actual sixth $J$ response is
$d+f(6)(1+2r+u+2v)$, with nonzero slope $2f(6)$ in $r$.
Given its raw reading $w$, put $s_6=(w-D_0)/\lambda$ and recover

$$
r=\frac12\left(\frac{s_6-d}{f(6)}-1-u-2v\right),\qquad
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix}.                     \tag{3.17}
$$

Equations (3.2) and (1.5) return the full $g,\delta$.
The divisions are by $\lambda\ne0$ and the proved nonzero $f(6)$.
The known ancestor and root class determine the unique legal
quadratic root; its existence at an actual candidate follows from
that candidate. Empty classes are unreachable; a known singleton
may stop already. The same $J$ read and inverse work on every known
subset, without imposing a cardinality premise. At most seven total
readings are used, at the original clocks zero through six.

For explicit recursion quantifiers, for this fixed first action $J$
and every real raw response $w$, the actual child

$$
K_w=K\cap\mathcal F(H,J,w),\qquad H_w=(H,J,w)
$$

has at most one world for every known $K\subseteq\mathcal Z_{45}$.
Thus $L_0(K_w,H_w)$ and $L_1(K_w,H_w)$ both fail for every $w$.
The $J$ action conjunct in (1.6) consequently fails for both
$L_1(K,H)$ and $L_2(K,H)$. This includes empty and singleton sets,
whose cardinality clauses already fail. ∎

## 4. An exact sharp two-world example

**Theorem 4.1.** The bound two in Theorem 3.1 is sharp. On the
normalized ancestor $D_0=0$, $\lambda=1$, $Y=z=178/3$, the entire
class $\mathcal Z_{45}$ consists of the following two worlds:

$$
\begin{gathered}
d=\delta=178/3,\qquad
f(T)=g(T)=-\frac{89}{30}(T-4)(T-5)(1-3T/8),\\
u=413/267,\quad v=11/267,\quad
r_\pm=\frac{267\pm\sqrt{53117}}{534},\qquad
P_\pm=\begin{pmatrix}r_\pm&413/267\\11/267&1-r_\pm\end{pmatrix}.
\end{gathered}                                                       \tag{4.1}
$$

**Proof.** Since $0<53117<267^2=71289$,
$0<r_-<r_+<1$. Moreover

$$
r_\pm(1-r_\pm)
=\frac{71289-53117}{4\cdot71289}
=\frac{4543}{71289}
=\frac{413}{267}\frac{11}{267}=uv.
$$

Thus both matrices are strictly positive, rank one and trace one.
They are nonsymmetric because $413\ne11$. They are distinct because
$r_+\ne r_-$. The gain is nonzero cubic with the three distinct roots
$4,5,8/3$. The drifts and gains agree, but the complete targets differ.

For both sources the first four traces and gain samples are

$$
\begin{array}{c|c|c|c}
i&\operatorname{tr}(A_iP_\pm)&f(i)&
                  d+f(i)\operatorname{tr}(A_iP_\pm)\\ \hline
0&1&-178/3&0\\
1&424/267&-89/4&178/3-106/3=24\\
2&680/267&-89/20&178/3-34/3=48\\
3&1104/267=368/89&89/120&178/3+46/15=312/5
\end{array}                                                       \tag{4.2}
$$

Here the traces are respectively $1,j,\ell,j+\ell$ from (1.9).
At clock four the actual cumulative matrix is $C$, and at clock
five it is $Q$. The gain is zero at both, so the two remaining
actual equations, for each of the two sources, are exactly

$$
f(4)(1+r_\pm+u+v)+d=178/3,\qquad
f(5)(2-r_\pm+3u+v)+d=178/3.                                  \tag{4.3}
$$

Thus both worlds satisfy all six equations of the same entire
$JMMJM$ history. Theorem 3.1 gives at most two such worlds; these two
are therefore the whole root class on this ancestor.

Finally $f(6)=89/12$, so their sixth $J$ responses differ by

$$
2f(6)(r_+-r_-)
=\frac{89}{6}(r_+-r_-)=\frac{\sqrt{53117}}{18}\ne0.            \tag{4.4}
$$

This proves both sharpness and one-read separation. It is not an
$L_2$ witness: the fixed $J$ action separates this pair immediately. ∎

## 5. Terminal response identities and pair quantifiers

For any world set

$$
X=f(7)QP=\begin{pmatrix}a&b\\c&e\end{pmatrix}.
$$

Multiplying the two terminal atoms gives the complete table

$$
\begin{array}{c|c|c}
\text{chronological word}&FE& r_{EF}\\ \hline
JJ&I&a+e+d\\
JM&MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}&a+b+e+d\\
MJ&JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}&a+c+e+d\\
MM&M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix}&a+b+c+2e+d
\end{array}                                                       \tag{5.1}
$$

In particular the gap between terminal responses after sixth $J$ is
$b$, and the gap after sixth $M$ is $b+e$. If $f(7)\ne0$, positivity
of $QP$ makes $b,e$ nonzero and of the same sign. Consequently

$$
|b+e|>|b|>0.                                                 \tag{5.2}
$$

For completeness, the terminal reconstruction identities are

$$
b=r_{JM}-r_{JJ},\quad c=r_{MJ}-r_{JJ},\quad
e=r_{MM}-r_{MJ}-r_{JM}+r_{JJ}.                               \tag{5.3}
$$

If $e\ne0$, rank one gives $a=bc/e$ and then
$d=r_{JJ}-a-e$. If $e=0$, strict positivity of $(QP)_{22}$ forces
$f(7)=0$, so $X=0$ and every terminal response is $d$. The
reconstruction mechanism is credited in VII, equation (4.2), to
V, Theorem 7.1; (5.1)–(5.3) supply all its calculation needed here.
No unseen proof from V is required for these identities.

A two-world child has $L_1$ exactly when its two terminal responses
agree under each of the two possible next atoms. Indeed the only
response child with at least two worlds is the whole pair. Applying
the same observation one level earlier gives, for a distinct pair
$G=\{W_1,W_2\}$ on $H$,

$$
\begin{aligned}
L_2(G,H)\quad\Longleftrightarrow\quad
&v_J(W_1)=v_J(W_2),\quad v_M(W_1)=v_M(W_2),\\
&r_{EF}(W_1)=r_{EF}(W_2)\quad\text{for every }E,F\in\{J,M\}.
\end{aligned}                                                       \tag{5.4}
$$

On three-world children the terminal collision pair may depend on
the last atom. None of the following arguments replaces that
possibility by (5.4) for an arbitrarily chosen pair.

## 6. Exactly two terminal roots reduce to their proper pair

**Theorem 6.1.** Let $K=\{W_1,W_2,W_3\}$ be three pairwise distinct
fixed legal worlds, all on the one entire history (1.1). Suppose

$$
f_1(7)=f_2(7)=0,\qquad f_3(7)\ne0.
$$

Then

$$
\begin{aligned}
L_2(K,H)\quad\Longleftrightarrow\quad
&d_1=d_2,\quad v_J(W_1)=v_J(W_2),\quad v_M(W_1)=v_M(W_2)\\
\quad\Longleftrightarrow\quad &L_2(\{W_1,W_2\},H).
\end{aligned}                                                       \tag{6.1}
$$

Thus an $L_2$ triple in this pattern is not inclusion-minimal.
The statement is an unconditional reduction and does not assume
VII's pair-exclusion theorem.

**Proof.** Each terminal response of $W_i$ for $i=1,2$ is $d_i$.
For $W_3$, let $b,e$ be the entries of $X=f_3(7)QP_3$ in (5.1).
They satisfy (5.2). On either sixth branch its two terminal
responses differ. Therefore a mixed pair consisting of $W_3$ and
one zero-terminal-gain world cannot have $L_1$ at that branch:
equality with the latter's constant drift response under both last
atoms would require those two different responses to be equal.

First suppose $d_1\ne d_2$. The pair of zero worlds cannot have
$L_1$ either, because their terminal responses are different.
No response child of size at most two can consequently have $L_1$.
If $K$ had $L_2$, then for each sixth action $E\in\{J,M\}$ its
existential response child in (1.6) would have to contain all three
worlds. On that whole child, each terminal action must have a
collision. Since $d_1\ne d_2$, each such collision involves $W_3$.
Since $W_3$'s two responses on that branch differ, they must be
$d_1,d_2$ in some order. The sixth $J$ branch would imply

$$
|d_1-d_2|=|b|,
$$

while the sixth $M$ branch would imply

$$
|d_1-d_2|=|b+e|.
$$

This contradicts (5.2). In particular the argument has allowed the
two terminal collision pairs to differ after a shared-three sixth
response. It proves $\neg L_2(K,H)$ whenever $d_1\ne d_2$.

Now suppose $d_1=d_2=d$. Fix either sixth action $E$, and for every
real normalized response $s$ write

$$
K_{E,s}=\{W\in K:v_E(W)=s\}.
$$

Any child omitting one of $W_1,W_2$ is empty, singleton or a mixed
pair, so it cannot have $L_1$. An $L_1$ child must therefore contain
both zero worlds. Such a child can exist only if
$v_E(W_1)=v_E(W_2)$. Conversely, if these two sixth responses are
equal, use their common response $s$. For each terminal action $F$
the raw response $D_0+\lambda d$ retains both worlds in that child. Thus
$L_0$ holds for that terminal response under each $F$, and
$L_1(K_{E,s},(H,E,D_0+\lambda s))$ holds. This is true whether or
not the same sixth response also retains $W_3$.

For each $E$ separately, existence of an $L_1$ response child is
therefore equivalent to equality of the zero pair's sixth responses.
Conjoining for both $E$ proves the first equivalence in (6.1).
For the pair alone the same sixth equalities and the common drift
make all four terminal values equal; conversely (5.4) requires just
these equalities. This proves the second equivalence, including the
unequal-drift case. Affine normalization transfers all existential
and universal response quantifiers to the raw readings bijectively.
No condition on the sixth gain samples, sources, other roots or
gain multiplicities has been imposed. ∎

## 7. Common drift and different terminal signs

**Theorem 7.1.** Let $K$ consist of three distinct fixed legal worlds
on (1.1), with one common normalized drift $d$. Suppose their signs
$\operatorname{sgn}f_W(7)\in\{-1,0,1\}$ are not all identical.
If all three signs differ, $\neg L_2(K,H)$. Otherwise let $G$ be the
unique two-world sign class. Then

$$
L_2(K,H)\quad\Longleftrightarrow\quad L_2(G,H).               \tag{7.1}
$$

Consequently an inclusion-minimal common-drift $L_2$ triple must
have one common terminal-gain sign, including the all-zero possibility.

**Proof.** Put $B=QP$, which is strictly entrywise positive. The
traces of $B, MJB, JMB, M^2B$ in (5.1) are all positive sums of its
entries. Therefore for every terminal word $EF$,

$$
\operatorname{sgn}(r_{EF}(W)-d)=\operatorname{sgn}f_W(7).
                                                                    \tag{7.2}
$$

Responses from different sign classes never collide. If all signs
are different, each terminal scalar is injective on every sixth
child. For either terminal action every real terminal response then
retains at most one world, so no sixth child has $L_1$ and $K$ cannot
have $L_2$.

Otherwise the only possible terminal collision is the fixed pair
$G$. Fix a sixth action $E$. If its response child has $L_1$, each
last action $F$ has a response retaining at least two worlds. Those
two must be $G$. Hence the sixth child contains $G$ and the two
$r_{EF}$ values agree on $G$ for both last actions. This reasoning
also applies when the sixth child contains all three worlds.
If $K$ has $L_2$, applying it for each first action shows equal sixth
responses on $G$ for both $E$, and equal terminal responses for
all four $EF$. These are precisely (5.4), so $L_2(G,H)$.
Conversely, if the pair has $L_2$, for each $E$ retain its common
sixth response in the triple. For each $F$ retain the pair's common
terminal response. These actual children still contain $G$, which
verifies $L_1$ for each chosen sixth child and then $L_2(K,H)$.
This proves (7.1) with all action and response quantifiers.
No assumption about $f(6)$, degree drops or repeated roots is used. ∎

## 8. Dependencies, known promises and remaining joint-realization gaps

The late-double-root rigidity, exact sharpness example and terminal
reductions develop the supplied late-root and terminal-reduction
proposals. Lemma 2.1 is reused from the whole-class companion, with
its full proof. The common model and ancestor come from VII.
Polynomial factorization, direct trace multiplication, quadratic
sign analysis and Bernstein convex combinations are established
mathematics. The complete small certificate needed here is
(3.10)–(3.13).

The earlier whole-class companion proves conditioned decoders for
one fixed polynomial shape and for one fixed source. Theorem 3.1
instead starts with the entire known root class (3.1), with source,
shape, amplitude sign and arbitrary original drift initially free.
It derives one polynomial, at most two sources and a fixed one-read
inverse. The terminal reductions concern simultaneously realized
triples with varying sources and shapes. These are distinct
deductions from the earlier fixed-shape and fixed-source inverses.
No claim of external priority or literature completeness is made.

VII, Theorem 4.1 separately states pair exclusion on every entire
history (1.1). Its proof uses its nine integer coefficient matrices
and their three-variable Bernstein identities, as well as a separate
six/seven-double-root argument. Theorems 3.1, 4.1, 6.1 and 7.1 here
do not use those large coefficient identities, that pair-exclusion
theorem or any unseen II–VI bridge as a premise. The reductions do
not independently certify those arrays. If the supplied pair
exclusion is taken as a separately certified premise, (6.1) excludes
the entire exactly-two-terminal-roots triple stratum, and (7.1)
excludes common-drift triples with differing terminal signs. The
unconditional results here are the displayed equivalences and the
all-different-sign exclusion; they supply no losing pair or triple.
The small quartic certificate is separate from VII's three-variable
identities.

The root conditions in (3.1) are promises about the known candidate
class. Equal observed values $\widehat Y=\widehat z$ do not identify
that class: (1.4) only equates
$f(4)\operatorname{tr}(CP)$ and $f(5)\operatorname{tr}(QP)$ in
that case; it does not make either zero or identify $d$ with their
common reading. A candidate outside the promised class has not been
excluded by the conditioned inverse. Injectivity on a class does
not establish injectivity on an unrestricted union of classes.
The same distinction applies to fixed-source and fixed-shape
promises. All inverses here recover complete worlds, with every
mandatory immediate reading and the original clocks retained.

The precise unrestricted triple question remains whether some
$D_0,Y,z\in\mathbb R$, $\lambda\ne0$ admit three pairwise distinct
fixed legal worlds, all satisfying all six equations (1.4) on the
same literal (1.1), for which $L_2$ holds, or whether such triples
are uniformly impossible. No witness or uniform exclusion is given
here. In particular:

- Worlds outside $\mathcal Z_{45}$ retain the other zero-, one- and
  two-ancestor-root patterns, variable sources and gain shapes,
  all remaining degrees and multiplicities, and arbitrary original
  drifts. A triple with only one or two members in
  $\mathcal Z_{45}$ is not excluded by its whole-class decoder.
- A single terminal-root world and the all-three-terminal-roots
  pattern are not generally eliminated. Variable-drift triples with
  no terminal roots, and common-drift triples with one common
  nonzero terminal sign, remain outside these reductions. The
  all-zero common-sign case is also not settled.
- Roots at clock six, their interaction with clock seven and with
  permitted ancestor roots, and other future-root multiplicities
  remain available outside the restrictions actually proved above.
- Different sixth actions may retain different collision pairs.
  A sixth response shared by all three may leave different terminal
  actions colliding on different pairs. These possibilities remain
  except where Theorems 6.1 and 7.1 explicitly resolve them.
  Separately compatible pairs do not supply a common three-world
  realization, and pairwise separating suffixes do not give one
  policy on an arbitrary family.

The larger actual-fiber problem, the joint losing-arm question at
the earlier $JMMJ$ parent, and the unrestricted original-root
alternative of at least nine total readings versus a lawful decoder
with at most eight on every degree-three complete world remain
unresolved here. The distinct $MMJM$ and $MJMMJ$ ancestors discussed
in VII are not identified with (1.1). No global nonlinear bound is
proved, and the continuing mathematical objective is not settled.

## 追加锚（本行以下为增补区）
