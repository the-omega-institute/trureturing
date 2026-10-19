# FIB JMMJM Whole-Class Affine Decoders

## 1. Complete targets and the same actual ancestor

A complete target is a world $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$g\in\mathbb R[T]\setminus\{0\}$ has degree at most three, and
$\delta\in\mathbb R$. The source need not be symmetric. In particular,
no equality between its off-diagonal entries is assumed. The gain may
have either sign, any permitted degree drop, sampled roots and repeated
roots.

Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\qquad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
$$

At original clock $i$ the reading is
$g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts. Each
atom is immediately read on one unresettable, uncopyable trajectory.
A chronological word $EF$ means first $E$ and its reading, then $F$
and its reading; its cumulative matrix is $FEA$. There are no skipped
readings, unread compound actions, extra ports or clock renumberings.
Deterministic actions, stops and answers may be arbitrary functions of
the actual history; no regularity or computational bound is imposed.

For arbitrary real $D_0,Y,z$ and $\lambda\ne0$, fix the literal history

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
                         M,D_0+312\lambda/5),\\
H_J(Y)&=(H_J^-,J,Y),\\
H&=H_{JM}(Y,z)=(H_J(Y),M,z).
\end{aligned}                                                     \tag{1.1}
$$

Thus the five actual atoms are $JMMJM$, and all original clocks
$0,\ldots,5$ and all six readings are retained. In particular $D_0$ is
a history parameter, not a promise that $\delta=D_0$.

Normalize by

$$
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
\widehat Y=(Y-D_0)/\lambda,\qquad
\widehat z=(z-D_0)/\lambda.
$$

The normalized readings and ancestor matrices are

$$
\begin{gathered}
(c_0,c_1,c_2,c_3,c_4,c_5)
=(0,24,48,312/5,\widehat Y,\widehat z),\\
(A_0,A_1,A_2,A_3,A_4,A_5)=(I,J,L,J+L,C,Q),\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
C=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
Q=\begin{pmatrix}1&1\\3&2\end{pmatrix}
  =I+2J+2L-C .
\end{gathered}                                                     \tag{1.2}
$$

A world in the actual fiber $\mathcal F(H)$ satisfies every equation

$$
f(i)\operatorname{tr}(A_iP)+d=c_i,\qquad 0\le i\le5.                \tag{1.3}
$$

Each trace factor is strictly positive: the matrices in (1.2) are
nonzero and entrywise nonnegative, and $P$ is strictly entrywise
positive. Applying the same invertible affine change
$v\mapsto(v-D_0)/\lambda$ to all subsequent readings preserves every
actual response partition, for either sign of $\lambda$. It preserves
complete-target distinction. Induction in (1.5), using the preserved
cardinalities and the bijection of real response values for each action,
proves preservation of every $L_r$. Recovery in normalized coordinates
returns the original target through

$$
g=\lambda f,\qquad \delta=D_0+\lambda d,                            \tag{1.4}
$$

with the same $P$.

For a known candidate set $K\subseteq\mathcal F(H')$ at any literal
history $H'$, define

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
 \bigwedge_{E\in\{M,J\}}\exists v\in\mathbb R:
 L_r(K\cap\mathcal F(H',E,v),(H',E,v)).
\end{aligned}                                                     \tag{1.5}
$$

Every child retains the same fixed worlds and all their actual
ancestors. Unchosen responses are mathematical functions of those
worlds, not observations available to the decoder.

These model and history definitions are those of
[FIB self-calibrating relation mathematics VII, Definitions 1.1–1.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md).
The arguments below establish their conditioned whole-class conclusions
directly from (1.1)–(1.5).

## 2. Linear trace coordinates and terminal words

**Lemma 2.1.** The matrices $I,J,L,C$ form a basis of
$\operatorname{Mat}_2(\mathbb R)$. Every five matrices in (1.2) span
this space, and every four span a space of dimension at least three.

**Proof.** In
$a_0I+a_1J+a_2L+a_3C=0$, the first diagonal entry minus the second is
$a_3$, so $a_3=0$. The lower off-diagonal entry minus the upper one
then gives $a_2=0$. The upper off-diagonal and diagonal entries now
give $a_1=a_0=0$.

If $I$ is missing from the six matrices, recover it as
$Q-2J-2L+C$. If $J$ or $L$ is missing, recover it from $J+L$ and the
other summand. If $C$ is missing, use $I+2J+2L-Q$. If $J+L$ or $Q$
is missing, the original basis remains. Thus every five span all four
dimensions. Adding one matrix to any given four can increase dimension
by at most one; since the resulting five span four dimensions, the
given four have dimension at least three.

The trace pairing is nondegenerate:
$\operatorname{tr}(E_{ab}U)=U_{ba}$ for matrix units $E_{ab}$.
Consequently all these span assertions are also rank assertions for
the corresponding linear trace equations. ∎

The fifth cumulative matrix $Q$ is invertible, with

$$
Q^{-1}=\begin{pmatrix}-2&1\\3&-1\end{pmatrix}.
$$

Two useful sixth-matrix identities, obtained by the displayed
multiplications, are

$$
JQ=\begin{pmatrix}3&2\\1&1\end{pmatrix}=2C-L,\qquad
MQ=\begin{pmatrix}3&2\\4&3\end{pmatrix}=I+2J+2L.                    \tag{2.1}
$$

For any $X=\left(\begin{smallmatrix}u&v\\w&e\end{smallmatrix}\right)$,
the four chronological terminal trace expressions, with an added
drift $d$, are

$$
\begin{array}{c|c|c}
\text{word at clocks six and seven}&\text{matrix acting on }X&
                                  \text{terminal expression}\\ \hline
JJ&J^2=I&u+e+d\\
JM&MJ=L&u+v+e+d\\
MJ&JM&u+w+e+d\\
MM&M^2&u+v+w+2e+d .
\end{array}                                                       \tag{2.2}
$$

The four values determine

$$
v=r_{JM}-r_{JJ},\qquad
w=r_{MJ}-r_{JJ},\qquad
e=r_{MM}-r_{MJ}-r_{JM}+r_{JJ}.                                   \tag{2.3}
$$

If $X$ has rank one and $e\ne0$, then $u=vw/e$, after which
$d=r_{JJ}-u-e$. This is the rank-one terminal reconstruction mechanism
displayed in VII, equation (4.2), and credited there to
[V, Theorem 7.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md).
Equations (2.2)–(2.3) give the complete calculation needed here; no
unseen result of V is required. These four counterfactual expressions
are used together only to prove separation. The decoder acquires one
chronological path.

## 3. No three sampled ancestor gain zeros

**Theorem 3.1.** Every legal world in the entire actual fiber (1.1)
has at most two distinct gain zeros among original clocks
$0,1,2,3,4,5$. Equivalently, at least four ancestor gain samples are
nonzero. This holds uniformly in $D_0,\lambda,Y,z$.

**Proof.** A nonzero polynomial of degree at most three has at most
three distinct real roots: successive factorization at distinct roots
would otherwise give more linear factors than its degree. Suppose
there are three sampled roots. At each of them (1.3) gives $c_i=d$.
The readings $0,24,48,312/5$ are pairwise distinct, so at most one of
clocks zero through three is a root. The three roots must therefore
be exactly $j,4,5$ for some $j\in\{0,1,2,3\}$. In particular

$$
d=c_j=\widehat Y=\widehat z,\qquad
f(T)=a(T-j)(T-4)(T-5),\qquad a\ne0.                              \tag{3.1}
$$

Three distinct roots force degree three and the displayed
factorization, with no further degree or multiplicity case.

Write

$$
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix}.
$$

Strict positivity and rank one give
$0<r<1$, $b,c>0$ and $bc=r(1-r)\le1/4$. Direct multiplication gives

$$
t_J=\operatorname{tr}(JP)=b+c,\qquad
t_L=\operatorname{tr}(LP)=1+b,\qquad
\operatorname{tr}((J+L)P)=t_J+t_L .
$$

The clock-zero equation is $f(0)=-d$. We now exclude all four
possibilities in (3.1).

If $j=0$, then $d=0$ and
$f(1)=12a$, $f(2)=12a$, $f(3)=6a$.
The next three readings require

$$
t_J=2/a,\qquad t_L=4/a,\qquad t_J+t_L=52/(5a).
$$

The first two instead give $t_J+t_L=6/a$, which, since $a\ne0$,
would require $30=52$.

If $j=1$, then $d=24$. The equation $-20a=-24$ gives $a=6/5$.
The clock-two and clock-three gain values are $36/5$ and $24/5$,
so

$$
t_L=\frac{48-24}{36/5}=\frac{10}3,\qquad
t_J+t_L=\frac{312/5-24}{24/5}=8.
$$

Thus $t_J=14/3$, $b=7/3$, $c=7/3$ and
$bc=49/9>1/4$, a contradiction.

If $j=2$, then $d=48$ and $-40a=-48$, so $a=6/5$.
Now $f(1)=-72/5$ and $f(3)=12/5$, yielding

$$
t_J=\frac{24-48}{-72/5}=\frac53,\qquad
t_J+t_L=\frac{312/5-48}{12/5}=6.
$$

Consequently $t_L=13/3$, $b=10/3$ and
$c=5/3-10/3=-5/3$, contrary to positivity.

If $j=3$, then $d=312/5$ and $-60a=-312/5$, so $a=26/25$.
Here $f(1)=-624/25$ and $f(2)=-156/25$, giving

$$
t_J=\frac{24-312/5}{-624/25}=\frac{20}{13},\qquad
t_L=\frac{48-312/5}{-156/25}=\frac{30}{13}.
$$

It follows that $b=17/13$, $c=3/13$ and
$bc=51/169>1/4$, since $204>169$.

All possible three-root patterns are impossible. Throughout, the
fourth and fifth readings are retained: a vanishing gain at either
clock makes that actual reading equal to the same $d$. No
baseline-drift promise has been introduced. The conclusion leaves
every legal zero-, one- or two-root ancestor pattern, lower degree,
sign and repeated-root possibility available. ∎

## 4. The entire fixed-polynomial-shape class

Fix a known $h\in\mathbb R[T]\setminus\{0\}$ of degree at most three.
Define

$$
K_h=\{W\in\mathcal F(H):f=a h
                         \text{ for some }a\in\mathbb R\setminus\{0\}\}.
                                                                    \tag{4.1}
$$

The gain constraint specifies a fixed one-dimensional polynomial
subspace with its zero element removed; both amplitude signs are
included. The shape promise
is information about known candidates, not information inferred from
the observed ancestor. No drift or source is fixed, and the class
has no cardinality bound.

**Theorem 4.1.** The whole class $K_h$, and every known subset of it,
has one fixed continuation with at most two further immediate
readings recovering the complete target. In particular
$\neg L_2(K_h,H)$. If exactly one of $h(0),\ldots,h(5)$ is zero,
$K_h$ has at most one target. If at least three are zero, $K_h$ is
empty.

**Proof, affine containment.** For a world in $K_h$ lift its source to

$$
S=aP.
$$

Then $\operatorname{tr}S=a\ne0$, and $(S,d)$ determines the entire
normalized world by

$$
P=S/\operatorname{tr}S,\qquad f=(\operatorname{tr}S)h .
                                                                    \tag{4.2}
$$

There is no positivity requirement on $S$ itself when $a<0$; legality
means precisely the original conditions on the reconstructed world.
The ancestor equations become six linear equations in the five real
coordinates $(S,d)$:

$$
h(i)\operatorname{tr}(A_iS)+d=c_i,\qquad 0\le i\le5.                \tag{4.3}
$$

If none of these six samples of $h$ vanishes, projecting the six rows
onto their four matrix coordinates gives rank four by Lemma 2.1.
The full system has rank at least four, and its affine solution space
has dimension at most one.

If a sample vanishes, its equation fixes $d=c_i$. For a nonempty
legal class Theorem 3.1 permits at most two sampled zeros. At least
four nonzero samples therefore remain, whose matrices have span
dimension at least three. With $d$ fixed, the affine solution space
for $S$ has dimension at most one. If exactly one sample vanishes,
the remaining five matrices span all four dimensions, so $S$ and $d$
are unique. If at least three vanish, Theorem 3.1 gives an empty
legal class.

Thus every nonempty legal class is injectively lifted into one affine
line or one point. Rank one, positivity and nonzero trace only remove
points from the containing affine solution space; they do not enlarge
it.

**Proof, joint separation of future responses.** Put $h_6=h(6)$ and
$h_7=h(7)$. On the containing affine space define

$$
\begin{aligned}
j_6(S,d)&=h_6\operatorname{tr}(JQS)+d,\\
m_6(S,d)&=h_6\operatorname{tr}(MQS)+d,\\
r_{EF}(S,d)&=h_7\operatorname{tr}(FEQS)+d,
                         \qquad E,F\in\{J,M\}.
\end{aligned}                                                       \tag{4.4}
$$

These are affine scalar functions. We prove that their joint vector

$$
(j_6,m_6,r_{JJ},r_{JM},r_{MJ},r_{MM})                              \tag{4.5}
$$

is injective on the legal class, including every future-zero case.

If $h_7\ne0$, let

$$
X=h_7QS=\begin{pmatrix}u&v\\w&e\end{pmatrix}.
$$

Equations (2.2)–(2.3) recover $v,w,e$ from the terminal responses.
For a legal world,

$$
e=h_7a(QP)_{22}\ne0,
$$

because $h_7\ne0$, $a\ne0$ and $QP$ is strictly entrywise positive.
The rank-one identity recovers $u=vw/e$, then $d$, and finally
$S=h_7^{-1}Q^{-1}X$. Equal terminal vectors therefore give the same
$(S,d)$ and complete world. Neither $h_7$ nor $a$ is required to be
positive. The only variable divisions here are by $h_7$ and $e$ in
this explicitly nonzero case.

If $h_7=0$ but $h_6\ne0$, suppose two legal worlds have the same
vector (4.5). Every terminal response is its world's $d$, so
$d_1=d_2$. Write $U=S_1-S_2$. Equality of the two sixth responses,
with division by $h_6$ only in this case, gives

$$
\operatorname{tr}(JQU)=\operatorname{tr}(MQU)=0.
$$

Set

$$
\alpha=\operatorname{tr}U,\quad
\beta=\operatorname{tr}(JU),\quad
\gamma=\operatorname{tr}(LU),\quad
\epsilon=\operatorname{tr}(CU).
$$

By (2.1), $\epsilon=\gamma/2$ and
$\alpha=-2\beta-2\gamma$. Hence the six ancestor traces of $U$ are

$$
\bigl(-2(\beta+\gamma),\ \beta,\ \gamma,\
                  \beta+\gamma,\ \gamma/2,\ -\gamma/2\bigr).
                                                                    \tag{4.6}
$$

Since seven is a root of $h$, at most two of clocks zero through five
can be further roots. Subtracting (4.3) for the two worlds therefore
makes at least four entries of (4.6) zero. If $\gamma\ne0$, the
entries at two, four and five are all nonzero, leaving at most three
zero entries. If $\gamma=0$ and $\beta\ne0$, the entries at zero, one
and three are all nonzero, again leaving at most three. Thus
$\beta=\gamma=0$, and then $\alpha=\epsilon=0$. Nondegeneracy on the
basis $I,J,L,C$ forces $U=0$. The worlds coincide.

If $h_6=h_7=0$, equality of terminal responses again gives $d_1=d_2$.
Six and seven are two distinct roots of $h$, so at most one ancestor
clock is a root. The other at least five equations (4.3) force

$$
\operatorname{tr}(A_i(S_1-S_2))=0
$$

at five ancestor matrices. Lemma 2.1 gives $S_1=S_2$ and the same
complete target. This case divides by neither future gain sample.
The three cases exhaust all possible values at six and seven,
including every multiplicity compatible with the degree bound.

**Proof, one scalar for the whole class.** If $K_h$ has at least
two worlds, its distinct lifts lie in the same one-dimensional affine
solution space $\ell$. Joint injectivity of (4.5) implies that some
coordinate in that vector is nonconstant on $\ell$. An affine scalar
on a real line has the form $b+at$; if it is nonconstant, $a\ne0$ and
it is injective on the whole line. It is therefore injective on all
of $K_h$, including any infinite or disconnected legal subset.
No interval or convexity assumption on the legal points is used.

Choose the first nonconstant coordinate in the fixed order (4.5).
This is one choice for the known shape and ancestor, independent of
the unknown world. If it is $j_6$ or $m_6$, execute respectively $J$
or $M$, immediately read at original clock six, and invert that
coordinate on the known class. If it is $r_{EF}$, execute the fixed
chronological word $EF$, immediately reading at both six and seven.
The terminal value has one inverse on the entire known class. It
recovers $S,d$, then (4.2) and (1.4) recover $P,g,\delta$.

A known singleton can stop at clock five; an empty class is unreachable.
Restriction of the same chosen inverse works on every known subset.
There are at most $6+2=8$ total readings. This is an existence result
for a deterministic inverse, with no cost, efficiency, numerical
stability or effective class-recognition guarantee. Section 6 proves
the asserted $L_2$ negation with all actual-child quantifiers. ∎

## 5. The entire fixed-source class

For a fixed known legal source $P_*$, define

$$
K_{P_*}=\{W\in\mathcal F(H):P=P_*\}.                              \tag{5.1}
$$

The source promise is candidate information. It is not inferred from
the ancestor. Gains may have different shapes, arbitrary drift and all
legal root patterns; the class has no cardinality bound.

**Theorem 5.1.** One fixed chronological continuation $JJ$ or $JM$
has an injective clock-seven response on $K_{P_*}$. It recovers the
complete target with both immediate reads, hence at most eight total
readings. The same continuation works on any known subset, and
$\neg L_2(K_{P_*},H)$.

**Proof.** Put $t_i=\operatorname{tr}(A_iP_*)>0$ for $0\le i\le3$.
Define the interpolation polynomials

$$
\ell_i(T)=\prod_{\substack{0\le j\le3\\j\ne i}}
                       \frac{T-j}{i-j},\qquad
U_*(T)=\sum_{i=0}^3\frac{c_i}{t_i}\ell_i(T),\qquad
V_*(T)=\sum_{i=0}^3\frac1{t_i}\ell_i(T).
                                                                    \tag{5.2}
$$

Every compatible gain satisfies

$$
f(T)=U_*(T)-dV_*(T).                                             \tag{5.3}
$$

Indeed (1.3) gives equality at four distinct clocks, and the
difference is a polynomial of degree at most three, so the root
bound makes it identically zero. Only strictly positive $t_i$ and
nonzero integer interpolation denominators have been divided out,
never a gain sample. The last two ancestor equations, nonzero-gain
condition and all remaining legality conditions restrict the allowed
real values of $d$. They are retained, not discarded. Equal $d$
gives equal $f$ by (5.3), so $d$ parametrizes the legal class
injectively.

Let

$$
B=QP_*,\qquad q_0=\operatorname{tr}(QP_*),\qquad
q_1=\operatorname{tr}(MJQP_*).
$$

Since $MJ=L$, direct multiplication gives

$$
\operatorname{tr}(LB)=B_{11}+B_{12}+B_{22},\qquad
q_1-q_0=B_{12}=(QP_*)_{12}>0.                                   \tag{5.4}
$$

The clock-seven responses after the words $JJ$ and $JM$ are

$$
\begin{aligned}
r_{JJ}&=q_0U_*(7)+(1-q_0V_*(7))d,\\
r_{JM}&=q_1U_*(7)+(1-q_1V_*(7))d .
\end{aligned}                                                       \tag{5.5}
$$

Their slopes $k_0=1-q_0V_*(7)$ and $k_1=1-q_1V_*(7)$ cannot both
vanish. Otherwise subtraction gives
$(q_1-q_0)V_*(7)=0$; (5.4) implies $V_*(7)=0$, contradicting $k_0=0$.

Choose $JJ$ when $k_0\ne0$ and $JM$ otherwise. The selected terminal
response is affine in $d$ with nonzero slope, hence injective on the
whole legal class. In either case first execute $J$ and read clock
six, then execute the chosen second atom and read clock seven. If the
chosen coefficient and trace are $k$ and $q$, the terminal value $r$
returns

$$
d=\frac{r-qU_*(7)}{k}.
$$

Now (5.3) and (1.4), together with the known $P_*$, recover the complete
original target. Worlds with $f(6)=0$ or $f(7)=0$ remain covered,
because neither value has been divided out. Lower degrees, cancellations,
either gain sign and repeated roots remain legal. Restricting the
same inverse to a known subset preserves injectivity. The claimed
recursion statement follows from Section 6. ∎

## 6. Explicit negation of L2 on actual children

The decoder arguments give the same fixed-world quantifier statement
for either conditioned class and every known subset $K$ of it.

Here all appended readings $v,w$ are original, unnormalized values,
and $H$ is exactly (1.1). Write $\rho_E(W)$ for the normalized sixth
response ($j_6$ or $m_6$ in the shape class). The corresponding raw
response functions are

$$
v_E(W)=D_0+\lambda\rho_E(W),\qquad
w_{EF}(W)=D_0+\lambda r_{EF}(W).
$$

Since $\lambda\ne0$, each selected raw scalar has precisely the same
injectivity as its normalized scalar. For the chosen first atom $E$
and any real original-clock response $v$, set

$$
\begin{aligned}
H_v&=(H,E,v),\\
K_v&=K\cap\mathcal F(H,E,v)
    =\{W\in K:v_E(W)=v\}.
\end{aligned}                                                       \tag{6.1}
$$

If the selected sixth response is injective on $K$, then for every
real $v$ the set $K_v$ has at most one world. The cardinality clause
of (1.5) gives $\neg L_1(K_v,H_v)$ for every $v$.

If instead the selected injective raw scalar is the terminal response
$w_{EF}$ of a fixed word $EF$, then for every real $v$ and every
real $w$,

$$
\begin{aligned}
K_{v,w}
 &=K_v\cap\mathcal F(H_v,F,w)\\
 &=\{W\in K:v_E(W)=v,\ w_{EF}(W)=w\}
\end{aligned}                                                       \tag{6.2}
$$

has at most one world. Thus $L_0(K_{v,w},(H_v,F,w))$ is false for
every $w$. When $|K_v|\ge2$, the particular second atom $F$ consequently
has no response retaining $L_0$, so the conjunction defining
$L_1(K_v,H_v)$ fails. When $|K_v|\le1$, its cardinality clause already
fails. In all cases,

$$
\exists E\in\{M,J\}\ \forall v\in\mathbb R:
                  \neg L_1(K_v,H_v).                             \tag{6.3}
$$

This is precisely a failed action conjunct in the definition of
$L_2(K,H)$. If $|K|\le1$, its cardinality clause gives the same
conclusion immediately. Hence both theorems prove $\neg L_2$ on
the whole promised class, without replacing its actual children by
independently chosen pairs. Empty and singleton children, all real
sixth responses and all real seventh responses have been included.
The physical policy still acquires the immediate sixth read whenever
the seventh read supplies the inverse.

## 7. Whole-class information, unions and comparison with VII

The gain-shape result uses one affine line containing the entire
lifted legal class. Joint separation of the six coordinates then
provides one scalar injective on that whole line. This rules out
different collision pairs on different arms inside that class, even
when the pairs have no common endpoint. The fixed-source result
instead uses one parameter $d$ and two terminal slopes which cannot
both vanish. Neither proof imposes a finite-cardinality restriction.

Both are conditional statements about known candidates. The observed
history does not identify a shape $h$ or a source $P_*$, and neither
theorem supplies such information. A union of different shape classes
can have different containing affine lines; a scalar injective on
each of several classes need not be injective on their union.
Different fixed-source classes may require different responses and
may collide with each other. No theorem here gives one scalar or one
policy on the unrestricted union by taking these conditional inverses
separately.

VII, Theorem 4.1 states that every distinct pair on this exact entire
$JMMJM$ fiber has $\neg L_2$. Its Section 4 proof includes the
rank-one terminal calculation, a separate double-future-root argument
and the rational Bernstein certificate of its Section 3. The
coefficient-array identities are not independently certified here.
None of that pair-exclusion theorem, its large coefficient arrays or
the unseen II–VI bridges is a premise of Theorems 3.1, 4.1 or 5.1
above. The small matrix identities, factorization, interpolation and
all separation arguments needed for these three theorems are
displayed here.

Even granting VII's pair exclusion, its logical scope is a pair,
not an arbitrary family or an unrestricted triple. For two worlds,
$L_2$ requires agreement on both sixth responses and all four
terminal responses. On a larger set, the collision pairs retained
after different actions or responses can differ. Excluding each
fixed pair does not establish (6.3) for the whole larger set.
The additional affine structure above is what supplies (6.3) for
the promised classes.

The histories appearing in the supplied VII source have distinct
roles:

| Literal history | Scope retained |
| --- | --- |
| $JMMJM$, with (1.1) and all six readings | Theorems 3.1–5.1 here; the pair exclusion stated in VII, Theorem 4.1 |
| $JMMJ$ and its earlier $JMM$ history with the readings in (1.1) | VII's small-child consumers retain their cardinality promises on each actual $J$, then $M$, child |
| $MMJM$, namely $(0,M,1,M,23/7,J,331/35,M,Y)$ | VII's separate common-prediction, common-$b,d_6$ whole-class application retains its own promises and zero-stratum restrictions |
| $MJMMJ$ | The distinct pair-exclusion history attributed by VII to VI; it is not (1.1) |

No local decoder or obstruction is transferred between these ancestors.
In particular the $MMJM$ common-prediction constants are not extra
observations on the present trajectory, and its response chart is
not the $Q$ chart of this $JMMJM$ child.

## 8. Necessary diversity and the unresolved unrestricted triple

**Corollary 8.1.** If three pairwise distinct fixed legal worlds on
the same actual history (1.1) satisfy

$$
L_2(\{W_1,W_2,W_3\},H),
$$

they use at least two distinct one-dimensional polynomial subspaces
and at least two distinct sources. Each of the three worlds has at
least four nonzero ancestor gain samples.

**Proof.** If all gains had one shape, the triple would be a subset
of one $K_h$, contradicting Theorem 4.1 and Section 6. If all sources
were equal, it would be a subset of one $K_{P_*}$, contradicting
Theorem 5.1 and Section 6. The sample assertion is Theorem 3.1 applied
separately to each fixed world. Proportionality of $f$ is equivalent
to proportionality of $g$ under the same nonzero $\lambda$. ∎

These are necessary diversity conditions. They do not require three
pairwise different sources or shapes, and they do not decide whether
a triple exists.

The precise remaining question is whether there exist
$D_0,Y,z\in\mathbb R$, $\lambda\ne0$ and three pairwise distinct
fixed complete legal worlds, all satisfying every equation (1.3)
on the same literal (1.1), for which $L_2$ holds. Uniform
impossibility across these data is also unproved here. In the
remaining class the sources and gain shapes may vary; each world
may have zero, one or two ancestor roots, independent future-zero
patterns and arbitrary real drift. Different sixth actions may
retain different collision pairs. Even a sixth response shared by
all three can leave different terminal actions colliding on different
pairs. Neither a collection of compatible marginal pairs nor
pairwise separating suffixes supplies or excludes the required joint
three-world realization.

The deductions here extend the supplied JMMJM whole-class proposals
into complete conditioned decoders. They are repository deductions
using established polynomial root counting, elementary matrix
coordinates, the rank-one terminal mechanism, Lagrange interpolation
and affine functions on a line. The supplied VII text supplies the
model, exact ancestor and credited terminal mechanism. Its references
to II–VI and external literature remain credited interfaces with
their stated scopes; no unseen proof is imported. No external
priority or literature-completeness claim is made.

The original full-domain alternative remains whether the deterministic
complete-target problem at degree three requires at least nine total
readings, or admits a lawful decoder with at most eight total readings
on every legal world from the original root. No result here settles
either alternative, proves a global nonlinear lower bound or
completes the continuing research goal. There is no general neural
network, empirical, kernel-verification, complexity or stability
claim. Existence of the conditioned exact inverses entails no
efficiency or robustness guarantee.

## 追加锚（本行以下为增补区）
