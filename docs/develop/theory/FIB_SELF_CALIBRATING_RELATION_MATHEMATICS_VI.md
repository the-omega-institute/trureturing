# FIB 自校准关系数学 VI

## 1. 完整目标、实际纤维与两个不同的父历史

**定义 1.1（原子采集域）。** Let $\mathcal W_3$ be the set of triples
$W=(P,g,\delta)$ with $P$ a strictly entrywise positive real $2\times2$
matrix of rank one and trace one, $0\ne g\in\mathbb R[t]$ of degree at most
three, and $\delta\in\mathbb R$. Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
$$

The original-clock reading is

$$
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.                 \tag{1.1}
$$

The initial reading counts. Each atom is followed immediately by its reading;
eight total readings use exactly clocks $0,\ldots,7$. There is one
unresettable, uncopyable trajectory. Skipped readings, unread compound
actions, empty-action readings, clock renumbering and additional observation
ports are excluded. A protocol's actions, stopping and returned complete
target may be arbitrary deterministic functions of its entire actual
history. There is no continuity, measurability, computability or finite
description requirement. All gain signs, lower actual degrees, sampled
roots, repeated roots and constant drifts are retained.

For a literal history $H$, let $\mathcal F(H)$ consist of all compatible
complete targets, retaining every action and reading. For known
$K\subseteq\mathcal F(H)$ use [II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_{s+1}(K,H)&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:
L_s(K\cap\mathcal F(H,E,z),(H,E,z)).
\end{aligned}                                                   \tag{1.2}
$$

The horizon never exceeds the remaining original clocks. These predicates
include early stopping. Their negations mean that one strategy recovers
every member of the known family within the remaining horizon. Every child
is an actual response fiber of the same fixed worlds. Predictions for an
unchosen action are mathematical functions of a world, not additional
physical readings.

**定义 1.2（字面 MMJM 父历史）。** Fix any real $Y$ and set

$$
\begin{gathered}
c_0=23/7,\qquad h_0=331/35,\\
H_3=(0,M,1,M,c_0,J,h_0),\qquad H_4(Y)=(H_3,M,Y),\\
T=M^2=I+M,\qquad
B=JT=\begin{pmatrix}1&2\\1&1\end{pmatrix},\qquad
D=MB=\begin{pmatrix}1&1\\2&3\end{pmatrix},\\
Q_M=MD=B+D,\qquad Q_J=JD=2B-M.
\end{gathered}                                                   \tag{1.3}
$$

Thus the matrices through clock four are $I,M,T,B,D$. For each individual
$W\in\mathcal F(H_4(Y))$, define its two fifth predictions by

$$
m(W)=\delta+g(5)\operatorname{tr}(Q_MP),\qquad
j(W)=\delta+g(5)\operatorname{tr}(Q_JP).                         \tag{1.4}
$$

No constancy of either function is part of this definition. Write
$\mathcal F(Y;m,j)$ for their joint level set within this entire parent
fiber.

Use the positive chart of [II, Definition 69.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
\begin{gathered}
\eta=(DP)_{22}>0,\quad R=P/\eta,\quad H=\eta g,\\
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},
\qquad \frac13<x<\frac12,\quad y>0,\\
s=x+y,\qquad p=xy.
\end{gathered}                                                   \tag{1.5}
$$

These coordinates are unique. The complete target is
$(R/\operatorname{tr}R,(\operatorname{tr}R)H,\delta)$, and the
normalizing factor is positive. The five positive parent trace factors are

$$
(T_0,T_1,T_2,T_3,T_4)
=(3p+1-s-x,\ s-2p,\ p+1-x,\ s-p,\ p+1).                       \tag{1.6}
$$

Every target still satisfies
$H(i)T_i+\delta=(0,1,c_0,h_0,Y)_i$ for $0\le i\le4$.
The individual fifth predictions and the two sixth predictions following
fifth $M$ are

$$
\begin{aligned}
j&=\delta+H(5)s,&m&=\delta+H(5)(s+1),\\
z_6^{MJ}&=\delta+H(6)(p+y+1),&
z_6^{MM}&=\delta+H(6)(p+s+2).
\end{aligned}                                                   \tag{1.7}
$$

Superscripts list atoms in chronological order, beginning at clock five.
These formulas are the corresponding entries of II, Definition 69.2.
Identical $x,y,\delta$ determine an identical complete target at this parent:
the source is fixed by the chart, and the four positive trace factors at
clocks $0,1,2,3$ determine the entire gain by interpolation.

**约定 1.3（所用的既有根类接口）。** The following results retain the
literal parent (1.3), arbitrary real $Y$ and all the domain conditions of
Definition 1.1. [II, Theorem 52.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
gives at most one target at any fixed drift with $g(6)=g(7)=0$.
II, Theorem 53.1 consequently says that two distinct targets forming
$L_2$ in either actual fifth child have equal drift, both seventh gains
zero, and both sixth gains nonzero. II, Theorem 53.2 excludes such a
two-target $L_2$ child after fifth $J$, for every actual fifth reading.

[II, Theorem 58.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) gives
one fixed $J,J,J$ continuation recovering the entire
$\mathcal F(H_4(Y))\cap\{g(5)=0\}$, with unknown gain shape and drift.
This is a promise on each member, not a conclusion from one unrestricted
reading. Its three readings are at clocks $5,6,7$.

[V, Corollary 4.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) recovers
any known set of at most three targets in one
$\mathcal F(Y;m,j)$ with $m\ne j$, using at most those same three further
readings. Its common non-diagonal fifth hypothesis remains explicit here;
it is not a hypothesis on an arbitrary triple in (1.3).

## 2. 第五 M 坏对与共同第五 J 的不相容性

**引理 2.1（固定漂移的五、七双根注入性）。** For every real $Y,d$, there
is at most one target in $\mathcal F(H_4(Y))$ with
$\delta=d$ and $g(5)=g(7)=0$.

Proof. Set
$u=\operatorname{tr}(MP)>0$, $v=\operatorname{tr}(BP)>0$ and
$w=\operatorname{tr}(DP)>0$. Trace one and strict entrywise positivity give

$$
v=1+P_{12}+2P_{21}<1+2u,
\qquad 1+2u-v=P_{12}+2P_{22}>0.                              \tag{2.1}
$$

Factor

$$
g(t)=(t-5)(t-7)(a+bt),\qquad
a=-d/35,\qquad b=\frac{1-d}{24u}+\frac d{35}.                 \tag{2.2}
$$

The first two equations of the parent give these coefficients. This
factorization includes all lower degrees and all further root
multiplicities. The clock-two equation is exactly

$$
Q_5(u)=12du^2+(5d-57)u+35(1-d)=0.                            \tag{2.3}
$$

Suppose $0<d<1$. Then

$$
g(3)=\frac{1-d}{u}+\frac{16d}{35}>0,\qquad
du<\frac{57-5d}{12}.
$$

Using (2.3), direct substitution reduces the relevant upper expression to

$$
d+g(3)(1+2u)=\frac{127-24d+20du}{35}
<\frac{222-97d/3}{35}<\frac{222}{35}.                        \tag{2.4}
$$

But the actual clock-three reading and (2.1) require
$331/35=d+g(3)v<d+g(3)(1+2u)$, a contradiction.

For $d<0$ or $d>1$, the quadratic (2.3) has negative root product
$35(1-d)/(12d)$, so it has at most one positive root. At $d=0$ its unique
positive root is $35/57$; at $d=1$ its unique positive root is $13/3$.
Thus each drift admitting a target determines at most one $u$, hence the
entire polynomial in (2.2). No discriminant or sampled gain was divided
out in this argument.

For source reconstruction, $g(3)$ and $g(4)$ are nonzero. Indeed, an
additional root three makes $g$ a nonzero multiple of
$(t-3)(t-5)(t-7)$. The first three readings and $T=I+M$ then give
$61d=333$, whereas the clock-three root requires $d=331/35$.
An additional root four makes $g$ a nonzero multiple of
$(t-4)(t-5)(t-7)$. The first three readings instead force
$d=241/31$ and $g(3)=-2d/35<0$. Since $241/31<331/35$ and $v>0$, this
cannot give the clock-three reading. In either triple-root factorization
$d=0$ would force the whole polynomial to vanish and is forbidden, rather
than an omitted solution.

Consequently

$$
v=\frac{331/35-d}{g(3)},\qquad w=\frac{Y-d}{g(4)}.
$$

The existing four-trace inverse [II, equation (52.5)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
now gives the unique matrix

$$
P=\begin{pmatrix}
-1-3u+v+w&-3-4u+v+2w\\
1+2u-w&2+3u-v-w
\end{pmatrix}.                                                 \tag{2.5}
$$

All divisions used a nonzero fixed integer, $u>0$, or the two samples
just proved nonzero. Existence was not asserted for an empty drift class.
This proves uniqueness of the complete target. ∎

**定理 2.2（共同 J 预测排除实际 M 坏对）。** Fix any real $Y,m,j$. Two
distinct targets in $\mathcal F(Y;m,j)$ cannot form $L_2$ after their
actual fifth $M$ reading $m$. Thus any two-target $L_2$ actual fifth-$M$
child at (1.3) must have unequal fifth-$J$ predictions.

Proof. Suppose such a pair exists, keeping these same two worlds
throughout. The precise fifth-child application of II, Theorem 53.1 in
Convention 1.3 gives a common drift $d$, two seventh roots and two nonzero
sixth gains. Put $\kappa=m-j$. In each world's chart, (1.7) gives
$H_i(5)=\kappa$.

If $\kappa=0$, both targets have roots five and seven and the same drift.
Lemma 2.1 makes their complete targets identical, a contradiction.

Suppose $\kappa\ne0$. The common $j$ and drift make
$s_i=(j-d)/\kappa$ the same number $s$. Write $v_i=H_i(6)\ne0$.
Equality of both sixth readings after the actual fifth $M$ gives

$$
\begin{aligned}
v_1[p_1+y_1+1]&=v_2[p_2+y_2+1],\\
v_1[p_1+s+2]&=v_2[p_2+s+2].
\end{aligned}                                                   \tag{2.6}
$$

The first line is nonzero because $p_i+y_i+1>0$. Dividing the second
line by the first yields equality at $x_1,x_2$ of

$$
F_s(x)=\frac{x(s-x)+s+2}{x(s-x)+s-x+1},\qquad
F_s'(x)=\frac{x^2+2x+2}{[x(s-x)+s-x+1]^2}>0.                  \tag{2.7}
$$

The legal fixed-$s$ set
$\{x:1/3<x<1/2,\ s-x>0\}$ is an interval, and its denominator is
positive. Strict monotonicity forces $x_1=x_2$, hence $y_1=y_2$.
The common drift and the four parent readings at $0,1,2,3$ now give the
same entire gain and the same normalized source, again a contradiction.
Both signs of $v_i$ were allowed. The zero-sixth branch was excluded by
the same-parent result in Convention 1.3, not by an additional promise. ∎

## 3. 恰三目标桥梁及其整族消费者

**定理 3.1（不受限恰三目标的共同非对角第五响应）。** For every real $Y$
and every set $K\subseteq\mathcal F(H_4(Y))$ of exactly three distinct
complete targets,

$$
L_3(K,H_4(Y))\quad\Longrightarrow\quad
\exists m,j\in\mathbb R:\ m\ne j\ \land\
\bigl(\forall W\in K:\ m(W)=m,\ j(W)=j\bigr).                 \tag{3.1}
$$

Proof. Apply the failure recursion to fifth $J$, retaining all its actual
response fibers. The selected $L_2$ child cannot contain fewer than two
targets; II, Theorem 53.2 excludes exactly two. Since the whole parent
set has exactly three targets, the selected child must be all of $K$.
Thus $j(W)=j$ is constant on the entire original triple.

Apply the recursion to fifth $M$. Its selected $L_2$ child again contains
at least two targets. If it had exactly two, they would share their
actual fifth-$M$ reading and the fifth-$J$ prediction already derived on
the same $K$. Theorem 2.2 excludes this pair. The child must therefore
be all three targets, so $m(W)=m$ is constant as well. In particular the
two selected children are the same fixed triple, not separately fitted
families at unrelated fifth histories.

If $m=j$, (1.7) forces $H_W(5)=0$ for each $W\in K$, hence $g_W(5)=0$
because $\eta_W>0$. The root-five domain of II, Theorem 58.1 therefore
contains the entire $K$. Its single fixed $J,J,J$ continuation recovers
all these targets within the three remaining readings, contradicting
$L_3$. Thus $m\ne j$.

All targets retain the same literal $Y$ and every earlier reading. The
argument starts with varying fifth responses and exhausts their possible
actual children. Each selected losing node contains distinct targets,
so early stopping is included. ∎

**定理 3.2（整个已知三目标域与失败见证的基数界）。** Every known
$K\subseteq\mathcal F(H_4(Y))$ with $|K|\le3$ has a deterministic
recovery strategy with at most three further readings. Therefore

$$
L_3(K,H_4(Y))\quad\Longrightarrow\quad |K|\ge4                 \tag{3.2}
$$

for every compatible family $K$, finite or infinite.

Proof. First let $|K|=3$. If it had $L_3$, Theorem 3.1 would put all its
targets in one $\mathcal F(Y;m,j)$ with $m\ne j$. This supplies exactly
the premise of V, Corollary 4.1: the parent, cardinality, complete-target
domain and remaining clocks agree. That corollary gives one whole-$K$
strategy, contradicting $L_3$. Its common-fifth premise has thus been
derived, not inserted into the unrestricted input.

One can describe the strategy by exhaustive cases on the known response
functions. If $j$ is nonconstant, execute fifth $J$ and read. Every
reachable child has at most two targets. A singleton stops; an actual
pair is not $L_2$ by II, Theorem 53.2. Choose the first of
$MM,MJ,JM,JJ$, in this fixed order, whose sixth or seventh reading
differs on that pair. Execute its atoms individually, stopping at the
first distinguishing reading. A separating suffix exists by the
two-target meaning of $L_2$.

If $j$ is constant and $m$ is nonconstant, use fifth $M$ and the same
rule, now justified on each pair by Theorem 2.2. If both functions are
constant and equal, use the single root-five $J,J,J$ inverse from II,
Theorem 58.1. If both are constant and different, use V, Corollary 4.1
on that entire joint fiber's known triple. Its finite policy chooses
an atom whose every reachable actual response child has a successful
remaining subtree, recurses on the actual reading, and stops at a
singleton. Nonfailure proved there ensures such an atom at every
nonsingleton node. These cases exhaust every known triple.

For two targets, fifth $J$ either separates immediately or leaves a
pair covered by II, Theorem 53.2. At most one target can stop already.
Each strategy is defined on every actual retained fiber of its whole
known input set; predictions only define the policy and cost no
additional acquisition. There are five parent readings and at most
three new atoms, each immediately read at $5,6,7$, for at most eight
total readings. The conclusion for any $K$ of size below four follows
by applying this recovery statement to that same $K$, without an
extraction claim for a larger family. ∎

**定理 3.3（变响应整族与前一层的恢复）。** The following are sufficient
conditions on known families; neither condition is imposed on an
unrestricted fiber.

1. Let $K\subseteq\mathcal F(H_4(Y))$, with $j(W)$ constant on all $K$.
   If every actual fifth-$M$ response fiber of $K$ has at most two
   distinct targets, one strategy recovers all of $K$ in at most three
   further readings, even when $K$ is infinite and $m(W)$ varies.
2. Let $K\subseteq\mathcal F(H_3)$. If every actual fourth-$M$ response
   fiber of $K$ has at most three distinct targets, one strategy
   recovers all of $K$ in at most four further readings.

Proof. For the first assertion, execute fifth $M$ and read $m$. Stop
on a singleton. Every remaining pair shares the stipulated $j$, so
Theorem 2.2 excludes $L_2$ after this actual $M$ reading. Choose the
first separating suffix from the four ordered two-atom words as in
Theorem 3.2 and execute it with immediate readings. This rule is defined
from each entire actual fiber, so the same policy serves every target,
regardless of the number of possible $m$ values.

For the second assertion execute fourth $M$ and read $Y$. The whole
retained fiber lies in that literal $H_4(Y)$ and has at most three
targets. Apply Theorem 3.2 to that set. The reading at clock four is
already acquired and is not repeated. The budgets are respectively
$5+3=8$ and $4+1+3=8$; the last possible reading is at clock seven. ∎

## 4. MJMMJ 的完整实际历史与正源坐标

**定义 4.1（互补历史及全部参数）。** Independently of (1.3), fix

$$
D_0\in\mathbb R,\qquad \lambda\ne0,\qquad
0<\varepsilon<1/6,\qquad Y,z\in\mathbb R.
$$

Put $a_0=D_0-21\lambda$, $a_2=D_0+5\lambda(1+\varepsilon)$ and

$$
\begin{aligned}
C_3&=(a_0,M,D_0,J,a_2,M,D_0),\\
C_4(Y)&=(C_3,M,Y),\\
C_5(Y,z)&=(C_4(Y),J,z).
\end{aligned}                                                   \tag{4.1}
$$

The cumulative matrices along this chronological $MJMMJ$ history are

$$
\begin{gathered}
I,\ M,\ U,\ MU,\ A_4,\ Q,\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\\
MU=\begin{pmatrix}0&1\\1&2\end{pmatrix},\qquad
A_4=M^2U=\begin{pmatrix}1&2\\1&3\end{pmatrix}=U+MU,\qquad
Q=JA_4=\begin{pmatrix}1&3\\1&2\end{pmatrix}.
\end{gathered}                                                   \tag{4.2}
$$

Thus every compatible world satisfies all six equations

$$
g(i)\operatorname{tr}(A_iP)+\delta
=(a_0,D_0,a_2,D_0,Y,z)_i\qquad(0\le i\le5).                  \tag{4.3}
$$

The parameter $D_0$ is part of the history and is not presumed to be
the target's drift. This is the $H_{MJ}$ history of [V, Definition 5.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)
and its actual fifth-$J$ child. It is different from the $JMMJ$ history
there and from the $MMJM$ parent (1.3).

For a target at (4.1), put $\eta=(QP)_{22}>0$, $R=P/\eta$ and $H=\eta g$.
The inverse $Q^{-1}=\left(\begin{smallmatrix}-2&3\\1&-1\end{smallmatrix}\right)$
gives the unique chart

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(3-2x)y&3-2x\\(x-1)y&x-1\end{pmatrix},
\qquad 1<x<3/2,\quad y>0.                                    \tag{4.4}
$$

Conversely these inequalities make every displayed entry positive and
the matrix rank one. As before, the normalized target is
$(R/\operatorname{tr}R,(\operatorname{tr}R)H,\delta)$.
For $s=x+y$, $p=xy$, the actual parent trace factors and the next two
trace factors are

$$
\begin{aligned}
\operatorname{tr}(MR)&=p+2-s,&
\operatorname{tr}(MUR)&=p+x+1-s,\\
\operatorname{tr}(A_4R)&=s,&\operatorname{tr}(QR)&=p+1,\\
\operatorname{tr}(JQR)&=s,&\operatorname{tr}(MQR)&=s+1.
\end{aligned}                                                   \tag{4.5}
$$

All are positive. These are the traces at original clocks $1,3,4,5$
and the two possible sixth actions, respectively. Equations (4.3)
continue to impose clocks zero and two as well.

## 5. MJMMJ 的任意漂移二目标排除

**定理 5.1（每个实际第五 J 纤维都没有二目标 L2）。** For every parameter
choice in Definition 4.1 and every two distinct complete targets
$W_1,W_2\in\mathcal F(C_5(Y,z))$,

$$
\neg L_2(\{W_1,W_2\},C_5(Y,z)).                              \tag{5.1}
$$

There is no common-drift, baseline-drift, gain-ray or nonzero-sixth-gain
assumption on the pair.

Proof. Suppose a fixed pair has $L_2$. For exactly two targets, this
forces equality of both sixth predictions and of all four terminal
predictions. Otherwise a separating atom, or a separating two-atom
suffix, recovers the pair with immediate readings. Apply the
four-terminal reconstruction of [V, Theorem 7.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)
to this actual cumulative $Q$.

Specifically, for either target put
$X=g(7)QP=\left(\begin{smallmatrix}A&B\\C&E\end{smallmatrix}\right)$.
The terminal predictions in chronological sixth/seventh order are

$$
\begin{aligned}
r_{MM}&=A+B+C+2E+\delta,& r_{MJ}&=A+C+E+\delta,\\
r_{JM}&=A+B+E+\delta,& r_{JJ}&=A+E+\delta.
\end{aligned}                                                   \tag{5.2}
$$

Their differences determine $B,C,E$. Since $QP$ is strictly positive
rank one, $E\ne0$ gives $A=BC/E$ and then $\delta$; $E=0$ forces
$g(7)=0$, $X=0$, and all four values equal $\delta$. Thus equal tables
give equal drift and equal $X$, for either gain sign and for zero gain.
If the common $X$ were nonzero, $Q^{-1}X=g(7)P$ and trace one would fix
the same source. The common drift and all four ancestor readings at
$0,1,2,3$, with positive trace factors, would fix the same cubic-or-lower
gain. This contradicts distinctness. Consequently the pair has

$$
\delta_1=\delta_2=d,\qquad g_1(7)=g_2(7)=0.                   \tag{5.3}
$$

This use of the terminal calculation makes no claim about sixth roots
at this different history.

First suppose $d=D_0$. Both targets are now in the precise whole
baseline-drift, root-seven class of [V, Theorem 6.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md).
Indeed clocks one and three force roots one and three, so
$g(t)=\lambda(t-1)(t-3)(t-7)$ by the initial reading. Clock two forces
$P_{21}=\varepsilon$, and the source has the form

$$
P=\begin{pmatrix}1-b&b(1-b)/\varepsilon\\\varepsilon&b\end{pmatrix},
\qquad 0<b<1.
$$

The inverse there, applied to these same actual fourth and fifth
readings, is

$$
b=\varepsilon-\frac{Y-D_0}{9\lambda}
                  +\frac{z-D_0}{16\lambda}.                  \tag{5.4}
$$

Thus the targets coincide. This disposes of the baseline case by that
existing class inverse; its denominator $\lambda$ is known nonzero.

Assume henceforth $d\ne D_0$. Put

$$
c_1=D_0-d\ne0,\qquad c_2=a_2-d.
$$

Use chart (4.4) for each target. Equality of the sixth-$M$ and sixth-$J$
predictions, whose trace difference is exactly one, gives

$$
H_1(6)=H_2(6)=k,\qquad k(s_1-s_2)=0.                         \tag{5.5}
$$

In particular either both sixth gains vanish or neither does. Both
cases must be retained.

Suppose $k=0$. In the trace-one normalization, each gain has roots six
and seven and can be written

$$
g_i(t)=(t-6)(t-7)(a+b_it),\qquad a=(a_0-d)/42.                \tag{5.6}
$$

Here $a$ is the same for the two targets. The actual readings at clocks
one and three and strict positivity give

$$
1<\frac{g_i(1)}{g_i(3)}
=\frac{\operatorname{tr}(MUP_i)}{\operatorname{tr}(MP_i)}<2.   \tag{5.7}
$$

The bounds follow from
$\operatorname{tr}(MUP)=\operatorname{tr}(MP)+P_{22}$ and
$\operatorname{tr}(MP)>P_{22}>0$. Neither sample in (5.7) vanishes,
since $c_1\ne0$. If $a=0$, nonzero $g_i$ gives the ratio $5/6$, which
is impossible. Hence $a\ne0$; put $r_i=b_i/a$. The ratio is
$5(1+r_i)/(2(1+3r_i))$. Its positivity permits only $r_i<-1$ or
$r_i>-1/3$. On $r_i<-1$ it is less than $5/6$; on $r_i>-1/3$ the two
strict bounds (5.7) are equivalent to

$$
1/7<r_i<3.                                                   \tag{5.8}
$$

All of $g_i(1),g_i(2),g_i(3)$ now have the sign of $a$. Thus $c_1,c_2$
are nonzero with that same sign. The actual matrix identity
$A_4=U+MU$ expresses the shared fourth reading as

$$
\begin{aligned}
Y-d&=F(r_i),\\
F(r)&=\frac3{10}c_2\frac{1+4r}{1+2r}
       +\frac12c_1\frac{1+4r}{1+3r},\\
F'(r)&=\frac{3c_2}{5(1+2r)^2}
       +\frac{c_1}{2(1+3r)^2}.
\end{aligned}                                                   \tag{5.9}
$$

All denominators are positive on (5.8). The derivative has one strict
sign throughout the interval, so the common $Y$ forces $r_1=r_2$.
Since $a$ is common, the entire gains coincide. With this gain the
actual readings reconstruct the source through

$$
\begin{aligned}
P_{21}&=c_2/g(2)-1,&P_{22}&=c_1/g(3)-c_1/g(1),\\
P_{12}&=c_1/g(1)-P_{21}-P_{22},&P_{11}&=1-P_{22}.
\end{aligned}                                                   \tag{5.10}
$$

The three divided samples were proved nonzero. The two complete
targets coincide, contradicting the supposed pair. This includes a
vanishing coefficient $b_i$ whenever it is compatible with the actual
readings; the inequality itself excludes incompatible values.

It remains to treat $k\ne0$. Equation (5.5) gives a common
$s=s_1=s_2>1$. Define

$$
\begin{gathered}
h=(Y-d)/s=H_i(4),\qquad w=z-d,\qquad q_i=p_i+1>0,\\
T_i=p_i+2-s>0,\qquad V_i=p_i+x_i+1-s=T_i+x_i-1>0.
\end{gathered}                                                   \tag{5.11}
$$

The actual fifth reading says $H_i(5)=w/q_i$, while $H_i(7)=0$.
Cubic interpolation at the distinct original clocks $4,5,6,7$ gives

$$
H_i(1)=20h-45w/q_i+36k,\qquad
H_i(3)=4h-6w/q_i+4k.                                         \tag{5.12}
$$

Write $A=20h+36k$ and $B=4h+4k$. The complete clock-one and clock-three
conditions on the same pair are therefore

$$
(A-45w/q_i)T_i=c_1,\qquad (B-6w/q_i)V_i=c_1
\quad(i=1,2).                                                 \tag{5.13}
$$

If $x_1=x_2$, the common $s$ gives the same $y$ and normalized source;
the four earlier readings and common drift give the same gain. Thus
$x_1\ne x_2$. If $p_1=p_2$, (5.11) and the samples at $4,5,6,7$ give
$H_1=H_2$. Since $c_1\ne0$, their common $H(3)$ is nonzero, and the
clock-three equation gives $V_1=V_2$, hence $x_1=x_2$, again impossible.
Consequently $p_1\ne p_2$.

Because $T_i=q_i-(s-1)$, subtracting the two clock-one equations in
(5.13), and dividing only by $p_1-p_2\ne0$, gives

$$
A=\frac{45w(s-1)}{q_1q_2},\qquad
c_1=-\frac{45wT_1T_2}{q_1q_2}.                               \tag{5.14}
$$

In particular $w\ne0$ is a consequence, not an initial restriction.
Set $\xi=s-x_1-x_2$. Since $p_i=x_i(s-x_i)$,

$$
p_1-p_2=(x_1-x_2)\xi,\qquad
V_1-V_2=(x_1-x_2)(\xi+1).
$$

Subtracting $B=6w/q_i+c_1/V_i$ and using (5.14) now yields

$$
2\xi V_1V_2=15(\xi+1)T_1T_2.                                \tag{5.15}
$$

For example, before canceling the nonzero $x_1-x_2$, that subtraction
is
$0=-6w(p_1-p_2)/(q_1q_2)-c_1(V_1-V_2)/(V_1V_2)$.
Thus no sign of $h,k,w$ was selected and no minor or ancestor sample
was divided out.

Since all $T_i,V_i$ are positive, (5.15) permits only $\xi>0$ or
$\xi<-1$; the endpoints zero and minus one cannot satisfy it. If
$\xi>0$, then

$$
T_i=2-x_i+(x_i-1)y_i>1/2,\qquad
\frac{V_i}{T_i}=1+\frac{x_i-1}{T_i}<2.
$$

Equation (5.15) would require
$V_1V_2/(T_1T_2)=15(\xi+1)/(2\xi)>15/2$, while the left side is
less than four. This is a contradiction.

If $\xi<-1$, put $\rho=-\xi-1>0$, $x_1=1+a$, $x_2=1+b$.
The source bounds and $y_i=s-x_i>0$ give

$$
0<\rho<a,b<1/2,\qquad y_1=b-\rho,\quad y_2=a-\rho,
$$

and hence

$$
V_1=1+a(b-\rho),\quad V_2=1+b(a-\rho),\quad
T_1=V_1-a,\quad T_2=V_2-b.                                   \tag{5.16}
$$

For fixed $\rho$, consider the positive ratio
$R(a,b)=V_1V_2/(T_1T_2)$ on this rectangle. The exact derivative is

$$
\partial_a\log R=\frac1{V_1T_1}-\frac{b^2}{V_2T_2}
>\frac45-\frac12=\frac3{10}>0.                              \tag{5.17}
$$

Indeed $1\le V_i<5/4$ and $1/2<T_i<1$ throughout the rectangle
including its lower edges, so $V_1T_1<5/4$, $V_2T_2>1/2$ and
$b^2<1/4$. The same calculation holds for $\partial_b\log R$.
The denominators remain positive as $a,b$ decrease to $\rho$, yielding

$$
R(a,b)\ge R(\rho,\rho)=\frac1{(1-\rho)^2}.                  \tag{5.18}
$$

On the other hand (5.15) would require
$R(a,b)=15\rho/[2(1+\rho)]$. For $0<\rho<1/2$,

$$
\begin{aligned}
2(1+\rho)-15\rho(1-\rho)^2
&=2-13\rho+30\rho^2-15\rho^3\\
&=\frac{45}{2}\left(\rho-\frac{13}{45}\right)^2
  +\frac{11}{90}+15\rho^2(1/2-\rho)>0.
\end{aligned}                                                   \tag{5.19}
$$

Thus $15\rho/[2(1+\rho)]<1/(1-\rho)^2$, contradicting (5.18).
Both signs allowed by (5.15) are excluded.

The baseline drift, the nonbaseline drift with zero sixth gains, and
the nonbaseline drift with nonzero sixth gains exhaust the pair. Each
contradiction concerns the same two worlds and their entire actual
history (4.3). The polynomial factorizations and interpolations included
all lower degrees, repeated roots and additional sampled roots. All
divisors were established nonzero within their respective cases. This
proves (5.1). ∎

## 6. 任意漂移的整族策略与至少三目标子纤维

**定理 6.1（每个实际小纤维上的同一恢复策略）。** Fix the parameters
$D_0,\lambda,\varepsilon$ in Definition 4.1.

1. For any $Y$ and any known $K\subseteq\mathcal F(C_4(Y))$, if every
   actual fifth-$J$ response fiber $K_z=K\cap\mathcal F(C_5(Y,z))$
   has at most two distinct targets, one deterministic strategy
   recovers all of $K$ within three further readings.
2. For any known $K\subseteq\mathcal F(C_3)$, if every actual
   fourth-$M$, fifth-$J$ joint response fiber has at most two distinct
   targets, one deterministic strategy recovers all of $K$ within four
   further readings.

Both assertions permit infinite families, varying actual response
values, mixed drifts and arbitrary legal gain shapes and signs.

Proof. In the first assertion execute fifth $J$ and immediately read
$z$. Stop if $K_z$ is a singleton. If $K_z$ contains a pair, Theorem
5.1 excludes $L_2$ for this actual pair. Select the first word in
$MM,MJ,JM,JJ$ for which the pair's sixth or seventh predictions differ.
Execute its sixth atom and read; stop if it separates, otherwise
execute and read its seventh atom. Equality of all these predictions
would be exactly two-target $L_2$, so a separating word always exists.
The returned target is the unique member matching the acquired
history. This choice uses the whole known actual $K_z$, not an unknown
choice of pair in a larger fiber. Empty fibers are unreachable.

For the second assertion execute fourth $M$ and read its actual $Y$;
then execute fifth $J$ and read its actual $z$. The retained joint
fiber is now a singleton or the pair just treated, so use only the
remaining two-atom separating rule. The fifth $J$ is already acquired
and is not repeated by invoking the first assertion's continuation.

There is one policy for every actual $Y,z$ and every retained target.
Its choices can depend arbitrarily on the known family and the
actual reads; no regularity assumption or extra counterfactual
acquisition is needed. The budgets are $5+1+2=8$ and $4+2+2=8$,
respectively. All acquired atoms are individually read on original
clocks through seven. ∎

**推论 6.2（同历史失败族的基数必要条件）。** For arbitrary compatible
families, with no drift promise,

$$
L_3(K,C_4(Y))\ \Longrightarrow\
\exists z:\ L_2(K_z,C_5(Y,z))\ \land\ |K_z|\ge3.               \tag{6.1}
$$

In particular, if $|K|=3$ and $K$ has $L_3$ at this $C_4(Y)$, its
fifth-$J$ prediction is constant on all three targets. Moreover any
$L_4$ family at this same $C_3$ retains, after some actual fourth-$M$
reading $Y$ and actual fifth-$J$ reading $z$, an $L_2$ subfiber with
at least three targets.

Proof. The failure recursion supplies an actual fifth-$J$ child with
$L_2$. It has at least two targets, and Theorem 5.1 excludes exactly
two, so it has at least three. When $K$ itself has three targets this
child equals all of $K$. At $C_3$, first unfold the recursion at fourth
$M$ to get an actual $Y$ child with $L_3$, and then apply (6.1) to that
same child's fifth $J$. All ancestor equations and all worlds are
retained by these intersections. ∎

## 7. 数学接口与剩余问题

**约定 7.1（复用范围与文献条件）。** The root-six injection,
two-target $MMJMJ$ exclusion, root-five inverse, trace-coordinate
inverse and positive $MMJM$ chart used above are the specified results
of [II](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), Sections
52–53, 58 and 69. The sparse common-fifth exclusion and its conditional
three-target consumer are those of [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md),
Theorem 2.1 and Corollary 4.1, using [IV, Theorem 7.1 and Corollary
7.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) within their stated
joint fiber. The baseline $MJMMJ$ inverse in (5.4) is V, Theorem 6.1.
Theorem 3.1 supplies the common-fifth hypothesis
only for exactly three targets at (1.3); Theorem 5.1 concerns instead
every actual fifth-$J$ fiber of (4.1).

The following primary mathematical interfaces have different premises
from any unrestricted acquisition-count theorem in Definition 1.1.

| Mathematical source | Correspondence and precise restriction |
| --- | --- |
| Yanjun Li, Kiryung Lee, Yoram Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1) | Identifiability requires every compatible solution to lie in the specified transformation orbit. Theorem 2.8 requires one factor's orbit identification and conditional identification of the remaining factor. Here trace one removes positive source/gain scaling; additive drift remains a target coordinate. These conditions provide neither the fixed $M/J$ original-clock model nor its adaptive reading budget. |
| Petra van den Bos, Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [Theorem 6.1 and Example 7](https://arxiv.org/html/1907.11034v2) | The theorem assumes a suspension automaton with all distinct state pairs incompatible, and injective splits in the splitting-graph construction. Example 7 has an adaptive distinguishing graph missed by that construction when compatible pairs exist. No such automaton identification is imposed here; the whole-known-family policies above follow from actual response fibers and their stated cardinality bounds. |
| Michael Kech, Felix Krahmer, *Optimal Injectivity Conditions for Bilinear Inverse Problems*, [Theorems III.1–III.3](https://arxiv.org/html/1603.07316v1) | The lower bound assumes stable injectivity on the specified complex rank-one domain. The upper bounds quantify over almost all linear maps or structured measurement maps. Neither stability on that complex domain nor an almost-all measurement choice identifies this positive real domain with unknown additive drift, fixed atoms and arbitrary deterministic feedback. Their numerical thresholds are not reading bounds for (1.1). |

Polynomial interpolation, the rank-one identity $AE=BC$, trace
normalization and strict monotonicity are the algebraic tools in the
displayed proofs. V's Bernstein certificate concerns its particular
ancestor determinant and enters Theorem 3.2 through V, Corollary 4.1.

**开放问题 7.2（完整实际纤维与原根）。** Determine whether

$$
\exists Y\in\mathbb R:
L_3(\mathcal F(H_4(Y)),H_4(Y))                                \tag{7.1}
$$

holds. Any such family needs at least four distinct targets by
Theorem 3.2. This is a necessary bound on a losing family, not a
three-target extraction theorem or a bound on the cardinality of a
complete fiber. A nonconstant fifth function on a larger family can
retain an actual child of size at least three. The pairs colliding
under different sixth or seventh actions may differ. Their common
ancestor constraints remain simultaneous obligations.

At (4.1), determine whether a family with $L_3$ can retain an actual
fifth-$J$ child with at least three targets and jointly realize the
opposite fifth arm's losing child. Theorem 5.1 excludes the
two-target alternative only. It supplies neither recovery of every
larger child nor a uniform decoder for the entire $C_4(Y)$ fiber.
The different complementary $JMMJ$ history of V, Definition 5.1,
including its nonbaseline-drift pairs, remains a separate problem;
the coordinates and ancestor equations (4.2) do not identify it with
$MJMMJ$.

Determine the original full-domain alternative
$n_{\mathrm{det}}(3,0)\ge9$ versus existence of a lawful decoder with
at most eight total readings. It includes every initial action,
subsequent actual history and early stop in Definition 1.1. Neither
(3.2) nor (6.1) supplies a complete original-root failure tree or a
full-domain decoder. Feasibility of the sixteen-slot local and
256-slot root systems of IV, Theorems 9.2–9.3, is a separate
simultaneous realization question. The finite linear-palette
obstruction of IV, Theorem 10.2, retains its specified readout
architecture and does not decide nonlinear recovery. The known-family
conditions in Theorems 3.3 and 6.1 are sufficient conditions, not
certificates that an unrestricted observed target satisfies them.

## 追加锚（本行以下为增补区）

## 8. 非零偏离父族上的精确 MM 碰撞与末 J 分离

**定义 8.1（保留前三次动作的两参数父族）。** 使用定义 1.1 的整个 $\mathcal W_3$、原时钟及完整目标。对 $s,t>0$ 置

$$
\begin{gathered}
P(s,t)=\frac1{1+st}\begin{pmatrix}1&t\\s&st\end{pmatrix},\qquad
u_0=\operatorname{tr}(MP)=\frac{s+t+st}{1+st},\\
n=\operatorname{tr}(JM^2P)=1+\frac{2s+t}{1+st},\qquad
 a=\operatorname{tr}(MJM^2P)=\frac{1+s+2t+3st}{1+st},\\
h=\nu_0(\nu_0+1),\qquad \ell=\nu_0^2+3\nu_0-4,\\
\Delta=nh+an\ell-4ah,\qquad
\Phi=(3h-10)a+(8\nu_0^2+18\nu_0-30)n-23h.
\end{gathered}                                                     \tag{8.1}
$$

每个严格正秩一迹一矩阵唯一具有这个形式：$s=P_{21}/P_{11}$、$t=P_{12}/P_{11}$，其余元素由秩一和迹一确定。为与本卷此前符号区分，$\nu_0$ 表示 V 第29章的 $u$。以下所有 $h,n$ 都严格正。

给定任意 $d\in\mathbb R$，令 $g_{s,t,d}$ 是在时钟 $0,1,2,3$ 分别取值

$$
-d,\qquad -d/\nu_0,\qquad -d/(1+\nu_0),\qquad (6-d)/n
\tag{8.2}
$$

的唯一至多三次多项式。记 $W(s,t,d)=(P(s,t),g_{s,t,d},d)$。这些世界恰为整个实际历史 $(0,M,0,M,0,J,6)$ 的纤维；$g$ 不可能恒零，因为时钟零与三的读数不同。前两次 $M$ 和其立即读数始终保留。

对实参数 $\theta,\xi$ 定义六读父历史

$$
H^-_{\theta,\xi}=(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta+\xi)).
\tag{8.3}
$$

$\xi=0$ 时回到 [V，定义31.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) 的字面父历史；这里不限制 $\xi$。

**定理 8.2（无除数父条件与两项实际响应不变量）。** 世界 $W(s,t,d)$ 属于 $\mathcal F(H^-_{\theta,\xi})$，当且仅当

$$
d\Delta=24h(\theta n-a),\qquad d\Phi=120h\xi.
\tag{8.4}
$$

因此整个父纤维保留 $\Delta=0$ 的可能性。若 $\xi\ne0$，则 $d\ne0,\Phi\ne0$，且

$$
k=\frac an,\qquad q=\frac{5\Delta}{n\Phi},\qquad
 d=\frac{120h\xi}{\Phi},\qquad \theta=k+\xi q.
\tag{8.5}
$$

这里的 $q$ 是源函数。置

$$
\begin{gathered}
V_6=10\nu_0^2+19\nu_0-36,\qquad X_7=20\nu_0^2+34\nu_0-70,\\
\Psi_6=(n+2a)V_6-10a\ell-29h,\\
\Psi_7=4(2n+3a)X_7-105a\ell-381h,\\
\mu=\Psi_6/\Phi,\qquad \eta=\Psi_7/\Phi.
\end{gathered}                                                     \tag{8.6}
$$

从同一父历史依次实际执行第六、七动作 $M,M$，读数记 $w,m$；若在第七时钟改选 $J$，其互择读数记 $j$。则

$$
\begin{aligned}
w&=120(1+2\theta)+120\xi\mu,\\
m&=210(2+3\theta)+30\xi\eta,\\
j&=d+(4n-\nu_0+1)\left[\frac{210}{n}
+d\left(\frac{X_7}{h}-\frac{35}{n}\right)\right].
\end{aligned}                                                     \tag{8.7}
$$

证明。令 $E=d\Delta-24h(\theta n-a)$。四节点插值在时钟四、五的读数残差为

$$
\begin{aligned}
a g(4)+d-24\theta&=\frac{E}{nh},\\
(n+a)g(5)+d-60(1+\theta+\xi)
&=\frac{5E}{2nh}+\frac{d\Phi-120h\xi}{2h}.
\end{aligned}                                                     \tag{8.8}
$$

所以给(8.4)，且没有除以 $\Delta$。当 $\xi\ne0$ 时，第二式才允许除 $\Phi$；代回第一式得到(8.5)，包括 $\Delta=0$ 的来源。

同一整个插值多项式满足

$$
g(6)=\frac{120}{n}+d\left(\frac{V_6}{h}-\frac{20}{n}\right),\qquad
g(7)=\frac{210}{n}+d\left(\frac{X_7}{h}-\frac{35}{n}\right).
\tag{8.9}
$$

实际累计矩阵在时钟五、六及两个互择的时钟七，分别给迹 $n+a,n+2a,2n+3a,4n-\nu_0+1$。将(8.9)代入 $d+\operatorname{tr}(A_iP)g(i)$，再使用 $\theta=a/n+d\Delta/(24hn)$，即得

$$
w-120(1+2\theta)=d\Psi_6/h,\qquad
m-210(2+3\theta)=d\Psi_7/(4h),
$$

继而得到(8.7)。这些等式比较的是声明的真实接续，未同时取得两个互择的第七读数。$\square$

**定义 8.3（有理矩形内的唯一来源）。** 令

$$
\begin{gathered}
x_1=(1,8/5),\qquad
F(s,t)=\begin{pmatrix}\mu(s,t)-\mu(x_1)\\\eta(s,t)-\eta(x_1)\end{pmatrix},\\
c_s=1.3668354280688564193145835408836333031459902242674,\\
c_t=1.5901260498010329978871678969013649280689869011129,\\
c=(c_s,c_t),\qquad r=10^{-30},\qquad
B=[c_s-r,c_s+r]\times[c_t-r,c_t+r].
\end{gathered}                                                     \tag{8.10}
$$

全部有限小数均是精确有理数。定义精确有理矩阵

$$
C=\begin{pmatrix}
904.93210381774114595014897571659013569&-66.32150200441973789392504996729505825\\
-55.00399809630821426212726430454664348&3.55838270959647055443328665173286166
\end{pmatrix}.
\tag{8.11}
$$

下条定理给 $F$ 在 $B$ 内的唯一零点 $x_2$。随后所有 $k_i,q_i,h_i,\Phi_i$ 及其他源函数都指在 $x_i$ 的取值，而非在近似中心的取值。

**定理 8.4（非零偏离下的完整目标碰撞与另一末动作分离）。** 定义8.3中的唯一零点 $x_2$ 存在，且为严格正来源。置

$$
\xi_* =\frac{k_2-k_1}{q_1-q_2},\qquad
\theta_*=k_1+\xi_*q_1,\qquad
 d_i=\frac{120h_i\xi_*}{\Phi_i},\qquad W_i=W(x_i,d_i).
\tag{8.12}
$$

这些表达式的分母非零，两个 $W_i$ 是不同的合法完整世界，并且

$$
\begin{gathered}
-0.962<\xi_*<-0.961,\qquad 0.420<\theta_*<0.422,\\
12.407<d_1<12.408,\qquad12.271<d_2<12.272,\\
W_1,W_2\in\mathcal F(H^-_{\theta_*,\xi_*}),\qquad
w(W_1)=w(W_2),\quad m(W_1)=m(W_2),\\
-0.028<j(W_1)-j(W_2)<-0.027.
\end{gathered}                                                     \tag{8.13}
$$

两个增益还满足 $g_i(j)<0$（整数 $0\le j\le4$）及 $g_i(j)>0$（整数 $5\le j\le7$），所以全部八个采样点的增益均非零。特别地，不存在对全部非零 $\xi$ 父历史均正确的固定 $MM$ 完整目标解码器。对仅含这两个世界的集合，第六 $M$ 之后不满足 $L_1$，因为末 $J$ 将它们分开；该两点结论不排除整个实际子纤维中的其他末 $J$ 碰撞。

证明。先给出定义8.3中存在与唯一性的有理证书。向量范数取最大绝对坐标，矩阵范数取最大绝对行和。将每个有理函数先约为整数系数多项式之比，再依次按 $t,s$ 作 Horner 区间求值。加减取相应端点，乘法取四个端点积的最小和最大值，除法仅在整个分母区间不含零时取倒数相乘。这些规则对(8.10)的整个闭矩形给

$$
\begin{gathered}
\Phi(B)\subset(-40,-39),\qquad
\|CF(c)\|_\infty<10^{-40},\\
\sup_{x\in B}\|I-CDF(x)\|_\infty<10^{-20}.
\end{gathered}                                                     \tag{8.14}
$$

上式的最后界可具体由同一逐项区间雅可比 $[DF](B)$ 验算：令 $R=I-C[DF](B)$，对其每一行将两个分量区间端点的最大绝对值相加，所得行和小于 $10^{-20}$。所有除数区间均排除零；$1+st,h,n$ 的正性也由矩形的正坐标直接给出。这里(8.1)、(8.6)、(8.10)—(8.11)完整指定了证书的有理输入，不依赖近似根相等。

考虑 $T(x)=x-CF(x)$。由(8.14)，$T$ 在凸矩形上为 Lipschitz 常数小于 $10^{-20}$ 的压缩，且

$$
\|T(x)-c\|_\infty
\le\|CF(c)\|_\infty+10^{-20}\|x-c\|_\infty
<10^{-40}+10^{-50}<r.
\tag{8.15}
$$

故 $T(B)\subset B$。从任一点迭代 $T$，相邻差按几何级数衰减，得到 $B$ 中的 Cauchy 列；其极限为唯一不动点。矩阵 $C$ 非奇异：由 $\|I-CDF(c)\|<1$，$CDF(c)$ 可逆，因而方阵 $C$ 可逆。不动点遂是 $F$ 的零点；反之每个零点都是不动点。这就是这里使用的标准压缩映射论证，而非以有限近似迭代代替存在性。

对 $x_1$ 和整个 $B$ 使用同一有理区间规则，还得到

$$
\begin{array}{c|c}
\Phi_1&(-40,-39)\\
\Phi_2&(-40,-39)\\
q_1-q_2&(0.003453,0.003455)\\
k_2-k_1&(-0.003323,-0.003322)\\
\xi_*&(-0.962,-0.961)\\
\theta_*&(0.420,0.422)\\
d_1&(12.407,12.408)\\
d_2&(12.271,12.272)\\
w&(86,87)\\
m&(256,257)\\
j(W_1)-j(W_2)&(-0.028,-0.027).
\end{array}                                                       \tag{8.16}
$$

在计算读数行时，先以(8.12)求 $\xi_*,\theta_*,d_i$ 的区间，再分别使用(8.7)的三个有理式；区间变量允许独立扩大，仍给所列严格包含。因此这些界在 $B$ 的唯一零点处成立。源 $x_2$ 的第一坐标大于 $1.36$，而 $x_1$ 的第一坐标为一，故两个来源不同；两个漂移的区间也不交。严格正、秩一及迹一由(8.1)保证，整个增益由(8.2)保证。

(8.12)给同一个 $\theta_*=k_i+\xi_*q_i$，故(8.5)与定理8.2保证两个世界实现完全相同的六读父历史。$F(x_2)=0$ 则精确给 $\mu_1=\mu_2,\eta_1=\eta_2$，由(8.7)得到 $w,m$ 的精确相等。末 $J$ 的严格差界已经在(8.16)给出。

最后核对采样增益的符号。时钟零、一、二的负号由 $d_i>0$ 和(8.2)给出；时钟三由 $d_i>6$ 给出。时钟四的共同读数小于 $24\cdot0.422<d_i$，所以 $g_i(4)<0$。时钟五的共同读数大于 $60(1+0.420-0.962)=27.48>d_i$；时钟六、七分别有 $w>86$、$m>256$，也都大于 $d_i$。各实际迹严格正，故得到所列正负号；没有用采样增益为零来隐藏这些步骤。

因此固定八读动作词 $MMJMMMM$ 在这些完整目标上不单射，即使实际父参数承诺 $\xi\ne0$ 也如此。令 $K=\{W_1,W_2\}$，其第六 $M$ 实际子族仍为 $K$；在该子历史末 $J$ 的每个响应子族至多一个元素，故定义1.1的 $L_1$ 全称动作条款失败。整个 $\mathcal F(H^-_{\theta_*,\xi_*},M,w)$ 可以含有其他世界，不能用 $K$ 的结论代替其分类，更不能据固定 $MM$ 碰撞宣告同父 $L_2$。

这里的承重新增是非零 $\xi$、非零且不同漂移下的实际完整目标对、精确同父条件及互择末动作分离，属于本仓构造（repo-derived）。有限插值、有理区间包含、压缩映射及迹线性是成熟的中间工具。Li、Lee、Bresler 的[变换群识别框架，Definition 2.7 与 Theorem 2.8](https://arxiv.org/html/1501.06120v1)以所有兼容解的轨道识别为条件；这里没有把含加性漂移的指定轨迹归约到其无漂移双线性应用，亦不以该文替代(8.14)—(8.16)的构造。该引用只定位识别问题的既有框架，不申领文献首创。$\square$

## 追加锚（本行以下为增补区）

## 9. 八读 MM 碰撞在父参数平面的开集上持续

**定理 9.1（非零采样增益的开父族）。** 存在包含 $(\theta_*,\xi_*)$ 的非空开集

$$
U\subset(0.420,0.422)\times(-0.962,-0.961)
\tag{9.1}
$$

及定义在 $U$ 上的两族完整世界 $W_1(\theta,\xi),W_2(\theta,\xi)$，满足以下全部条件：每个世界合法，两者来源不同、漂移不同且严格为正；两者实现同一个 $H^-_{\theta,\xi}$；固定接续 $MM$ 的两个读数分别相同；互择末 $J$ 的读数差位于 $(-0.028,-0.027)$。其整个增益满足

$$
g_i(j)<0\quad(0\le j\le4),\qquad
g_i(j)>0\quad(5\le j\le7),\qquad j\in\mathbb Z.
\tag{9.2}
$$

来源、漂移和增益的系数均可取为父参数的实解析函数。因此，固定八读动作词 $MMJMMMM$ 的非单射性在这个两参数历史平面的非空开集上持续，而非仅由一个孤立参数实现。

证明。令 $\mathcal A=(\mu,\eta)$，记定义8.3的两来源为 $x_1,x_2$。由(8.14)，$D\mathcal A(x_2)$ 可逆。实解析隐函数定理给 $x_1$ 附近的解析函数 $y(x)$，满足

$$
y(x_1)=x_2,\qquad \mathcal A(y(x))=\mathcal A(x),\qquad
Dy(x)=D\mathcal A(y(x))^{-1}D\mathcal A(x).
\tag{9.3}
$$

缩小邻域可使 $x,y(x)$ 都严格正、彼此不同，且两个 $\Phi$ 和 $q(x)-q(y(x))$ 都非零。定义

$$
\begin{gathered}
K(x)=k(y(x))-k(x),\qquad Q(x)=q(x)-q(y(x)),\\
\xi(x)=K(x)/Q(x),\qquad
\theta(x)=k(x)+\xi(x)q(x),\qquad
\Pi(x)=(\theta(x),\xi(x)).
\end{gathered}                                                     \tag{9.4}
$$

关键是父参数并未因该来源延拓而局限于一条曲线。下面给 $D\Pi(x_1)$ 的有理区间证书。置 $H=D\mathcal A(x_2)^{-1}D\mathcal A(x_1)$；所有微分在对应来源处取值，则

$$
\begin{aligned}
dK&=dk(x_2)H-dk(x_1),\\
dQ&=dq(x_1)-dq(x_2)H,\\
d\xi&=(Q\,dK-K\,dQ)/Q^2,\\
d\theta&=dk(x_1)+q(x_1)d\xi+\xi_*dq(x_1).
\end{aligned}                                                     \tag{9.5}
$$

在(8.10)的整个 $B$ 上用二阶矩阵求逆公式及(8.14)的同一有理区间规则，$\det D\mathcal A$ 的除数区间排除零，且得到

$$
\begin{array}{c|c}
\partial_s\theta&(-0.003419,-0.003418)\\
\partial_t\theta&(-0.121730,-0.121728)\\
\partial_s\xi&(0.001017,0.001018)\\
\partial_t\xi&(0.143586,0.143588)\\
\det D\Pi(x_1)&(-0.000368,-0.000366).
\end{array}                                                       \tag{9.6}
$$

此处 $x_1=(1,8/5)$ 保持精确，只有 $x_2$ 在 $B$ 上作区间扩大；(9.3)的隐导数使用同一实际来源对。(9.5)完整指定了(9.6)所需的有理运算，不能把两个独立最优导数拼成该表。

由行列式严格非零，实解析逆函数定理给 $\Pi$ 在 $x_1$ 的一个邻域上为到开像的解析双射。取其开像的小邻域为 $U$。对每个 $(\theta,\xi)\in U$，用 $x=\Pi^{-1}(\theta,\xi)$ 和 $y(x)$，再以(8.5)定义各自漂移及(8.2)的整个增益。由(9.3)，两个来源的 $\mu,\eta$ 精确相同；由(9.4)，两者父参数相同。定理8.2于是供应全部父读数及两个接续 $M$ 的逐项相等。

定理8.4给出的来源分离、两个正漂移的分离、末 $J$ 差界及有限个采样增益的严格符号都是开条件。各源函数与四节点插值的系数在所取邻域解析；继续缩小 $U$，这些条件同时保持，并保证(9.1)。这给全部结论。

本定理的开集指规定了前三次动作和前四读数的二参数历史平面，不是全部八读数据空间中的开集。每个父历史上的这对世界仍被末 $J$ 分开，故其两点子族不满足 $L_1$；整个实际子纤维的 $L_1$、同父的 $L_2$ 以及原根八读／九读判别仍需其他世界的共同兼容证明。没有把两种互择末响应当成共同取得的额外记录。

承重增量为(9.6)的实际父映射非退化性及其开父族消费者，属于本仓综合推导（repo-derived）。实解析隐函数与逆函数定理、矩阵求逆及严格不等式的局部保持是成熟中间工具；来源对与完整目标合同直接消费第8章，不另作孤立点的重复构造，也不申领文献首创。$\square$

## 追加锚（本行以下为增补区）


## 10. 非零偏离实际子纤维的完整三来源分类与末 J 恢复

**定义 10.1（保留全部世界的锚定子历史）。** 使用定义1.1的整个来源域与定义8.1的实际父历史，不限制漂移、增益符号或次数。置

$$
\begin{gathered}
I_\xi=[-0.961942514933679944270,\,-0.961942514933679944269],\\
\xi_0=-0.961942514933679944270,\qquad
\mu_0=\frac{100975}{86354},\\
\theta_\xi=\frac{50}{31}+\frac{1658645}{1338487}\xi,\qquad
w_\xi=120(1+2\theta_\xi)+120\xi\mu_0,\\
C_\xi=(H^-_{\theta_\xi,\xi},M,w_\xi),\qquad
K_\xi=\mathcal F(C_\xi).
\end{gathered}                                                     \tag{10.1}
$$

全部有限小数是精确有理数。$\xi_0$ 是区间左端点。$C_\xi$ 保留原时钟零至六的全部七个读数。其首四读仍为 $(0,M,0,M,0,J,6)$；没有把初始两个 $M$ 或立即读数删除。锚定来源 $x_1=(1,8/5)$ 的迹坐标为 $(u,n,a)=(21/13,31/13,50/13)$，其 $k,q,\mu$ 恰为(10.1)的三个系数。因此每个 $K_\xi$ 都含该来源对应的完整世界，但定义不把其他世界排除。

**引理 10.2（完整子纤维的迹坐标消元）。** 对 $\xi\in I_\xi$，每个 $K_\xi$ 世界唯一对应一个实三元组 $(u,n,a)$。其来源矩阵为

$$
P(u,n,a)=
\begin{pmatrix}
n-1-3u+a&n-3-4u+2a\\
1+2u-a&2+3u-n-a
\end{pmatrix}.                                                    \tag{10.2}
$$

四项严格正，且

$$
\mathcal C=a^2-an-2au-2a-n^2+4nu+2n-u^2+u+1=0.
\tag{10.3}
$$

以下 $h,\ell,\Delta,\Phi$ 使用(8.1)，把 $\nu_0$ 写为 $u$。置

$$
\begin{gathered}
D=560615u^2+387907u-1753578,\\
A=55740u^2-176824u-79494,\qquad
N=181841h-An,\\
\widehat\Phi=(3h-10)N+(8u^2+18u-30)nD-23hD,\\
\widehat\Delta=nhD+Nn\ell-4Nh,\\
F=N^2-NnD-2N(u+1)D
  +(-n^2+4nu+2n-u^2+u+1)D^2,\\
G=\frac{1}{43177}\left[
\bigl((2158850+1658645\xi)nD-1338487N\bigr)\widehat\Phi
-6692435\xi D\widehat\Delta\right].
\end{gathered}                                                     \tag{10.4}
$$

每个合法来源都有 $D\ne0$，且 $a=N/D$。在这些条件下，子纤维方程恰为 $F=G=0$、(10.2)四项正及 $\Phi\ne0$。完整世界由

$$
d=120h\xi/\Phi
\tag{10.5}
$$

及(8.2)的唯一整个增益恢复。

以 $n$ 为消元变量，有精确多项式恒等式

$$
\operatorname{Res}_n(F,G)=8(13u-21)D^4R(u,\xi),
\qquad \deg_uR=15,\quad\deg_\xi R=2.
\tag{10.6}
$$

(10.4)与(10.6)唯一指定这里的有理系数多项式 $R$。记 $F,G$ 关于 $n$ 的一次子结式为

$$
S_1(u,n,\xi)=\sigma_1(u,\xi)n+\sigma_0(u,\xi).
\tag{10.7}
$$

在下条定理列出的全部候选区间，$F,G$ 的二次首项系数及 $\sigma_1$ 都非零。因此每个候选 $u$ 至多给一个来源，且必须有 $n=-\sigma_0/\sigma_1$。

证明。对一般迹一矩阵写成 $\begin{pmatrix}p&q\\r&1-p\end{pmatrix}$。其三个实际迹给 $u=q+r+1-p$、$n=1+q+2r$、$a=3-2p+r+2q$；反解得到(10.2)，行列式展开给(10.3)。这不是给任意对称矩阵加上的来源假设。

由定理8.2及 $\xi\ne0$，父条件给(10.5)和 $\theta=k+\xi q$；第六 $M$ 的实际读数则给 $\mu=\mu_0$。后一等式恰为

$$
Da+An-181841h=0.
\tag{10.8}
$$

不能直接假设 $D\ne0$。$D$ 在正半轴严格递增，其唯一正根位于 $(7/5,3/2)$。在该闭区间 $A<0$，而合法来源有 $n>0,h>0$；故 $D=0$ 时(10.8)不可能成立。这排除了整个例外分支。

代入 $a=N/D$ 后，$D^2\mathcal C=F$，且

$$
\frac{1338487D^2}{43177}
\bigl((\theta_\xi n-a)\Phi-5\xi\Delta\bigr)=G.
\tag{10.9}
$$

所有除数已非零，故这些等式可双向使用；没有除以 $\Delta$。关于 $n$ 的 Sylvester 行列式直接给(10.6)，子结式序列的次数依次为 $2,2,1,0$，给(10.7)。下条定理的区间非零证书保证这些式子在全部可能合法根处都能回代。

反向，(10.2)严格正及(10.3)给严格正秩一迹一来源。父残差与第六读数由(10.8)–(10.9)和定理8.2给出；(8.2)的增益不可能恒零，因为首四读不恒定。故恢复的是整个完整目标。$\square$

**定理 10.3（整个实际子纤维恰有三个来源）。** 对每个 $\xi\in I_\xi$，$K_\xi$ 恰含三个不同完整世界。其来源分别是锚定来源、下表 $U_3$ 内唯一根对应的来源、以及 $U_4$ 内唯一根对应的来源。末 $J$ 的读数分别位于

$$
\begin{array}{c|c}
\text{来源}&\text{原时钟七的 }J\text{ 读数}\\ \hline
u=21/13&(145.762,145.763)\\
u\in U_3&(95.366,95.368)\\
u\in U_4&(145.789,145.791).
\end{array}                                                       \tag{10.10}
$$

证明。先给覆盖整个正实轴的实根证书，而非只包围已知来源。对(10.6)的 $R$，在整个 $I_\xi$ 上，其 $u^{15}$ 系数、常数项、$R(21/13,\xi)$ 及 $\operatorname{Disc}_uR$ 都非零；前三项的符号依次为 $+,-,+$。判别式的非恒定本原因子次数及重数为 $1^2,1^2,1^2,9^2,32^1$，每个因子在该区间都排除零。

这些非零界可用以下精确区间规则重算：先把待验一元多项式在 $\xi_0$ 作精确移位，令 $v=\xi-\xi_0\in[0,10^{-21}]$，再按 $v$ 作 Horner 区间求值。加减取端点，乘法取四个端点积；判别式可按上述本原因子逐项求值。不能用未移位的、存在大幅相关抵消的区间失败来宣告判别式为零。

在基点 $\xi_0$，用 $R,\partial_uR$ 及负余式递推组成 Sturm 链。其在零与正无穷的符号分别为

$$
\begin{aligned}
&(-,-,+,-,-,-,+,-,-,-,+,-,-,-,+,+),\\
&(+,+,+,+,+,+,-,-,+,+,+,+,+,+,+,+).
\end{aligned}                                                     \tag{10.11}
$$

变号数分别为七与二，故恰有五个正实根。首项、常数与判别式在整个连通区间不消失，保证次数不降、根不穿过零且不出现重根；首项在紧参数区间远离零还给统一有限根界。因而正根数在整个 $I_\xi$ 恒为五。

下面五个互不相交的闭有理区间覆盖这五个根。每行左右端点的 $R(u,\xi)$ 符号对整个 $I_\xi$ 都为所列值：

$$
\begin{array}{c|c|c|c}
&\text{左端点}&\text{右端点}&\text{端点符号}\\ \hline
U_1&0.426517059293639&0.426517059293642&(-,+)\\
U_2&1.168158226005415&1.168158226005419&(+,-)\\
U_3&1.583353993785919&1.583353993785924&(-,+)\\
U_4&1.616668692509694&1.616668692509700&(+,-)\\
U_5&5.694613617156701&5.694613617156708&(-,+).
\end{array}                                                       \tag{10.12}
$$

端点按 $\xi$ 作有理 Horner 区间求值即可；每行至少含一个根，根数总计为五，故每行恰一个，没有遗漏其他正根。(10.6)余下的正候选只有 $u=21/13$；$D$ 的根已由引理10.2排除。

对每个 $U_i\times I_\xi$，以及 $\{21/13\}\times I_\xi$，对原始一次子结式的 $\sigma_1$、$F,G$ 的二次首项及回代的各分母作同样的有理区间核对，全部排除零。这里必须检查原始 $\sigma_1$，不能只在约分后的 $-\sigma_0/\sigma_1$ 看不到分母零就忽略可能被约掉的公共因子。

回代 $n=-\sigma_0/\sigma_1$、$a=N/D$ 后，四个来源元素的符号分类为

$$
\begin{array}{c|c}
\text{候选}&\text{整个区间上的严格分类}\\ \hline
21/13&\text{四项均正}\\
U_1&P_{11}<0,\ P_{12}<0\\
U_2&P_{12}<0,\ P_{22}<0\\
U_3&\text{四项均正，且 }\Phi\ne0\\
U_4&\text{四项均正，且 }\Phi\ne0\\
U_5&P_{11}<0,\ P_{12}<0.
\end{array}                                                       \tag{10.13}
$$

锚定来源也有 $\Phi\ne0$。这些是整个根区间的包含界，不是在近似根上检查符号。对两个合法非锚定根，$F,G$ 的二次首项均非零，结式为零保证共同复根存在；一次子结式的非零系数迫使该根唯一且等于实数 $-\sigma_0/\sigma_1$。所以它确实解原来的两个方程。引理10.2给其合法完整世界。三个不同 $u$ 保证三个来源不同；上表排除了其他全部候选。

最后按(8.7)的末 $J$ 式，用这些有理区间回代 $d=120h\xi/\Phi$，得到(10.10)的三个不交区间。全部分母的非零性均已核对，故读数分离对整个 $I_\xi$ 成立。$\square$

**推论 10.4（已知 MM 碰撞所在的整个实际子纤维可由 J 恢复）。** 对所有 $\xi\in I_\xi$，

$$
\neg L_1(K_\xi,C_\xi).
\tag{10.14}
$$

从这个实际历史只须再执行并读取一个 $J$，即可恢复完整目标。可用阈值 $100$ 与 $145.775$：低于第一阈值对应 $U_3$，两阈值之间对应锚定来源，高于第二阈值对应 $U_4$；随后用唯一根、(10.2)、(10.5)及整个四节点插值恢复 $P,g,d$。这是原精确实数合同中的解码器，不附加有限精度或有效实数表示承诺。

证明。定理10.3给末 $J$ 在整个 $K_\xi$ 上单射，故其每个实际响应子纤维至多一个完整目标，$L_1$ 的该动作条款失败。两阈值严格落在三个读数区间之间，给所述策略。

定义8.3的整个来源矩形还给

$$
\xi_*\in\operatorname{int}I_\xi.
\tag{10.15}
$$

直接把 $k_2-k_1$ 与 $q_1-q_2$ 在该矩形上作有理区间求值，再相除即可；其分母已在(8.16)排除零。因此定理8.4的两个世界属于这里的完整三世界子纤维，原先未认证的第三来源由定理10.3补全，而末 $J$ 对全部三者均有效。

这个结论只处理(10.1)的一个指定实际第六响应族。它没有排除同一父历史的其他第六 $M$ 响应含有 $L_1$，也没有处理第六 $J$ 臂，故不能推出全部父纤维的 $\neg L_2$。第9章的二维开父族与这里固定 $\mu_0$ 的一参数历史线也没有被认作同一个范围。原始根八读／九读问题仍未结算。

承重增量是实际完整子纤维的无遗漏三来源分类及其统一末动作恢复，属于仓内综合推导（repo-derived）。迹坐标、Sylvester 结式、一次子结式、Sturm 链及简单实根的参数稳定性是成熟工具；(8.1)–(8.9)是直接消费的既有接口。没有把高次数消元、多项式命名或数值根列表本身算成新数学内容，也不申领文献首创。$\square$

## 追加锚（本行以下为增补区）

## 11. 完整三来源分类的开邻域稳定性及开父族上的恢复

**定义 11.1（三参数实际子历史）。** 保留整个 $\mathcal W_3$ 和原时钟、完整目标。对 $\alpha=(\theta,\xi,\mu)$、$\xi\ne0$，置

$$
C_\alpha=(H^-_{\theta,\xi},M,120(1+2\theta)+120\xi\mu),\qquad
K_\alpha=\mathcal F(C_\alpha),\qquad
\alpha_*=(\theta_*,\xi_*,\mu_0).
\tag{11.1}
$$

这里的 $\mu$ 是指定实际第六响应的坐标，不是对来源再加的先验。来源变量仍为(10.2)的 $(u,n,a)$，并沿用 $h,\ell,\Phi,\Delta$。定义

$$
\begin{aligned}
D_\mu&=10u^2+8u-32-\mu(3h-10),\\
A_\mu&=10u^2+19u-36-\mu(8u^2+18u-30),\\
N_\mu&=(29-23\mu)h-A_\mu n,\\
\widehat\Phi_\mu&=(3h-10)N_\mu+(8u^2+18u-30)nD_\mu-23hD_\mu,\\
\widehat\Delta_\mu&=nhD_\mu+N_\mu n\ell-4N_\mu h,\\
F_\mu&=N_\mu^2-N_\mu nD_\mu-2N_\mu(u+1)D_\mu\\
&\hspace{1em}+(-n^2+4nu+2n-u^2+u+1)D_\mu^2,\\
G_\alpha&=(\theta nD_\mu-N_\mu)\widehat\Phi_\mu
          -5\xi D_\mu\widehat\Delta_\mu,\\
\mathscr R(u,\alpha)&=\operatorname{Res}_n(F_\mu,G_\alpha).
\end{aligned}                                                     \tag{11.2}
$$

**定理 11.2（整个实际子纤维在三参数开邻域中仍恰有三支）。** 存在 $\alpha_*$ 的非空开邻域 $V\subset\{\xi\ne0\}$，使每个 $K_\alpha$ 恰含三个完整世界。三个世界的来源、漂移和整个增益的系数均为 $\alpha$ 的实解析函数。按基点的三个来源标号后，末 $J$ 读数仍分别位于(10.10)的三个区间，故末 $J$ 在整个 $K_\alpha$ 上单射。

证明。先核对一般消元及基点的次数。实际第六读数条件为 $\Psi_6=\mu\Phi$，展开恰给

$$
D_\mu a=N_\mu.
\tag{11.3}
$$

若 $D_\mu\ne0$，代入 $a=N_\mu/D_\mu$，则 $F_\mu=D_\mu^2\mathcal C$，$G_\alpha=D_\mu^2((\theta n-a)\Phi-5\xi\Delta)$。若 $D_\mu=0$，(11.3)又迫 $N_\mu=0$，从而在实际 $(u,n)$ 上仍有 $F_\mu=G_\alpha=0$。所以每个合法来源的 $u$ 都是 $\mathscr R$ 的根；这一必要条件没有遗漏不能作除法的来源。

$F_\mu,G_\alpha$ 关于 $n$ 的次数至多二，关于 $u$ 的次数至多六。四阶 Sylvester 行列式遂给 $\deg_u\mathscr R\le24$。在 $\mu=\mu_0,\theta=\theta_\xi$ 上，与(10.4)的多项式有精确比例

$$
F_\mu=\frac F{86354^2},\qquad
G_\alpha=\frac G{31\cdot86354^2},\qquad
\mathscr R(u,\alpha)=
\frac{8(13u-21)D^4R(u,\xi)}{31^2\,86354^8}.
\tag{11.4}
$$

这些等式只需在(11.2)中代入 $\mu_0,\theta_\xi$；结式对两个二次多项式的缩放次数各为二。(10.15)使基点位于此前证书内部。因此 $\mathscr R(u,\alpha_*)$ 确有次数二十四，首项及常数非零。其三个合法来源的 $u$ 根均简单：$D$ 在这些根非零，$R$ 的根简单，且 $R(21/13,\xi_*)\ne0$。

对这三个简单实根应用实解析隐函数定理，取得三个互不相交的局部实根支。取 $F_\mu,G_\alpha$ 关于 $n$ 的原始一次子结式。在这三点，它的一次系数以及两个二次首项由第10章非零；(11.4)中的非零常数缩放不改变这些性质。缩小邻域后它们仍非零，故唯一共同根为该一次式的实解析零点。结式为零且二次首项非零保证共同复根存在；一次子结式迫它恰为这个实根。继而由 $a=N_\mu/D_\mu$ 解析恢复 $a$。来源的四项正、$\Phi\ne0$ 持续成立；(10.5)和(8.2)解析恢复唯一完整世界。末 $J$ 的严格区间也连续保持。这先给至少三个世界及每支附近的唯一性，尚未排除远处或边界进入的第四个世界。

为完成全体分类，反设任意小邻域都有这三支以外的合法世界。取 $\alpha_j\to\alpha_*$ 及这样的来源 $P_j$。二十四次首项在一个闭参数小邻域远离零，其余有限个系数有界。由多项式根的 Cauchy 界，所有 $u_j$ 一致有界；这个结论对 $D_{\mu_j}=0$ 的来源也成立，因为已经证明其 $u_j$ 仍使结式为零。对正迹一矩阵写 $P_j=\begin{pmatrix}p_j&q_j\\r_j&s_j\end{pmatrix}$，有

$$
0<p_j,s_j<1,\qquad 0<q_j,r_j\le q_j+r_j=u_j-s_j\le u_j.
\tag{11.5}
$$

故来源矩阵存在收敛子列，极限 $P_\infty$ 非负、秩一、迹一。其 $u_\infty\ge0$；基点结式常数非零排除 $u_\infty=0$，故 $h_\infty>0$，并有 $n_\infty=1+q_\infty+2r_\infty\ge1$。将连续等式(11.3)取极限，乘以 $86354$ 得

$$
D(u_\infty)a_\infty+A(u_\infty)n_\infty
=181841h_\infty.
\tag{11.6}
$$

若 $D(u_\infty)=0$，则其正根位于 $(7/5,3/2)$，此处 $A<0$；(11.6)左侧负、右侧正，矛盾。这个排除对非负边界同样成立，不需要极限来源严格正。

于是 $D(u_\infty)\ne0$，极限来源可用第10章完整消元回代。它的 $u_\infty$ 只能是锚点或五个 $U_i$ 内的根；原始一次子结式迫 $n_\infty,a_\infty$ 也取该候选的唯一值。三个非法候选各有严格负元素，与 $P_\infty\ge0$ 矛盾。余下三个候选全都严格正且 $\Phi\ne0$，正是已建的三支基点。

因此 $P_j$ 的这个子列最终进入某一支的局部唯一邻域。该处(11.2)的简单根及一次子结式只容许已经构造的来源；(10.5)与初始插值又只容许一个完整世界，矛盾。特别地，没有额外漂移或增益能经 $\Phi\to0$ 隐藏进入，因为极限来源已被迫落在 $\Phi\ne0$ 的三点之一。

故某个开邻域只有这三个世界。再缩小，使来源正性、三个末 $J$ 区间及 $\xi\ne0$ 同时保持，得到 $V$。这里不声称已给出 $V$ 的显式半径。$\square$

**推论 11.3（开父族中的指定 MM 碰撞子历史全部可由 J 恢复）。** 定理9.1的 $U$ 可以缩小为仍包含 $(\theta_*,\xi_*)$ 的非空开集 $U'$，使其中每个已构造 MM 碰撞所在的整个实际第六-$M$ 子纤维恰有三个完整世界，且

$$
\neg L_1\bigl(K_{\alpha(\theta,\xi)},C_{\alpha(\theta,\xi)}\bigr),
\qquad
\alpha(\theta,\xi)=
\bigl(\theta,\xi,\mu(x(\theta,\xi))\bigr).
\tag{11.7}
$$

这里 $x=\Pi^{-1}(\theta,\xi)$ 是第9章同一父族的第一来源。

证明。$\alpha$ 为实解析，且把基点送到 $\alpha_*$。因此 $U'=U\cap\alpha^{-1}(V)$ 是所需非空开邻域。第9章两世界的 $\mu$ 相等，故它们正属于(11.7)的同一个实际子历史。定理11.2的全体分类和末 $J$ 单射性给结论；读到 $J$ 后，按(10.10)的区间分支和唯一解析世界恢复完整目标。没有把未执行的末 $M,J$ 响应共同算作数据。$\square$

**命题 11.4（实际响应邻域与自适应下界的范围）。** 定理11.2给三参数实际子历史中的恢复开邻域，推论11.3给其与第9章开父族的接合；它们均不推出任一完整父纤维的 $\neg L_2$，也不结算原根八读／九读问题。

证明。父 $L_2$ 在每个可选第六动作下只需存在一个仍有 $L_1$ 的实际响应。这里仅排除已指定响应及其开邻域，未排除同父其他响应，更未穷尽第六 $J$ 臂。反之，固定 $MM$ 碰撞在 $U'$ 上仍由第9章保留，却已在整个对应子纤维被末 $J$ 解开，所以不能继续把这一族当作末层自适应失败见证。下一项失败构造必须在同一实际子历史上同时实现两种末动作各自的碰撞，允许两对世界不同，并继续满足共同父约束。$\square$

本章的承重接合是(11.5)–(11.6)排除远方及非负边界新来源，并将第10章全体分类接到第9章开父族。它是仓内综合推导（repo-derived），不申领文献首创。实解析隐函数定理、子结式、Cauchy 根界与有限维紧性是成熟工具；只延拓三个已知解的局部隐函数定理不足以替代这里的全体排除。全文保持普通数学证明层级，不声称新增 Lean 核验。

## 追加锚（本行以下为增补区）

## 12. 非零采样增益下两种末动作的共同碰撞

**定义 12.1（三元共同碰撞方程）。** 使用定义8.1的整个正来源、原时钟及完整目标，不添加漂移或增益符号承诺。对正数 $s$ 和 $x=(t_1,s_2,t_2)$，令 $z_1=(s,t_1)$、$z_2=(s_2,t_2)$。所有带下标的 $u_i,n_i,a_i,h_i,\Phi_i,k_i,q_i,\mu_i,\eta_i$ 都是(8.1)、(8.5)–(8.6)在 $z_i$ 的值。仅在 $\Phi_1\Phi_2(q_1-q_2)\ne0$ 的区域定义

$$
\begin{gathered}
\xi_s(x)=\frac{k_2-k_1}{q_1-q_2},\qquad
\theta_s(x)=k_1+\xi_s(x)q_1,\qquad b_i=\frac{120h_i}{\Phi_i},\\
B_i=\frac{210(4n_i-u_i+1)}{n_i},\\
C_i=b_i\left[1+(4n_i-u_i+1)
       \left(\frac{20u_i^2+34u_i-70}{h_i}-\frac{35}{n_i}\right)\right],\\
\mathscr F_s(x)=
\begin{pmatrix}
\mu_1-\mu_2\\
\eta_1-\eta_2\\
B_1-B_2+\xi_s(x)(C_1-C_2)
\end{pmatrix}.
\end{gathered}                                                     \tag{12.1}
$$

$B_i+\xi C_i$ 正是(8.7)的末 $J$ 读数，其中 $d_i=b_i\xi$。故 $\mathscr F_s=0$ 的三项分别要求同一个实际第六-$M$ 响应、同一个末 $M$ 响应及同一个末 $J$ 响应；共同父参数由 $\theta_s,\xi_s$ 的定义强制满足。

**定理 12.2（合法非对角零点的有理盒）。** 置 $s_0=1/128$。以下小数全部是精确有理数：

$$
\begin{gathered}
c=\begin{pmatrix}
1.4705556548179257340150455245744131098602\\
0.1320274660921843741654131371468169037723\\
1.4248118101895048849927107012897929305742
\end{pmatrix},\qquad r=10^{-20},\qquad
\mathcal B=c+[-r,r]^3,\\
R_0=\begin{pmatrix}
284.329638772264&-18.286694831022&-0.303823228329\\
-634.527234441023&37.304215035556&-0.236600678710\\
616.589185355469&-38.236478833295&-0.303695123964
\end{pmatrix}.
\end{gathered}                                                     \tag{12.2}
$$

则 $\mathscr F_{s_0}$ 在 $\mathcal B$ 内恰有一个零点 $x_\dagger$。整个盒都在定义12.1的合法区域内，且

$$
\begin{gathered}
-46<\Phi_1<-45,\qquad -47<\Phi_2<-46,\\
0.013<q_1-q_2<0.014,\qquad
0.13<s_2<0.14,\qquad t_1,t_2>0,\\
0.4415<\theta_{s_0}<0.4416,\qquad
-1.126<\xi_{s_0}<-1.125,\\
1.439<\mu_1<1.440,\qquad 19.296<\eta_1<19.297.
\end{gathered}                                                     \tag{12.3}
$$

证明。对(12.1)的有理表达式及其乘积、倒数导数逐项作有理区间包含，得到

$$
\|R_0\mathscr F_{s_0}(c)\|_\infty<10^{-34},\qquad
\sup_{x\in\mathcal B}\|I-R_0D_x\mathscr F_{s_0}(x)\|_\infty<10^{-8}.
\tag{12.4}
$$

这里的矩阵范数为最大绝对行和。可用固定网格 $10^{-100}\mathbb Z$ 重算这些严格包含：加减取端点，乘法取四个端点积，倒数在不跨零区间上交换端点后取倒数；每步下端向下、上端向上舍入。导数使用 $(fg)'=f'g+fg'$ 和 $(1/f)'=-f'/f^2$，对三个变量分别传递。对中心单点和整个盒使用同一规则，第一项上界小于 $4.235\cdot10^{-41}$，第二项上界小于 $7.667\cdot10^{-11}$，均严格小于(12.4)的较宽有理界。同样的区间四则运算给(12.3)，并排除所有倒数分母为零；这些界覆盖整个盒，不只近似零点。

令 $T(x)=x-R_0\mathscr F_{s_0}(x)$。由(12.4)，$T$ 在凸盒上是 Lipschitz 常数小于 $10^{-8}$ 的压缩，且

$$
\|T(x)-c\|_\infty<10^{-34}+10^{-8}r<r.
\tag{12.5}
$$

因此 $T$ 映盒入自身内部。沿用定理8.4的压缩映射论证，迭代给盒内唯一不动点。由 $\|I-R_0D_x\mathscr F_{s_0}(c)\|<1$，乘积矩阵可逆，故 $R_0$ 可逆；不动点恰为 $\mathscr F_{s_0}$ 的零点。来源坐标 $s_0<0.13<s_2$ 排除两来源相同。$\square$

**定理 12.3（同一实际子纤维的二目标 $L_1$）。** 在 $x_\dagger$ 处令 $\theta_\dagger=\theta_{s_0}(x_\dagger)$、$\xi_\dagger=\xi_{s_0}(x_\dagger)$、$\mu_\dagger=\mu_1$，并令

$$
\begin{gathered}
d_i=120h_i\xi_\dagger/\Phi_i,\qquad
W_i=\bigl(P(z_i),g_{z_i,d_i},d_i\bigr),\qquad K_\dagger=\{W_1,W_2\},\\
w_\dagger=120(1+2\theta_\dagger)+120\xi_\dagger\mu_\dagger,\qquad
C_\dagger=(H^-_{\theta_\dagger,\xi_\dagger},M,w_\dagger),
\end{gathered}                                                     \tag{12.6}
$$

其中 $g_{z_i,d_i}$ 是(8.2)的同一个整个插值多项式。则两个世界合法、不同，均属 $\mathcal F(C_\dagger)$，且

$$
L_1(K_\dagger,C_\dagger),\qquad
L_1(\mathcal F(C_\dagger),C_\dagger).
\tag{12.7}
$$

两个世界都有严格正且不同的漂移、实际次数三的增益，并在时钟零至七的每个采样点具有非零增益。其符号依次为

$$
\begin{array}{c|rrrrrrrr}
&0&1&2&3&4&5&6&7\\ \hline
g_1&-&-&-&-&-&+&+&+\\
g_2&-&-&-&-&+&+&+&+
\end{array}
\tag{12.8}
$$

证明。定义12.1及 $\mathscr F_{s_0}(x_\dagger)=0$ 给

$$
k_1+\xi_\dagger q_1=k_2+\xi_\dagger q_2=\theta_\dagger,\qquad
\mu_1=\mu_2,\qquad \eta_1=\eta_2,\qquad
B_1+\xi_\dagger C_1=B_2+\xi_\dagger C_2.
\tag{12.9}
$$

由定理8.2，前两个父条件与插值恰保证两个完整世界共享整个 $H^-_{\theta_\dagger,\xi_\dagger}$，$\mu$ 相等又给同一个实际第六-$M$ 响应 $w_\dagger$。末 $M$ 的读数为 $210(2+3\theta_\dagger)+30\xi_\dagger\eta_i$，末 $J$ 为 $B_i+\xi_\dagger C_i$，因此两种末动作各自都在同一对世界上碰撞。$W_1\ne W_2$ 已由来源坐标分离保证，故两动作的相应实际响应子纤维都含两个不同目标；递归(1.2)给第一式，再由包含单调性给第二式。没有要求同时取得两种末读数。

具体合法性可在整个 $\mathcal B$ 上核对。正来源由正坐标与(8.1)给出。(12.3)使 $\xi_\dagger,\Phi_i$ 都非零，且

$$
10.724<d_1<10.726,\qquad 10.446<d_2<10.448.
\tag{12.10}
$$

把(8.2)的四个值代入四节点 Lagrange 插值后，(12.4)使用的同一区间规则给下表严格包含。最后一行是三次项系数。

$$
\begin{array}{c|c|c}
&g_1&g_2\\ \hline
g(4)&(-0.033,-0.032)&(0.038,0.040)\\
g(5)&(1.283,1.285)&(1.360,1.362)\\
g(6)&(2.013,2.015)&(2.095,2.097)\\
g(7)&(2.136,2.137)&(2.209,2.211)\\
[t^3]g&(-0.003624,-0.003622)&(-0.005617,-0.005614)
\end{array}
\tag{12.11}
$$

前四个增益的负号由 $d_i>6$、$u_i,n_i>0$ 和(8.2)直接得到；(12.11)给后四个符号及次数恰三。故没有用采样增益为零隐藏读数。共同实际第六读数及两种互择末读数的区间为

$$
w_\dagger\in(31.561,31.562),\qquad
y_{7,M}\in(46.517,46.518),\qquad
y_{7,J}\in(30.816,30.817).
\tag{12.12}
$$

这些区间只定位已经由(12.9)证明精确相等的读数，不用小误差代替相等。$\square$

**推论 12.4（变化父历史上的解析末层失败曲线）。** 存在 $s_0$ 的开区间 $I$ 及实解析 $x(s)$，满足 $x(s_0)=x_\dagger$、$\mathscr F_s(x(s))=0$。相应两世界及其共同实际子历史满足定理12.3的全部严格合法性、符号及 $L_1$ 结论，且父参数确实变化。在基点有

$$
-0.003198<\frac{d\theta_s(x(s))}{ds}\Big|_{s=s_0}<-0.003197,
\qquad
0.001637<\frac{d\xi_s(x(s))}{ds}\Big|_{s=s_0}<0.001638.
\tag{12.13}
$$

证明。(12.4)使 $D_x\mathscr F_{s_0}(x_\dagger)$ 可逆，故实解析隐函数定理给该曲线，严格不等式通过缩小 $I$ 同时保持。为确认不是恒定父历史的重复参数化，置 $J_x=D_x\mathscr F_s$、$v=-\partial_s\mathscr F_s$。对 $s=s_0,x\in\mathcal B$ 的区间微分给

$$
0.065969<\det J_x<0.065970.
\tag{12.14}
$$

按 Cramer 法则以 $v$ 替换 $J_x$ 的第 $j$ 列，除以该行列式，得到 $x'_j(s_0)$ 的区间；再使用 $d\theta/ds=\partial_s\theta+D_x\theta\,x'$ 及 $\xi$ 的同一式，给(12.13)。这些区间都使用同一个 $x_\dagger\in\mathcal B$，没有拼合分别取得的导数最优值。于是缩小区间后 $\theta$ 严格递减，所构成的是不同实际父历史的一条曲线，而非父参数平面的开集。$\square$

**命题 12.5（前移一个动作即可分开这对，但不排除其他父层见证）。** 从同一个 $H^-_{\theta_\dagger,\xi_\dagger}$ 出发，第六动作选 $J$ 时，两个世界的实际响应分别在

$$
(22.6855,22.6857),\qquad(22.6935,22.6938).
\tag{12.15}
$$

因此这对世界在父历史可由一次 $J$ 恢复，不能单凭(12.7)推出整个父纤维的 $L_2$；原根八读／九读问题也未由此结算。

证明。该实际第六-$J$ 累积矩阵的迹是 $1+2n_i$，原读数为 $d_i+(1+2n_i)g_i(6)$。用(12.2)同一盒及插值的区间包含给(12.15)，故这对在该动作下分开。父 $L_2$ 还需要第六 $J$ 有一个实际响应子纤维保留 $L_1$，其见证可以来自其他世界，仍须与同一个完整父历史兼容。第11章的恢复开邻域和本章失败曲线属于不同参数区域；前者没有被本章推翻，后者也没有提供原始根的完整失败树。$\square$

本章新增的是非零偏离、不同正漂移及所有采样增益非零时，两种末动作在同一实际子纤维上的共同二目标碰撞，以及父参数变化的解析延拓，属于仓内构造与综合推导（repo-derived）。压缩映射、区间包含、Lagrange 插值、隐函数定理与 Cramer 法则是成熟中间工具；完整目标与实际读数的回接直接复用定理8.2。这里不申领文献首创，也不把数值近似当作零点存在性。

## 追加锚（本行以下为增补区）

## 13. 非零偏离开父族上的固定 JJ 碰撞

**定义 13.1（实际 J 臂的响应函数）。** 保留定义8.1的整个正来源、完整目标与原时钟，以下 $u=\nu_0$。在 $\Phi\ne0$ 的来源上置

$$
\begin{gathered}
b=120h/\Phi,\qquad \beta=120/n,\\
\gamma=b[1+(1+2n)(V_6/h-20/n)],\\
\zeta=\{b[1+(n+a)(X_7/h-35/n)]-210q\}/30.
\end{gathered}                                                     \tag{13.1}
$$

对两个来源 $z_i=(s_i,t_i)$，在 $\Phi_1\Phi_2(q_1-q_2)\ne0$ 时定义

$$
\begin{gathered}
\xi=(k_2-k_1)/(q_1-q_2),\qquad \theta=k_1+\xi q_1,\\
F_{s_1,s_2}(t_1,t_2)=
\begin{pmatrix}\zeta_1-\zeta_2\\
[\beta_1-\beta_2+\xi(\gamma_1-\gamma_2)]/100\end{pmatrix}.
\end{gathered}                                                     \tag{13.2}
$$

所有带下标源函数都在对应的同一个来源处取值。

**定理 13.2（原时钟 J 臂恒等式）。** 在父历史 $H^-_{\theta,\xi}$ 上，第六动作实际选 $J$ 的读数及其后两个互择末读数为

$$
w_J=240+\beta+\xi\gamma,\qquad
r_{JJ}=210(1+\theta)+30\xi\zeta,\qquad
r_{JM}=d+(u+2a)g(7),\quad d=b\xi.
\tag{13.3}
$$

证明。时钟五的实际累计矩阵及第六、七步矩阵是

$$
\begin{gathered}
A_5=M^2JM^2=\begin{pmatrix}2&3\\3&4\end{pmatrix},\qquad
JA_5=\begin{pmatrix}3&4\\2&3\end{pmatrix},\\
MJA_5=\begin{pmatrix}2&3\\5&7\end{pmatrix},\qquad JJA_5=A_5.
\end{gathered}                                                     \tag{13.4}
$$

它们的迹读出为 $n+a,1+2n,u+2a,n+a$。将(8.9)的同一个整个多项式代入 $d+\operatorname{tr}(A_iP)g(i)$，得到

$$
\begin{aligned}
w_J&=b\xi+(1+2n)[120/n+b\xi(V_6/h-20/n)],\\
r_{JJ}&=210(n+a)/n+b\xi[1+(n+a)(X_7/h-35/n)].
\end{aligned}                                                     \tag{13.5}
$$

使用 $\theta=a/n+\xi q$ 即得(13.3)。两次 $J$ 虽使累计矩阵回到 $A_5$，增益仍从原时钟五变成七；没有重置时钟或插入空动作读数。$\square$

**定理 13.3（非对角零点的精确盒）。** 固定 $s_1=1/128,s_2=1/8$。所有有限小数均是精确有理数，令

$$
\begin{gathered}
c_1=1.70063246334455220821050734320735763312171885152510278572642768284003767091,\\
c_2=1.73669835798369801498718890571098163831164200326868628871046700585854159548,\\
c=(c_1,c_2),\quad r=10^{-20},\quad \mathcal B=c+[-r,r]^2,\\
R_0=\begin{pmatrix}
0.710232231649885952492271652426&16.9933215528503526086581264972\\
1.03488459475917806450248509213&23.8588533025301271599379779751
\end{pmatrix}.
\end{gathered}                                                     \tag{13.6}
$$

则 $F_{1/128,1/8}$ 在 $\mathcal B$ 内恰有一个零点 $x_*$。整个盒都在定义13.1的合法区域内，且

$$
\begin{gathered}
-25.188<\Phi_1<-25.187,\qquad-26.272<\Phi_2<-26.271,\\
-0.019527<q_1-q_2<-0.019526,\\
0.9414<\theta<0.9415,\qquad-0.4436<\xi<-0.4435.
\end{gathered}                                                     \tag{13.7}
$$

证明。使用定理12.2的有理区间规则，对(8.1)、(8.5)、(13.1)–(13.2)及其乘积、倒数导数逐项包含；固定网格可取 $10^{-100}\mathbb Z$。全部除数区间排除零，并得(13.7)及

$$
\begin{gathered}
\|R_0F(c)\|_\infty<3.327\cdot10^{-75}<10^{-60},\\
\sup_{x\in\mathcal B}\|I-R_0D_xF(x)\|_\infty
 <1.614\cdot10^{-14}<10^{-8},\\
-1.560550<\det D_xF<-1.560548.
\end{gathered}                                                     \tag{13.8}
$$

矩阵范数是最大绝对行和：先对每个雅可比分量取区间，再将每行绝对上界求和。这些界覆盖整个盒。令 $T(x)=x-R_0F(x)$，则它为压缩且

$$
\|T(x)-c\|_\infty<10^{-60}+10^{-8}r<r.
\tag{13.9}
$$

定理8.4的压缩论证给盒内唯一不动点；$\|I-R_0DF(c)\|<1$ 使 $R_0$ 可逆，故不动点恰为零点。两个来源第一坐标固定不同，因而来源对非对角。$\square$

**定理 13.4（完整目标碰撞与另一末动作分离）。** 在 $x_*$ 处按(13.2)定义共同父参数，令 $d_i=b_i\xi$、$W_i=W(z_i,d_i)$。两个世界合法、不同，共享同一个 $H^-_{\theta,\xi}$，且

$$
w_J(W_1)=w_J(W_2),\qquad r_{JJ}(W_1)=r_{JJ}(W_2).
\tag{13.10}
$$

它们的漂移严格正且不同，增益实际次数均为三，时钟零至七的采样增益符号均为 $(-,-,-,-,+,+,+,+)$；但

$$
3.080<r_{JM}(W_2)-r_{JM}(W_1)<3.081.
\tag{13.11}
$$

证明。共同父由(13.2)和定理8.2保证，$F(x_*)=0$ 与(13.3)精确给(13.10)。对整个 $\mathcal B$ 上同一完整插值的有理区间包含给

$$
\begin{array}{c|c|c}
&W_1&W_2\\ \hline
d&(9.6908,9.6909)&(9.3701,9.3702)\\
g(4)&(2.938,2.940)&(3.065,3.067)\\
g(5)&(11.318,11.320)&(11.590,11.592)\\
g(6)&(25.750,25.751)&(26.306,26.307)\\
g(7)&(48.215,48.217)&(49.225,49.226)\\
[t^3]g&(0.33028,0.33029)&(0.33537,0.33539)\\
r_{JM}&(515.011,515.012)&(518.091,518.092).
\end{array}                                                       \tag{13.12}
$$

同一包含给 $d_1-d_2\in(0.320,0.322)$、(13.11)及已经精确相等的读数位置

$$
w_J\in(174.170,174.171),\qquad r_{JJ}\in(351.269,351.270).
\tag{13.13}
$$

前四个增益的负号由 $d_i>6$ 与(8.2)得到，后四个及次数由(13.12)得到。因此固定 $JJ$ 的确失败，末 $M$ 却分开本对。对仅含本对的实际第六-$J$ 子族，$L_1$ 不成立；整个子纤维是否另有末 $M$ 碰撞，不由本对决定。读数区间只定位已证明相等的值，不承担相等性证明。$\square$

**定理 13.5（固定 JJ 碰撞的开父族）。** 存在父参数平面中的非空开集

$$
U_J\subset(0.9414,0.9415)\times(-0.4436,-0.4435)
\tag{13.14}
$$

使每个父记录都有实解析依赖于父参数的两完整世界，满足定理13.4的全部结论。

证明。令 $p=(s_1,s_2)$、$x=(t_1,t_2)$、$p_0=(1/128,1/8)$。(13.8)与实解析隐函数定理给 $p_0$ 附近的解 $x(p)$。记 $\Pi(p,x)=(\theta,\xi)$、$\widehat\Pi(p)=\Pi(p,x(p))$，则

$$
x_p=-(D_xF)^{-1}D_pF,\qquad
D_p\widehat\Pi=D_p\Pi+D_x\Pi\,x_p.
\tag{13.15}
$$

在同一个精确零点 $x_*\in\mathcal B$ 上作四变量区间微分，以(13.8)和二阶逆公式求逆，给

$$
0.0063056358<\det D_p\widehat\Pi(p_0)<0.0063056361.
\tag{13.16}
$$

逆函数定理给实际父平面的非空开像。缩小开像，保持来源不同、漂移不同且正、真实三次项、全部采样非零及(13.11)，得到结论。这里没有拼合分别取得的导数最优值；开集只在声明的两参数父历史平面中，未声称任意八读数据空间中的开集，也未给显式邻域半径。$\square$

本章新增的是指定实际 $JJ$ 路径的完整目标碰撞及实际父参数开像，属于仓内构造（repo-derived）。压缩映射、实解析函数定理、有限插值与迹线性均为成熟工具。第12章末层共同碰撞曲线与本章开族属于不同父区域；固定字失败没有被提升为自适应失败。

## 追加锚（本行以下为增补区）

## 14. 实际 J 子记录上两种末动作的共同失败

**定义 14.1（保留共同父的 J 臂四元方程）。** 在定义13.1的源函数之外置

$$
\tau=(u+2a)/n,\qquad
\varpi=b[1+(u+2a)(X_7/h-35/n)]/210.
\tag{14.1}
$$

给定 $\lambda>0$ 和 $x=(s,t_1,t_2,\xi)$，使用同一对正来源 $z_1=(s,t_1)$、$z_2=(\lambda s,t_2)$。令 $\delta f=f(z_1)-f(z_2)$，定义

$$
\mathcal G_\lambda(x)=
\begin{pmatrix}
\delta k+\xi\delta q\\
(\delta\beta+\xi\delta\gamma)/120\\
\delta\tau+\xi\delta\varpi\\
\delta\zeta
\end{pmatrix}.
\tag{14.2}
$$

这里只除以各来源的 $1+st,n,h,\Phi$，不除以 $q_1-q_2$。第一项为零强制共同父 $\theta=k_1+\xi q_1=k_2+\xi q_2$；其余三项分别强制实际第六-$J$、末 $M$ 及末 $J$ 读数相等，最后一项使用 $\xi\ne0$。其中

$$
r_{JM}=210(\tau+\xi\varpi).
\tag{14.3}
$$

**定理 14.2（共同 J 碰撞的四维精确盒）。** 固定 $\lambda_0=2$。以下有限小数均为精确有理数，令

$$
\begin{aligned}
c_1&=5.2008815849346999818362170155313688221858456187015196988684064776295048101404306257591623736606,\\
c_2&=0.036765592638387180576299121214778623123798351197348295804260552271822645927517285853154444956258,\\
c_3&=0.019946210824298202645970048551951627266006239530300549721844726706873952998532787749158758893992,\\
c_4&=-0.84564016224047725877333250816943180760191942516023718775642804632165163001070490657785295376237.
\end{aligned}                                                     \tag{14.4}
$$

置 $c=(c_1,c_2,c_3,c_4)$、$r=10^{-24}$、$\mathcal C=c+[-r,r]^4$，定义精确有理矩阵

$$
R_1=\begin{pmatrix}
-4622.23118933957524055934326589182921346779591&4703.50916392475756007517078806914091434374841&-499.025761959425030857016947992154853004599776&357.052703862742354114700193108543328354863962\\
-94.9985096929377347905814962593445415361329474&91.8104088380380174513784260941214127061913827&-6.79410735411003357884533052940016105609670667&8.26430113679682917456474494916715443710151693\\
-123.845948031399411187337125745712437718320872&116.551370190834562128550069707103786987646977&-6.62087073461630471526640684294757807220808971&10.4804112743487580557842430613808967076230937\\
8.25772099399987462793407831689885176419010091&-41.224811757219182965911635356375127030203148&36.933917049960014670665576224186732190776119&0.592250364976610285735674951395287250728918737
\end{pmatrix}.
\tag{14.5}
$$

则 $\mathcal G_2$ 在 $\mathcal C$ 中恰有一个零点 $x_\ddagger$。盒内来源严格正，全部除数非零，且

$$
\begin{gathered}
1927<\Phi_1<1928,\qquad14156<\Phi_2<14157,\qquad
0.048<q_1-q_2<0.049,\\
0.2801<\theta<0.2802,\qquad-0.8457<\xi<-0.8456,
\quad\theta=k_1+\xi q_1.
\end{gathered}                                                     \tag{14.6}
$$

证明。对(8.1)、(8.5)、(13.1)、(14.1)–(14.2)使用定理13.3的有理区间规则和逐变量微分，得到(14.6)及

$$
\begin{gathered}
\|R_1\mathcal G_2(c)\|_\infty<5\cdot10^{-92}<10^{-70},\\
\sup_{x\in\mathcal C}\|I-R_1D_x\mathcal G_2(x)\|_\infty
 <1.746\cdot10^{-16}<10^{-8}.
\end{gathered}                                                     \tag{14.7}
$$

取 $10^{-100}\mathbb Z$ 网格、每步外向取整即可重算；乘积、倒数及导数规则与定理12.2相同。矩阵界为四行各自四项绝对上界之和的最大值，覆盖整个盒。正坐标与(14.6)排除全部倒数分母为零。令 $T(x)=x-R_1\mathcal G_2(x)$，则

$$
\|T(x)-c\|_\infty<10^{-70}+10^{-8}r<r.
\tag{14.8}
$$

它是闭盒自映射及压缩。定理8.4的不动点证明适用于四维盒；(14.7)又使 $R_1D_x\mathcal G_2(c)$、从而 $R_1$ 可逆，不动点恰为唯一零点。来源第一坐标为 $s$ 与 $2s$，$s>0$ 排除来源相同。$\square$

**定理 14.3（非零采样增益的实际 J 子纤维 L1）。** 在 $x_\ddagger$ 处置 $\theta_\ddagger=k_1+\xi_\ddagger q_1$、$d_i=b_i\xi_\ddagger$、$W_i=W(z_i,d_i)$，并令

$$
\begin{gathered}
w_\ddagger=240+\beta_1+\xi_\ddagger\gamma_1,\\
C_\ddagger=(H^-_{\theta_\ddagger,\xi_\ddagger},J,w_\ddagger),
\qquad K_\ddagger=\{W_1,W_2\}.
\end{gathered}                                                     \tag{14.9}
$$

两个完整世界合法、不同，且

$$
L_1(K_\ddagger,C_\ddagger),\qquad
L_1(\mathcal F(C_\ddagger),C_\ddagger).
\tag{14.10}
$$

两个漂移严格负且不同，两个增益实际次数均为三，时钟零至七的采样增益符号均为 $(+,+,+,+,+,+,+,-)$。

证明。$\mathcal G_2(x_\ddagger)=0$ 的第一项及 $d_i=b_i\xi_\ddagger$ 经定理8.2给完整共同父历史。第二项给相同实际第六-$J$ 响应，第三项与(14.3)给相同末 $M$ 响应，第四项与(13.3)给相同末 $J$ 响应。两个不同完整目标在每个末动作下各自留在同一个实际响应纤维，故递归(1.2)给 $L_1$；包含单调性给整个子纤维的结论。没有把两种互择末读数共同当作已取得数据。

对整个 $\mathcal C$ 内同一来源和同一整个插值，有理区间包含给

$$
\begin{array}{c|c|c}
&W_1&W_2\\ \hline
d&(-1.3338,-1.3337)&(-0.6186,-0.6185)\\
g(4)&(1.4016,1.4017)&(0.7349,0.7350)\\
g(5)&(1.7667,1.7668)&(0.9452,0.9453)\\
g(6)&(1.4219,1.4220)&(0.7594,0.7595)\\
g(7)&(-0.05742,-0.05741)&(-0.05688,-0.05686)\\
[t^3]g&(-0.07077,-0.07076)&(-0.03906,-0.03905).
\end{array}                                                       \tag{14.11}
$$

漂移差在 $(-0.7152,-0.7151)$。前四个增益的正号由 $d_i<0$、$u_i,n_i>0$ 和(8.2)得到，后四个及真实三次项由表给出。已由零点等式证明相等的三读数位于

$$
\begin{gathered}
w_\ddagger\in(27.8523,27.8525),\\
r_{JM}\in(-2.2557,-2.2555),\qquad r_{JJ}\in(-2.2245,-2.2243).
\end{gathered}                                                     \tag{14.12}
$$

负读数、负漂移及符号变化均在定义1.1原合同内，没有通过采样零点制造碰撞。$\square$

**推论 14.4（父参数变化的 J 末层失败曲线）。** 存在 $2$ 附近的开区间 $I$ 及实解析 $x(\lambda)$，满足 $x(2)=x_\ddagger$、$\mathcal G_\lambda(x(\lambda))=0$。相应世界、实际子历史及 $L_1$ 保留定理14.3的全部严格条件，且在基点有

$$
\begin{gathered}
0.0029058<\theta'(2)<0.0029060,\\
-0.0007929<\xi'(2)<-0.0007927.
\end{gathered}                                                     \tag{14.13}
$$

证明。(14.7)给可逆的 $D_x\mathcal G_2(x_\ddagger)$，实解析隐函数定理给 $x(\lambda)$。缩小 $I$，使 $\lambda>0,\lambda\ne1$，来源第一坐标始终不同；所有严格界同时保持。按同一精确零点处的

$$
x'=-(D_x\mathcal G)^{-1}\partial_\lambda\mathcal G,\qquad
\theta'=\partial_\lambda\theta+D_x\theta\,x'
\tag{14.14}
$$

作五变量区间微分，再以不跨零主元的四阶消元求逆，给(14.13)；$\xi'$ 是 $x'$ 的第四分量。第五变量始终是同一关系 $s_2=\lambda s$ 中的 $\lambda$，没有对两来源分别取最优。$\theta'(2)\ne0$ 证明实际父历史变化；一维延拓没有给父平面的开集。$\square$

**命题 14.5（另一第六动作分离本对与共同父接合义务）。** 从同一个 $H^-_{\theta_\ddagger,\xi_\ddagger}$ 改选第六动作 $M$，两个世界读数分别在

$$
(28.8970,28.8971),\qquad(28.4119,28.4120),
\tag{14.15}
$$

差在 $(0.4850,0.4851)$。因此本对自身在父历史不具有 $L_2$。第12章与本章分别给两臂末层失败，尚未给同一个父记录的 $L_2$。

证明。另一个第六累计矩阵的迹为 $n+2a$，故读数是 $d_i+(n_i+2a_i)g_i(6)$。对同一 $\mathcal C$ 作区间包含即得(14.15)和差界，该动作分开本对。

更一般地，定义实际父参数集合

$$
\begin{aligned}
\mathcal P_M&=\{(\theta,\xi):\exists w\
 L_1(\mathcal F(H^-_{\theta,\xi},M,w),(H^-_{\theta,\xi},M,w))\},\\
\mathcal P_J&=\{(\theta,\xi):\exists w\
 L_1(\mathcal F(H^-_{\theta,\xi},J,w),(H^-_{\theta,\xi},J,w))\}.
\end{aligned}                                                     \tag{14.16}
$$

由(1.2)，该父具有 $L_2$ 恰当且仅当 $(\theta,\xi)\in\mathcal P_M\cap\mathcal P_J$。两臂可以使用不同见证世界和不同第六读数，但父 $\theta,\xi$ 必须相同；每臂内部的两种末动作又须共享同一个实际第六读数。第12章证明 $\mathcal P_M$ 含变化曲线，本章证明 $\mathcal P_J$ 含另一变化曲线。两个集合非空不蕴含交集非空，两个基点的 $\theta$ 区间在(12.3)、(14.6)中已不交。因此交点存在、共同父 $L_2$、原根八读下界及九读上界均须另证。$\square$

本章新增的是实际第六-$J$ 子记录的完整二目标共同末层碰撞及变化父历史的解析延拓，属于仓内构造与综合推导（repo-derived）。有限插值、压缩映射、区间包含、隐函数定理及线性消元是成熟工具。第13章给固定 $JJ$ 失败的二维开父族，本章给更强的 $L_1$ 但只证明一维父族；参数区域与量词不互相替代。不申领文献首创，不将有理盒纸面证书称作 Lean 核验。

## 追加锚（本行以下为增补区）

## 15. 末钟零增益的全父族刚性

**定义 15.1（零末增益的插值系数）。** 保留定义8.1的整个父历史 $H^-_{\theta,\xi}$，本章允许任意 $\theta,\xi\in\mathbb R$，不要求 $\Phi$、$\Delta$ 或 $\xi$ 非零。对 $u>0$ 定义

$$
\begin{gathered}
H(u)=u(u+1),\qquad X(u)=20u^2+34u-70,\\
D(u)=45u^2+31u-140,\qquad
E(u)=5(12u^2+5u-35),\\
T(u)=28-3u-10u^2.
\end{gathered}                                                     \tag{15.1}
$$

若世界满足 $g(7)=0$，则其漂移 $d\ne0$。事实上 $d=0$ 将由前三个零读数迫使 $g(0)=g(1)=g(2)=0$，连同 $g(7)=0$ 使至多三次的 $g$ 恒零，与时钟三读数六矛盾。以时钟 $0,1,2,7$ 插值可得

$$
\frac1d\bigl(g(3),g(4),g(5),g(6)\bigr)
=\left(-\frac X{35H},-\frac D{35H},
       -\frac E{35H},\frac T{7H}\right).
\tag{15.2}
$$

这里用的是同一个整个多项式；不假定它的实际次数为三。

**定理 15.2（零末增益切片上的任一末动作恢复）。** 固定任意父参数 $\theta,\xi$、第六动作 $A\in\{M,J\}$ 和实际响应 $w$。在实际子纤维

$$
K_0=\{W\in\mathcal F(H^-_{\theta,\xi},A,w):g_W(7)=0\}
\tag{15.3}
$$

上，任一末动作 $B\in\{M,J\}$ 的原时钟读数对完整目标都是单射。此结论也适用于将来源扩为全部逐项严格正、迹一的实二阶矩阵而不要求秩一的同一模型。

证明。若 $W_1,W_2\in K_0$ 在末动作 $B$ 上读数相同，因两者 $g_i(7)=0$，这个共同读数就是同一个漂移 $d$。由定义15.1，$d\ne0$。记两者的正迹坐标为 $(u_i,n_i,a_i)$，设 $x=u_1,y=u_2$。

共同的时钟三至六读数和(15.2)给

$$
\begin{gathered}
n_1X(x)/H(x)=n_2X(y)/H(y),\\
a_1D(x)/H(x)=a_2D(y)/H(y),\\
(n_1+a_1)E(x)/H(x)=(n_2+a_2)E(y)/H(y).
\end{gathered}                                                     \tag{15.4}
$$

第六动作若为 $M$，第四个等式是

$$
(n_1+2a_1)T(x)/H(x)=(n_2+2a_2)T(y)/H(y);
\tag{15.5M}
$$

若为 $J$，则是

$$
(1+2n_1)T(x)/H(x)=(1+2n_2)T(y)/H(y).
\tag{15.5J}
$$

这些条件来自同一实际子记录，不曾同时执行两个第六动作。

先处理 $x=y$。以下多项式对均无公共正零点：

$$
(X,T),\qquad(D,E),\qquad(X,D).
\tag{15.6}
$$

可由
$X+2T=14(2u-1)$、
$3E-4D=-7(7u-5)$、
$9X-4D=14(13u-5)$
核对：候选公共根分别为 $1/2,5/7,5/13$，但对应的
$X,D,X$ 值分别为 $-48,-4650/49,-9120/169$。
在 $J$ 情形，(15.4)第一式和(15.5J)先给 $n_1=n_2$，第二、三式再给 $a_1=a_2$。
在 $M$ 情形，若 $X(x)\ne0$，先得 $n_1=n_2$，再由 $(D,E)$ 得 $a_1=a_2$；若 $X(x)=0$，则 $D(x)\ne0$ 先给 $a_1=a_2$，再由 $T(x)\ne0$ 和(15.5M)给 $n_1=n_2$。

下面证明 $x\ne y$ 不可能。$X$ 在正半轴严格递增，且 $X(1)=-16$、$X(5/4)=15/4$，故有唯一正根 $\rho\in(1,5/4)$。(15.4)第一式及 $n_i,H(u_i)>0$ 说明 $X(x),X(y)$ 同号；它们不能同时为零，否则 $x=y=\rho$。

当第六动作为 $M$，置
$v=(n_1/H(x),a_1/H(x),n_2/H(y),a_2/H(y))^{\mathsf T}$。
(15.4)、(15.5M)是 $\mathcal Kv=0$，其中

$$
\mathcal K=
\begin{pmatrix}
X(x)&0&-X(y)&0\\
0&D(x)&0&-D(y)\\
E(x)&E(x)&-E(y)&-E(y)\\
T(x)&2T(x)&-T(y)&-2T(y)
\end{pmatrix}.
\tag{15.7}
$$

直接展开得

$$
\begin{aligned}
\det\mathcal K&=-490(x-y)^2Q(x,y),\\
Q(x,y)&=680x^2y^2-870x^2y-870xy^2+250(x^2+y^2)\\
&\hspace{12mm}+4103xy-2335(x+y)+4765.
\end{aligned}                                                     \tag{15.8}
$$

所需的是在上述同号区域上 $Q>0$，不是在整个正象限上误称正性。若 $X(x),X(y)>0$，则 $x,y>1$。写 $x=1+r,y=1+s$，有

$$
Q(1+r,1+s)=680r^2s^2+490rs(r+s)+60(r^2+s^2)
 +3343rs+1018(r+s)+3638>0.
\tag{15.9}
$$

若 $X(x),X(y)<0$，则 $0<x,y<5/4$。令
$B_i(z)=\binom2i z^i(1-z)^{2-i}$，$i=0,1,2$。
在这个闭方形上有精确展开

$$
Q(x,y)=\sum_{i,j=0}^2c_{ij}B_i(4x/5)B_j(4y/5),\qquad
(c_{ij})=
\begin{pmatrix}
4765&26445/8&17895/8\\
26445/8&220735/64&200535/64\\
17895/8&200535/64&140205/32
\end{pmatrix}.
\tag{15.10}
$$

全部系数严格正，基函数非负且总和为一，所以 $Q>0$。因此两种同号情形下 $\det\mathcal K\ne0$，迫使 $v=0$，与 $n_i,a_i>0$ 矛盾。

当第六动作为 $J$，置

$$
\begin{gathered}
A_*=xy+4(x+y)+4,\qquad
B_*=20xy-10(x+y)+53,\\
C_*=11xy-5(x+y)+30,\qquad
L_*=21xy-15(x+y)+55.
\end{gathered}                                                     \tag{15.11}
$$

以下差商由多项式展开得到：

$$
\begin{aligned}
[T(x)H(y)-T(y)H(x)]/(x-y)&=-7A_*,\\
[T(x)X(y)-T(y)X(x)]/(x-y)&=-14B_*,\\
[D(x)E(y)-D(y)E(x)]/(x-y)&=-35L_*,\\
[X(x)E(y)-X(y)E(x)]/(x-y)&=-140C_*.
\end{aligned}                                                     \tag{15.12}
$$

由(15.4)第一式与(15.5J)消去另一侧 $n$，得到

$$
4B_*H(y)n_1=-A_*X(y),\qquad
4B_*H(x)n_2=-A_*X(x).
\tag{15.13}
$$

若 $B_*=0$，因 $A_*>0$，这迫使 $X(x)=X(y)=0$，矛盾；故可除以 $B_*$。
若两 $X$ 都正，则 $x,y>1$，从而
$B_*=20(x-\tfrac12)(y-\tfrac12)+48>0$，(15.13)却给 $n_i<0$。
因此两 $X$ 都负，$0<x,y<5/4$。双线性函数的矩形极值在角点取得，给

$$
B_*\ge81/2,\qquad C_*\ge95/4,\qquad L_*\ge145/4.
\tag{15.14}
$$

再用(15.4)第二、三式消去 $a_2$，代入(15.13)并使用(15.12)后两式，得

$$
a_1=\frac{D(y)A_*C_*}{H(y)B_*L_*}.
\tag{15.15}
$$

而 $D$ 在正半轴严格递增，$D(5/4)=-495/16$，所以 $D(y)<0$，(15.15)与 $a_1>0$ 矛盾。

综上只能有 $u_1=u_2,n_1=n_2,a_1=a_2$。对任意迹一矩阵
$P=\left(\begin{smallmatrix}p&q_0\\r&1-p\end{smallmatrix}\right)$，
这些迹坐标满足

$$
p=n+a-3u-1,\qquad q_0=n+2a-4u-3,\qquad r=1+2u-a.
\tag{15.16}
$$

故 $P_1=P_2$。共同 $d$ 与时钟零至三的四个值再给 $g_1=g_2$，完整目标相同。全部证明仅使用来源逐项正、迹一、至多三次增益、指定实际历史及允许的末钟零点；未使用秩一、$\Phi$ 的非零性或额外增益符号。$\square$

**推论 15.3（共同末层碰撞的末钟符号约束）。** 在任意 $H^-_{\theta,\xi}$ 的同一实际第六-$A$ 子纤维中，若同一对不同完整目标在两个互择末动作上分别都碰撞，则

$$
g_1(7)g_2(7)>0.
\tag{15.17}
$$

证明。由(13.4)，第六动作为 $J$ 时，两个末累计矩阵之差是
$\left(\begin{smallmatrix}0&0\\2&3\end{smallmatrix}\right)$；
第六动作为 $M$ 时，其差是
$\left(\begin{smallmatrix}0&0\\5&7\end{smallmatrix}\right)$。
因此同一世界的两个末响应差为

$$
r_{AM}-r_{AJ}=c_A(P)g(7),\qquad
c_J(P)=2P_{12}+3P_{22}>0,\quad
c_M(P)=5P_{12}+7P_{22}>0.
\tag{15.18}
$$

分别相同的两末响应使两世界的差也相同，所以 $g_1(7),g_2(7)$ 同号或同时为零。同时为零由定理15.2迫使完整目标相同，矛盾。故乘积严格正。$\square$

**命题 15.4（零切片恢复与原自适应任务的边界）。** 定理15.2不消去第12、14章的 $L_1$，也不把一般 $L_1$ 的两个碰撞对强制识别为同一对；共同父 $L_2$ 及原根八读／九读问题仍须另证。

证明。定理15.2的恢复带有 $g(7)=0$ 的明确承诺，第12、14章见证均满足 $g_i(7)\ne0$，故不在该切片中。推论15.3只约束同一对同时匹配两种末动作的情形；一般 $L_1$ 允许两种动作使用不同目标对，这时不能相减得到同一响应差。共同父条件仍是(14.16)中两个父参数像的交集非空，零分支排除没有提供交点。$\square$

本章新增的是两个实际第六动作、全部父参数上的零末增益完整目标刚性，以及由此得到的共同末层碰撞符号条件，属于仓内推导（repo-derived）。有限插值、行列式、差商消元和 Bernstein 基上的正系数包含是成熟工具；这里承重的是(15.8)–(15.15)在实际正来源条件下的刚性接合，不申领文献首创，也不声称新增 Lean 核验。

## 追加锚（本行以下为增补区）

## 16. 第六 M 子纤维中两个二次增益的共同末碰撞排除

**定义 16.1（二次增益的齐次来源坐标）。** 保留定义8.1的整个父族、原时钟与完整目标，只在本章的待比较世界上另要求 $\deg g\le2$。记 $u=\operatorname{tr}(MP)>0$、$n=\operatorname{tr}(JM^2P)>0$、$a=\operatorname{tr}(MJM^2P)>0$ 和 $h=u(u+1)$。前三个零读数给 $g(0)=-d$、$g(1)=-d/u$、$g(2)=-d/(u+1)$。若 $d=0$，二次次数上界使 $g=0$，与时钟三读数六矛盾。因此

$$
\begin{gathered}
g(t)=\frac d{2h}\bigl((2-u^2)t^2+(3u^2-4)t-2h\bigr),\\
D=d/h\ne0,\qquad N=Dn,\qquad A=Da.
\end{gathered}                                                     \tag{16.1}
$$

式(15.16)给原矩阵 $P=P(u,n,a)$。其秩一条件的齐次式是

$$
\begin{aligned}
F(u,D,N,A)={}&A^2-AN-2uAD-2AD-N^2+4uND+2ND\\
&-u^2D^2+uD^2+D^2=0.
\end{aligned}                                                     \tag{16.2}
$$

置 $q_3=3-h$、$q_4=8-u-3u^2$、$q_5=15-u-6u^2$、$q_6=24-u-10u^2$、$q_7=35-u-15u^2$。时钟三、四、五、六 $M$、七 $MM$ 及七 $MJ$ 的响应依次是下列矩阵乘以 $(D,N,A)^{\mathsf T}$：

$$
C(u)=
\begin{pmatrix}
h&q_3&0\\
h&0&q_4\\
h&q_5&q_5\\
h&q_6&2q_6\\
h&2q_7&3q_7\\
h+(1-u)q_7&4q_7&0
\end{pmatrix}.
\tag{16.3}
$$

最后两行属于同一个世界的互择末响应函数；实际第六动作始终是 $M$，不增加观察口或更改时钟。

**定理 16.2（两个二次增益不能共同见证 M 子纤维的两末动作失败）。** 对任意 $\theta,\xi,w\in\mathbb R$，在

$$
\{W\in\mathcal F(H^-_{\theta,\xi},M,w):\deg g_W\le2\}
\tag{16.4}
$$

上，两互择末响应的联合映射 $W\mapsto(r_{MM}(W),r_{MJ}(W))$ 对完整目标单射。因此，若同一对不同完整世界在一个这样的实际第六 $M$ 子纤维中分别匹配两种末响应，则至少一个增益次数恰为三。

证明。设两世界的六项响应(16.3)相同，令 $x=u_1,y=u_2$，并置

$$
K(x,y)=[C(x)\mid-C(y)],\qquad
z=(D_1,N_1,A_1,D_2,N_2,A_2)^{\mathsf T}.
\tag{16.5}
$$

于是 $Kz=0$，且每一组 $(D_i,N_i,A_i)$ 均满足(16.2)。因 $D_i\ne0$、$n_i,a_i>0$，有 $N_iA_i\ne0$。

先处理 $x=y=u$。取 $C(u)$ 的前三行与第1、2、4行的三阶行列式，分别除以 $h>0$，得到

$$
\begin{aligned}
p_0(u)&=-3(7u^4+4u^3-36u^2-10u+47),\\
p_1(u)&=-47u^4-31u^3+241u^2+75u-312.
\end{aligned}                                                     \tag{16.6}
$$

记 $b_0=193499u^3+421142u^2-369774u-881436$、$b_1=28819u^3+60183u^2-59364u-132754$。直接展开给

$$
b_0p_0-3b_1p_1=24732.
\tag{16.7}
$$

故两行列式不能同时为零，$C(u)$ 列秩为三，迫使两组齐次坐标相同。由(16.1)、(15.16)恢复相同的 $d,P,g$。

以下设 $x\ne y$。对一个五行六列矩阵，按列序 $i=0,\ldots,5$ 定义其带号最大余子式为 $(-1)^i$ 乘以删去第 $i$ 列后的行列式。$K$ 前五行的该向量恰为

$$
-(x-y)^2Q(x,y)
\bigl(y(y+1),0,0,x(x+1),0,0\bigr)^{\mathsf T},
\tag{16.8}
$$

其中

$$
\begin{aligned}
Q(x,y)={}&88x^2y^2-322x^2y-322xy^2+205(x^2+y^2)\\
&+807xy-743(x+y)+447.
\end{aligned}                                                     \tag{16.9}
$$

若 $Q\ne0$，前五行秩为五，其核只有(16.8)张成的一维，故 $Kz=0$ 迫使 $N_i=A_i=0$，与正来源矛盾。因此必要条件是 $Q(x,y)=0$。

还须使用两份来源的秩一条件，而不能只把(16.9)当作来源实现。令 $B$ 为 $K$ 的第1、2、3、4、6行，并定义

$$
\begin{gathered}
v_i(x,y)=\frac{(-1)^i\det(B\text{ 删去第 }i\text{ 列})}{(x-y)^2},
\quad 0\le i\le5,\\
F_1(x,y)=F(x,v_0,v_1,v_2),\qquad
F_2(x,y)=F(y,v_3,v_4,v_5).
\end{gathered}                                                     \tag{16.10}
$$

每个分子均被 $(x-y)^2$ 整除，所以 $v_i,F_1,F_2$ 是整系数多项式。若 $B$ 秩为五，余子式向量张成其核，与实际 $z$ 成比例；(16.2)的齐次性给 $F_1=F_2=0$。若 $B$ 秩至多四，则所有 $v_i$ 同时为零，仍有 $F_1=F_2=0$。这个推论没有除以任何单个余子式，包含其全部退化情形。

以下给出所用的精确单变量消元。以(16.2)、(16.3)、(16.10)作为多项式的定义，取

$$
\begin{gathered}
R_i(x)=\operatorname{Res}_y(F_i(x,y),Q(x,y)),\qquad i=1,2,\\
S(x)=2225x^6+1174x^5-16477x^4-5760x^3
       +41031x^2+7074x-34335.
\end{gathered}                                                     \tag{16.11}
$$

两结式的次数均为32。在 $\mathbb Z[x]$ 中取首项为正并保留整数内容的最大公因式，Sylvester 行列式展开及多项式余除给

$$
\gcd(R_1,R_2)=36S^2.
\tag{16.12}
$$

等价地，$R_1/S^2,R_2/S^2$ 是两个互素的二十次有理多项式；有理 Euclid 算法给它们的 Bézout 组合为一。这也是不需要假定结式首项在候选点非零的消元形式。由于 $Q=F_1=F_2=0$，实际 $x$ 同时消去 $R_1,R_2$，故 $S(x)=0$。

可用系数符号直接定位 $S$ 的全部正根，不用选择其中某一根。按 $z^0,\ldots,z^6$ 的次序，下列两多项式的系数分别为

$$
\begin{array}{c|rrrrrrr}
&0&1&2&3&4&5&6\\ \hline
3125(1+z)^6S\!\left(\dfrac{7z}{5(1+z)}\right)
&-107296875&-612832500&-1203394500&-880582500&-138058760&-7835352&-146412\\
3125S(8/5+z)
&267877&8224250&84717875&315980000&244859375&70418750&6953125
\end{array}
\tag{16.13}
$$

第一行严格负，第二行严格正，且 $S(7/5)=-146412/3125<0$。因此每个正根都满足 $7/5<x<8/5$。

写 $x=7/5+r$，其中 $0<r<1/5$。将 $Q$ 看作 $y$ 的二次多项式，其三个系数依次为

$$
\begin{aligned}
88r^2-\tfrac{378}5r-\tfrac{1833}{25}
&\le-58r-\tfrac{1833}{25}<0,\\
-322r^2-\tfrac{473}5r-\tfrac{6108}{25}&<0,\\
205r^2-169r-\tfrac{957}5
&\le-128r-\tfrac{957}5<0.
\end{aligned}                                                     \tag{16.14}
$$

因 $y>0$，这迫使 $Q(x,y)<0$，与(16.9)矛盾。故不同 $u$ 的情形不存在。结合相同 $u$ 的恢复，得到完整目标单射。$\square$

**定理 16.3（对二目标失败的消费及量词边界）。** 在任意 $H^-_{\theta,\xi}$ 的实际第六 $M$ 子纤维中，若一个已知集合 $K$ 至多有两个完整目标，且每个增益次数至多二，则 $\neg L_1(K,H)$。同一父族中 M 子纤维的同一对共同末碰撞，必须同时满足至少一个真实三次增益以及 $g_1(7)g_2(7)>0$；这个结论不排除由不同目标对见证的 $L_1$，也不决定共同父 $L_2$。

证明。若两个目标不同，定理16.2使至少一个末动作区分它们，选择该动作便在余下一读恢复整个已知 $K$；零个或一个目标可立即停止。对一般共同碰撞对，次数断言由定理16.2，末增益符号由推论15.3。若 $K$ 至少有三个目标，两种末动作可以分别合并不同的目标对，不能把这些等式改写成同一个 $K(x,y)z=0$。第六 $J$ 子纤维也没有被本章的矩阵(16.3)覆盖。因此定义1.1的全部三次世界、两个实际第六动作及共同父条件仍保持原范围。$\square$

本章承重结论是整个两参数父族上二次增益共同碰撞的排除，使用原来源的秩一条件，不能沿用第15章到任意正迹一矩阵的扩张。与IV，定理5.2所需的相同第五、七增益及联合第五响应承诺不同，本章只保留(16.4)的实际父子历史。有限插值、最大余子式、结式和 Bézout 消元是成熟方法；本章的齐次来源约束接合及正域排除属于仓内推导（repo-derived），不申领文献优先权。

## 追加锚（本行以下为增补区）

## 17. 第六 J 子纤维的二次排除与两臂完整次数约束

**定义 17.1（第六 J 的二次响应矩阵）。** 保留定义16.1的 $u,h,D,N,A,q_3,\ldots,q_7$ 与齐次秩一式 $F$。实际第六动作为 $J$ 时，时钟三、四、五、六以及互择的七 $JM$、七 $JJ$ 响应依次是

$$
C_J(u)\begin{pmatrix}D\\N\\A\end{pmatrix},\qquad
C_J(u)=
\begin{pmatrix}
h&q_3&0\\
h&0&q_4\\
h&q_5&q_5\\
h+q_6&2q_6&0\\
h+uq_7&0&2q_7\\
h&q_7&q_7
\end{pmatrix}.
\tag{17.1}
$$

相应实际迹为 $n,a,n+a,1+2n,u+2a,n+a$。最后一项使用两个连续 $J$ 的累计作用恢复到时钟五的累计矩阵，但增益仍在原时钟七取值。

**定理 17.2（J 子纤维中两个二次增益的联合末响应单射）。** 对任意 $\theta,\xi,w\in\mathbb R$，在

$$
\{W\in\mathcal F(H^-_{\theta,\xi},J,w):\deg g_W\le2\}
\tag{17.2}
$$

上，$W\mapsto(r_{JM}(W),r_{JJ}(W))$ 对完整目标单射。

证明。沿用(16.5)的两个正迹坐标 $x,y$ 和实际齐次向量 $z$，将矩阵换成 $K_J=[C_J(x)\mid-C_J(y)]$。两世界的共同响应给 $K_Jz=0$，且 $F(x,D_1,N_1,A_1)=F(y,D_2,N_2,A_2)=0$。

先设 $x=y=u$。$C_J$ 前三行的行列式除以 $h$ 仍是(16.6)的 $p_0$，第1、2、6行的对应商是

$$
p_J(u)=-57u^4-30u^3+287u^2+70u-361.
\tag{17.3}
$$

置 $c_0=1070916u^3+2091411u^2-2303050u-4599529$、$c_1=131516u^3+262773u^2-288540u-598784$，有恒等式 $c_0p_0-3c_1p_J=50517$。故 $C_J$ 列秩为三，齐次坐标及完整目标相同。

以下设 $x\ne y$。行列式展开给

$$
\det K_J=3(x-y)^3Q_J(x,y),\qquad
Q_J(x,y)=\sum_{j=0}^4a_j(x)y^j,
\tag{17.4}
$$

其中

$$
\begin{aligned}
a_0(x)&=-8(225x^4-885x^3-292x^2+2908x-2320),\\
a_1(x)&=2(1650x^4-3973x^3-558x^2+15672x-11632),\\
a_2(x)&=-825x^4+3779x^3+1332x^2-1116x+2336,\\
a_3(x)&=-345x^4+1171x^3+3779x^2-7946x+7080,\\
a_4(x)&=15(12x^4-23x^3-55x^2+220x-120).
\end{aligned}                                                     \tag{17.5}
$$

实际 $z\ne0$，所以必要条件是 $Q_J(x,y)=0$。取 $B_J$ 为 $K_J$ 的前五行，以(16.10)相同的带号余子式公式定义 $v_i^J$，仍整除 $(x-y)^2$。置

$$
\begin{gathered}
F_1^J=F(x,v_0^J,v_1^J,v_2^J),\qquad
F_2^J=F(y,v_3^J,v_4^J,v_5^J),\\
R_i^J(x)=\operatorname{Res}_y(F_i^J,Q_J),\qquad i=1,2.
\end{gathered}                                                     \tag{17.6}
$$

当 $B_J$ 秩为五，余子式向量与实际 $z$ 成比例；秩至多四时该向量为零。因此两种情形都有 $F_1^J=F_2^J=0$，没有遗漏余子式退化分支。

这次两个结式的次数均为64，整系数最大公因式去掉整数内容后恰为 $(S_JT_J)^2$，其中

$$
\begin{aligned}
S_J(x)={}&425x^6+10665x^5-14027x^4-38910x^3\\
&+44968x^2+29976x-29680,\\
T_J(x)={}&20250x^{14}+71685x^{13}-217575x^{12}-1020159x^{11}\\
&+701020x^{10}+6083779x^9+664027x^8-19411345x^7\\
&-10048304x^6+34870702x^5+26933248x^4-33373656x^3\\
&-31792320x^2+13271040x+14515200.
\end{aligned}                                                     \tag{17.7}
$$

此恒等式由(17.1)、(17.5)、(17.6)的 Sylvester 行列式及有理 Euclid 余除给出；去掉 $(S_JT_J)^2$ 后的两个二十四次商互素。故实际 $x$ 必满足 $S_J(x)T_J(x)=0$。

按 $p,p'$ 起始、每次取负余式的 Sturm 链，符号变差数为

$$
\begin{array}{c|rrrrrr}
&0&3/4&4/5&7/5&8/5&+\infty\\ \hline
S_J&3&3&2&2&0&0\\
T_J&7&7&7&7&5&5
\end{array}.
\tag{17.8}
$$

各有限端点均不消去两多项式。因而全部正候选根都属于 $(3/4,4/5)\cup(7/5,8/5)$。

最后在这两个区间排除 $Q_J=0$。对任一四次多项式 $a_j$ 和区间 $[l,r]$，在 $x=l+(r-l)t$、$0\le t\le1$ 下，其四阶 Bernstein 系数是

$$
\beta_i(a_j;l,r)=
\sum_{b=0}^i\frac{\binom ib}{\binom4b}
\frac{a_j^{(b)}(l)}{b!}(r-l)^b,
\qquad 0\le i\le4.
\tag{17.9}
$$

将(17.5)代入，各列的全部五个系数分别严格大于下表数值：

$$
\begin{array}{c|rrrrr}
[l,r]&a_0&a_1&a_2&a_3&a_4\\ \hline
[3/4,4/5]&4000&-3000&3500&3500&100\\
[7/5,8/5]&3000&9000&10000&5000&900
\end{array}.
\tag{17.10}
$$

Bernstein 基非负且和为一，同样的严格下界适用于 $a_j(x)$。在第二个区间，全部系数严格正，故 $Q_J(x,y)>0$。在第一个区间，对 $y>0$ 有

$$
\begin{aligned}
Q_J(x,y)&>100y^4+3500y^3+3500y^2-3000y+4000\\
&=100y^4+3500y^3+3500(y-3/7)^2+23500/7>0.
\end{aligned}                                                     \tag{17.11}
$$

两者都与必要条件 $Q_J=0$ 矛盾，故只能有 $x=y$，完整目标相同。$\square$

**定理 17.3（任一实际第六动作的共同碰撞都需要三次增益）。** 固定任意 $H^-_{\theta,\xi}$、第六动作 $A\in\{M,J\}$ 和实际响应 $w$。若同一对不同完整目标在其实际子纤维中分别匹配两种末响应，则

$$
\max(\deg g_1,\deg g_2)=3,\qquad g_1(7)g_2(7)>0.
\tag{17.12}
$$

若该子纤维中的已知集合至多有两个目标且两增益次数至多二，则存在余下一读的恢复策略。

证明。次数条件由定理16.2、17.2，符号条件由推论15.3。已知两个不同目标时，联合末响应单射使至少一个允许末动作区分它们；较小集合可直接停止。这个选择依赖已知集合，不能因此断言一个末动作在整个任意基数二次子纤维上单射。不同末动作的失败仍可由不同目标对见证，故一般 $L_1$ 与共同父 $L_2$ 保留原量词。$\square$

这里新增的是任意父参数上第六 $J$ 臂的秩一二次排除，并将它与第16章及第15章连接为两臂的共同碰撞约束。最大余子式、齐次二次约束、结式、Sturm 根定位和 Bernstein 包含均为成熟工具；本章的实际正域排除属于仓内推导（repo-derived）。来源秩一、原时钟及整个父历史均参与证明，结论不外推至任意正迹一矩阵或任意历史，不申领文献优先权。

## 追加锚（本行以下为增补区）

## 18. 整棵二步响应树的两世界刚性

**引理 18.1（四叶迹的秩一加性校准）。** 设 $X_1,X_2$ 是逐项严格正的二阶实秩一矩阵，$\alpha_1,\alpha_2,d_1,d_2\in\mathbb R$。若对每个

$$
Q\in\{I,JM,MJ,M^2\}
\qquad\text{均有}\qquad
d_1+\alpha_1\operatorname{tr}(QX_1)
=d_2+\alpha_2\operatorname{tr}(QX_2),
\tag{18.1}
$$

则 $d_1=d_2$ 且 $\alpha_1X_1=\alpha_2X_2$。特别地，两标量同时为零，或者同时非零。

证明。置 $U_i=\alpha_iX_i$、$\delta=d_1-d_2$，写

$$
U_1-U_2=\begin{pmatrix}p&q\\r&s\end{pmatrix}.
$$

四个等式依次给

$$
p+s=-\delta,\quad p+r+s=-\delta,\quad
p+q+s=-\delta,\quad p+q+r+2s=-\delta.
\tag{18.2}
$$

相减得 $q=r=s=0$，所以 $U_1-U_2=-\delta E_{11}$。因此两 $U_i$ 的右下元素共同为某个 $v$。若 $v=0$，$X_{i,22}>0$ 迫使两 $\alpha_i$ 都为零，继而 $\delta=0$。若 $v\ne0$，两 $U_i$ 均秩一，且有相同的非对角元素；由

$$
U_{i,11}v=U_{i,12}U_{i,21}
\tag{18.3}
$$

得到两左上元素也相同，故 $\delta=0$ 且 $U_1=U_2$。没有排除零标量或预设两标量同号。$\square$

**定义 18.2（两步反事实签名）。** 固定定义8.1的整个父历史 $H=H^-_{\theta,\xi}$。对 $W\in\mathcal F(H)$，以 $r_A^{(6)}(W)$ 表示实际下一动作选 $A$ 时的时钟六响应，以 $r_{AB}^{(7)}(W)$ 表示随后选 $B$ 时的时钟七响应。记

$$
\Sigma_A(W)=
\bigl(r_A^{(6)}(W),r_{AM}^{(7)}(W),r_{AJ}^{(7)}(W)\bigr),
\qquad A\in\{M,J\}.
\tag{18.4}
$$

签名用于比较允许策略的响应函数，不是声称单轨迹已经共同取得全部分量。时钟五的累计矩阵是

$$
B_5=M^2JM^2=\begin{pmatrix}2&3\\3&4\end{pmatrix},
\qquad\det B_5=-1.
\tag{18.5}
$$

四个时钟七响应的累计矩阵分别是 $M^2B_5,JMB_5,MJB_5,B_5$。每个世界的同一个 $g_W(7)$ 和同一个漂移用于这四个响应函数。

**定理 18.3（全部三次世界的联合两步签名单射）。** 对任意 $\theta,\xi\in\mathbb R$，映射

$$
W\longmapsto\bigl(\Sigma_M(W),\Sigma_J(W)\bigr)
\tag{18.6}
$$

在整个 $\mathcal F(H^-_{\theta,\xi})$ 上对完整目标单射。结论保留全部非零至多三次增益、任意漂移符号、低次数和采样零点。

证明。设两世界有相同联合签名。取 $X_i=B_5P_i$、$\alpha_i=g_i(7)$。因 $B_5$ 逐项正、可逆，两 $X_i$ 都逐项正且秩一；四个时钟七响应相同恰给(18.1)。引理18.1得

$$
d_1=d_2,\qquad g_1(7)B_5P_1=g_2(7)B_5P_2.
\tag{18.7}
$$

消去可逆 $B_5$，再用 $\operatorname{tr}P_i=1$，得到 $g_1(7)=g_2(7)=\gamma$。

若 $\gamma\ne0$，(18.7)给 $P_1=P_2$。父历史中的时钟零至三以及共同漂移，遂给 $g_1,g_2$ 在四个不同节点的相同值；来源在这四个累计矩阵下的迹均正，故除这些迹合法。至多三次插值唯一性给 $g_1=g_2$，完整目标相同。

若 $\gamma=0$，两世界都属于第15章的零末增益切片。共同 $r_M^{(6)}$ 把它们放在同一个实际第六-$M$ 子纤维，共同 $r_{MM}^{(7)}$ 又给相同末 $M$ 读数。直接应用定理15.2的该臂零切片单射性，仍得完整目标相同。因此零末增益没有被除去。$\square$

**推论 18.4（两世界的父历史不具有两读失败）。** 对任意已知 $K\subseteq\mathcal F(H^-_{\theta,\xi})$，若 $K$ 至多有两个完整目标，则

$$
\neg L_2(K,H^-_{\theta,\xi}).
\tag{18.8}
$$

因此，整个父纤维若具有 $L_2$，不能由相同的两个世界同时承担两臂失败；其任何有限失败见证至少含三个完整目标。

证明。零或单目标可停止。若恰有两个不同世界，定理18.3保证至少一个 $A\in\{M,J\}$ 满足 $\Sigma_A(W_1)\ne\Sigma_A(W_2)$。先执行这个 $A$。若两候选的时钟六响应不同，实际响应已识别目标；若相同，则(18.4)至少一个末动作的响应不同，选择它并取得最后一读，仍识别目标。这只实际取得一条分支的记录。策略依赖已知 $K$，不声称存在处理任意描述的有效算法。两臂若完全共用相同坏对，联合签名将相同，与定理18.3矛盾。$\square$

这与定理17.3的任务不同：第17章在一个实际子纤维、余下一读时约束二次坏对；本章允许真实三次增益，在整个父历史、余下两读时排除同一坏对覆盖两臂。一般 $L_2$ 仍允许不同目标对、不同实际第六响应，并允许更大目标集合；联合签名单射不提供这些集合上的单轨迹统一识别策略。共同父交点、原根八读／九读和九读上界仍保持未解。

这里承重的是四叶等式将差矩阵限制到 $E_{11}$ 方向，再由正秩一实现排除该方向，最后与零末增益刚性及实际策略接合。迹线性、二阶行列式和有限插值均为成熟工具；这一父族内的完整目标推导归 repo-derived，不申领文献首创，不声称 Lean 核验。上述四叶只作为反事实响应比较，没有增加传感器、重置或复制权限。

## 追加锚（本行以下为增补区）

## 19. 两个末钟零增益候选的双读恢复

**定理 19.1（三候选中至多一个非零末增益时的实际恢复）。** 固定任意 $\theta,\xi\in\mathbb R$ 和父历史 $H=H^-_{\theta,\xi}$。令 $K\subseteq\mathcal F(H)$ 是已知的有限完整目标集合，满足

$$
|K|\le3,
\qquad
\bigl|\{W\in K:g_W(7)\ne0\}\bigr|\le1.
\tag{19.1}
$$

则存在从 $H$ 开始、至多取得两次后续实际读数的确定性策略，在 $K$ 上恢复完整目标。该结论仍适用于将来源放宽为全部逐项严格正、迹一的二阶实矩阵而不要求秩一的模型。策略依赖已知 $K$；不主张一个对任意实数描述都有效的统一计算算法。

特别地，在原秩一模型中，三个不同世界组成的 $L_2$ 见证至多含一个满足 $g(7)=0$ 的世界。这里没有要求 $\xi,\Phi,\Delta$、三次项或其他采样增益非零。

证明。沿用定义18.2的原时钟响应记号。对同一个世界定义

$$
D_M(W)=r_{MM}^{(7)}(W)-r_{MJ}^{(7)}(W),
\qquad
D_J(W)=r_{JM}^{(7)}(W)-r_{JJ}^{(7)}(W).
\tag{19.2}
$$

时钟五的累计矩阵仍为 $B_5=\left(\begin{smallmatrix}2&3\\3&4\end{smallmatrix}\right)$。同一时钟七的两个差矩阵为

$$
M^2B_5-JMB_5=\begin{pmatrix}0&0\\5&7\end{pmatrix},
\qquad
MJB_5-B_5=\begin{pmatrix}0&0\\2&3\end{pmatrix}.
\tag{19.3}
$$

因此，若 $P_{12}=x>0$、$P_{22}=y>0$，则

$$
D_M=(5x+7y)g(7),
\qquad
D_J=(2x+3y)g(7).
\tag{19.4}
$$

当 $g(7)\ne0$，两差均非零，并且

$$
\frac73<\frac{D_M}{D_J}<\frac52.
\tag{19.5}
$$

两项严格界分别来自
$3(5x+7y)-7(2x+3y)=x>0$ 和
$5(2x+3y)-2(5x+7y)=y>0$。
比值消去的是同一个世界的同一个末钟增益；允许该增益为负。若 $g(7)=0$，该世界在四个末位置的读数全部等于自身漂移 $d$。

先说明任何至多二目标、且至多一个非零末增益的实际第六子族，都能用一项末动作恢复。若两个目标末增益均为零，定理15.2保证任一末动作单射。若恰有一个为零，另一个记为 $W_*$；若两个末动作都不能区分本对，$W_*$ 的两项末响应就都等于零增益世界的漂移，迫使 $D_A(W_*)=0$，与(19.4)矛盾。因此至少一个末动作区分该对。单目标可直接停止。这一论证不使用秩一。

零或单目标的 $K$ 可停止，二目标的 $K$ 可先取任意第六动作，再使用上述子族结论。若 $K$ 全部为零末增益世界，则先取任意第六动作，定理15.2在每个实际子族中提供任一末动作的完整目标恢复。

只剩 $K=\{W_1,W_2,W_*\}$，其中 $g_1(7)=g_2(7)=0$、$g_*(7)\ne0$。若某个第六动作 $A$ 的响应在 $K$ 上不是常数，就先执行它。每个实际响应子族至多有两个目标，继而按上述子族结论选择末动作，即可恢复。

最后假设两个第六预测都分别在全部 $K$ 上为常数：

$$
r_M^{(6)}|_K\equiv w_M,
\qquad
r_J^{(6)}|_K\equiv w_J.
\tag{19.6}
$$

这不是要求实际同时读取 $w_M,w_J$。两个零增益世界此时共享任一实际第六子历史，故其漂移 $d_1,d_2$ 必须不同；否则任一末读数都相同，定理15.2会使它们成为同一个完整目标。

若四个末响应函数中有一个在 $K$ 上单射，就执行它所对应的两项动作，取得该响应即可恢复。反设四个都不单射。因两个零增益世界在每项末动作下分别读出不同的 $d_1,d_2$，每项非单射只能来自 $W_*$ 与其中一个零增益世界的碰撞。因此

$$
r_{AB}^{(7)}(W_*)\in\{d_1,d_2\}
\qquad(A,B\in\{M,J\}).
\tag{19.7}
$$

由(19.4)，$W_*$ 在同一臂的两个末响应不同。故每臂恰好使用 $d_1,d_2$ 各一次，得到

$$
D_M(W_*),D_J(W_*)\in\{d_1-d_2,d_2-d_1\},
\qquad
\frac{D_M(W_*)}{D_J(W_*)}\in\{-1,1\}.
\tag{19.8}
$$

这与(19.5)矛盾。因此至少一个末响应在整个 $K$ 上单射，完成真实两读策略。所有分支均只执行一条实际路径；反事实响应仅用于从已知候选中选择该路径。$\square$

本条的新增结论是完整父历史下零末增益占优的三候选恢复，并覆盖非秩一正来源。其承重部分是将定理15.2的零切片单射接到两个不同实际动作的严格响应比值，排除两个零候选与一个非零候选共同承担四项末碰撞。有限候选的自适应区分属于成熟问题；[van den Bos–Vaandrager，Theorem 6.1](https://arxiv.org/html/1907.11034v2) 使用 suspension automaton、状态不相容与 injective split 条件，并不直接给出这里的连续来源、固定原钟及两读结论。上述具体推导归 repo-derived，不申领文献首创。

条件(19.1)不由任意父读数自动保证。只有一个零末增益的三世界、三个非零末增益的三世界以及更大候选集合均未由本条解决；共同父 $L_2$、原根八读／九读及九读上界仍保持未解。

## 追加锚（本行以下为增补区）

## 20. 共同双预测纤维在固定迹层至多含两个完整目标

**定理 20.1（固定首步迹的双预测纤维界）。** 固定任意 $u>0$、$\theta,\xi,v_M,v_J\in\mathbb R$。在完整父纤维 $\mathcal F(H^-_{\theta,\xi})$ 中，同时满足

$$
\operatorname{tr}(MP)=u,\qquad
r_M^{(6)}=v_M,\qquad r_J^{(6)}=v_J
\tag{20.1}
$$

的完整目标至多有两个。结论仍适用于全部逐项严格正、迹一的二阶实来源，不要求秩一。保留整个至多三次非零增益、任意漂移、全部父参数及采样零点。

这里固定的 $u$ 可以是未知的来源参数；定理不将其增设为实际传感器。两个第六预测用于比较同一实验合同的行为，不表示在一条历史中共同取得它们。界只对每个固定 $u$ 的切片成立，不是整个父纤维只有两个世界。

证明。记

$$
\begin{gathered}
n=\operatorname{tr}(JM^2P)>0,\qquad
a=\operatorname{tr}(MJM^2P),\qquad h=u(u+1)>0,\\
L=u^2+3u-4,\quad W=4u^2+9u-15,\quad V=10u^2+19u-36,\\
\alpha=d/h,\quad \beta=(6-d)/n,\quad
N=\alpha n,\quad A=\alpha a,\quad C=\beta a.
\end{gathered}
\tag{20.2}
$$

时钟零至三给出(8.2)的同一个完整插值多项式；这些公式对非秩一迹一正来源也成立。由四节点插值，$g(4)=\alpha L+4\beta$、$g(5)=\alpha W+10\beta$、$g(6)=\alpha V+20\beta$。又有 $\beta n=6-\alpha h$，故父历史与两个第六预测给四个仿射约束

$$
\begin{aligned}
24\theta&=\alpha h+LA+4C,\\
60(1+\theta+\xi)&=60-9\alpha h+W(N+A)+10C,\\
v_M&=120-19\alpha h+V(N+2A)+40C,\\
v_J&=240+\alpha(V-39h)+2VN+20\beta.
\end{aligned}
\tag{20.3}
$$

这里第六 $J$ 的实际累计矩阵为 $JB_5$，其来源迹为 $2n+1$；第六 $M$ 的迹为 $n+2a$。因而两项约束使用同一个原时钟六的增益，没有把互择动作改为先后执行。提升变量还满足

$$
\beta N-6\alpha+h\alpha^2=0,\qquad
\beta A-\alpha C=0.
\tag{20.4}
$$

先证(20.3)的系数矩阵对每个 $u>0$ 都有秩四。按变量 $(\alpha,N,A,C,\beta)$ 排列，该矩阵为

$$
\mathsf A(u)=
\begin{pmatrix}
h&0&L&4&0\\
-9h&W&W&10&0\\
-19h&V&2V&40&0\\
V-39h&2V&0&0&20
\end{pmatrix}.
\tag{20.5}
$$

定义 $S=2u^2+85u-42$、$T=143u^2+97u-446$。前三行在列 $(\alpha,N,C)$、$(\alpha,A,C)$ 上的三阶子式分别为 $2hS$、$-2hT$。它们不能同时为零：若 $S=T=0$，恒等式 $143S-2T=11961u-5114$ 迫 $u=5114/11961$，而

$$
S(5114/11961)=-\frac{757118800}{143065521}\ne0.
\tag{20.6}
$$

末列只有最后一个分量非零，故(20.5)秩四。其解集是一条仿射直线。

为控制这条直线与(20.4)的交点数，置

$$
\begin{aligned}
Q&=50u^4+157u^3-261u^2-518u+600,\\
D&=13u^4+62u^3-14u^2-246u+192,\\
E&=1410u^6+4681u^5-5527u^4-24872u^3
       +10536u^2+38760u-21600.
\end{aligned}
\tag{20.7}
$$

直接展开给出非零核向量

$$
\mathbf v=(20Q,\ 20hT,\ 20hS,\ -20hD,\ -E)^{\mathsf T},
\qquad \mathsf A(u)\mathbf v=0.
\tag{20.8}
$$

非零性也由 $S,T$ 不同时为零得到。因此所有仿射解唯一写为 $z_0+t\mathbf v$。将它代入(20.4)，得到两个次数至多二的实多项式。它们的二次项系数分别为 $-20hF(u)$ 和 $20hG(u)$，其中

$$
\begin{aligned}
F(u)={}&151630u^8+492153u^7-936144u^6-3505461u^5\\
       &+2249726u^4+8481664u^3-3130616u^2-6950160u+2433600,\\
G(u)={}&10180u^8-26392u^7-214791u^6-32139u^5\\
       &+867234u^4+758336u^3-1430568u^2-1477200u+1396800.
\end{aligned}
\tag{20.9}
$$

这两个系数不能同时为零。给出一个有限整系数证书：在 $\mathbb F_{11}[u]$ 中，令

$$
\begin{aligned}
B_F&=3u^7+3u^6+3u^5-5u^4-2u^3+4u^2-4u-4,\\
B_G&=3u^7-3u^6+3u^5-3u^4-4u^3+u^2+u-3.
\end{aligned}
\tag{20.10}
$$

逐项乘开即得 $B_F\overline F+B_G\overline G=1$。$F,G$ 的首项系数都不被十一整除，故模十一降次不会隐藏一个共同的正次数整系数因子。由 Gauss 引理，它们在 $\mathbb Q[u]$ 中互素，也就在 $\mathbb C$ 中没有共同根。由于 $h>0$，至少一项代入后的约束具有非零二次项，整条直线上同时满足(20.4)的点至多两个。

最后，提升没有把不同世界合为同一点。若 $\alpha\ne0$，由 $n=N/\alpha$、$a=A/\alpha$ 及 $d=\alpha h$ 恢复来源坐标与漂移。若 $\alpha=0$，真实世界满足 $d=0$、$\beta=6/n>0$，遂由 $n=6/\beta$、$a=C/\beta$ 恢复；没有除去此分支。一般迹一来源由

$$
P=
\begin{pmatrix}
n+a-3u-1&n+2a-4u-3\\
1+2u-a&2+3u-n-a
\end{pmatrix}
\tag{20.11}
$$

唯一确定。时钟零至三的四节点值再唯一恢复整个增益。因此至多两个提升点只可能给至多两个完整目标。秩一条件没有被用于这个上界，来源正性及其余约束只会删除候选。$\square$

**定理 20.2（充分交叉的三世界见证不能集中在一个迹层）。** 设三个不同完整世界位于同一个父纤维。若对每个第六动作 $A\in\{M,J\}$，两项末动作的碰撞分别由三角形中的两条不同目标对承担，且它们属于同一个实际第六子历史，则这三个世界的 $\operatorname{tr}(MP)$ 不能全相等。

证明。三顶点上的两条不同边相交且覆盖全部顶点。它们同属一个实际第六子历史，故三个世界在该臂的第六响应全相同。两臂分别应用这一论证，三个世界遂共享两个第六预测。若首步迹也全相同，就违反定理20.1。这里不同臂仍可有不同的实际第六读数。$\square$

本章将原父历史的插值约束转为固定迹层上的二次交点上界；秩与多项式互素性是成熟工具，具体全参数纤维界及三世界约束归 repo-derived。没有假设 $\xi,\Phi,\Delta,\alpha,\beta$ 或 $g(7)$ 非零，也没有以一般位置排除(20.7)中 $Q$ 的零点。不同迹层上的三世界、包含同臂重复目标对的模式、更大候选集合及共同父 $L_2$ 仍未由本条解决。

## 追加锚（本行以下为增补区）

## 21. 两个第六预测相等时整个共同纤维至多为二元

**定理 21.1（对角双预测纤维的正实上界）。** 对任意 $\theta,\xi,v\in\mathbb R$，集合

$$
\mathcal D_{\theta,\xi,v}
=\{W\in\mathcal F(H^-_{\theta,\xi}):
r_M^{(6)}(W)=r_J^{(6)}(W)=v\}
\tag{21.1}
$$

至多含两个完整目标。与定理20.1不同，这里不固定 $\operatorname{tr}(MP)$。结论仍适用于全部逐项严格正、迹一的二阶实来源，不要求秩一。相等的是同一世界的两种互择预测，不是预设取得两个实验分支。

证明。沿用 $B_5=\left(\begin{smallmatrix}2&3\\3&4\end{smallmatrix}\right)$。真实差矩阵为

$$
MB_5-JB_5=\begin{pmatrix}0&0\\3&4\end{pmatrix},
\qquad r_M^{(6)}-r_J^{(6)}=(3P_{12}+4P_{22})g(6).
\tag{21.2}
$$

来源正性给 $g(6)=0$、$d=v$。且 $d\ne0$：否则时钟零、一、二及六都是至多三次增益的零点，迫 $g\equiv0$，与时钟三读数六矛盾。因此整个集合的漂移是同一个非零常数。

置 $u=\operatorname{tr}(MP)>0$、$h=u(u+1)$、$\alpha=d/h$，并沿用(20.2)的 $n,a$。现在时钟零、一、二及六的增益值唯一确定整个多项式。定义

$$
V=10u^2+19u-36,\qquad
R=16-4u-5u^2,\qquad S=6-u-2u^2.
\tag{21.3}
$$

四节点插值给

$$
g(3)=-\frac{\alpha V}{20},\qquad
g(4)=\frac{\alpha R}{5},\qquad
g(5)=\frac{\alpha S}{2}.
\tag{21.4}
$$

将父读数减去共同漂移，记

$$
c_3=6-d,\qquad c_4=24\theta-d,\qquad
c_5=60(1+\theta+\xi)-d.
\tag{21.5}
$$

所有候选满足

$$
c_3=ng(3),\qquad c_4=ag(4),\qquad
c_5=(n+a)g(5),\qquad n,a>0.
\tag{21.6}
$$

$V,R,S$ 各有唯一正根，分别记作 $\rho_V,\rho_R,3/2$；因 $V$ 严增、$R$ 严减、$S=-(u+2)(2u-3)$，并比较在 $1,6/5,3/2$ 的符号，有

$$
1<\rho_V<6/5<\rho_R<3/2.
\tag{21.7}
$$

若 $c_3,c_4,c_5$ 中有一个为零，(21.6)将 $u$ 固定为相应唯一正根。三个正根不同，其余两个增益非零；相应的两项读数唯一确定 $n,a$。若多于一个 $c_j$ 为零则没有候选。因此含零分支至多一个完整世界，没有通过除法遗漏。

以下设三个 $c_j$ 全非零。正性使 $\operatorname{sgn}(c_3/d,c_4/d,c_5/d)$ 等于 $\operatorname{sgn}(-V,R,S)$。在

$$
(0,\rho_V),\quad(\rho_V,\rho_R),\quad
(\rho_R,3/2),\quad(3/2,\infty)
\tag{21.8}
$$

上，这四个符号向量分别为 $(+,+,+)$、$(-,+,+)$、$(-,-,+)$、$(-,-,-)$。故所有候选 $u$ 必须落在同一个指定区间。

令

$$
r(u)=-\frac{V}{10S}=\frac{g(3)}{g(5)},\qquad
s(u)=\frac{2R}{5S}=\frac{g(4)}{g(5)},\qquad
p=\frac{c_3}{c_5},\quad q=\frac{c_4}{c_5}.
\tag{21.9}
$$

消去(21.6)中的 $n+a$ 得

$$
\frac{p}{r(u)}+\frac{q}{s(u)}=1.
\tag{21.10}
$$

逐项微分给

$$
r'(u)=-\frac{14u^2-12u+39}{5S^2}<0,\qquad
s'(u)=-\frac{2(3u^2-4u+8)}{5S^2}<0.
\tag{21.11}
$$

两个分子的二次式均首项正、判别式负。除区间 $(\rho_V,\rho_R)$ 外，$p,q$ 同号，因此(21.10)左边的导数严格同号，至多一个解。

在剩下的区间中，$p<0<q$ 且 $V,R,S>0$，左边写为

$$
F(u)=(-10p)\frac{S}{V}+\frac{5q}{2}\frac{S}{R}.
\tag{21.12}
$$

两个系数都严格正，并且

$$
\left(\frac SV\right)''
=\frac{20(28u^3-36u^2+234u+105)}{V^3}>0,
\qquad
\left(\frac SR\right)''
=\frac{30u(u^2-2u+8)}{R^3}>0.
\tag{21.13}
$$

第一分子括号是 $u(28u^2-36u+234)+105$，其中二次式首项正、判别式负；第二分子的二次式为 $(u-1)^2+7$。所以 $F$ 严格凸，水平线 $F=1$ 至多有两个交点。

对每个允许的 $u$，完整 $g$ 已由时钟零、一、二、六固定。在(21.6)中，三个增益至多一个为零，故唯一确定 $n,a$；再由(20.11)恢复 $P$。因此每个 $u$ 至多给一个完整世界，得总数至多二。所有来源正性与秩一附加约束只会删除解。$\square$

**定理 21.2（对角共同预测不承载充分交叉的三世界失败）。** 在定理20.2的三世界构型中，若每臂内部共同的第六预测分别为 $v_M,v_J$，则必有 $v_M\ne v_J$。相反，$v_M=v_J$ 的来源分支本身非空，且可有非零末增益；排除失败构型不等于排除该来源分支。

证明。若 $v_M=v_J=v$，三个世界均属于(21.1)，违反定理21.1。非空性由一个原秩一世界给出：

$$
P=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
d=12,\qquad g(t)=-\frac25(t-5)(t-6).
\tag{21.14}
$$

沿声明的原父路径，其时钟零至五读数为 $(0,0,0,6,46/5,12)$，对应 $\theta=23/60$、$\xi=-71/60$。两个第六预测均为十二，而 $g(7)=-4/5\ne0$。增益实际次数二仍在原合同内。$\square$

本章的上界使用原正来源给出的增益符号区间，以及该区间中有理响应比值的严格单调性或凸性。插值与严格凸函数的交点界是成熟工具；此完整原钟纤维的上界及实际匹配排除归 repo-derived，不申领文献首创。没有要求父参数、漂移符号或末增益符号预先非零；非零漂移是(21.2)与原历史推出的结论。$v_M\ne v_J$ 的跨迹层纤维、同臂重复目标对的模式、一般共同父 $L_2$ 及原根八读／九读问题仍未由本条解决。

## 追加锚（本行以下为增补区）

## 22. 完整共同双预测纤维的统一有限上界

**定理 22.1（任意父参数下至多二十四个完整世界）。** 在原严格正、秩一、迹一来源及整个至多三次非零增益模型中，对任意 $\theta,\xi,v_M,v_J\in\mathbb R$，

$$
\mathcal F_{\theta,\xi}(v_M,v_J)
=\{W\in\mathcal F(H^-_{\theta,\xi}):
r_M^{(6)}(W)=v_M,\ r_J^{(6)}(W)=v_J\}
\tag{22.1}
$$

至多有二十四个完整目标。若 $\xi=0$ 且 $v_M=120(1+2\theta)$，上界可改为三。两个第六预测相等的分支仍有定理21.1的更强二元上界。

这里不把两个互择预测视为共同取得的实际读数。结论是整个来源纤维的有限性，不提供任意实数输入的有效枚举，也不把单个实际第六子历史宣告为有限。与20—21不同，本条的全参数上界使用原来源的秩一条件。

证明。令

$$
c=6\theta,\qquad x=60\xi,\qquad
y=v_M-120-40c,\qquad z=v_J-240.
\tag{22.2}
$$

用 $u>0$ 表示首步来源迹，$h,L,W,V$ 沿用(20.2)。以下先构造完全指定的消元多项式。令 $t$ 为独立变量，并置

$$
\mathsf B(u)=\begin{pmatrix}0&L&4\\W&W&10\\V&2V&40\end{pmatrix},
\qquad D(u)=\det\mathsf B(u)=2Q(u),
\tag{22.3}
$$

其中 $Q$ 是(20.7)的四次式。定义三个分子多项式

$$
\begin{pmatrix}N_\#\\A_\#\\C_\#\end{pmatrix}
=\operatorname{adj}(\mathsf B)
\begin{pmatrix}4c-ht\\10c+x+9ht\\40c+y+19ht\end{pmatrix},
\qquad
b_\#=Dz-tD(V-39h)-2VN_\#.
\tag{22.4}
$$

由此构造关于 $t$ 次数至多二的三个多项式

$$
\begin{aligned}
F_1&=b_\#N_\#-120tD^2+20ht^2D^2,\\
F_2&=b_\#A_\#-20tC_\#D,\\
F_3&=A_\#^2-A_\#N_\#-N_\#^2
  +tD\bigl((-2u-2)A_\#+(4u+2)N_\#\bigr)
  +t^2D^2(-u^2+u+1).
\end{aligned}
\tag{22.5}
$$

令 $\mathsf H$ 的第 $i$ 行依次为 $F_i$ 的 $t^2,t,1$ 系数。精确多项式展开给

$$
\det\mathsf H=D^3\mathscr P,
\qquad \mathscr P\in\mathbb Q[u,c,x,y,z],
\qquad \deg_u\mathscr P=12.
\tag{22.6}
$$

式(22.3)—(22.6)以伴随矩阵、系数提取与精确多项式除法唯一指定 $\mathscr P$，没有按实际数值倒取可能为零的 $D$。

先证这个多项式作为 $u$ 的多项式恒零，当且仅当 $x=y=0$。给出有限有理证书以区分恒零与普通降次：对 $i=0,\ldots,12$，将 $[u^{12-i}]\mathscr P$ 除以其正有理内容，记所得本原整数系数多项式为 $p_i(c,x,y,z)$；保留原来的整体符号。这十三个形式多项式均非零。按 $i$ 递增、再按 $(1,c,x,y,z)$ 的次序，列出六十五个多项式

$$
p_i,\quad cp_i,\quad xp_i,\quad yp_i,\quad zp_i.
\tag{22.7}
$$

取这些多项式中出现的全部单项式，按 $(c,x,y,z)$ 的指数四元组的递增字典序排列，共四十七个。令 $\mathsf M\in\mathbb Z^{47\times65}$ 为(22.7)的系数矩阵，行列下标从零开始。取

$$
\begin{gathered}
I=\{0,\ldots,46\}\setminus\{11,42,44\},\qquad
J=\{0,\ldots,43\},\qquad B_0=\mathsf M_{I,J},\\
E\in\mathbb Z^{47\times2},\qquad E_{18,1}=1,\quad E_{3,2}=1,
\quad\text{其余分量为零}.
\end{gathered}
\tag{22.8}
$$

$E$ 的两列从一编号；行仍从零编号。第十八行单项式是 $x^2$，第三行是 $y^2$。这些完全指定的整数矩阵满足

$$
\mathsf M_{:,J}\operatorname{adj}(B_0)E_{I,:}
=\det(B_0)E,
\qquad \det(B_0)\equiv61\pmod{101}.
\tag{22.9}
$$

该证书只要求整数矩阵乘法及一次模一百零一的行列式；$B_0$ 为四十四阶方阵。若某组实读数使全部 $p_i$ 为零，将该组读数的单项式行向量左乘(22.9)，左边为零，右边为 $\det(B_0)(x^2,y^2)$。故 $x=y=0$。反向，将 $x=y=0$ 代入(22.3)—(22.6)的十三个系数，都直接为零。因此

$$
\mathscr P(\,\cdot\,,c,x,y,z)\equiv0
\quad\Longleftrightarrow\quad x=y=0.
\tag{22.10}
$$

还须证明任意实际世界的 $u$ 满足 $\mathscr P=0$，包括 $D(u)=0$。在 $D\ne0$ 时，(20.3)给 $N=N_\#/D$、$A=A_\#/D$、$C=C_\#/D$、$\beta=b_\#/(20D)$，其中 $t=\alpha$。前两个(22.5)就是(20.4)清除分母后的约束。第三个则来自原来源行列式

$$
\mathcal R(u,n,a)
=a^2-an-2au-2a-n^2+4nu+2n-u^2+u+1
=\det P=0.
\tag{22.11}
$$

于是 $\mathsf H(\alpha^2,\alpha,1)^{\mathsf T}=0$，其行列式为零。为使坏主元分支也有无除数证书，沿用(20.7)、(20.9)的 $Q,E,F,G$，并定义

$$
\begin{aligned}
K(u)={}&35180u^8+146440u^7-138920u^6-937640u^5\\
       &+146660u^4+1945800u^3-96960u^2-1208640u.
\end{aligned}
\tag{22.12}
$$

把实际来源坐标 $u,n,a,d$ 代入读数，令 $\Phi,\Psi_6$ 沿用(8.1)、(8.6)。相应的(22.2)准确为

$$
\begin{aligned}
4hnc&=dhn+dLan+4ah(6-d),\\
2hx&=d\Phi,\qquad hy=d\Psi_6,\\
hnz&=d(V-39h)n+2Vdn^2+20h(6-d).
\end{aligned}
\tag{22.13}
$$

对(22.6)作这个代入并清除正分母，得到完整恒等式

$$
\begin{aligned}
(4hn)^3\mathscr P(u,c,x,y,z)
={}&512d^2n^2h
\bigl(dnE(u)+20h(6-d)Q(u)\bigr)\\
&\quad\cdot\bigl(aF(u)+nG(u)-K(u)\bigr)
\mathcal R(u,n,a).
\end{aligned}
\tag{22.14}
$$

这条恒等式由(22.3)—(22.6)、(22.12)—(22.13)的多项式乘法直接检验，不除 $D,d,\beta$ 或任何采样增益。因为 $h,n>0$ 且 $\mathcal R=0$，每个实际来源都满足 $\mathscr P=0$，包括两个正坏主元、零漂移及其他降次分支。

若 $(x,y)\ne(0,0)$，由(22.10)，所有候选 $u$ 都是同一个非零、次数至多十二的实多项式的正根。因此至多有十二个不同 $u$；对每个固定 $u$，定理20.1再给至多两个完整世界，总数至多二十四。

最后处理 $x=y=0$ 的整个例外平面。它准确等于 $\xi=0$、$v_M=120(1+2\theta)$。所有候选因而位于 [V，定义28.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) 的同一个实际七读纤维。直接复用该卷定理28.2的全实参数分类：它是零漂移部分 $\mathcal Z_\theta$ 与一个完整世界 $\mathsf E_\theta$ 的并。

对零漂移世界，$g(T)=T(T-1)(T-2)/n$，第六 $J$ 的原钟读数为

$$
v_J=240+120/n.
\tag{22.15}
$$

若 $v_J\le240$ 就没有这个部分；否则 $n=120/(v_J-240)$ 唯一，且 $a=\theta n$。式(22.11)现在是关于 $u$ 的首项系数为负一的二次式，所以至多两个来源；(20.11)及完整增益公式使每个来源至多给一个完整世界。再加入至多一个 $\mathsf E_\theta$，例外平面共至多三个，仍小于二十四。交叠只删除重复目标。至此所有父参数及全部读数分支都已包含。$\square$

**定理 22.2（充分交叉三世界不能位于恒零消元平面）。** 在定理20.2的三世界两臂构型中，若共同父参数及共同第六预测记为 $\theta,\xi,v_M,v_J$，则

$$
\xi\ne0\quad\text{或}\quad v_M\ne120(1+2\theta).
\tag{22.16}
$$

证明。直接证明例外平面的共同双预测纤维至多含两个完整世界。反设 $\xi=0$ 且 $v_M=120(1+2\theta)$。由定理20.2的两条相交边，每臂的三个世界都有同一个实际第六响应。因此三个世界均位于 V 定义28.1的同一个 $\mathcal F(H_\theta)$，且其第六 $J$ 预测均为 $v_J$。以下只复用 V 定理28.2的完整分类

$$
\mathcal F(H_\theta)=\mathcal Z_\theta\cup\{\mathsf E_\theta\}.
$$

零漂移部分的来源唯一写成 $P(s,t)$，其中 $s,t>0$，整个增益为 $f_{012}/n$，且 $a=\theta n$。由(22.15)，共同 $v_J$ 唯一固定 $n$；若 $v_J\le240$，这部分为空。其非空还要求 $1/2<\theta<3$。先设 $1/2<\theta\le3/2$。将 $a=\theta n$ 代入(8.1)，得到

$$
\begin{gathered}
t=\frac{(\theta-1)+(2\theta-1)s}{(2-\theta)+(3-\theta)s},\qquad
n(s)=\frac{5s^2+5s+1}{D_\theta(s)},\\
D_\theta(s)=(2\theta-1)s^2+2s+2-\theta>0,\\
n'(s)=\frac{(8-5\theta)+(22-14\theta)s+(15-10\theta)s^2}
 {D_\theta(s)^2}>0.
\end{gathered}
\tag{22.17}
$$

第一个分母严格正；合法条件 $t>0$ 使 $s$ 落在一个开区间内。导数分子的三个系数分别至少为 $1/2,1,0$，所以在该区间上严格递增。同一个 $n$ 至多给一个 $s$，再唯一给 $t$、整个增益及完整世界。因此 $\theta\le3/2$ 时，零漂移部分至多一元，加上至多一个 $\mathsf E_\theta$，共同纤维至多二元；$\theta\le1/2$ 的空零漂移分支也包括在内。

再设 $\theta\ge3/2$。对每个严格正来源，

$$
n=1+\frac{2s+t}{1+st}>1,
\qquad 240<r_J^{(6)}(W)<360\quad(W\in\mathcal Z_\theta).
\tag{22.18}
$$

记 $u_*,k_*,n_*,S_*$ 为 V 式(27.5)—(27.6)的固定代数常数，置

$$
\Lambda_6=\frac{24}{S_*}
\left[1+(1+2n_*)\left(
\frac{10u_*^2+19u_*-36}{u_*(u_*+1)}-\frac{20}{n_*}
\right)\right].
\tag{22.19}
$$

由原第六 $J$ 累计矩阵 $JB_5=I+2JM^2$、(8.9)及 $d_\theta=24(\theta-k_*)/S_*$，固定源世界的响应准确为

$$
r_J^{(6)}(\mathsf E_\theta)
=240+\frac{120}{n_*}+\Lambda_6(\theta-k_*).
\tag{22.20}
$$

这些常数所需的严格有理界为

$$
\frac{779}{1000}<k_*<\frac{780}{1000},\qquad
\frac{3897}{1000}<n_*<\frac{3899}{1000},\qquad
\frac{547}{1000}<S_*<\frac{548}{1000},\qquad
216<\Lambda_6<217.
\tag{22.21}
$$

为指定这些界的有理验证，取 V 式(27.5)的两个有理端点作闭区间 $I_*$。在 $I_*$ 上以端点四则区间运算求 $U=u(u+1)$、$H=143u^2+97u-446$、$N=2u^2+85u-42$，并以 Horner 式 $T=(((50u+157)u-261)u-518)u+600$ 求区间。再依次取 $k=N/H$、$n=UH/T$、$S=1-4k+nk(1-4/u+6/(u+1))$ 及(22.19)。所有除数区间均排除零，所得区间分别严格包含于(22.21)；最后一项的两端还分别位于 $(216.801894490780417816,216.801894490780417817)$ 内。这里仅定位 V 分类已有的同一个固定来源，不重新选择来源。

于是 $\theta\ge3/2$ 时，(22.20)—(22.21)给

$$
r_J^{(6)}(\mathsf E_\theta)
>240+216\left(\frac32-\frac45\right)
=\frac{1956}{5}>360.
\tag{22.22}
$$

所以在同一个第六 $J$ 预测纤维内，$\mathsf E_\theta$ 与任何零漂移世界都不能并存。若只含零漂移世界，共同 $v_J$ 固定 $n$、$a=\theta n$；(22.11)是关于 $u$ 的首项系数为负一的二次式，至多给两个来源，且(20.11)及整个增益公式使每个来源至多给一个世界。因此高参数分支也至多二元。

综上，例外平面的任意共同双预测纤维均至多二元，与给定三个不同世界矛盾。这一证明不使用 V 式(31.13)的完整父恢复链；没有除以漂移、坏主元或采样增益，低次数、零漂移和所有采样零点均由 V 的完整分类保留。$\square$

本章把原秩一关系接到完整双预测的仿射提升，通过一个十二次迹约束及其恒零平面的有限整数证书，得到全参数的统一有限性；例外平面复用 V 的完整实际子纤维分类。有限次数根界、伴随矩阵及多项式消元均为成熟工具，具体原钟模型的有限性接合归 repo-derived，不申领文献首创，也不主张二十四是最优上界。两种第六预测不能在不可重置轨迹上默认共同取得；跨迹层三世界的实际末响应匹配、同臂重复目标对、一般共同父 $L_2$ 与原根八读／九读问题仍未由本条解决。

## 追加锚（本行以下为增补区）

## 23. 物理源四元签名单射与非零偏离 MM 碰撞的穷尽父坐标

**定理 23.1（包括正奇异层的源签名单射）。** 在全部逐项严格正、秩一、迹一的实二阶来源中，限制到 $\Phi\ne0$ 的源域。取定义8.1及(8.5)—(8.6)的原源函数，则

$$
P\longmapsto\bigl(k(P),q(P),\mu(P),\eta(P)\bigr)
\tag{23.1}
$$

为单射。

证明。以下写 $u=\nu_0$、$h=u(u+1)$、$\ell=u^2+3u-4$。正性给 $u,n,a,h>0$，因而 $k=a/n>0$。在 $a=kn$ 下置

$$
\begin{gathered}
z=(nu^2,nu,n,h)^{\mathsf T},\qquad x=z/\Phi,\\
\mathsf A(k)=
\begin{pmatrix}
3k+8&3k+18&-10k-30&-23\\
5k&15k&-20k&5-20k\\
10+10k&19+8k&-36-32k&-29\\
160+135k&272+93k&-560-420k&-381
\end{pmatrix}.
\end{gathered}
\tag{23.2}
$$

将(8.1)、(8.5)—(8.6)逐项展开，得到

$$
\mathsf A(k)z=
\begin{pmatrix}\Phi\\5\Delta/n\\\Psi_6\\\Psi_7\end{pmatrix},
\qquad
\mathsf A(k)x=
\begin{pmatrix}1\\q\\\mu\\\eta\end{pmatrix}.
\tag{23.3}
$$

这里第二行使用 $\Delta/n=k n\ell+(1-4k)h$，未除 $\Delta$。若两个来源有相同的四元签名，它们有同一个 $k$，且其归一化提升之差属于 $\ker\mathsf A(k)$。

相同的 $k,x$ 已足以恢复原来源。用 $x_0,x_1,x_2,x_3$ 表示 $x$ 的四个分量，则 $x_2=n/\Phi\ne0$、$x_3=h/\Phi\ne0$，且

$$
u=x_1/x_2,\qquad
\Phi=u(u+1)/x_3,\qquad n=\Phi x_2,\qquad a=kn.
\tag{23.4}
$$

由既有四迹逆(20.11)随即唯一恢复 $P$。因此只需证明同签名来源的归一化提升相同。

直接计算行列式给

$$
\det\mathsf A(k)=40Q(k),\qquad
Q(k)=6k^4+15k^3-18k^2-29k-8.
\tag{23.5}
$$

在 $k>0$ 上，

$$
\frac{d}{dk}\frac{Q(k)}{k^2}
=12k+15+\frac{29}{k^2}+\frac{16}{k^3}>0,
\qquad
Q(159/100)=-\frac{48643867}{50000000},\quad
Q(8/5)=\frac{176}{625}.
\tag{23.6}
$$

所以 $Q$ 恰有一个正根 $\kappa$，且 $159/100<\kappa<8/5$。若 $k\ne\kappa$，(23.3)的系数矩阵可逆，两个提升相同；(23.4)即给结论。

现在处理整个 $k=\kappa$ 层。定义

$$
b(k)=
\begin{pmatrix}
32k^3+25k^2-78k-39\\
8k^3+7k^2-11k-6\\
12k^3+9k^2-28k-14\\
k(k+1)(2k+1)
\end{pmatrix}.
\tag{23.7}
$$

有 $\mathsf A(k)b(k)=(0,0,0,4Q(k))^{\mathsf T}$。将 $\mathsf A(k)$ 的前三行删去第 $j$ 列所得三阶行列式乘以 $(-1)^j$，其中 $j=0,1,2,3$，所得四个数恰为 $-10b_j(k)$。尤其最后一个为 $-10k(k+1)(2k+1)\ne0$。因此在 $k=\kappa$ 时矩阵秩恰为三，且核恰为 $\mathbb R b(\kappa)$。

物理来源还限制这一核能连接的点。由定义8.1，每个来源唯一写为 $P(s,t)$，其中 $s,t>0$。等式 $a=kn$ 正是

$$
\bigl((3-k)t+1-2k\bigr)s=(k-1)-(2-k)t.
\tag{23.8}
$$

当 $k=\kappa$ 时置

$$
\alpha=\frac{k-1}{2-k},\qquad
\beta=\frac{2k-1}{3-k}.
\tag{23.9}
$$

分母为正，并且

$$
\alpha-1=\frac{2k-3}{2-k}>0,\qquad
\beta-\alpha=\frac{1+k-k^2}{(3-k)(2-k)}>0,\qquad
2-\beta=\frac{7-4k}{3-k}>0.
\tag{23.10}
$$

中间的正号可由 $k>159/100>1/2$、$k<8/5$ 及 $1+8/5-(8/5)^2=1/25$ 得到，因为 $1+k-k^2$ 在 $k>1/2$ 上严格递减。若 $t=\beta$，(23.8)左边为零，右边为 $(2-k)(\alpha-\beta)\ne0$，故这个分母零点不可能是来源。其余情形，(23.8)给

$$
s=\frac{2-k}{3-k}\frac{\alpha-t}{t-\beta}.
\tag{23.11}
$$

由 $s>0$ 与 $\alpha<\beta$，恰有 $\alpha<t<\beta$，从而 $1<t<2$。再由原源公式，

$$
u-1=\frac{s+t-1}{1+st}>0,\qquad
2-u=\frac{2-t+s(t-1)}{1+st}>0.
\tag{23.12}
$$

所以这个奇异层上的每个物理来源都满足 $1<u<2$。

设同签名的两个来源在这个层上，其提升为 $x^{(1)},x^{(2)}$，首步迹为 $u_1,u_2$。若提升不同，则存在非零实数 $\lambda$ 使

$$
x^{(1)}-x^{(2)}=\lambda b(\kappa).
\tag{23.13}
$$

每个提升的前三分量为 $c_i(u_i^2,u_i,1)$，其中 $c_i=n_i/\Phi_i\ne0$；不要求两个 $c_i$ 同号。向量 $(1,-u_1-u_2,u_1u_2)$ 同时消去这两个三元组。因 $\lambda\ne0$，(23.13)迫使

$$
C(u_1,u_2)=0,\qquad
C(v,w)=b_0(\kappa)-(v+w)b_1(\kappa)+vw b_2(\kappa).
\tag{23.14}
$$

这一步不要求 $u_1\ne u_2$。为确定其符号，先把四角值视为 $k$ 的多项式：

$$
\begin{aligned}
C_{11}(k)&=b_0(k)-2b_1(k)+b_2(k)
 =28k^3+20k^2-84k-41,\\
C_{12}(k)=C_{21}(k)&=b_0(k)-3b_1(k)+2b_2(k)
 =32k^3+22k^2-101k-49,\\
C_{22}(k)&=b_0(k)-4b_1(k)+4b_2(k)
 =48k^3+33k^2-146k-71.
\end{aligned}
\tag{23.15}
$$

它们在 $k\ge3/2$ 上的导数分别至少为 $165,181,277$，故严格递增。在右端点，

$$
C_{11}(8/5)=-\frac{1189}{125},\qquad
C_{12}(8/5)=-\frac{2901}{125},\qquad
C_{22}(8/5)=-\frac{2939}{125}.
\tag{23.16}
$$

因此 $k=\kappa$ 时四角值都严格负。对任意 $v,w\in[1,2]$，双仿射插值为

$$
\begin{aligned}
C(v,w)={}&(2-v)(2-w)C_{11}(\kappa)\\
&+\bigl((v-1)(2-w)+(2-v)(w-1)\bigr)C_{12}(\kappa)\\
&+(v-1)(w-1)C_{22}(\kappa).
\end{aligned}
\tag{23.17}
$$

三个系数非负且和为一，故 $C(v,w)<0$。由(23.12)，这适用于 $v=u_1,w=u_2$，与(23.14)矛盾。所以两个归一化提升相同，(23.4)与(20.11)恢复同一个来源。常规层与正奇异层至此全部包含。$\square$

**定理 23.2（完整 MM 碰撞的父坐标与一般 L2 的必需边）。** 保持定义1.1、8.1的整个世界域、原时钟与字面父历史 $H=H^-_{\theta,\xi}$，并设 $\xi\ne0$。若两个不同完整世界 $W_i=(P_i,g_i,d_i)\in\mathcal F(H)$ 满足

$$
r_M^{(6)}(W_1)=r_M^{(6)}(W_2),\qquad
r_{MM}^{(7)}(W_1)=r_{MM}^{(7)}(W_2),
\tag{23.18}
$$

则它们的来源满足

$$
\begin{gathered}
\Phi_1\Phi_2\ne0,\qquad
\mu_1=\mu_2,\quad\eta_1=\eta_2,\quad q_1\ne q_2,\quad k_1\ne k_2,\\
\xi=\frac{k_2-k_1}{q_1-q_2},\qquad
\theta=k_1+\xi q_1,\qquad
d_i=\frac{120h_i\xi}{\Phi_i}.
\end{gathered}
\tag{23.19}
$$

反向构造不预先固定父参数：任取两个物理来源 $P_1,P_2$，使 $\Phi_1\Phi_2\ne0$、$\mu_1=\mu_2$、$\eta_1=\eta_2$、$q_1\ne q_2$、$k_1\ne k_2$，用(23.19)重建 $\xi,\theta,d_i$，并用(8.2)的四节点插值定义整个 $g_i$。所得两个世界不同，属于同一个重建的 $\mathcal F(H^-_{\theta,\xi})$，并满足(23.18)。所以这些有序源对与所有非零 $\xi$ 父历史上的同父 MM 碰撞对一一对应，参数和整个世界均由所给公式恢复。在一个预先固定的父历史上，该对应恰限制为重建参数等于其给定 $(\theta,\xi)$ 的源对。

对任意 $K\subseteq\mathcal F(H)$，若 $L_2(K,H)$ 成立，则其中必有一个满足(23.18)—(23.19)的不同世界对，位于同一个实际第六 $M$ 子历史。这是一般 $L_2$ 的必要条件；同臂另一末动作与另一第六臂的碰撞对可以分别不同。

证明。由定理8.2的无除数父方程 $d_i\Phi_i=120h_i\xi$，$h_i>0$ 与 $\xi\ne0$ 给 $d_i\ne0$、$\Phi_i\ne0$，并给

$$
\theta=k_i+\xi q_i,\qquad
r_M^{(6)}(W_i)=120(1+2\theta)+120\xi\mu_i,\qquad
r_{MM}^{(7)}(W_i)=210(2+3\theta)+30\xi\eta_i.
\tag{23.20}
$$

故(23.18)推出 $\mu_1=\mu_2$、$\eta_1=\eta_2$。若 $q_1=q_2$，共同父条件再给 $k_1=k_2$。定理23.1于是给 $P_1=P_2$。父方程随即唯一给相同的 $d_i$；时钟零至三的(8.2)给相同的整个至多三次增益。两个完整世界遂相同，矛盾。因此 $q_1\ne q_2$。从两个共同父等式相减，得 $k_2-k_1=\xi(q_1-q_2)\ne0$，从而得到(23.19)。这也说明不同的完整世界在这里必有不同的来源。

反向构造中，$q_1-q_2\ne0$ 与 $k_2-k_1\ne0$ 保证 $\xi\ne0$。由(23.19)，$k_1+\xi q_1=k_2+\xi q_2=\theta$。再由(8.5)中的 $q=5\Delta/(n\Phi)$，对每个来源都有

$$
d_i\Phi_i=120h_i\xi,\qquad
d_i\Delta_i=24h_i n_i\xi q_i
=24h_i(\theta n_i-a_i).
\tag{23.21}
$$

定理8.2于是保证六次父读数逐项相同；(23.20)及共同 $\mu,\eta$ 保证实际第六 $M$ 和末 $MM$ 响应相同。四节点插值保留原时钟 $0,1,2,3$，且 $g_i$ 不恒零：否则时钟零的读数迫 $d_i=0$，时钟三却要求 $d_i=6$。来源严格正、秩一、迹一由其原源域保证；$q_1\ne q_2$ 保证来源不同，故完整世界不同。正向恢复与此构造互逆，给所述穷尽对应。

最后设 $L_2(K,H)$。按(1.2)的第六 $M$ 条款，有同一个实际响应 $w$，使

$$
K_{M,w}=K\cap\mathcal F(H,M,w),\qquad
L_1(K_{M,w},(H,M,w)).
\tag{23.22}
$$

对这个 $L_1$ 使用末 $M$ 条款，得到一个末响应 $m$，其真实响应纤维至少含两个不同世界。取其中任意两个，就得到(23.18)，因此必受(23.19)的父坐标约束。同一个 $L_1$ 的末 $J$ 条款可以由另两个世界见证，但它们也必须位于这个同一 $K_{M,w}$，共享实际第六读数 $w$。第六 $J$ 条款则选取自己的实际响应 $v$ 和 $L_1$ 子族，两个末动作又各可由不同的世界对见证。这里没有将四个末碰撞对强制合为一个或两个世界对，也没有要求 $M$ 臂的锚定对共享未执行的第六 $J$ 响应。碰撞式是允许响应函数之间的等式，策略仍只执行一条不可复制、不可重置且每步立即读取的实际路径。

全证明不除 $\Delta$、$g(6)$、$g(7)$ 或任何采样增益；低次数、任意增益符号及采样零点均保留。$\xi=0$ 及其 $\Phi=0$、零漂移分支仍属原问题，但不在本条条件域内。上述必要边尚不提供其余三种末碰撞与它的共同父实现，也不决定一般 $L_2$ 的存在、原根八读／九读问题或九读上界。$\square$

## 追加锚（本行以下为增补区）

## 24. 单个实际 M 子纤维的全参数有限性与完整根重构

**定义 24.1（单响应直线及无除数消元式）。** 使用定义1.1的整个 $\mathcal W_3$、定义8.1的字面父历史和原时钟。父方程与响应复用定理8.2，源二次曲面与唯一源逆复用(10.2)—(10.3)、(20.11)；这些供给的[固定正文](https://github.com/the-omega-institute/trureturing/blob/f4f1d65445c7ee55f2619e5597e939eebdbeb91c/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md)均按原前件使用。

给定 $\theta,w\in\mathbb R$、$\xi\ne0$，置

$$
\begin{gathered}
H=H^-_{\theta,\xi},\qquad H_M=(H,M,w),\qquad
K_{\theta,\xi,w}=\mathcal F(H_M),\\
b=\frac{w-120(1+2\theta)}{120\xi}.
\end{gathered}
\tag{24.1}
$$

以下 $u=\operatorname{tr}(MP)$、$n,a$ 为既有源迹坐标，$h=u(u+1)$、$\ell=u^2+3u-4$、$\Phi,\Delta,\Psi_6$ 沿用(8.1)、(8.6)。记 $\mathcal Q(u,n,a)=\det P(u,n,a)$，其中 $P$ 是(20.11)的唯一源逆。定义

$$
\begin{aligned}
\alpha&=3h-10,\qquad \beta=8u^2+18u-30,\\
A&=(10-3b)u^2+(8-3b)u+10b-32,\\
B&=(10-8b)u^2+(19-18b)u+30b-36,\\
C&=(23b-29)h,\\
\mathcal L&=Aa+Bn+C=\Psi_6-b\Phi,\\
\mathcal T&=(\theta n-a)\Phi-5\xi\Delta.
\end{aligned}
\tag{24.2}
$$

字母 $b$ 是单个实际第六 $M$ 响应的归一化参数，不是另一个读出端口。为构造多项式，暂把 $u,b,\theta,\xi$ 视为独立变量。按齐次坐标 $x=(a,n,z)^{\mathsf T}$，定义对称矩阵

$$
\mathsf Q=
\begin{pmatrix}
1&-1/2&-u-1\\
-1/2&-1&2u+1\\
-u-1&2u+1&-u^2+u+1
\end{pmatrix},
\tag{24.3}
$$

$$
\mathsf T=
\begin{pmatrix}
-\alpha&(\theta\alpha-\beta-5\xi\ell)/2&(23+20\xi)h/2\\
(\theta\alpha-\beta-5\xi\ell)/2&\theta\beta&-(23\theta+5\xi)h/2\\
(23+20\xi)h/2&-(23\theta+5\xi)h/2&0
\end{pmatrix}.
\tag{24.4}
$$

于是 $x^{\mathsf T}\mathsf Qx$、$x^{\mathsf T}\mathsf Tx$ 分别是 $\mathcal Q$、$\mathcal T$ 关于 $(a,n)$ 的二次齐次化。令 $v=(A,B,C)^{\mathsf T}$，并置

$$
\begin{aligned}
\rho&=v^{\mathsf T}\operatorname{adj}(\mathsf Q)v,\\
\sigma&=v^{\mathsf T}\operatorname{adj}(\mathsf T)v,\\
\tau&=v^{\mathsf T}\bigl(
\operatorname{adj}(\mathsf Q+\mathsf T)
-\operatorname{adj}(\mathsf Q)-\operatorname{adj}(\mathsf T)
\bigr)v,\\
R(u,b,\theta,\xi)&=\tau^2-4\rho\sigma.
\end{aligned}
\tag{24.5}
$$

伴随矩阵在此仅由二阶子式定义，不要求任何矩阵可逆。(24.2)—(24.5)给出一个完全指定的有理系数多项式，不含按参数值实施的除法。

**引理 24.2（两张主元图上的同一消元式）。** 多项式 $R$ 满足 $\deg_uR\le16$。对任意实 $u,b,\theta,\xi,n,a$，有

$$
\mathcal Q=\mathcal L=\mathcal T=0
\quad\Longrightarrow\quad R(u,b,\theta,\xi)=0.
\tag{24.6}
$$

此必要条件包括 $A=0$、$B=0$ 以及二次式首项消失的全部分支。

证明。对两个对称二阶矩阵 $F,G$，令

$$
\mathfrak d(F,G)=
\bigl(\det(F+G)-\det F-\det G\bigr)^2
-4\det F\det G.
\tag{24.7}
$$

若其二元齐次二次式写成
$f_2r^2+f_1rs+f_0s^2$ 与 $g_2r^2+g_1rs+g_0s^2$，逐项展开给

$$
\begin{aligned}
\mathfrak d(F,G)
&=(f_2g_0-f_0g_2)^2
 -(f_2g_1-f_1g_2)(f_1g_0-f_0g_1)\\
&=\det
\begin{pmatrix}
f_2&f_1&f_0&0\\
0&f_2&f_1&f_0\\
g_2&g_1&g_0&0\\
0&g_2&g_1&g_0
\end{pmatrix}.
\end{aligned}
\tag{24.8}
$$

这是齐次二次结式的行列式表达，首项为零时仍是同一个多项式。若两式有共同非零实向量，取可逆线性换元将该向量移到 $(1,0)$；两式的首项遂同时为零，(24.8)为零。换元使(24.7)乘以换元行列式的四次方，所以原来的 $\mathfrak d$ 也为零。

现在取

$$
U_A=\begin{pmatrix}-B&-C\\A&0\\0&A\end{pmatrix},
\qquad
U_B=\begin{pmatrix}B&0\\-A&-C\\0&B\end{pmatrix}.
\tag{24.9}
$$

对任意三阶对称矩阵 $S$ 及列向量为 $p,q$ 的三行二列矩阵 $U$，二阶行列式展开给

$$
\det(U^{\mathsf T}SU)
=(p\mathbin\times q)^{\mathsf T}\operatorname{adj}(S)
 (p\mathbin\times q).
\tag{24.10}
$$

$U_A$、$U_B$ 的列叉积分别为 $Av$、$-Bv$。对 $S=\mathsf Q,\mathsf T,\mathsf Q+\mathsf T$ 使用(24.10)，得到无除数恒等式

$$
\begin{aligned}
\mathfrak d(U_A^{\mathsf T}\mathsf Q U_A,
             U_A^{\mathsf T}\mathsf T U_A)&=A^4R,\\
\mathfrak d(U_B^{\mathsf T}\mathsf Q U_B,
             U_B^{\mathsf T}\mathsf T U_B)&=B^4R.
\end{aligned}
\tag{24.11}
$$

若 $A\ne0$ 且三式同时成立，$U_A(n,1)^{\mathsf T}=A(a,n,1)^{\mathsf T}$ 给两张限制二次式的共同非零根，故第一式强制 $R=0$。若 $B\ne0$，用 $U_B(a,1)^{\mathsf T}=B(a,n,1)^{\mathsf T}$ 和第二式。若 $A=B=0$，$\mathcal L=0$ 迫 $C=0$，于是 $v=0$，(24.5)直接给 $R=0$。因此没有遗漏坏主元。

最后，$\mathsf Q,\mathsf T$ 的每项关于 $u$ 的次数至多二，$v$ 的每项也是如此；$\rho,\sigma,\tau$ 的次数至多八，故 $R$ 的次数至多十六。这是多项式环内的界，任意参数特殊化均保留。$\square$

**引理 24.3（所有实参数下的非塌缩）。** 对每个 $(b,\theta,\xi)\in\mathbb R^3$，$R(\,\cdot\,,b,\theta,\xi)$ 都不是零多项式。

证明。定义

$$
\begin{aligned}
E&=(50-15b)\theta+(12b^2-55b+50)\xi-40b+50,\\
H_0&=5(5b-16)\theta-(5b-16)(5b-6)\xi+15(5b-6),\\
H_-&=10(b-3)\theta-2(b-3)(8b-9)\xi+5(8b-9).
\end{aligned}
\tag{24.12}
$$

由(24.2)—(24.5)的子式乘法，得到三个多项式恒等式

$$
[u^{16}]R=100E^2,\qquad
R(0,b,\theta,\xi)=57600H_0^2,\qquad
R(-1,b,\theta,\xi)=562500H_-^2.
\tag{24.13}
$$

这里 $0,-1$ 只是多项式的代入点，并非物理来源。若 $R$ 恒零，则 $E=H_0=H_-=0$。按 $(\theta,\xi,1)$ 排列这三个仿射式的系数，其行列式为

$$
\det\begin{pmatrix}
50-15b&12b^2-55b+50&-40b+50\\
5(5b-16)&-(5b-16)(5b-6)&15(5b-6)\\
10(b-3)&-2(b-3)(8b-9)&5(8b-9)
\end{pmatrix}
=125b(b-1)(b-2).
\tag{24.14}
$$

非零向量 $(\theta,\xi,1)^{\mathsf T}$ 在其核中，故 $b\in\{0,1,2\}$。当 $b=1$ 时，$4H_0-11H_-=-5$，矛盾。当 $b=0,2$ 时，$H_0=H_-=0$ 关于 $(\theta,\xi)$ 的二阶系数行列式分别为 $1440,-180$，所以唯一可能参数及其残余值为

$$
\begin{array}{c|c|c|r}
b&\theta&\xi&R(1,b,\theta,\xi)\\ \hline
0&-3/8&-5/8&55531247\\
2&0&-5/2&-4146716
\end{array}.
\tag{24.15}
$$

两项都非零，再次矛盾。这里并未假设首项、$A$、$B$ 或 $\xi$ 非零；(24.13)—(24.15)排除的是恒零，允许普通降次和重根。$\square$

**引理 24.4（每个正迹层至多两个来源候选）。** 对每个实 $b$ 和每个 $u>0$，仿射方程

$$
\mathcal Q(u,n,a)=0,\qquad Aa+Bn+C=0
\tag{24.16}
$$

至多有两个实解 $(n,a)$。此结论尚未施加来源正性、父条件或 $\Phi\ne0$。

证明。先排除零直线。若 $A=B=C=0$，由 $h>0$ 得 $b=29/23$，此时

$$
23A=143u^2+97u-446,\qquad
23B=-(2u^2+85u-42).
\tag{24.17}
$$

这两个多项式没有共同零点，直接复用(20.6)的证书。因此 $(A,B,C)\ne0$。若 $A=B=0$，则 $C\ne0$，(24.16)无解；以下 $\mathcal L=0$ 是一条真正的仿射直线。

由(24.3)，

$$
\det\mathsf Q=\frac{u^2-u-1}{4}.
\tag{24.18}
$$

若 $u^2-u-1\ne0$，源二次曲面在此平面上不含直线分量：二次多项式若含一次因子，其齐次二次型是两个线性式的乘积，对称矩阵秩至多二，与(24.18)矛盾。因此把 $\mathcal Q$ 限制到 $\mathcal L=0$ 得到非零的至多二次多项式，至多有两个实根。

唯一正的退化迹为 $\varphi=(1+\sqrt5)/2$。使用 $\varphi^2=\varphi+1$，(10.3)给

$$
\mathcal Q(\varphi,n,a)
=(a-\varphi n)
 \bigl(a+(\varphi-1)n-2(\varphi+1)\bigr).
\tag{24.19}
$$

若 $\mathcal L$ 包含第一条分量 $a=\varphi n$，必须 $C=0$、$\varphi A+B=0$。前者给 $b=29/23$，而此时

$$
\varphi A+B=\frac{280-150\varphi}{23}\ne0.
\tag{24.20}
$$

若 $\mathcal L$ 包含第二条分量，必须同时有

$$
\begin{aligned}
B-(\varphi-1)A
 &=(35-33\varphi)b+51\varphi-66=0,\\
2(\varphi+1)A+C
 &=(36\varphi+25)b-30\varphi-37=0.
\end{aligned}
\tag{24.21}
$$

这两个关于 $b$ 的仿射式的系数行列式为

$$
\det\begin{pmatrix}
35-33\varphi&51\varphi-66\\
36\varphi+25&-30\varphi-37
\end{pmatrix}
=426\varphi-491\ne0.
\tag{24.22}
$$

(24.20)、(24.22)的非零性都由 $\varphi$ 的无理性给出。故 $\mathcal L$ 与两条分量均不重合，每条至多贡献一个交点。退化层也至多有两个实解。$\square$

**定理 24.5（整个实际 M 子纤维至多三十二个完整世界）。** 对任意 $\theta,w\in\mathbb R$、$\xi\in\mathbb R\setminus\{0\}$，在定义1.1的全部严格正秩一迹一实二阶来源、整个非零且次数至多三的增益和任意实常漂移模型中，

$$
|K_{\theta,\xi,w}|\le32.
\tag{24.23}
$$

其完整世界恰由以下有限根描述恢复。取(24.1)的 $b$，取非零多项式 $R(\,\cdot\,,b,\theta,\xi)$ 的全部不同正实根 $u$。对每个根保留全部满足

$$
\mathcal Q=0,\qquad \mathcal L=0,\qquad \mathcal T=0,
\qquad \Phi\ne0,\qquad
P(u,n,a)>0\text{ 逐项}
\tag{24.24}
$$

的实解 $(n,a)$。用(20.11)恢复 $P$，再令

$$
d=\frac{120h\xi}{\Phi},
\qquad g=\text{(8.2)四个原钟节点值的唯一至多三次插值多项式}.
\tag{24.25}
$$

该对应在所保留三元组与 $K_{\theta,\xi,w}$ 之间是双射。每个根的候选可用次数至多二的方程给出：$A\ne0$ 时先取 $a=-(Bn+C)/A$；$A=0,B\ne0$ 时先取 $n=-C/B$；再解 $\mathcal Q=0$ 并施加其余过滤。$A=B=0$ 时没有候选。所有方程按实际次数求根，不要求二次首项非零，也不以根的重数重复计数。

证明。任取实际世界。其严格正来源有 $u,n,h>0$，并由(10.2)—(10.3)满足源逆与 $\mathcal Q=0$。定理8.2的无除数父方程给

$$
d\Phi=120h\xi\ne0,
\qquad d\Delta=24h(\theta n-a).
\tag{24.26}
$$

因此 $\Phi\ne0$，漂移唯一等于(24.25)，消去 $d$ 得 $\mathcal T=0$。实际第六 $M$ 读数由(8.7)给 $\Psi_6/\Phi=b$，故 $\mathcal L=0$。引理24.2于是给 $R(u,b,\theta,\xi)=0$，包括全部坏主元。故每个实际世界均进入(24.24)的候选，未丢弃任何 $\Delta=0$ 来源。

反向取任一保留三元组。既有源逆给 $\operatorname{tr}P=1$ 及三个声明的迹；$\mathcal Q=\det P=0$ 与逐项正性给秩恰为一。由正迹得 $n>0$，所以(8.2)的插值及(24.25)都有定义。由 $\mathcal T=0$，

$$
\frac{120h\xi}{\Phi}\Delta
=24h(\theta n-a).
\tag{24.27}
$$

故(24.26)的两个父方程成立。定理8.2保证全部六个原父读数；$\mathcal L=0$ 和 $\Phi\ne0$ 再保证第六 $M$ 的实际读数恰为 $w$。增益不可能恒零，因为同一个原历史的时钟零读数为零、时钟三读数为六；零增益会迫使常漂移同时等于零和六。因此恢复的是合法完整世界，包括整个多项式，而非有限节点值的等价类。

源逆唯一；在固定 $\theta,\xi$ 下漂移由(24.26)唯一；整个增益由四节点插值唯一。不同保留三元组给不同来源，因而给不同完整世界；上述正反构造互逆。引理24.3保证至多十六个不同正根，引理24.4保证每根至多两个候选，得到(24.23)。其余过滤只删除候选。

两张回代图穷尽所有候选，是因为引理24.4已经排除正 $u$ 上的 $A=B=C=0$；$A=B=0$ 时 $C\ne0$，无解。各图中的源二次式不恒零也由该引理的直线分量排除证明保证。这里没有除以 $\Delta$、$g(6)$、$g(7)$ 或任何采样增益；没有假设增益符号、实际次数、采样非零或消元根为单根。$\Delta=0$、低次数、全部增益符号、采样零点及消元重根全部保留。

这是一份任意实参数下的有限数学描述。它不把任意实数参数自动赋予有效有限位表示，也不据此宣称有限位程序可以取得全部根或判定全部相等关系。$\square$

**推论 24.6（同一个实际子纤维上的两末碰撞判据）。** 固定定理24.5的同一个 $H_M=(H^-_{\theta,\xi},M,w)$ 及完整根重构集 $K=K_{\theta,\xi,w}$。对 $D\in\{M,J\}$，令 $r_D^K(W)$ 表示从该实际子历史在原时钟七选取 $D$ 的响应函数，并定义

$$
N_D(K)\quad\Longleftrightarrow\quad
\exists W\ne W'\in K:\ r_D^K(W)=r_D^K(W').
\tag{24.28}
$$

则

$$
L_1(K,H_M)\quad\Longleftrightarrow\quad
N_M(K)\ \land\ N_J(K).
\tag{24.29}
$$

每个末动作的存在量词至多涉及 $\binom{32}{2}=496$ 个无序不同世界对，两项可以由不同对见证。特别地，对定理23.2的任一实际 MM 碰撞，使用它重建的同一个 $(\theta,\xi)$ 和共同 $\mu=b$，取 $w=120(1+2\theta)+120\xi b$；锚定对已给 $N_M(K)$，另一项恰须在本定理恢复的同一个 $K$ 内寻找 $N_J(K)$。

证明。(24.29)直接展开(1.2)：每个末动作都有一个至少含两个不同世界的实际响应纤维，当且仅当该响应函数在 $K$ 上非单射。一个碰撞对已经保证 $|K|\ge2$。定理24.5供应全部候选，故两种末动作的比较均无遗漏。末响应函数可分别使用(8.7)的 $m,j$；这些函数值是对完整世界的数学比较，未增加实际读数，也未把未选动作的预测改成已取得数据。

一般共同父条件仍须保持全部独立存在量词。对 $E\in\{M,J\}$ 定义父参数集

$$
\mathcal P_E=\left\{(\theta,\xi):\ \exists z_E\in\mathbb R,\
L_1\bigl(\mathcal F(H^-_{\theta,\xi},E,z_E),
         (H^-_{\theta,\xi},E,z_E)\bigr)\right\}.
\tag{24.30}
$$

仍由(1.2)，对完整父纤维有

$$
L_2\bigl(\mathcal F(H^-_{\theta,\xi}),H^-_{\theta,\xi}\bigr)
\quad\Longleftrightarrow\quad
(\theta,\xi)\in\mathcal P_M\cap\mathcal P_J.
\tag{24.31}
$$

两个第六臂各自选择自己的实际响应 $z_E$；每个实际子纤维的两个末动作又各自选择碰撞对。无需同对、四个不同世界、两臂共享来源或共享互择第六预测。(24.29)—(24.31)只是既有失败递归的量词重写；新增有限性供应固定非零 $\xi$ 实际 $M$ 子纤维的完整候选全集，未给 $\mathcal P_M\cap\mathcal P_J$ 的非空或空结论。

$\xi=0$ 的全局分支仍在原目标内，不能由(24.23)延拓覆盖：[V，定理28.2](https://github.com/the-omega-institute/trureturing/blob/f4f1d65445c7ee55f2619e5597e939eebdbeb91c/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)已给出零偏离下连续的实际 $M$ 子纤维。本章不结清一般共同父 $L_2$、祖先兼容、原根八读／九读问题或九读上界。所用四节点插值、二次结式和直线与圆锥交点界均为成熟代数工具；固定 FIB 单实际子纤维的非塌缩、完整重构和统一界是这里的仓内推导，不作全球首创主张。$\square$

## 追加锚（本行以下为增补区）

## 25. 精确 J 失败父附近的整个 M 臂恢复

**定义 25.1（紧化父曲线与分离函数）。** 保留定义1.1的整个 $\mathcal W_3$、定义8.1的完整父历史及原时钟。令

$$
\begin{aligned}
I_\theta&=[0.280163636202,\ 0.280163636204],\\
I_\xi&=[-0.845640162242,\ -0.845640162239],\qquad
\mathcal U=I_\theta\times I_\xi .
\end{aligned}
\tag{25.1}
$$

所有有限小数均为精确有理数。以下多项式只用于分析来源，不增加观察端口。对正源坐标 $(s,t)$ 置

$$
\begin{gathered}
D=1+st,\quad U=s+t+st,\quad N=1+2s+t+st,\quad A=1+s+2t+3st,\\
H=U(U+D),\quad L=U^2+3UD-4D^2,\\
\widehat\Phi=(3H-10D^2)A+(8U^2+18UD-30D^2)N-23HD,\\
\widehat\Delta=(N-4A)HD+ANL,\\
\widehat V=10U^2+19UD-36D^2,\qquad
\widehat X=20U^2+34UD-70D^2,\\
\widehat M=(N+2A)\widehat V-10AL-29HD,\\
\widehat E=4(2N+3A)\widehat X-105AL-381HD .
\end{gathered}
\tag{25.2}
$$

这些式子分别满足 $\widehat\Phi=D^3\Phi$、$\widehat\Delta=D^4\Delta$、$\widehat M=D^3\Psi_6$、$\widehat E=D^3\Psi_7$。对双次数至多 $(m,n)$ 的多项式 $f(s,t)$，记

$$
\mathfrak C_{m,n}f(x,y)
=(1-x)^m(1-y)^n
 f\!\left(\frac{x}{1-x},\frac{y}{1-y}\right).
\tag{25.3}
$$

右边按多项式恒等式延伸到闭方形 $Q=[0,1]^2$。定义

$$
\begin{gathered}
p=\mathfrak C_{3,3}\widehat\Phi,\quad
d=\mathfrak C_{4,4}\widehat\Delta,\quad
m=\mathfrak C_{3,3}\widehat M,\quad
e=\mathfrak C_{3,3}\widehat E,\quad r=e-20m,\\
f=f_{\theta,\xi}
=\mathfrak C_{4,4}\bigl((\theta N-A)\widehat\Phi-5\xi\widehat\Delta\bigr),\\
c=f_x(r_y p-rp_y)-f_y(r_xp-rp_x),\qquad
g_0=3m-2p,\quad g_1=m-p .
\end{gathered}
\tag{25.4}
$$

这里 $p,d,m,e,r,f,c$ 均为多项式，字母 $d$ 在本章(25.3)以后的曲线计算中表示紧化多项式，而非世界的常漂移。世界漂移仍记 $d_W$。在 $0<x,y<1$ 且 $p\ne0$ 处有

$$
\mu=\frac mp,\qquad \eta=\frac ep,\qquad
\rho=\eta-20\mu=\frac rp .
\tag{25.5}
$$

由定理8.2，固定 $(\theta,\xi)\in\mathcal U$ 的全部实际父世界，与曲线

$$
\Gamma_{\theta,\xi}
=\{(x,y)\in(0,1)^2:f_{\theta,\xi}(x,y)=0,\ p(x,y)\ne0\}
\tag{25.6}
$$

双射。该双射先取 $s=x/(1-x)$、$t=y/(1-y)$，再使用(8.1)的来源、$d_W=120h\xi/\Phi$ 和(8.2)的整个插值增益。这里 $\xi\ne0$，故实际世界确有 $\Phi\ne0$；没有除以 $\Delta$ 或任何采样增益。

**引理 25.2（全闭方形的曲线与分离证书）。** 对每个 $(\theta,\xi)\in\mathcal U$，闭方形上有

$$
f=0\quad\Longrightarrow\quad c\,g_0\,g_1\ne0 .
\tag{25.7}
$$

$p=d=0$ 在 $Q$ 中恰有一个解 $b_*$，且

$$
b_*\in B_*=[0.7053,0.7057]\times[0.3558,0.3562]
\subset(0,1)^2 .
\tag{25.8}
$$

$f=0$ 与方形边界恰有下表四个交点；表内变化坐标的开区间各含一个单根，$\mu$ 的界对整段边界区间成立：

$$
\begin{array}{c|c|c|c}
\text{边}&\text{变化坐标区间}&\operatorname{sgn}p&\mu\\ \hline
x=0&0.6306<y<0.6307&-& (0.69,0.72)\\
y=1&0.5778<x<0.5779&-& (0.81,0.82)\\
x=1&0.00511<y<0.00512&+& (1.57,1.59)\\
x=1&0.5627<y<0.5628&-& (0.60,0.65)
\end{array}
\tag{25.9}
$$

边 $y=0$ 无根，四角也无根。

证明。给出完全由(25.1)—(25.4)指定的有理包含证书。使用 Bernstein 基的非负性、单位分解及二分限制恒等式；这些是成熟的多项式工具，参见 Patrikalakis、Maekawa、Cho 的 [Bernstein 基性质，§1.3.1](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node9.html)与[二分限制，§1.3.5](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node13.html)。下述系数、参数角点与递归规则给出本曲线的具体有限证书。

若 $F(x,y)=\sum a_{kl}x^ky^l$ 的双次数至多 $(M,N)$，其在 $Q$ 上的 Bernstein 系数为

$$
\beta_{ij}(F)
=\sum_{k\le i,\ l\le j}
a_{kl}\frac{\binom{i}{k}}{\binom{M}{k}}
       \frac{\binom{j}{l}}{\binom{N}{l}} .
\tag{25.10}
$$

对依赖父参数的多项式，在 $\mathcal U$ 的四个角点分别取(25.10)，再对每个系数取四值的闭区间包络。$f,c$ 关于 $(\theta,\xi)$ 都是仿射式，故这覆盖整个 $\mathcal U$；其余多项式不依赖父参数。$f,d$ 的基次数取 $(4,4)$，$p,g_0,g_1$ 取 $(3,3)$，$c$ 取 $(9,9)$。

空间二分在每个一维系数列上使用

$$
b_i^{(0)}=b_i,\qquad
b_i^{(j+1)}=\frac{b_i^{(j)}+b_{i+1}^{(j)}}2 .
\tag{25.11}
$$

左半段的新系数为 $b_0^{(i)}$，右半段为 $b_i^{(M-i)}$；对另一坐标相同。区间的上下端点分别按此正系数公式传播。称一个系数区间网为严格定号，若所有下端点严格正，或所有上端点严格负。Bernstein 凸组合恒等式保证多项式在该闭矩形上具有同一严格符号。

对根矩形 $Q$ 赋深度零。在每个矩形上先检查 $f$ 的区间系数网：严格定号就结束该支；否则，$c,g_0,g_1$ 三网均严格定号也结束该支。两项都不成立时，深度为偶数沿 $x$ 二分，为奇数沿 $y$ 二分。对(25.1)—(25.4)和(25.10)—(25.11)作有理数比较得到

$$
\begin{array}{c|r}
\text{量}&\text{值}\\ \hline
\text{全部矩形数，含非叶节点}&2165\\
\text{由 }f\text{ 严格定号结束的叶数}&702\\
\text{由 }c,g_0,g_1\text{ 均严格定号结束的叶数}&381\\
\text{最大叶深度}&22
\end{array}.
\tag{25.12}
$$

停止判据按所述顺序使用；所有终止比较均严格。这个有限递归指定了全部叶矩形及其系数，不以采样点的符号代替闭矩形包含。每个 $f=0$ 点必落在第二类叶内，故给(25.7)。

对 $p,d$ 使用相同二分规则，先以“至少一网严格定号”结束该支；否则，矩形包含于 $B_*$ 时结束；仍不满足才二分。这里两网的初始系数为精确有理数，无参数包络。所得全部矩形数为 $461$，第一类叶 $226$ 个，包含于 $B_*$ 的叶 $5$ 个，最大叶深度为 $30$。故 $Q$ 中的每个共同零点都在 $B_*$ 内。

还须证明该盒内恰有一个共同零点，不能用未排除的小盒代替存在性。令

$$
z_0=(0.7055,0.3560),\qquad
C_*=
\begin{pmatrix}
0.08021375&-0.31816718\\
0.08180923&-0.51517195
\end{pmatrix},\qquad
F_*=(p,d)^{\mathsf T}.
\tag{25.13}
$$

矩阵范数为最大绝对行和。将(25.2)—(25.4)的多项式先按 $y$、再按 $x$ 作 Horner 区间包含，给

$$
\begin{gathered}
\det C_*=-\frac{152948619972411}{10^{16}}\ne0,\qquad
\|C_*F_*(z_0)\|_\infty<7\cdot10^{-5},\\
\sup_{z\in B_*}\|I-C_*DF_*(z)\|_\infty<\frac1{50}.
\end{gathered}
\tag{25.14}
$$

$B_*$ 是以 $z_0$ 为中心、最大范数半径 $2\cdot10^{-4}$ 的闭盒。因此 $z\mapsto z-C_*F_*(z)$ 在 $B_*$ 上压缩且

$$
7\cdot10^{-5}+\frac1{50}(2\cdot10^{-4})
=7.4\cdot10^{-5}<2\cdot10^{-4}.
\tag{25.15}
$$

它将盒映入内部，标准压缩映射论证给唯一不动点；$\det C_*\ne0$ 使不动点恰为 $F_*=0$。结合全方形包含，得到(25.8)的存在与唯一性。

最后给出边界根计数。按变化坐标递增顺序，$f$ 的四阶 Bernstein 系数在边 $x=0,y=1,x=1$ 上的符号分别恒为

$$
(+,+,+,-,-),\qquad(-,-,-,+,+),\qquad(+,-,-,-,+).
\tag{25.16}
$$

这些符号同样由四个参数角点的区间包络给出。边 $y=0$ 沿 $x=1/2$ 二分后，两段的所有系数均严格正。在(25.9)四个区间的两端，$f$ 的严格符号依表顺序分别为 $(+,-),(-,+),(+,-),(-,+)$，对整个参数矩形同时成立。

一维 Bernstein 系数的变号数给区间内根数的重数上界：将 $\sum_i\beta_i\binom{4}{i}z^i(1-z)^{4-i}$ 置换 $z=v/(1+v)$ 并乘以 $(1+v)^4$，直接成为系数为 $\binom4i\beta_i$ 的普通多项式，故只用了经典 Descartes 规则。介值定理给四个区间各至少一根；(25.16)给相应总上界 $1,1,2$，所以它们全为单根且穷尽。边界端点的严格符号也排除四角。对(25.9)各段直接以 Horner 包含取 $p,m$，在排除 $p=0$ 后取商，给表内符号与 $\mu$ 界。这里边界点只承担曲线穷尽，不被当作合法正来源。$\square$

**定理 25.3（整个父纤维上的固定 MM 单射与精确父判定）。** 对每个 $(\theta,\xi)\in\mathcal U$，在整个 $\mathcal F(H^-_{\theta,\xi})$ 上，原时钟六、七的联合响应

$$
W\longmapsto
\bigl(r_M^{(6)}(W),r_{MM}^{(7)}(W)\bigr)
\tag{25.17}
$$

单射。因此从该父实际依次执行 $M,M$，至多再读两次即可恢复完整世界，并且

$$
\begin{gathered}
\forall w\in\mathbb R:\quad
\neg L_1\bigl(\mathcal F(H^-_{\theta,\xi},M,w),
                 (H^-_{\theta,\xi},M,w)\bigr),\\
\neg L_2\bigl(\mathcal F(H^-_{\theta,\xi}),H^-_{\theta,\xi}\bigr).
\end{gathered}
\tag{25.18}
$$

特别地，定理14.2指定的唯一精确零点 $x_\ddagger$ 所定义的父参数 $(\theta_\ddagger,\xi_\ddagger)$ 属于 $\mathcal U$。该精确父的实际 $J$ 臂仍由定理14.3给出 $L_1$，但其整个实际 $M$ 臂满足(25.18)，故此父不具有 $L_2$。

证明。固定 $\mathcal U$ 中一个父参数，先在整个闭方形研究 $Z=\{f=0\}$。由(25.7)，$c\ne0$，故 $\nabla f\ne0$。由(25.9)及边界单根，$Z$ 与边界横截且避开四角。隐函数定理及紧性说明 $Z$ 是紧的一维光滑流形，其边界恰为四个交点；每个连通分量是圆周或闭弧。

$p=d=0$ 的唯一点 $b_*$ 对每个父参数均属于 $Z$，因为

$$
f=\bigl(\theta\,\mathfrak C_{1,1}N-\mathfrak C_{1,1}A\bigr)p-5\xi d .
\tag{25.19}
$$

反之，$Z$ 上 $p=0$ 时，$\xi\ne0$ 强制 $d=0$，故 $b_*$ 是 $Z$ 上唯一的 $p$ 零点。由 $g_0(b_*)\ne0$ 得 $m(b_*)\ne0$。又在此点有

$$
c(b_*)=-r(b_*)\bigl(f_xp_y-f_yp_x\bigr)(b_*)\ne0.
\tag{25.20}
$$

所以 $p$ 沿 $Z$ 在该点横截过零。一个圆周分量不可能恰有一次横截零点；若圆周不含该点，则 $\rho=r/p$ 在其上连续可微，必有极值。对 $Z$ 的切向量 $(-f_y,f_x)$ 有

$$
(-f_y,f_x)\cdot\nabla\rho=\frac{c}{p^2}\ne0,
\tag{25.21}
$$

又排除了极值。因此没有圆周分量，四个边界点恰配成两条闭弧；其中一条经过 $b_*$。删除 $b_*$ 后，恰得三个弧分量。

在每个分量上 $\mu=m/p$ 连续。由(25.7)中的 $g_0,g_1\ne0$，它从不等于 $2/3$ 或 $1$，故该分量完全处于下面一个带：

$$
\mu<2/3,\qquad 2/3<\mu<1,\qquad \mu>1.
\tag{25.22}
$$

不含 $b_*$ 的整条闭弧的两个边界端点必须处于同一带。(25.9)中只有前两个端点同处中间带，其余两个分别处于下带和上带。因此前两端点由不经过 $b_*$ 的弧连接；另一弧的两个端点为 $x=1$ 上的两个交点，并由 $b_*$ 分成下带、上带两支。特别地，三个弧分量各占一个不同的带。在物理开方形内删去边界端点，不改变这三个分量及其分离。

由(25.21)，$\rho$ 在每条弧上沿任一正则定向参数的导数连续且不为零，因而严格单调。于是同带内的 $\rho$ 值唯一确定来源点，不同带由 $\mu$ 分开。因此

$$
(x,y)\longmapsto(\mu,\rho)
\quad\text{在 }\Gamma_{\theta,\xi}\text{ 上单射}.
\tag{25.23}
$$

$\eta=\rho+20\mu$ 给 $(\mu,\eta)$ 同样单射。复用(8.7)，在同一个固定父上有

$$
r_M^{(6)}=120(1+2\theta)+120\xi\mu,\qquad
r_{MM}^{(7)}=210(2+3\theta)+30\xi\eta .
\tag{25.24}
$$

$\xi\ne0$，所以相同的两项实际响应给相同 $\mu,\eta$，继而给相同正来源。定义25.1的双射再唯一恢复世界漂移和整个至多三次增益，得到(25.17)。对每个实际第六 $M$ 响应，末 $M$ 在其全部兼容世界上已单射；故不论末 $J$ 是否另有碰撞，都不满足 $L_1$。按(1.2)的第六 $M$ 条款立即得(25.18)。这覆盖全部实响应，无需假设坏响应有限，也无需把两个末动作的碰撞对强制相同。

还须核对精确父，而非仅核对参数近似。对(14.4)四个有理中心各取半径 $10^{-24}$ 的原盒 $\mathcal C$，在第一来源 $z_1=(s,t_1)$ 上，按(8.1)、(8.5)作有理区间运算，给

$$
\begin{gathered}
\{\,k(z_1)+\xi q(z_1):(s,t_1,t_2,\xi)\in\mathcal C\,\}
 \subset(0.280163636202,\ 0.280163636204),\\
\{\,\xi:(s,t_1,t_2,\xi)\in\mathcal C\,\}
 \subset(-0.845640162242,\ -0.845640162239).
\end{gathered}
\tag{25.25}
$$

这些包含对整个原盒成立；其分母区间均排除零。(14.2)在该盒中唯一的零点遂定义 $\mathcal U$ 内的精确父。定理14.3的两个世界在这个同一父的 $J$ 子历史中仍共同见证 $L_1$；(25.17)只给另一实际起步动作的完整恢复，不改判既有碰撞。

闭方形包含、边界计数和唯一内部分母零点的分析已经穷尽正来源的所有非紧尾部；边界不作为额外世界。证明未限制增益符号、实际次数、采样零点、重根或漂移符号，也未除以 $\Delta$、$g(6)$、$g(7)$。固定 $MM$ 是单条原轨迹的两个后续动作，每次立即读数；完整世界的恢复指响应像上唯一的逆，不额外声称任意实数输入都有有限位有效算法。

本章承重结论是(25.1)整个参数矩形上的全父固定 $MM$ 恢复，以及其对定理14.2精确 $J$ 失败父的否定判定，属于仓内推导（repo-derived）。(25.2)—(25.6)只代数化既有来源与响应；真正新增的是(25.7)—(25.23)的全域排除、弧分离及消费者。Bernstein 凸组合与二分、Descartes 规则、四节点插值、压缩映射、隐函数定理和紧一维流形分类是成熟供应，不作为本仓新增定理；不申领文献优先权或 Lean 核验。本结论不排除其他父的共同 $L_2$，不决定整条第14章解析父曲线，也不完成祖先兼容、原根八读／九读判别或九读上界；$\xi=0$ 的整个分支仍留在原目标内。$\square$

## 追加锚（本行以下为增补区）

## 26. 零偏离整个父族的源比分离与两读恢复

**定义 26.1（零偏离父与不除漂移的响应比）。** 保持定义1.1的整个 $\mathcal W_3$、完整目标、含早停失败递归及原时钟。对任意 $\theta\in\mathbb R$，令

$$
\begin{gathered}
H^-_\theta=H^-_{\theta,0}
 =(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta)),\\
w_0(\theta)=120(1+2\theta),\qquad
m_0(\theta)=210(2+3\theta).
\end{gathered}
\tag{26.1}
$$

以下 $u=\nu_0$，源坐标 $u,n,a,h,\ell,\Delta,\Phi$ 及 $\Psi_6,\Psi_7$ 沿用(8.1)、(8.6)。四迹逆 $P(u,n,a)$、秩一方程 $D=0$、$A=3u^2+3u-10$、$B_1=8u^2+18u-30$ 及 $F,c_2,c_1,c_0,\mathcal Q,n_\pm,a_\pm$ 沿用 [V，(29.1)、(29.9)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)。特别地，$F=c_2n^2+c_1n+c_0$，而不是随 $\theta$ 改变的父方程。

对正来源的 $\Phi=0$ 层，定义

$$
\begin{aligned}
T(u,n)={}&50nu^4+157nu^3-261nu^2-518nu+600n\\
 &-143u^4-240u^3+349u^2+446u,\\
C(u,n)={}&300nu^4+939nu^3-1636nu^2-2975nu+3500n\\
 &-981u^4-1479u^3+2427u^2+2925u,\\
\mathcal R(P)&=\frac{\Psi_7(P)}{\Psi_6(P)}\quad(\Psi_6(P)\ne0).
\end{aligned}
\tag{26.2}
$$

此处 $T$ 是标量多项式，不是累计矩阵；$C$ 也不表示世界族。由 $a=(23h-B_1n)/A$ 直接有

$$
\Psi_6=-T/A,\qquad \Psi_7=-2C/A,\qquad
\mathcal R=2C/T.
\tag{26.3}
$$

**定理 26.2（全部正来源的响应比单射）。** 在所有严格逐项正、秩一、迹一且满足 $\Phi=0,\Psi_6\ne0$ 的来源上，$P\mapsto\mathcal R(P)$ 单射。准确地，复用 V 定理29.3的两条完整正来源曲线 $\mathcal S_+,\mathcal S_-$ 及端点 $\alpha_0,\beta_0,\gamma_0,\eta_0$。存在唯一正来源满足 $\Phi=\Psi_6=0$，它位于 $\mathcal S_+$，其 $u$ 坐标记为 $\rho$，且

$$
1714/1000<\rho<1715/1000.
\tag{26.4}
$$

令 $\mathcal S_+^{\mathrm{left}}$、$\mathcal S_+^{\mathrm{right}}$ 分别为 $\alpha_0<u<\rho$、$\rho<u<\gamma_0$ 的部分。三个来源区间上 $\mathcal R$ 均随 $u$ 严格递减，且

$$
\begin{array}{c|c}
\text{来源区间}&\text{响应比范围}\\ \hline
\mathcal S_+^{\mathrm{left}}&\mathcal R<1\\
\mathcal S_-&14<\mathcal R<17\\
\mathcal S_+^{\mathrm{right}}&\mathcal R>17.
\end{array}
\tag{26.5}
$$

这里不删去 $\Delta=0$ 的来源。$\rho$ 是 $\Psi_6$ 的零点，与 V (29.12) 的 $\Delta$ 零点 $\sigma$ 不同。

证明。V 定理29.3的 $D=\Phi=0$ 正性分类只依赖来源，故可直接用于本章的全部参数。它给

$$
\begin{gathered}
\mathcal S_+=\{(u,n_+(u),a_+(u)): \alpha_0<u<\gamma_0\},\\
\mathcal S_-=\{(u,n_-(u),a_-(u)): \beta_0<u<\eta_0\},\\
1649/1000<u<2171/1000,\qquad A>0,\quad c_2>0,\quad\mathcal Q>0,\\
F_n(u,n_\pm(u))=\pm A\sqrt{\mathcal Q}\ne0.
\end{gathered}
\tag{26.6}
$$

因此既不把 V 定理29.2的特定 $\theta=33/20$ 父条件移用于别的父，也不把该定理的 $\Delta\ne0$ 限制加到来源分类。由(26.3)，只须分析 $2C/T$。

以偏导数定义多项式

$$
\mathcal H=2\bigl[(C_uT-CT_u)F_n-(C_nT-CT_n)F_u\bigr].
\tag{26.7}
$$

在 $T\ne0$ 的每条来源分支上，隐函数求导给

$$
\frac{d\mathcal R}{du}=\frac{\mathcal H}{T^2F_n}.
\tag{26.8}
$$

以下给出所需的有理符号证书。对 $G\in\{\mathcal H,T\}$，令 $E_G$ 为 $\operatorname{Res}_n(F,G)$ 的首一无平方因子部分，不剔除 $A$ 或 $c_2$ 因子。令 $V_G(x)$ 为从 $E_G,E_G'$ 开始、后项取前两项除法的负余式所得 Sturm 序列在 $x$ 处去零后的变号数。由(26.2)、(26.7)及 V (29.9)的显示多项式，有

$$
\begin{array}{c|r|c|c}
G&\deg E_G&(l,r)&(V_G(l),V_G(r))\\ \hline
\mathcal H&28&(1649/1000,2171/1000)&(10,10)\\
T&12&(1649/1000,2171/1000)&(3,2)\\
T&12&(1714/1000,1715/1000)&(3,2).
\end{array}
\tag{26.9}
$$

所有显示端点均非根。这些计数使用有理多项式除法；共同实零点必使消元式为零，所以第一行排除全部正来源上的 $\mathcal H=0$，后两行把所有可能的 $T=0$ 限于同一个 $u$。

为核对分支、导数符号及端点像，采用有理区间的加减乘除与 Horner 求值。对区间中的正 $\mathcal Q$，取分母 $10^{40}$ 的平方根上下界，由整数平方比较向外包围，再代入 V (29.9) 的 $n_\pm$。这给下列严格包围，所有除数区间均排除零：

$$
\begin{array}{c|c|c|c}
\text{来源}&u&\mathcal R&d\mathcal R/du\\ \hline
\mathcal S_+&17/10&(-48,-47)&(-4269,-4268)\\
\mathcal S_+&19/10&(18,19)&(-24,-23)\\
\mathcal S_-&2&(15,16)&(-7,-6).
\end{array}
\tag{26.10}
$$

另在 $n_+$ 分支上有 $-2<\Psi_6(17/10)<-1$ 及 $11<\Psi_6(9/5)<12$。两点都在 $\mathcal S_+$，故连续性供应其间的一个实际 $\Psi_6$ 零点。(26.9)随后给唯一的 $u=\rho$ 及(26.4)。因 $\alpha_0<\rho<\beta_0$，该处只有 $n_+$ 是正来源；由(26.6)与 V (29.15)，另一分支不是合法来源。故这确为唯一正来源零点。此时 $\mathcal H\ne0$；若同时 $C=T=0$，(26.7)反而给 $\mathcal H=0$，所以 $\mathcal R$ 在该点确有极点。

(26.6)、(26.9)说明 $\mathcal H/F_n$ 在每条完整来源分支上连续且不为零。(26.10)给它的负号。由(26.8)，删除 $\rho$ 后的三个区间上导数均严格负，因而严格递减；没有在 $\sigma$ 处分割或删点。

四个源边界的根隔离与响应比包围如下。表中有限小数全为精确有理数，$n_\pm$ 与 $\mathcal R$ 在所列端点按连续延拓取值。

$$
\begin{array}{c|c|c|c}
\text{边界根}&\text{根的有理隔离区间}&\text{分支}&\mathcal R\text{ 的严格包围}\\ \hline
\alpha_0&(1.649663989864,1.649663989865)&n_+&(0,1)\\
\beta_0&(1.896231213642,1.896231213643)&n_-&(16,17)\\
\gamma_0&(1.953790826240,1.953790826241)&n_+&(17,18)\\
\eta_0&(2.170055243572,2.170055243573)&n_-&(14,15).
\end{array}
\tag{26.11}
$$

根的方程直接复用 V (29.10)，各显示小区间上的 Sturm 根数为一；它们位于各自已有的唯一根隔离区间内。用上述同一有理根式规则在整段小区间求值即可得最后一列，且 $T$ 的区间不含零。因此四个端点的单侧极限确为该列所包围的有限值，而不是浮点采样推断。严格递减遂给：左 $\mathcal S_+$ 的值小于其 $\alpha_0$ 极限，右 $\mathcal S_+$ 的值大于其 $\gamma_0$ 极限，$\mathcal S_-$ 的值夹在其 $\eta_0$ 与 $\beta_0$ 极限之间。这正是(26.5)。每段内部的严格单调与三段互不相交的像共同证明来源单射；四迹逆将唯一的 $(u,n,a)$ 还原为唯一矩阵 $P$。∎

**定理 26.3（每个非基线实际 M 子纤维的完整恢复）。** 对任意 $\theta\in\mathbb R$ 及任意实际响应 $w\ne w_0(\theta)$，在整个

$$
K_{\theta,w}=\mathcal F(H^-_\theta,M,w)
\tag{26.12}
$$

上，原时钟七的末 $M$ 响应 $m$ 对完整世界 $(P,g,d)$ 单射。

证明。定理8.2证明中的无除数恒等式在 $\xi=0$ 仍然成立，故任意父世界满足

$$
\begin{gathered}
d\Delta=24h(\theta n-a),\qquad d\Phi=0,\\
w-w_0(\theta)=d\Psi_6/h,\qquad
m-m_0(\theta)=d\Psi_7/(4h).
\end{gathered}
\tag{26.13}
$$

$h>0$，而实际 $w\ne w_0(\theta)$，所以 $d\ne0$、$\Psi_6\ne0$，继而 $\Phi=0$。因此

$$
\mathcal R(P)=\frac{4(m-m_0(\theta))}{w-w_0(\theta)}.
\tag{26.14}
$$

同一个 $\theta,w,m$ 给相同的右端，定理26.2遂给唯一来源。然后

$$
d=\frac{h(w-w_0(\theta))}{\Psi_6},\qquad
(g(0),g(1),g(2),g(3))
 =(-d,-d/u,-d/(u+1),(6-d)/n)
\tag{26.15}
$$

给唯一漂移及同一个完整至多三次多项式。四个节点不同，故有限插值唯一；时钟零与三的读数不同，又排除零多项式。全过程只除 $h,n,u,u+1$ 及已由非基线响应排除的 $\Psi_6,w-w_0$，不除 $\Delta$、$g(6)$ 或 $g(7)$。于是同读世界确为同一完整目标，证明(26.12)上的单射。∎

**定理 26.4（所有实参数的整个零偏离父族两读恢复）。** 对每个 $\theta\in\mathbb R$，存在只用原时钟六、七至多两个进一步实际读数的确定性策略，恢复整个 $\mathcal F(H^-_\theta)$。特别地，

$$
\forall\theta\in\mathbb R\quad
\forall K\subseteq\mathcal F(H^-_\theta),\qquad
\neg L_2(K,H^-_\theta).
\tag{26.16}
$$

证明。复用 V (28.15)的精确代数阈值 $a_\circ,b_\circ$ 与 V (27.5)—(27.6)的 $k_*$，令

$$
\mathcal B=\bigl((a_\circ,b_\circ)\setminus\{k_*\}\bigr)
 \cup(13/8,5/3).
\tag{26.17}
$$

V 定理28.2—28.4已经穷尽基线实际子纤维

$$
\mathcal F(H^-_\theta,M,w_0(\theta))=\mathcal F(H_\theta).
\tag{26.18}
$$

其中末 $J$ 的全部碰撞恰由 $\theta\in\mathcal B$ 给出：零漂移内部折返发生在 $(13/8,5/3)$，固定源与零漂移分支的不同目标接合响应发生在 $(a_\circ,b_\circ)\setminus\{k_*\}$；除此之外末 $J$ 单射。$\theta=k_*$ 处是同一个完整世界的分支接合，四个开区间阈值处也没有额外碰撞。若 $\theta\le1/2$ 或 $\theta\ge3$，该基线纤维为单点，仍在上述单射结论内。

由 V (28.16)，$\mathcal B$ 的低参数部分包含在 $[7/10,27/25]$，高参数部分包含在 $[13/8,5/3]$。因此策略可准确写为

$$
\begin{array}{c|c|c}
\text{已知父参数}&\text{原时钟六动作}&\text{原时钟七动作}\\ \hline
\theta\in\mathcal B&J&J\\
\theta\notin\mathcal B&M&
 \begin{cases}J,&\text{实际 }w=w_0(\theta),\\ M,&\text{实际 }w\ne w_0(\theta).\end{cases}
\end{array}
\tag{26.19}
$$

第一行直接由 V 定理30.4及31.4的完整父纤维固定 $JJ$ 单射供应。第二行的基线情况由(26.18)及上述完整末 $J$ 分类供应；非基线情况由定理26.3供应。因而每个实际响应路径的终纤维都至多一个完整世界。反过来，每个合法父世界都实际生成其中一条路径，故在响应像上取唯一逆就给确定性完整解码器；空响应纤维无需被实现，单点纤维允许早停。

这个策略的第六动作只依赖已取得的父历史参数，第七动作只依赖该父及实际第六读数。两次接续都是原子操作后立即读数，连同既有初读共至多八读；没有复制、重置、删去早期动作、重编号时钟或同时取得互择预测。若对某个子集成立 $L_2$，其第一动作条款必为(26.19)所选的动作供应一个仍满足 $L_1$ 的实际子纤维；而该子纤维已由所选末动作单射，矛盾。这同时证明所有子集的(26.16)，无需限制各末动作使用同一个碰撞对。

V 定理29.3穷尽了 $\Phi=0$ 的全部正来源，定理26.3在完整世界上又不限制漂移大小。因此(26.16)包括全部实际响应、非紧漂移尾部、所有增益符号、低次数、采样零点、重根及 $\Delta=0$ 层。恢复是原精确实响应合同中的像上逆，不附加连续性、可计算性、有限精度或稳定性结论。

本章的来源响应比单射及其非基线、全父消费者是仓内推导（repo-derived）。多项式消元与 Sturm 实根计数使用成熟方法，参见 Basu、Pollack、Roy，[*Algorithms in Real Algebraic Geometry*](https://doi.org/10.1007/3-540-33099-2)；四节点插值、隐函数求导及单变量严格单调性亦为成熟供应。一般纤维可识别性可参见 Li、Lee、Bresler，[*A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*](https://arxiv.org/html/1501.06120v1)，定义2.7、定理2.8；其双线性变换群前提不直接提供本章的加性漂移、原时钟及实际路径结论。本章不申领这些方法或外部文献优先权。

(26.16)只处理字面父族 $H^-_{\theta,0}$。非零 $\xi$ 的共同父两臂失败或恢复、其他字面历史、整条第14章解析父曲线以及更早祖先的共同实现仍须各自证明。第25章的矩形排除与此前的合法碰撞保持各自原范围；本章不把任何单臂禁例或两世界整树刚性扩大成一般两臂排除。原根八读／九读判别、初始两动作的全部分支义务及九读上界均不由(26.16)结清。∎

## 追加锚（本行以下为增补区）

## 27. 实际 MM 的漂移符号校准与重复源签名的全局界

**定义 27.1（重复 MM 源签名域）。** 保留定义1.1的整个 $\mathcal W_3$、原时钟、立即读数及含早停的任意确定性策略。父历史仍为(8.3)的同一个 $H^-_{\theta,\xi}$。以 $\mathscr S$ 表示全部严格逐项正、秩一、迹一的实二阶来源；$u=\nu_0$、$h,\ell,n,a,\Delta,\Phi,k,q,\Psi_6,\Psi_7,\mu,\eta$ 复用(8.1)、(8.5)—(8.6)。定义

$$
\begin{aligned}
\mathscr C=\{P\in\mathscr S:\ &\Phi(P)\ne0,\quad
 \exists Q\in\mathscr S\setminus\{P\},\ \Phi(Q)\ne0,\\
 &\mu(Q)=\mu(P),\quad\eta(Q)=\eta(P)\}.
\end{aligned}
\tag{27.1}
$$

这里只要求源签名重复；没有要求这两个来源能在预定父参数上共同实现。实际同父碰撞的额外条件由定理23.2供应。置

$$
\begin{gathered}
w_0(\theta)=120(1+2\theta),\qquad
m_0(\theta)=210(2+3\theta),\\
\mathfrak T(P)=2\Psi_7(P)-26\Psi_6(P)-5\Phi(P),\\
\Lambda_{\theta,\xi}(w,m)=4m-13w-120+600\theta-300\xi.
\end{gathered}
\tag{27.2}
$$

**定理 27.2（整个父族的仿射漂移符号校准）。** 对任意 $\theta,\xi\in\mathbb R$、任意 $W=(P,g,d)\in\mathcal F(H^-_{\theta,\xi})$，从该父实际依次执行原时钟六、七的 $M,M$，记立即读数为 $w,m$。则

$$
\begin{gathered}
\Lambda_{\theta,\xi}(w,m)=0\quad\Longleftrightarrow\quad d=0,\\
d\ne0\quad\Longrightarrow\quad
\operatorname{sgn}\Lambda_{\theta,\xi}(w,m)=\operatorname{sgn}d,
\qquad 0<|d|<\frac{|\Lambda_{\theta,\xi}(w,m)|}{2}.
\end{gathered}
\tag{27.3}
$$

特别地，当 $\xi\ne0$ 时，同一父上任何两个不同完整世界若具有相同的实际 $MM$ 记录，必有 $d_1d_2>0$ 及 $\Phi_1\Phi_2>0$。对固定实际第六 $M$ 子纤维，末 $M$ 响应因此把正漂移、零漂移和负漂移三部分彼此分开；各部分内部仍可碰撞。

证明。定理8.2证明中的无除数恒等式对全部 $\xi$ 成立：

$$
d\Phi=120h\xi,\qquad
w-w_0(\theta)=\frac{d\Psi_6}{h},\qquad
m-m_0(\theta)=\frac{d\Psi_7}{4h}.
\tag{27.4}
$$

因 $4m_0-13w_0-120+600\theta=0$，它们给出

$$
2h\Lambda_{\theta,\xi}(w,m)=d\mathfrak T(P).
\tag{27.5}
$$

真正所需的全源严格不等式是 $\mathfrak T(P)>4h$。使用(8.1)的唯一正坐标 $P=P(s,t)$，令 $D_0=1+st$、$U=s+t+st$，于是 $h=U(U+D_0)/D_0^2$。直接展开(8.1)、(8.6)得

$$
D_0^3(\mathfrak T-4h)=\mathscr B(s,t),
\tag{27.6}
$$

其中

$$
\begin{aligned}
\mathscr B(s,t)={}&152s^3t^3+60s^3t^2+61s^3t+35s^3\\
 &+114s^2t^3+363s^2t^2+125s^2t+s^2\\
 &+14st^3+255st^2+139st\\
 &+10t^3+4t^2+76t+8.
\end{aligned}
\tag{27.7}
$$

全部系数严格正，故对每个 $s,t>0$ 有 $\mathscr B>0$。于是 $h>0$ 且 $\mathfrak T/(2h)>2$；(27.5)即给(27.3)。这个恒等式没有除以 $\xi$ 或 $\Phi$，所以包括 $\xi=0,\Phi=0,d=0$。在 $\Phi\ne0$ 的源域上，同一不等式也给

$$
\operatorname{sgn}(2\eta-26\mu-5)=\operatorname{sgn}\Phi.
\tag{27.8}
$$

若 $\xi\ne0$ 且两个世界的实际 $w,m$ 相同，(27.3)及(27.4)先给两个非零漂移同号，再由 $d_i\Phi_i=120h_i\xi$ 给两个 $\Phi_i$ 同号。固定子纤维的三部分分离同样由(27.3)给出，无须假设另一末动作使用同一个碰撞对。此证明只读取所声明的原时钟路径；增益的低次数、符号、根和 $\Delta=0$ 层均未被删去。常数 $2$ 只作严格有效界，不主张最优。∎

**定理 27.3（重复签名的全局有界性及实际必需边的线性塌缩）。** 存在与父参数和世界均无关的有限常数 $B>0$，使每个 $P\in\mathscr C$ 满足

$$
\max\left\{\frac{h(P)}{|\Phi(P)|},\ |q(P)|,
                   |\mu(P)|,\ |\eta(P)|\right\}\le B.
\tag{27.9}
$$

因此对任意 $\theta\in\mathbb R$、$\xi\ne0$，若两个不同完整世界 $W_i=(P_i,g_i,d_i)\in\mathcal F(H^-_{\theta,\xi})$ 有相同的实际第六 $M$ 读数 $w$ 及实际第七 $MM$ 读数 $m$，则同一个 $B$ 给

$$
\begin{gathered}
|d_i|\le120B|\xi|,\qquad |\theta-k(P_i)|\le B|\xi|
\quad(i=1,2),\\
|w-w_0(\theta)|\le120B|\xi|,\qquad
|m-m_0(\theta)|\le30B|\xi|,\\
\operatorname{dist}(\theta,[1/2,3])\le B|\xi|.
\end{gathered}
\tag{27.10}
$$

对任意 $\theta\in\mathbb R$、$\xi\ne0$ 及 $K\subseteq\mathcal F(H^-_{\theta,\xi})$，若 $L_2(K,H^-_{\theta,\xi})$ 成立，则其实际第六 $M$ 子纤维中末 $M$ 条款所必需的任一碰撞对均满足(27.3)、(27.10)。因而在任意 $\xi_j\to0$、$\xi_j\ne0$ 的此类父序列上，该必需对的两个漂移都趋于零，其共同 $w_j,m_j$ 与各自父的基线之差均为 $O(|\xi_j|)$。这里没有先验的来源紧性、漂移有界性或 $\theta_j$ 有界性假设。

证明。先控制全部非紧来源尾部。写

$$
P=\begin{pmatrix}p&b\\c&1-p\end{pmatrix},\qquad
0<p<1,\quad b,c>0,\quad bc=p(1-p).
$$

四迹逆[V，(29.1)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)给

$$
u=b+c+1-p,\qquad n=1+b+2c,\qquad a=1+2u-c.
\tag{27.11}
$$

因此 $n\ge u$、$a\ge u+1$、$n,a\le2u+1$。当 $u\ge3$ 时，$A=3u^2+3u-10$ 及 $B_1=8u^2+18u-30$ 均正，从而

$$
\begin{aligned}
\Phi&=Aa+B_1n-23u(u+1)\\
&\ge A(u+1)+B_1u-23u(u+1)\\
&=11u^3+u^2-60u-10\ge4u^3.
\end{aligned}
\tag{27.12}
$$

最后一步置 $u=3+v$，差为 $7v^3+64v^2+135v+8>0$。同一范围内有

$$
\begin{gathered}
h\le\frac43u^2,\quad 0<\ell\le2u^2,\quad
0<V_6\le17u^2,\quad0<X_7\le32u^2,\quad n,a\le\frac73u.
\end{gathered}
\tag{27.13}
$$

由(8.6)和三角不等式，$|\Psi_6|$ 至多为
$119u^3+(140/3)u^3+(116/3)u^2$，$|\Psi_7|$ 至多为
$(4480/3)u^3+490u^3+508u^2$。又
$\Delta/n=h+a\ell-4ah/n$，所以

$$
\begin{gathered}
\frac h{|\Phi|}\le\frac19,\qquad
|\mu|\le\frac{1607}{36}<45,\qquad
|\eta|\le\frac{3229}{6}<539,\\
|q|\le\frac5{4u^3}
 \left(\frac43u^2+\frac{14}3u^3+\frac{112}9u^2\right)
 \le\frac{625}{54}<12.
\end{gathered}
\tag{27.14}
$$

这些是整个 $u\ge3$ 尾部的界，不要求源签名重复。

余下来源置于紧集

$$
\mathscr K=\left\{\begin{pmatrix}p&b\\c&1-p\end{pmatrix}:
0\le p\le1,\ b,c\ge0,\ bc=p(1-p),\ b+c+1-p\le3\right\}.
\tag{27.15}
$$

这里 $b+c\le3$，故此集闭且有界；它的非负边界只用于极限分析。需证明重复签名点不能逼近 $\mathscr K$ 中的 $\Phi=0$ 层。

先精确识别这个闭极层。V 定理29.3证明中 $u\le3/2$ 时 $\Phi<0$ 的估计对非负来源仍成立：将 $n,a<1+2u$ 换成弱不等式，其所用两个三次上界在相应区间仍严格负；$u=0$ 时直接有 $n=a=1,\Phi=-40$。故此极层的 $u>3/2$。复用 V (29.9)、(29.14)—(29.15)，非负来源恰为两条正来源弧的闭包

$$
\begin{aligned}
\overline{\mathcal S_+}&=\{(u,n_+(u),a_+(u)):
                              \alpha_0\le u\le\gamma_0\},\\
\overline{\mathcal S_-}&=\{(u,n_-(u),a_-(u)):
                              \beta_0\le u\le\eta_0\}.
\end{aligned}
\tag{27.16}
$$

确实，V (29.14)穷尽 $p=0,1,b=0,c=0$ 的边界交点；(29.15)在其余开区间给严格违反非负性的坐标，端点取连续极限即得(27.16)，没有孤立的额外非负支。四端点均在 $1649/1000<u<2171/1000$ 内。

由(26.6)、(26.9)，两条闭弧上 $A>0$、$F_n\ne0$、$\mathcal H\ne0$。复用(26.3)，$\Psi_6,\Psi_7$ 不可能同时为零，否则 $T=C=0$ 将使(26.7)的 $\mathcal H=0$。定理26.2的严格单调性与(26.11)的端点严格包围说明：$[\Psi_6:\Psi_7]$ 在这两条闭弧的并上单射。具体地，$\mathcal S_+$ 的极点左侧连同端点有 $\mathcal R<1$，右侧连同端点有 $\mathcal R>17$；闭 $\mathcal S_-$ 上有 $14<\mathcal R<17$。唯一 $\Psi_6=0$ 点仍是(26.4)的内点，那里 $\Psi_7\ne0$，代表唯一的射影无穷点。故端点与极点均未被删除。

还需排除两个重复签名点在极层上合流；仅有极层内部单射不足以保证这一点。在(27.16)每一点附近，令 $v=\Phi$，以

$$
a=\frac{v+23h-B_1n}{A},\qquad
\widetilde F(u,n,v)=A^2D\!\left(u,n,\frac{v+23h-B_1n}{A}\right)
\tag{27.17}
$$

代入 V (29.1)的源方程 $D=0$。V (29.13)给
$\widetilde F(u,n,0)=F(u,n)$，故
$\partial_n\widetilde F(u,n,0)=F_n\ne0$。隐函数定理于是把 $(u,v)$ 作为源曲面的局部坐标。此结论在非负端点也成立：先在包含端点的完整实曲面邻域使用定理，再限制回非负来源，不把端点当作额外合法世界。

沿 $v=0$ 对 $u$ 求导，定义 Wronskian

$$
\mathcal W=\Psi_6\frac{d\Psi_7}{du}
             -\Psi_7\frac{d\Psi_6}{du}
          =\frac{\mathcal H}{A^2F_n}\ne0.
\tag{27.18}
$$

等式由(26.3)、(26.7)及 $dn/du=-F_u/F_n$ 得到，因而也包括四个端点和唯一极点。若 $\Psi_6\ne0$，用局部映射

$$
(u,v)\longmapsto
 \left(\frac v{\Psi_6},\frac{\Psi_7}{\Psi_6}\right);
\qquad
\det D_{(u,v)}\bigg|_{v=0}=-\frac{\mathcal W}{\Psi_6^3}\ne0.
\tag{27.19}
$$

在 $\Psi_6=0$ 的唯一点改用

$$
(u,v)\longmapsto
 \left(\frac v{\Psi_7},\frac{\Psi_6}{\Psi_7}\right);
\qquad
\det D_{(u,v)}\bigg|_{v=0}=\frac{\mathcal W}{\Psi_7^3}\ne0.
\tag{27.20}
$$

逆函数定理给这两种映射各自在相应点的某个邻域内单射。只在分母非零的邻域使用相应映射，故没有把极点误作可除点。

反设有 $P_j\in\mathscr C\cap\mathscr K$ 且 $\Phi(P_j)\to0$。为每个 $P_j$ 选择定义(27.1)中的 $Q_j\ne P_j$。取子列使 $P_j\to P_*\in\mathscr K$。由(27.16)及极层上 $\Psi_6,\Psi_7$ 不同时为零，

$$
\| (\mu(P_j),\eta(P_j))\|_\infty\longrightarrow\infty.
\tag{27.21}
$$

$Q_j$ 的签名相同，(27.14)遂迫使最终 $u(Q_j)<3$。再取子列使 $Q_j\to Q_*\in\mathscr K$。由于 $n\ge1$，若 $\Phi(Q_*)\ne0$，两个签名在该处连续而有界，与(27.21)矛盾。因此 $\Phi(Q_*)=0$。对充分大的 $j$，签名相等给
$[\Psi_6(P_j):\Psi_7(P_j)]=[\Psi_6(Q_j):\Psi_7(Q_j)]$；在两个极限点这些射影对都有定义，取极限并使用闭极层的射影单射，得 $P_*=Q_*$。

选择该共同极限点处分母非零的(27.19)或(27.20)邻域。充分大的 $j$ 使两点同在这个单射邻域内。若用(27.19)，其值为 $(1/\mu,\eta/\mu)$；若用(27.20)，其值为 $(1/\eta,\mu/\eta)$。在相应邻域内这些分母确实非零，故相同签名给相同局部映射值，强制 $P_j=Q_j$，矛盾。

因此存在 $\varepsilon>0$，使 $\mathscr C\cap\mathscr K$ 上 $|\Phi|\ge\varepsilon$。在紧集 $\mathscr K\cap\{|\Phi|\ge\varepsilon\}$ 上，$h/|\Phi|,q,\mu,\eta$ 连续：这里 $n\ge1$，没有额外分母零点。它们有共同有限上界。把此上界与(27.14)合并，取 $B\ge539$ 即得(27.9)。不要求 $\mathscr C$ 本身闭或紧，也没有把极层外单射误当成全域单射。

最后回到实际世界。定理23.2保证任一实际同父 $MM$ 碰撞对具有不同来源，且两来源都在 $\mathscr C$。于是(8.5)、(8.7)给

$$
d_i=\frac{120h_i\xi}{\Phi_i},\qquad
\theta-k_i=\xi q_i,\qquad
w-w_0=120\xi\mu_i,\qquad m-m_0=30\xi\eta_i.
\tag{27.22}
$$

再由正坐标(8.1)，

$$
2a-n=\frac{1+3t+5st}{1+st}>0,\qquad
3n-a=\frac{2+5s+t}{1+st}>0,
\tag{27.23}
$$

所以 $1/2<k_i<3$。(27.9)、(27.22)—(27.23)证明(27.10)。

若 $L_2(K,H^-_{\theta,\xi})$ 成立，直接使用定理23.2的必要边：在同一个实际第六 $M$ 子纤维中取末 $M$ 条款的两个不同世界，应用上述界即可。其共同第六读数 $w$ 因而也受界。这没有把该界赋给子纤维中的每个世界；定理24.6的末 $J$ 碰撞对可以不同，第六 $J$ 臂的两种末碰撞对也可各自不同。所有对仍必须分别满足各自共同实际历史和响应纤维条件。令 $\xi_j\to0$ 即得所述必需对的漂移与移动基线残差的线性塌缩；来源本身仍可逼近边界或逃向无穷。

本条与定理27.2的承重内容是此指定观察映射的全源正性证书、极层附近的重复签名排除及全局实际响应界，属于仓内推导（repo-derived）。隐函数定理、逆函数定理、紧性和 Sturm 计数只作成熟中间供应；源分支、端点和射影供应分别按 V 定理29.3及本卷定理26.2的原条件使用。一般可识别性语言可参见 Li、Lee、Bresler，[*A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*](https://arxiv.org/html/1501.06120v1)，定义2.7、定理2.8；其双线性变换群条件不提供这里的加性漂移、原时钟或极层估计，不作为本证明的前提。不申领外部优先权。

以上只给部分校准及必要边约束。常数 $B$ 是存在性的统一有限界，没有数值最优性或有限精度稳定性结论；(27.10)不扩展到任意父世界。相同漂移符号的共同父两臂实现、$\mathcal P_M\cap\mathcal P_J$ 的空性或非空性、整条第14章父曲线、更早祖先兼容及原根八读／九读问题仍未由本条解决；也未给九读上界。$\xi=0$ 的父排除保持定理26.4的范围，仿射校准(27.3)则仍在该层成立。全部推导保留增益次数下降、任意符号与采样根、重根、任意漂移以及 $\Delta=0$，未除以任何采样增益。∎

## 追加锚（本行以下为增补区）

## 28. 临界第四 M 的完整世界与指定支持

**定义 28.1（完整世界与失败递归）。** Use the entire $\mathcal W_3$ of Definition 1.1, writing $d$ for the drift coordinate $\delta$. Thus a world is a triple $W=(P,g,d)$, where $P$ is a strictly entrywise positive real $2\times2$ matrix of rank one and trace one, $g\in\mathbb R[t]\setminus\{0\}$ has degree at most three, and $d\in\mathbb R$. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

For a chronological word $E_1\cdots E_k$, set $A_0=I$ and $A_i=E_iA_{i-1}$. The response at original clock $i$ is $g(i)\operatorname{tr}(A_iP)+d$. The set $\mathcal F(H)$ consists of every world realizing the entire literal history $H$. For $K\subseteq\mathcal F(H)$, write $K_{E,z}=K\cap\mathcal F(H,E,z)$ and define

$$
\begin{aligned}
L_0(K,H)&\iff |K|\ge2,\\
L_{s+1}(K,H)&\iff |K|\ge2\ \land\
 \forall E\in\{M,J\}\ \exists z\in\mathbb R:
 L_s(K_{E,z},(H,E,z)).
\end{aligned}                                                     \tag{28.1}
$$

Each world retains its same source, entire gain and drift at every shared prefix. There is one unresettable, uncopyable trajectory, each atomic action is immediately read, and the initial reading at clock zero counts. The remaining clocks at $H_4$ are exactly $5,6,7$. Actions, stopping and returned worlds may depend arbitrarily and deterministically on the entire actual history. The cardinality guard includes stopping. These are exactly the whole-world and actual-history conventions of Definition 1.1, including all gain signs, lower actual degrees, sampled roots and repeated roots.

**定义 28.2（临界第四 M 历史）。** Put

$$
\begin{gathered}
h(t)=(t-1)(t-3)(t-7),\qquad
P_r=\begin{pmatrix}1-r&12r(1-r)\\1/12&r\end{pmatrix},\qquad U_r=(P_r,h,0),\\
H_3=(-21,M,0,J,65/12,M,0),\qquad
H_4=(H_3,M,-93/2),\\
z_{1/2}=-76,\qquad z_{2/3}=-220/3,\qquad
H_5^r=(H_4,J,z_r)\quad(r\in\{1/2,2/3\}).
\end{gathered}                                                     \tag{28.2}
$$

Both $U_{1/2}$ and $U_{2/3}$ realize $H_4$. Their fifth-$J$ responses are the distinct values $z_r$. The cumulative matrices at clocks four and five are

$$
A_4=\begin{pmatrix}1&2\\1&3\end{pmatrix},\qquad
Q=JA_4=\begin{pmatrix}1&3\\1&2\end{pmatrix}.
\tag{28.3}
$$

The corresponding sixth responses are $-275/2$ after $M$ and $-155/2$ after $J$, for either $r$; every seventh response is zero. The common fourth history and the fifth responses are [V, Theorem 6.1 and Proposition 6.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md). The sixth values follow from the trace table in Definition 29.1 below and $h(6)=-15$.

## 29. 临界第四 M 八读点纤维的有限整数证书

**定义 29.1（八种数据与正来源图）。** The symbols in Sections 28–31 refer to the histories of Definition 28.2. For each $z\in\{-76,-220/3\}$ and $w=EF\in\{MM,MJ,JM,JJ\}$, use independent variables $x,y$ and put

$$
R(x,y)=\begin{pmatrix}(3-2x)y&3-2x\\(x-1)y&x-1\end{pmatrix}.
\tag{29.1}
$$

Every legal source has a unique such representative: if $\eta=(QP)_{22}>0$, then $R=P/\eta$ and

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
1<x<3/2,\quad y>0.
\tag{29.2}
$$

Conversely (29.2) makes $R$ strictly positive of rank one and $P=R/\operatorname{tr}R$ legal. This is the source chart (4.4) of Definition 4.1, for the same cumulative matrix $Q$. Its trace polynomials at clocks zero through five are

$$
\begin{aligned}
T_0&=-2xy+x+3y-1,& T_1&=xy-x-y+2,\\
T_2&=-xy+x+2y-1,& T_3&=xy-y+1,\\
T_4&=x+y,&T_5&=xy+1.
\end{aligned}                                                     \tag{29.3}
$$

For the chronological sixth and seventh actions $EF$, complete the table by

| $w=EF$ | $T_6=\operatorname{tr}(EQR)$ | $T_7=\operatorname{tr}(FEQR)$ |
| --- | --- | --- |
| $MM$ | $x+y+1$ | $xy+x+y+2$ |
| $MJ$ | $x+y+1$ | $xy+y+1$ |
| $JM$ | $x+y$ | $xy+x+1$ |
| $JJ$ | $x+y$ | $xy+1$ |

Define the data vector

$$
v=(-21,0,65/12,0,-93/2,z,v_6,0),\qquad
v_6=\begin{cases}-275/2&E=M,\\-155/2&E=J.\end{cases}
\tag{29.4}
$$

The source coordinates of the prescribed world are

$$
u_z=(x_z,y_z)=
\begin{cases}(9/8,1/6)&z=-76,\\(7/6,1/8)&z=-220/3.\end{cases}
\tag{29.5}
$$

At either point, $\operatorname{tr}R=1/4$, $P=4R=P_r$, and the normalized gain $G=\eta g$ is $4h$.

**定义 29.2（消去漂移的六个多项式）。** Let

$$
\ell_j(t)=\prod_{\substack{0\le k\le3\\k\ne j}}\frac{t-k}{j-k}
\quad(0\le j\le3),\qquad D=T_0T_1T_2T_3.
$$

For $n=4,5,6,7$, define

$$
\bigl(\ell_0(n),\ell_1(n),\ell_2(n),\ell_3(n)\bigr)=
\begin{cases}
(-1,4,-6,4)&n=4,\\
(-4,15,-20,10)&n=5,\\
(-10,36,-45,20)&n=6,\\
(-20,70,-84,35)&n=7,
\end{cases}
$$

and

$$
\begin{aligned}
a_n&=D\left(1-T_n\sum_{j=0}^3\frac{\ell_j(n)}{T_j}\right),\\
b_n&=D\left(T_n\sum_{j=0}^3\frac{v_j\ell_j(n)}{T_j}-v_n\right),\\
f_{nm}&=\frac{12(a_nb_m-a_mb_n)}{D}\quad(4\le n<m\le7).
\end{aligned}                                                     \tag{29.6}
$$

All six $f_{nm}$ lie in $\mathbb Z[x,y]$ and have degree at most four in each variable. Order them as

$$
(f_{45},f_{46},f_{47},f_{56},f_{57},f_{67})=(f_0,\ldots,f_5).
\tag{29.7}
$$

Let $V$ be the $49$-dimensional real space spanned by $x^uy^v$, $0\le u,v\le6$. Define the integer matrix $C=C_{z,w}$ by

$$
C_{9k+3a+b,\,7u+v}=[x^uy^v](x^ay^bf_k),
\quad 0\le k\le5,\quad 0\le a,b\le2,\quad 0\le u,v\le6.
\tag{29.8}
$$

Thus $C$ has $54$ rows and $49$ columns, with all indices starting at zero. Its row space is identified with a polynomial subspace of $V$.

**定理 29.3（精确行空间证书）。** For $p\in V$, write $p_j(x)=[y^j]p(x,y)$ and define

$$
\Lambda_0(p)=p_6(1),\qquad
\Lambda_1(p)=p_5(1)-p_6'(1).
\tag{29.9}
$$

Set $\psi_\pm=(-1\pm\sqrt5)/2$ and

$$
S_{z,w}=\begin{cases}
\{u_z\},&w\ne JM,\\
\{u_z,(-\psi_+,\psi_+),(-\psi_-,\psi_-)\},&w=JM.
\end{cases}
$$

Then, for every one of the eight choices $(z,w)$,

$$
\operatorname{row}(C_{z,w})=
\ker\Lambda_0\cap\ker\Lambda_1\cap
\bigcap_{q\in S_{z,w}}\{p\in V:p(q)=0\}.
\tag{29.10}
$$

Proof. The expressions in (29.6) are polynomials: the factors $D/T_j$ are polynomial, and in the alternating expression for $a_nb_m-a_mb_n$ the terms with two equal denominator factors cancel. Every other product denominator divides $D$, leaving $D$ as a factor of that alternating expression. Expanding gives integral coefficients after the factor $12$, and bidegree at most $(4,4)$.

The following polynomial identities, together with the determinant table below, give a finite certificate for (29.10). For each of its six $f=f_k$, put $f_j(x)=[y^j]f$. Substitution in (29.6) gives

$$
\begin{gathered}
f(u_z)=0,\qquad f_4(1)=0,\qquad f_3(1)-f_4'(1)=0,\\
\text{if }w=JM:\quad f(-y,y)\equiv0\pmod{y^2+y-1}.
\end{gathered}                                                     \tag{29.11}
$$

These identities also show that all $x^ay^bf$, $0\le a,b\le2$, belong to the right side of (29.10). For the two functionals in (29.9), the only nontrivial case is $b=2$, when the last two identities at $x=1$ in the first line of (29.11) apply. For $b=1$ only $f_4(1)=0$ is needed, and for $b=0$ both functionals vanish by degree.

Here are square integer minors of (29.8). Use ascending row and column order and put

$$
\begin{aligned}
I_{46}&=\{0,\ldots,34\}\cup\{36,\ldots,43\}\cup\{45,46,47\},\\
I_{44}&=\{0,\ldots,34\}\cup\{36,\ldots,43\}\cup\{45\},\\
J_r&=\{0,\ldots,r-1\},\qquad N_{z,w}=C_{z,w}[I_r,J_r].
\end{aligned}                                                     \tag{29.12}
$$

The determinants, reduced modulo $1000003$, are

| $z$ | $w$ | $r$ | $\det N_{z,w}\pmod{1000003}$ |
| --- | --- | --- | --- |
| $-76$ | $MM$ | $46$ | $6010$ |
| $-76$ | $MJ$ | $46$ | $600600$ |
| $-76$ | $JM$ | $44$ | $176698$ |
| $-76$ | $JJ$ | $46$ | $372449$ |
| $-220/3$ | $MM$ | $46$ | $535142$ |
| $-220/3$ | $MJ$ | $46$ | $894382$ |
| $-220/3$ | $JM$ | $44$ | $358619$ |
| $-220/3$ | $JJ$ | $46$ | $518998$ |

All entries of these minors are specified by (29.3)–(29.8). Over $\mathbb Z/1000003\mathbb Z$, row swaps and the elimination step $R_i\leftarrow R_i-c_{ij}c_{jj}^{-1}R_j$ give the displayed residues as the signed products of the resulting nonzero pivots. Their nonzero residues imply rank at least $r$ over $\mathbb R$.

The functionals defining the right side of (29.10) are independent. When there is one evaluation, restrict first to the constant polynomial. When there are three, restrict to $1,y,y^2$; their three $y$ coordinates are distinct, so the evaluation matrix is Vandermonde and invertible. Both $\Lambda_i$ vanish on these low degree polynomials. After eliminating the evaluation functionals, use $y^6,y^5$ to see that $\Lambda_0,\Lambda_1$ are independent. The right side therefore has dimension $46$ when $w\ne JM$ and $44$ when $w=JM$. Its inclusion of every row, and the matching lower rank bounds, prove (29.10). ∎

**推论 29.4（正域中的唯一共同零点）。** In the domain $1<x<3/2$, $y>0$, the simultaneous equations $f_k(x,y)=0$ for all $0\le k\le5$ have only the solution $u_z$.

Proof. If $w\ne JM$, both $x-x_z$ and $y-y_z$ belong to the right side of (29.10), and hence to the row space. Every common zero of the six $f_k$ annihilates every row polynomial and their linear combinations. Thus $x=x_z,y=y_z$.

For $w=JM$, the following two polynomials belong to the same row space:

| $z$ | first polynomial | second polynomial |
| --- | --- | --- |
| $-76$ | $58x+93y^2+151y-93$ | $(6y-1)(y^2+y-1)$ |
| $-220/3$ | $165x+248y^2+413y-248$ | $(8y-1)(y^2+y-1)$ |

Indeed they vanish at all three points in $S_{z,JM}$ and have zero $\Lambda_0,\Lambda_1$. At a common zero, the second polynomial gives $y=y_z$ or $y^2+y-1=0$. In the first case the first polynomial gives $x=x_z$. In the second, that polynomial reduces to $58(x+y)$ or $165(x+y)$, respectively. This contradicts $x>1,y>0$. ∎

## 30. 临界第四 M 的全域点纤维刚性与指定四世界排除

**定理 30.1（指定 U 的四条八读点纤维）。** Fix $r\in\{1/2,2/3\}$ and $E,F\in\{M,J\}$. If a legal complete world $W$ realizes $H_5^r$, has the same actual sixth response as $U_r$ after $E$, and has the same actual seventh response as $U_r$ after the chronological suffix $EF$, then $W=U_r$.

Proof. Apply the chart (29.1)–(29.2) to the source of $W$, and let $G=\eta g$. All $T_j$ at $j=0,1,2,3$ are strictly positive, so $D>0$. The entire gain $G$ has degree at most three. Its first four values therefore determine it by

$$
G(t)=\sum_{j=0}^3\frac{v_j-d}{T_j}\ell_j(t).
\tag{30.1}
$$

The four remaining actual response equations are exactly $a_nd+b_n=0$, $4\le n\le7$. Hence all six $f_{nm}$ vanish. Corollary 29.4 identifies the source coordinates as $u_{z_r}$, including every possible sign of the drift or gain and every lower degree.

At these coordinates, $b_4=0$ and

$$
a_4(u_{-76})=\frac{3936643}{2654208},\qquad
a_4(u_{-220/3})=\frac{3709457}{2654208}.
\tag{30.2}
$$

Both are nonzero, so $a_4d+b_4=0$ gives $d=0$. Formula (30.1) now gives $G=4h$. Since $\operatorname{tr}R=1/4$, the original normalized source and gain are $P=4R=P_r$ and $g=G/4=h$. This proves equality of the entire worlds. Only the single word $MJMMJEF$ is used in this point-fiber assertion. ∎

**定理 30.2（含指定 U 的三世界两读排除）。** For $r\in\{1/2,2/3\}$ and any pairwise distinct complete worlds $U_r,B,C\in\mathcal F(H_5^r)$,

$$
\neg L_2(\{U_r,B,C\},H_5^r).
\tag{30.3}
$$

Proof. Suppose the triple has $L_2$. For each sixth action $E$, choose its actual $L_1$ response child $S_E$. If $U_r\notin S_E$, the cardinality guard forces $S_E=\{B,C\}$. If $U_r\in S_E$, no terminal collision under either final action can involve $U_r$: another member in that collision would share the whole fifth history, the sixth response, and that seventh response with $U_r$, contrary to Theorem 30.1. Consequently the collision required for each final action must again be the pair $B,C$.

For both sixth actions, therefore, $B,C$ share the selected sixth response and both terminal responses after that sixth action. Thus the same pair $\{B,C\}$ has $L_2$ at $H_5^r$.

Apply Theorem 5.1 with $D_0=0$, $\lambda=1$, $\varepsilon=1/12$, $Y=-93/2$, and $z=z_r$. It excludes every distinct two-world $L_2$ in precisely this actual $MJMMJ$ fiber, without drift, root or gain-shape promises. This is a contradiction. The two terminal collision pairs were allowed to differ before Theorem 30.1 forced them to be $B,C$. ∎

**定理 30.3（两个新增完整世界不能补成临界 L3）。** For all legal complete worlds $B,C\in\mathcal F(H_4)$ such that $B,C,U_{1/2},U_{2/3}$ are pairwise distinct,

$$
\neg L_3(\{U_{1/2},U_{2/3},B,C\},H_4).
\tag{30.4}
$$

Proof. Write the four-world set as $K$ and suppose $L_3(K,H_4)$. Its fifth-$J$ branch has an actual response child $K_{J,z}$ with $L_2$. It has at least two worlds. Theorem 5.1, with the same parameters just specified and this actual $z$, excludes cardinality two.

The two prescribed worlds have different fifth-$J$ responses, so $K_{J,z}$ contains at most one of them and hence at most three worlds. It must therefore be exactly $\{U_r,B,C\}$ for one $r\in\{1/2,2/3\}$, with $z=z_r$. Theorem 30.2 excludes $L_2$ on this same triple. This contradiction proves (30.4) for every allowed source, entire gain and drift of both additions. ∎

## 31. 临界第四 M 排除的适用范围与未决共同实现

**约定 31.1（数学来源与结论范围）。** The fourth-$J$ sibling at $H_3$ is supplied by [IV, Theorem 3.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md). The prescribed sources, the $H_4,H_5^r$ data and the baseline root-seven inverse are those of [V, Theorem 6.1 and Proposition 6.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md); the arbitrary-drift two-world exclusion is Theorem 5.1. That baseline inverse alone does not give the unrestricted point fibers of Theorem 30.1. Lemma 18.1 concerns the four matrices $I,JM,MJ,M^2$ at one shared terminal clock; its subsequent injectivity theorem has a different parent history and is not used here. The extra first-response hypotheses of the mixed-prefix triple exclusion are not assumed.

The coefficient-space certificate in Section 29, the four point fibers of Theorem 30.1, and their consumption in Theorems 30.2–30.3 are model-specific deductions (repo-derived). Lagrange interpolation, finite-dimensional duality and integer determinants are classical intermediate tools. Li–Lee–Bresler, [arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1), Definition 2.7 and Theorem 2.8, treat constrained bilinear identifiability modulo its specified ambiguity group; they do not identify the unknown source in this history. Van den Bos–Vaandrager, [arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Section 4, defines adaptive test cases and their distinguishing observations for suspension automata; these finite-state definitions supply no continuous-world response certificate here. No literature priority claim is made for these deductions.

**开放问题 31.2（其他支持与更早兄弟）。** The existence of another finite $K\subseteq\mathcal F(H_4)$ with $L_3(K,H_4)$ is not decided by (30.4). No extraction of a losing pair or a losing four-world subset from a larger losing support is assumed or proved here. IV, Theorem 3.1, still supplies the fourth-$J$ $L_3$ sibling at $H_3$; an actual fourth-$M$ $L_3$ remains necessary for that route to a same-ancestor $L_4$.

Under the affine response translation by $+21$ of [V, Lemmas 9.2–9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md), the corresponding third-clock history is

$$
\overline H_3=(0,M,21,J,317/12,M,21).
$$

The third-$J$ $L_4$ at $(0,M,21,J,317/12)$ and the second-$M$ $L_5$ at $(0,M,21)$ remain separate requirements for the indicated initial-$M$ $L_6$ route. Initial $J$, the original root, and a nine-reading upper bound are not decided by this fixed-support exclusion.

The separate parent $H^-_{\theta,\xi}$ in (8.3) has chronological prefix $MMJMM$, whereas $H_4$ has prefix $MJMM$. Theorem 26.4 recovers every complete world at each $H^-_{\theta,0}$ within its two remaining original-clock reads. Theorems 27.2–27.3 give drift-sign calibration and uniform necessary bounds on a repeated $MM$ signature at $H^-_{\theta,\xi}$. These conclusions do not supply an identification between either of those fibers and $\mathcal F(H_4)$. The nonzero-$\xi$ common-parent two-arm realization remains distinct from the present specified-support exclusion.

For the parent $H_4$ of Definition 28.2, the remaining joint condition is the existence of one fixed family $K\subseteq\mathcal F(H_4)$ and actual values $m,j$ such that

$$
L_2(K_{M,m},(H_4,M,m))
\quad\text{and}\quad
L_2(K_{J,j},(H_4,J,j)).
\tag{31.1}
$$

Both children must be intersections of this same $K$ with their actual response fibers; they may use different retained worlds and different terminal collision pairs. Theorem 5.1 forces the $J$ child to contain at least three worlds. If it has exactly three and contains either prescribed $U_r$, Theorem 30.2 excludes it. Theorem 30.3 only rules out the special four-world support consisting of both prescribed $U$ and two additions. Neither it nor the point-fiber rigidity excludes a support omitting those prescribed worlds, a larger support, an arbitrary parent, or the original root.

## 追加锚（本行以下为增补区）

## 32. 统一小非零偏离的整个外侧父走廊固定 MM 恢复

**定理 32.1（全部正来源上的外侧走廊恢复）。** 保持定义1.1的整个 $\mathcal W_3$、定义8.1的原时钟及字面父历史 $H=H^-_{\theta,\xi}$。取定理27.3中任一个满足(27.9)的统一常数 $B\ge539$，令

$$
\varepsilon=\frac1{10^{20}B},\qquad \mathcal D_B=\{(\theta,\xi)\in\mathbb R^2:0<|\xi|<\varepsilon,\
                 \theta\le11/10\ \text{或}\ \theta\ge181/100\}. \tag{32.1}
$$

则对每个 $(\theta,\xi)\in\mathcal D_B$，在整个实际父纤维 $\mathcal F(H)$ 上，原时钟六、七实际依次选择 $M,M$ 的响应映射

$$
W\longmapsto\bigl(r_M^{(6)}(W),r_{MM}^{(7)}(W)\bigr) \tag{32.2}
$$

对完整世界单射。因此固定接续 $MM$ 在至多两个进一步实际读数内恢复整个父纤维；每个实际第六 $M$ 子纤维的末 $M$ 响应单射，且

$$
\forall K\subseteq\mathcal F(H),\qquad \neg L_2(K,H). \tag{32.3}
$$

证明。以下所有来源量沿用(8.1)、(8.5)—(8.6)。对 $\Phi\ne0$ 的来源使用(23.2)的归一化提升和矩阵，记

$$
x=\frac1\Phi(nu^2,nu,n,h)^{\mathsf T},\quad \mathsf A(k)x=(1,q,\mu,\eta)^{\mathsf T},\quad \mathcal T(y)=y_0y_2-y_1^2,\quad e=(0,1,0,0)^{\mathsf T}. \tag{32.4}
$$

向量指标从零开始；$\mathcal T$ 只取前三分量。矩阵 $\mathsf A$ 关于 $k$ 仿射，$e$ 的非零分量对应签名中的 $q$。本证明需要两个完整闭区间

$$
I_-=[1/2,551/500],\qquad I_+=[226/125,3],\qquad \mathcal I=I_-\cup I_+. \tag{32.5}
$$

先给用于整个 $\mathcal I$ 的有理符号及范数证书。复用(23.5)的 $Q$，置

$$
\begin{aligned}
F(k)&=208827k^4-219885k^3-532630k^2+250705k+359123,\\
N(k)&=\bigl(-5358k^2+2012k+6458,\,
 -1674k^2-166k+1028,\,
 -2082k^2+756k+2388,\,
 -12k^3-546k^2-478k-64\bigr)^{\mathsf T}.
\end{aligned} \tag{32.6}
$$

由(23.2)逐项取余子式，有 $\det\mathsf A=40Q$、$\operatorname{adj}(\mathsf A)e=N$，以及多项式恒等式 $N_0N_2-N_1^2=40F$。因而在 $Q\ne0$ 处

$$
v(k)=\mathsf A(k)^{-1}e=\frac{N(k)}{40Q(k)},\qquad
\mathcal T(v(k))=\frac{F(k)}{40Q(k)^2}. \tag{32.7}
$$

为完整指定有限精确证书，对次数至多 $d$ 的多项式 $p$ 及有理区间 $I=[a,b]$，令 $c_j=[t^j]p(a+(b-a)t)$，并定义

$$
\beta_i^{I,d}(p)=\sum_{j=0}^i c_j\frac{\binom ij}{\binom dj},
\qquad
p(a+(b-a)t)=\sum_{i=0}^d\beta_i^{I,d}(p)\binom di t^i(1-t)^{d-i}. \tag{32.8}
$$

这里系数不足的 $c_j$ 为零。$0\le t\le1$ 时基函数非负且和为一；故下表的系数极值控制整个闭区间。表内多项式均取 $d=4$，系数界均是精确有理数：

$$
\begin{array}{c|c|c}
 I&\min_i\beta_i^{I,4}(F)&\text{对 }Q\text{ 的系数界}\\ \hline
 I_-&142435964065727/62500000000&
       \max_i\beta_i^{I_-,4}(Q)=-99/4\\
 I_+&774891446877/244140625&
       \min_i\beta_i^{I_+,4}(Q)=8176970406/244140625
\end{array} \tag{32.9}
$$

因此 $\mathcal I$ 上 $F>2000$、$|Q|>24$。又 $|k|\le3$ 给
$|Q|\le6\cdot3^4+15\cdot3^3+18\cdot3^2+29\cdot3+8=1148$。
记 $C_{ij}(k)=(\operatorname{adj}\mathsf A(k))_{ij}$，其次数至多三。用(32.8)取 $d=3$，四个行号依次为 $0,1,2,3$，直接有如下严格整数上界：

$$
\begin{array}{c|rrrr}
 I&\sum_j\max_i|\beta_i^{I,3}(C_{0j})|&
 \sum_j\max_i|\beta_i^{I,3}(C_{1j})|&
 \sum_j\max_i|\beta_i^{I,3}(C_{2j})|&
 \sum_j\max_i|\beta_i^{I,3}(C_{3j})|\\ \hline
 I_-&<32000&<5000&<12000&<6000\\
 I_+&<385000&<141000&<150000&<57000
\end{array} \tag{32.10}
$$

式(23.2)、(32.8)及这些整数比较指定了全部有限有理计算，不使用采样或根近似。以最大绝对行和为矩阵范数，(32.9)—(32.10)遂给 $\mathcal I$ 上

$$
\|\mathsf A^{-1}\|_\infty<
 \frac{400000}{40\cdot24}<4000,\qquad
\|\mathsf A'\|_\infty=648,\qquad
\mathcal T(v)>\frac{2000}{40\cdot1148^2}>\frac1{30000}. \tag{32.11}
$$

$\mathsf A'$ 的四个绝对行和为 $16,60,50,648$。这同时证明所有用到的矩阵逆存在。

现在反设(32.2)在某个 $(\theta,\xi)\in\mathcal D_B$ 上有不同完整世界 $W_1,W_2$ 的碰撞。定理23.2给不同来源、$\Phi_i\ne0$、$\mu_1=\mu_2$、$\eta_1=\eta_2$，且

$$
r=q_1-q_2\ne0,\qquad k_2-k_1=\xi r,\qquad
\theta=k_i+\xi q_i,\qquad x^{(i)}=x(P_i). \tag{32.12}
$$

两来源均属于(27.1)的 $\mathscr C$。因此仅对这对来源使用定理27.3，得到

$$
|q_i|,|\mu_i|,|\eta_i|\le B,\qquad
|\theta-k_i|\le B|\xi|<10^{-20},\qquad 1/2<k_i<3. \tag{32.13}
$$

末项是(27.23)的严格正性。不限制任意父世界或其他末动作碰撞对。若 $\theta\le11/10$，两 $k_i$ 都小于 $11/10+10^{-20}<551/500$，故同在 $I_-$；若 $\theta\ge181/100$，两 $k_i$ 都大于 $181/100-10^{-20}>226/125$，故同在 $I_+$。这涵盖全部实 $\theta$，没有另设来源紧性条件。

由 $B\ge539>1$、(32.4)、(32.11)及(32.13)，这对来源满足

$$
\|x^{(i)}\|_\infty
 \le\|\mathsf A(k_i)^{-1}\|_\infty
           \|(1,q_i,\mu_i,\eta_i)\|_\infty<4000B. \tag{32.14}
$$

由于 $\mathsf A$ 仿射，相减响应方程而不取任何中间参数的逆，精确得到

$$
\begin{aligned}
\mathsf A(k_1)(x^{(1)}-x^{(2)})
 &=r e+(k_2-k_1)\mathsf A'x^{(2)},\\
\frac{x^{(1)}-x^{(2)}}r&=v(k_1)+z,\qquad
z=\xi\,\mathsf A(k_1)^{-1}\mathsf A'x^{(2)},\\
\|z\|_\infty&<4000^2\cdot648\,B|\xi|
 <\frac{10368000000}{10^{20}}<2\cdot10^{-10}.
\end{aligned} \tag{32.15}
$$

这里 $r\ne0$ 的依据正是(32.12)，无需为 $|r|$ 设置下界。由 $\|v\|_\infty<4000$，

$$
|\mathcal T(v+z)-\mathcal T(v)|
 \le4\|v\|_\infty\|z\|_\infty+2\|z\|_\infty^2
 <16000(2\cdot10^{-10})+2(2\cdot10^{-10})^2<\frac1{100000}. \tag{32.16}
$$

结合(32.11)，$\mathcal T(v+z)>1/30000-1/100000>0$，于是
$\mathcal T(x^{(1)}-x^{(2)})=r^2\mathcal T(v+z)>0$。

另一方面，定理27.2对同一实际 $MM$ 记录给 $\Phi_1\Phi_2>0$。令 $c_i=n_i/\Phi_i$，则 $n_i>0$、$c_1c_2>0$。提升的前三分量为 $c_i(u_i^2,u_i,1)$，直接相减给

$$
\mathcal T(x^{(1)}-x^{(2)})=-c_1c_2(u_1-u_2)^2\le0, \tag{32.17}
$$

矛盾。这个非严格不等式包括相同 $u$；(32.15)允许来源对任意趋近对角。由此排除所有不同完整世界的碰撞，证明(32.2)。

固定父及其实际第六读数 $w$ 后，若末 $M$ 响应相同，就有相同的(32.2)，故完整世界相同。实际响应像上取唯一完整世界的逆即给固定 $MM$ 解码器；空纤维无实际路径，单点纤维可早停。若任意 $K\subseteq\mathcal F(H)$ 有 $L_2$，递归(1.2)的第六 $M$ 条款会给一个实际子纤维的 $L_1$，其末 $M$ 条款再给两个不同世界的碰撞，违反上述单射，故(32.3)成立。没有要求末 $J$ 或另一第六臂使用同一对世界，也没有对它们套用 $B$ 界。

全部推导只除已非零的 $\xi,\Phi,r,Q$ 及(8.2)中原本严格正的迹量；事实上(32.15)不除 $\xi$，(32.12)中签名相等只使用 $\xi\ne0$。未除 $\Delta$、任何采样增益或增益的最高次系数。因此整个非零至多三次实多项式、任意增益符号、降次、采样根、重根、$\Delta=0$ 及任意常漂移均保留。未给来源或漂移增加紧性假设；非紧尾部的控制来自已有全源定理27.3与(32.14)。

接续动作是同一不可复制、不可重置轨迹上原时钟六、七的两个实际 $M$，每步立即读取；连同既有初读共至多八读。这里的逆仅属于精确实响应合同，$B$ 是存在性的统一界，$\varepsilon$ 不是数值稳定半径或有限位算法的运行参数；不主张逆的连续性、可计算性或稳定性。

承重内容是全源差几何的符号不相容、统一扰动控制及其整个外侧父走廊的固定 $MM$ 消费者，属于仓内推导（repo-derived）；四次式展开本身不单列为成果。伴随矩阵恒等式与范数估计是成熟线性代数；Bernstein 非负性、单位分解及系数凸包界沿用第25章的成熟供应，参见 Patrikalakis、Maekawa、Cho，[§1.3.1](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node9.html)。定理23.2和27.2—27.3分别供应完整实际碰撞的父坐标、同号性与全源重复签名界；本条不重证这些结果，不申领外部文献优先权。这是普通数学纸面证明，非 Lean 核验。

本条仅收缩 $\mathcal P_M\cap\mathcal P_J$ 的可能父域：$0<|\xi|<\varepsilon$ 时，若共同父失败存在，就必须有 $11/10<\theta<181/100$。这个中心带、$|\xi|\ge\varepsilon$ 的非零偏离父族、同父两臂共同实现及更早祖先仍未解决；零偏离只复用定理26.4的策略，不声称该层固定 $MM$ 单射。第28—31章的 $MJMM$ 历史不作本证明供应，亦不与这里的 $MMJMM$ 认同。原根八读／九读判别、九读上界及有限精度稳定性均未由本定理结清。∎

## 追加锚（本行以下为增补区）
