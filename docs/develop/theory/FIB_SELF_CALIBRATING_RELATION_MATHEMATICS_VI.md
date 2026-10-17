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
