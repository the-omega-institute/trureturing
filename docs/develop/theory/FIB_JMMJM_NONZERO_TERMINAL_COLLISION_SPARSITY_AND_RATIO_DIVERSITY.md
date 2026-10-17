# FIB JMMJM Nonzero-Terminal Collision Sparsity and Ratio Diversity

## 1. Complete worlds and the entire original-clock ancestor

**Definition 1.1 (acquisition model).** A complete world is
$W=(P,g,\delta)$, where $P$ is a strictly entrywise positive real
$2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and
$\delta\in\mathbb R$. Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The reading at original clock $i$ is

$$
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.
\tag{1.2}
$$

The initial reading counts. Each individual atom is immediately read
on one unresettable, uncopyable trajectory. Eight total readings use
clocks $0,\ldots,7$. There are no skipped readings, unread compound
actions, empty-action readings, clock renumberings or extra ports.
Actions, stops and complete-target answers may be arbitrary
deterministic functions of the entire actual history, without
regularity or computability assumptions. The source need not be
symmetric. Both gain signs, every lower actual degree, all sampled
roots, other roots and repeated roots are initially allowed.

These are the acquisition and complete-target conventions of
[VII, Definition 1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md)
and [VIII, Definition 1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md).

**Definition 1.2 (literal six-reading history).** Fix arbitrary real
$D_0,Y,z$ and nonzero real $\lambda$. Throughout, the entire ancestor is

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
        M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.3}
$$

Write $\mathcal F(H)$ for the complete worlds realizing every action
and every reading of this history. Put

$$
f=g/\lambda,\quad d=(\delta-D_0)/\lambda,\quad
\widehat Y=(Y-D_0)/\lambda,\quad \widehat z=(z-D_0)/\lambda.
\tag{1.4}
$$

The inverse is $g=\lambda f$, $\delta=D_0+\lambda d$.
Every normalized response $w$ corresponds to the raw response
$D_0+\lambda w$. This is bijective for either sign of $\lambda$,
preserves equality and actual response children, and changes no clock.
The observed $D_0$ is not assumed to be the drift.

For

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
0<r<1,\quad u,v>0,\quad uv=r(1-r),
\tag{1.5}
$$

the six cumulative matrices are

$$
\begin{gathered}
I,\ J,\ L,\ J+L,\ C,\ Q,\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\\
J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\qquad
C=J(J+L)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix}.
\end{gathered}
\tag{1.6}
$$

Consequently every world under discussion satisfies all six equations

$$
\begin{aligned}
f(0)+d&=0,\\
f(1)(u+v)+d&=24,\\
f(2)(1+u)+d&=48,\\
f(3)(1+2u+v)+d&=312/5,\\
f(4)(1+r+u+v)+d&=\widehat Y,\\
f(5)(2-r+3u+v)+d&=\widehat z.
\end{aligned}
\tag{1.7}
$$

All six trace factors are positive. In particular the last two
equations are actual ancestor constraints, not adjustable future
observations. The explicit stratum of this volume is

$$
\mathcal F^{\ne0}_7(H)=\{W\in\mathcal F(H):f(7)\ne0\}.
\tag{1.8}
$$

There is initially no restriction on $f(6)$.

**Definition 1.3 (actual losing sets).** For a known compatible set
$K$ at a history $H'$ ending at clock $i$, and within clocks through
seven, define

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:
L_r(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{1.9}
$$

Here $0\le r<7-i$ in the recursive line. Each child retains the same
fixed complete worlds and every ancestor equation. An empty or
singleton child fails $L_0$. At one remaining reading, failure of
$L_1$ means that a terminal action is injective on the whole child,
or that a singleton can already be returned. Thus failure of $L_2$
on the known finite sets below gives one deterministic policy for
every actual response child. Predictions for unchosen actions are
functions on candidates, not additional physical acquisitions.

## 2. Established positive chart and four-terminal reconstruction

The positive $Q$ chart is the established interface of
[VII, Definition 1.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md).
The four-terminal rank-one interface is displayed in VII's proof of
Theorem 4.1, where it is credited to V, Theorem 7.1. The needed
identities and inverse are proved here to fix every normalization.

**Lemma 2.1 (chart with its complete inverse).** Put
$\eta=(QP)_{22}>0$, $R=P/\eta$ and $F=\eta f$. There are unique
coordinates $x,y$ such that

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(1-2x)y&1-2x\\(3x-1)y&3x-1\end{pmatrix},
\qquad \frac13<x<\frac12,\quad y>0.
\tag{2.1}
$$

Conversely each point of this strip gives a strictly positive
rank-one $R$. With $s=x+y$, $p=xy$, its six traces are

$$
\begin{aligned}
T_0&=s+2x-2p-1=(1-2x)y+3x-1,\\
T_1&=1-x-s+3p, &T_2&=s-2p,\\
T_3&=1-x+p, &T_4&=s-p, &T_5&=p+1.
\end{aligned}
\tag{2.2}
$$

All are positive, and the complete inverse and ancestor are

$$
P=R/T_0,\qquad f=T_0F,\qquad
F(i)T_i+d=(0,24,48,312/5,\widehat Y,\widehat z)_i
\quad(0\le i\le5).
\tag{2.3}
$$

Proof. The positive rank-one matrix $QP/\eta$ has lower right entry
one. Define its upper right and lower left entries as $x,y$; its
zero determinant forces its upper left entry to be $xy$. Since

$$
Q^{-1}=\begin{pmatrix}-2&1\\3&-1\end{pmatrix},
\tag{2.4}
$$

multiplication gives (2.1). Positivity of the upper and lower entries
in its second column gives $x<1/2$ and $x>1/3$. Positivity of $QR$
gives $y>0$. Conversely these inequalities make every displayed
entry of $R$ positive; its columns are proportional, so it has
rank one. Its trace $T_0=(1-2x)y+3x-1$ is positive. Normalizing that
trace gives a positive rank-one trace-one source. Since
$\operatorname{tr}(P/\eta)=1/\eta$, we have $T_0=1/\eta$ and
$f=T_0F$ as asserted.

Taking traces against the six explicit matrices (1.6) gives (2.2).
For example $T_1=R_{12}+R_{21}$, $T_2=T_0+R_{12}$,
$T_3=T_1+T_2$, $T_4=T_0+R_{11}+T_1$ and
$T_5=\operatorname{tr}(QR)=p+1$. These expressions also prove
positivity of every denominator used in (2.3). Substitution in
(1.7) proves all of (2.3), including the two late readings. ∎

**Definition 2.2 (future response functions).** For each world put
$h=F(6)$ and $t=F(7)\ne0$. The counterfactual sixth predictions are

$$
U=d+hs\quad\hbox{after }J,\qquad
V=d+h(s+1)\quad\hbox{after }M.
\tag{2.5}
$$

These are two alternative predictions on each fixed world. Only the
chosen sixth atom is executed and read. The four terminal response
functions in chronological order $JJ,JM,MJ,MM$ are

$$
\begin{aligned}
A&=d+t(p+1),\\
B&=A+tx,\\
C&=A+ty,\\
D&=d+t(p+s+2)=A+t(s+1)=C+t(x+1).
\end{aligned}
\tag{2.6}
$$

In particular a terminal $B$ is available only after executing and
immediately reading sixth $J$, then executing and reading seventh
$M$. The same chronological convention applies to every column.

Indeed for $Z=QR=\left(\begin{smallmatrix}p&x\\y&1\end{smallmatrix}\right)$,
the traces of $JZ,MZ$ are $s,s+1$, and the traces of
$J^2Z,MJZ,JMZ,M^2Z$ are $p+1,p+x+1,p+y+1,p+s+2$.
Thus (2.5)–(2.6) follow directly from (1.2).

Equivalently set

$$
X=f(7)QP=t\begin{pmatrix}xy&x\\y&1\end{pmatrix}
 =\begin{pmatrix}a&b\\c&e\end{pmatrix},\qquad
q=\frac{f(6)}{f(7)}=\frac{g(6)}{g(7)}=\frac ht.
\tag{2.7}
$$

Every entry of $X$ is nonzero with sign $t$, $ae=bc$, and
$b/e=x\in(1/3,1/2)$, $c/e=y>0$. The same response functions are

$$
\begin{aligned}
A&=a+e+d,& B&=A+b,& C&=A+c,& D&=A+b+c+e,\\
U&=d+q(b+c),& V&=d+q(b+c+e).
\end{aligned}
\tag{2.8}
$$

**Lemma 2.3 (complete-world four-terminal inverse).** If two worlds
of $\mathcal F^{\ne0}_7(H)$ agree in all of $A,B,C,D$, they are
the same complete world, even when their drifts were initially
unrestricted.

Proof. The four scalars determine

$$
b=B-A,\quad c=C-A,\quad e=D-C-B+A,\quad
a=bc/e,\quad d=A-a-e.
\tag{2.9}
$$

The division is legal because $e=f(7)(QP)_{22}\ne0$ by (1.8) and
positivity. Rank one gives $a=bc/e$. Next

$$
Q^{-1}X=f(7)P,\qquad
f(7)=\operatorname{tr}(Q^{-1}X)\ne0,\qquad
P=\frac{Q^{-1}X}{\operatorname{tr}(Q^{-1}X)}.
\tag{2.10}
$$

These identities recover the source and terminal gain. For that
same recovered source and drift, the first four equations (1.7),
whose trace factors are positive, determine $f(0),\ldots,f(3)$.
Four distinct sample arguments determine the entire polynomial of
degree at most three. Finally (1.4) recovers $g,\delta$. No leading
coefficient, sampled ancestor gain or root difference is divided
out, so degree drops and repeated roots are included. ∎

## 3. Different proper pairs and terminal-sign connectivity

**Theorem 3.1 (arbitrary-drift proper-pair restriction).** Let
$K=\{W_1,W_2,W_3\}\subseteq\mathcal F^{\ne0}_7(H)$ consist of
three distinct complete worlds. Suppose $L_2(K,H)$ and neither
sixth action has a response shared by all three. Then the two losing
sixth children are different proper pairs. All three terminal gains
$g_i(7)$ have one common sign. In particular differing terminal
signs force a shared-three sixth response for at least one action,
without a common-drift hypothesis.

Proof. A sixth child witnessing $L_1$ has at least two worlds.
On a three-world set without a shared-three response, this is the
unique colliding pair for that sixth action; the remaining world
has a different response. A two-world child has $L_1$ exactly when
its two worlds agree in both terminal columns for that branch.
The $J$ pair therefore agrees in $A,B$, and the $M$ pair in $C,D$.
If those pairs were the same, they would agree in all four terminal
columns, contradicting distinctness by Lemma 2.3. Relabel so that
the $J$ pair is $\{1,2\}$ and the $M$ pair is $\{1,3\}$.

Equality of $A,B$ gives $b_1=b_2$. Since $b_i=t_ix_i$ and $x_i>0$,
the terminal chart gains $t_1,t_2$ have the same sign. Equality of
$C,D$ gives $b_1+e_1=b_3+e_3$. Since
$b_i+e_i=t_i(x_i+1)$ with $x_i+1>0$, $t_1,t_3$ have the same sign.
The two different pairs connect all three worlds. Since
$f_i(7)=T_{i,0}t_i$ with $T_{i,0}>0$, and the single common scale
$\lambda$ multiplies every $f_i$, all original $g_i(7)$ have the
same sign. No drift equality or sixth-gain nonvanishing was used.
Every equation concerns these same three worlds on (1.3). ∎

## 4. Common sixth predictions: five strict ratios and the swap case

**Theorem 4.1 (at most one common terminal coordinate).** Two distinct
worlds of $\mathcal F^{\ne0}_7(H)$ on the entire ancestor (1.3),
with common $d$, common $U$, common $V$, and nonzero sixth gains,
can agree in at most one of $A,B,C,D$.

Proof. By (2.5), $h=V-U$ is common and nonzero: $f(6)=T_0h$ and
$T_0>0$. Equality of $U=d+hs$ then gives a common $s$. Thus
$y=s-x>0$ in both worlds. Define

$$
K_0=1+xy,\quad K_1=1+xy+x,\quad
K_2=1+xy+y,\quad K_3=2+xy+x+y.
\tag{4.1}
$$

All $K_j$ are positive, and terminal coordinates are respectively
$d+tK_0,d+tK_1,d+tK_2,d+tK_3$, with $t\ne0$.

At fixed $s$, differentiation in $x$ gives
$K_0'=y-x$, $K_1'=y-x+1$, $K_2'=y-x-1$ and $K_3'=y-x$.
The complete five strict numerator identities are

$$
\begin{aligned}
K_1'K_0-K_1K_0'&=1+x^2,\\
K_2'K_0-K_2K_0'&=-(1+y^2),\\
K_2'K_1-K_2K_1'&=-(2+x^2+y^2+s),\\
K_3'K_1-K_3K_1'&=-\bigl(1+(y+1)^2\bigr),\\
K_3'K_2-K_3K_2'&=1+(x+1)^2.
\end{aligned}
\tag{4.2}
$$

For full algebraic verification, put $w=y-x$. The first numerator
is $K_0-xw=1+x^2$; the second is
$-K_0-yw=-(1+y^2)$. Since $K_2=K_1+w$ and $w'=-2$, the third
is $-2K_1-w(w+1)=-(2+x^2+y^2+x+y)$. Since
$K_3=K_1+y+1$, the fourth is
$-K_1-(y+1)(w+1)=-[1+(y+1)^2]$. Since
$K_3=K_2+x+1$, the fifth is
$K_2-(x+1)(w-1)=1+(x+1)^2$.
The quotient rule therefore yields

$$
\begin{aligned}
(K_1/K_0)'&=(1+x^2)/K_0^2>0,\\
(K_2/K_0)'&=-(1+y^2)/K_0^2<0,\\
(K_2/K_1)'&=-(2+x^2+y^2+s)/K_1^2<0,\\
(K_3/K_1)'&=-[1+(y+1)^2]/K_1^2<0,\\
(K_3/K_2)'&=[1+(x+1)^2]/K_2^2>0.
\end{aligned}
\tag{4.3}
$$

Every denominator is positive; also $s=x+y>0$. The entire legal
fixed-$s$ domain

$$
I_s=\{x:1/3<x<1/2,\ x<s\}
\tag{4.4}
$$

is an interval, possibly empty. Each ratio in (4.3) is strictly
monotone on this interval. If two worlds share a pair of terminal
coordinates other than $\{A,D\}$, divide their offsets from the
common drift. Those offsets are nonzero because $t\ne0$ and
$K_j>0$. One of the five ratios (4.3) is equal in both worlds,
forcing equal $x$. Common $s$ then forces equal $y$. One equal
terminal coordinate forces equal $t$. In particular the sources
and drift are the same. The first four positive trace factors of
the ancestor determine equal gain polynomials, as in Lemma 2.3.
The worlds coincide, contrary to the hypothesis.

It remains to exclude precisely $\{A,D\}$. Since
$D-A=t(s+1)$ and $s+1>0$, equality of $A,D$ gives common $t$.
Equality of $A=d+t(p+1)$ gives common $p$. Two real pairs with the
same sum and product are either individually equal or exchanged:
they are the two roots, including multiplicity, of
$Z^2-sZ+p$. Individual equality gives the same world as above.
In the distinct case

$$
x_2=y_1,\quad y_2=x_1,\quad \Delta=x_1-x_2\ne0.
\tag{4.5}
$$

The two worlds then have equal $T_2=s-2p$, $T_4=s-p$ and
$T_5=p+1$. Their common drift and actual readings at clocks
$2,4,5$ in (2.3) force equal $F$ samples at those clocks, since
all three traces are positive. Their common sixth predictions
gave equal $F(6)=h$, and their common $A,D$ gave equal $F(7)=t$.
Thus $F_1-F_2$ has the five distinct zeros $2,4,5,6,7$.
Its degree is at most three, so it vanishes identically.
In particular both late ancestor equations, with the same
$\widehat Y,\widehat z$, are used in this step.

Call the common polynomial $F$. From (2.2) and common $s,p$,

$$
T_{1,0}-T_{2,0}=2\Delta,\qquad
T_{1,1}-T_{2,1}=-\Delta.
\tag{4.6}
$$

Subtracting the clock-zero and clock-one equations of the same
ancestor gives $2\Delta F(0)=0$ and $-\Delta F(1)=0$.
Thus $F(0)=F(1)=0$. Clock zero then gives $d=0$, while clock
one gives $d=24$, a contradiction. The contradiction uses no
division by a sampled gain and is valid for every degree drop or
root multiplicity. This excludes the last possible coordinate
pair and proves the theorem. ∎

**Corollary 4.2 (one fixed injective coordinate for at most three
known worlds).** Let $K\subseteq\mathcal F^{\ne0}_7(H)$ be known,
with $|K|\le3$, common $d,U,V$, and nonzero sixth gains. There
is one terminal coordinate injective on all of $K$. Its fixed
chronological two-atom word gives a lawful complete-target inverse
on the whole known set, using at most eight total readings.

Proof. There are at most three unordered pairs of distinct members.
If every one of the four terminal coordinates had a collision,
choose a colliding pair for each coordinate. Some pair would then
occur for two coordinates. This contradicts Theorem 4.1. Hence one
coordinate is injective on the whole known set. This argument also
handles two members; on an empty set or singleton any coordinate
is injective.

Choose the first injective coordinate in the order $A,B,C,D$.
Choose the corresponding fixed chronological word $JJ,JM,MJ,MM$,
and denote its first and second atoms by $E,F$. The inverse sends
an actual terminal raw response $v$ to the unique $W\in K$ whose
selected normalized coordinate equals $(v-D_0)/\lambda$.
Existence follows from actual membership, and injectivity proves
uniqueness of the complete world, not just of a parameter.

More explicitly, for every real raw sixth response $w$, let

$$
K_{E,w}=K\cap\mathcal F(H,E,w).
\tag{4.7}
$$

For every such $w$ and every real raw terminal response $v$,

$$
\left|K_{E,w}\cap\mathcal F(H,E,w,F,v)\right|\le1.
\tag{4.8}
$$

Indeed both sets are subsets of the same known $K$, on which
the selected terminal scalar is injective. Thus every actual
sixth child fails $L_1$, and $K$ fails $L_2$. Execute and read
each selected atom immediately; a known singleton or a singleton
intermediate child may stop earlier. Empty children are unreachable.
The six ancestor readings plus these two give at most eight.
The cardinality bound is essential to this pigeonhole argument:
for larger sets there can be at least four distinct colliding
pairs. No assertion for a larger or infinite common-prediction
class follows from this proof. Common drift and both predictions
are promises on $K$, not data acquired on both sixth branches. ∎

## 5. Common drift forces sixth-sign agreement and excludes shared-three branches

**Theorem 5.1 (sixth signs, including zero).** Suppose a three-world
$K\subseteq\mathcal F^{\ne0}_7(H)$ has common drift and $L_2$.
Then all three sixth gains have the same sign, where zero is a
separate sign. If that common sign is nonzero, neither sixth action
has a response shared by all three. The two sixth partitions are
different proper pairs, and the terminal gains have a common sign.

Proof. In chart coordinates, the normalized sixth responses minus
the common $d$ are $h_i s_i$ and $h_i(s_i+1)$. Both multipliers
are positive, and $f_i(6)=T_{i,0}h_i$ with $T_{i,0}>0$.
Thus distinct sixth-sign classes cannot share a response for either
action. Multiplication by the common nonzero $\lambda$ preserves
the assertion that all original sixth signs are equal.

If all three signs differ, every sixth child has size at most one,
contrary to $L_2$. If the signs are not all equal but two agree,
that unique same-sign pair is the only possible sixth child of
size at least two for either action. The $L_2$ condition would
make that pair agree in $A,B$ and in $C,D$. Lemma 2.3 would make
the two complete worlds identical. Therefore all three signs
coincide. This includes the all-zero case and excludes every
mixture of zero and nonzero.

Now suppose the common sixth sign is nonzero. If both sixth
responses were shared by all three, Corollary 4.2 would give one
fixed injective terminal coordinate on the triple, contradicting
$L_2$. If exactly one sixth action had a shared-three response,
the other action would have a losing proper-pair child. That
pair has both sixth predictions common: one because its own
response collides, the other because the other action's response
is shared by the whole triple. Its drift is common and its sixth
gains are nonzero. Its $L_1$ condition requires equality in two
terminal coordinates, $A,B$ for a $J$ child or $C,D$ for an $M$
child. Theorem 4.1 excludes this.

This argument places no requirement on the two terminal collision
pairs inside the shared-three child. They can be different pairs;
the contradiction uses the other, actual proper-pair child.
Thus no shared-three sixth response is possible. Theorem 3.1
applies and, after relabeling, the exact pattern is

$$
U_1=U_2\ne U_3,\qquad V_1=V_3\ne V_2,\qquad
A_1=A_2,\ B_1=B_2,\ C_1=C_3,\ D_1=D_3.
\tag{5.1}
$$

It also gives the common terminal-gain sign. In the all-zero
sixth case, $U_i=V_i=d$ for every world; the shared-three pattern
is retained and no terminal-sign conclusion is asserted here. ∎

## 6. A common nonzero future ratio is incompatible with a losing triple

**Theorem 6.1 (diagonal-swap obstruction).** No three distinct worlds
of $\mathcal F^{\ne0}_7(H)$ with common drift and common nonzero
ratio

$$
q_i=g_i(6)/g_i(7)=q\ne0
\tag{6.1}
$$

have $L_2$. Sources and cubic-or-lower gain shapes may all differ.

Proof. Suppose otherwise. The nonzero ratio and nonzero terminal
gains make all sixth gains nonzero. Theorem 5.1 and Theorem 3.1
give (5.1) and a common terminal sign. Let this sign for the
normalized terminal matrices $X_i$ be $\sigma\in\{1,-1\}$.
For the rest of this proof replace every $X_i$ by $\sigma X_i$
and use $a_i,b_i,c_i,e_i$ for its entries. All entries are now
strictly positive,

$$
a_ie_i=b_ic_i,\qquad 1/3<b_i/e_i<1/2.
\tag{6.2}
$$

Terminal equality equations with common drift can be multiplied
by $\sigma$ after subtracting that drift. Sixth equality equations
can be divided by the common nonzero $q$, and then multiplied
by $\sigma$. Hence all equalities below follow from the original
actual response equalities, with no sign change in positivity.

Write $X_1=\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$.
The $J$ pair $\{1,2\}$ shares $A,B$, so
$b_2=b$ and $a_2+e_2=a+e=:S$. Equality of $U_1,U_2$ in (2.8)
gives $b+c=b_2+c_2$, so $c_2=c$. Rank one therefore gives
$a_2e_2=bc=ae$. Eliminating $a_2=S-e_2$ gives the full factorization

$$
e_2^2-Se_2+ae=(e_2-e)(e_2-a)=0.
\tag{6.3}
$$

If $e_2=e$, every entry of $X_2$ equals that of $X_1$.
Together with common drift and the first four actual ancestor
readings this makes the complete worlds equal by (2.10) and
interpolation. Distinctness thus forces

$$
e_2=a,\qquad a_2=e.
\tag{6.4}
$$

If the quadratic roots repeat, $a=e$, (6.4) also gives the same
matrix, so distinctness is already impossible. Otherwise the
second world's strip gives

$$
1/3<b/a<1/2,\qquad a>2b>b>0.
\tag{6.5}
$$

For the $M$ pair $\{1,3\}$, equality of $C,D$ gives
$b_3+e_3=b+e=:K$. Equality of $V_1,V_3$ gives
$b_3+c_3+e_3=b+c+e$, hence $c_3=c$. Equality of $C$ then gives
$a_3+e_3=a+e=S$. Rank one now gives

$$
(S-e_3)e_3=(K-e_3)c,
\qquad e_3^2-(S+c)e_3+Kc=0.
\tag{6.6}
$$

Since $ae=bc$, we have $Kc=(b+e)c=e(a+c)$ and
$S+c=e+a+c$. Thus the second complete factorization is

$$
e_3^2-(S+c)e_3+Kc=(e_3-e)(e_3-a-c)=0.
\tag{6.7}
$$

The root $e_3=e$ again makes all entries agree with $X_1$,
so distinctness forces $e_3=a+c$. If these roots coincide,
there is only that identical world and the contradiction is
already obtained. Otherwise the remaining entry must satisfy
the decisive identity

$$
\begin{aligned}
b_3&=b+e-a-c\\
   &=b+e-a-\frac{ae}{b}
     =\frac{(b-a)(b+e)}b<0.
\end{aligned}
\tag{6.8}
$$

Here the only entry denominator is $b>0$; the last inequality
uses (6.5) and $b+e>0$. This contradicts strict positivity of
the third sign-adjusted matrix. Both possible roots of each
quadratic and their repeated-root cases have been included.
No discriminant, root difference or leading gain coefficient
was divided out. The only gain-ratio cancellation used the
explicit common $q\ne0$. The proof requires no common source,
no common gain shape and no coefficient array. ∎

**Corollary 6.2 (finite known-set policy under the ratio promise).**
A known $K\subseteq\mathcal F^{\ne0}_7(H)$ with at most three
members, common drift and common nonzero $q$ has one deterministic
two-further-reading complete-target policy.

Proof. A set of two distinct worlds cannot have $L_2$: its two
losing sixth children would have to be that same pair and require
all four terminal equalities, contradicting Lemma 2.3. Three
members are excluded by Theorem 6.1. Empty sets are unreachable
and singletons can stop. Therefore choose the first sixth action
$E$ in the order $J,M$ for which every raw-response child
$K_{E,w}$ fails $L_1$. Such an action exists by the negation
of (1.9). For each real raw $w$, stop on a singleton or choose
the first terminal action $F_w$ in the order $J,M$ injective
on the whole child. This is possible because that child fails
$L_1$. For every real $w,v$ the retained set

$$
K_{E,w}\cap\mathcal F(H,E,w,F_w,v)
\tag{6.9}
$$

has at most one member. At every reachable value return that
unique complete world. All choices are functions of the same
known $K$ and the actual sixth response. Each selected atom
is immediately read, giving at most eight total readings.
The last action may depend on that actual sixth child; unlike
Corollary 4.2, no single fixed terminal coordinate is asserted.
Neither theorem makes an arbitrary-cardinality class claim. ∎

## 7. Exact simultaneous-system interface for the remaining cases

This section is bookkeeping for precise open systems. It is not
independent new mathematical content or a feasibility verdict.
It keeps the common ancestor, source legality, interpolation and
actual-child quantifiers explicit.

**Definition 7.1 (full legal-world parameters).** For the fixed
$\widehat Y,\widehat z$ of (1.4), choose three triples
$(x_i,y_i,d_i)$, $i=1,2,3$, satisfying

$$
1/3<x_i<1/2,\quad y_i>0,\quad d_i\in\mathbb R,
\quad (x_i,y_i,d_i)\ne(x_j,y_j,d_j)\ (i\ne j).
\tag{7.1}
$$

For each world use the six positive $T_{i,k}$ in (2.2), and define

$$
\alpha_{i,0}=-d_i/T_{i,0},\quad
\alpha_{i,1}=(24-d_i)/T_{i,1},\quad
\alpha_{i,2}=(48-d_i)/T_{i,2},\quad
\alpha_{i,3}=(312/5-d_i)/T_{i,3}.
\tag{7.2}
$$

The four Lagrange polynomials and the gain are exactly

$$
\begin{aligned}
\ell_0(T)&=-(T-1)(T-2)(T-3)/6,\\
\ell_1(T)&=T(T-2)(T-3)/2,\\
\ell_2(T)&=-T(T-1)(T-3)/2,\\
\ell_3(T)&=T(T-1)(T-2)/6,\\
F_i(T)&=\sum_{j=0}^3\alpha_{i,j}\ell_j(T).
\end{aligned}
\tag{7.3}
$$

For a sample vector $(\alpha_0,\alpha_1,\alpha_2,\alpha_3)$,
the entire increasing-power coefficient vector of this interpolant is

$$
\left(
\alpha_0,
-\frac{11}6\alpha_0+3\alpha_1-\frac32\alpha_2+\frac13\alpha_3,
\alpha_0-\frac52\alpha_1+2\alpha_2-\frac12\alpha_3,
-\frac16\alpha_0+\frac12\alpha_1-\frac12\alpha_2+\frac16\alpha_3
\right).
\tag{7.4}
$$

The four complete evaluation rows are

$$
\begin{pmatrix}F_i(4)\\F_i(5)\\F_i(6)\\F_i(7)\end{pmatrix}
=\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}\alpha_{i,0}\\\alpha_{i,1}\\\alpha_{i,2}\\\alpha_{i,3}\end{pmatrix}.
\tag{7.5}
$$

These identities follow by expanding the four products in (7.3)
and substituting the respective integer arguments; they specify
every coefficient and sample row. Retain both actual late equations

$$
d_i+F_i(4)T_{i,4}=\widehat Y,\qquad
d_i+F_i(5)T_{i,5}=\widehat z
\quad(i=1,2,3),
\tag{7.6}
$$

and put $h_i=F_i(6)$, $t_i=F_i(7)$, requiring $t_i\ne0$.
The $h_i$ remain unrestricted unless a stated case adds a promise.
The polynomial is nonzero: if all of $F_i$ vanished, its first
four equations would require the distinct readings
$0,24,48,312/5$ all to equal $d_i$. Thus no extra leading-degree,
sign, sampled-root or multiplicity condition is needed.

Form $R_i$ by (2.1) and recover the original complete worlds by

$$
P_i=R_i/T_{i,0},\quad f_i=T_{i,0}F_i,\quad
g_i=\lambda T_{i,0}F_i,\quad
\delta_i=D_0+\lambda d_i.
\tag{7.7}
$$

Equations (7.1)–(7.7) are necessary and sufficient for three
distinct legal worlds of the terminal-nonzero stratum on the
one fixed ancestor (1.3). Necessity is Lemma 2.1 and interpolation.
For sufficiency, (2.1) gives strictly positive rank-one sources,
positive $T_{i,0}$ gives trace-one normalization, (7.3) supplies
the first four equations, and (7.6) supplies exactly the remaining
two. The gain is nonzero and of degree at most three, and
$t_i\ne0$ gives the required terminal stratum. The chart and
the first four equations show that equal $(x_i,y_i,d_i)$ give
the same world; its converse follows from chart uniqueness.
Thus (7.1) is precisely complete-world distinctness. All claims
hold for both signs of the same $\lambda$.

Define $U_i,V_i,A_i,B_i,C_i,D_i$ by (2.5)–(2.6) on those
same worlds. For any scalar column $S$ write

$$
\Delta(S)=(S_1-S_2)(S_1-S_3)(S_2-S_3).
\tag{7.8}
$$

Then $\Delta(S)=0$ means that some pair collides; it also allows
a shared-three value.

**Proposition 7.2 (PP/PT/TP/TT, with necessity and sufficiency).**
Subject to every condition (7.1)–(7.7), the triple has $L_2$
if and only if, after relabeling worlds, one of these systems holds:

| Pattern | Sixth conditions | Terminal conditions |
| --- | --- | --- |
| PP | $U_1=U_2\ne U_3$; $V_1=V_3\ne V_2$ | $A_1=A_2$, $B_1=B_2$, $C_1=C_3$, $D_1=D_3$ |
| PT | $U_1=U_2\ne U_3$; $V_1=V_2=V_3$ | $A_1=A_2$, $B_1=B_2$, $\Delta(C)=\Delta(D)=0$ |
| TP | $U_1=U_2=U_3$; $V_1=V_2\ne V_3$ | $C_1=C_2$, $D_1=D_2$, $\Delta(A)=\Delta(B)=0$ |
| TT | $U_1=U_2=U_3$; $V_1=V_2=V_3$ | $\Delta(A)=\Delta(B)=\Delta(C)=\Delta(D)=0$ |

The two actions are not interchanged: $A,B$ always belong to a
sixth-$J$ child and $C,D$ to a sixth-$M$ child.

Proof of necessity. A sixth child witnessing $L_1$ has size two
or three. Size two is the unique proper colliding pair and must
agree in both branch terminal columns. Size three is precisely
a shared-three sixth response, and each of the branch's two
terminal columns must be noninjective on that whole triple.
If both sixth children are proper, their pairs differ by Lemma
2.3. These are exactly the four listed alternatives after
relabeling, and none changes the fixed ancestor.

Proof of sufficiency and the raw witnesses. In PP, sixth $J$
and the raw response $D_0+\lambda U_1$ retain exactly
$\{W_1,W_2\}$. Last $J$ and response $D_0+\lambda A_1$
retain that pair; last $M$ and response $D_0+\lambda B_1$
also retain it. Thus this actual sixth child has $L_1$.
Sixth $M$ and raw $D_0+\lambda V_1$ retain exactly
$\{W_1,W_3\}$, whose last-$J$ and last-$M$ witnesses are
$D_0+\lambda C_1$ and $D_0+\lambda D_1$. This proves both
action conjuncts of $L_2$ on the same triple.

In PT the $J$ child and its last responses are exactly that
proper-pair construction. Sixth $M$ with the common raw response
$D_0+\lambda V_1$ retains the whole triple. A pair supplied by
$\Delta(C)=0$ supplies a last-$J$ raw response retaining at
least two members, and a pair supplied by $\Delta(D)=0$
supplies a last-$M$ raw response retaining at least two.
The pairs may differ, and both witnesses make the whole-three
child satisfy $L_1$.

In TP, sixth $J$ with the common raw response
$D_0+\lambda U_1$ retains the whole triple. The collisions in
$A$ and $B$ supply its two last-action witnesses, with raw values
$D_0+\lambda A_i$ and $D_0+\lambda B_j$ for members of the
respective colliding pairs. Sixth $M$ and raw
$D_0+\lambda V_1$ retain exactly $\{W_1,W_2\}$, which survives
last $J$ at raw $D_0+\lambda C_1$ and last $M$ at raw
$D_0+\lambda D_1$.

In TT, either sixth action's common raw response retains all
three. For each branch, its two specified zero collision products
supply the two last-action raw response witnesses. These four
terminal pairs need not agree. Again both sixth children have
$L_1$, so the same triple has $L_2$.

For completeness, every real raw response defines its actual
retained child by intersection with the extended history. Children
of size zero or one fail the requisite cardinality clause. A
two-world child can satisfy $L_1$ only by retaining that same
pair under both last actions. A three-world child permits different
last-action pairs, exactly as the collision products express.
The bijection $w\mapsto D_0+\lambda w$ preserves all these
quantifiers even for $\lambda<0$. Predictions or witnesses for
unchosen actions are never acquired as extra observations. ∎

**Corollary 7.3 (precise remaining common-drift alternatives).**
An $L_2$ triple in the terminal-nonzero stratum with common drift
must lie in one of the following two unresolved systems:

1. Every sixth gain is zero. Then $U_i=V_i=d$, so the remaining
   template is TT, with all terminal gains still nonzero.
2. Every sixth gain is nonzero, with a common sign. Then the
   template is PP with different proper pairs, the terminal gains
   have a common sign, and at least two of the ratios
   $g_i(6)/g_i(7)$ differ.

Proof. The sixth-sign claim, including its zero case, is Theorem
5.1. Its nonzero case excludes PT, TP and TT and gives PP;
Theorem 3.1 gives the terminal sign, and Theorem 6.1 excludes
one common nonzero ratio. In the zero case (2.5) gives the TT
sixth conditions directly. No feasibility assertion follows in
either direction. ∎

For arbitrary drifts, Theorem 3.1 excludes mixed-terminal-sign
PP systems. Such mixed-sign triples, if they exist, must use PT,
TP or TT. All variable-drift residual systems still require
simultaneous solution of (7.1)–(7.7) and their terminal
conditions; marginal pair constructions would not suffice.

## 8. Permanent source correspondence and unresolved scope

| Permanent source | Established interface and exact scope here |
| --- | --- |
| [VII, Definitions 1.1–1.3; proof of Theorem 4.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md) | Original-clock complete worlds, the full literal $JMMJM$ ancestor, positive $Q$ chart, and four-terminal rank-one reconstruction. The reconstruction is credited there to V, Theorem 7.1. Lemmas 2.1 and 2.3 supply the needed full algebra here; these interfaces are established project results, not new general mathematics. |
| VII, Sections 2–5 | The fixed-drift double-terminal-root rigidity, full rational same-sum minor certificate and arbitrary-drift two-world $L_2$ exclusion retain their own domains. The nine coefficient matrices and tensor Bernstein identities are not hypotheses for the five-ratio or diagonal-swap arguments here. The larger-family conclusion is not inferred from pair exclusion. |
| VII, Section 6 | The whole known common-$b,d_6$ class inverse belongs to its separate literal $MMJM$ history. Its known common predictions, nonzero-$\omega$ or stated non-diagonal zero-layer promises are not inferred on (1.3). |
| VII, Sections 8–11 | The proportional-gain exclusion on the exact $H_*$ fiber, its distinct-reading negative-discriminant extension, the exhaustive $u=1$ two-world slice including the remote algebraic target, the local response inverses and the no-escape whole-band inverse remain established deductions with those exact history and known-source-band restrictions. They do not make the unrestricted fiber a common-gain-ray or known-band class. |
| [VIII, Theorem 2.1 and Corollary 3.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md) | The entire known initial-root $JMMJM$ class has its supplied decoder, without a cardinality bound. The root promise is equivalent to $\delta=D_0$ at this history and remains prior information. It is not an assumption in Theorems 3.1–6.1. |
| VIII, Proposition 3.2; Theorem 4.2 and Corollary 4.3 | The actual nonterminal-root consumer and the exact mixed-drift continuous six-reading $H^*$ fiber retain their existing proofs and scopes. That continuous fiber alone neither establishes $L_2$ nor certifies an initial-root label or drift from six readings. No generic implicit-function result or local fiber reparametrization is claimed as new content here. |

The source-relative deductions of this volume are the arbitrary-drift
proper-pair terminal-sign restriction, the five strict ratio identities
and full-ancestor exchanged-source contradiction, the fixed injective
terminal coordinate for at most three common-prediction candidates,
the common-drift sixth-sign and shared-three exclusions, and the
positive rank-one diagonal-swap obstruction to a common nonzero future
ratio. Polynomial interpolation, root counting, elementary matrix
algebra, monotone scalar ratios and finite pigeonhole arguments are
standard tools used within these model-specific deductions. Section
7 specifies open systems rather than adding an independent novelty
claim. No worldwide priority or literature-completeness assertion is
made.

The all-sixth-zero TT case in Corollary 7.3 has terminal gains
nonzero. It is distinct from an all-terminal-root core, which is
not settled here. The varying-ratio PP case at common drift is
also unresolved. Arbitrary-drift strata retain the residual PP,
PT, TP and TT possibilities described above. No actual losing
triple is supplied, and no uniform exclusion of the unrestricted
terminal-nonzero stratum is asserted. The other terminal-root-count
strata, full actual fibers, and larger or infinite losing families
remain outside the finite-set conclusions.

Common drift, common sixth predictions, common future ratio and
source-domain restrictions are explicit promises where used. None
is inferred from the six observations. The fixed-coordinate policy
of Corollary 4.2 concerns one entire known set of at most three
candidates. The ratio policy of Corollary 6.2 also has that cardinality
bound. Neither is a policy on an unrestricted union or on an arbitrary
infinite common-prediction class. In particular a larger losing
family need not contain a losing triple.

At the earlier $JMMJ$ parent, a losing actual $JMMJM$ child would
still have to be joined with losing children of the other action
on the same fixed ancestors. At the separate $MMJM$ parent the
unrestricted four-target and larger $L_3$ question and the whole-fiber
three-further-reading inverse remain unresolved. The simultaneous
local and original-root systems referred to in VII and VIII retain
their own unresolved feasibility obligations.

The full original-root alternative remains
$n_{\mathrm{det}}(3,0)\ge9$ versus a lawful complete-target decoder
on all of $\mathcal W_3$ with at most eight total readings. It
includes both initial actions, every actual history and early stop,
arbitrary constant drifts, all positive nonsymmetric rank-one
trace-one sources and all nonzero cubic-or-lower gains with every
sign, sampled root and multiplicity. The present deductions supply
neither original-root alternative. They make no kernel or Lean
verification, empirical, general neural-network, stability,
efficiency, computational-resource or cost claim.
