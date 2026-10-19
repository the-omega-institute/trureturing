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

## 9. Common-drift actual-J pair exclusion without a ratio promise

All definitions in Sections 1–2 remain in force, with the entire fixed
history (1.3), including both late readings. In this section the letters
used for local positive coordinates are separate from the chart in
Lemma 2.1. No sixth-gain nonvanishing is assumed.

**Theorem 9.1 (the actual-J pair map).** On
$\mathcal F^{\ne0}_7(H)$ at each fixed arbitrary normalized drift $d$,
the map $W\mapsto(U,A,B)$ is injective. Thus two distinct worlds with
this common drift cannot form a losing two-world actual sixth-$J$
child. Their future ratios and entire gain shapes may differ.

Proof. Suppose two worlds agree in $U,A,B$. In (2.7) their matrices
$X_i$ have the same nonzero upper-right entry $b=B-A$. All entries
of each $X_i$ have the sign of $b$. Therefore $Z_i=X_i/b$ is strictly
positive, even for $b<0$. Put $m_i=(Z_i)_{22}$. The common $A$ gives
a common $S=\operatorname{tr}Z_i=(A-d)/b$, and rank one gives

$$
Z_i=\begin{pmatrix}S-m_i&1\\c_i&m_i\end{pmatrix},\qquad
c_i=m_i(S-m_i),\quad 2<m_i<3,\quad S>m_i.
\tag{9.1}
$$

Indeed $b/e\in(1/3,1/2)$ gives $2<m_i<3$, and explicitly

$$
Q^{-1}Z_i=
\begin{pmatrix}
(m_i-2)(S-m_i)&m_i-2\\
(3-m_i)(S-m_i)&3-m_i
\end{pmatrix}>0.
\tag{9.2}
$$

Let $L_{i,k}=\operatorname{tr}(A_kQ^{-1}Z_i)>0$,
$a_i=L_{i,0}$ and $\kappa_i=f_i/a_i$. Then
$P_i=Q^{-1}Z_i/a_i$, $\kappa_i(7)=b$, and the entire ancestor is
$d+\kappa_i(k)L_{i,k}=(0,24,48,312/5,\widehat Y,\widehat z)_k$.
The six trace forms, obtained from (9.2), are

$$
(L_{i,0},\ldots,L_{i,5})=
(c_i-2S+m_i+3,\ 3S-2m_i-c_i-2,\ c_i-2S+2m_i+1,
 S-1,\ c_i-S+m_i+1,\ S).
\tag{9.3}
$$

In particular $L_{i,3}=L_{i,1}+L_{i,2}=S-1$ and $L_{i,5}=S$.
The common actual readings at three and five force agreement of
$\kappa_1,\kappa_2$ at those clocks; they also agree at seven.
Writing $\epsilon=\kappa_1(6)-\kappa_2(6)$, factorization gives

$$
\kappa_1(T)-\kappa_2(T)
 =-\frac\epsilon3(T-3)(T-5)(T-7).
\tag{9.4}
$$

Its values at $0,1,2,4$ are $35\epsilon,16\epsilon,5\epsilon,
-\epsilon$. Put $\Delta m=m_1-m_2$, $\Delta c=c_1-c_2$,
$v=\Delta c+2\Delta m$ and $w=\Delta c+\Delta m$. Then
$\Delta L_0=\Delta L_4=w$, $\Delta L_1=-v$, $\Delta L_2=v$.

First let $\epsilon=0$, so both polynomials equal $\kappa$.
At least one of $\kappa(1),\kappa(2)$ is nonzero, since the
corresponding actual readings 24 and 48 differ. Subtracting the
ancestor equations gives $v=0$. If $\kappa(6)\ne0$, shared $U$
gives $\Delta c=0$, hence $\Delta m=0$. If $\kappa(6)=0$ but
one of $\kappa(0),\kappa(4)$ is nonzero, the corresponding
ancestor equation gives $w=0$, again forcing $\Delta m=\Delta c=0$.
The remaining case has roots zero, four and six, and

$$
\kappa(T)=C T(T-4)(T-6),\quad C\ne0,\qquad d=\widehat Y=0.
\tag{9.5}
$$

Its values at one, two and three are $15C,16C,9C$. The identity
$L_3=L_1+L_2$, multiplied by $9C$, now forces

$$
312/5=9\left(24/15+48/16\right)=207/5,
\tag{9.6}
$$

a contradiction. Thus the zero-difference branch either makes the
matrices equal or is impossible, including when both sixth gains vanish.

Suppose now $\epsilon\ne0$. Subtracting the samples expressed
through their positive trace factors gives

$$
16\epsilon=\frac{(24-d)v}{L_{1,1}L_{2,1}},\qquad
5\epsilon=-\frac{(48-d)v}{L_{1,2}L_{2,2}},\qquad
35\epsilon=\frac{dw}{L_{1,0}L_{2,0}}.
\tag{9.7}
$$

Hence $v\ne0$, $24<d<48$ and $wv<0$. The rank-one relation is
$\Delta c=\Delta m(S-m_1-m_2)$, so $\Delta m\ne0$ and
$-2<S-m_1-m_2<-1$. Exchanging the same two worlds if necessary, set

$$
m_1=x+2,\quad m_2=y+2,\quad \rho=S-m_1-m_2+2,
\qquad 0<x<y<1,\quad 0<\rho<1.
\tag{9.8}
$$

Consequently their matrices are exactly

$$
Z_1=\begin{pmatrix}y+\rho&1\\(x+2)(y+\rho)&x+2\end{pmatrix},
\qquad
Z_2=\begin{pmatrix}x+\rho&1\\(y+2)(x+\rho)&y+2\end{pmatrix}.
\tag{9.9}
$$

Define the following strictly positive quantities:

$$
\begin{aligned}
a&=1-x+x(y+\rho),&j&=x+(1-x)(y+\rho),\\
j'&=y+(1-y)(x+\rho),&l&=1+x(y+\rho),\\
l'&=1+y(x+\rho),&k&=1+x+y+\rho,\\
D'&=1+(y+2)(x+\rho).
\end{aligned}
\tag{9.10}
$$

Here $a,j,l,k$ are the first world's traces at zero, one, two,
three, and $j',l'$ are the second world's corresponding traces.
Put $\beta=48-d>0$ and $r_*=d/\beta$. The first two equations
of (9.7) give

$$
r_*=1+\frac{32jj'}{5ll'},\qquad
\epsilon=-\frac{\beta\rho(x-y)}{5ll'},\qquad
\Delta c=-(2-\rho)(x-y).
\tag{9.11}
$$

The shared actual sixth-$J$ reading says
$\kappa_1(6)(1+c_1)=\kappa_2(6)(1+c_2)$. Thus
$\kappa_1(6)\Delta c=-\epsilon(1+c_2)$ and

$$
\frac{\kappa_1(6)}\beta
 =-\frac{\rho D'}{5(2-\rho)ll'}.
\tag{9.12}
$$

On the other hand the clock-six interpolation row (7.5) applied
to $\kappa_1$ gives

$$
\frac{\kappa_1(6)}\beta
 =\frac{10r_*}a+\frac{18(1-r_*)}j-\frac{45}l
                  +\frac{26+6r_*}k.
\tag{9.13}
$$

For its last term, $20(312/5-d)/\beta=26+6r_*$;
for its second, $(24-d)/\beta=(1-r_*)/2$.
In particular the actual clock-three value has not been replaced.
Equations (9.12)–(9.13) require $E=0$, where

$$
E=\frac{10r_*}a+\frac{18(1-r_*)}j-\frac{45}l
 +\frac{26+6r_*}k+\frac{\rho D'}{5(2-\rho)ll'}.
\tag{9.14}
$$

Substituting (9.11) and clearing positive factors gives the entire
polynomial identity

$$
\begin{aligned}
N&=5ak(2-\rho)ll'E\\
 &=50k(2-\rho)ll'+320k(2-\rho)jj'
   -576ak(2-\rho)j'-225ak(2-\rho)l'\\
 &\hspace{1em}+160a(2-\rho)ll'+192a(2-\rho)jj'+ak\rho D'.
\end{aligned}
\tag{9.15}
$$

Here is a complete integer certificate for the required strict sign.
Set $y=x+(1-x)s$, so $0<s<1$. With the definitions (9.10),

$$
-N(x,x+(1-x)s,\rho)=
 \sum_{i=0}^{6}\sum_{j_0=0}^{3}\sum_{h=0}^{4}
 C_{i,j_0,h}\,x^i(1-x)^{6-i}s^{j_0}(1-s)^{3-j_0}
                         \rho^h(1-\rho)^{4-h}.
\tag{9.16}
$$

The basis in this identity has no binomial prefactors. All 140
integers are given below; each row lists $h=0,1,2,3,4$.

| $i$ | $j_0$ | $C_{i,j_0,0}$ | $C_{i,j_0,1}$ | $C_{i,j_0,2}$ | $C_{i,j_0,3}$ | $C_{i,j_0,4}$ |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 0 | 30 | 1606 | 4012 | 2620 | 504 |
| 0 | 1 | 1592 | 9208 | 14926 | 7966 | 1296 |
| 0 | 2 | 3222 | 12348 | 15426 | 6914 | 934 |
| 0 | 3 | 1020 | 3146 | 3232 | 1248 | 142 |
| 1 | 0 | 3054 | 17190 | 28876 | 17138 | 3292 |
| 1 | 1 | 14170 | 62506 | 90726 | 49934 | 9154 |
| 1 | 2 | 17830 | 68486 | 91160 | 49098 | 9132 |
| 1 | 3 | 6842 | 24480 | 32040 | 18344 | 3764 |
| 2 | 0 | 10716 | 46328 | 70196 | 44186 | 9608 |
| 2 | 1 | 35994 | 150248 | 227082 | 146194 | 32648 |
| 2 | 2 | 42416 | 175508 | 267520 | 176066 | 40184 |
| 2 | 3 | 18640 | 75944 | 115138 | 76006 | 17442 |
| 3 | 0 | 11570 | 51406 | 90702 | 71890 | 18860 |
| 3 | 1 | 41834 | 198042 | 356628 | 276946 | 71058 |
| 3 | 2 | 56674 | 269230 | 472694 | 352098 | 87516 |
| 3 | 3 | 26440 | 121576 | 204094 | 144868 | 34770 |
| 4 | 0 | 5778 | 40554 | 96212 | 88708 | 24884 |
| 4 | 1 | 30604 | 185512 | 388976 | 326542 | 86878 |
| 4 | 2 | 45426 | 251632 | 486138 | 381122 | 97162 |
| 4 | 3 | 20600 | 106674 | 193374 | 143288 | 35168 |
| 5 | 0 | 3976 | 31520 | 72610 | 62680 | 16804 |
| 5 | 1 | 16302 | 111912 | 239430 | 197124 | 51434 |
| 5 | 2 | 20676 | 129264 | 261030 | 206208 | 52456 |
| 5 | 3 | 8350 | 48872 | 94210 | 71764 | 17826 |
| 6 | 0 | 1372 | 9164 | 18600 | 14434 | 3608 |
| 6 | 1 | 4116 | 27492 | 55800 | 43302 | 10824 |
| 6 | 2 | 4116 | 27492 | 55800 | 43302 | 10824 |
| 6 | 3 | 1372 | 9164 | 18600 | 14434 | 3608 |

For an explicit algebraic interpretation of the certificate, expand
$-N(x,x+(1-x)s,\rho)=\sum p_{abc}x^as^b\rho^c$ using (9.10)
and (9.15). Its coordinate degrees are at most $(6,3,4)$.
The coefficients in (9.16) are exactly

$$
C_{i,j_0,h}=
\sum_{a\le i,\ b\le j_0,\ c\le h}
p_{abc}\binom{6-a}{i-a}\binom{3-b}{j_0-b}\binom{4-c}{h-c}.
\tag{9.17}
$$

This is a direct finite coefficient identity: in one variable
$X^a=\sum_{i=a}^n\binom{n-a}{i-a}X^i(1-X)^{n-i}$ by the
binomial theorem, and applying it in the three variables gives
(9.16)–(9.17) with precisely the displayed integers. Every integer
is strictly positive, and every basis factor is strictly positive
for $0<x,s,\rho<1$. Hence $-N>0$. Since the multiplier in
(9.15) is positive, this contradicts $E=0$.

The remaining possibility in the zero-difference branch was
$Z_1=Z_2$. It gives $a_1=a_2$ and $P_1=P_2$ by (9.2).
At the common drift the first four positive trace factors determine
the same four gain samples, hence the same entire polynomial and,
by (1.4), the same $(P,g,\delta)$. This proves the theorem.
No sixth gain, ancestor gain, leading coefficient or root separation
was divided out. The nonzero terminal gain is the explicit premise
that makes $b\ne0$; every later cancellation uses positive factors
or the established $x-y\ne0$. Lower degrees, repeated roots,
zero sixth gains and either sign of $\lambda$ are included. ∎

**Corollary 9.2 (PP exclusion and its finite-set consumer).** A
common-drift terminal-nonzero $L_2$ triple on $H$ has all three
sixth gains zero and is TT. In particular the common-drift PP
system of Proposition 7.2 is impossible without any restriction
on its future ratios. If a known $K\subseteq\mathcal F^{\ne0}_7(H)$
has at most three members, common drift, and at least one nonzero
sixth gain, it has a lawful two-further-reading complete-target policy.

Proof. A PP system supplies the same distinct actual-$J$ pair with
equal $U,A,B$, contradicting Theorem 9.1. Theorem 5.1 makes any
common-drift $L_2$ triple with one nonzero sixth gain entirely
nonzero-sixth and PP; hence only its all-zero TT alternative remains.
For two worlds $L_2$ would require the same pair to agree in all
four terminal columns, contrary to Lemma 2.3. Thus the stated known
$K$ fails $L_2$. When it has at least two members, choose the first
sixth action $E$ in the order $J,M$ whose every raw-response child
$K_{E,w}=K\cap\mathcal F(H,E,w)$ fails $L_1$. For each real $w$,
stop on a singleton, or choose the first terminal action $F_w$ in
the order $J,M$ injective on the entire nonsingleton child. Negating
(1.9) supplies these choices. For every real raw $w,v$,

$$
\left|K_{E,w}\cap\mathcal F(H,E,w,F_w,v)\right|\le1.
\tag{9.18}
$$

At a reachable response return its unique complete world. Empty
children are unreachable and admit arbitrary choices. Each selected
atom is immediately read; a known singleton may stop at once.
The total is at most eight readings on the original clocks. ∎

For unequal-drift triples Theorem 9.1 still excludes any PP or PT
actual-$J$ proper pair whose two drifts agree. It does not exclude
an unequal-drift pair or a shared-three $J$ child with different
terminal collision pairs. Theorem 9.1 includes zero sixth gains;
on that subdomain its $AB$ consequence is already the published
pair injection cited in Section 10. Its new exclusion here is the
broader nonzero-sixth, varying-ratio PP case.

## 10. Zero-sixth coordinates and the reused pair inverses

**Definition 10.1 (the entire sixth-root class).** Write
$y_4=\widehat Y$, $\zeta=\widehat z$ and

$$
\mathcal Z_6(d)=\{W\in\mathcal F(H):
 (\delta-D_0)/\lambda=d,\ f(6)=0\}.
\tag{10.1}
$$

This class also includes $f(7)=0$. Its terminal functions are the
same chronological responses as in (2.6), extended by their original
trace formulas without dividing by $f(7)$. In the trace-one source
coordinates (1.5), put $j=u+v$, $\ell=1+u>1$, $k=j/\ell>0$.
Then $u=\ell-1$, $v=(k-1)\ell+1$, and the six positive traces are

$$
(1,k\ell,\ell,(k+1)\ell,1+r+k\ell,(k+2)\ell-r).
\tag{10.2}
$$

**Lemma 10.2 (sixth-root identities).** Define

$$
\begin{aligned}
N_d(k)&=(2160-45d)k^2+(48+11d)k+36d-864,\\
p_4(k,d)&=\frac{3d-144}{2}k^2+\frac{624-9d}{10}k
                                      +\frac{48-2d}{5},\\
p_5(k,d)&=2(d-48)k^2+\frac{216-3d}{5}k+\frac{72-3d}{5},\\
p_7(k,d)&=6(48-d)k^2+(d-72)k+2d-48.
\end{aligned}
\tag{10.3}
$$

Every world of $\mathcal Z_6(d)$ satisfies

$$
10d\ell k(k+1)=N_d(k),\qquad
f(i)=\frac{p_i(k,d)}{\ell k(k+1)}\quad(i=4,5,7).
\tag{10.4}
$$

Proof. Its samples at zero through three are
$-d,(24-d)/(k\ell),(48-d)/\ell,(312/5-d)/((k+1)\ell)$.
The clock-six row of (7.5) is zero; clearing the positive
$\ell k(k+1)$ gives the first identity. Subtract respectively
$1/10,2/5,2$ times that zero row from the rows for clocks four,
five and seven. Their coefficient rows become respectively
$(0,2/5,-3/2,2)$, $(0,3/5,-2,2)$ and $(0,-2,6,-5)$.
Substituting the three samples and collecting powers of $k$ gives
all three polynomials in (10.3). No degree-exactness assumption or
sampled-gain cancellation occurs. ∎

**Reused whole-class pair injection and its coordinate inverse.**
[Zero-Sixth Pairs, Theorem 4.1](FIB_JMMJM_ZERO_SIXTH_PAIR_INJECTIVITY_AND_JOINT_COLLISION_OBSTRUCTIONS.md)
already proves that both $(A,B)$ and $(A,D)$ are injective on
the entire $\mathcal Z_6(d)\cap\mathcal F^{\ne0}_7(H)$ for every
real $d$ and every fixed pair of late readings. These are reused
results, with no cardinality, common-shape or common-source-sum
restriction. The following gives the $AB$ inverse explicitly in
the coordinates (10.2); it is not a new pair-injectivity claim.

Since $A-d=f(7)((k+2)\ell-r)\ne0$, put

$$
L_*=2A-B-d=f(7)(k+1)\ell\ne0,\qquad
m_*=(\zeta-d)/(A-d)=f(5)/f(7).
\tag{10.5}
$$

Here $B-A=f(7)(\ell-r)$ by the trace of $MJQP$.
Equations (10.4) give $L_*=p_7/k$, $m_*L_*=p_5/k$.
The complete coefficient identity is

$$
3p_5+p_7=\frac{4(72-d)k+d-24}{5}.
\tag{10.6}
$$

For $d\ne24$ it gives

$$
k=\frac{d-24}{5(3m_*+1)L_*-4(72-d)},\qquad
5(3m_*+1)L_*-4(72-d)=\frac{d-24}{k}\ne0.
\tag{10.7}
$$

For $d=24$, use instead $p_7/k=144k-48$, hence
$k=(L_*+48)/144$. When $d\ne0$, recover
$\ell=N_d(k)/(10dk(k+1))$, compute $f(7)$ by (10.4), and set

$$
r=(k+2)\ell-\frac{A-d}{f(7)}.
\tag{10.8}
$$

Then recover $u,v$ and interpolate the first four gain samples.
The $d=0$ stratum is recovered from the ancestor alone by Lemma
11.1 below. In (10.5) $m_*=0$ is permitted: no division by the
fifth gain occurs. Neither $d-48$ nor a leading coefficient nor
a root separation is a divisor. These formulas recover the whole
$(P,g,\delta)$ through (1.4); on legal inputs all remaining
ancestor equations and determinant constraints hold by membership.
They do not assert legality for arbitrary supplied scalar values.
The pair inverse does not physically acquire both alternative
terminal coordinates on one trajectory.

## 11. Scalar terminal injection on the safe drift ranges

**Lemma 11.1 (zero drift and late-zero strata).** The class
$\mathcal Z_6(0)$ has at most one member. At every arbitrary real
$d$, if $y_4=d$ or $\zeta=d$, then $|\mathcal Z_6(d)|\le2$.
There is no legal world on $H$ with roots four, five and six.

Proof. At $d=0$, (10.4) becomes $45k^2+k-18=0$. This quadratic
is strictly increasing for $k>0$, is negative at $3/5$ and positive
at $2/3$ (the values are $-6/5,8/3$), so has a unique positive
root $\kappa\in(3/5,2/3)$. Reduction modulo this quadratic gives

$$
p_4(\kappa,0)=64\kappa-96/5>0,\qquad
p_5(\kappa,0)=(136/3)\kappa-24>0.
\tag{11.1}
$$

Put $c_i=p_i(\kappa,0)/(\kappa(\kappa+1))>0$ for $i=4,5$,
and $w_*=r/\ell$. Both actual late equations become

$$
\zeta/c_5=\kappa+2-w_*,\qquad
y_4/c_4=\kappa+w_*+1/\ell.
\tag{11.2}
$$

They fix $w_*$ and then $1/\ell=y_4/c_4-\kappa-w_*$,
which is positive on every legal candidate. Thus they fix
$\ell,r,u,v$, and the first four samples fix the entire gain.
This proves uniqueness without a terminal reading, and also shows
that neither late reading can equal zero on this stratum.

If four, five and six were roots, degree at most three and a nonzero
gain would force $f(T)=a(T-4)(T-5)(T-6)$, $a=d/120\ne0$.
Clocks one, two and three then give

$$
j=\frac{2(d-24)}d,\qquad
\ell=\frac{5(d-48)}d,\qquad
j+\ell=\frac{20(d-312/5)}d.
\tag{11.3}
$$

Consequently $d=960/13$, $j=27/20$, $\ell=7/4$, and
$uv=(\ell-1)(j-\ell+1)=9/20>1/4$, contradicting
$uv=r(1-r)\le1/4$. Lower degrees cannot have those three roots.

Now take $d\ne0$. If $\zeta=d$, positivity of the fifth trace
gives $f(5)=0$, hence $p_5(k,d)=0$. This is a nonzero polynomial
of degree at most two: its quadratic coefficient vanishes only
at $d=48$, where $p_5=(72/5)(k-1)$ remains nonzero.
There are at most two positive roots, counted without multiplicity.
Each fixes $\ell$ by (10.4); the exclusion just proved gives
$f(4)\ne0$, so the actual fourth equation fixes
$r=(y_4-d)/f(4)-1-k\ell$. Thus each root supplies at most one
world. If $y_4=d$, use instead $p_4(k,d)=0$ and the nonzero
fifth sample to fix $r=(k+2)\ell-(\zeta-d)/f(5)$.
The polynomial $p_4$ also has degree at most two and is nonzero
for all $d$: at its only quadratic degree drop $d=48$ it is
$(48/5)(2k-1)$. The simultaneous late-zero case is empty by
(11.3). Repeated polynomial roots reduce these cardinalities.
Together with the already settled $d=0$ case this proves the lemma. ∎

**Theorem 11.2 (whole-class scalar $A$ injection).** Define

$$
\mathcal S=(-\infty,24]\ \cup\ [48,72]\ \cup\ [96,\infty).
\tag{11.4}
$$

For every $d\in\mathcal S$, $A$ is injective on the entire
$\mathcal Z_6(d)$, including terminal-zero worlds and arbitrary
cardinality. The endpoints refer to normalized $d$ for either
sign of $\lambda$.

Proof. First suppose $\zeta\ne d$. Since the fifth trace in
(10.2) is positive, $f(5)\ne0$ and
$\operatorname{sgn}p_5=\operatorname{sgn}(\zeta-d)$.
The repeated cumulative matrix $Q$ at clock seven after $JJ$ gives

$$
A-d=(\zeta-d)\frac{f(7)}{f(5)}
     =(\zeta-d)\frac{p_7(k,d)}{p_5(k,d)}.
\tag{11.5}
$$

There is no restriction on $f(7)$ in this identity. Direct
differentiation gives the full numerator and its discriminant:

$$
\begin{aligned}
\left(\frac{p_7}{p_5}\right)'&=\frac{Q_d(k)}{5p_5^2},\\
Q_d(k)&=8(d-48)(d-72)k^2-4(d-24)(d-48)k
                           +3(d-24)(d-72),\\
\operatorname{disc}_k Q_d
 &=-80(d-24)(d-48)(d-312/5)(d-96).
\end{aligned}
\tag{11.6}
$$

For $d<24$ or $d>96$, its leading coefficient is positive and
its discriminant negative, so $Q_d>0$ for all real $k$.
At $d=24$ it is $9216k^2>0$ for $k>0$.
For $48\le d\le72$ every coefficient is nonpositive and at
least one term is strictly negative for $k>0$; explicitly
$Q_{48}=-1728$ and $Q_{72}=-4608k$. At $d=96$,

$$
Q_{96}=576(4k-3)^2,\qquad
p_5(k,96)=\frac{24}{5}(4k-3)(5k+3).
\tag{11.7}
$$

Its sole stationary point $k=3/4$ is therefore excluded when
$p_5\ne0$. These facts give a strict derivative sign wherever
the fixed nonzero sign of $p_5$ is legal in (11.5).

To obtain global, rather than merely local, injectivity, consider
the whole positive $k$ axis. For $d<24$, $p_5$ has negative
quadratic coefficient and positive constant, so has exactly one
positive root and one negative root. For $48<d\le72$ or
$d\ge96$, it has positive quadratic coefficient and negative
constant, again exactly one positive root. The opposite signs of
the product also ensure real distinct roots. The remaining endpoint
polynomials are

$$
p_5(k,24)=-\frac{48}{5}k(5k-3),\qquad
p_5(k,48)=\frac{72}{5}(k-1).
\tag{11.8}
$$

In each case exactly one root lies in $k>0$, is simple there,
and each prescribed nonzero sign of $p_5$ selects exactly one
interval. Every legal candidate for the same actual $\zeta$ lies
in that same interval. The derivative sign in (11.6) is strict
throughout the interval, including the endpoint drift 96 by
(11.7), so $p_7/p_5$ is strictly monotone on it. Any disconnected
subsets caused by the other source or ancestor constraints remain
inside this one monotonicity interval. Hence equal $A$ forces equal
$k$, even if either terminal gain is zero.

For $d\ne0$, (10.4) fixes $\ell$; its fifth sample and the
actual fifth equation fix $r$. Thus $u,v$ and $P$ are fixed.
The first four positive trace factors fix all four gain samples;
Lagrange interpolation fixes the full polynomial. This gives the
entire original target by (1.4). The $d=0$ stratum is already
unique by Lemma 11.1, without dividing by $d$.

It remains to include $\zeta=d$. At $d=0$ there is no such world.
For $d\in\mathcal S\setminus\{0\}$ the preceding root count
shows that $p_5$ has exactly one positive root. It fixes $\ell$,
and $f(4)\ne0$ by Lemma 11.1, so the actual fourth equation
fixes $r$. Thus this entire class has at most one world, which
makes $A$ injective, including when its terminal gain vanishes.
The case $y_4=d$, $\zeta\ne d$ was already included in (11.5).
Both late-zero cases and all endpoint and degree-drop cases have
now been covered. The proof divides only by positive traces,
$\ell k(k+1)$, the nonzero $d$ on its stated stratum, and the
particular late sample proved nonzero before use. It imposes no
restriction on the sign, other roots or multiplicities of the gain. ∎

**Corollary 11.3 (an actual $JJ$ decoder on a known union).** For
any known set

$$
K\subseteq\bigcup_{d\in\mathcal S}\mathcal Z_6(d),
\tag{11.9}
$$

with no cardinality bound, the fixed continuation $JJ$ recovers
the complete target using at most eight total original-clock
readings. In particular $\neg L_2(K,H)$.

Proof. Execute sixth $J$ and immediately read raw $w$.
The sixth-root promise makes $w=\delta$, so for every real $w$
its actual child is exactly

$$
K_{J,w}=
\begin{cases}
K\cap\mathcal Z_6((w-D_0)/\lambda),&(w-D_0)/\lambda\in\mathcal S,\\
\varnothing,&(w-D_0)/\lambda\notin\mathcal S.
\end{cases}
\tag{11.10}
$$

Execute seventh $J$ and immediately read raw $v$. Theorem 11.2
is injective on the whole retained class, so for every real $w,v$

$$
\left|K_{J,w}\cap\mathcal F(H,J,w,J,v)\right|\le1.
\tag{11.11}
$$

At reachable responses membership supplies the unique world, and
returning it recovers $(P,g,\delta)$. Reconstruction uses the
unique $k$ in the monotonicity interval and the formulas in the
proof, or the zero-drift or zero-fifth alternatives of Lemma 11.1.
All actual ancestor equations and source constraints remain required;
existence follows from membership, not from arbitrary inverse inputs.
Singletons may stop earlier; empty responses are unreachable.
The six ancestor readings plus the two immediate readings total
eight. The prior sixth-root promise has not been inferred on an
unrestricted fiber; within that promised class the actual sixth
read does identify its drift. No unchosen response is acquired. ∎

## 12. The localized TT system and its remaining collision patterns

**Corollary 12.1 (remaining common-drift terminal-nonzero triples).**
If three distinct worlds $K\subseteq\mathcal F^{\ne0}_7(H)$
have common drift and $L_2(K,H)$, then necessarily

$$
\begin{gathered}
f_i(6)=0,\quad f_i'(6)\ne0\quad(i=1,2,3),\\
d\in(24,48)\cup(72,96),\qquad d\ne y_4,\zeta,\\
\Delta(A)=\Delta(B)=\Delta(C)=\Delta(D)=0.
\end{gathered}
\tag{12.1}
$$

Their normalized terminal gains have one common sign. The whole
system (7.1)–(7.7) and both late readings still hold on these same
fixed worlds. Its only remaining sixth template is TT.

Proof. Corollary 9.2 forces all sixth gains zero. The scalar
injection and actual decoder of Theorem 11.2 and Corollary 11.3
exclude $d\in\mathcal S$. Lemma 11.1 excludes $d=y_4$ or
$d=\zeta$, since either gives at most two worlds. Proposition 7.2
then supplies exactly the TT collision products. The repeated-sixth
root ranges in
[Zero-Sixth Geometry, Theorem 2.1](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
are $d<0$, $0<d<24$, or $48<d<312/5$. Both surviving windows
are disjoint from them, so every sixth root is simple. Its
Theorem 6.1, or Zero-Sixth Pairs, Section 6, gives the common
terminal sign on this same triple. No condition here proves
existence. ∎

**Corollary 12.2 (intersection with the published pattern obstructions).**
Under Corollary 12.1, the $AB$ and $AD$ repeated collision pairs
are impossible by the entire-class injections of Zero-Sixth Pairs,
Theorem 4.1. Its Theorem 6.2 leaves exactly the following necessary
pattern alternatives:

1. A constant column can only be $C$; the proper columns $A,B,D$
   use three different pairs.
2. With no constant column and pair counts $(2,2,0)$, only
   $AC\mid BD$ remains, with different pairs for its two blocks.
3. With no constant column and counts $(2,1,1)$, the repeated
   subset is one of $AC,BC,BD,CD$.

Every configuration containing an $AC$ pair additionally requires

$$
24<d<48,\qquad y_4>d.
\tag{12.2}
$$

In particular for $72<d<96$ only alternative 3 with repeated
subset $BC,BD$ or $CD$ can remain.

Proof. The published pattern theorem applies to exactly
$\mathcal Z_6(d)\cap\mathcal F^{\ne0}_7(H)$, without a
cardinality restriction on its pair injections and with its stated
three-world hypothesis for the pattern list. Thus it applies to
this same triple. Its strict $AC$ theorem (Theorem 5.1) requires
either $0<d<24$, $y_4<d$, $\zeta<d$, or $24<d<48$, $y_4>d$.
Intersecting with (12.1) removes the first alternative and gives
(12.2). The pattern alternatives containing $AC$ are precisely
constant $C$, $AC\mid BD$, and the $AC$ repeat in type $(2,1,1)$.
The other three repeat types acquire no additional $AC$ restriction.
These are intersections of necessary conditions on one common class,
not new pair-injectivity proofs or sufficient realizations. ∎

Consequently the remaining common-drift terminal-nonzero triple
question is the simultaneous solvability of (7.1)–(7.7) with
$d_i=d$, $h_i=0$ and all four products (7.8) zero, localized by
(12.1) and the patterns above. Equivalently one may retain the
source-graph system of Zero-Sixth Pairs, Proposition 7.1, with
these additional necessary restrictions. No gains, late readings,
pair witnesses or extrema can be fitted independently in either
system. Conversely, a legal triple satisfying the original full
system with $h_i=0$ and its four terminal collision products is
$L_2$ by Proposition 7.2; the new restrictions are consequences,
not substitutes for those full equations.

## 13. Mathematical correspondence and the unchanged original-root obligation

| Source and exact scope | Use and resulting boundary |
| --- | --- |
| This volume, Sections 1–2 and 7 | Complete worlds, all six original-clock equations, positive traces, chronological response functions, complete-target inverse, interpolation and the actual-child PP/PT/TP/TT interface are reused. Theorem 9.1 adds a shared-$U$ exclusion at common drift without requiring a common future ratio. |
| This volume, Theorem 5.1 and Corollary 7.3 | The sixth-sign classification is retained. The nonzero-sixth varying-ratio PP alternative is excluded by Corollary 9.2; the all-zero TT alternative is restricted by Corollary 12.1. The earlier algebraic statements and their proofs retain their original domains. |
| [Zero-Sixth Pairs](FIB_JMMJM_ZERO_SIXTH_PAIR_INJECTIVITY_AND_JOINT_COLLISION_OBSTRUCTIONS.md), Theorems 4.1, 5.1 and 6.2; Proposition 7.1 | Whole-class $AB,AD$ injections, strict $AC$ obstructions and entire-slice consequences, exact pattern exclusions and joint realization are established inputs. Section 10 gives a coordinate inverse for the reused $AB$ map; Corollary 12.2 intersects the existing restrictions with the new drift localization. None is counted as a new pair-injectivity result. |
| [Zero-Sixth Geometry](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md), Theorems 2.1, 4.1 and 6.1 | Fixed-drift repeated-sixth rigidity, its strict necessary drift ranges, three-coordinate injections and simultaneous sign/incidence restrictions are reused at their stated scopes. Their repeated-root ranges make all sixth roots in (12.1) simple. They do not decide TT feasibility. |
| [VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), Definition 1.1 and Sections 1–4; [VIII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md), Definition 1.1 | The legal model, literal ancestor and full-target meaning are unchanged. The known initial-root inverse and the double-terminal-root results retain their own promises; the safe-drift decoder supplies no label on an unrestricted fiber. |
| [IV](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), Theorem 9.3; Definitions 13.1–13.2, Theorem 13.3 and Section 14 | The full original-root system has 256 world slots and 254 shared-prefix responses. Its source projection keeps all gain and applicable same-source separation guards. No common drift, three-world size, terminal nonvanishing or this particular ancestor can be imposed on that unrestricted source-tuple problem without an additional bridge. |

The new deductions in Sections 9–12 are the broad common-drift
actual-$J$ pair exclusion and its nonzero-sixth PP consequence,
the whole-class scalar $A$ injection on (11.4), its actual $JJ$
decoder on the promised union, the late-zero cardinality bound,
and their sharper localization of the remaining TT system after
reusing the published pair obstructions. Matrix multiplication,
cubic interpolation and root counting, binomial positivity
certificates, quadratic signs and strict monotonicity are standard
tools within these model-specific deductions. The full certificate
(9.15)–(9.17) and scalar proof carry the ordinary mathematical
claims; no self-check or external generic identifiability theorem
is used in place of a proof. No literature-priority or exhaustive
literature-search claim is made.

Neither a legal TT witness nor a uniform TT exclusion in the two
remaining windows is supplied. The allowed patterns are necessary
restrictions, not attainable configurations. Unequal drifts,
mixed terminal-root strata, arbitrary larger or infinite losing
families outside the promised decoder class, other actual histories,
earlier $JMMJ$ parent-arm gluing and the separate $MMJM$ and
$MJMMJ$ obligations remain unresolved. A larger losing set is not
proved to contain a losing triple. A jointly injective terminal
vector is not joint physical acquisition, and root/drift promises
are not labels obtained on the unrestricted six-reading fiber.

The original full-domain alternative remains
$n_{\mathrm{det}}(3,0)\ge9$ versus a lawful complete-target decoder
on every legal world with at most eight total readings. Both first
actions, every actual history and early stop, arbitrary constant
drift, all strictly positive nonsymmetric rank-one trace-one
sources, and all nonzero real cubic-or-lower gains with both signs,
all roots and multiplicities remain in that goal. Neither this
alternative nor a uniform nine-reading upper bound is established
or assumed here. These are ordinary mathematical results without
a Lean or kernel-verification claim.

## 追加锚（本行以下为增补区）
