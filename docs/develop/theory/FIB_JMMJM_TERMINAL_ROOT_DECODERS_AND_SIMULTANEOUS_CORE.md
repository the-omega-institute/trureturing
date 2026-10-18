# FIB JMMJM Terminal-Root Decoders and the Simultaneous Core

## 1. Complete worlds, normalization and actual children

A complete world is $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and
$\delta\in\mathbb R$. The source need not be symmetric. Both gain
signs, all permitted degree drops, sampled roots and repeated roots
are allowed unless a conclusion below excludes them. Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

At original clock $i$ the reading is
$g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts.
Every atom is immediately read on one unresettable, uncopyable
trajectory. A chronological word $EF$ means first $E$ and its
reading, then $F$ and its reading; its cumulative matrix is $FEA$.
There are no skipped or extra readings and no clock renumberings.
Policies may be arbitrary deterministic functions of the entire
actual history, without a regularity or computational bound.

For arbitrary $D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, fix exactly
the literal history

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
                 M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.2}
$$

Its five chronological atoms are $JMMJM$. All six readings at clocks
zero through five remain imposed on every world considered together.
The history parameter $D_0$ is not a drift promise. Put

$$
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
y=(Y-D_0)/\lambda,\qquad \zeta=(z-D_0)/\lambda.
\tag{1.3}
$$

The matrices and normalized readings are

$$
\begin{gathered}
(A_0,\ldots,A_5)=(I,J,L,J+L,C,Q),\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
C=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q=\begin{pmatrix}1&1\\3&2\end{pmatrix}=I+2J+2L-C,\\
(c_0,\ldots,c_5)=(0,24,48,312/5,y,\zeta).
\end{gathered}
\tag{1.4}
$$

Write

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
0<r<1,\quad u,v>0,\quad uv=r(1-r)\le\tfrac14,
\qquad j=u+v,\quad \ell=1+u.
\tag{1.5}
$$

These inequalities and the determinant equation are equivalent to
source legality: determinant zero and trace one give rank one.
Direct trace multiplication gives the entire ancestor system

$$
\begin{aligned}
f(0)+d&=0,\\
f(1)j+d&=24,\\
f(2)\ell+d&=48,\\
f(3)(j+\ell)+d&=312/5,\\
f(4)(1+r+j)+d&=y,\\
f(5)(j+2\ell-r)+d&=\zeta.
\end{aligned}
\tag{1.6}
$$

All six trace factors are strictly positive. More generally this
holds for the trace of any nonzero entrywise nonnegative cumulative
matrix against a strictly positive source. Membership in
$\mathcal F(H)$ means legality and all six equations, not merely an
eliminated necessary relation.

The individual sixth-matrix identities are

$$
JQ=\begin{pmatrix}3&2\\1&1\end{pmatrix}=2C-L,\qquad
MQ=\begin{pmatrix}3&2\\4&3\end{pmatrix}=I+2J+2L.
\tag{1.7}
$$

Thus define the normalized sixth and terminal responses by

$$
\begin{aligned}
t_J&=2(1+r+j)-\ell,&t_M&=1+2j+2\ell,\\
v_E(W)&=d+f(6)\operatorname{tr}(EQP),&
r_{EF}(W)&=d+f(7)\operatorname{tr}(FEQP).
\end{aligned}
\tag{1.8}
$$

Here $E,F\in\{J,M\}$ and $EF$ is chronological. Raw responses are
$D_0+\lambda v_E$ and $D_0+\lambda r_{EF}$. Counterfactual response
functions in a proof are not additional acquisitions.

For a known candidate set $K$ at any literal history $H'$, use

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{q+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
 \bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:
 L_q(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{1.9}
$$

Each actual child retains the same fixed worlds and their whole
common ancestor. The affine response map
$w\mapsto(w-D_0)/\lambda$ is a bijection for either sign of
$\lambda$. It preserves response equalities and child cardinalities.
Induction in (1.9), using the bijection for each existential real
response, proves preservation of every $L_q$. Complete-world
distinction is preserved, and inverse normalization is

$$
g=\lambda f,\qquad \delta=D_0+\lambda d,
\tag{1.10}
$$

with the same $P$.

The model, ancestor and positive chart used below are credited to
*FIB self-calibrating relation mathematics VII*, Definitions 1.1–1.3.
Every identity needed for those deductions
is proved below; no unseen source or large coefficient certificate is
a premise.

## 2. The complete root-seven interpolation identities

**Lemma 2.1.** Let $\deg f\le3$, $f(7)=0$, and put
$a_i=f(i)$ for $i=1,2,3$. Then

$$
\begin{aligned}
0=f(7)&=-20f(0)+70a_1-84a_2+35a_3,\\
f(4)&=\tfrac12a_1-\tfrac95a_2+\tfrac94a_3,\\
f(5)&=a_1-\tfrac{16}5a_2+3a_3,\\
f(6)&=a_1-3a_2+\tfrac52a_3.
\end{aligned}
\tag{2.1}
$$

When $f(0)=-d$, the entire coefficient vector in increasing powers
of $T$ is

$$
\left(-d,\ \tfrac{11}6d+3a_1-\tfrac32a_2+\tfrac13a_3,
 -d-\tfrac52a_1+2a_2-\tfrac12a_3,
 \tfrac16d+\tfrac12a_1-\tfrac12a_2+\tfrac16a_3\right).
\tag{2.2}
$$

**Proof.** The Lagrange polynomials at clocks zero through three are

$$
\begin{aligned}
\ell_0(T)&=-(T-1)(T-2)(T-3)/6,\\
\ell_1(T)&=T(T-2)(T-3)/2,\\
\ell_2(T)&=-T(T-1)(T-3)/2,\\
\ell_3(T)&=T(T-1)(T-2)/6.
\end{aligned}
\tag{2.3}
$$

They have value one at their own node and zero at the other three.
The difference between $f$ and its interpolation has four distinct
zeros, hence is zero: successive division by distinct linear factors
proves the root bound for a nonzero polynomial. Their complete
evaluation table needed here is

$$
\begin{array}{c|rrrr}
T&\ell_0&\ell_1&\ell_2&\ell_3\\ \hline
4&-1&4&-6&4\\
5&-4&15&-20&10\\
6&-10&36&-45&20\\
7&-20&70&-84&35
\end{array}
\tag{2.4}
$$

The last row and $f(7)=0$ give
$f(0)=\tfrac72a_1-\tfrac{21}5a_2+\tfrac74a_3$.
Substitution into the other rows yields, respectively, the triples
$(1/2,-9/5,9/4)$, $(1,-16/5,3)$ and $(1,-3,5/2)$.
Expanding $-d\ell_0+a_1\ell_1+a_2\ell_2+a_3\ell_3$ gives (2.2).
Only fixed nonzero integer denominators occur. No gain sample has
been divided out. Lower degrees and repeated roots are included. ∎

## 3. All three terminal roots: the exact actual-child reduction

**Theorem 3.1.** Let $K=\{W_1,W_2,W_3\}$ consist of three pairwise
distinct fixed legal worlds on (1.2), with $f_i(7)=0$ for every $i$.
Allow arbitrary drifts $d_i$. Then

$$
L_2(K,H)\quad\Longleftrightarrow\quad
\bigwedge_{E\in\{J,M\}}\exists i<j:
       d_i=d_j\ \land\ v_E(W_i)=v_E(W_j).
\tag{3.1}
$$

The pair may depend on $E$. If the drifts are not all equal, this
reduces to $L_2$ of the unique equal-drift proper pair, when such a
pair exists. If all three drifts differ, $L_2(K,H)$ is false.

**Proof.** Fix $E$ and any real raw sixth response $w$. Its actual
child is

$$
K_{E,w}=\{W_i\in K:D_0+\lambda v_E(W_i)=w\}.
\tag{3.2}
$$

For each last action $F$, the raw response of $W_i$ at clock seven
is $D_0+\lambda d_i$, because its seventh gain vanishes. Thus an
$L_1$ child must contain an equal-drift pair: applying its defining
condition to either last action requires a terminal response class
of size at least two. Conversely, an equal-drift pair in the child
supplies, under each last action, the raw response
$D_0+\lambda d_i$ retaining that same pair and satisfying $L_0$.
This includes empty, singleton and shared-three sixth children.

Existence of an $L_1$ child for a fixed $E$ is therefore exactly
existence of an equal-drift pair with equal $v_E$. Conjoining for
the two first actions proves (3.1), with all response quantifiers.
If the drifts are not all equal, there is at most one equal-drift
pair. It must collide under both sixth actions. All its terminal
responses are the common drift, so the pair itself has $L_2$ by
(1.9). Conversely such a proper pair supplies actual losing children
in the triple. With three distinct drifts no equal-drift pair exists.
All pairs here belong to the same fixed triple on the same history;
no separately realizable pairs are combined. ∎

## 4. Fixed-M decoders at the four early drifts

**Theorem 4.1.** For each fixed
$d\in\{0,24,48,312/5\}$, the scalar sixth response under $M$ is
injective on the entire class

$$
\mathcal K_d^7=\{W\in\mathcal F(H):d_W=d,\ f_W(7)=0\}.
\tag{4.1}
$$

One $M$ and its immediate sixth read recover the complete target on
this known class and every known subset, with no cardinality bound.
In particular neither $L_1$ nor $L_2$ holds on such a subset. The
$d=0$ decoder is the credited baseline root-seven case; the other
three formulas extend the drift coverage.

**Proof, the positive trace parameter.** Put $k=j/\ell>0$ and
$A=24-d$, $B=48-d$, $C_*=312/5-d$. The first four equations and
Lemma 2.1 give

$$
20d+\frac{70A}{j}-\frac{84B}{\ell}
                       +\frac{35C_*}{j+\ell}=0.
\tag{4.2}
$$

These divisions use only positive traces, so sampled zeros are not
excluded. We examine all four drifts.

If $d=0$, multiplying (4.2) by $j\ell(j+\ell)$ gives
$-168\ell^2(24k^2+k-10)=0$. Since

$$
24k^2+k-10=(8k-5)(3k+2),
\tag{4.3}
$$

positivity forces $k=5/8$. The four initial gain samples are
$(0,24/j,30/j,24/j)$, hence interpolation gives

$$
f(T)=cT(T-5)(T-7),\qquad c=1/j>0.
\tag{4.4}
$$

Here $\ell=8j/5$ and $v_M=-6c-156/5$, an injective function of
$c$. Recovering $c$ fixes the gain, $j,\ell,u=\ell-1$ and
$v=j-\ell+1$. Since $f(4)=12c\ne0$, the fourth equation fixes
$r$. This calculation supplies the baseline in full, without
requiring an unseen proof from V.

For each nonzero $d$ in the theorem, (4.2) is equivalently

$$
20d\ell=84B-70A/k-35C_* /(k+1).
\tag{4.5}
$$

At $d=24$, this gives

$$
\begin{aligned}
\ell&=\frac{7(3k+1)}{5(k+1)},&
f(6)&=\frac{120(1-3k)}{7(3k+1)},\\
v_M-d=B_{24}(k)&=\frac{24}{7}
                  \left(9-42k+\frac{10}{3k+1}\right).
\end{aligned}
\tag{4.6}
$$

Indeed $1+2(k+1)\ell=(42k+19)/5$ and

$$
(1-3k)(42k+19)=(9-42k)(3k+1)+10.
\tag{4.7}
$$

For $k_2>k_1>0$, both $-42k$ and $10/(3k+1)$ strictly decrease.
Thus $B_{24}$ is strictly decreasing, including its zero at
$k=1/3$ without division by that zero.

At $d=48$, the formulas are

$$
\begin{aligned}
\ell&=\frac{7(7k+10)}{40k(k+1)},&
f(6)&=\frac{480(k-2)}{7(7k+10)},\\
v_M-d=B_{48}(k)&=\frac{24(k-2)(69k+70)}{7k(7k+10)}\\
&=\frac{24}{7}\left(\frac{69}{7}-\frac{14}{k}
                              -\frac{480}{7(7k+10)}\right).
\end{aligned}
\tag{4.8}
$$

The sixth trace is $(69k+70)/(20k)$. The partial fraction identity
is certified by

$$
\begin{aligned}
(k-2)(69k+70)&=69k^2-68k-140,\\
(k-2)(69k+70)-\tfrac{69}7k(7k+10)
 &=-\tfrac{1166}7k-140\\
 &=-14(7k+10)-\tfrac{480}7k.
\end{aligned}
\tag{4.9}
$$

Both negative reciprocal terms in (4.8) strictly increase for
$k>0$, so $B_{48}$ is strictly increasing, including $k=2$.

At $d=312/5$, one obtains

$$
\begin{aligned}
\ell&=\frac{7(20-9k)}{65k},&0<k&<20/9,\\
f(6)&=\frac{312(9k-8)}{7(20-9k)},\\
v_M-d=B_{312/5}(k)
 &=\frac{312}{7}\left(-1+\frac{12}{20-9k}\right)
       +\frac{48}{5}\left(9k+1-\frac8k\right).
\end{aligned}
\tag{4.10}
$$

The interval is forced by $\ell>0$. The complete simplifications are

$$
\frac{9k-8}{20-9k}=-1+\frac{12}{20-9k},\qquad
\frac{(9k-8)(k+1)}k=9k+1-\frac8k.
\tag{4.11}
$$

Both summands in (4.10) strictly increase on this interval. The
possible sixth zero $k=8/9$ is included.

In all nonzero-drift cases, equal sixth $M$ responses give equal
$k$, then equal $\ell,j$. The first four ancestor equations fix
$f(0),\ldots,f(3)$, dividing only by positive traces, hence fix the
entire gain. Moreover $d$ equals the reading at one clock
$q\in\{1,2,3\}$, so $f(q)=0$. Both $f(4)$ and $f(5)$ cannot
vanish: together with $q,7$ that would give four distinct roots of a
nonzero degree-at-most-three polynomial. A nonzero one of these two
samples fixes $r$, using respectively $1+r+j$ or $j+2\ell-r$.
Thus the complete worlds agree. This argument allows every degree
drop and root multiplicity and never divides by an unproved nonzero
gain sample.

**Proof, inverse and actual-child quantifiers.** The known whole
class has a unique inverse at its actual sixth $M$ response by the
injectivity just proved; existence comes from the actual candidate.
Reconstruction above and (1.10) return $P,g,\delta$. A known
singleton may stop; empty classes are unreachable. The same fixed
action and inverse restrict to every known subset $K$, including
infinite or disconnected subsets. For every real raw response $w$,

$$
K_w=\{W\in K:D_0+\lambda v_M(W)=w\}
\tag{4.12}
$$

has at most one world. Thus $L_0(K_w,(H,M,w))$ and
$L_1(K_w,(H,M,w))$ both fail for every $w$. The $M$ conjunct of
(1.9) fails for both $L_1(K,H)$ and $L_2(K,H)$; empty and
singleton parents also fail their cardinality clause. The last
clock is six, with at most seven total readings. ∎

## 5. Two entire late-and-terminal-root classes have at most two worlds

For $a\in\{4,5\}$ define the known root class

$$
\mathcal Z_{a7}=\{W\in\mathcal F(H):f(a)=f(7)=0\}.
\tag{5.1}
$$

**Theorem 5.1.** Each entire $\mathcal Z_{a7}$ contains at most two
complete worlds. The source and gain shape are initially variable,
and the original drift is arbitrary. Within the class the drift is
forced to equal the actual reading at $a$.

**Proof, generic drift and all quadratic coefficients.** Write

$$
f(T)=(T-a)(T-7)(b+eT),\qquad b=-d/(7a).
\tag{5.2}
$$

This includes quadratic gains and repeated roots. First suppose
$d\notin\{0,24,48,312/5\}$. Then $b\ne0$, and each of the first
three noninitial gain samples is nonzero by (1.6) and positivity.
Put $\mu=e/b$. In particular $1+\mu,1+2\mu,1+3\mu$ are
nonzero. Use $j+\ell$ as the sum of the first two traces. Set
$A=24-d$, $B=48-d$, $C_*=312/5-d$ and

$$
\begin{aligned}
p_1&=(1+2\mu)(1+3\mu)=1+5\mu+6\mu^2,\\
p_2&=(1+\mu)(1+3\mu)=1+4\mu+3\mu^2,\\
p_3&=(1+\mu)(1+2\mu)=1+3\mu+2\mu^2.
\end{aligned}
\tag{5.3}
$$

For $a=4$, the samples at one, two and three are
$b(18(1+\mu),10(1+2\mu),4(1+3\mu))$. Clearing the proved
nonzero factors in $A/f(1)+B/f(2)=C_*/f(3)$ gives

$$
10A p_1+18B p_2-45C_*p_3=R_4(\mu)=0,
\tag{5.4}
$$

whose complete coefficient triple is

$$
\begin{aligned}
&(10A+18B-45C_*,\ 50A+72B-135C_*,\ 60A+54B-90C_*)\\
&\hspace{8mm}=(17d-1704,\ 13d-3768,\ -24d-1584).
\end{aligned}
\tag{5.5}
$$

This polynomial is never identically zero: its quadratic coefficient
can vanish only at $d=-66$, where its constant is $-2826$.

For $a=5$, the three samples are
$b(24(1+\mu),15(1+2\mu),8(1+3\mu))$, giving

$$
5A p_1+8B p_2-15C_*p_3=R_5(\mu)=0,
\tag{5.6}
$$

with the complete triple

$$
\begin{aligned}
&(5A+8B-15C_*,\ 25A+32B-45C_*,\ 30A+24B-30C_*)\\
&\hspace{8mm}=(2d-432,\ -12d-672,\ -24d).
\end{aligned}
\tag{5.7}
$$

Its quadratic coefficient is nonzero in this case. Thus at most two
real $\mu$ values are possible for either class, including the
linear degree drop in $R_4$.

We need a nonzero late sample to recover $r$. No legal world has all
three roots $4,5,7$. Indeed such a world would have

$$
f(T)=c(T-4)(T-5)(T-7),\qquad c=d/140\ne0.
\tag{5.8}
$$

Its samples at one, two and three are $-72c,-30c,-8c$. The trace
sum relation gives

$$
\frac{35}{18}(d-24)+\frac{14}{3}(d-48)
                         =\frac{35}{2}(d-312/5).
\tag{5.9}
$$

Multiplying by 18 gives $119d-4872=315d-19656$, whence
$d=528/7$. Therefore

$$
j=175/132,\quad \ell=56/33,\quad u=23/33,\quad v=83/132,
\qquad uv=1909/4356>1/4
\tag{5.10}
$$

because $7636>4356$. This contradicts rank-one source legality.

For a fixed $\mu$, the other late sample (at five for $a=4$, at
four for $a=5$) is consequently nonzero. The first two gain samples
fix $j,\ell$, hence $u,v$; the other late equation fixes $r$.
Each $\mu$ thus gives at most one complete world. All remaining
equations and inequalities still apply: the quadratic equation alone
is not sufficient for membership.

**Proof, the three nonzero exceptional drifts.** If
$d\in\{24,48,312/5\}$, let $q\in\{1,2,3\}$ be its corresponding
clock. The gain also has root $q$, so it is uniquely

$$
f(T)=\frac{d}{7aq}(T-a)(T-q)(T-7).
\tag{5.11}
$$

At zero the product is $-7aq$, giving exactly $f(0)=-d$.
At the two non-root clocks among one, two and three, the trace
factors determine $j,\ell$: for $q=1$ use $\ell,j+\ell$, for
$q=2$ use $j,j+\ell$, and for $q=3$ use $j,\ell$. The other late
sample is nonzero in this explicit three-root polynomial and fixes
$r$. Thus each such class has at most one world. The zero sample at
$q$ is not divided out.

**Proof, zero drift.** If $d=0$, (5.2) has $b=0$ and $e\ne0$.
For $a=4$, the samples are $18e,20e,12e$, which would require

$$
j=\frac4{3e},\quad \ell=\frac{12}{5e},\quad
j+\ell=\frac{26}{5e}.
\tag{5.12}
$$

The first two sum to $56/(15e)$, whereas the third is
$78/(15e)$. Thus this class is empty.

For $a=5$, write $f(T)=cT(T-5)(T-7)$. The clock-one trace forces
$c>0$, and the first four equations give

$$
j=1/c,\quad \ell=8/(5c),\quad
u=8/(5c)-1,\quad v=1-3/(5c).
\tag{5.13}
$$

Put $A_0=(y-12)/12$. Since $f(4)=12c$, the fourth equation gives
$r=A_0/c-1$. The rank-one equation is exactly

$$
c^2-(3A_0-11/5)c+A_0^2-24/25=0.
\tag{5.14}
$$

To check every coefficient, multiply $uv=r(1-r)$ by $c^2$:
the two sides are respectively
$(11/5)c-c^2-24/25$ and $3A_0c-2c^2-A_0^2$.
The leading coefficient in (5.14) is one, so at most two $c$ values
are possible, each fixing the complete world. The fifth equation is
also retained and requires $\zeta=0$. These cases exhaust all drifts
and every permitted gain degree and multiplicity. ∎

## 6. Small independent pair separation and the whole-class inverse

**Theorem 6.1.** Two distinct worlds in one $\mathcal Z_{47}$ or one
$\mathcal Z_{57}$ cannot have both sixth responses equal. Consequently
one fixed sixth action is injective on each entire known class and
recovers the complete target with one immediate read, also on every
known subset. Neither $L_1$ nor $L_2$ holds on such a subset.

**Proof, the positive chart and the zero-sixth case.** Suppose both
sixth responses agree for two worlds in $\mathcal Z_{a7}$. Their
drifts agree because their common actual reading at $a$ is that
drift. For each world put $\eta=(QP)_{22}>0$, $R=P/\eta$,
$F=\eta f$. The full rank-one positive chart is

$$
\begin{aligned}
QR&=\begin{pmatrix}x\xi&x\\\xi&1\end{pmatrix},&
R&=\begin{pmatrix}(1-2x)\xi&1-2x\\(3x-1)\xi&3x-1\end{pmatrix},\\
&\tfrac13<x<\tfrac12,\quad \xi>0,&
P&=R/\operatorname{tr}R,\quad f=(\operatorname{tr}R)F.
\end{aligned}
\tag{6.1}
$$

Here $\xi$ denotes a source-chart coordinate; $y$ remains the normalized
ancestor reading. Rank one fixes the top-left entry of $QR$ as $x\xi$ after its
bottom-right entry is normalized to one. Multiplication by
$Q^{-1}=\left(\begin{smallmatrix}-2&1\\3&-1\end{smallmatrix}\right)$
gives $R$, whose four entries are positive exactly on the stated
strip. This proves both directions of the chart correspondence.
Writing $s=x+\xi$, $p=x\xi$, its complete ancestor trace vector is

$$
(T_0,\ldots,T_5)
=(s+2x-2p-1,\ 1-x-s+3p,\ s-2p,\ 1-x+p,\ s-p,\ p+1).
\tag{6.2}
$$

The equations are $F(i)T_i+d=c_i$ for all six clocks. The sixth
traces are $s,s+1$. Equality of both sixth responses therefore gives

$$
F_1(6)=F_2(6)=c,\qquad c(s_1-s_2)=0.
\tag{6.3}
$$

If $c=0$, the trace-one gains have roots $a,6,7$, so both equal
$d(T-a)(T-6)(T-7)/(42a)$. Here $d=0$ would make the gain zero
and is impossible. The nonzero samples at one and two fix $j,\ell$;
the other late sample is nonzero and fixes $r$. Thus the worlds
coincide. This case divides by no sixth sample.

**Proof, the complete difference and mean identities.** Suppose
$c\ne0$. Then $s_1=s_2=s>0$. Equal $x$ would imply equal $\xi$ and
source, then equal gain by the first four equations and common
drift. Thus

$$
\Delta=x_1-x_2\ne0,\qquad q=s-x_1-x_2,
\qquad U=(T_{1,4}+T_{2,4})/2.
\tag{6.4}
$$

Here $T_{h,i}$ is world $h$'s clock-$i$ trace. Since
$p_1-p_2=q\Delta$, subtracting and averaging (6.2) gives

$$
\begin{aligned}
(T_{1,i}-T_{2,i})/\Delta&=\ell_i,\\
(\ell_0,\ldots,\ell_5)&=(2(1-q),\ 3q-1,\ -2q,\ q-1,\ -q,\ q),\\
\overline T_i&=(T_{1,i}+T_{2,i})/2,\\
(\overline T_0,\ldots,\overline T_5)
 &=\left(2U-q-1,\ 1+\frac{3s+q}{2}-3U,\ 2U-s,
                  1+\frac{s+q}{2}-U,\ U,\ s+1-U\right).
\end{aligned}
\tag{6.5}
$$

All mean traces are positive. For example the mean $x$ is
$(s-q)/2$, and the mean $p$ is $s-U$; substituting these two
quantities into each entry of (6.2) proves every mean formula.

The difference $F_1-F_2$ is not zero. Otherwise the common equations
would give $F(i)\ell_i=0$ for all six clocks. If $q\ne0$, entries
two, four and five of $\ell$ are nonzero; if $q=0$, entries zero,
one and three are nonzero. Thus $F$ would have three ancestor roots
and root seven, contradicting its being a nonzero polynomial of
degree at most three. Its shared roots $a,7$ and common sixth
sample now force

$$
\frac{F_1-F_2}{\Delta}=\alpha(T-a)(T-6)(T-7),\quad \alpha\ne0,
\qquad
\frac{F_1+F_2}{2}=(T-a)(T-7)(bT+e).
\tag{6.6}
$$

Subtract the two ancestor equations and use the elementary product
difference identity. After division by $\Delta$ and the nonzero
integer factors $(i-a)(i-7)$, this gives exactly

$$
\ell_i(bi+e)=(6-i)\alpha\overline T_i,
\qquad i\in\{0,1,2,3,4,5\}\setminus\{a\}.
\tag{6.7}
$$

The root-$a$ equation is the common drift equation itself. Thus no
ancestor equation is omitted. Every right side in (6.7) is nonzero
and has sign $\alpha$.

**Proof, root four.** For $a=4$, $q=0$ or $q=1$ makes an
$\ell_i$ vanish at a non-root index, impossible in (6.7). If
$q<0$, the signs at indices $0,1,2$ are $+,-,+$; if $q>1$, they
are $-,+,-$. If $0<q<1$, the signs at indices $0,2,5$ are
$+,-,+$. In each case $bi+e$ would have to alternate signs twice
at increasing indices, since its sign is
$\operatorname{sgn}(\alpha)\operatorname{sgn}(\ell_i)$.
A nonzero affine function cannot have two sign changes: its two
successive opposite-sign intervals would force two distinct roots,
whereas its degree is at most one. This excludes the pair for $a=4$.

**Proof, root five and the full small scalar certificate.** For
$a=5$, $q=0$ is impossible at index two. Divide (6.7) by
$\alpha\ne0$ and put $K=b/\alpha$, $H_0=e/\alpha$. Indices two
and four yield

$$
2K+H_0=(-4U+2s)/q,\qquad 4K+H_0=-2U/q,
\qquad
K=(U-s)/q,\quad H_0=(-6U+4s)/q.
\tag{6.8}
$$

The equations at zero, one and three respectively become

$$
\begin{aligned}
6U&=4(1-q)s+3q^2+3q,\\
10U&=(6-3q)s+10q+5q^2,\\
6U&=(q+2)s+6q+3q^2.
\end{aligned}
\tag{6.9}
$$

For a direct expansion certificate, before collecting coefficients
these three equations are

$$
\begin{aligned}
2(1-q)(-6U+4s)&=6q(2U-q-1),\\
(3q-1)(-5U+3s)&=5q\left(1+(3s+q)/2-3U\right),\\
(q-1)(-3U+s)&=3q\left(1+(s+q)/2-U\right).
\end{aligned}
\tag{6.10}
$$

Five times the third line of (6.9) minus three times the second
gives $(14q-8)s=0$. Since $s>0$, $q=4/7$. Subtracting the third
line from the first gives $(2-5q)s=3q$, hence $s=-2$, a
contradiction. This proves separation for $a=5$ as well. The chart,
factorizations and (6.5)–(6.10) are the entire certificate; no large
array or general pair-exclusion theorem is used.

**Proof, one whole-class action and all response children.** By
Theorem 5.1 a nonempty entire class has one or two worlds. A known
singleton may stop. For two worlds choose $J$ if their sixth $J$
responses differ, and $M$ otherwise; the separation proof guarantees
different $M$ responses in the latter case. This is one action
selected from the entire known class, independent of the unknown
member. Its raw sixth reading has exactly one inverse there. The
inverse returns the full world and then (1.10), not merely a gain
shape or source orbit. Candidate formation retains all equations
and legality; an extraneous root of (5.4) or (5.6) is not a world.

For the selected action $E$, every known subset $K$ of the class
and every real raw response $w$, the actual child
$\{W\in K:D_0+\lambda v_E(W)=w\}$ has at most one world. Its
$L_0$ and $L_1$ both fail. Therefore the selected action conjunct
fails in both $L_1(K,H)$ and $L_2(K,H)$. Empty and singleton sets
already fail their cardinality clauses. The same action restricts
to every subset; at most seven total readings are used. ∎

## 7. A sharp legal roots-five-and-seven example

**Theorem 7.1.** For every real $D_0$ and every $\lambda\ne0$, take
$Y=D_0+30\lambda$, $z=D_0$. Put

$$
\begin{gathered}
c_-=(23-\sqrt{13})/20,\qquad c_+=(23+\sqrt{13})/20,\\
r_c=\frac{3}{2c}-1,\qquad u_c=\frac{8}{5c}-1,\qquad
v_c=1-\frac{3}{5c},\qquad
P_c=\begin{pmatrix}r_c&u_c\\v_c&1-r_c\end{pmatrix},\\
f_c(T)=cT(T-5)(T-7),\qquad
g_c=\lambda f_c,\qquad \delta_c=D_0,
\quad c\in\{c_-,c_+\}.
\end{gathered}
\tag{7.1}
$$

These are exactly the two worlds of the entire $\mathcal Z_{57}$
on this one history. They prove the cardinality bound sharp and
are not an $L_2$ witness.

**Proof, coefficients and legality.** The complete normalized gain
coefficient vector is $(0,35c,-12c,c)$; the raw vector is
$\lambda(0,35c,-12c,c)$. The two amplitudes are exactly the roots of

$$
100c^2-230c+129=0,
\tag{7.2}
$$

since its discriminant is $1300=100\cdot13$. From
$3<\sqrt{13}<4$ one has

$$
19/20<c_-<1,\qquad 13/10<c_+<27/20.
\tag{7.3}
$$

Thus $3/4<c<3/2$ gives $0<r_c<1$, and $3/5<c<8/5$ gives
$u_c,v_c>0$. The trace is one. Direct multiplication gives

$$
\begin{aligned}
r_c(1-r_c)&=9/(2c)-2-9/(4c^2),\\
u_cv_c&=11/(5c)-1-24/(25c^2),\\
r_c(1-r_c)-u_cv_c
 &=-\frac{100c^2-230c+129}{100c^2}=0.
\end{aligned}
\tag{7.4}
$$

The matrices are therefore strictly positive, rank one and trace
one. They are nonsymmetric: $u_c=v_c$ would require $c=11/10$,
outside both intervals in (7.3). Both gains are nonzero cubics with
simple roots $0,5,7$, for either sign of $\lambda$. The worlds
are distinct because their gain coefficients differ.

**Proof, every actual ancestor reading.** Here $d=0$, $y=30$,
$\zeta=0$. For each of the two fixed worlds the full table is

$$
\begin{array}{c|c|c|c|c}
i&A_i&\operatorname{tr}(A_iP_c)&f_c(i)&
                    d+f_c(i)\operatorname{tr}(A_iP_c)\\ \hline
0&I&1&0&0\\
1&J&1/c&24c&24\\
2&L&8/(5c)&30c&48\\
3&J+L&13/(5c)&24c&312/5\\
4&C&5/(2c)&12c&30\\
5&Q&1+27/(10c)&0&0
\end{array}
\tag{7.5}
$$

Thus all six equations of precisely the same $JMMJM$ ancestor hold.
The raw readings are $D_0,D_0+24\lambda,D_0+48\lambda,
D_0+312\lambda/5,D_0+30\lambda,D_0$. Theorem 5.1 gives at most
two worlds in this root class; the two legal worlds displayed here
are consequently the entire class. This does not assert that they
are the whole unrestricted fiber.

**Proof, every sixth and terminal response and the losing-child
quantifiers.** One has

$$
\begin{aligned}
f_c(6)&=-6c,&t_J&=17/(5c),&t_M&=1+26/(5c),\\
v_J(W_c)&=-102/5,&v_M(W_c)&=-6c-156/5,\\
r_{JJ}(W_c)&=r_{JM}(W_c)=r_{MJ}(W_c)=r_{MM}(W_c)=0.
\end{aligned}
\tag{7.6}
$$

The difference in sixth $M$ values, plus-world minus minus-world,
is $-3\sqrt{13}/5\ne0$. In raw units the sixth $J$ value is
$D_0-102\lambda/5$, the sixth $M$ value is
$D_0+\lambda(-6c-156/5)$, and every terminal value is $D_0$.

Let $K$ be this pair. Under first action $J$, the actual response
$D_0-102\lambda/5$ retains both worlds. Under either last action
$F$, response $D_0$ retains that same pair, so this particular
$J$ child has $L_1$. Every other raw sixth $J$ response has an
empty child. Under first action $M$, every real raw response has
at most one world, hence no $M$ child has $L_1$. Therefore the
$M$ conjunct in (1.9) fails and $L_2(K,H)$ is false. This includes
every sixth response and both last actions and does not turn
terminal-root collisions into a losing pair. ∎

## 8. No ancestor zero and the inclusion-minimal simultaneous core

**Theorem 8.1.** Suppose three pairwise distinct fixed legal worlds
on (1.2) have one common drift $d$, all have root seven, and their
triple has $L_2$. Then

$$
d\notin\{0,24,48,312/5,y,\zeta\},\qquad
f_h(i)\ne0\quad(h=1,2,3;\ 0\le i\le5).
\tag{8.1}
$$

If in addition no proper pair of this triple has $L_2$, then their
sixth gain samples have one common nonzero sign and, after
relabeling, their exact sixth collision pattern is

$$
v_J(W_1)=v_J(W_2)\ne v_J(W_3),\qquad
v_M(W_1)=v_M(W_3)\ne v_M(W_2).
\tag{8.2}
$$

Every inclusion-minimal all-root-seven $L_2$ triple, even with
initially arbitrary drifts, therefore has a common drift and all
these restrictions. In this restricted core its sources are pairwise
distinct and its gains belong to pairwise distinct one-dimensional
polynomial subspaces.

**Proof, ancestor-zero exclusion.** If any one gain vanishes at an
ancestor clock $i$, its reading is $c_i=d$. The other two worlds
have the same drift and that same reading. Since their trace
factors are positive, both their gains also vanish there. For
$i\in\{0,1,2,3\}$, Theorem 4.1 gives a fixed sixth $M$ action
injective on the entire common-drift root-seven class, contradicting
$L_2$. For $i=4$ or $5$, all three worlds would belong to
$\mathcal Z_{i7}$, contradicting Theorem 5.1. Conversely if $d$
equaled any of the six readings, positivity in (1.6) would force a
gain zero there. This proves (8.1) without inclusion-minimality.

**Proof, signs and different pairs.** For both sixth actions,

$$
\operatorname{sgn}(v_E(W)-d)=\operatorname{sgn}f_W(6)
\tag{8.3}
$$

because the sixth trace is positive. Different sign classes cannot
collide. If all three signs differ, neither action has any collision,
contrary to Theorem 3.1. If exactly two signs agree, the only possible
collision pair for either action is that fixed same-sign pair.
Theorem 3.1 requires collisions under both actions, so this proper
pair has $L_2$, a contradiction. If all signs are zero, every
proper pair has both sixth values and all terminal values equal to
$d$ and is $L_2$. Thus all three signs must be the same nonzero
sign. This proves nonvanishing at clock six as well.

Both actions have a collision by Theorem 3.1. If one action is
shared by all three worlds, a colliding pair for the other action
collides for both and is a proper $L_2$ pair. Otherwise each action
has precisely one pair and a singleton. The two pairs cannot be the
same, for the same reason. Two different pairs on three worlds
intersect in one world, giving exactly (8.2). Theorem 3.1 also shows
that an initially variable-drift triple with no proper $L_2$ pair
must first have one common drift. All these are actual pairs in one
simultaneous triple, not separate constructions.

**Proof, the restricted pairwise diversity.** By (8.1), $d\ne0$
and $f(1),f(2),f(4)$ are nonzero. If two gains are proportional,
their common constant value $-d$ forces the proportionality factor
to be one. Equal gains and the first two nontrivial readings fix
equal $j,\ell$, hence $u,v$; the nonzero fourth sample fixes $r$.
The worlds would coincide. If two sources were equal, their common
drift and first four positive trace factors would fix equal gain
samples at zero through three and hence the same entire gain.
Again they would coincide. Thus both distinctions are pairwise
within this common-drift core. This does not extend pairwise
diversity to unrestricted triples. ∎

## 9. Exact rational feasibility of the remaining simultaneous core

The following equivalence supplies a full simultaneous system; it
does not assign that system a feasibility verdict.

**Theorem 9.1.** Fix $d,y,\zeta\in\mathbb R$ with
$d\notin\{0,24,48,312/5,y,\zeta\}$. A triple as in the restricted
core of Theorem 8.1 exists on these normalized data if and only if,
after the relabeling in (8.2), the rational system below has a
solution. All three parameter evaluations use the same $d,y,\zeta$.

Seek pairwise distinct real $k_1,k_2,k_3>0$. Put

$$
\begin{aligned}
A&=24-d,&B&=48-d,&C_*&=312/5-d,\\
N_d(k)&=(4032-84d)k^2+(168+21d)k+70d-1680,\\
\ell(k)&=\frac{N_d(k)}{20d\,k(k+1)},&j(k)&=k\ell(k),\\
u(k)&=\ell(k)-1,&v(k)&=(k-1)\ell(k)+1.
\end{aligned}
\tag{9.1}
$$

For each $k=k_h$ require $\ell>1$, $v>0$, and define

$$
a_1=\frac{A}{k\ell},\qquad
a_2=\frac{B}{\ell},\qquad
a_3=\frac{C_*}{(k+1)\ell}.
\tag{9.2}
$$

Define $f_k$ by the full increasing-power coefficient vector

$$
\left(-d,\ \tfrac{11}6d+3a_1-\tfrac32a_2+\tfrac13a_3,
 -d-\tfrac52a_1+2a_2-\tfrac12a_3,
 \tfrac16d+\tfrac12a_1-\tfrac12a_2+\tfrac16a_3\right),
\tag{9.3}
$$

and put

$$
h_4=\tfrac12a_1-\tfrac95a_2+\tfrac94a_3,\qquad
h_5=a_1-\tfrac{16}5a_2+3a_3,\qquad
h_6=a_1-3a_2+\tfrac52a_3.
\tag{9.4}
$$

Require $h_4h_5h_6\ne0$, and set

$$
\begin{aligned}
r(k)&=(y-d)/h_4-1-k\ell,\qquad 0<r(k)<1,\\
(\ell-1)((k-1)\ell+1)&=r(k)(1-r(k)),\\
\zeta-d&=h_5((k+2)\ell-r(k)),\\
P_k&=\begin{pmatrix}r(k)&\ell-1\\(k-1)\ell+1&1-r(k)\end{pmatrix}.
\end{aligned}
\tag{9.5}
$$

Finally define

$$
U(k)=h_6\bigl(2+2r(k)+(2k-1)\ell\bigr),\qquad
V(k)=h_6\bigl(1+2(k+1)\ell\bigr),
\tag{9.6}
$$

and require a common nonzero sign for $h_6(k_1),h_6(k_2),h_6(k_3)$,
together with

$$
U(k_1)=U(k_2)\ne U(k_3),\qquad
V(k_1)=V(k_3)\ne V(k_2).
\tag{9.7}
$$

The rank-one equality and fifth-reading equality in (9.5), as well
as the inequalities and simultaneous constraints, are part of the
system. None may be replaced by only (9.1).

**Proof, necessity and all coefficients of the elimination.** For
an actual core world put $k=j/\ell>0$. Its first four equations
give (9.2). Its seventh root and Lemma 2.1 give (4.5). Multiplying
by $k(k+1)$ gives

$$
20d\ell k(k+1)
   =84B k(k+1)-70A(k+1)-35C_*k=N_d(k).
\tag{9.8}
$$

The coefficients on the right are exactly

$$
\begin{array}{c|c|c}
\text{power}&\text{unsimplified coefficient}&\text{coefficient}\\ \hline
2&84B&4032-84d\\
1&84B-70A-35C_*&168+21d\\
0&-70A&70d-1680
\end{array}
\tag{9.9}
$$

Since $d\ne0$, (9.8) determines $\ell$ as in (9.1). Interpolation
gives (9.3) and (9.4). Theorem 8.1 gives the nonzero late and sixth
samples. The fourth equation, divided only by the proved nonzero
$h_4$, gives $r$ in (9.5). Source legality supplies all its
inequalities and rank-one equality. The fifth equation is precisely
the retained last scalar equality in (9.5). Identities (1.7)–(1.8)
give (9.6), and Theorem 8.1 gives the sign and collision conditions.

At fixed $d,y,\zeta$, equal $k$ determines equal $\ell,j$, the
entire polynomial and $r$, hence the same complete world. Therefore
three distinct core worlds supply three distinct parameters. Every
denominator used is nonzero by $d\ne0$, $k>0$, $\ell>1$ and
$h_4\ne0$. The example in Section 7, having $d=0$, is outside this
chart, rather than an omitted special case of this theorem.

**Proof, sufficiency and every ancestor equation.** Conversely take
three parameters satisfying all conditions. For each one,
$\ell>1$, $v>0$ and $0<r<1$ make all four entries of $P_k$
strictly positive. The retained equality $uv=r(1-r)$ gives
determinant zero, and trace one gives rank one. The coefficient
vector (9.3) defines a degree-at-most-three polynomial with
constant term $-d\ne0$, so the gain is legal and nonzero.
Expansion of (2.3) shows its four samples are exactly
$-d,a_1,a_2,a_3$. Equation (9.8), divided only by positive
$k\ell(k+1)$, is

$$
20d+70a_1-84a_2+35a_3=0.
\tag{9.10}
$$

By (2.4) this is exactly $f_k(7)=0$. Lemma 2.1 gives
$f_k(4)=h_4$, $f_k(5)=h_5$, $f_k(6)=h_6$. The six actual
ancestor equations now verify individually as

$$
\begin{aligned}
f_k(0)+d&=-d+d=0,\\
f_k(1)j+d&=\frac{A}{k\ell}(k\ell)+d=24,\\
f_k(2)\ell+d&=\frac{B}{\ell}\ell+d=48,\\
f_k(3)(j+\ell)+d
 &=\frac{C_*}{(k+1)\ell}(k+1)\ell+d=312/5,\\
f_k(4)(1+r+j)+d&=h_4(1+r+k\ell)+d=y,\\
f_k(5)(j+2\ell-r)+d&=h_5((k+2)\ell-r)+d=\zeta.
\end{aligned}
\tag{9.11}
$$

Because $d$ differs from all six readings and the traces are positive,
no ancestor gain sample is zero. Sixth gains are nonzero by (9.4).
Different $k$ give different complete worlds, since any one source
itself determines $j/\ell$. Their normalized sixth values are
$d+U(k)$ and $d+V(k)$, and their terminal values are all $d$.

**Proof, actual losing children and absence of a losing proper
pair.** Use the one resulting fixed triple $K$. Under first action
$J$, choose the raw response

$$
w_J=D_0+\lambda(d+U(k_1)).
\tag{9.12}
$$

Its actual child is exactly $\{W_1,W_2\}$ by (9.7). For each last
action $F\in\{J,M\}$, choose raw response $D_0+\lambda d$;
its actual terminal child is that same pair and has $L_0$. Thus
this particular $J$ child has $L_1$. Under first action $M$ choose

$$
w_M=D_0+\lambda(d+V(k_1)).
\tag{9.13}
$$

Its actual child is exactly $\{W_1,W_3\}$, and under each last
action the response $D_0+\lambda d$ again retains that pair and
has $L_0$. This proves both existential response clauses required
for $L_2(K,H)$. The only colliding proper pair under $J$ is
$\{1,2\}$ and the only one under $M$ is $\{1,3\}$; every proper
pair consequently fails one first-action clause of $L_2$. Empty
and singleton proper subsets fail the cardinality clause. Thus the
triple is inclusion-minimal and has exactly the core properties.

For arbitrary original $D_0$ and either sign of $\lambda\ne0$, set

$$
g_h=\lambda f_{k_h},\qquad \delta_h=D_0+\lambda d,
\qquad Y=D_0+\lambda y,\quad z=D_0+\lambda\zeta.
\tag{9.14}
$$

The bijection in Section 1 gives precisely the original-world
correspondence and the same actual-child quantifiers. This proves
both directions of the equivalence. No feasible parameters or
impossibility proof for (9.1)–(9.7) are supplied. ∎

## 10. Credits, promises and the exact residual gap

The supporting interpolation, polynomial root bound, direct trace
coordinates, positive rank-one chart and affine sign arguments are
established mathematical tools. This volume develops the early-drift formulas, roots-$\{4,7\}$ and
roots-$\{5,7\}$ cardinality and separation deductions, sharp example,
ancestor-zero exclusion and rational simultaneous-core description.
The complete proofs above establish their needed identities directly.

| Supplied source | Credit and scope retained |
| --- | --- |
| *FIB self-calibrating relation mathematics VII*, Definitions 1.1–1.3 and Section 4 | Complete-world model, exact $JMMJM$ ancestor, normalization, positive $Q$ chart and difference/mean-trace setup. The nine integer matrices and their tensor Bernstein identities are not premises here. |
| V, as credited by supplied VII, Definition 5.1 and Theorems 5.2, 7.1 | The earlier $JMMJ$ interface, baseline-drift root-seven inverse and rank-one terminal reconstruction. Section 4 includes the baseline computation directly and does not count $d=0$ as a new decoder. No unseen proof from V is required. |
| *FIB JMMJM Whole-Class Affine Decoders* | The entire fixed-shape and fixed-source classes have conditioned at-most-eight-reading decoders. Its no-three-ancestor-roots lemma and unrestricted at-least-two source/shape diversity statement retain their proved scopes. These are credited comparisons, not new theorems here. |
| *FIB JMMJM Late-Root Rigidity and Terminal Collision Reductions* | The entire roots-$\{4,5\}$ class has at most two worlds and a sixth-$J$ inverse, with its own sharp example. Exactly-two-terminal-roots triples and common-drift triples with different terminal signs reduce to a proper pair as stated there. These results are not retold as new contributions. |

The present roots-$\{4,7\}$ and roots-$\{5,7\}$ classes differ from
the roots-$\{4,5\}$ class. They start with both source and shape
free. Theorem 8.1 excludes every ancestor zero for a common-drift
all-root-seven losing triple, strengthening the supplied generic
at-most-two-ancestor-zeros restriction only under these hypotheses.
Its pairwise diversity conclusion is restricted to that nonzero,
common-drift core; the unrestricted companion requires only at
least two sources and two shapes.

All root, shape, source and fixed-drift class conditions are known
candidate promises or explicit theorem hypotheses. They are not
inferred from observed equalities. In particular $y=\zeta$ alone
equates $f(4)\operatorname{tr}(CP)$ and
$f(5)\operatorname{tr}(QP)$; it neither makes them zero nor
identifies $d$. A scalar injective on each promised class need not
be injective on their unrestricted union. The actions in Sections
4 and 6 are chosen from the entire known class, not separately for
different unknown members. All policies acquire the actual sixth
atom and its immediate reading on the original trajectory.

VII, Theorem 4.1 states uniform exclusion of every distinct $L_2$
pair on this exact entire ancestor. Its large-array certificate is
not independently certified here, and that general theorem is not
a premise of any new conclusion above. The small root-conditioned
pair proof in Section 6 is independent. If VII's general pair
exclusion is separately certified, Theorem 3.1 excludes all
variable-drift all-root-seven triples and removes the proper-pair
branch. Even with that theorem granted, the common-drift simultaneous
system (9.1)–(9.7) remains unresolved. Without it, a general losing
root-seven proper pair outside the new conditioned classes has not
been independently excluded here.

The exact residual question is whether some common $d,y,\zeta$
and three distinct positive parameters satisfy every condition of
Section 9, including rank one, the actual fifth reading, nonzero
samples, the shared sign and different-pair collisions. The theorem
proves both necessity and sufficiency; it proves neither emptiness
nor nonemptiness. Separate compatible pairs cannot replace this
joint feasibility problem. A failed search or a necessary eliminated
polynomial would not settle it. No search or numerical feasibility
claim is part of these results.

The unrestricted question still permits all other terminal-root
patterns, arbitrary drifts and gain signs, changing sources and
shapes, and every remaining degree and root multiplicity on the
same full ancestor. Different sixth actions may retain different
pairs; a shared-three sixth child may leave different terminal
actions colliding on different pairs, except in the strata actually
resolved by the stated reductions. A whole-class decoder for one
promised subset does not recover the unrestricted fiber.

No $MMJM$ or $MJMMJ$ history is identified with this $JMMJM$
history, and no common-prediction promise from another ancestor is
an extra observation here. The larger actual-fiber recovery problem,
the earlier $JMMJ$ joint losing-arm realization and the original-root
alternative of at least nine total readings versus a lawful decoder
with at most eight on every degree-three complete world all remain
unresolved. The continuing unrestricted mathematical goal is not
completed. No worldwide priority, literature completeness, general
neural-network, empirical, Lean/kernel, complexity, efficiency,
numerical stability or global-optimality certification is claimed.

## 追加锚（本行以下为增补区）
