# Native terminal span-five strict compensation

The local result is a strict surplus on a consecutive terminal support gap
$(n-5,n)$ in the original paid stationary threshold model. It holds for
all original middle-range parameters and costs, without an all-history
both-conflict hypothesis. The six-pair mechanism of [SI, Section 10][SI]
is reused; a fourth ambiguous diagonal supplies the additional unit.
[SI, Section 11][SI] already compensates arbitrary spans under its explicit
both-conflict condition. [TC, Sections 4--5][TC] already proves the exact
seven-coordinate Boolean minimum $16$, its stronger central-host and
collective bounds, and the full-fiber native minimum $20+r$. Those results
are inherited. The contributions here are the unconditional terminal local
unit, its exact same-graph consequences, the corresponding terminal-exception
class and its separating example, and the strict local seven-coordinate
corollaries. The unrestricted all-parameter aggregate remains an open problem.

## 1. The original paid graph and actual incidence

**Assumption 1.1 (parameters and complete Boolean graph).** Fix
$n\ge7$, $4\le k\le n-3$, positive integers
$s_1<\cdots<s_n$, and a nonnegative integer $r$. Set

$$
c_i=s_i+4,\qquad C_X=\sum_{i\in X}c_i,\qquad W=C_{[n]},
\qquad K=k,\quad L=n-k+1,\quad n=K+L-1,\quad G=KL.
$$

Thus $K,L\ge4$. A graph has a finite installed running set $Q$, a fixed
running start, two distinct terminals $\mathsf0,\mathsf1$ outside
$m=|Q|$, a fixed coordinate $i(q)\in[n]$ at each running state, and two
fixed successors $\delta(q,0),\delta(q,1)$. The current state is the
entire changing configuration. Every actual input $x\in\{0,1\}^n$
terminates with $\mathbf1_{\{|x|\ge k\}}$ and satisfies, on that same
input,

$$
t(x)\le n,\qquad J(x)=\sum_{\text{all running visits }q}c_{i(q)}\le W.
\tag{TS.1}
$$

All installed states count, including unused ones. Repeated-coordinate
queries and every query after certification are paid. Coordinate orders,
sharing, union cycles and inconsistent syntactic paths are allowed; only
actual runs must terminate. There is no additional history, counter, clock,
phase, selector or computed-address register. No order, global read-once
condition, level structure, unique host, unique support, unique residual,
nonresonance or disjointness of residual cones is assumed. Distinct
individual costs do not preclude equal sums of larger disjoint subsets.

**Definition 1.2 (actual histories and host excess).** A history is an
actual finite run prefix ending immediately before a query. Let $S$ be its
exposed coordinate set, with its particular exposed assignment, $h$ ones
and $z$ zeros. It is live when both outputs have completions, equivalently
when

$$
p=(h,z)\in V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\}.
$$

Let $F_p$ be the set of installed states hosting such histories,
$\mathcal S_p$ their support family, $b_p=|F_p|$, and
$a_p=|\mathcal S_p|$. Write

$$
\begin{aligned}
Q_{\rm live}&=\bigcup_{p\in V}F_p,&
\nu&=|Q\setminus Q_{\rm live}|,\\
d(q)&=|\{p\in V:q\in F_p\}|,&
D&=\sum_{q\in Q_{\rm live}}(d(q)-1),\\
E&=\sum_{p\in V}(b_p-1).
\end{aligned}
\tag{TS.2}
$$

The number $\nu$ includes unused and exclusively certified states. A state
live somewhere remains in $Q_{\rm live}$ even when another input visits
it after certification. Supports, counts and histories are proof indices,
not extra configuration supplied to the graph.

## 2. Credited live-history laws and exact localization

**Convention 2.1 (saturation and local separation).** The following are
the actual-history laws of [SB, Lemmas 2.2--2.4][SB] and
[SI, Theorem 2.2][SI]. Their ordinary arguments are included to specify
precisely which paid and actual-path premises enter the new local proof.
Every live query is fresh; a live history with support $S$ has exactly
$|S|$ preceding queries and charge $C_S$. At a common state, properly
nested supports are excluded, equal supports force equal hits, and
different supports cannot have equal hits. Distinct hosted cells, oriented
by $h<g$, satisfy

$$
g-h\ge2,\qquad z-w\ge2.
\tag{TS.3}
$$

Proof of the reused laws. From a live history, put $q=k-h$ and
$N=n-|S|$. Give one on the first $q-1$ distinct new exposures and zero
on the rest, preserving old answers on repeats. Before the last distinct
exposure both outputs remain possible. Correctness forbids a terminal;
finiteness and actual termination forbid an indefinitely repeating state
sequence. Thus all coordinates are exposed. A repeat at this or any
preceding live prefix would make this one actual completion pay more than
$n$ queries. All live queries and their ancestors are therefore fresh.
The completion has weight $k-1$, pays exactly $n,W$, and must halt
immediately after the last query. Giving zero on the first $N-q$ new
exposures and then one gives the dual saturated weight-$k$ completion.
This conclusion about immediate halting applies to these saturated runs;
it does not erase arbitrary paid certified traffic.

Suppose histories at one state have $S\subseteq T$ and hits $h,g$.
Replay a negative saturated suffix from $T$ after the $S$ history,
putting one on $T\setminus S$. The suffix queries only outside $T$
and halts; determinism makes it identical. Correctness gives
$h+|T\setminus S|\le g$. Replay the positive saturated suffix with
$T\setminus S$ zero to obtain $g\le h$. Thus $S=T$ and $g=h$.
Reverse containment is symmetric.

For incomparable supports put

$$
I=S\cap T,\quad X=S\setminus T,\quad Y=T\setminus S,
\quad U=[n]\setminus(S\cup T),\quad
 a=|X|,\ b=|Y|,\ u=|U|,
\quad Q_0=k-h,\quad V_0=k-g.
$$

The nonempty integer intervals

$$
[0,u]\cap[Q_0-b,Q_0-1],\qquad
[0,u]\cap[V_0-a,V_0-1]
\tag{TS.4}
$$

are disjoint. Otherwise choose a common $U$ assignment with weight in
both intervals. Each history stays live even after all $U$ is exposed.
Until then a common next state must query a coordinate fresh for both,
hence unread in $U$. Afterwards no such query remains, while a terminal
is still impossible. This contradicts correctness and termination on each
of the two separate actual completions. Their old $I$ assignments need
not agree. Equal hits would give the same clipped upper endpoint in
(TS.4), so cannot occur. For $h<g$, with $\Delta=g-h=Q_0-V_0$,
disjointness puts the second interval strictly below the first, giving

$$
u\ge1,\qquad Q_0\ge b+1,\qquad 1\le V_0\le u,
\qquad \Delta\ge b.
\tag{TS.5}
$$

Here and below $u=|U|$; it is distinct from the never-live count $\nu$.
If the old $X$ values are all zero, complete $T$ with $X$ zero,
its first $V_0-1$ fresh $U$ exposures one and the rest zero. This is a
negative saturated suffix reading all $X\cup U$ and halting. Replayed
after $S$, with any $Y$ assignment, it is still negative and has charges
$n+a-b$ and $W+C_X-C_Y$. Its own caps imply

$$
a\le b,\qquad C_X\le C_Y.
\tag{TS.6}
$$

If the old $Y$ values are all one, the dual positive saturated suffix
from $S$, with its first $b+u-Q_0$ new $U$ exposures zero and the
rest one, replays after $T$. Its charges give
$b\le a$ and $C_Y\le C_X$. These are paid private-polarity exchanges;
no charge from one input is added to a charge from another.

For completeness, let $\xi,\eta$ be the old one counts on $X,Y$ and put

$$
\delta_I=\Delta+\xi-\eta=(\Delta-b)+\xi+(b-\eta)\ge0,
\qquad \lambda=b+u-Q_0+1.
$$

If $\delta_I>0$, choose an integer

$$
\max(0,V_0-\xi)\le t\le\min(u,Q_0-\eta-1).
\tag{TS.7}
$$

The interval is nonempty by (TS.5), $\eta\le b$, and
$V_0-\xi\le Q_0-\eta-1$. Use the old $X$ values, old $Y$ values and
one common $U$ assignment of weight $t$ on both completions; retain each
history's own values on $I$. Their total weights are respectively at
most $k-1$ and at least $k$. Their common suffix must first split at an
old coordinate of $I$. Both histories are certified before that old query,
by live freshness. The negative certificate needs $\lambda$ new zeros
in $Y_0\cup U_0$; the positive one needs $V_0$ new ones in
$X_1\cup U_1$. Those sets and the discriminator coordinate are disjoint.
Thus, separately on each completed run, their suffix uses at least
$\lambda+V_0+1$ calls. If $A_-,A_+$ are these certificate coordinates
and $i$ the discriminator, the two caps give

$$
\begin{aligned}
\lambda+V_0+1&\le u+\min(a,b),\\
C_{A_-}+C_{A_+}+c_i&\le C_U+\min(C_X,C_Y).
\end{aligned}
\tag{TS.8}
$$

The calls proving the two certificates occur on the common suffix, so
both are paid on each of those runs. Substituting
$\lambda+V_0+1=b+u-\Delta+2$ yields
$\Delta\ge2+\max(0,b-a)$ and $z-w=\Delta+a-b\ge2$.
If $\delta_I=0$, then $\Delta=b$, $\xi=0$, $\eta=b$. Both
private-polarity exchanges apply, forcing $a=b=\Delta$ and $C_X=C_Y$.
Distinct individual costs exclude disjoint singleton private sets with
that equality; hence $\Delta\ge2$, again giving both gaps. Equality
of larger subset sums has not been excluded. This proves (TS.3).
$\square$

**Convention 2.2 (actual forks and singleton diagonals).** Every cell is
realized by a fresh live reply word. At fixed $p,q$ the support is unique,
so $b_p\ge a_p\ge1$. If a history at $q$ has support $S$ and counts
$(h,z)$, and its reply $\varepsilon$ has live child counts, then its
actual fixed successor hosts that child with support $S\cup\{i(q)\}$.
Axis cells have one host and one support. Adjacent cells
$(h,z),(h+1,z-1)$ on a diagonal have a common live parent $(h,z-1)$.
Forking any actual parent history gives child supports that are equal.
Consequently a consecutive string of cells with singleton support families
has one support throughout. In particular a diagonal is common-support
exactly when all its cells have singleton support families. Depth one is
always common-support, since both first replies expose the fixed start
label. These are [SI, Theorem 2.2 and the local argument of Theorem 4.1][SI].

Indeed a requested word with $h$ ones and $z$ zeros stays live at every
prefix, so freshness realizes it on a consistent actual completion. The
support uniqueness follows from equal-hit exclusion. Either reply at an
unread coordinate has a completion; its installed successor is running
when the child remains live. The deterministic all-zero and all-one spines
give the axis claim. The stated fork proves the diagonal assertion without
any singleton-parent assumption.

**Definition 2.3 (consecutive cuts and pools).** List all common-support
depths in $\{0,\ldots,n-1\}$, together with the formal endpoint $n$.
Their common supports are $T_d$, with $T_0=\varnothing$ and
$T_n=[n]$. Let $\mathcal I$ be the open gaps $I=(a,b)$ between
consecutive listed depths; the span is $b-a$. Define

$$
\begin{aligned}
V_I&=\{(h,z)\in V:a<h+z<b\},&
Q_I&=\bigcup_{p\in V_I}F_p,\\
E_I&=\sum_{p\in V_I}(b_p-1),&
D_I&=\sum_{q\in Q_I}(|\{p\in V_I:q\in F_p\}|-1).
\end{aligned}
$$

Let $E_{\rm reg}$ be the sum of $b_p-1$ on actual cut diagonals;
there is no live diagonal at the formal endpoint $n$.

The credited localization [SI, Lemma 9.2 and Theorem 9.3][SI] gives

$$
\begin{gathered}
|Q_I|=|V_I|+E_I-D_I,\qquad
m-G=\nu+E_{\rm reg}+\sum_{I\in\mathcal I}(E_I-D_I),\\
|Q_{\rm live}|=G+E-D,\qquad m-G=E-D+\nu.
\tag{TS.9}
\end{gathered}
$$

To see the localization directly, every live history extends to each later
live depth through actual fresh live children: away from the final corner
at least one reply stays live. Hence cut supports form a strictly increasing
chain of their indicated sizes. Inside a consecutive gap, ancestry and
extension give

$$
T_a\subseteq S\subsetneq T_b,\qquad i(q)\in T_b\setminus S.
\tag{TS.10}
$$

At $b=n$ this follows from freshness and $T_n=[n]$. Cut hosts are
exclusive by equal- and nested-support exclusion. The disjoint coordinate
blocks $X_I=T_b\setminus T_a$ partition $[n]$ and contain the labels
of all live states in the corresponding half-open depth range. Thus no live
state can belong to different ranges or different interior pools. Restricted
and global double counting give (TS.9). If $m_i$ counts all installed
coordinate-$i$ states, $\nu_I$ counts the never-live ones labelled in
$X_I$, and $E_a$ is the lower cut excess, the stronger same-vector identity
is

$$
m(X_I)-(|V_a|+|V_I|)=E_a+E_I-D_I+\nu_I,
\qquad \sum_I\nu_I=\nu.
\tag{TS.11}
$$

This includes empty interiors and all unused states. Certified visits do
not obey a live envelope and are not deleted by this proof decomposition.
Every internal diagonal of a consecutive nonempty gap is ambiguous and
therefore contributes at least one to $E_I$.

## 3. A fourth ambiguous diagonal in the six-pair device

**Lemma 3.1 (strict six-pair device).** Under Assumption 1.1, put
$d=n-4$ and define

$$
\begin{array}{ll}
 A=(K-4,L-1),&C=(K-3,L-2),\\
 Y=(K-2,L-3),&Z=(K-1,L-4),\\
 U=(K-3,L-1),&V'=(K-1,L-3).
\end{array}
\tag{TS.12}
$$

The first four cells lie at depth $d$, the last two at $d+1$.
Suppose one actual consecutive gap $I$ contains these two diagonals and
at least two other internal diagonals. Suppose every pair of different
cells sharing a state within $V_I$ is among

$$
AZ,\quad CZ,\quad AY,\quad UV',\quad AV',\quad ZU.
\tag{TS.13}
$$

Then $E_I-D_I\ge1$. This is a conditional application lemma; (TS.13)
is verified for the claimed applications, not imposed on arbitrary graphs.

Proof. The relation (TS.13) is the four-cycle $A-Z-U-V'-A$, with pendant
edges $C-Z$ and $A-Y$. It has no triangle. Three hosted cells at one state
would require a triangle, so every state with multiple cell incidences has
exactly two. Let $s$ count these states; then $D_I=s$. Regard each such
state as an edge of a multigraph, retaining parallel edges for distinct
states, and let $v\le6$ count its incident cells. At an incident cell,
the host count dominates its degree, so incident excess is at least
$2s-v$. The other internal diagonals are exclusive under (TS.13) and
each has ambiguity excess at least one. Consequently

$$
E_I\ge4,\qquad E_I\ge2s-v+2\ge2s-4.
\tag{TS.14}
$$

Assume $E_I\le D_I=s$. The two bounds force $s=E_I=4$, and then
$v=6$. There are exactly four internal diagonals, each with excess one;
any extra diagonal would make $E_I\ge5$. The two exclusive diagonals
already contribute two. Every incident host count therefore equals its
degree, and every other cell on the first two diagonals has one host.

Write $x,y,z_*,u_*,v_*,w_*$ for the multiplicities of
$CZ,AY,UV',AZ,AV',ZU$. Since the pendant cells are incident,
$x,y\ge1$. A $CZ$ state has a common live zero reply whose actual
successor hosts $U,V'$; an $AY$ state has a common live one reply with
those same child cells. Thus $z_*\ge1$, without successor injectivity.
Counting total edges and degrees on the two diagonals gives

$$
\begin{aligned}
x+y+z_*+u_*+v_*+w_*&=4,\\
2x+2y+2u_*+v_*+w_*-4&=1,\\
2z_*+v_*+w_*-2&=1.
\end{aligned}
\tag{TS.15}
$$

Nonnegative integrality gives $z_*=1$, $v_*+w_*=1$, $x=y=1$ and
$u_*=0$. If $v_*=1$, only $A$ on the first diagonal has multiple hosts.
Thus $C,Y,Z$ have singleton support families; the adjacent actual forks of
Convention 2.2 make all three supports equal. The existing $CZ$ state then
hosts equal supports with unequal hits, impossible. If $w_*=1$, only $Z$
has multiple hosts there; the same reasoning on $A,C,Y$ contradicts the
existing $AY$ state. These exhaust $v_*+w_*=1$. Hence $E_I>D_I$;
integer cardinalities give the asserted unit. $\square$

The multigraph, actual-successor forks and singleton-support contradiction
are the mechanism of [SI, Lemma 10.3 and Theorem 10.4][SI], also exposed in
[SB, Lemma 5.3 and Theorem 5.4][SB]. Their span-four application has three
ambiguous diagonals and proves nonnegative compensation. The change in
(TS.14) is the fourth actual ambiguous diagonal; the strict unit and its
applications below are the bounded extension.

## 4. Unconditional terminal span-five compensation

**Theorem 4.1 (strict terminal unit in every original graph).** For every
parameter choice and graph of Assumption 1.1, if $I_5=(n-5,n)$ is a
consecutive common-support gap, then

$$
E_{I_5}-D_{I_5}\ge1,\qquad
|Q_{I_5}|\ge |V_{I_5}|+1.
\tag{TS.16}
$$

No all-history conflict condition is required. No attainment or sharpness
of the lower margin one is asserted.

Proof. Since $K,L\ge4$ and $n=K+L-1$, the four internal diagonals
have the following complete cell lists:

| Depth | Cells |
| --- | --- |
| $n-4$ | $A,C,Y,Z$ of (TS.12) |
| $n-3$ | $U,M=(K-2,L-2),V'$ |
| $n-2$ | $(K-2,L-1),(K-1,L-2)$ |
| $n-1$ | $(K-1,L-1)$ |

A cell with $h\ge K-2$ and $z\ge L-2$ is exclusive relative to
every different cell of $V$ under (TS.3). A larger hit count would need
to be at least $K$; a smaller hit count would need a zero count at least
$L$. Equal hits at a different cell are also excluded. This accounts for
$M$ and both last diagonals.

On the first diagonal the two-gap rule allows only $AZ,CZ,AY$;
on the second, only $UV'$. To check the cross pairs explicitly, write
a first-diagonal cell as
$(K-4+i,L-1-i)$, $0\le i\le3$, and a second-diagonal cell as
$(K-3+j,L-1-j)$, $0\le j\le2$. From the first to the second
the hit increase and zero decrease are $(1+j-i,j-i)$.
Both are at least two only for $(i,j)=(0,2)$.
In the reverse orientation they are $(i-j-1,i-j)$, which are both
at least two only for $(i,j)=(3,0)$. These pairs are $AV'$ and $ZU$.
Thus (TS.13) exhausts all sharing in this pool.

Consecutivity makes all four internal diagonals genuinely ambiguous.
Lemma 3.1 applies with the last two as its additional exclusive diagonals,
giving $E_{I_5}-D_{I_5}\ge1$. Restricted double counting (TS.9)
gives the second inequality. The argument concerns the one original
installed graph, with no alteration to its certified continuations or
cost vector. $\square$

In particular $|V_{I_5}|=4+3+2+1=10$, so its live pool has at least
eleven states. This cardinality bound does not assert that a graph with
exactly eleven states in that pool exists.

## 5. Exact aggregate contribution and endpoint necessity

**Convention 5.1 (credited safe-gap surplus).** Put
$e_*=\max(K,L)$ and $d_*=\min(K,L)$, and retain the original partition

$$
\mathcal L_*=\{I=(a,b)\in\mathcal I:b-a\ge5,\ b>e_*\},
\qquad \mathcal A_*=\mathcal I\setminus\mathcal L_*.
\tag{TS.17}
$$

The safe-gap facts used here are [SI, Lemma 10.2, Theorem 10.4,
Corollary 10.5 and Proposition 10.9][SI], with the strict short units of
[SB, Section 4 and Theorem 5.6][SB]:

- A gap ending at $b\le e_*$ has $D_I=0$, at any span.
- Spans at most four satisfy $E_I-D_I\ge0$.
- Each span-two or span-three gap satisfies $E_I-D_I\ge1$.
- A terminal span-four gap $(n-4,n)$ satisfies $E_I-D_I\ge2$.

For clarity, their local mechanisms do not assume a realizable arbitrary
syntactic path. At the last internal layer a host with label $i$ has support
$T_b\setminus\{i\}$, excluding sharing by nested/equal-support exclusion.
If a shared pair had
$\min(g-h,z-w)\le n-b$, put
$M=\max(h+z,g+w)$ and $t=b-1-M$. The capacities
$A_1=K-1-g$, $A_0=L-1-z$ satisfy

$$
A_1+A_0-t=n-b-\min(g-h,z-w)\ge0.
$$

A common reply word of $t$ letters, with at most $A_1$ ones and $A_0$
zeros, therefore gives two actual live extensions to the exclusive last
layer: every common state queries fresh coordinates for both histories.
This contradiction proves both gaps at least $\max(2,n-b+1)$.
When $b\le e_*$, that bound is at least $d_*$, exceeding one of the
two count-range diameters, so sharing is impossible.

At span two the two possible internal supports demand opposite missing
labels, so $D_I=0$, while ambiguity gives $E_I\ge1$.
At span three, last-layer and cross-layer sharing are excluded; all sharing
is between the single possible pair of first-layer cells with opposite
singleton live-reply sets. If there are $s$ shared states, $D_I=s$.
The two ambiguous layers give
$E_I\ge\max(2,2s-1)$ and hence $E_I-s\ge1$.
At span four the credited fixed-successor classification is the six-pair
relation with its appropriate first two layers, and an exclusive last
layer. With three ambiguous layers it gives $E_I\ge3$ and
$E_I\ge2s-5$. A strict deficit would force $s=4,E_I=3$ and all
six incident cells. The pendant-edge degree equations are (TS.15);
the same singleton-support contradiction excludes that case. This is
nonnegative span-four compensation, not Lemma 3.1's strict extension.
At terminal span four only one extreme pair survives (TS.3).
Then $D_I=s$, and its three ambiguous layers give

$$
E_I-D_I\ge2+\max(1,2s-2)-s\ge2.
$$

No attainment of that terminal bound is part of these credited facts.

Let $\mathcal S$ be the set of span-two/three gaps, put
$b_{\rm short}=|\mathcal S|$, and let
$\tau=\mathbf1_{\{(n-4,n)\in\mathcal I\}}$. Define exactly the safe
remainder of [SB, Theorem 5.6][SB]:

$$
\begin{aligned}
\Xi={}&\sum_{I\in\mathcal S}(E_I-D_I-1)\\
&+\begin{cases}
 E_{(n-4,n)}-D_{(n-4,n)}-2,&\tau=1,\\
 0,&\tau=0,
 \end{cases}\\
&+\sum_{I\in\mathcal A_*\setminus(\mathcal S\cup\{(n-4,n)\})}
 (E_I-D_I),\\
R={}&\nu+E_{\rm reg}+b_{\rm short}+2\tau+\Xi.
\end{aligned}
\tag{TS.18}
$$

Each term of $\Xi$ is nonnegative. Empty span-one interiors contribute
zero. The local facts above and (TS.9) give the exact original identity

$$
m-G=R-\sum_{I\in\mathcal L_*}(D_I-E_I).
\tag{TS.19}
$$

It is essential that $R$ and the deficits are evaluated on the same graph;
they are not independently optimized block quantities.

**Theorem 5.2 (exact terminal extraction).** Let
$\rho=\mathbf1_{\{I_5\in\mathcal I\}}$, and define

$$
\eta_5=
\begin{cases}
E_{I_5}-D_{I_5}-1,&\rho=1,\\
0,&\rho=0.
\end{cases}
$$

Then $\eta_5\ge0$, and on every graph of Assumption 1.1,

$$
m-G=R+\rho+\eta_5
-\sum_{I\in\mathcal L_*\setminus\{I_5\}}(D_I-E_I).
\tag{TS.20}
$$

Consequently the original comparison $m\ge G$ is equivalent to

$$
\sum_{I\in\mathcal L_*\setminus\{I_5\}}(D_I-E_I)
\le R+\rho+\eta_5.
\tag{TS.21}
$$

Proof. If present, $I_5$ belongs to $\mathcal L_*$ and Theorem 4.1
gives its exact nonnegative excess $1+\eta_5$. Extract that actual summand
from (TS.19). If absent, both new terms are zero and the original identity
is unchanged. Rearranging proves the equivalence. A terminal span-four gap
cannot coexist with $I_5$, since consecutive gaps cannot overlap; retaining
$\tau$ in the formula therefore charges no second terminal margin.
$\square$

**Corollary 5.3 (another late endpoint is necessary for a saving).**
If $\rho=1$ and $m<G$, another positive-deficit gap must end at a depth

$$
b\in\{e_*+1,\ldots,n-5\}.
\tag{TS.22}
$$

There are $\max(0,d_*-6)$ such endpoints. In particular, if $I_5$ is
present and $d_*\le6$, then

$$
m\ge G+R+1+\eta_5,\qquad
|Q_{\rm live}|\ge G+(R-\nu)+1+\eta_5.
\tag{TS.23}
$$

Thus $d_*\ge7$ is necessary for a strict saving in a graph with $I_5$.

Proof. All other gaps precede $I_5$ and end at most $n-5$.
Under $m<G$, (TS.20) makes their total late deficit exceed the
nonnegative $R+1+\eta_5$, so at least one has positive deficit.
Its endpoint is after $e_*$ by (TS.17). The endpoint count is

$$
\max(0,n-5-e_*)=\max(0,d_*-6).
$$

For $d_*\le6$ there are no other late gaps at all, so (TS.20) becomes
(TS.23), using $m=|Q_{\rm live}|+\nu$. Nothing in this argument
excludes a saving in a graph without $I_5$ or controls the other late
pools when $d_*\ge7$. $\square$

## 6. SI11 mass balance and the corrected exception class

**Definition 6.1 (all-history masses and the existing SI11 condition).**
For each cell $p=(h,z)$, let $\mathscr H_p$ be all distinct actual live
prefixes with those counts, including their ending state; completing inputs
with the same prefix count only once. For $H$ define its exposed one and
zero sets $A_H,B_H$, and let

$$
\omega(H)=\binom{h+z}{h}^{-1},\qquad
\lambda(q)=\sum_{H\text{ live, ending at }q}\omega(H).
\tag{TS.24}
$$

A state is both-conflict when every two distinct such prefixes satisfy

$$
A_H\cap B_{H'}\ne\varnothing,\qquad
A_{H'}\cap B_H\ne\varnothing.
\tag{TS.25}
$$

The quantifier includes different prefixes in the same cell; choosing one
history per cell is not this condition. The existing class $\mathfrak C$
of [SI, Definition 11.6][SI] requires (TS.25) at every state in every pool
of $\mathcal L_*$, with no requirement on the safe pools or cut states.

The exact bridge [SI, Lemma 11.3 and Corollary 11.5][SI] is

$$
\sum_{q\in Q_I}\lambda(q)=|V_I|,\qquad
E_I-D_I=\sum_{q\in Q_I}(1-\lambda(q)).
\tag{TS.26}
$$

Indeed a reply word with $h$ ones and $z$ zeros has live counts at every
prefix, so freshness and fixed successors give exactly one actual prefix.
Conversely every such prefix has that word. There are
$\binom{h+z}{h}$ of them and their mass is one. Pool localization then
gives (TS.26).

The capacity bound $\lambda(q)\le1$ under (TS.25) is the classical
nonuniform Bollobás set-pairs inequality, used in [SI, Theorem 11.4][SI].
Here its elementary permutation proof also makes the precise hypothesis
visible. The set pairs have disjoint diagonals. They are distinct:
compatible old assignments at the same state would make one actual input
follow both prefixes, either identically or with a repeated state, contrary
to actual termination. In a uniform random ordering of their finite union,
the event that all of $A_H$ precedes all of $B_H$ has probability
$\binom{|A_H|+|B_H|}{|A_H|}^{-1}$. Two events cannot coexist under
both conflicts: an element of $A_H\cap B_{H'}$ would precede one of
$A_{H'}\cap B_H$ in the first event and follow it in the second.
Thus the events are disjoint and their probabilities sum to at most one.
A pair with an empty side forces a singleton family under (TS.25);
its weight is at most one directly. This is the mature set-pairs
inequality, not a new capacity theorem or a source probability law.

It follows that SI11 already proves $E_I-D_I\ge0$ at arbitrary span
whenever all states of that pool satisfy (TS.25). Determinism alone gives
at least one directed conflict between distinct prefixes; it does not give
both. At fixed cell and host, equal-hit support uniqueness fixes one support,
and distinct equal-sized one sets give both conflicts. The additional
SI11 hypothesis concerns cross-cell histories as well.

**Theorem 6.2 (unconditional terminal mass surplus and exact residual mass
target).** Define, on each pool,

$$
O_I=\sum_{q\in Q_I}(\lambda(q)-1)_+,\qquad
S_I=\sum_{q\in Q_I}(1-\lambda(q))_+,\qquad x_+=\max(x,0).
$$

Then $D_I-E_I=O_I-S_I$. If $\rho=1$,

$$
S_{I_5}-O_{I_5}=1+\eta_5\ge1.
\tag{TS.27}
$$

Let $O_{\rm rem},S_{\rm rem}$ sum over
$\mathcal L_*\setminus\{I_5\}$. The original universal comparison on
this graph is exactly

$$
O_{\rm rem}\le S_{\rm rem}+R+\rho+\eta_5.
\tag{TS.28}
$$

Proof. Split positive and negative parts in (TS.26), then apply
Theorems 4.1 and 5.2. This is SI11's collective balance with one actual
terminal contribution extracted; it neither assumes pointwise capacity
nor requires separate compensation of all other late gaps. $\square$

**Definition 6.3 (two terminal classes).** Let $\mathfrak A_5$ consist
of graphs for which $\mathcal L_*\subseteq\{I_5\}$. Let
$\mathfrak C_5$ consist of graphs satisfying (TS.25) at every state of
every pool in $\mathcal L_*\setminus\{I_5\}$. No conflict condition is
placed on $I_5$ itself. These are explicit qualified classes; neither
is asserted to contain all original competitors.

**Theorem 6.4 (qualified exact minima with retained slack).** Every
graph in $\mathfrak C_5$, hence every graph in $\mathfrak A_5$, satisfies

$$
\begin{aligned}
m&\ge G+R+\rho+\eta_5
 \ge G+\nu+E_{\rm reg}+b_{\rm short}+2\tau+\rho,\\
|Q_{\rm live}|&\ge
G+(R-\nu)+\rho+\eta_5.
\end{aligned}
\tag{TS.29}
$$

For every original $n,k,A$, the minimum $m$ in either class at both
caps is exactly $G$. The subclass forced to have $I_5$ has at least one
additional state, without an asserted attained minimum. The class
$\mathfrak C_5$ contains $\mathfrak C$ and $\mathfrak A_5$.
The inclusion $\mathfrak C\subseteq\mathfrak C_5$ is strict across the
original parameter family; no strictness claim is made separately at every
fixed parameter instance.

Proof. SI11 capacity makes each other late contribution $E_I-D_I$
nonnegative. Theorem 4.1 treats $I_5$ without a conflict condition.
Substitute in (TS.20) and remove $\nu$ for the live count. A graph in
$\mathfrak A_5$ has no other late pool, so meets the condition vacuously.
The fixed-order grid has one state $q_{h,z}$ per cell, label $h+z+1$,
zero successor $q_{h,z+1}$ unless $z=L-1$, when it is $\mathsf0$,
and one successor $q_{h+1,z}$ unless $h=K-1$, when it is $\mathsf1$.
It starts at $q_{0,0}$. The actual counts are its invariant; it reads a
prefix of $1,\ldots,n$ and is correct at both caps. An input with
$K-1$ ones and $L-1$ zeros before the last query pays $n,W$ together.
Every depth has one common support and every cell one host, so all gaps
have span one and all slack vanishes. This gives equality in both classes.
Inclusion of $\mathfrak C$ is immediate by dropping only its condition
on $I_5$. Proposition 7.2 supplies a complete graph in
$\mathfrak C_5\setminus\mathfrak C$, proving strictness. $\square$

The plain terminal-only class $\mathfrak A_5$ is not a superset of SI11's
$\mathfrak C$. Over the complete original parameter family the two are incomparable.
Proposition 7.2 is in
$\mathfrak A_5\setminus\mathfrak C$. In the other direction, the already
proved [SI, Proposition 11.8][SI] at $v=4$ gives $n=12,k=6,s_i=i$,
belongs to $\mathfrak C$, and has the sole late terminal gap $(6,12)$
of span six, so is outside $\mathfrak A_5$. That existing interacting
family has unbounded late spans and is above-grid. Its $v=3$ member
already has terminal span five inside $\mathfrak C$. The additional
content of Theorem 4.1 is unconditional strict local compensation,
including graphs outside that sufficient class.

## 7. Complete original-model witnesses for the class distinctions

**Proposition 7.1 (terminal nonvacuity at every original cost vector).**
For every parameter choice of Assumption 1.1 there is a complete correct
graph at both caps with consecutive gap $I_5$, all other gaps of span one,
and $2^n-1$ running states. It belongs to both $\mathfrak A_5$ and
$\mathfrak C$. It separates $\mathfrak A_5$ from SI10's class with
no late gap of span at least five; it does not separate from SI11's
$\mathfrak C$.

Proof. Set $a=n-5\ge2$ and install a distinct state $q_v$ for every
binary word $v$ of length $d<n$, with start $q_\varepsilon$.
For $d<a$, its fixed label is $d+1$. For $d\ge a$ put
$j=d-a+1\in\{1,\ldots,5\}$. If the first bit of $v$ is zero,
the label is $a+j$. If that bit is one, the label is $a+j+1$
for $j\le4$ and $a+1$ for $j=5$.
For $d<n-1$ the $\epsilon$ successor is $q_{v\epsilon}$;
at $d=n-1$ it is terminal one exactly when $v\epsilon$ has at
least $k$ ones. This specifies every fixed row, including rows only
visited after certification. The first-bit information is contained in
the counted state name, not supplied by an external selector.

Every input reads coordinates $1,\ldots,a$ and then one of the two
permutations

$$
(a+1,a+2,a+3,a+4,a+5),\qquad
(a+2,a+3,a+4,a+5,a+1).
$$

Thus every word is an actual consistent reply word, every input is correct,
and every run pays exactly $n,W$. There are $2^n-1$ running vertices;
the two terminals remain outside $m$. The graph is above-grid: choose
one distinct live vertex for each cell, and also the exclusively certified
vertex $q_{0^L}$, which exists because $L<n$.

Every depth through $a$ has a fixed-prefix support. At depth $a$, the
cell $(K-3,L-3)$ has both counts positive, so actual prefixes with either
specified first reply exist. At the next four depths choose the additional
counts respectively

$$
(1,0),\quad(1,1),\quad(1,2),\quad(2,2).
$$

Both branch orders realize these counts with live prefixes. Their supports
at each depth $a+j$, $1\le j\le4$, differ: one includes $a+1$ and
omits $a+j+1$, while the other does the reverse. Hence each such depth is
ambiguous and $a,n$ are consecutive cuts. Every earlier gap has span one.
Each installed tree vertex has one incoming prefix, so every live state
satisfies (TS.25) vacuously. This proves both claimed memberships and
explains why this witness supplies no separation from $\mathfrak C$.

The full-fiber lift of Section 9 uses exactly $2^n-1+4+r$ preparation
states at caps $n+1,W+3$, preserving all rows and their paid visits.
It is an above-grid realization, not an attained example of margin one.
$\square$

**Proposition 7.2 (a terminal span-five graph outside SI11's class).**
For $n=7,k=4,s_i=i$, there is a complete original graph with $106$
running states, correct at caps $7,56$, whose sole late gap is $(2,7)$.
It lies in $\mathfrak A_5\subseteq\mathfrak C_5$ and outside
$\mathfrak C$. Its faithful native lift has $110+r$ preparation states
at caps $8,59$ on the whole original fiber. Neither count is an optimum
claim.

Proof, fixed finite table. Write

$$
t=1,\quad \text{core}=\{1,2\},\quad x=4,\quad y=3,
\quad u_1=5,\quad u_2=6,\quad u_3=7.
$$

Start from the full depth-seven binary query tree with all $127$ running
vertices distinct, start at its root, and two distinct common terminals
outside $m$. Query $1$, then $2$. In the core-$11$ subtree the
remaining fixed order is $(y,x,u_1,u_2,u_3)$; in every other core
subtree it is $(x,y,u_1,u_2,u_3)$. Every internal edge has its distinct
child, and every final edge has the threshold-four output of its complete
reply word. These are fixed labels at separate vertices, and every path
reads a permutation.

Delete the entire running subtree after each of the two reply prefixes

$$
\text{low}: (1,2,x)=(0,0,1),\qquad
\text{high}: (1,2,y)=(1,1,1).
\tag{TS.30}
$$

The roots are at depth three and each deleted subtree has fifteen running
vertices. Redirect the two incoming edges to one new state $H$. Retain
all other tree rows and leaf outputs, and install exactly these nine new
distinct running rows:

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $H$ | $u_1$ | $V$ | $B$ |
| $V$ | $u_2$ | $X$ | $S$ |
| $X$ | $x$ | $F$ | $J$ |
| $F$ | $u_3$ | $\mathsf0$ | $\mathsf1$ |
| $S$ | $u_3$ | $J$ | $Y$ |
| $Y$ | $y$ | $\mathsf0$ | $\mathsf1$ |
| $B$ | $u_2$ | $S$ | $O$ |
| $O$ | $y$ | $F$ | $\mathsf1$ |
| $J$ | $t$ | $\mathsf0$ | $\mathsf1$ |

No row targets a deleted vertex. This table and the retained-tree rule
specify both successors and the literal coordinate of every installed state.

Proof, correctness and termination on all inputs. Inputs avoiding (TS.30)
follow the full-scan permutation tree and are correct. Low has one old one,
so its residual is threshold three on $\{y,u_1,u_2,u_3\}$, with old
$x=1,t=0$. High has three old ones, so its residual is OR on
$\{x,u_1,u_2,u_3\}$, with old $y=1,t=1$.

If $u_1=0$, state $V$ queries $u_2$. For $u_2=0$, low is negative:
$X$ rereads its $x=1$ and $J$ returns its old $t=0$. High still needs
$x\lor u_3$: $X$ sends $x=1$ through $J$ to one, and $x=0$
through $F$ to $u_3$. For $u_2=1$, low needs $y\land u_3$ and
high is positive. State $S$ sends $u_3=0$ through $J$ to low zero
or high one; with $u_3=1$, $Y$ reads the free low $y$ or the old
high $y=1$, giving the correct output.

If $u_1=1$, high is positive and low needs at least two of
$y,u_2,u_3$. State $B$ with $u_2=0$ uses the same $y\land u_3$
routine $S$. With $u_2=1$ it uses $O$, computing $y\lor u_3$
on low; on high the old $y=1$ gives one immediately. These cases exhaust
both contexts. Every new path is finite, as is every retained tree path.

Proof, both paid caps on each actual input. Prefixes cost three calls
and respectively $C_{\{1,2\}}+c_x$ or $C_{\{1,2\}}+c_y$.
Every new suffix has at most four calls. The following are all possible
suffix coordinate sequences; the entries are their complete-run excess
$J-W$ in the respective context:

| Suffix sequence | Low excess | High excess |
| --- | --- | --- |
| $(u_1,u_2,x,u_3)$ | impossible | $0$ |
| $(u_1,u_2,x,t)$ | $c_x+c_t-c_y-c_{u_3}$ | $c_t-c_{u_3}$ |
| $(u_1,u_2,u_3,t)$ | $c_t-c_y$ | $c_t-c_x$ |
| $(u_1,u_2,u_3,y)$ | $0$ | $c_y-c_x$ |
| $(u_1,u_2,y,u_3)$ | $0$ | impossible |
| $(u_1,u_2,y)$ | $-c_{u_3}$ | $c_y-c_x-c_{u_3}$ |

The impossible entries follow from low's old $x=1$ and high's old
$y=1$. Here $c_t=5,c_x=8,c_y=7,c_{u_3}=11$ and
$W=5+6+7+8+9+10+11=56$, so every displayed excess is nonpositive.
In particular $c_x+c_t\le c_y+c_{u_3}$ pays the only potentially
two-coordinate repeat trade. All repeats of $x,y,t$ and every certified
visit have been included. Untouched inputs still read all seven coordinates,
attaining both $7,56$ on the same run.

Proof, installed count. The two deleted subtrees are disjoint. Exactly
$127-2\cdot15+9=106$ running states remain. Retained vertices are all
reachable by their original prefixes. The new states $V,X,B,S,O$ occur
after the corresponding choices of $u_1,u_2$; $F$ is reached from high
with $u_1=u_2=x=0$, $Y$ from low with
$u_1=0,u_2=u_3=1$, and $J$ from low with $u_1=u_2=0$ and its
old $x=1$. Thus no new row has an unmentioned installation status.
The number is strictly above $G=16$.

Proof, consecutive gap. Depths zero, one and two have fixed-prefix supports.
The following pairs give different actual live supports at every later
internal depth:

| Depth | First actual live history | Second actual live history |
| --- | --- | --- |
| $3$ | low at $H$: $(h,z)=(1,2)$, support $\{1,2,x\}$ | high at $H$: $(3,0)$, support $\{1,2,y\}$ |
| $4$ | low, $u_1=0$, at $V$: $(1,3)$, support $\{1,2,x,u_1\}$ | high, $u_1=0$, at $V$: $(3,1)$, support $\{1,2,y,u_1\}$ |
| $5$ | low, $u_1=0,u_2=1$, at $S$: $(2,3)$, support $\{1,2,x,u_1,u_2\}$ | high, $u_1=u_2=0$, at $X$: $(3,2)$, support $\{1,2,y,u_1,u_2\}$ |
| $6$ | low, $u_1=0,u_2=u_3=1$, at $Y$: $(3,3)$, support $\{1,2,x,u_1,u_2,u_3\}$ | high, $u_1=u_2=x=0$, at $F$: $(3,3)$, support $\{1,2,y,u_1,u_2,x\}$ |

All earlier prefixes of these live histories are live. The common-support
criterion in Convention 2.2 therefore makes depths three through six
ambiguous, while $2$ and the formal endpoint $7$ are consecutive cuts.
The other gaps have span one. Hence the graph is in $\mathfrak A_5$.

Proof, failure of the SI11 sufficient condition. State $H$ has exactly
two live incoming prefixes, reply words $001$ and $111$. Their set pairs
are

$$
(A_{\rm low},B_{\rm low})=(\{x\},\{1,2\}),\qquad
(A_{\rm high},B_{\rm high})=(\{1,2,y\},\varnothing).
$$

One directed intersection is empty and the other is $\{1,2\}$.
Moreover

$$
\lambda(H)=\binom31^{-1}+\binom33^{-1}=\frac43>1.
\tag{TS.31}
$$

Since $H$ is in the sole late pool $I_5$, the graph is outside
$\mathfrak C$ and inside $\mathfrak C_5$. This proves the asserted
strict class separation using an actual complete paid graph. Its overload
does not imply a total deficit: Theorem 4.1 gives
$S_{I_5}-O_{I_5}\ge1$ despite this overloaded state.

Proof, full-fiber native realization. Replace each retained or new
coordinate-$i$ row by the literal $a_i=LLL L^iR$, with branch following
the one edge and alpha, beta and absent separately following the zero edge.
Replace terminals by the original latches and add precisely the profile
rows $D,T$ of Section 9 and all $r$ additional mandated latches.
Thus every native successor is specified by the displayed table and the
retained-tree rule. The full-fiber proof in Section 9 applies to this
every-input Boolean proof and pays each actual visit. It gives
$106+4+r=110+r$ preparation states and caps $8,59$, with the original
complete reader separately paid. Actual cube origins of untouched
full-scan vectors attain the two maxima together. $\square$

## 8. Strict local seven-coordinate corollaries and inherited TC optima

**Corollary 8.1 (each possible late pool on seven coordinates).** For
$n=7,k=4$ and every original position vector, each actual gap in
$\mathcal L_*$ has $E_I-D_I\ge1$. The only possible such gaps are
$(1,6),(1,7),(2,7)$. Consequently

$$
m-16\ge
\nu+E_{\rm reg}+b_{\rm short}+2\tau+|\mathcal L_*|.
\tag{TS.32}
$$

These are local consequences of Lemma 3.1. The numerical optimum $16$
is already [TC, Corollary 4.2][TC], not an additional optimum theorem.

Proof. If an all-zero-axis history and an all-one-axis history share a
state, equal or nested supports are already excluded. For incomparable
supports the old private $X$ values are zero and old private $Y$ values
are one. Both paid exchanges in Convention 2.1 give $a=b$ and $C_X=C_Y$;
the two supports therefore have equal sizes. Thus opposite-axis histories
of different depths cannot share a state. At depth two both supports contain
the fixed start coordinate. If they differ, their private sets are disjoint
singletons, and $C_X=C_Y$ contradicts distinct individual costs. Equal
supports are forbidden by unequal hits. Hence $(0,2),(2,0)$ cannot share.

In $\{0,1,2,3\}^2$, (TS.3) permits exactly the nine pairs

$$
\begin{gathered}
(0,2)(2,0),\ (0,2)(3,0),\ (0,3)(2,0),\\
(0,3)(3,0),\ (0,3)(2,1),\ (0,3)(3,1),\\
(1,2)(3,0),\ (1,3)(3,0),\ (1,3)(3,1).
\end{gathered}
$$

This list follows by $h=0,1$, $g\ge h+2$, $z\ge2$ and $w\le z-2$.
The first three are excluded by the preceding axis arguments. The remaining
six are exactly $AZ,CZ,AY,UV',AV',ZU$ at depths three and four,
with $A=(0,3),C=(1,2),Y=(2,1),Z=(3,0),U=(1,3),V'=(3,1)$.
All other cells are exclusive relative to different count cells.

Depth one is a mandatory cut. A gap of span at least five ending after
$e_*=4$ can therefore only be $(1,6),(1,7),(2,7)$.
Each contains depths three and four and at least two other ambiguous
internal depths; all its sharing is among the six displayed cells.
Lemma 3.1 gives the unit on each. Substitution in (TS.19), retaining
$\Xi\ge0$, proves (TS.32). No cone lower bounds have been added.
$\square$

**Convention 8.2 (the stronger current seven-coordinate results).**
For exactly this unrestricted $n=7,k=4$ graph and every original $A$,
[TC, Theorem 4.1 and Corollaries 4.2--4.3][TC] already gives

$$
\begin{gathered}
|Q_{\rm live}|\ge16+\max(0,b_{1,1}-2),\\
m\ge16+\nu+\max(0,b_{1,1}-2),\qquad \min m=16,\\
\sum_{I\in\mathcal L_*}(D_I-E_I)
\le E_{\rm reg}+\sum_{I\in\mathcal A_*}(E_I-D_I)
-\max(0,b_{1,1}-2).
\tag{TS.33}
\end{gathered}
$$

This central-host and collective statement is stronger than merely
$m\ge16$; it is retained as current coverage. Its proof counts coherent
representative forks and an additional actual successor when both remaining
collisions occur, using distinct successors at live states. It is not a
local nonnegative assertion for every late pool. Corollary 8.1 supplies
the separately proved strict local inequalities; no new numerical novelty
is assigned to their weaker whole-graph consequence.

Likewise [TC, Corollary 5.1][TC] already gives the full-fiber preparation
minimum $20+r$ at caps $8,W+3$, with the complete eight-state reader
separate. TC Corollary 5.2 gives $m(R)\ge16$, and its selected native
analogue $M(R)\ge16$, at every actual residual-seven/threshold-four
prefix, without an inherited-cut condition. Such prefixes exist throughout
the original middle range: their counts are
$(k-4,n-k-3)$ at depth $n-7$. TC Corollary 5.3 further gives
$\sum_{i\ne j}m_i\ge16$ at $n=8,k=4$ or $5$, where $j$ is the
start label, and forces $m_j=1$ in any hypothetical $m=17$ graph.
Those are inherited one-vector constraints, not disjoint cone allocations.
The earlier cross-cone boundary in [SB, Corollary 6.3][SB] does not leave
the seven-coordinate optimum unresolved in the presence of these TC results.

## 9. Full-fiber native transport and the literal complete reader

**Assumption 9.1 (original source, prescribed code and paid native
apparatus).** Retain the ordered finite-tree algebra

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\quad \rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

At $P=\{L,R\}^3$, the current complete row $R_*$ has the perfect
ordered exterior and whole-subtree classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,\quad
\{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4,
$$

with different classes disequal. Use the entire fiber

$$
\mathcal U_*=\{u\in\mathcal T:R_P(\rho u)=R_*\},
$$

with no bound on source size, depth or branch shape. The complete
predecessor row retains ordered exterior, all reached occurrences,
canonical equality partition, repetitions, surviving disequalities and
strict-prefix blocking guards.

The image algebra has the disjoint cases
$\beta$, $E=\langle\beta,\alpha\rangle$, and pairs of image children;
$\alpha$ itself is not an image. Its recursive inverse sends $\beta$
to $\alpha$, $E$ to $\beta$, and an image-child pair to the pair of
inverses. Structural induction proves both inverse identities. Applied
at the four depth-two parents, these cases give the eleven profiles exposed
in [SB, Definition 1.1][SB]. On $\Pi_j$, right class $b_j$ is alpha,
its left class is beta ($a$ for $j=1,2$, $c$ for $j=3,4$), and the
other classes are branches. On $Z_d$ only class $d$ is beta, for one of
the six classes; on $Z_*$ all six roots are branches. Different-class
disequalities remain in force. An alpha must be the right child of $E$;
the distinct right classes allow at most one such collapse. Without a
collapse each class is an image root, beta or branch, with at most one beta
class. This explains exhaustiveness without restricting branch interiors.

For the original positions define

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad
\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}.
$$

Alpha, beta and absent separately give zero. The required literal code is

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in any other zero profile}.
\end{cases}
\tag{TS.34}
$$

Each native running state has one fixed finite absolute query word and four
separately fixed successors, in reply order alpha, beta, branch, absent.
A query at or below any finite word, including the empty word, is permitted;
descent beyond a leaf gives absent. Every running visit makes a query and
pays one call and its full word length. Constant, root, absent, repeated
and certified invocations all count. There are no silent running edges.
The current counted state is the entire changing configuration. All
installed running states, the two original distinct latches
$\widehat e_0,\widehat e_1$ and every one of the $r$ further mandated
distinct latches count, including unused ones. Every source terminates
at precisely $\widehat e_{\sigma_{A,k}(u)}$.

Register binding, acquired authenticated same-version row, lawful original
root permission, actual export, complete access isolation, paid code-only
handoff, lawful complete entry and stationary truthful service are separate
supplied assumptions. No free source copy, archive, inverse evaluation,
history, clock, counter, computed address, restriction, reset, entry
reselection or service is added.

**Convention 9.2 (the separately priced complete reader).** Put
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. Let $R_0=R_*$; let $R_j$
replace the two sibling holes $q_jL,q_jR$ by concrete beta at $q_j$,
canonically restricting the surviving occurrence partition and retaining
all surviving disequalities and guards. The other occurrence of the
repeated left class remains a hole. Injectivity of the image inverse
preserves equality and disequality of surviving holes, so these are the
complete predecessor rows on the respective profiles.

For the fixed supplied order $i_1,i_2$ of $\{1,2\}$, the original
reader is literally

| Running entry | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $e_0$ | $q_{i_1}R$ | $H_{i_1}$ | $H_0$ | $Q_2$ | $H_0$ |
| $Q_2$ | $q_{i_2}R$ | $H_{i_2}$ | $H_0$ | $H_0$ | $H_0$ |
| $e_1$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

Halt $H_j$ returns the whole $R_j$, not merely a root-type summary.
The profile classification verifies each row: the possible alpha right
child identifies the collapsed parent, while the prescribed code chooses
the appropriate entry group. On $Z_{b_3}$ either entry yields the zero
row, but (TS.34) still prescribes which literal entry must be prepared.
Preparation first ends at $\widehat e_\sigma$; the separately supplied
paid code-only handoff then enters exactly $e_\sigma$ on the same register.
The three running states and five complete-row halts are eight installed
reader states, with at most two fresh calls and six fresh letters, all
separate from preparation. No reader entry is a preparation latch.
This is the complete reader of [SB, Remark 1.5][SB], reused unchanged.

**Convention 9.3 (faithful lower and upper interface).** Write
$\mathsf N(H,p,\ell)$ for uniform full-fiber feasibility under Assumption
9.1, and $\mathsf B(m,t,J)$ for Boolean threshold feasibility with the
same original costs. The reused exact interface
[SB, Theorem 1.4][SB], equivalently SI (SI.5) and TC (TC.1), is

$$
\mathsf N(H,p,\ell)\ \Longleftrightarrow\
\mathsf B(H-4-r,p-1,\ell-3).
\tag{TS.35}
$$

Its lower direction is a cube projection only; its upper direction is
correct on the full unbounded fiber. The proof below records the offsets
needed by the new consumer, without a graph-normalization claim.

For the lower witness, put $G_0=\langle\beta,\beta\rangle$,
$C_0=G_0$, $C_{v+1}=\langle C_v,\beta\rangle$, and take comb depth
at least $s_n$. At each prefix-free word $w_i$, replace its beta by
$G_0$ precisely for bit one. The resulting $B_\theta$ is a branch image.
Choose four pairwise distinct fixed branch images outside the finite family
of all $B_\theta$, use them at $c,b_1,b_2,b_4$, use $B_\theta$
at both $a$ occurrences and beta at $b_3$, and take the image inverse
after filling the exterior. This is an actual finite origin in $Z_{b_3}$
for every vector, with all original repetitions, disequalities and guards.
The occurrence identity is
$r_{\rho u}(pv)=r_{x_{[p]}}(v)$. On this cube the only nonconstant words
are the pairwise disjoint classes

$$
E_i=\{p w_i v:p\in\{LLL,LRL\},\
                    v\in\{\varepsilon,L,R\}\}.
\tag{TS.36}
$$

At the roots, bit zero/one gives beta/branch; at their children it gives
absent/beta. Proper prefixes are branch and deeper extensions absent
in both cases. Every selected word has length at least $c_i=s_i+4$.

For each negative cube input, changing $c$ to beta and $b_3$ to alpha
gives an actual $\Pi_3$ source of opposite code, with unchanged selected
replies. For each positive cube input, changing only $b_3$ to a fresh
branch image gives an actual $Z_*$ source of opposite code and the same
selected replies. All differences begin at depth three. Correctness
therefore forces at least one nonselected query of length at least three
on that very cube run. This is a same-input mandatory charge.

Independently, start with a $Z_c$ source whose other classes are distinct
branch images. Changing just $b_3$ to alpha gives the opposite-code
$\Pi_3$ profile and forces an installed word in the cone
$RLR\{L,R\}^*$. Changing instead just $b_4$ to alpha gives $\Pi_4$
and forces an installed word in $RRR\{L,R\}^*$. The cones are disjoint
and outside every $E_i$. If $M$ counts all installed selected running
states, including unused ones, these two installed states and the $2+r$
latches give $M\le H-4-r$.

Retain each selected state reached on some cube input as a Boolean state
of its coordinate class. Follow its two bit-dependent native edges and
suppress intervening cube-constant chains. Each realized chain is finite
by actual termination; the initial chain reaches a selected state because
threshold is nonconstant. Complete unrealized selected edges arbitrarily
by terminals. For each vector, induction follows exactly its own actual
selected-state subsequence, so no completed impossible edge becomes actual.
The result is a complete correct terminating Boolean graph, without state
copying, and with simultaneous same-input inequalities

$$
m\le M\le H-4-r,\qquad
t_B(\theta)+1\le q_P(u_\theta),\qquad
J_B(\theta)+3\le \ell_P(u_\theta).
\tag{TS.37}
$$

Every selected visit, including repeats, is retained and charged at least
its $c_i$. The other offsets are paid on that same source run.

Conversely, lift every installed Boolean coordinate-$i$ state to the
shortest literal $a_i$. Branch follows its one successor; alpha, beta and
absent each have a separately installed zero successor. Replace the Boolean
terminals by the original latches, and add exactly these two profile rows:

| Profile state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | Boolean start | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

Start at $D$ and install all $r$ further mandated latches even unused.
On every $Z_{b_3}$ source, its arbitrary branch image defines one static
Boolean indicator vector. The occurrence identity identifies the whole
selected run, including repeated or certified visits, with that Boolean
run. This works for noncomb shapes and absent selected addresses.
At $D$, alpha is $\Pi_3$, beta is $Z_{b_3}$, and in the branch
case only alpha at $T$ gives the remaining code-one profile $\Pi_4$.
All other routes require zero. Thus the lift is correct on the full fiber
with exactly $m+4+r$ preparation states, at most $1+t$ calls and
$3+J$ letters on selected routes, and at most two calls/six letters
otherwise. Every correct threshold graph has an actual input exposing all
coordinates by the saturation adversary, so feasible Boolean bounds satisfy
$t\ge n,J\ge W$; the short profile routes fit those shifted bounds.
Negative bounds are infeasible by definition and (TS.37).
This proves the uniform interface (TS.35), not pointwise normalization of
an arbitrary native computation.

**Theorem 9.4 (qualified full-fiber consumers with the terminal unit).**
Let one complete original native preparer satisfy caps $n+1,W+3$,
and let its supplied Boolean projection be the graph in (TS.37).
If that graph belongs to $\mathfrak C_5$ or $\mathfrak A_5$, then

$$
H\ge G+4+r+R+\rho+\eta_5
\ge G+4+r+\nu+E_{\rm reg}+b_{\rm short}+2\tau+\rho.
\tag{TS.38}
$$

In either projected class the exact preparation minimum is $G+4+r$.
A projection with $I_5$ has at least one additional state; no attainment
with that forced gap is asserted. If the projection has $I_5$ and
$d_*\le6$, the stronger first bound holds without a separately imposed
conflict condition on its other pools. These statements hold for every
original $A$ and every $r\ge0$.

Proof. Apply Theorem 6.4, or Corollary 5.3 in the last case, to that
one projected graph and use $m\le H-4-r$. Its $\nu$, cuts, masses
and excesses are properties of that graph; they are not asserted for an
unrelated native history index. The grid in Theorem 6.4 and the complete
four-reply upper just proved attain $G+4+r$ on the entire fiber, with
the original code, literal latches and complete entries. The cube supplies
one origin attaining both caps together. The eight reader states and its
fresh costs remain separate. This proves the claimed class minima and
preserves the forced-gap lower bound without an attainment claim.
$\square$

For $n=7,k=4$, (TS.35) applied to the existing TC optimum gives the
already known $20+r$. Its upper has the sixteen grid states, two profile
states, two original latches and $r$ additional latches, with both native
caps $8,W+3$. The full-fiber and reader arguments above specify exactly
which existing result is reused; no new native numerical optimum is claimed.

## 10. Actual-prefix consumers on the same installed vector

**Corollary 10.1 (qualified residual terminal slack).** Fix one actual
live prefix of an original graph, with support $S$, particular assignment
and $h$ ones. Put

$$
R_0=[n]\setminus S,\qquad N=|R_0|,\qquad q=k-h.
$$

Suppose $N\ge7$ and $4\le q\le N-3$. Let $P_0$ be the no-copy
residual graph of this prefix. If $P_0\in\mathfrak C_5$ for its own
parameters, or if it has its own terminal span-five gap with
$\min(q,N-q+1)\le6$, then

$$
m(R_0)\ge
q(N-q+1)+\nu_0+E_{{\rm reg},0}
+b_{{\rm short},0}+2\tau_0+\rho_0+\Xi_0+\eta_{5,0}.
\tag{TS.39}
$$

All subscript-zero quantities concern that same residual graph. For a
native preparer and its supplied cube projection, with $M_i$ counting all
installed native states in $E_i$, the corresponding actual live prefix
satisfies the same lower bound for
$M(R_0)=\sum_{i\in R_0}M_i$.

Proof. Live freshness gives prefix charges $|S|,C_S$, so every completion
has remaining caps $N,C_{R_0}$. Freeze precisely its actual old assignment,
retain the $R_0$-labelled states reached on those completions, and suppress
fixed-$S$ chains. A realized chain is finite and ends at a retained state
or terminal. The initial chain reaches a retained state because the
residual threshold is nonconstant. Arbitrarily completing unrealized edges
does not make them actual: inputwise induction follows each original
$R_0$-state subsequence. The residual graph is correct and terminating at
both residual caps, with at most $m(R_0)$ states, no copies, and the same
original costs reindexed in their increasing order. This is the actual-prefix
restriction exposed in [SB, Theorem 6.2][SB] and used by SI Theorem 10.8
and TC Corollary 5.2.

A residual live history with $j$ new ones and $z'$ new zeros is still
live originally, since

$$
h+j\le k-1,\qquad
|S|-h+z'\le |S|-h+N-q=n-k.
$$

Thus its live queries are literal fresh original queries; no old-coordinate
step is silently suppressed on this live portion. Apply Theorem 6.4 or
Corollary 5.3 to this one residual graph, then its installed-count upper
bound $m(R_0)$, to obtain (TS.39). For native states (TS.37) gives
coordinatewise $m_i\le M_i$, so summing over this $R_0$ proves the
native assertion. All suppressed invocations stay paid in the original
runs. No runtime restriction, reset or residual entry is supplied.
$\square$

Different actual-prefix restrictions may overlap on the one original
installed vector. Their inequalities hold simultaneously but cannot be
added as disjoint allocations, or subtracted to assign a difference of
lower bounds to a complement. For example
$|Q_1|+|Q_2|=|Q_1\cup Q_2|+|Q_1\cap Q_2|$ requires overlap
control before obtaining a union lower bound. TC's unconditional
residual-seven bound of Convention 8.2 remains the applicable stronger
supplier in its solved slice; it has no inherited-cut premise. SI10's
inherited-cut theorem and SB's short-block refinement remain credited
sufficient conditions in their respective residual ranges.

## 11. Exact unresolved target, method limits and attribution

**Open problem 11.1 (the unchanged universal middle range).** For every
$n\ge7$, $4\le k\le n-3$, every strictly increasing positive integer
position vector and every complete correct graph at both same-input caps
$n,W$, prove

$$
D\le E+\nu,\qquad\text{equivalently }m\ge G,
$$

or construct one complete original graph with $m<G$ and its faithful
full-fiber lift. In the notation of this volume the missing universal
inequality is exactly (TS.21), or (TS.28). No bound on the total remaining
late deficit is proved here for arbitrary graphs. When $\rho=0$ the
equation is the original unmodified aggregate; when $\rho=1$ the new
contribution is the actual $1+\eta_5$ of that graph.

A contrary construction must specify every fixed row, prove correctness
and actual termination on every Boolean input, and pay both caps on each
same input. Its native upper must cover all of $\mathcal U_*$ with the
same code, original literal latches, complete entries, all four replies,
all installed states and all original services. A local overload, an
abstract support pattern, a relaxation, independently attainable block
minima or an above-grid example does not meet those requirements.
Theorems 4.1 and 6.4 are bounded results, not a resolution of this problem.

**Proposition 11.2 (the six-pair classification does not follow at larger
terminal spans).** At terminal span six and $K,L\ge5$, the first
internal diagonal can contain

$$
(K-5,L-1),\qquad(K-3,L-3),\qquad(K-1,L-5).
\tag{TS.40}
$$

Each pair meets both count gaps of (TS.3). Therefore that rule alone does
not exclude a three-cell hosted set, and cannot justify the two-incidence
multigraph reduction used in Lemma 3.1 at this larger span.

Proof. All three cells have depth $K+L-6=n-5$. Their successive hit
increases and zero decreases are both two; the extreme pair has both
four. Thus none is removed by (TS.3). This asserts only eligibility under
that necessary rule, not their joint realizability in a correct graph.
A nonterminal span-five gap ending at $n-1$ can likewise include this
earlier layer, so the terminal span-five classification cannot be transported
there just by changing the endpoint. For $n\ge8$ the larger count rectangle
also has additional eligible pairs: at $n=8,k=4$, $(0,4),(2,2)$ already
meets the two-gap rule, as recorded in TC Section 9. $\square$

Common live successors propagate paired occurrences only while both
remain live. At a boundary, one reply may certify one occurrence while its
same literal successor remains live for another. That state cannot be
erased, replaced globally by a terminal, or charged as a new installed
state for each use. There is no derived universal separator-capacity
premise. The complete above-grid construction in [SB, Section 8][SB]
forces one retained live-elsewhere separator under every allowed cross-fill
for arbitrarily many fixed cell-disjoint collisions, and can place every
allowed pack for a fixed collision inside a chosen representative image.
It refutes exactly the two stated universal fixed-representative charging
shortcuts. Favorable representative choice and collective compensation
remain unrefuted; the retained separator is not automatically counted by
$\nu$.

Likewise [SI, Sections 6--7][SI] gives the sharp $2n-2$ count relaxation,
discarding actual supports and certified-output correctness. Its complete
six-coordinate table is budget-feasible but returns one on $000011$ at
threshold three. It is not an original counterexample. SI11's one-way
cross-count pair and mass overload are necessary for a positive-deficit late
pool, not sufficient for a strict saving; other underloaded states, safe
surplus, cut excess and never-live states can compensate. Proposition 7.2
is a direct original-model example of such compensated overload.

[TC, Sections 6--9][TC] supplies an additional equivalent cost-certificate
form of the unresolved all-position target. For each fixed correct
$n$-query table it reduces existence of original feasible costs to a
positive ordered-gap cone, with a sparse actual-full-length-run obstruction
in the opposite case, using finite rational Farkas duality. Cramer's rule
and Hadamard's inequality give its bounded-position witness. The universal
implication from a state shortage $m<G$ to that obstruction remains
unproved. This volume neither changes a fixed position instance nor
discharges that quantifier. The seven-coordinate result and the qualified
classes do not settle larger rectangles; TC's stated
$17\le m_{\rm exec}\le20$ at $n=8,k=4$ remains a bounded comparison.

**Convention 11.3 (source correspondence and ordinary proof scope).**
The correspondence below distinguishes the actual new local applications
from existing mathematics.

| Mathematical content | Source and exact role |
| --- | --- |
| Saturation, private exchanges, support exclusions, two gaps, complete profiles and reader, all-address cube and exact native shifts | SB Sections 1--2 expose the ordinary proofs; its underlying WTF/PE interfaces are credited through those exposed arguments |
| Actual forks, singleton-diagonal propagation, exact incidence and compatible original-vector localization | SI Theorems 2.2, 4.1, 5.2, Lemma 9.2 and Theorem 9.3 |
| Right-cut separation, early-ending no-sharing, span-four six-pair mechanism, terminal span-four margin and inherited-cut consumers | SI Sections 9--10; reproduced at the stated scopes in SB Sections 3, 5--7 |
| Strict short-gap units and the precise nonnegative $\Xi$ expansion | SB Section 4 and Theorem 5.6 |
| All-history mass, arbitrary-span both-conflict capacity, class $\mathfrak C$, unbounded interacting late-gap family and collective overload balance | SI Sections 11.1--11.5; the capacity supplier is the classical nonuniform Bollobás set-pairs inequality |
| Boolean $16$, stronger central-host and collective bounds, native $20+r$, residual-seven and next-start constraints | TC Theorem 4.1, Corollaries 4.2--4.3 and 5.1--5.3; all reused, not new optima |
| Strict fourth-layer six-pair application and unconditional terminal span-five local unit | Lemma 3.1 and Theorem 4.1; repo-derived extension of the credited mechanism |
| Exact extracted aggregate, endpoint necessity, mass form, terminal-exception class and original separating construction | Sections 5--7; repo-derived consequences and complete witness |
| Strict seven-coordinate local gap inequalities and qualified residual/native terminal consumers | Corollary 8.1, Theorem 9.4 and Corollary 10.1; repo-derived applications, with their original costs and explicit hypotheses |
| Full-tree nonvacuity | Proposition 7.1; a unique-prefix example inside $\mathfrak C$, not a separation from that class |
| Fixed-representative charging obstructions and their above-grid boundary | SB Section 8, credited with its universal quantifiers; no new obstruction theorem here |
| Cost cones, sparse run obstruction and bounded-position reduction | TC Sections 6--9; inherited finite duality and linear algebra, not a proof of the universal lower bound |

The capacity inequality is literature-attested at the scope exposed in SI11:
Jason O'Neill and Jacques Verstraëte, *A generalization of the Bollobás
set pairs inequality*, arXiv:1812.00537v2, Theorem 1, page 1. Its two
ordered off-diagonal intersections are kept explicit in (TS.25), and the
permutation argument above supplies the finite inequality used here.
TC's general Farkas premise is its credited finite rational alternative;
no additional certificate or unseen table is a premise of the terminal proof.
The stated new deductions are repo-derived ordinary mathematics under the
declared model assumptions. No literature-wide priority claim is made.
Other volumes named inside SI, TC or SB are not separately invoked as
unexposed stronger suppliers.

The classical BP1 normalization of Wegener, Chapter 14, Section 4, uses
realizability of every path; Bryant's increasing-index diagrams and the
acyclic semantic read-once models discussed in SI and TC have different
hypotheses. None normalizes the arbitrary paid stationary graph here.
The proofs above are ordinary mathematical arguments; this reference
text carries no Lean-kernel certification. Installed-control cardinality
is distinct from source acquisition, authentication, access, export,
handoff implementation, table/address representation, workspace, physical
memory, elapsed time, energy and stationary service. No physical-efficiency,
general neural-network, empirical-learning or complete four-view recovery
claim follows. The general unrestricted-budget native minimum and the
wider original programme retain their separate unresolved obligations.

[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[TC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THRESHOLD_COST_CERTIFICATES.md
[SB]: FIB_NATIVE_SUPPORT_BARRIERS_AND_SHORT_BLOCK_COMPENSATION.md

## 追加锚（本行以下为增补区）
