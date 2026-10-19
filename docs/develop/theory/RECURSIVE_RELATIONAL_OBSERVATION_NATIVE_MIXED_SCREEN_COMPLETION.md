# Arbitrary completion of a native threshold mixed-screen fragment

## 1. The complete graph and the retained-fragment question

**Convention 1.1 (scope and attribution).** This companion to [SI][SI],
[PE][PE] and [WTF][WTF] studies a fixed mixed-screen head and its fixed
shared continuation. Its four failed-screen successors are free: their
entire strategies may be jointly replaced, with sharing into the retained
fragment or other installed states. Theorem 4.2 bounds the final complete
graph under both original per-input execution caps. Theorem 5.1 supplies
a complete original-model consumer for every pair of parameters, and
Theorem 7.4 gives its entire-fiber native consumer and corresponding
projection-qualified lower bound.

The new derivation is *repo-derived* ordinary paper mathematics. The
actual-history exclusions, ordered threshold grids, source profiles,
literal code, complete reader and Boolean/native correspondence are
credited suppliers, with their exact uses in Section 8. This is generic-v1
reference input, not a claim of Lean kernel verification or physical
realization. Published text is append-only; extensions and corrections
belong after the final append anchor.

**Definition 1.2 (one stationary paid Boolean graph).** Fix integers
$k,L\ge4$ and put

$$
k,L\ge4,\qquad n=k+L-1,\qquad u=n-5=k+L-6,\qquad G=kL.
\tag{MSC.1}
$$

The original positions are positive integers $s_1<\cdots<s_n$, with
$c_i=s_i+4$ and $W=\sum_{i=1}^n c_i$. Individual costs are distinct;
no distinct-subset-sums premise is imposed. A graph has a finite installed
running set $Q$, two distinct terminals $0,1$, one source-independent
running start, and at each running state one fixed coordinate label and
two fixed successors. Its only changing configuration is its current
state. On an input $\theta\in\{0,1\}^n$, every visit to label $i$
pays one query and $c_i$ letters and follows its fixed successor for
$\theta_i$.

Count $m=|Q|$, including unused states. The Boolean total installed count
is $m+2$. Require actual termination with output
$\mathbf1_{\{|\theta|\ge k\}}$ and, on each same complete input,

$$
t_P(\theta)\le n,\qquad J_P(\theta)\le W.
\tag{MSC.2}
$$

Every repeat and postcertificate visit is charged. Variable order,
leveling, immediate stopping at certificates, read-once behavior after
certification, and acyclicity of the syntactic union graph are not
assumed. Contradictory syntactic paths need not be actual executions.

An actual history ends just before a query. Its support $S$ contains
the exposed coordinates, with $h$ old ones and $z$ old zeros. It is live
when $h<k$ and $z<L$, so both outputs still have completions. Every
completion of its exposed assignment follows that history. Histories,
counts and restrictions below are mathematical indices, never accessible
runtime records.

**Convention 1.3 (consumed actual-history suppliers).** For these graphs,
[SI, Theorem 2.2][SI] gives freshness of every query at a live history.
Such a history therefore has exactly $h+z$ preceding queries. A
terminating fixed-input run cannot revisit a physical running state,
since its stationary suffix would then repeat forever.

The following shared-state exclusions retain their original scopes:
properly nested live supports cannot share a state; equal live supports
with different hit counts cannot share a state; and for incomparable
supports $S,T$ with hits $h<g$, if all old bits in $S\setminus T$ are
zero and all old bits in $T\setminus S$ are one, then

$$
|S\setminus T|=|T\setminus S|,
\qquad C_{S\setminus T}=C_{T\setminus S},
\qquad C_B:=\sum_{i\in B}c_i.
\tag{MSC.3}
$$

These are [PE, Lemma 4.1 and Theorem 3.1][PE] and [PCA, Theorem
35.1][PCA], in Boolean language. Their application here is lawful by
lifting this entire complete graph through [WTF, Theorem 4.1][WTF].
It gives the original full-domain native graph at both caps
$n+1,W+3$, and every Boolean history lifts to an actual selected-cube
history after the paid profile front. Since $n\ge7$ and
$4\le k\le n-3$, all their parameter restrictions hold. No property
of arbitrary states having unique residuals is inferred. These suppliers
are consumed below rather than reproved as new content.

## 2. The exact mixed screen and shared scan

**Definition 2.1 (retained head).** Partition the original coordinate
labels into the five distinct labels $j,x_1,x_2,y_1,y_2$ and the ordered
list $U=(u_1,\ldots,u_u)$. Put $X=(x_1,x_2)$ and $Y=(y_1,y_2)$.
The start and the following roles are retained:

| Role | Label | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ (start) | $j$ | $A$ | $B$ |
| $A$ | $x_1$ | $F_{00}$ | $A_2$ |
| $A_2$ | $x_2$ | $Q(0,0)$ | $F_{11}$ |
| $B$ | $y_1$ | $F_{10}$ | $B_2$ |
| $B_2$ | $y_2$ | $F_{110}$ | $Q(0,0)$ |

The symbols $F_{00},F_{11},F_{10},F_{110}$ name four successor
targets, not four compulsory states. Each may be any running state or
terminal of the final complete graph, subject to correctness and
(MSC.2). Their continuations are entirely unrestricted. The two
successful cylinders are

$$
\mathcal C_\ell=\{j=0,\ X=10\},\qquad
\mathcal C_h=\{j=1,\ Y=11\}.
\tag{MSC.4}
$$

They have respectively one and three exposed ones after three queries.
Every assignment of their other coordinates remains in the original
Boolean domain, whether or not the history has already certified.

**Definition 2.2 (all retained scan edges).** For every

$$
0\le s<k-1,\qquad 0\le z<L,\qquad s+z<u,
\tag{MSC.5}
$$

retain a running role $Q(s,z)$ labelled $u_{s+z+1}$. A reply
$\varepsilon$ gives $(s',z')=(s+\varepsilon,z+1-\varepsilon)$.
If $s'=k-1$, its successor is terminal $1$; if $z'=L$, its
successor is terminal $0$. Otherwise, when $s'+z'<u$ the successor
is $Q(s',z')$. When $s'+z'=u$, the successor is $D_{s'}$ from
Definition 2.3. The two certificate cases cannot occur together.

Every outgoing edge is fixed, including edges that are already certified
on one successful cylinder. The subscripts designate installed roles and
connections. They implement neither arithmetic nor a changing counter.
The scan never consults a failure target.

**Definition 2.3 (complete retained decoder).** The possible nonterminal
full-$U$ counts are exactly

$$
s\in\{k-5,k-4,k-3,k-2\}\cap\mathbb Z_{\ge0}.
\tag{MSC.6}
$$

Set $D_{k-5}=X_A$, $D_{k-4}=X_O$, $D_{k-3}=Y_A$ and
$D_{k-2}=Y_O$, omitting $X_A$ and $D_{k-5}$ when $k=4$.
The entire decoder table is

| Role | Label | Zero successor | One successor |
| --- | --- | --- | --- |
| $X_A$ (only $k\ge5$) | $x_1$ | $0$ | $I_X$ |
| $X_O$ | $x_1$ | $I_X$ | $E$ |
| $I_X$ | $x_2$ | $0$ | $1$ |
| $E$ | $j$ | $0$ | $1$ |
| $Y_A$ | $y_1$ | $0$ | $I_Y$ |
| $Y_O$ | $y_1$ | $I_Y$ | $1$ |
| $I_Y$ | $y_2$ | $0$ | $1$ |

In particular $E$ is an actual second paid read of $j$, rather than
an available copy of its earlier reply. All table entries are retained,
including those unused by successful-screen inputs.

**Definition 2.4 (arbitrary complete extension).** A graph of Definition
1.2 extends this fragment if it has a map from all the displayed running
roles to its installed running set that preserves their labels and every
specified successor, maps $R$ to its start, and preserves terminals.
The four failure targets are free images in the final graph. The role
map is not required a priori to be injective. Identifying roles is allowed
only if one physical label and both fixed successors satisfy all their
prescriptions. All additional arrivals, sharing with failed-screen
continuations, certified/live reuse and syntactic cycles remain allowed.
Only actual inputs must terminate. No failure behavior is fixed by this
definition.

## 3. The physically forced fragment

**Lemma 3.1 (behavior on both entire success cylinders).** The retained
continuation computes threshold $k$ correctly on every input in
$\mathcal C_\ell\cup\mathcal C_h$, including paid certified tails.
After a prefix of $U$ with counts $(s,z)$ and length $t=s+z$, its
future functions on the two cylinders are respectively

$$
\operatorname{Thr}_{k-1-s}(Y,U_{>t}),\qquad
\operatorname{Thr}_{k-3-s}(X,U_{>t}).
\tag{MSC.7}
$$

Here thresholds outside the nonconstant range mean their usual constant
functions. This statement concerns the specified continuation on its
actual arrival cylinders, not a residual convention for arbitrary states.

Proof. A prefix of $U$ adds $s$ ones to the head's one or three ones.
At $s=k-1$, even the low cylinder is positive. At $z=L$, even the
high cylinder can have at most

$$
3+(u-L)+2=k-1
$$

total ones, whenever that exit is reachable. These are lawful early
terminals on both cylinders. At full $U$, avoiding both exits means
$s\le k-2$ and $u-s\le L-1$, giving (MSC.6). The required pair
of low/high functions at each possible final count is

| Final $U$ ones | Low cylinder | High cylinder |
| --- | --- | --- |
| $k-5\ge0$ | $0$ | $x_1\wedge x_2$ |
| $k-4$ | $0$ | $x_1\vee x_2$ |
| $k-3$ | $y_1\wedge y_2$ | $1$ |
| $k-2$ | $y_1\vee y_2$ | $1$ |

On the low cylinder $X=10$: $X_A$ returns zero, while $X_O$
reaches $E$ and returns zero by its paid $j=0$ reply. On the high
cylinder $j=1$, $X_O$ implements OR, including its $x_1=1$ edge
through $E$. On the high cylinder $Y=11$, $Y_A,Y_O$ return one;
on the low cylinder they implement the displayed AND and OR. The table
also specifies every other reply. All routes advance through the finite
$U$ list and then make at most two decoder queries. This proves the
claim for arbitrary free coordinates in both complete cylinders.
$\square$

**Lemma 3.2 (no physical role identifications).** In every arbitrary
complete extension, the retained running-role map is injective.

Proof. First separate the head and decoder roles of each common label
using their fixed successors. $A_2=I_X$ would force the running
$Q(0,0)$ to be terminal $0$; $B_2=I_Y$ would force it to be terminal
$1$. Both are impossible. Then $A=X_A$ would force $A_2=I_X$,
and $B=Y_A$ would force $B_2=I_Y$. Also $A=X_O$ would force
$A_2=E$, whose labels differ; $B=Y_O$ would force $B_2=1$.
$X_A=X_O$ would identify $0$ with $I_X$, and $Y_A=Y_O$ would
identify $0$ with $I_Y$. Finally $R=E$ would identify $A$ with
terminal $0$. This covers every pair of distinct head/decoder roles
with equal labels. Running states and terminals are disjoint; all other
such pairs have different labels.

Every scan label is different from these five labels. Scan roles at
different positions $t+1$ also have different labels. It remains to
separate two roles $Q(s,t-s)$ and $Q(s',t-s')$ at the same position,
where $s\ne s'$. Every listed role is actually reached from each
successful head by a $U$ prefix with its listed counts: its partial
counts never cross an early-exit boundary. This includes histories
that have already certified on one cylinder.

The retained suffix only reads $U_{>t}$ and $j,X,Y$, never earlier
$U$ coordinates. On the common low context it therefore has the two
functions in (MSC.7), on the same

$$
N=2+u-t
$$

free coordinates, with thresholds $k-1-s$ and $k-1-s'$. Both
thresholds are positive. They are distinct functions unless both exceed
$N$, in which case both functions are zero. This exceptional condition
for a role is equivalent to $z=t-s\ge L-2$. Since $t<u$, it also
implies $s\le k-5$. For both exceptional roles their high-context
thresholds $k-3-s$ and $k-3-s'$ are distinct and lie in $[1,N]$:
they are at least two and

$$
N-(k-3-s)=L-1-z\ge0.
$$

Thus the high-context functions distinguish them instead. If the two
roles were one physical state, choose identical values on the common
suffix coordinates. Their earlier $U$ assignments are never queried
again, so fixed-successor induction gives identical suffix outputs.
The distinguishing comparison contradicts Lemma 3.1. This argument uses
only the explicitly retained suffix, without assigning unique residual
functions to arbitrary graph states. $\square$

**Lemma 3.3 (forced physical count).** The retained fragment contains
exactly $(k-1)L+2=G-L+2$ distinct running roles.

Proof. The full scan rectangle has $(k-1)L$ points. Write its opposite
corner coordinates as

$$
a=(k-2)-s,\qquad b=(L-1)-z.
$$

The removed condition $s+z\ge u$ is $a+b\le3$. For $k\ge5$,
all its $4+3+2+1=10$ points lie in the rectangle. For $k=4$, only
the point $(a,b)=(3,0)$ is missing from that triangle, so nine points
are removed. This uses $L\ge4$, including its endpoint case. There
are seven decoder roles when $k\ge5$, and six when $k=4$, together
with five head roles. Both totals are $(k-1)L+2$. Lemma 3.2 makes
this a physical-state count, rather than an incidence or role count
with unexamined aliases. $\square$

## 4. An actual zero execution outside the whole fragment

**Lemma 4.1 (small accepting witnesses under the zero-axis context).**
Fix any original coordinates already exposed as zero, including
$j=x_1=0$. From a retained scan role $Q(s,z')$, every actual
accepting suffix tests at most $k-1-s$ distinct unread coordinates
with reply one. From any retained decoder role, an actual accepting
suffix tests at most two such coordinates. These claims concern
suffixes actually compatible with the fixed old zeros.

Proof. At a scan start, early acceptance requires precisely $k-1-s$
new $U$ one replies. Otherwise acceptance follows a full-$U$ decoder.
The number of subsequent $U$ one replies at its four possible exits
is, respectively, $k-5-s,k-4-s,k-3-s,k-2-s$. A negative number
simply makes that particular exit unreachable from this role.

The $X_A$ exit cannot accept because $x_1=0$. The $X_O$ exit
then uses $I_X$ and needs $x_2=1$, giving at most
$k-4-s+1\le k-1-s$ unread one replies. The $Y_A$ exit needs
two $Y$ ones, giving at most $k-3-s+2=k-1-s$. The $Y_O$
exit needs at most one $Y$ one, giving at most
$k-2-s+1=k-1-s$. The $E$ branch of $X_O$ cannot occur when
$x_1=0$. Coordinates already fixed zero can only prohibit these
accepting routes, not increase their positive-reply count. The decoder
table directly gives its at-most-two bound, including $E$, which
returns zero when $j=0$. $\square$

**Theorem 4.2 (dual-cap arbitrary-completion lower bound).** For every
$k,L\ge4$, every graph of Definition 1.2 extending exactly Definitions
2.1–2.3, with arbitrary complete failed-screen continuations as in
Definition 2.4, satisfies

$$
\boxed{m\ge kL.}
\tag{MSC.8}
$$

The same graph must satisfy both caps in (MSC.2). This theorem does not
claim that every threshold graph contains this fragment, that $kL$ is
attained within the retained-fragment class, or that the query cap alone
suffices.

Proof. On the actual all-zero input the first states are $R,A$.
Until $L$ distinct zeros are exposed the history remains live. By
Convention 1.3 it has fresh queries, so for every
$d=2,\ldots,L-1$ there is a running state $Z_d$ after exactly
$d$ zero queries. These $L-2$ states are distinct: otherwise this
one fixed-input run would not terminate. Let $S_d$ be its exposed
support. It contains $j,x_1$, and all its old values are zero.
Every assignment of the other $n-d$ coordinates follows that prefix;
the residual requirement on that full cylinder is threshold $k$, with
$n-d\ge k$.

Suppose first that $Z_d$ were a retained scan or decoder role. Set
all unread coordinates to one. This is a compatible actual input of
weight at least $k$, so correctness supplies an accepting suffix.
Let $T$ contain exactly the unread coordinates queried with reply one
on that particular suffix. Keep the old zeros, set exactly $T$ to one,
and set every other unread coordinate to zero. This new complete input
follows the same original zero prefix. It also follows the same
accepting suffix: inductively every tested one lies in $T$, every
tested zero is still zero, and the fixed successor is therefore the
same. This preserves an actual run; it does not realize an arbitrary
syntactic path or erase a queried one.

For a scan role Lemma 4.1 gives $|T|\le k-1-s<k$. For a decoder
role it gives $|T|\le2<k$. The resulting input has total weight
below $k$ but accepts, a contradiction. Consequently no $Z_d$
belongs to the retained scan or decoder.

It remains to separate $Z_d$ from the five head states. It cannot
be $R$ or $A$, already visited on the same zero input. The actual
live history at $A_2$ has support $\{j,x_1\}$ and hit count one.
This support equals $S_d$ with different hits when $d=2$, and is
properly contained in $S_d$ when $d>2$. Convention 1.3 excludes
both cases. The actual live history at $B$ has support $\{j\}$,
properly contained in $S_d$, so it too is excluded.

For $B_2$, use the actual live history $j=y_1=1$ with support
$T_0=\{j,y_1\}$ and two hits. If $y_1\in S_d$, then $T_0$ is
properly contained in $S_d$: the latter also contains $x_1$, a
different coordinate. Nested-support exclusion applies. If
$y_1\notin S_d$, the supports are incomparable, with

$$
S_d\setminus T_0=S_d\setminus\{j\},\qquad
T_0\setminus S_d=\{y_1\}.
$$

Every old bit in the first private side is zero on the zero history;
the second private side is one on the $B_2$ history. The hits are
$0<2$. Both implications of the supplied private-charge law (MSC.3)
therefore apply on this same complete graph. They force $d-1=1$
and equality of the private costs. Hence $d=2$,
$S_d=\{j,x_1\}$, and $c_{x_1}=c_{y_1}$, contradicting the original
distinct individual costs. This is where both original caps, including
the weighted cap, are consumed. A possible equality of different
multi-coordinate subset sums is not being excluded.

All $L-2$ physical states $Z_d$ therefore lie outside the entire
retained fragment. By Lemma 3.3, on this one final installed graph,

$$
m\ge\bigl((k-1)L+2\bigr)+(L-2)=kL.
$$

No failed-screen strategy, query order or state allocation was fixed in
this sum. A paid discriminator shared elsewhere was not automatically
assigned to a new batch or a nonlive pool. Extra arrivals at the
retained fragment do not change its fixed successors and hence do not
invalidate the witness separation. $\square$

## 5. A complete consumer at both original Boolean caps

**Theorem 5.1 (nonempty unbounded retained-fragment family).** For every
$k,L\ge4$ there is a complete correct actually terminating graph
extending the fragment, on original positions $s_i=i$, satisfying both
caps in (MSC.2). Its exact installed running count is

$$
M=(5k-6)L-5k+7>kL.
\tag{MSC.9}
$$

One actual input attains both $n$ queries and $W$ letters. This is an
above-grid consumer of Theorem 4.2, not a strict-subgrid construction or
an attainment of that theorem's lower bound.

Proof. Choose the literal coordinate assignment

$$
j=1,\quad x_1=2,\quad y_1=3,\quad y_2=4,\quad x_2=5,
\qquad U=(6,\ldots,n).
\tag{MSC.10}
$$

Thus $c_j=5$ and

$$
C_X=c_{x_1}+c_{x_2}=6+9=15
 =7+8=c_{y_1}+c_{y_2}=C_Y,
\qquad W=5+15+15+C_U.
\tag{MSC.11}
$$

Install the fragment with distinct roles. Complete its four free targets
using four separate ordinary ordered threshold grids, sharing only the
two terminals. Their complete specifications are

| Target | Unread coordinate order | Residual threshold | Running states |
| --- | --- | --- | --- |
| $F_{00}$ | $(y_1,x_2,y_2,U)$ | $k$ | $k(L-2)$ |
| $F_{11}$ | $(y_1,y_2,U)$ | $k-2$ | $(k-2)(L-1)$ |
| $F_{10}$ | $(x_1,x_2,y_2,U)$ | $k-1$ | $(k-1)(L-1)$ |
| $F_{110}$ | $(x_1,x_2,U)$ | $k-2$ | $(k-2)(L-1)$ |

The standard grid of [PCA, Theorem 26.1][PCA] on an ordered list
$(v_1,\ldots,v_N)$ and threshold $q$ has all roles

$$
G_{a,b},\qquad 0\le a<q,\quad 0\le b<N-q+1.
$$

It starts at $G_{0,0}$, reads the literal $v_{a+b+1}$ and follows
reply $\varepsilon$ to the role with incremented counts, except that
reaching $a=q$ gives terminal $1$ and reaching $b=N-q+1$ gives
terminal $0$. This fixes every grid label and successor, with
$q(N-q+1)$ running states. Its list is exactly the unread list at
the corresponding failure edge, and its threshold subtracts exactly the
head's old ones. For example $F_{00}$ follows $j=x_1=0$, while
$F_{110}$ follows $j=y_1=1,y_2=0$. The other two rows follow
$j=0,X=11$ and $j=1,y_1=0$. These four failure cylinders together
with (MSC.4) partition all original Boolean inputs.

Every failure route therefore computes its correct residual on the
entire unread cube. It reads each remaining coordinate at most once
and none of its old head coordinates again. Both complete-input bounds
$t\le n$ and $J\le W$ hold together. For the successful cylinders,
Lemma 3.1 proves correctness. They make three head queries, at most
$u$ scan queries and at most two decoder queries, giving

$$
t\le3+u+2=n.
$$

Each successful head costs $5+15$. The scan costs at most $C_U$.
The possible longest decoder bills, with shorter paths included, are

$$
\begin{array}{c|c}
\text{decoder start}&\text{letter upper bound}\\ \hline
X_A&c_{x_1}+c_{x_2}=15\\
X_O&\max(c_{x_1}+c_{x_2},c_{x_1}+c_j)=\max(15,11)=15\\
Y_A&c_{y_1}+c_{y_2}=15\\
Y_O&c_{y_1}+c_{y_2}=15.
\end{array}
$$

Thus $J\le5+15+C_U+15=W$ on each of these same inputs. This
pays every old $X$ or $Y$ requery, the second $j$ query at $E$,
and every visit after one context has already certified. No free saved
head reply or postcertificate discount is used.

The explicit construction terminates: each head enters a finite forward
grid or the finite scan/decoder. Only its displayed terminals are shared
between components. This construction is acyclic, but Theorem 4.2 does
not impose that restriction on its competitors.

Adding the four grid counts to Lemma 3.3 gives exactly (MSC.9), counting
every installed role, including any role unused under a particular
incoming cylinder. Moreover

$$
M-kL=(4k-6)L-5k+7\ge11k-17>0.
$$

For simultaneous attainment, take $j=x_1=0$ and enter $F_{00}$.
On its unread list of length $N=n-2$, assign its first $k-1$
positions one and every later position zero. Here $N\ge k+1$.
Every proper grid prefix has fewer than $k$ ones and fewer than
$N-k+1=L-2$ zeros. It therefore reads all $N$ coordinates before
rejecting. This complete input queries all original coordinates once,
so it pays exactly $n,W$ together. $\square$

## 6. Actual overload, internal ambiguity and coverage boundaries

**Theorem 6.1 (the consumer is beyond the named sufficient classes).**
For the complete family in Theorem 5.1 the following hold, in the exact
actual-history notation of SI Sections 2 and 9–15.

1. $Q(0,0)$ has all-history reciprocal-binomial mass at least $4/3$
   and a pair with only one directed conflict.
2. Its complete common-support cut list is $0,1,n$, where $n$ is
   SI's adjoined formal endpoint. The gap $(1,n)$ has unbounded span
   $n-1$ and ends after $\max(k,L)$.
3. No reblocking puts all its actual live queries into SI12, SI13,
   SI14 or IC's one-permutation-per-fixed-initial-assignment form.
4. It violates SI15's interior-singleton support condition.

These exclusions concern the specified sufficient classes, not SI's
general incidence identities, collective compensation target or every
consequence of the supplied papers.

Proof. At $Q(0,0)$ the two actual head histories have reply words
$010$ and $111$. Their one/zero set pairs are

$$
(\{x_1\},\{j,x_2\}),\qquad
(\{j,y_1,y_2\},\varnothing).
\tag{MSC.12}
$$

Both histories are live for $k,L\ge4$. In the exact all-history
normalization of [SI, Definition 11.2][SI], their contributions are

$$
\binom31^{-1}+\binom33^{-1}=\frac13+1=\frac43.
\tag{MSC.13}
$$

The high one's set meets the low zero's set at $j$; the other directed
intersection is empty. These are distinct actual prefixes, not two
representatives manufactured by separately optimized graphs. Other
arrivals can only add nonnegative mass. Hence $Q(0,0)$ fails SI11's
both-conflict condition and its pointwise capacity sufficient condition.

Depths zero and one have common supports $\varnothing$ and $\{j\}$.
At depth two, live prefixes $j=0,x_1=1$ and $j=1,y_1=1$ have
different supports. For every $0\le t\le u-1$, choose

$$
s+z=t,\qquad 0\le s\le k-4,\qquad 0\le z\le L-3.
\tag{MSC.14}
$$

Such counts exist at every listed $t$ because the two upper bounds sum
to $u-1$. Use the same $U$ prefix counts after each successful head.
The low and high histories at depth $3+t$ are both live and have
supports $\{j,x_1,x_2\}\cup U_{\le t}$ and
$\{j,y_1,y_2\}\cup U_{\le t}$, which differ. These supply depths
$3,\ldots,n-3$.

At depth $n-2$, use the high cylinder with full-$U$ weight $k-4$
and the low cylinder with full-$U$ weight $k-2$. These respectively
reach $X_O$ and $Y_O$, both with total counts $(k-1,L-2)$, and
retain the different head supports with all $U$. At depth $n-1$,
give $x_1=0$ on that high path and $y_1=0$ on that low path.
The live states are $I_X,I_Y$, with counts $(k-1,L-1)$ and
supports missing respectively $x_2$ and $y_2$. These are different
again. All these assignments avoid the scan's early exits. Thus no
depth $2,\ldots,n-1$ is common-support. Adjoining SI's endpoint
proves the asserted cut list. Its long gap has span $n-1\ge6$ and
$n>\max(k,L)$, so it belongs to SI's remaining late-long pool
$\mathcal L_*$. The overloaded state in (MSC.12) lies in that pool.
Consequently SI11's qualified capacity class and the short-late-gap
sufficient classes do not cover this family.

Each SI12–SI14 or IC reblocking has a fixed common initial coordinate
list $\mathsf I$, after whose complete assignment one permutation
governs every subsequent live query. The two live root branches here
have different second labels $x_1,y_1$, so $|\mathsf I|\le1$,
and the first label forces $\mathsf I=(j)$ in those nonempty-prefix
definitions. But for the same assignment $j=0$, the live history
$00$ has next label $y_1$ in $F_{00}$ and the live history $01$
has next label $x_2$ at $A_2$. A single permutation for that fixed
initial assignment cannot give both third labels. This rules out every
such reblocking, irrespective of block names, weights or mode labels.

Finally the interior count cell $(1,2)$ has the actual histories $010$
and $001$. The former ends at $Q(0,0)$ with support
$\{j,x_1,x_2\}$; the latter follows $F_{00}$ and its first
$y_1=1$ reply, with support $\{j,x_1,y_1\}$. Both are live, and
$1\le k-2$, $2\le L-2$, including $L=4$. Thus its support
multiplicity exceeds one at a cell covered by [SI, (SI.134)][SI].
This excludes SI15's interior-singleton class. $\square$

**Proposition 6.2 (actual paid root rereading).** The family of Theorem
5.1 has an actual input visiting the initial $j$ state and then the
decoder's $j$ state $E$, as well as histories certified on one incoming
screen that continue through retained scan or decoder states.

Proof. Take $j=0,X=10$ and full-$U$ weight $k-4$. Since
$u-(k-4)=L-2$, the scan reaches $X_O$. Its old $x_1=1$ leads to
$E$, whose paid old $j=0$ returns zero. The same input has total
weight at most $1+(k-4)+2=k-1$, so the low context is already
negative when full $U$ is known. Its decoder visits remain actual and
charged. The distinct physical roles $R,E$ were already proved in
Lemma 3.2. This does not endow another graph with a free root reply or
assume every syntactic path is realizable. $\square$

## 7. The entire original native consumer and the literal reader

**Definition 7.1 (unchanged unbounded source and whole target).** Use
exactly [WTF, Definition 1.1][WTF] and [PCA, Definition 4.1][PCA].
The source algebra and update are

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=E_0:=\langle\beta,\alpha\rangle,\quad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
\tag{MSC.15}
$$

The symbol $E_0$ here is a tree and is distinct from the decoder state
$E$. Every finite absolute original-root word in $\{L,R\}^*$,
including $\varepsilon$, is legal. Replies are alpha, beta, branch,
absent, with descent past a leaf absent. Repeated values keep their
distinct occurrences. Let $P=\{L,R\}^3$. The complete current row
$R_*$ has the perfect depth-three exterior and classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
\tag{MSC.16}
$$

Different classes assert whole-subtree disequality. A complete row
retains the ordered exterior, every reached occurrence hole, the whole
equality partition including repetitions, every different-class
disequality and every concrete strict-prefix blocking guard. Canonical
names are recomputed from first occurrences after restriction. The
domain and target are

$$
\mathcal U_*:=\{\tau\in\mathcal T:R_P(\rho\tau)=R_*\},
\qquad F(\tau)=R_P(\tau).
\tag{MSC.17}
$$

This includes all actual inverse sources, with no size, depth or shape
bound. In particular it is not restricted to a Boolean witness cube.
For distinct class values $x$, the actual current filling is

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
$$

The supplied image grammar is
$\mathcal I=\rho[\mathcal T]=\{\beta,E_0\}\cup
\{\langle v,w\rangle:v,w\in\mathcal I\}$. Its disjoint parsing
cases have inverse $\delta(\beta)=\alpha$, $\delta(E_0)=\beta$,
and pairwise recursive inverse for image children. A distinct-class
filling is an image exactly when all six values are images, or exactly
one right-class value is alpha, its repeated left partner is beta and
every other value is an image. Its origin is
$\delta(\mathscr S(x))$. This is the source supplier of WTF Section
1, not an inverse operation available to either apparatus.

The exhaustive eleven profiles are $\Pi_1,\ldots,\Pi_4$, where
the indicated $b_i$ is alpha, its partner beta and all other roots
branches; $Z_d$ for the six classes $d$, where only $d$ is beta and
the others are branches; and $Z_*$, where all six are branches. All
branch values range over their entire allowed finite image sets, with
all six-class disequalities retained.

The five literal complete targets are $R_0=R_*$ on the zero profiles
and $R_i$ on $\Pi_i$. Writing
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, $R_i$ replaces the two
sibling holes at $q_iL,q_iR$ by concrete beta at $q_i$, retaining
every other exterior part and old hole. Restrict the whole equality
partition and recompute its canonical names. The other occurrence of
the repeated partner remains an old hole. Every surviving disequality
and blocking guard is part of the output, not discarded by the code.

**Definition 7.2 (literal pointwise code and complete entries).** Keep
the original positions, $w_i=L^{s_i}R$, $a_i=LLLw_i$, and
$c_i=|a_i|=s_i+4$. For every branch image $B$, define
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$; alpha,
beta and absent each give zero. The prescribed function is literally

$$
\sigma_{A,k}(\tau)=
\begin{cases}
0,&\tau\in\Pi_1\cup\Pi_2,\\
1,&\tau\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&\tau\in Z_{b_3},\\
0,&\tau\text{ is in any other zero profile},
\end{cases}
\qquad A=\{s_1,\ldots,s_n\}.
\tag{MSC.18}
$$

This is [PCA, Definitions 4.2 and 23.1][PCA], on the same full domain.
It specifies the code on acquired finite data; those data do not become
an input or accessible archive for the paid preparer.

Retain exactly [PCA, Supplier application 4.3 and Convention 23.2][PCA],
equivalently [WTF, Convention 1.3][WTF]. Its literal complete distinct
entries are $e_0,e_1$ with their original recoverable labels and all
their contents. Let $(i_1,i_2)$ denote the original fixed order of
$\{1,2\}$ in its zero-entry chain, not a design choice. The whole
running table and outputs are

| Original reader state | Absolute literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $e_0$ | $q_{i_1}R$ | $H_{i_1}$ | $H_0$ | $Q_2$ | $H_0$ |
| $Q_2$ | $q_{i_2}R$ | $H_{i_2}$ | $H_0$ | $H_0$ | $H_0$ |
| $e_1$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

Each $H_i$ is the halt containing the entire literal row $R_i$
of Definition 7.1, not a root reply or class label. Thus its three
running states and five distinct complete-row halts remain separately
counted as $K=8$. Its fresh bounds remain two invocations and six
letters. Preparation must end at the original latch
$\widehat e_{\sigma_{A,k}(\tau)}$; code-only handoff enters that
same complete $e_{\sigma_{A,k}(\tau)}$ on that same actual source.
Changing the encoder, entry map, reader order or usable code is not
allowed.

**Assumption 7.3 (unchanged paid native contract).** A native preparer
has one source-independent running start, one fixed absolute word and
four fixed successors at each running state, the two original-entry
latches and $r\ge0$ further mandated distinct latches. Its counted
current state is the entire changing configuration. Count every installed
running state and every latch, including unused ones. Each running
visit pays one invocation and its actual word length, including roots,
constants, absence, repeats and postcertificate visits. Every actual
$\tau\in\mathcal U_*$ must terminate correctly. Shared successors
and cycles in the syntactic union graph are permitted.

Keep the original origin/update/register binding, acquisition of the
authenticated same-version row and code arguments, version
authentication, pre-cut access permission, actual same-source export,
complete access isolation, code-only handoff, lawful complete entry and
stationary truthful service continuity as separately supplied and priced
services. The register remains the same $\rho\tau$ throughout both
phases. Table/address representation, installation, initialization,
entry and whole-output contents, local acquired-term work, handoff and
service storage keep their separate prices.

No archive/code reread, selector, source copy, counter, phase coordinate,
computed address, cursor, reset, clock, equality/inverse port or extra
work/control register is added. Counts and input choices in a proof
are not runtime getters. Finite code length, installed control, exported
alphabet, microsteps, physical time, memory and energy remain distinct
resources, as in [WTF, Assumption 1.5][WTF].

**Theorem 7.4 (complete original lift and qualified lower).** The complete
Boolean consumer of Theorem 5.1 has an original native preparer on all
of $\mathcal U_*$ with exactly

$$
H=M+4+r
\tag{MSC.19}
$$

installed preparation states and both per-source caps
$q_P\le n+1$, $\ell_P\le W+3$, with the literal code, latches,
complete entries and separate reader of Definition 7.2. These two caps
are attained together on one actual source.

For any original native preparer at those same caps, if its particular
Boolean projection in [WTF, Theorem 4.1][WTF] extends Definitions
2.1–2.3, then

$$
\boxed{H\ge kL+4+r.}
\tag{MSC.20}
$$

No normalization of arbitrary projections into this fragment is claimed.

Proof. Apply the supplied correspondence to the entire complete Boolean
table, not merely to its successful cylinders. For clarity its full
native table is specified as follows. For each Boolean running state
$v$ labelled $i$, install the literal $a_i=LLL L^{s_i}R$, with
four successors in alpha, beta, branch, absent order

$$
\bigl(\delta(v,0),\delta(v,0),\delta(v,1),\delta(v,0)\bigr),
\tag{MSC.21}
$$

replacing Boolean terminals by $\widehat e_0,\widehat e_1$.
Keep every installed Boolean state, even if unused. Add the two
profile states below, start at $D$, and install all $r$ further
mandated distinct latches:

| Profile state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | Boolean start $R$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

All four replies are fixed even where a profile-root reply is
unreachable. On every $Z_{b_3}$ source, its arbitrary branch image
$x_a$ determines the static Boolean vector $\theta(x_a)$ of
Definition 7.2. The original all-address occurrence identity
$r_{\rho\tau}(p w)=r_{x_{[p]}}(w)$ makes (MSC.21) exactly the
Boolean test on every visit. It covers leaf and absent replies as well
as branch replies, at every selected word, for noncomb images too.
No vector or copy of the source is supplied to the apparatus. Boolean
correctness and actual termination hold for that same fixed vector,
so the native run terminates at the literal prescribed latch.

The profile table exhausts the rest of the original domain. Alpha at
$D$ means $\Pi_3$ and requires code one. Beta there means exactly
$Z_{b_3}$ and enters the Boolean table. For branch at $D$, the only
remaining code-one profile is $\Pi_4$, detected by alpha at $T$;
every other such profile latches zero. This also covers $\Pi_1,
\Pi_2$ and all other zero profiles. Thus all eleven profiles, all
their allowed branch values and every actual inverse source have the
same pointwise code (MSC.18). Source size, depth and shape are
unbounded in this upper proof.

The running count is $M+2$ and the latch count is $2+r$, giving
(MSC.19). On a selected route for its same actual $\tau$ the
resource identities are exactly

$$
q_P(\tau)=1+t_P^{\mathrm{Bool}}(\theta(x_a)),\qquad
\ell_P(\tau)=3+J_P^{\mathrm{Bool}}(\theta(x_a)).
\tag{MSC.22}
$$

All repeats of the Boolean table remain paid native visits. Other
profile routes cost at most two calls and six letters, dominated by
$n+1,W+3$ since $n\ge7$, $c_i\ge5$. The same-input bounds of
Theorem 5.1 therefore give both native caps on every original source.
Its simultaneously saturated Boolean input has an actual selected-cube
origin by [WTF, Supplier 2.1][WTF], equivalently [PCA, Lemma 24.1][PCA].
Its native run attains both shifted bounds. The cube is used here only
to witness attainment, not to restrict the upper domain.

Handoff enters the original complete reader state. By its supplied
profile semantics it outputs $R_i$ on $\Pi_i$ and $R_0$ on all
zero profiles, including either code on $Z_{b_3}$. Thus the entire
predecessor row, every exterior occurrence, whole equality partition,
repetition, disequality and blocking guard in Definition 7.1 is retained.
The independent reader remains $K=8$ with its separate fresh two-call,
six-letter budget. Its states and fresh work are not absorbed into
preparation's $H,q_P,\ell_P$.

Finally WTF's projection of any qualifying native competitor is a
complete correct actual-terminating Boolean graph at both caps, with
$m\le H-4-r$. The explicit fragment-membership hypothesis permits
Theorem 4.2, giving $H-4-r\ge m\ge kL$. This proves (MSC.20)
without assuming that the chosen projection preserves a native path
pointwise on other sources or that arbitrary preparers have this
fragment. All separately supplied services of Assumption 7.3 remain
in force. $\square$

## 8. Suppliers, literature correspondence and unresolved objectives

**Convention 8.1 (mathematical ownership).** Theorem 4.2's new step is
the separation of one entire mandatory actual zero axis from the
retained shared continuation, together with the physical fragment count.
The conclusion quantifies over the final complete graph while all four
failed-screen strategies may be jointly redesigned. It is not merely
the above-grid construction, a fixed fallback minimum, a conditional
transport plan, an accounting identity or a restatement of a dual
certificate alternative.

The following suppliers retain their ownership:

| Source | Exact use and limit |
| --- | --- |
| SI Theorem 2.2; PCA Theorems 34.3, 35.1; PE Theorem 3.1 and Lemma 4.1 | Actual live freshness, equal/nested-support exclusions and the two-polarity private charges consumed in Theorem 4.2. No unique residual is attached to every state. |
| PCA Theorem 26.1; CP Section 5 | Ordinary complete threshold grids and actual-prefix restrictions. The four grids in Theorem 5.1 are applications, not new ordered-grid minima or state-nonincreasing normalizations. |
| WTF Theorem 4.1 and Supplier 2.1; PCA Sections 4, 23–24; NBP Propositions 9.3, 15.2 and Theorem 15.5 | Full original source, actual inverse/cube, exhaustive profiles, fixed pointwise code, complete entries, reader and simultaneous native overheads. None of $+4+r,+1,+3$ or $K=8$ is new here. |
| SI Sections 9–11; SB; TS | Existing localization, short-gap/terminal-span compensation and qualified capacity minima. Their collective identities still apply to this family; Theorem 6.1 excludes particular sufficient classes, not those general statements. |
| SI Sections 12–14; IC | Existing star/cyclic/interval-cover injections and complete consumers. Theorem 6.1 excludes all their specified fixed-initial-assignment permutation reblockings; this is no claim that their entire classes are contained here or that this family escapes all SI11 accounting. |
| SI Sections 15–18 | Interior-singleton representatives and the complete PE8 consumer. The explicit ambiguous interior cell in Theorem 6.1 is outside that hypothesis; the new theorem does not reindex the PE8 result. |
| TC Sections 1–9; CL Section 11 | Existing full-run obstruction alternatives, sparsification/common-offset results and conditional exact eight-input result. They are not reproved, numerically extended or replaced by this scoped theorem. |

The screen/shared-suffix motifs reuse the paid old-coordinate
discrimination of PCA Section 36 and PE Sections 5, 7–8. Theorem
4.2 leaves every failure completion free and compares its actual zero
axis with the whole fixed suffix, rather than assuming that suffix's
states or discriminators are unavailable elsewhere. A state-count-cell
incidence is not a separately allocated physical batch.

**Convention 8.2 (primary literature correspondence).** Abel and
Reineke's *MeMin: SAT-based Exact Minimization of Incompletely Specified
Mealy Machines*, [DOI 10.1109/ICCAD.2015.7372555][MEMIN], Section
II.A–C and Theorem 1, supplies the classical distinction between
pairwise compatible states and a successor-closed cover. Cover classes
may overlap. Their Section IV constrains complete successor choices
for implementations of given incompletely specified behavior. That
classical framework is credited, rather than replaced by an assumption
that locally compatible histories can be merged for free.

Larrauri and Bloem's *Minimization and Synthesis of the Tail in Sequential
Compositions of Mealy Machines*, [arXiv:2105.10292v2][LB], treats both
fixed-head tail minimization and tail synthesis for a given head and
specified overall target behavior: Problems 1–4, Section 5, Theorem 4
and Appendix B, and Section 6. In particular it is not limited to
compressing an already supplied tail. Its observation-machine
closed-cover construction represents all permitted implementations of
the specified behavior. Here the conceptual correspondence is that
retaining a head still leaves a genuine entire-continuation synthesis
problem, and local compatibility must respect complete successors.

Neither source supplies an original threshold state-cost lower bound,
an outer query-strategy optimum, or a transfer preserving the two
correlated costs of all actual static-input runs. A Mealy input word
cannot silently be substituted for a consistent original assignment,
nor can an observation-machine state become a free history or entry
service. Theorem 4.2 is derived directly from the retained table and
actual inputs. It does not assert a new generic closed-cover theorem.
The related fixed-faithful-tree correspondence in [ContextGeometry,
Sections 60.8–60.9 and 60.12][CG] retains its outer strategy minimization;
the paid boundary-cover correspondence in [NativeConstructorBoundaryNetworks,
Section 7.1][NCBN] retains its own acquisition contract.

The primary literature comparisons and named owning-source comparisons
are bounded attribution, not worldwide novelty or an exhaustive
repository implication classification. No mathematical algorithm, SAT
search or enumerative computation from the cited literature is part of
these proofs. The *repo-derived* attribution is for this explicit
arbitrary-completion derivation and complete consumer, with all reused
components credited above.

**Open problem 8.3 (unchanged unrestricted alternatives).** Theorem
4.2 supplies no proof that an arbitrary correct original graph contains
this fragment or can be changed into it without increasing installed
states and both execution maxima. Changing the screens or the shared
continuation escapes its hypotheses. The above-grid consumer gives no
exact retained-fragment minimum. In the unresolved general parameter
range, retain both original alternatives: prove the unrestricted
whole-graph grid lower at both original caps, or construct one complete
correct strict-subgrid graph at both caps. Existing solved parameter
cases remain suppliers, not targets of this statement.

In SI's common-support notation, the unresolved collective target is
still (SI.59), equivalently (SI.83):

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\rm cut}+\nu+
          \sum_{B\notin\mathcal L_*}(E_B-D_B),
\tag{MSC.23}
$$

where $\nu$ is the number of installed states never live, distinct
from this paper's scan length $u$. Every term is computed on the same
actual installed graph. Separate compensation in each remaining long
gap would be a stronger sufficient target, not a necessary replacement.
The overloaded state (MSC.12) alone refutes neither (MSC.23) nor the
grid lower. TC Section 9's shortage-to-actual-full-run-obstruction
implication remains unresolved beyond its supplied scopes. The
unrestricted-budget $H_{\min}$ is a separate open optimum; removing
either execution cap is not covered by Theorem 4.2. A bounded
retained-fragment result does not settle either unrestricted alternative
or the continuing research objective.

These ordinary proofs certify no physical device, acquisition service,
total memory/time/energy price or current kernel result. Distinct
quantum, stochastic timing, paid storage or calibration contracts
contribute no new operation, permission, source copy, selector, clock,
state discount or numerical bound to this original Boolean/native
argument.

[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[CP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md
[TC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THRESHOLD_COST_CERTIFICATES.md
[IC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ATTAINABLE_WEIGHT_INTERVAL_COVER.md
[SB]: FIB_NATIVE_SUPPORT_BARRIERS_AND_SHORT_BLOCK_COMPENSATION.md
[TS]: FIB_NATIVE_TERMINAL_SPAN_FIVE_STRICT_COMPENSATION.md
[CL]: RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_EIGHT_INPUT_LOWER_BOUND.md
[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[CG]: RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md
[NCBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[MEMIN]: https://embedded.cs.uni-saarland.de/publications/iccad15.pdf
[LB]: https://arxiv.org/pdf/2105.10292v2

## 追加锚（本行以下为增补区）
