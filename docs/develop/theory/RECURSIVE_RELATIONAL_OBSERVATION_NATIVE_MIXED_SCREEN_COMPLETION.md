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
## 9. 独立自由满屏延伸

**定义 9.1（扩大完成类）。** 固定定义 1.2 的参数、头部定义
2.1 和扫描标签 $U=(u_1,\ldots,u_u)$。一个有限静态图属于
${\mathcal C}_{k,L}$，当且仅当它满足下列条件。

1. 它包含定义 2.1 的五个头部状态及其字面标签和两个后继。
2. 对每个 $(s,z)$ 满足

   $$
   0\le s<k-1,\qquad 0\le z<L,\qquad s+z<u,
   \tag{MSC.24}
   $$

   它包含一个标签为 $u_{s+z+1}$ 的扫描状态 $Q(s,z)$。在回复
   $\varepsilon$ 后令
   $s'=s+\varepsilon$、$z'=z+1-\varepsilon$。若
   $s'=k-1$，后继必须是终点 $1$；若 $z'=L$，后继必须是终点
   $0$。这两个证书条件按此顺序优先，即使 $s'+z'=u$ 也如此。
   在没有证书条件且 $s'+z'<u$ 时，后继必须是
   $Q(s',z')$。在没有证书条件且 $s'+z'=u$ 时，该后继是这个
   有序边的独立自由目标；不同的有序边没有共同目标的要求。
3. 四个头部失败目标以及全部自由满 $U$ 目标的后继策略任意，只要
   最终图在每个输入上正确并实际终止，并满足定义 1.2 的两个上限。
4. 任何显示的扫描、头部或自由目标可以与另一个已安装状态相同；不要求
   角色映射单射，不要求后继并图无环，也不要求证书后的访问只读一次。

因此 ${\mathcal C}_{k,L}$ 不包含定义 2.3 的任何 $D_s$ 目标规定。
它只保留头部、未完成 $U$ 的有序扫描和两个早期证书端点；每一条
非证书的满 $U$ 边都可以独立选择其整个延伸。失败回复、付费证书尾、
物理别名和共享都在此定义中保留。各个 $c_i$ 仍两两不同，但不同坐标子集的成本和可以相等。

**引理 9.2（满 $U$ 到达的四个剩余函数）。** 设图属于
${\mathcal C}_{k,L}$，并从两个头部柱

$$
\mathcal C_\ell=\{j=0,x_1=1,x_2=0\},\qquad
\mathcal C_h=\{j=1,y_1=1,y_2=1\}
\tag{MSC.25}
$$

进入同一个扫描前缀，使 $U$ 中已有 $s$ 个一和 $z$ 个零，且
$s+z=u$。只要没有在最后一次扫描回复上触发证书，两个实际到达
继续的布尔函数如下，其中未显示的坐标可任意取值：

$$
\begin{array}{c|c|c}
s&\mathcal C_\ell&\mathcal C_h\\ \hline
k-5&0&x_1\wedge x_2\\
k-4&0&x_1\vee x_2\\
k-3&y_1\wedge y_2&1\\
k-2&y_1\vee y_2&1.
\end{array}
\tag{MSC.26}
$$

第一行在 $k=4$ 时省略。

**证明。** 头部在低柱给出一个一，在高柱给出三个一。扫描前缀再
给出 $s$ 个一。低柱剩下 $Y$，所需阈值为 $k-1-s$；高柱剩下
$X$，所需阈值为 $k-3-s$。满 $U$ 且未触发证书意味着
$s\le k-2$ 且 $z\le L-1$，而 $s+z=k+L-6$，故
$s\in\{k-5,k-4,k-3,k-2\}$，并且阈值逐行化为常值、AND、OR。
证书端点只依定义 9.1 在达到边界时优先发生；其余路径必须给出相应
阈值函数，因而得到表 (MSC.26)。每一个前缀和每一个表中延伸都来自
完整布尔输入，所以这些到达是实际到达，而不是语法路径。$\square$

**引理 9.3（两查询刚性）。** 在引理 9.2 的四种满 $U$ 情形中，
任一实际承载相应非恒定函数的状态，至多还可访问两个坐标。对四种
函数的所有实际到达同时取并集时，最终图中至少出现下列七个物理状态，
当 $k=4$ 时出现六个：

$$
\begin{array}{c|c|c}
\text{功能}&\text{必要标签及后继形状}&\text{可复用的直接测试}\\ \hline
(0,x_1\vee x_2)&x_1\text{ 根},\ x_1=0\text{ 后测 }x_2,\ x_1=1\text{ 后测 }j& I_X,E\\
(0,x_1\wedge x_2)&x_1\text{ 根},\ x_1=0\to0,\ x_1=1\text{ 后测 }x_2&I_X\\
(y_1\wedge y_2,1)&y_1\text{ 根},\ y_1=0\to0,\ y_1=1\text{ 后测 }y_2&I_Y\\
(y_1\vee y_2,1)&y_1\text{ 根},\ y_1=1\to1,\ y_1=0\text{ 后测 }y_2&I_Y.
\end{array}
\tag{MSC.27}
$$

这里 $I_X$ 的两个后继为 $(0,1)$，$I_Y$ 的两个后继为 $(0,1)$；
$E$ 的标签为 $j$ 且两个后继为 $(0,1)$。表中的同一直接测试可以
被两种功能共同使用，但根状态按其两个固定后继区分。$X$ 的 OR 根和
$x_1$ 首查询的 AND 根的最小并集为 $3+1=4$ 个状态；若 AND 根先查
$x_2$，还要增加一个根和一个 $x_1$ 直接测试。$Y$ 的两根在首查询
相同时共享一个直接测试，最小并集为 $2+1=3$ 个状态；首查询不同
时只会增加状态。故总数至少为七；$k=4$ 时 AND 行不存在，减去一个。

**证明。** 先逐一列出 $X$ 的允许首查询。对
$(0,x_1\vee x_2)$，首查询为 $x_1$ 时，回复 $0$ 只能进入一个
标签为 $x_2$、后继为 $(0,1)$ 的直接测试：此回复只在高柱可发生。
回复 $1$ 同时可能来自低柱和高柱；低柱要求输出 $0$、高柱要求输出
$1$，所以其唯一剩余的区分查询是 $j$，并且也必须有后继 $(0,1)$。
这给出 OR 根、$I_X$ 和 $E$ 三个物理状态。

OR 根若首查询 $x_2$，则在 $x_2=0$ 的后继上，低柱的固定
$x_1=1$ 要求输出 $0$，而高柱仍要求计算 $x_1$。若剩余查询为
$x_1$，同一回复 $x_1=1$ 在两柱上分别要求 $0$ 和 $1$；若查询
$j$ 或其它坐标，则高柱的 $x_1$ 仍未被处理。因此只剩一次查询时
无法同时满足这两个实际到达，$x_2$ 首查询被排除。

对 $(0,x_1\wedge x_2)$，$x_1$ 首查询是允许的：其 $0$ 后继为
终点 $0$，其 $1$ 后继为标签 $x_2$、后继 $(0,1)$ 的直接测试，
并可复用上面的 $I_X$，所以在 OR 的三态并集上只增加一个根。$x_2$
首查询也允许，但其 $0$ 后继为终点 $0$，因为该回复涵盖低柱和高柱
的 $x_2=0$ 情形；其 $1$ 后继只能进入一个标签 $x_1$、后继
$(0,1)$ 的直接测试，因为这时只有高柱的 $x_2=1$ 情形仍可发生。
该根和该直接测试分别因标签或固定后继不能与 OR 的三态合并。故无论
AND 取哪种首查询，$X$ 的并集至少有四态（$x_2$ 首查询时至少五态）。
当 $k=4$ 时 AND 行不存在，只保留 OR 的三态。

$Y$ 的两种首查询都是真实可能的。对 $(y_1\wedge y_2,1)$，
若首查询 $y_i$，则 $0$ 后继为终点 $0$，$1$ 后继为另一标签的
$(0,1)$ 直接测试；对 $(y_1\vee y_2,1)$，则 $1$ 后继为终点
$1$，$0$ 后继为另一标签的同一直接测试。于是 AND 与 OR 的根不能
合并；若两者首查询相同，直接测试可复用，得到三态；若首查询不同，
两直接测试标签不同，得到至少四态。这完整列出了 $y_1$ 先或 $y_2$
先的四种顺序组合，也没有使用交换低柱固定坐标的假设。

最后，五个头标签、四个 $X/Y$ 标签和 $j$ 彼此不同；相同标签的
根或直接测试若固定后继不同不能合并。$E$ 与头部的 $R$ 虽同为 $j$，
但前者的两个后继是终点而后者进入 $A,B$；直接测试与 $A_2,B_2$
也分别因后继为终点或 $Q(0,0)$ 而不同。故上述并集下界只使用实际
到达函数和字面后继，得到七态（$k=4$ 时六态）。\square$

## 10. 同一图上的扫描和零轴分离

**引理 10.1（扫描状态的物理单射）。** 在 ${\mathcal C}_{k,L}$ 中，
所有状态 $Q(s,z)$ 在最终安装图中两两不同。

**证明。** 不同位置的扫描状态标签分别是不同的 $u_i$。只需考虑同一
位置 $t=s+z=s'+z'$ 且 $s<s'$ 的两态，令
$\delta=s'-s=z-z'>0$。

先在同一个头部柱上考虑两个实际前缀。若两个到达都 live，则它们的
支持相同而一的个数不同，故由 [PE, Lemma 4.1][PE] 及
$(\mathrm{SI}.7)$ 不能在一个状态。低柱固定的 $j=0,x_1=1,x_2=0$
含有两个已知零，所以较小到达在低柱不 live 只能是
$2+z\ge L$，即 $z\ge L-2$。再由 $t<u=k+L-6$ 得
$s\le k-5$；于是较小到达在高柱的总一数 $3+s$ 小于 $k$，而
其零数 $z$ 小于 $L$，故高柱较小到达 live。若高柱较大到达也 live，
同样回到等支持而命中数不同的矛盾；因此它必须由一证书变成 non-live，
而高柱的正确边界是 $3+s'\ge k$，即 $s'\ge k-3$。故这一
可能分支必有 $\delta=s'-s\ge2$。

反之，若高柱较小到达已经 non-live，则 $s\ge k-3$。代入
$t<u$ 得 $z\le L-4$，从而低柱的两个到达都满足
$1+s'<k$ 且 $2+z'<L$，同样同时 live，矛盾。因此上述低柱分支
是唯一需要继续比较的分支；这也排除了 $\delta=1$，包括 $k=4$
时的边界。

若 $\delta=2$，取较小状态的高柱前缀和较大状态的低柱前缀。它们的
计数分别都是 $(3+s,z)$，但头部支持不同；[PE, Lemma 4.1][PE]
排除等命中而不同支持的共同状态。

若 $\delta=3$，取同样的两次前缀。它们实际 live，计数分别为
$(3+s,z)$ 和 $(4+s,z-1)$，所以一数和零数各相差一，违反
$(\mathrm{SI}.7)$ 所要求的两个坐标方向至少相差二。这里
$s\le k-5$ 且 $z\ge L-2$，故较大状态的低柱前缀仍满足
$4+s<k$、$2+z-3<L$。

最后设 $\delta\ge4$。由 $z'=z-\delta\le L-5$，令
$r=k-1-s'\ge1$。从较大状态沿 $r$ 个一回复，保留的扫描边在第
$r$ 步到达终点 $1$；因为 $r\le u-t$，这一路径在完成 $U$ 前
已经触发早期一证书。现在从较小状态取低柱前缀，令随后同样的 $r$
个被查询坐标取一，其余尚未暴露坐标取零。若两扫描状态相同，固定
后继使这两个实际前缀沿相同的 $r$ 个一回复到同一个终点 $1$。但
较小前缀的总一数为

$$
1+s+r=1+s+k-1-s'=k-\delta<k,
$$

所以这是一个应输出零的完整输入，矛盾。这个比较只使用实际可兼容的
回复；没有把矛盾的语法路径当成运行。故所有扫描状态物理不同。$\square$

**引理 10.2（尾态的实际到达和已证分离）。** 引理 9.3 所需的七个
（或六个）状态可以在同一最终图中选取为实际到达状态；除 $E$ 外，
每个选定状态都有一个 live 到达，其计数属于

$$
(k-2,L-1),\quad(k-1,L-2),\quad(k-1,L-1).
\tag{MSC.29}
$$

这些状态不等于任何头部状态或扫描状态；它们也不等于全零执行中经过的
$Z_d$（$2\le d\le L-1$）。本引理只分离所选尾态与 $Z_d$，不声称
$Z_d$ 与头部或扫描状态分离。

**证明。** 表 (MSC.26) 的高柱在 $s=k-5,k-4$ 时给出分别为
$(k-2,L-1)$、$(k-1,L-2)$ 的 live 根到达；低柱在 $s=k-3,k-2$
时给出相同两类的 live 根到达。OR 根的一回复后的 $I_X$ 可取高柱
$x_1=0$，给出 $(k-1,L-1)$；AND/OR 的 $I_Y$ 可分别取低柱
$y_1=1$ 或 $y_1=0$，给出 $(k-1,L-1)$ 或 $(k-1,L-2)$。
这些前缀都实际存在，因为每个完整输入的头部和 $U$ 回复都被固定后继
逐字执行。

不同尾态的标签和固定后继已经在引理 9.3 中区分。与头部的唯一可能
同标签配对是 $x_1$ 的根和 $A$、$x_2$ 的 $I_X$ 和 $A_2$、
$y_1$ 的根和 $B$、$y_2$ 的 $I_Y$ 和 $B_2$、以及 $j$ 的 $E$ 和
$R$；每一对的后继表都不同。与扫描状态的标签不同，故不存在其他
配对。

若一个 live 尾态与全零轴的 $Z_d$ 相同，支持相同或严格嵌套时已由
[PE, Lemma 4.1][PE] 与 [PCA, Theorem 35.1][PCA] 排除；在剩余的
不可比情形，将计数较小的一方放在前面使用 $(\mathrm{SI}.7)$。尾态的
一数至少为 $k-2$，而其零数至少为 $L-2$；全零轴的零数至多 $L-1$，
故零方向差不可能达到二，矛盾。对于 $E$，其标签为 $j$ 且零后继是终点
$0$。若 $Z_d=E$，则把全零轴尚未暴露的 $n-d$ 个坐标全取一；因为
$n-d\ge k$，输入应为一，但 $j$ 的已暴露零回复会使 $E$ 立即输出零，
亦矛盾。这一步只涉及尾态与零轴的比较。

扫描状态与尾态的标签分别属于 $U$ 和 $\{j,x_1,x_2,y_1,y_2\}$，
所以也不能相同。\square$

**引理 10.3（同一图中已证的部分计数）。** 对每个
$P\in{\mathcal C}_{k,L}$，同一安装图中至少有

$$
\bigl((k-1)L-10\bigr)+5+7=(k-1)L+2
\tag{MSC.30}
$$

个彼此不同的运行状态（$k\ge5$）；当 $k=4$ 时相应的三项为

$$
(3L-9)+5+6=3L+2=(k-1)L+2.
\tag{MSC.31}
$$

**证明。** 扫描格 $(s,z)$ 的完整矩形有 $(k-1)L$ 个点。令
$a=(k-2)-s$、$b=(L-1)-z$，则 $s+z\ge u$ 等价于 $a+b\le3$。
当 $k\ge5$，删除的三角形有 $4+3+2+1=10$ 点；当 $k=4$，
$a=3$ 的一个点不在矩形内，故删除九点。引理 10.1 给出剩余扫描点
的物理计数；头部有五态；引理 9.3 给出七态或六态；引理 10.2
只分离所选尾态与这些头部、扫描态。这里没有加入 $L-2$ 个
$Z_d$，因为当前假设允许 $Z_d$ 与头部或扫描态共享。所有已列加数
仍取自同一最终安装图，因而得到 (MSC.30) 和 (MSC.31)。\square$

**待证命题 10.4（零轴补足的 $m\ge kL$ 目标）。** 若在
${\mathcal C}_{k,L}$ 中还能证明

$$
Z_d\notin\{R,A,A_2,B,B_2\}\cup
\{Q(s,z):0\le s<k-1,\ 0\le z<L,\ s+z<u\}
\quad(2\le d\le L-1),
\tag{MSC.32}
$$

则引理 10.3 的计数加上 $L-2$ 个零轴状态给出 $m(P)\ge kL$。
命题 (MSC.32) 是本文尚未证明的精确物理分离义务；它必须在同一
最终图中、在允许任意失败延伸、别名/共享、付费证书尾、相等子集和及
语法循环的条件下，由实际可到达历史、固定后继、正确性和两个原始上限
推出。它不能由旧解码器的规定替代。

现有支持排除在历史层面留下一个具体的未排除别名候选。取
$k=4,L=5$，于是 $n=8,u=3$。令全零输入的 $F_{00}$ 延伸在
$j=0,x_1=0$ 后查询 $y_1=0,u_1=0$，并把该实际四零历史送入物理
状态 $Q(1,0)$，记为 $Z_4=Q(1,0)$。同一物理状态由低柱实际前缀
$j=0,x_1=1,x_2=0,u_1=1$ 到达。前者的支持和计数为

$$
S_Z=\{j,x_1,y_1,u_1\},\quad (h,z)=(0,4),
$$

后者的支持和计数为

$$
S_Q=\{j,x_1,x_2,u_1\},\quad (h,z)=(2,2).
$$

两者都 live，支持不可比，且命中差与零差都等于二，正好满足
$(\mathrm{SI}.7)$ 的方向要求。私有收费条件在这里至多给出
$C_{\{y_1\}}\le C_{\{x_2\}}$；它不强迫逐坐标成本相等，允许的
不同坐标子集和相等也没有被排除。因此 $SI.7$、私有收费律和
现有支持排除本身没有排除这个历史层面的扫描别名候选；它不是一个已经
完成的正确图反例，而是说明 (MSC.32) 仍需同时分析固定扫描后继、正确性
和两项上限。现有文字没有完成这种分析，也没有给出 $Z_d$ 与五个头态的
普遍分离。

所以 (MSC.32) 尚不是定理；原定的无条件 $m\ge kL$ 结论在
本卷中不能声称成立。当前可保留的严格结论是引理 10.3 的
$m\ge(k-1)L+2$ 部分计数；它是对目标的部分进展，不是对
$m\ge kL$ 的替代。补足 (MSC.32) 仍需新的数学论证；本文不提供该论证。\square$

## 11. 严格扩大类的完整布尔消费者

**定义 11.1（有限替换）。** 对每个 $k,L\ge4$，取定理 5.1 的完整
图、位置 $s_i=i$、四个完整失败网格、两个终点和全部头部及扫描状态。
删除其旧的 $Y_A$，并加入两个新运行态

$$
Y_A^{+}:\ y_2\xrightarrow{0}0,\quad y_2\xrightarrow{1}J_Y,
\qquad
J_Y:\ y_1\xrightarrow{0}0,\quad y_1\xrightarrow{1}1.
\tag{MSC.33}
$$

所有原来进入 $Y_A$ 的边改为进入 $Y_A^{+}$；保留 $I_Y,Y_O$、
原来四个失败网格的每一个状态和每一条边。除此有限替换外，图完全
采用定理 5.1 的定义。

**引理 11.2（替换消费者的正确性和两项上限）。** 定义 11.1 的图
在每个输入上正确并实际终止，且

$$
t(\theta)\le n,qquad J(\theta)\le W.
\tag{MSC.34}
$$

其运行状态数为

$$
M_{+}=M+1=(5k-6)L-5k+8.
\tag{MSC.35}
$$

**证明。** 旧 $Y_A$ 在低柱计算 $y_1\wedge y_2$，在高柱
$Y=11$ 上返回一。新路径先读 $y_2$，再在 $y_2=1$ 时读 $y_1$。
在低柱四种输入上，它分别给出 $0,0,0,1$；在高柱上给出一，
故两柱函数完全相同。新路径至多访问 $y_2,y_1$ 各一次，且对每个输入
的尾部收费只满足统一上界 $c_{y_2}+c_{y_1}=15$。它不满足逐输入与
旧顺序相等：例如 $(y_1,y_2)=(0,1)$ 时旧路径只付 $c_{y_1}$、
新路径付两项，而 $(1,0)$ 时旧路径付两项、新路径只付 $c_{y_2}$。
然而进入该尾的路径已经付出头部 $5+15$ 和完整扫描 $C_U$，所以
新尾的最坏总额为 $5+15+C_U+15=W$；其它解码尾没有改变，仍有同一
统一上界。故两项全局上限保持，而这里只使用最坏收费和实际的固定前缀，
不主张路线级收费相等。定理 5.1 的四个失败网格、扫描、头部和其它解码尾
没有改变，所以正确性、逐输入查询上界和终止性全部保持。由于旧图只在
有限前向网格和有限扫描尾上运行，新替换仍是有限前向图；原来同时达到
$n,W$ 的 $F_{00}$ 输入也保持不变。
最后，(MSC.35) 由删除一个状态而加入两个状态得到。$\square$

**定理 11.3（严格扩大而非旧解码类）。** 定义 11.1 的图属于
${\mathcal C}_{k,L}$，并且

$$
M_{+}-kL=(4k-6)L-5k+8\ge11k-16>0.
\tag{MSC.36}
$$

它不属于定义 2.3 的旧完整解码类。

**证明。** 只有满 $U$ 的非证书边被定义 9.1 放开。定义 11.1 保留
头部、所有未完成 $U$ 的扫描边以及 $s'=k-1$、$z'=L$ 的证书优先
边，因此属于 ${\mathcal C}_{k,L}$。在最终计数 $s=k-3$ 的非证书
扫描出口，定义 2.3 要求目标的标签为 $y_1$；定义 11.1 的目标
$Y_A^{+}$ 标签为 $y_2$。它的零后继为终点、其一后继为 $J_Y$，
所以不能把它重命名为旧 $Y_A$（旧 $Y_A$ 的一后继为 $I_Y$）。
共同的头部和扫描标签又固定了该出口，故不存在保持全部旧后继的角色
映射。因而严格不属于旧类。

由 $k,L\ge4$，(MSC.36) 的最后一个下界在 $L=4$ 时为
$11k-16>0$，其余情形更大。$\square$

## 12. 整个原生消费者

**定义 12.1（替换图的全纤维原生提升）。** 对定义 11.1 的每个布尔
运行态 $v$，若其标签为 $i$，安装原字

$$
a_i=LLL\,L^{s_i}R,qquad s_i=i,qquad c_i=s_i+4,
$$

并在回复顺序 alpha、beta、branch、absent 下安装后继

$$
\bigl(\delta(v,0),\delta(v,0),\delta(v,1),\delta(v,0)\bigr),
\tag{MSC.37}
$$

把布尔终点换成原来的两个入口锁存态。加入与定理 7.4 相同的两个
剖面态和 $r$ 个强制锁存态：

$$
\begin{array}{c|c|cccc}
\text{态}&\text{原字}&\alpha&\beta&\text{branch}&\text{absent}\\ \hline
D&RLR&\widehat e_1&R&T&\widehat e_0\\
T&RRR&\widehat e_1&\widehat e_0&\widehat e_0&\widehat e_0.
\end{array}
\tag{MSC.38}
$$

保留定义 7.1 的全体无界源、完整当前行、所有实际逆源、所有十一
剖面和全部输出内容。保留定义 7.2 的逐点函数、字面 $e_0,e_1$
入口表以及其五个完整行停机态；该入口表逐字为

$$
\begin{array}{c|c|cccc}
\text{态}&\text{原字}&\alpha&\beta&\text{branch}&\text{absent}\\ \hline
e_0&q_{i_1}R&H_{i_1}&H_0&Q_2&H_0\\
Q_2&q_{i_2}R&H_{i_2}&H_0&H_0&H_0\\
e_1&RLR&H_3&H_0&H_4&H_0.
\end{array}
\tag{MSC.38a}
$$

其中每个 $H_i$ 仍含完整字面行。独立读者仍为三运行态和五完整行停机
态，共 $K=8$，并有独立的两次调用、六个字母上限。

**定理 12.2（替换消费者的原生资源和全域正确性）。** 定义 12.1
在整个 $\mathcal U_*$ 上正确并实际终止，安装准备态数为

$$
H_{+}=M_{+}+4+r,
\tag{MSC.39}
$$

并且对每个同一来源

$$
q_P\le n+1,qquad \ell_P\le W+3.
\tag{MSC.40}
$$

同一个实际来源同时达到两个上限。所有字面代码、完整 $e_0/e_1$
条目、前驱行输出和独立 $K=8$ 读者均保持原样。

**证明。** 对 $Z_{b_3}$ 剖面，定义 7.1 的分支值给出向量
$\theta(x_a)\in\{0,1\}^n$。由 [WTF, Supplier 2.1][WTF] 的逐地址
恒等式，(MSC.37) 在每次访问上恰好读取该向量对应的位；alpha、beta
和 absent 的零回复也由同一后继表处理。因此原生运行逐步投影为定义
11.1 的完整布尔运行，包含所有重复访问和所有自由尾，最后进入原来的
字面入口锁存态。

在其余剖面，$D$ 的 alpha 恰为 $\Pi_3$，beta 进入布尔图，branch
进入 $T$；$T$ 的 alpha 恰为 $\Pi_4$，其余情形进入零入口。于是
定义 7.2 的十一剖面划分在整个无界纤维上都得到原来的逐点函数。由于
每个有限源的外部、重复、相等类、不等类和严格前缀阻塞条件都由同一
完整读者处理，输出仍是原来的完整当前行与对应目标。

布尔表的每次访问对应一个字面 $a_i$，故在选定剖面上

$$
q_P=1+t_B,\qquad \ell_P=3+J_B.
\tag{MSC.41}
$$

其它剖面至多进行两次调用、六个字母；$n\ge7$ 且每个 $c_i\ge5$，
故它们被 (MSC.40) 支配。引理 11.2 给出所有布尔输入的两项上限，
而定理 5.1 中同时饱和 $n,W$ 的实际立方来源在全纤维提升中给出
$n+1,W+3$。安装数由 $M_+$ 个布尔运行态、两剖面态和 $2+r$
个入口锁存态组成，得到 (MSC.39)。独立读者的八态和其新鲜调用不计入
准备态，也不改变 (MSC.39)--(MSC.40)。$\square$

**条件推论 12.3（附加零轴义务下的原生下界）。** 设一个原生准备器在
$(H,n+1,W+3)$ 下满足 [WTF, Theorem 4.1][WTF] 的投影条件，且其
布尔投影属于 ${\mathcal C}_{k,L}$。若该投影的同一最终图还满足
(MSC.32) 的零轴物理分离义务，则

$$
H\ge kL+4+r.
\tag{MSC.42}
$$

**证明。** [WTF, Theorem 4.1][WTF] 的投影在两个上限下给出一个完整、
正确、实际终止的布尔图；其运行态数 $m$ 满足 $m\le H-4-r$。
在附加 (MSC.32) 时，命题 10.4 给出同一个投影图的 $m\ge kL$，
故 $H-4-r\ge kL$，即 (MSC.42)。本推论明确保留其附加前提；
当前卷没有证明该前提，所以没有无条件的原生 $kL+4+r$ 下界。
它也不把任意原生图正规化为 ${\mathcal C}_{k,L}$，不把 $M_+$ 当作
扩大类的精确最小值。\square$

## 追加锚（本行以下为增补区）
## 13. 自由完成类的现行命题与常值尾限定

**约定 13.1（范围及被取代的推断）。** 以下始终使用定义 9.1 的
原类 $\mathcal C_{k,L}$，其中 $k,L\ge4$、$n=k+L-1$、
$u=k+L-6$。所有原坐标各有不同的正整数位置 $s_i$，收费仍为
$c_i=s_i+4$。保留两个同输入上限 $t\le n$、$J\le W$。
每条非证书满 $U$ 有序边的目标及整个后续策略独立自由；不要求相同
最终计数的不同边具有同一个目标。$s'=k-1$ 的终点一和 $z'=L$
的终点零仍优先，包括恰在最后一次 $U$ 查询发生的证书。

本节及以下结论对旧文字作如下明确限定和取代。

| 旧编号 | 现行解释 |
| --- | --- |
| 引理 9.3 与 (MSC.27) | 常值分支必须立即停机的必要性断言不成立；整张旧解码表不能作为扩大类的必要形状。保留的数值尾态下界由引理 15.3–15.5 重新证明。 |
| 引理 10.2 | 按一种固定首查询顺序列出的同标签配对并不穷尽所有允许尾。现行物理分离使用引理 15.6，覆盖两种首查询顺序及付费常值尾。 |
| 引理 10.1 的末段 | 短一链可在最后一个 $U$ 坐标上取得证书，不必严格早于满 $U$；引理 15.1 包含等号情形。 |
| 命题 10.4、(MSC.32) 及其历史层面别名候选 | (MSC.32) 由定理 14.5 对整个定义 9.1 类证明；旧文的“尚未证明”不再描述现行数学结论。该候选不是可行完整图，见定理 14.5。 |
| 条件推论 12.3 | 零轴分离不再是额外前提；推论 16.2 仍明确要求所用的特定布尔投影属于定义 9.1。 |
| 定理 12.2 证明中的“完整当前行与对应目标” | 当前行是固定的来源条件；准备输出原入口代码，读者输出完整前驱行 $F(\tau)=R_P(\tau)$，见命题 17.3。 |

定义 2.3 的字面解码表仍合法地定义旧的较小类，定理 4.2 在该类的
结论不受上述限定影响。这里不把旧的必要性错误改写成扩大类的新假设。
引理 10.3 的数值结论也不凭旧的过强形状论证使用，而由下面完整的
物理并集论证取得。

**命题 13.2（常值分支确实可以付费继续）。** 对所有 $k,L\ge4$，
在原位置 $s_i=i$ 上，定义 9.1 允许完整正确图在满 $U$ 后的常值
分支再付费查询一次。

证明。取定理 5.1 的完整图，仅将 $Y_A$ 的零后继从终点零改接到
一个新态 $C$。该态标签为 $j$，两个后继均为终点零。四个失败网格、
头部和全部扫描边保持原样。满 $U$ 后进入 $Y_A$ 的低柱要求
$y_1\wedge y_2$；若 $y_1=0$，新尾在再读一次 $j$ 后仍返回零。
高柱固定 $Y=11$，不取该零边。其余路径没有改变，因而整个原输入域
上的正确性和实际终止保持。新尾最多两次查询，收费最多

$$
\max(c_{y_1}+c_j,c_{y_1}+c_{y_2})
 =\max(7+5,7+8)=15.
\tag{MSC.43}
$$

故定理 5.1 的同输入 $n,W$ 上限都保持。所有证书优先边保持，故
新图属于定义 9.1。它的这个常值分支并非立即停机。这只用于否定
必要形状，不作为另一个新消费者成果；无需执行该图。$\square$

**约定 13.3（实际历史供应及其适用性）。** 以下使用的局部事实是
[SI, 定义 2.1、定理 2.2 及 (SI.7)][SI]、[PE, 引理 4.1][PE]、
[PCA, 定理 34.3、35.1][PCA] 和 [WTF, 定理 9.1][WTF] 的供应结论。
对同一个可行最终布尔图，它们给出：

- 每个实际 live 历史的下一查询未读过；此前恰有 $h+z$ 次查询，
  每个旧赋值的完整延伸都实际遵循该前缀。
- 相同支持而不同一数、不同支持而相同一数，以及严格嵌套支持的两个
  live 历史不能共用一个物理态。
- 若共用一个物理态的两次 live 到达有不同计数，并按 $h<g$ 定向，
  则必须同时有

$$
g-h\ge2,\qquad z-w\ge2
\quad\text{对计数 }(h,z),(g,w).
\tag{MSC.44}
$$

其使用路线是对整个正确布尔图作 [WTF, 定理 4.1][WTF] 的全纤维
提升，得到原准备器在每个来源上的 $n+1,W+3$ 上限；每个布尔实际
历史成为付费剖面前端后的实际选定位立方历史。所用态是原来的选定
字态，而不是任意无关原生态。这里 $n\ge7$ 且
$4\le k\le n-3$，包含于这些供应结论的 $n\ge6$、
$3\le k\le n-2$ 范围。两项执行上限、完整来源正确性和不同单坐标
成本都是其前提。不同子集的成本和可以相等；(MSC.44) 不要求排除此类
等式。供应结论不禁止认证后付费重读，不赋予物理态唯一剩余函数。

对每个显示的 $Q(s,z)$，从低、高两个头柱各取一个具有相同 $U$
前缀字的实际输入。此前所有扫描计数都不超过 $s<k-1,z<L$，且此前
扫描长度小于 $u$，所以两柱都逐边到达这个角色。对应的总计数为

$$
(1+s,2+z),\qquad(3+s,z).
\tag{MSC.45}
$$

到达的实际性不要求其仍 live；后文每次使用局部排除时另行检查
liveness。各个自由满 $U$ 目标可以不同，这个到达论证没有合并它们。

## 14. 实际零前缀的短证书与 MSC.32

**引理 14.1（同一全零运行上的零轴）。** 对每个
$P\in\mathcal C_{k,L}$ 和 $2\le d\le L-1$，全零输入在第 $d$
次查询后仍有一个运行态 $Z_d$。其实际前缀有 $d$ 个不同的已读零
坐标，支持 $S_d$ 含 $j,x_1$。这 $L-2$ 个态两两不同。

证明。$d<L$ 时零证书未取得，一证书也未取得，且
$n-d\ge k$；该前缀有两个输出的完整延伸，不能停机。约定 13.3
给出每次 live 查询的新鲜性。前两步由头部固定为 $j=0,x_1=0$。
同一固定输入若两次访问同一个运行态，从该态开始的静态确定性后缀将
永久重复，违反实际终止。因此各个 $Z_d$ 是不同的物理态。
此处没有要求整个语法并图无环。$\square$

**引理 14.2（live 零前缀后没有短一证书链）。** 在引理 14.1 的
实际零前缀之后，其当前态不能有一条由 $r$ 个一后继组成、终止于
终点一的固定链，其中 $1\le r\le k-1$。

证明。假设有这样的固定链，逐步尝试在旧的 $d$ 个零之后实际执行。
已执行其中 $a$ 步而下一步尚未执行时，$0\le a<r$。归纳保持一数为
$a<k$、零数为 $d<L$，且已有回复与某个完整输入相容，所以这是
实际 live 前缀。下一态的查询标签由约定 13.3 必须尚未暴露；若它是
旧零标签，或重复了链上已有标签，这个查询本身已违反新鲜性。否则将
该新坐标赋一，所有完整延伸逐边遵循其固定一后继，归纳继续。

经过 $r$ 步后已到终点一。保留旧零和这 $r$ 个新一，将其余未读坐标
全赋零，得到遵循上述前缀及链的完整实际输入。它恰有 $r<k$ 个一，
却接受，违反正确性。链的相容性在每一步由 live 新鲜性证明，未将任意
语法链预先视为实际运行。$\square$

**引理 14.3（零轴与全部头态分离）。** 每个 $Z_d$ 均不等于
$R,A,A_2,B,B_2$。

证明。$R$ 和 $A$ 分别查询已经在零前缀暴露的 $j,x_1$，不能成为
live 的 $Z_d$。$A_2$ 有实际 live 到达 $j=0,x_1=1$，计数
$(1,1)$；$B$ 有实际 live 到达 $j=1$，计数 $(1,0)$。它们与
$(0,d)$ 的一数差为一，违反 (MSC.44)，故也不能与 $Z_d$ 相同。

若 $Z_d=B_2$，新鲜性先保证其标签 $y_2\notin S_d$。取
$y_2=1$，这是旧前缀的合法完整延伸，固定一边实际进入 $Q(0,0)$。
新计数 $(1,d)$ 仍 live，因为 $1<k,d<L$，支持为
$S_d\cup\{y_2\}$。另一方面，低头柱 $j=0,x_1=1,x_2=0$
实际进入同一个 $Q(0,0)$，live 计数为 $(1,2)$，支持为
$\{j,x_1,x_2\}$。前一支持含 $y_2$，后一支持不含，故它们不同，
但一数同为一，违反 PE 的等命中不同支持排除。该排除不要求两次
到达在共同坐标上的旧赋值相同，也包括支持嵌套的情形。因此 $B_2$
也被排除，包含 $d=2$ 和 $d=L-1$。$\square$

**引理 14.4（零轴与全部扫描态分离）。** 对所有显示的扫描角色和
所有 $2\le d\le L-1$，均有 $Z_d\ne Q(s,z)$。

证明。以下三个整数区间与 $0\le z<L$ 的交集穷尽所有情形。

若 $z\le L-5$，令 $r=k-1-s$。由扫描范围可知
$1\le r\le k-1$，而

$$
u-(s+z)-r=L-5-z\ge0.
\tag{MSC.46}
$$

故从 $Q(s,z)$ 连续取 $r$ 个一回复，前 $r-1$ 步沿保留的未完成
扫描边，最后一步触发 $s'=k-1$ 的终点一。即使 (MSC.46) 等号成立，
这仍是最后 $U$ 查询上的优先证书边，绝非自由满 $U$ 边。若当前态为
$Z_d$，该固定链违反引理 14.2。

若 $L-4\le z\le L-3$，取 (MSC.45) 的低柱到达。其一数
$1+s\le k-1$、零数 $2+z\le L-1$，故确实 live。若它与
$(0,d)$ 共态，(MSC.44) 要求 $d-(2+z)\ge2$；但是

$$
d-(2+z)\le L-3-z\le1,
$$

矛盾。一数差恰为一时也已包含在同一排除中。

若 $L-2\le z\le L-1$，由 $s+z<u$ 的严格整数不等式得
$s\le k-5$。因此高柱到达 $(3+s,z)$ 满足 $3+s\le k-2<k$、
$z<L$，确实 live。共态将要求 $d-z\ge2$，但
$d-z\le1$，仍矛盾。这里没有对可能已认证的低柱误用 live 定理。

当 $L=4$ 时第一段为空，第二段为 $z=0,1$；当 $k=4$ 时第三段
没有显示角色，因为会要求 $s\le-1$。因此两端点同时发生的
$k=L=4$ 也已覆盖，未增加任何参数限制。$\square$

**定理 14.5（整个扩大完成类的零轴补足）。** 对每个
$k,L\ge4$、每组原位置及每个 $P\in\mathcal C_{k,L}$，
(MSC.32) 成立，即所有 $Z_d$ 同时位于全部头态及扫描态之外。

证明。将引理 14.3 和 14.4 用于同一最终安装图即可。证明没有沿任一
自由非证书满 $U$ 边规定后续策略，也没有限定失败延伸。

旧命题 10.4 的 $k=4,L=5,Z_4=Q(1,0)$ 只通过了若干历史局部过滤，
不能扩成满足全部要求的完整图：从该扫描态有两条连续一边，经 $u_2,u_3$
在最后 $U$ 边触发终点一。引理 14.2 使该链在实际四零前缀之后
不可能存在；在旧文显示的支持上，两坐标确实尚未暴露，直接将它们取一、
其余未读位取零就会接受一个总重二的输入。否定的是该候选的完整可行性，
并非否定允许共享或相等子集和的模型。$\square$

## 15. 允许常值付费尾和任意首变量顺序的物理并集

**引理 15.1（扫描单射的供应论证，含最终证书等号）。** 同一
$P\in\mathcal C_{k,L}$ 的全部扫描角色两两为不同物理态。

证明。复用引理 10.1 的实际历史论证，并明确其等号边界。不同扫描
位置有不同标签，只须比较同位置 $t$、$s<s'$ 的两个角色。令
$\Delta=s'-s=z-z'>0$。若两个低柱到达均 live，相同支持不同一数
已被排除。否则较小 $s$ 的低柱必已负认证，即 $z\ge L-2$。
由 $t<u$ 得 $s\le k-5$，故较小 $s$ 的高柱 $(3+s,z)$ live。
若较大 $s'$ 的高柱也 live，再次由等支持不同一数排除；否则
$s'\ge k-3$，因而 $\Delta\ge2$。

$\Delta=2$ 时，较小高柱和较大低柱均 live，且有相同计数
$(3+s,z)$，但支持分别含 $Y$ 和 $X$，彼此不同，不能共态。
$\Delta=3$ 时，这两次到达分别有计数 $(3+s,z)$、$(4+s,z-1)$；
后者 live，因为 $s\le k-5$。一数差一违反 (MSC.44)。

$\Delta\ge4$ 时，较大角色的 $z'=z-\Delta\le L-5$。令
$r=k-1-s'\ge1$，则

$$
u-t-r=L-5-z'\ge0.
\tag{MSC.47}
$$

连续 $r$ 个一回复沿保留的扫描边到终点一，允许最后一步恰为最后
$U$ 查询。现在取较小角色的低柱实际前缀，将这些随后不同的、此前
未读的 $U$ 坐标取一，其他未读位取零。即使这个低柱已经负认证，它
仍实际沿固定扫描边继续；这里使用明确的未来 $U$ 标签相容性，不对
认证前缀调用新鲜性。若两个角色物理相同，固定后继归纳迫使此输入也
接受，而其总一数是

$$
1+s+r=k-\Delta<k,
$$

矛盾。所有同位置的不同角色均已分离。这是扫描单射的复用与边界限定，
不计为独立的新供应定理。$\square$

**引理 15.2（两个剩余查询只强制 pivotal 分支）。** 固定一个实际
非证书满 $U$ 前缀字，并从两头柱沿它到达其同一个自由目标。此时已
付出 $3+u=n-2$ 次查询，故每个后缀最多两次。若其中一柱的剩余函数
是两个未读坐标的 AND 或 OR，则该目标必须是运行态，首标签为这两
坐标之一。在 AND 的首回复一或 OR 的首回复零之后，必须直接查询
另一坐标，且其零、一后继分别为终点零、一。首查询后函数为常值的
分支仍可以付出剩下的一次查询。

证明。在非恒定柱上，两变量都本质相关。若首标签不是二者之一，它在
此柱已固定；其后仅余一个固定查询，不能计算依赖两个自由变量的 AND
或 OR。若首标签为其中之一，在所列 pivotal 回复后，目标恰为另一
自由位，且只剩一次查询。标签必须是该位；两种回复均由完整输入实现，
故二者都必须直接到相应终点，不能再进入运行态。对另一回复，目标已
为常值，正确性和调用上限只要求其在剩余一次内给出该常值，并不要求
立即停机。$\square$

**引理 15.3（$X$ 侧与直接 $j$ 测试）。** 同一最终图内，从
$(0,x_1\vee x_2)$ 的一对满 $U$ 到达至少强制三个物理态。若
$k\ge5$，再包括 $(0,x_1\wedge x_2)$ 的到达，至少强制四态。
每个所选 $X$ 态都有 live 到达；另外一态为标签 $j$、后继 $(0,1)$
的直接测试 $E$。这只是强制的实际子结构，不是规定整个自由解码器。

证明。对最终 $U$ 一数 $k-4$ 任选一个前缀字，使两柱实际到达其
同一个自由目标 $O_X$。这些满 $U$ 字存在：其零数为 $L-2<L$，
一数小于 $k-1$，所以不经过任何扫描证书边。高柱的非恒定 OR
使首标签只能为 $x_1$ 或 $x_2$。

若首查 $x_2$，回复零在两柱上都可能。高柱此时必须在唯一余下查询
直接计算 $x_1$，两终点为 $(0,1)$；低柱固定 $x_1=1,x_2=0$，
却要求零，沿同一直接测试会输出一，矛盾。因此 $O_X$ 必先查 $x_1$。
回复零只在高柱发生，强制一个标签 $x_2$、终点后继 $(0,1)$ 的态
$I_X$。回复一在两柱都发生，低柱要求零、高柱要求一；其唯一剩余
查询必须区分这两组完整输入。

只有 $j$ 能对这些组恒为零和一。两组中 $x_1$ 均为一，$U$ 字完全
相同；高柱的 $x_2$ 可为低柱的零，低柱的 $Y$ 可为高柱的 $11$。
因此除 $j$ 外，每个标签都有两组要求相反输出而回复相同的完整输入，
一次查询不能区分。故一后继必为直接 $j$ 测试 $E$，零、一回复均实际
发生，后继分别为终点零、一。三个态的标签各异。

$O_X$ 在高柱的 live 计数为 $(k-1,L-2)$；$I_X$ 在该柱的
$x_1=0$ 后有 live 计数 $(k-1,L-1)$。若 $k\ge5$，再取最终
一数 $k-5$ 的一个满 $U$ 字，其高柱为非恒定 AND，实际根记为
$A_X$，live 计数为 $(k-2,L-1)$。它先查 $x_1$ 或 $x_2$ 均允许；
其 pivotal 一回复后直接测另一位。无论首标签是哪一个，(MSC.44)
的一数差一都排除 $A_X=O_X$ 或 $A_X=I_X$；标签排除 $A_X=E$。
故至少增加一个根，得到四态。

更具体地，$x_1$ 先时其一后继为直接 $x_2$ 测试，可以与 $I_X$
共享；其常值零分支不作即停规定。$x_2$ 先时还强制一个直接 $x_1$
测试，live 计数为 $(k-1,L-1)$。它不能与 $O_X$ 合并：二者同一数，
而支持大小分别为 $n-1,n-2$，由 PE 等命中不同支持排除；它与
$A_X$ 一数差一，与 $I_X,E$ 标签不同。因此反向 AND 顺序至少
给出五态，绝不减少上述四态下界。$k=4$ 时 AND 行不存在，保留
OR 的三态。$\square$

**引理 15.4（$Y$ 侧的两种允许顺序）。** 从
$(y_1\wedge y_2,1)$ 和 $(y_1\vee y_2,1)$ 的实际满 $U$ 到达，
同一图中至少强制三个 $Y$ 标签物理态。两根的首标签可以各自独立选择
$y_1$ 或 $y_2$；首标签不同时至少有四态。

证明。分别选最终一数 $k-3,k-2$ 的一个满 $U$ 字。其零数为
$L-3,L-4$，故两种非证书到达在所有参数上均存在。低柱的 AND 根
$A_Y$ 和 OR 根 $O_Y$ 分别有 live 计数

$$
p_-=(k-2,L-1),\qquad p_+=(k-1,L-2).
\tag{MSC.48}
$$

引理 15.2 允许各根先查任意一个 $Y$ 坐标；AND 的一回复和 OR
的零回复均强制直接测另一位，各给一个 live 计数

$$
p_*=(k-1,L-1).
\tag{MSC.49}
$$

两根因一数差一不能共态。任选上述一个直接测试：它与 AND 根一数差
一，与 OR 根虽一数相同，但支持大小为 $n-1$ 对 $n-2$，都不能
共态。因此至少三态。若首标签不同，两条 pivotal 分支的直接测试
标签也不同，故两根和两直接测试共至少四态。若首标签相同，允许两根
共享那个直接测试，仍有三态。证明同时覆盖四种首标签组合，没有要求
任何常值分支立即停机。$\square$

**引理 15.5（常值尾自由下的六／七态数值界）。** 在同一个最终图中，
可以选出至少七个尾态（$k\ge5$），或六个尾态（$k=4$）。除 $E$
外，每个所选态都有实际 live 到达，计数属于

$$
\{p_-,p_+,p_*\}.
\tag{MSC.50}
$$

证明。引理 15.3 给出 $X/j$ 的四态或三态，引理 15.4 给出
$Y$ 的三态。这两组标签不交，内部的物理分离均已证明，故可加。
只选择实际存在的一组根与其必需直接测试；不同自由满 $U$ 边可能
还需要更多态，并不影响下界。不将这些自由目标人为汇成一个 $D_s$。
这些尾态可以有其他认证或 live 到达，后继也可在其他地方共享。
其计数只描述所选实际历史，不是每态唯一计数标签。$\square$

**引理 15.6（所选尾态与头、扫描、零轴的完整分离）。** 引理 15.5
的尾态都不等于五个头态、任何扫描态或任何 $Z_d$。

证明。非 $E$ 尾态的标签属于 $X\cup Y$，与扫描标签 $U$ 不交。
五头态依次在 $R,A,A_2,B,B_2$ 有下列实际 live 计数：

$$
(0,0),\ (0,1),\ (1,1),\ (1,0),\ (2,0).
\tag{MSC.51}
$$

所选非 $E$ 尾态的 live 一数至少 $k-2\ge2$，零数至少
$L-2\ge2$。若其一数大于某个头态的一数，共态将由 (MSC.44)
要求“头态零数减尾态零数至少二”，而头态零数至多一，矛盾。唯一
可能等一数的情形是 $k=4$、二命中尾态对 $B_2$；尾态支持大小至少
$n-2\ge5$，而 $B_2$ 的支持大小为二，PE 等命中不同支持排除共态。
因此任一首标签选择都已与头部完整分离，未依赖一种固定解码器的
同标签配对清单。

与零轴比较时，一数由零增到尾态一数。若共态，(MSC.44) 要求
$d-z_{\rm tail}\ge2$；但 $d\le L-1$、
$z_{\rm tail}\ge L-2$，所以该差至多一，矛盾。

$E$ 的标签为 $j$，与全部扫描和其余四头态标签不同；它的两个
后继是终点，$R$ 的两个后继为运行态 $A,B$，故 $E\ne R$。
若 $E=Z_d$，其已读 $j=0$ 标签违反该实际 live 历史的新鲜性。
这也说明 $E$ 虽可只在认证历史上承担付费重读，仍不能成为零轴的
live 态。所有所需物理分离均在同一最终图中完成。$\square$

## 16. 同一最终图的网格下界与投影限定原生后果

**定理 16.1（独立自由非证书满屏完成的双上限下界）。** 对每个
$k,L\ge4$、每组原位置 $s_1<\cdots<s_n$，每个定义 9.1 的完整
正确、实际终止且满足两个原同输入上限的图均满足

$$
\boxed{m(P)\ge kL,\qquad m(P)+2\ge kL+2.}
\tag{MSC.52}
$$

这里 $m$ 包括全部已安装运行态，第二项包括两个不同终点。允许所有
定义 9.1 中的失败策略、独立非证书满 $U$ 延伸、物理别名、共享、
认证后付费访问及语法并图循环；不另加解码器、只读一次或子集和条件。

证明。引理 15.1 给出扫描角色的物理单射。完整扫描矩形有
$(k-1)L$ 个角色，删去 $s+z\ge u$ 的角三角形。令
$a=k-2-s,b=L-1-z$，被删条件正是 $a+b\le3$。$k\ge5$ 时
删十点，$k=4$ 时删九点，因为 $a=3,b=0$ 不在矩形。五个头态
因标签不同而互异，且其标签不属于 $U$。引理 15.5、15.6 再给出
与全部头态和扫描态分离的七态或六态。因此在此同一图中已选的物理
并集至少有

$$
\begin{cases}
((k-1)L-10)+5+7=(k-1)L+2,&k\ge5,\\
(3L-9)+5+6=3L+2,&k=4.
\end{cases}
\tag{MSC.53}
$$

引理 14.1 的 $L-2$ 个零轴态两两不同；定理 14.5 将它们与全部
头态、扫描态分离，引理 15.6 将它们与所选尾态分离。所以

$$
m(P)\ge ((k-1)L+2)+(L-2)=kL.
$$

每个加数都是已经证明互不相交的物理态集合的基数。没有将同一态的
多个计数单元关联计成多个安装，也没有把付费区分器或另一条输入的
费用当作额外安装批次。所有供应排除均应用于此同一个满足两项上限
的最终图；证明不声称去掉任一上限后仍有同样结论。$\square$

**推论 16.2（原入口准备器的限定下界）。** 保留定义 7.1–7.2、
假设 7.3 的整个原生来源、逐点代码和服务契约。设一个原准备器在
每个实际来源上正确并终止，所有安装准备态和强制锁存态总数为 $H$，
且同时满足 $q_P\le n+1$、$\ell_P\le W+3$。若 [WTF, 定理
4.1][WTF] 对它所得的特定完整布尔投影属于定义 9.1，则

$$
\boxed{H\ge kL+4+r.}
\tag{MSC.54}
$$

不再假设该投影另行满足 (MSC.32)。

证明。该供应投影在每个布尔输入上正确、实际终止，同时满足
$t\le n,J\le W$，其安装运行态数 $m\le H-4-r$。它按前提属于
$\mathcal C_{k,L}$，故定理 16.1 给出 $m\ge kL$。于是
$H\ge m+4+r\ge kL+4+r$。$+4+r$ 已包括两个剖面运行态和
$2+r$ 个锁存态的原对应开销；不再将布尔两终点重复加一次。独立
读者的 $K=8$ 也不并入这个准备态计数。投影成员条件仍是实质前提，
没有证明任意准备器都满足它。$\square$

## 17. 既有严格扩大消费者的全域含义

**命题 17.1（完整布尔消费者及共同资源见证）。** 定义 11.1 的
既有完整图 $P_+$ 对每个 $k,L\ge4$ 均提供定理 16.1 的非空、
严格超出旧规定解码类的消费者。在其原位置 $s_i=i$ 上，

$$
M_+=(5k-6)L-5k+8>kL,\qquad
 t_{P_+}(\theta)\le n,\quad J_{P_+}(\theta)\le W
 \quad(\theta\in\{0,1\}^n),
\tag{MSC.55}
$$

且同一个完整输入同时达到 $n,W$。此命题复用整个定义 11.1 和
第 5、11 节的构造，不另取一个仅在成功柱正确的局部表。

证明。两个成功头柱和四个失败头柱划分整个原布尔域。四个失败目标
在定义 11.1 中仍有定理 5.1 的全部独立网格，依次在未读列表
$(y_1,x_2,y_2,U)$、$(y_1,y_2,U)$、$(x_1,x_2,y_2,U)$、
$(x_1,x_2,U)$ 上计算阈值 $k,k-2,k-1,k-2$。其安装数依次为
$k(L-2),(k-2)(L-1),(k-1)(L-1),(k-2)(L-1)$。
每个失败输入只查询每个旧头标签一次、每个随后未读标签至多一次，
所以对这个同一输入有 $t\le n,J\le W$；每条可能的网格边和终点
已经定义，不存在未付费的 fallback。

两个成功柱上，扫描证书终点的正确性由第 3 节给出的总阈值判断保证。
非证书满 $U$ 的四行函数是引理 9.2 的函数。唯一替换把低柱
$y_1\wedge y_2$ 改成先查 $y_2$、再于一回复查 $y_1$；高柱固定
$Y=11$，同样返回一。故所有成功输入正确。它们至多查询三次头部、
$u$ 次扫描、两次尾部，合为 $n$。对定义 5.1 的字面位置，

$$
c_j=5,\quad C_X=C_Y=15,\quad
W=5+15+15+C_U.
\tag{MSC.56}
$$

两个成功头的实际费用均为 $5+15$；扫描费用不超过 $C_U$；
$X$ 的 AND 尾至多十五，OR 尾至多
$\max(c_{x_1}+c_{x_2},c_{x_1}+c_j)=15$；$Y$ 的 OR 及替换后的
AND 尾均至多 $c_{y_1}+c_{y_2}=15$。故同一成功输入的总费用
至多 $W$，包括所有旧位重读、$E$ 的第二次 $j$ 查询和认证后访问。
没有声称替换前后每个输入的收费相等；只使用各条实际路线的共同上界。

完整图仍由有限前向头、扫描、尾和四个有限前向失败网格组成，所有
实际输入终止。安装数从旧 $M$ 删除 $Y_A$ 而加入 $Y_A^+,J_Y$，
所以为 $M+1=M_+$；每个安装态均计入。并且

$$
M_+-kL=(4k-6)L-5k+8\ge11k-16>0.
\tag{MSC.57}
$$

取 $j=x_1=0$，在 $F_{00}$ 的未读列表上将前 $k-1$ 个位置置一，
其余位置置零。这一列表长 $N=n-2$，负证书需要 $N-k+1=L-2$
个零。每个真前缀既未有 $k$ 个一，也未有 $L-2$ 个零，故网格
读完其整个列表才拒绝。连同头部，两项资源恰为 $n,W$，在同一个
输入上同时取得，未在不同输入上分别取最大值。

旧解码类的非证书出口 $s=k-3,z=L-3$ 在所有参数上实际存在。可取
该计数的一个满 $U$ 字；其所有较早计数均在扫描内。现在它的目标为
标签 $y_2$ 的 $Y_A^+$，而旧定义 2.3 在这个出口要求标签 $y_1$。
任何保持起点、头部及全部扫描后继的旧角色映射，都由逐边归纳固定
这些实际前缀和出口，不能另选一个 $y_1$ 态代替其真实后继。
故不存在旧完整片段的角色映射。这个理由不依赖状态名字，也不把
定义 9.1 的所有自由目标规定成该消费者的目标。$\square$

**命题 17.2（既有过载和覆盖排除在替换后保留）。** 定义 11.1 的
消费者仍有定理 6.1 的实际过载、任意长晚间隙和指定充分子类的排除。
这些性质与消费者本身均为复用，不作为定理 16.1 之外的新成果计数。

证明。$Q(0,0)$ 的实际 live 头历史 $010,111$ 完全未改；其集合对
仍是 (MSC.12)，质量至少 $1/3+1=4/3$，且只有一个有向冲突。
所有用于深度 $2,\ldots,n-3$ 的支持差异见证都在被替换尾之前。
深度 $n-2$、$n-1$ 的原见证只使用高柱的 $X_O,I_X$ 和低柱的
$Y_O,I_Y$，也未改变。因此完整 common-support 切口仍为
$0,1,n$，其中 $n$ 为 SI 的形式端点，晚间隙跨度 $n-1$ 无界。
同一 $j=0$ 初始赋值下第三查询分别为 $y_1,x_2$ 的两条 live
历史未变，所以 SI12–SI14 和 IC 的指定固定初始赋值单排列形式
仍不能经重分块覆盖。内部计数单元 $(1,2)$ 的历史 $010,001$
也未变，仍排除 SI15 的内部单支持前提。排除的是那些明确的充分
假设，不是 SI 的一般恒等式、集体补偿目标或它们的全部推论。
$\square$

**命题 17.3（整个原生纤维、原代码与独立完整读者）。** 定义 12.1
的既有提升在定义 7.1 的整个 $\mathcal U_*$ 上保留完整正确性和
实际终止，且

$$
H_+=M_++4+r,\qquad
q_P(\tau)\le n+1,\quad \ell_P(\tau)\le W+3
\quad(\tau\in\mathcal U_*).
\tag{MSC.58}
$$

存在同一个实际来源同时达到两项执行上限。结论继续使用原来的逐点
函数 $\sigma_{A,k}$、原来的两个入口锁存态、完整 $e_0,e_1$ 表和
独立 $K=8$ 读者；没有重新编码。

证明。这里的来源仍是全部有限非空有序 $\alpha/\beta$ 树，更新为
$\rho\alpha=\beta$、$\rho\beta=\langle\beta,\alpha\rangle$，
对子树同态作用；不限制大小、深度或形状。当前行、每个实际逆源及
整个原纤维均使用 (MSC.15)–(MSC.17) 和已供应的像语法。像逆在
此只用于数学来源见证，不是提供给准备器的逆操作。全体有限原根地址
仍合法，包含空地址与越过叶子后的 absent；相等值的不同出现保持
各自出现位置。

在 $Z_{b_3}$ 上，任意允许的分支像 $x_a$ 给出定义 7.2 的静态
$\theta_i(x_a)$。每个布尔态的字面原字仍为 $a_i=LLL L^{s_i}R$；
其四个实际回复 alpha、beta、branch、absent 分别沿零、零、一、零
后继。逐地址出现恒等式保证每次查询都是此同一向量的对应位，包括
非梳状像、叶回复、缺失回复、重复和认证后查询。无需在运行配置中
保存向量或计算地址。因此该来源的完整原生运行投影为其完整布尔运行，
在原锁存态输出原来规定的阈值代码。

其余来源由原来的 $D:RLR$、$T:RRR$ 两态前端穷尽。$D$ 的 alpha
恰为 $\Pi_3$，输出一；beta 恰为 $Z_{b_3}$，进入布尔表。
$D$ 的 branch 进入 $T$，其中 alpha 恰为 $\Pi_4$，输出一，
其余输出零。由十一个完整剖面的划分，这涵盖 $\Pi_1,\ldots,\Pi_4$、
六个 $Z_d$ 和 $Z_*$ 的所有允许分支值及实际逆源。所有四回复后继
仍按 (MSC.38) 固定，包括来源域中不发生的回复。

每个 $Z_{b_3}$ 来源上，两项资源是同一实际运行的恒等式

$$
q_P(\tau)=1+t_{P_+}(\theta(x_a)),\qquad
\ell_P(\tau)=3+J_{P_+}(\theta(x_a)).
\tag{MSC.59}
$$

其他剖面至多两次调用和六字母，均被 $n+1,W+3$ 支配。安装数为
$M_+$ 个布尔运行态、两个剖面态和 $2+r$ 个原锁存态，得
(MSC.58)。[WTF, 供应 2.1][WTF] 的实际立方来源实现命题 17.1
同时饱和的那个向量，所以同一个原生来源取得 $n+1,W+3$。
立方来源只见证饱和及供应下界，不取代这个全域上界的来源量词。

准备必须在 $\widehat e_{\sigma_{A,k}(\tau)}$ 终止，随后 code-only
handoff 进入同一实际寄存器上的原完整 $e_{\sigma_{A,k}(\tau)}$。
读者的完整表仍是 (MSC.38a)，包括原有固定顺序 $(i_1,i_2)$、全部
四回复后继、原有可恢复入口标签，以及五个承载整行的不同停机态。
在 $\Pi_1,\Pi_2$ 上零入口的两段链分别给出 $R_1,R_2$；在
$\Pi_3,\Pi_4$ 上一入口分别给出 $R_3,R_4$；所有零剖面给出
$R_0$。尤其 $Z_{b_3}$ 即使代码为一也经一入口的 beta 回复输出
$R_0$，代码为零也输出 $R_0$；目标相同不允许省略规定代码的计算。

每个 $R_i$ 是完整前驱行 $R_P(\tau)$，不是只输出当前行或根回复。
其有序外部、每个出现、相等划分、重复、不等类及具体严格前缀阻塞
条件均按定义 7.1 保留；对 $R_i$ 的限制后重新规范命名，未抹去
重复伙伴在别处的原出现。像逆的单射性保留被保留隐值的相等与不等。
独立读者仍有三个运行态和五个完整行停机态，共 $K=8$，其两次新鲜
调用和六字母上限独立收费，不从准备资源中抵扣。

上述组合依旧以同一来源／更新／寄存器绑定、同版本行和代码论证的
合法取得、版本认证、预切口访问权限、实际同源导出、完整访问隔离、
code-only handoff、合法完整入口和静态真实服务连续性为分别供应且
分别定价的服务。准备和阅读期间实际寄存器始终为同一个 $\rho\tau$。
表与字地址表示、安装、初始化、入口及整行输出内容、已取得项上的
局部工作、handoff 和服务存储继续各自计价。这些供应假设不由有限
图的数学存在自动实现。

没有增加 archive/code 重读、选择器、来源副本、计数器、相位坐标、
计算地址、游标、复位、时钟、相等或逆查询端口、额外工作／控制寄存器。
当前计入的状态仍是全部变化配置，常值、根、重复、缺失和认证后每次
调用都付费。有限代码长度、安装控制、导出字母表、微步、物理时间、
存储及能量仍为不同量。这完整保留假设 7.3 的资源边界。$\square$

## 18. 现行结论、归属与未解边界

**约定 18.1（成果及供应归属）。** 新的实质推断是引理 14.2 的
实际相容短证书工具及定理 14.5 的全类 (MSC.32) 分离；定理 16.1
在纠正后的同图物理并集上给出扩大类 $kL$ 下界，推论 16.2 消去旧
原生推论的额外零轴条件。引理 15.2–15.6 给出所需的常值尾安全计数，
不保留旧的强解码器必要性断言。

实际 live 饱和、新鲜性、支持排除和计数方向仍归 SI、PE、PCA、WTF；
扫描单射及角三角形数目归本卷已有论证；四个普通失败网格归 PCA 的
有序阈值供应。第 5、7、11、12 节的完整消费者、严格扩大替换、
全纤维提升、原源／代码／入口／读者及 $+4+r,+1,+3,K=8$ 对应
均为既有成果。第 17 节给出其在现行结论中的完整适用含义，不将复用
内容重复计作新数学。第 8.2 节对 MeMin、Larrauri–Bloem 及现有
closed-cover 来源的归属和跨模型限制保持；这里不需要另一个外部
定理来产生状态下界。

本增补为同一规范所有者中的 repo-derived、未经数学执行的普通纸面
推导，使用 formal-thinking-and-answer 的证据与前提纪律，以及
理论卷模板的追加和公式约定。它没有给出 Lean／kernel 认证、实验
检验、物理实现、文献穷尽或全球新颖性认证；独立全文审查的接受状态
也不能从此处的自含证明推出。不同来源／操作／控制／时序契约的量子、
存储、标定或在线记忆结论均未作为原布尔／原生问题的新数值前提。

**未解问题 18.2（原任务及精确最小值保持开放）。** 当前定理仅覆盖
定义 9.1。原 unrestricted A，即任意原正确完整图在两个原执行上限
下的全图网格下界，仍未解决；没有证明任意原图具有该头和扫描片段，
也没有状态不增且同时保持两个上限的正规化。原 alternative B，即
给出一个满足两个原上限的完整正确严格次网格图，仍未解决。
SI.59／SI.83 的同图集体补偿和 TC 的 shortage-to-actual-full-run
obstruction 在原未覆盖范围仍未解决。

消费者 $M_+>kL$ 只给出指定位置 $s_i=i$ 的上界和非空性；下界
$kL$ 没有证明在扩大类内可达到，也没有确定该类的精确最小值。
独立的无执行预算限制 $H_{\min}$ 仍是另一未解最小化，不能删除本
定理的任一执行上限而转用其结论。原持续研究期限的目标也不由这个
有限类定理完成。原生下界在且仅在其所用投影满足明确成员前提时可
依推论 16.2 使用；对任意原生准备器的该成员前提没有新结论。

## 追加锚（本行以下为增补区）

## 19. Two further state families in the same free-completion graph

**Convention 19.1 (exact class and the credited core).** Fix any integers
$k,L\ge4$, let $n=k+L-1$ and $u=k+L-6$, and retain the distinct
positive original positions and costs $c_i=s_i+4$, $W=\sum_i c_i$.
Throughout Sections 19–22, $P$ is one complete graph in Definition 9.1's
$\mathcal C_{k,L}$, at both same-input caps $t_P\le n$, $J_P\le W$.
Its five distinguished labels and the ordering of $U$ are arbitrary.
All installed running states count, including unused states and states
used only after certification. Every label and both successors are fixed;
only the current counted state changes. Total correctness and termination
are required on the entire Boolean cube. Adaptive orders, repeats,
sharing, aliases and cycles in the union graph remain allowed.

In particular, the two certificate edges of Definition 9.1 have priority
even on the last $U$ query. Every other full-$U$ ordered edge has its own
independent free target, and all four failed-head continuations are free.
Definition 2.3 is not a necessary decoder, and the superseded necessity
assertion in Lemma 9.3 is not used.

The corrected suppliers Lemmas 14.1, 15.1, 15.5, 15.6 and Theorem 14.5,
as assembled in Theorem 16.1, allow the following selection in this same
physical graph. Choose five heads, all scan roles, exactly seven selected
tails if $k\ge5$ or six if $k=4$, and the zero-axis states
$Z_e$, $2\le e\le L-1$. These sets are pairwise disjoint, and their
union $\mathscr K$ has cardinality

$$
|\mathscr K|=
\begin{cases}
((k-1)L-10)+5+7+(L-2)=kL,&k\ge5,\\
(3L-9)+5+6+(L-2)=kL,&k=4.
\end{cases}
\tag{MSC.60}
$$

Every selected tail other than $E$ has an actual live arrival of counts
in $\{(k-2,L-1),(k-1,L-2),(k-1,L-1)\}$. The selected state $E$
queries $j$ and has terminal successors $(0,1)$. The all-zero arrival
at $Z_e$ has support $S_e\supseteq\{j,x_1\}$, all assigned zero.
These facts select only the required physical substructure; they do not
fix constant tails or identify different free full-$U$ targets.

**Lemma 19.2 (short one chains after a live history).** Let an actual
live history in $P$ have $h$ ones and $z$ zeros. Its current state cannot
have a fixed chain of $r$ consecutive one-successor edges ending at
terminal $1$, where $1\le r<k-h$.

Proof. Attempt that chain from the given actual partial assignment.
After $a<r$ steps its counts would be $(h+a,z)$, with $h+a<k$ and
$z<L$. Inductively this is a consistent actual live prefix: every full
extension of the assigned coordinates follows it. Convention 13.3 forces
the next queried coordinate to be fresh. An old label would already
contradict that supplier; otherwise assign its previously unread bit one
and follow the fixed one edge. Thus the whole chain is realized by a
consistent partial assignment. Complete every remaining unread bit by
zero. This actual complete input follows the original history and chain,
accepts, and has exactly $h+r<k$ ones, contradicting correctness.
This is Lemma 14.2's actual-prefix mechanism with general $h$; syntactic
chain realizability is proved during the argument. $\square$

**Lemma 19.3 (the one-hit failure run).** Let $\theta^{j}$ be the
single actual input with $\theta_j=1$ and every other coordinate zero.
For every $1\le d\le L-1$, its run has a running state $V_d$ after
one one and $d$ zeros have been exposed. These states have live counts
$(1,d)$, supports $T_d\supseteq\{j,y_1\}$, and are pairwise distinct.
In particular $V_1=F_{10}$.

Proof. The head first queries $j=1,y_1=0$. After root reply one,
as long as fewer than $L$ zeros have been exposed, the prefix is live:
one hit is below $k$ and both output values have full completions.
Correctness forbids a terminal there. Freshness forces the next label
to be unread, so its actual reply on $\theta^j$ is zero. Induction
therefore gives all the stated prefixes and their supports. A repeated
physical state on this one fixed-input run would repeat the identical
stationary suffix forever, contradicting actual termination. No acyclicity
condition on the union graph is used. $\square$

**Lemma 19.4 (the one-hit family misses the entire core).** For every
$1\le d\le L-1$, $V_d\notin\mathscr K$.

Proof. The five heads have actual live counts, in the order
$R,A,A_2,B,B_2$,

$$
(0,0),\quad(0,1),\quad(1,1),\quad(1,0),\quad(2,0).
$$

The unit hit gap in (MSC.44) separates $V_d$ from $R,A,B_2$.
The remaining heads $A_2,B$ have supports $\{j,x_1\},\{j\}$.
Both differ from $T_d$, which contains $y_1$. Equal-hit,
different-support exclusion therefore separates them too. Every zero-axis
arrival has zero hits, again a unit hit gap from $V_d$.

A selected non-$E$ tail has a live arrival $(g,w)$ with
$g\ge k-2\ge2$ and $w\ge L-2$. Sharing with $(1,d)$ would
require $d-w\ge2$ by (MSC.44), whereas $d-w\le1$. The state $E$
queries the already exposed $j$, so live freshness excludes $V_d=E$.
This covers every selected tail for either permitted first-variable order
and for paid constant tails.

It remains to compare $V_d$ with each displayed scan $Q(s,z)$.
The following three ranges, intersected with $0\le z<L$, exhaust them.

For $z\le L-5$ and $s\ge1$, put $r=k-1-s$. Then
$1\le r\le k-2$ and

$$
u-(s+z)-r=L-5-z\ge0.
\tag{MSC.61}
$$

The next $r$ one edges in the retained scan end at terminal $1$.
At equality in (MSC.61) the final edge is exactly the priority
$s'=k-1$ certificate on the last $U$ query. No free full-$U$ target
is used. If $V_d=Q(s,z)$ this chain violates Lemma 19.2 with $h=1$.
For $s=0$ in this range, instead use the scan's low-column arrival
$(1,2+z)$. It is live, with support
$\{j,x_1,x_2\}\cup U_{\le z}$, which omits $y_1$. Equal hits and
different supports exclude sharing with $V_d$.

For $L-4\le z\le L-3$, the low-column arrival $(1+s,2+z)$ is
live: $1+s\le k-1$, $2+z\le L-1$. When $s=0$, its support again
omits $y_1$, so the preceding equal-hit argument applies. When $s\ge1$,
sharing with $V_d$ requires $d-(2+z)\ge2$, but

$$
d-(2+z)\le L-3-z\le1.
$$

For $L-2\le z\le L-1$, the strict scan inequality $s+z<u$ implies
$s\le k-5$. Use the high-column arrival $(3+s,z)$, which is live
since $3+s\le k-2<k$. Sharing would require $d-z\ge2$, but
$d-z\le1$. No live exclusion has been applied to a certified low-column
arrival in this range.

When $L=4$ the first range is empty and the second is $z=0,1$.
When $k=4$ the third has no roles because it requires $s\le-1$.
Thus $k=L=4$ is included, as are all clipped and equality boundaries.
All comparisons concern actual arrivals in the same $P$. $\square$

**Lemma 19.5 (a further two-hit state).** The failed-low-head target
$F_{11}$ is a running state $T$ outside both $\mathscr K$ and
$\{V_1,\ldots,V_{L-1}\}$.

Proof. The actual head word $j=0,x_1=1,x_2=1$ reaches $T$ with
support $A=\{j,x_1,x_2\}$ and counts $(2,1)$. It is live for all
$k,L\ge4$, so $T$ is running and every completion of this assignment
follows the prefix. The unit hit gap separates $T$ from every $V_d$
and from the hit-one heads $A_2,B$. Compared to the hit-zero heads
$R,A$, (MSC.44) would require their zero counts, zero or one, minus
the zero count one of $T$ to be at least two. This is impossible.
$B_2$ has equal hits but support $\{j,y_1\}$ of size two rather
than three. The equal-hit support exclusion separates it from $T$.
The selected $E$ queries old $j$, contradicting live freshness at $T$.

Each scan has a live arrival $(g,w)$ with $g\ge1,w\ge2$.
For $z\le L-3$ choose the low column $(1+s,2+z)$; for
$z\ge L-2$ choose the high column $(3+s,z)$, using $s\le k-5$
as in Lemma 19.4. When $g=1$ the hit gap is one. When $g=2$ its
support has size $g+w\ge4$, different from $A$; equal-hit support
exclusion applies. When $g>2$, sharing would require $1-w\ge2$,
again impossible. The same three-case comparison separates $T$ from
every selected non-$E$ tail, whose live counts have $g\ge2,w\ge2$.

It remains to exclude all $Z_e$, $2\le e\le L-1$. Recall that
$S_e$ contains $j,x_1$ and all its old replies are zero.
If $x_2\in S_e$, then $A\subseteq S_e$: equal supports with unequal
hits, or proper nesting, excludes sharing. If $x_2\notin S_e$ and
$e=2$, then $S_e=\{j,x_1\}\subsetneq A$, also excluded.
In the remaining case $e\ge3$, $x_2\notin S_e$, the supports are
incomparable and

$$
S_e\cap A=\{j,x_1\},\qquad A\setminus S_e=\{x_2\}.
\tag{MSC.62}
$$

Orient the shared-state comparison with the zero-hit history first.
Every old bit in $S_e\setminus A$ is zero and the sole old bit in
$A\setminus S_e$ is one. The two-polarity private exchange (MSC.3),
namely [PE, Theorem 3.1, part 3][PE] after the whole-graph lift, forces

$$
|S_e\setminus A|=|A\setminus S_e|=1,\qquad
C_{S_e\setminus A}=c_{x_2}.
\tag{MSC.63}
$$

Writing $S_e\setminus A=\{v\}$ gives $v\ne x_2$ and
$c_v=c_{x_2}$, contrary to distinct original positions. The old replies
on the intersection need not agree: $x_1$ is zero on the zero axis and
one at $T$. PE's theorem explicitly allows this; its replay does not
query that intersection. We have equated two distinct singleton costs,
not ruled out equal sums of larger subsets. This proves the remaining
separation, including $e=L-1$ and $k=L=4$. $\square$

## 20. A strict class lower bound and the normalization obstruction

**Theorem 20.1 (the free-completion class costs at least one extra column).**
For every $k,L\ge4$, every original position vector, every choice of
the five distinguished labels and ordering of $U$, and every complete
$P\in\mathcal C_{k,L}$ at the two original caps,

$$
\boxed{m(P)\ge(k+1)L,\qquad m(P)+2\ge(k+1)L+2.}
\tag{MSC.64}
$$

The second count includes the two distinct Boolean terminals. No
read-once, fixed variable order, leveling, acyclicity, distinct-subset-sums
or realizability-of-every-syntactic-path hypothesis is added.

Proof. Convention 19.1 selects $kL$ distinct physical states in
$\mathscr K$. Lemma 19.3 gives $L-1$ distinct states on one
terminating actual run, and Lemma 19.4 separates all of them from that
core. Lemma 19.5 supplies one further state $T$ outside their entire
union. Thus this one installed graph contains the disjoint union

$$
\mathscr K\ \dot\cup\ \{V_1,\ldots,V_{L-1}\}
\ \dot\cup\ \{T\},
\qquad kL+(L-1)+1=(k+1)L.
\tag{MSC.65}
$$

Every comparison uses this same complete feasible table. Different
actual inputs witness disjointness of its installed states; their
execution prices have never been summed across inputs. Both caps remain
premises of the actual-history suppliers. The endpoint $k=L=4$ gives
the same count $16+3+1=20$, with three scan states, five heads, six
selected tails and two zero-axis states in the core. $\square$

**Corollary 20.2 (no state-nonincreasing normalization into this class).**
Fix $k,L\ge4$ and any original position vector. No transformation on
all total original threshold-$k$ graphs at caps $n,W$ can simultaneously
preserve these two caps, produce a member of Definition 9.1, and never
increase installed running states. This remains false even if the
transformation chooses the distinguished labels and $U$ ordering afresh.
In particular, this class contains no unrestricted installed-state
minimizer at those caps.

Proof. The ordinary ordered grid supplied by [PCA, Theorem 26.1][PCA],
equivalently the Boolean grid in the proof of Theorem 5.1, has $kL$
running states at every original position vector. On each complete
input it queries each coordinate at most once, hence simultaneously
satisfies $t\le n,J\le W$. It is a lawful original competitor, not
an assertion that all competitors can be ordered. Applying the proposed
transformation to this graph would give a class member with at most
$kL$ states, contrary to Theorem 20.1's uniform bound $kL+L$.

The unrestricted minimum exists as the least element of a nonempty set
of finite integer cardinalities, and is at most $kL$ by this grid.
Every class member has at least $kL+L$, so none is such a minimizer.
If the class is empty at a particular cost vector, a transformation into
it is of course also impossible. No existence for every cost vector is
needed. This excludes this precise same-budget normal form; it proves
neither the unrestricted grid lower bound nor a strict-subgrid graph.
$\square$

**Remark 20.3 (the existing nonempty consumer).** No new completion
table is needed for nonvacuity. At the original positions $s_i=i$,
Definition 11.1's $P_+$ and Proposition 17.1 supply a complete class
member, correct and terminating on the whole cube, with both caps on
each input and one input attaining both. Its installed count satisfies

$$
M_+=(5k-6)L-5k+8,
\qquad M_+-(k+1)L=(4k-7)L-5k+8\ge11k-20>0.
\tag{MSC.66}
$$

The inequality follows from $L\ge4$ and $4k-7>0$; it includes $k=4$.
Thus the new lower bound is compatible with the entire existing
consumer. Neither its upper count nor (MSC.64) determines the exact
minimum inside the class. Its four complete failed-head grids, paid
old-coordinate visits and constant tails are the existing construction,
not additional contributions of Sections 19–22.

## 21. The original full-fiber task and its qualified Native consequence

**Convention 21.1 (unchanged actual source and supplied interfaces).**
Use precisely Definitions 7.1–7.2 and Assumption 7.3, with their supplier
[WTF, Sections 1–4][WTF]. The following specifies their correspondence
to Theorem 20.1; none of the supplied services is constructed by that
theorem.

The actual source is a finite nonempty ordered $\alpha/\beta$ tree
$\tau$, with no size, depth or shape restriction. Its update is the
homomorphism $\rho\alpha=\beta$,
$\rho\beta=\langle\beta,\alpha\rangle$. The fixed actual register
through preparation and reading is $\rho\tau$. Every finite absolute
address is legal, including the empty word and words below a leaf;
the four replies are alpha, beta, branch, absent. Equal subtree values
at different addresses retain different occurrences.

The domain is the entire $\mathcal U_*=\{\tau:R_P(\rho\tau)=R_*\}$,
$P=\{L,R\}^3$. Its complete current row has the ordered depth-three
exterior and six classes
$a=\{LLL,LRL\}$, $b_1=\{LLR\}$, $b_2=\{LRR\}$,
$c=\{RLL,RRL\}$, $b_3=\{RLR\}$, $b_4=\{RRR\}$, with all
different-class whole-subtree disequalities. The image grammar is the
beta tree, the special pair $\langle\beta,\alpha\rangle$, and ordered
pairs of image children. Its inverse $\delta$ constructs actual
witnesses and is not an apparatus port.

All eleven profiles of Definition 7.1 remain in the domain. On $\Pi_i$,
$b_i$ is alpha, its repeated left partner is beta and all other class
roots are branches. On each of the six $Z_d$ only $d$ is beta, and
on $Z_*$ all class roots are branches. Every allowed branch image and
every disequality is retained. The complete predecessor output is
$F(\tau)=R_P(\tau)$, namely $R_0=R_*$ on zero profiles and $R_i$
on $\Pi_i$. For $(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, $R_i$
replaces the sibling holes $q_iL,q_iR$ by concrete beta at $q_i$,
keeps the partner's other occurrence, and canonically restricts the
remaining partition. The entire ordered exterior, retained occurrences,
repetitions, surviving disequalities and concrete strict-prefix blocking
guards are output contents.

For the original positive positions, $w_i=L^{s_i}R$ and
$a_i=LLLw_i$, of length $c_i=s_i+4$. The actual test bit of a branch
image $B$ is one exactly when its reply at $w_i$ is branch; alpha,
beta and absent give zero. Preparation must retain the literal
$\widehat e_{\sigma_{A,k}(\tau)}$, where $\sigma$ is zero on
$\Pi_1,\Pi_2$, one on $\Pi_3,\Pi_4$, threshold $k$ of these
selected bits on $Z_{b_3}$, and zero on every other zero profile.
An alternative usable encoding or direct output of $F$ is not this task.

[WTF, Supplier 2.1][WTF] supplies one actual $\tau_\theta\in Z_{b_3}$
for every full Boolean vector. In its repeated $a$ value, replace beta
at each prefix-free comb position $w_i$ by $\langle\beta,\beta\rangle$
exactly for one bits. Fixed other class images avoid all these combs
and each other; applying $\delta$ to the actual filling gives the
origin. This retains both $a$ occurrences and all disequalities and
defines every finite-address reply. The cube is a lower-witness family;
it restricts neither the original domain nor any full-fiber upper proof.

The unchanged reader is the complete table (MSC.38a), with the original
fixed order $(i_1,i_2)$ of $\{1,2\}$. In alpha, beta, branch, absent
order, $e_0$ queries $q_{i_1}R$ with successors
$(H_{i_1},H_0,Q_2,H_0)$; $Q_2$ queries $q_{i_2}R$ with successors
$(H_{i_2},H_0,H_0,H_0)$; $e_1$ queries $RLR$ with successors
$(H_3,H_0,H_4,H_0)$. Every $H_i$ stores the whole $R_i$ just specified.
The three running states and five distinct whole-row halts have separate
count $K=8$ and fresh caps two calls, six letters. Paid code-only handoff
enters that same complete $e_\sigma$ on that same register. Both entries
can output $R_0$ on $Z_{b_3}$; this does not waive the independently
prescribed code and latch.

The preparer has a single source-independent running start, a fixed
absolute word and four fixed successors per running state, the two
original latches and $r\ge0$ additional mandated distinct latches.
Its current counted state is its whole changing configuration. All
installed states count. Every visit pays one call and the literal word
length, including constant, root, absent, repeated and certified visits.
Correctness and actual termination quantify over every $\tau\in\mathcal U_*$.
No variable order, syntactic acyclicity or immediate certified stopping
condition is added.

Origin/update/register binding, lawful acquisition of the authenticated
same-version row and code arguments, version authentication, pre-cut
permission, actual same-source export, complete access isolation, paid
code-only handoff, lawful complete entry, and stationary truthful service
continuity are separately supplied and priced premises of Assumption 7.3
and [WTF, Assumption 1.5][WTF]. Address/table representation, installation,
initialization, reference and record storage, whole-row output contents,
local acquired-term work, handoff and service storage have separate
prices. The call and letter caps do not price physical memory,
elapsed time or energy. No unknown seed, complete response oracle,
source-dependent initialization, selector, decoder service, old-reply
cache, callable history archive, source copy, clock, reset, phase, cursor,
computed address, equality/inverse port or extra work register is supplied.

**Corollary 21.2 (projection-qualified extra-column bound).** Under
Convention 21.1, let an original preparer be correct and actually
terminating on the entire $\mathcal U_*$, with $H$ installed preparation
states including all mandated latches. Suppose both caps
$q_P(\tau)\le n+1$, $\ell_P(\tau)\le W+3$ hold on each same
complete source. If its particular complete Boolean projection supplied
by [WTF, Theorem 4.1][WTF] belongs to Definition 9.1, then

$$
\boxed{H\ge(k+1)L+4+r.}
\tag{MSC.67}
$$

In particular, relative to the existing full-fiber Native grid with
$H_{\mathrm{grid}}=kL+4+r$ at these caps, any resulting preparer with
such a projection requires at least $L$ additional installed preparation
states. This does not assert that a transformation to such a preparer
exists.

Proof. WTF projects this one original preparer to one total stationary
Boolean graph $B$, with all realized selected visits retained and

$$
m(B)\le H-4-r,\qquad
t_B(\theta)+1\le q_P(\tau_\theta),\qquad
J_B(\theta)+3\le\ell_P(\tau_\theta).
\tag{MSC.68}
$$

Both Boolean bounds hold on each same actual complete input. The
projection membership premise permits Theorem 20.1, so
$H-4-r\ge m(B)\ge(k+1)L$. This gives (MSC.67). The grid and its
full-fiber count are supplied by PCA Theorem 26.1, giving the comparison.
For an arbitrary preparer the projection count is an inequality, not an
identity with its old native trace or an assumed exact overhead.

For the scope of the correspondence, WTF's canonical lift installs every
Boolean state at $a_i$, with four successors
$(\delta_B(v,0),\delta_B(v,0),\delta_B(v,1),\delta_B(v,0))$,
replacing terminals by the original latches. Its two added profile states
are distinct from all lifted Boolean states; their names $D,T$ are those
of (MSC.38), not the Boolean failure target $T=F_{11}$. Here $D$
queries $RLR$ with successors
$(\widehat e_1,\text{Boolean start},T,\widehat e_0)$, and $T$ queries
$RRR$ with successors
$(\widehat e_1,\widehat e_0,\widehat e_0,\widehat e_0)$. All four
edges are installed. It has $m(B)+4+r$ preparation states, and on every
actual $Z_{b_3}$ source its same run pays $1+t_B(\theta(x_a))$ calls
and $3+J_B(\theta(x_a))$ letters. The remaining profiles pay at most
two calls and six letters. The all-address occurrence identity makes
this valid for arbitrary full-fiber branch images, including leaf and
absent selected replies; it does not acquire a free vector. Thus the
lift of the existing $P_+$ remains the complete consumer of Proposition
17.3, with all services and reader of Convention 21.1 unchanged. This
is reused transport, not a new construction or a pointwise preservation
claim about arbitrary old native paths.

The $4+r$ counts two profile states and $2+r$ latches. Boolean terminals
are replaced, not charged a second time; the separate $K=8$ reader is
not added to or discounted from $H$. $\square$

## 22. Common-process readings, attribution and remaining recovery gaps

**Convention 22.1 (independent readings and the recovered direction).**
All four readings refer to the one actual source, fixed register,
installed tables and legal two-phase execution of Convention 21.1.
Space exposes ordered occurrences, their literal addresses and lengths;
equal values do not merge occurrence positions. Time exposes the actual
ordered calls, replies and fixed successors, together with the declared
$\tau\mapsto\rho\tau$ relation; there is no available clock. Boundary
exposes the complete current row with its guards and the current lawful
continuation or handoff interface. Memory exposes the current counted
state and, after preparation, the retained original latch. Whole-row
halt contents and any supplied reference or record have their separate
storage and access prices. No reading is defined as a desired inverse,
and no unrestricted copy of history is made available to a view.

The established operational recovery direction remains the supplied one:
paid observations of the current source compute the prescribed latch;
paid handoff enters the unchanged callable reader on that source; its
fresh paid observations return the complete predecessor row $F(\tau)$.
Proposition 17.3 proves its full-fiber realization for $P_+$, and WTF
Theorem 4.1 supplies the corresponding lift for any Boolean competitor.
Theorem 20.1 adds an installed-control obstruction for one exact
projection class, not a new inverse or acquisition procedure. Specifying
initialization and the actual reply sequence determines a stationary
execution, but does not supply that sequence as a retained runtime record.

The constant current row $R_*$ cannot itself determine the prescribed
code: the actual cube has both code values. Even its complete predecessor
target is $R_0$ on every cube source while the code varies. These results
establish no recovery from those rows or latches of an arbitrary hidden
tree, all address replies, the complete chronology or an arbitrary
controller cut. Mutual four-view
recovery, agreement of arbitrary recovery routes, dynamics compatibility
at arbitrary cuts and a universal alpha/beta reduction remain unproved.

**Convention 22.2 (mathematical dependence and literature scope).** The
new *repo-derived synthesis* is the disjointness of the mandatory
one-hit failure run and $F_{11}$ from the corrected core, yielding the
extra $L$ states and the same-price normalization obstruction. The
core's $kL$ count is Theorem 16.1; its constant-tail-safe tails, zero axis
and scan injectivity are Sections 13–15. Live freshness, support
exclusions, the oriented two-gap condition and private exchange retain
their SI/PE/PCA/WTF ownership. Lemma 19.2 adapts Lemma 14.2's mechanism
to the live one-hit consumer. The grid, $P_+$, actual source cube,
whole-fiber correspondence, exact original code, latches, reader and
overheads retain their existing suppliers. None is counted as a newly
proved optimum or a newly implemented service.

Stationary continuation and distinguishing actual completions are mature
methods. [Wegener's *The Complexity of Boolean Functions*][MSCWEG], Chapter 14,
Section 4, Theorems 4.1–4.3, treats the BP1 normalization and residual
count. Its printed page 424 explicitly restricts path realizability to
BP1 rather than general branching programs. [Bryant's *Graph-Based
Algorithms for Boolean Function Manipulation*][MSCBRY], Section 2, Definition 1,
requires strictly increasing variable indices, hence an acyclic graph.
These are credited structural precedents; neither normalization is a
transfer of the present paid-repeat, two-budget class. [MeMin, Section
II.A–C and Theorem 1][MEMIN] supplies successor-closed compatible covers,
which may overlap, as already credited in Convention 8.2. Its input-word
model does not replace static-assignment consistency or either price here.
No external minimization algorithm or executed enumeration is used.

The formalized [NativeLiteralMoore][MSCLIT] and
[NativeSharedMooreSynthesis][MSCSHARED] results, with their respective
[literal][MSCLITSCRIBE] and [shared-table][MSCSHAREDSCRIBE] Scribes, allow
acquired input-dependent initial exports and encoder/table reselection.
Their same-run contraction and
resource transfer do not supply fixed-start prescribed-code optimality.
[NativePredecessorRowRecovery.native_predecessor_row_recovery][MSCPRED],
with its [owning Scribe][MSCPREDSCRIBE], consumes the old reached set;
it does not acquire that set at the present price.
The pinned mathlib state-transition and DFA/Myhill–Nerode interfaces
supply evaluation, simulation and word-language continuation, without
the missing static-input charged-state lower bound. These are interface
distinctions, not absence-of-name arguments for mathematical impossibility.

The positive four-view results in Native Clocked Recovery and Order,
Native Paid View Conversion, PR57, Process Geometry and the structural
and callable storage atlases retain their respective clocks, acquired
seeds, tapes, entrances, rights, serializers and price coordinates.
The present lower bound neither imports those facilities at the original
state-only price nor improves their converters. Its precise gain is to
exclude a proposed parsimonious same-cap normal form for this prescribed
Native task. Bounded source and primary-literature correspondence gives
no worldwide originality or exhaustive supplier-absence claim. These are
ordinary paper proofs, without new Lean/kernel certification, mathematical
execution, experimental evidence or independent review approval.

**Open problem 22.3 (preserved original obligations).** The unrestricted
alternative A of Problem 18.2 and [WTF, Corollary 5.1 and Proposition
11.8][WTF] still asks for a whole-graph $kL$ lower bound at both caps;
alternative B still asks for one lawful complete strict-subgrid graph.
Theorem 20.1 settles neither. Corollary 20.2 excludes a specific
normalization route into Definition 9.1, not all possible normal forms
or all routes to A. SI.59/SI.83's collective compensation and TC's
shortage-to-actual-full-run obligation retain their unresolved scopes.
The class's exact minimum, its feasibility at arbitrary position vectors,
and the separate optimum without execution budgets are not determined.
No conclusion is asserted after dropping either cap.

All fixed-$G_{gc}$, original-$Q$, parked-consumer and unchanged-initialization
settlements keep their original hypotheses; the supplied acquisition,
authentication, permissions, actual export and continued callable-use
services are not derived here. No physical or universal impossibility
follows. The extra-column obstruction and its qualified transport are
bounded advances and do not complete the sustained four-expression
objective.

[MSCWEG]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[MSCBRY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[MSCLIT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[MSCLITSCRIBE]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[MSCSHARED]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.lean
[MSCSHAREDSCRIBE]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.scribe.cs
[MSCPRED]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.lean
[MSCPREDSCRIBE]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.scribe.cs

## 追加锚（本行以下为增补区）
