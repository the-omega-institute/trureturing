# Paid private exchange in native prescribed-code preparation

## 1. The original source and the two execution caps

**Definition 1.1 (actual source, current row and complete target).** Use the
finite nonempty ordered algebra

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

At every finite address in $\{L,R\}^*$, including the empty word, the
actual reply is alpha, beta, branch or absent. Descent beyond a leaf is
absent. Keep the cut $P=\{L,R\}^3$ and the complete current row $R_*$
whose six equality classes are

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
$$

Every two different classes assert disequality. The domain and target are

$$
\mathcal U_*:=\{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad F(u):=R_P(u).
$$

Here a complete row retains the ordered exterior, occurrence holes, their
entire equality partition and every exterior strict-prefix blocking guard;
class names are recomputed from first occurrences after restriction.
There is no size, depth or interior-shape promise on $u$ or $\rho u$.

Use [NBP, Definitions 1.1–1.2 and 9.1, Proposition 9.3][NBP] for this
source and its five complete target rows $R_0,\ldots,R_4$. Their actual
inverse supplier is [Transport–Memory Completion, Proposition 22.2,
(RA.2207)][TMC]: the disjoint image cases are beta, $E$, and a pair of
images. The inverse sends these respectively to alpha, beta and the pair
of inverse children. The cases are disjoint because alpha is not an
image. In particular the inverse is injective, preserving both equality
and disequality of retained hidden values.

For a filling by six pairwise different values $x_d$, the actual current
tree has the two displayed occurrences of each repeated class. Such a
filling is an image precisely when all six values are images, or exactly
one $x_{b_j}$ is alpha, its repeated left partner is beta, and every other
class value is an image. These are the exhaustive alternatives of NBP
Proposition 9.3, not merely formal root assignments.

Use the full profiles of [NBP, Proposition 15.2][NBP]. On $\Pi_j$ the
right class $b_j$ is alpha, its partner is beta and all other roots are
branches. On $Z_d$ only class $d$ is beta and all other roots are
branches; on $Z_*$ all roots are branches. These eleven profiles exhaust
$\mathcal U_*$. Their targets are $R_j$ on $\Pi_j$ and $R_0=R_*$ on
the zero profiles. For $j>0$, $R_j$ replaces the sibling holes at
$q_jL,q_jR$ by a concrete beta at $q_j$, where
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, and canonically restricts the old
partition. The other occurrence of the repeated partner remains an old
hole. All retained disequalities and all blocking guards remain in the
answer.

**Definition 1.2 (literal prescribed entries).** Fix distinct positive
positions $A=\{s_1<\cdots<s_n\}$, and put

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,
\qquad C_B=\sum_{i\in B}c_i,\qquad W=C_{[n]}.
$$

For every branch image $B$, without any shape promise, define

$$
\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}},\qquad
f_{A,k}(B)=\mathbf1_{\{\sum_i\theta_i(B)\ge k\}}.
$$

Alpha, beta and absent each contribute zero. Preserve exactly the code
of [PCA, Definitions 4.2 and 23.1][PCA]:

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
f_{A,k}(x_a),&u\in Z_{b_3},\\
0,&u\text{ belongs to any other zero profile}.
\end{cases}
$$

The reader is the fixed $K=8$ reader of PCA Supplier application 4.3,
using [NBP, Theorem 15.5][NBP] with $z=0$, positive codes $(0,0,1,1)$,
$S_{15}=\{1,2\}$ and distinguished test $3$. Its three running states,
five whole-row halts, all four successors and two recoverable complete
entries $e_0,e_1$ are fixed. The reader makes at most two fresh calls and
six fresh letters. Preparation must produce literally
$\widehat e_{\sigma_{A,k}(u)}$; handoff enters that original complete
state. No different encoder, recoloring, entry map or decoder is allowed.

**Assumption 1.3 (charged native preparers).** A preparer is any finite
stationary table of [PCA, Definition 2.2 and Convention 23.2][PCA], with
a source-independent running start, one fixed absolute word and four
fixed successors per running state, sourcewise termination on all of
$\mathcal U_*$, and the two original-entry latches. If $r\ge0$ further
distinct latches are mandated, they too are installed and counted. Write
$H$ for the number of all installed preparation states, including unused
running states and latches. A running visit is exactly one paid native
invocation, and its letter charge is its absolute word length. Assume on
every original source

$$
q_P(u)\le n+1,\qquad \ell_P(u)\le3+W.                 \tag{PE.1}
$$

There is no order, read-once or union-acyclic assumption. Repeated
words, shared successors, union cycles and unused states are allowed.
Root, constant, absent and post-certification invocations are paid.
The current counted state is the entire changing preparation
configuration; there is no second counter, phase coordinate, computed
address, transcript register, stored source or later code/archive access.
The reader states are charged separately, including every whole-output
state.

**Assumption 1.4 (supplied services and resource meaning).** Keep the same
actual origin and authenticated update, lawfully acquired same-version
current row, pre-cut access, actual export, complete access isolation,
code-only handoff, lawful complete reader entry and stationary truthful
native service of PCA Assumptions 1.2 and 33.2. They remain supplied and
separately priced. Installed address and successor representation,
initialization, entry contents, whole-output contents, handoff and service
storage, local acquired-term computation, physical memory, elapsed time
and energy retain their separate costs. The coordinates $H,q_P,\ell_P$
are not a total physical price. An inverse or a profile in a proof is not
an operation supplied to the running apparatus.

## 2. Actual cube histories and the saturation suppliers

**Definition 2.1 (actual witnesses and live histories).** Use precisely
the simultaneous actual cube $u_\theta\in Z_{b_3}$ of [PCA, Lemma
24.1][PCA], $\theta\in\{0,1\}^n$. It has the complete target $R_0$
and prescribed bit $\mathbf1_{\{|\theta|\ge k\}}$. Its whole repeated
value $x_a=B_\theta$ is a beta/pair comb with the selected beta at $w_i$
replaced by $\langle\beta,\beta\rangle$ exactly for $\theta_i=1$.
The other branch values are fixed, pairwise different and avoid every
$B_\theta$; $x_{b_3}=\beta$. The image inverse of Definition 1.1 gives
actual finite origins with every original disequality.

Every actual finite word on this cube is constant or reads exactly one
bit, the latter occurring precisely in the disjoint sets

$$
E_i=\{p w_i z:p\in\{LLL,LRL\},\
                     z\in\{\varepsilon,L,R\}\}.       \tag{PE.2}
$$

At an occurrence root the bit replies are beta/branch, and at a selected
child they are absent/beta, in bit order zero/one. Every word in $E_i$
has length at least $c_i$, with equality only at the two occurrence
roots. This is an all-address classification: proper prefixes are
unchanged branches, below the selected children both continuations are
absent, and the other occurrence cones are fixed. In particular no other
address combines bits. The occurrence identity [NBP, (NBP.9.7)][NBP]

$$
r_{\rho u}(p v)=r_{x_d}(v)\quad(p\in P,\ d=[p])       \tag{PE.3}
$$

holds for every finite suffix, including traversal past leaves. Repeated
values do not identify their occurrences.

A history includes every invocation already made and ends before its
next invocation. Let $S$ be its exposed coordinate set and $h$ its
number of exposed ones. It is live precisely when

$$
1\le k-h\le n-|S|.                                  \tag{PE.4}
$$

Every bit completion of such a history is an actual cube source
following that history. Sets, counts and completions are proof notation,
not accessible running coordinates. A selected state below means an
installed running state with word in some $E_i$.

Under (PE.1), [PCA, Theorem 34.3][PCA] gives the following supplied
saturation facts. Every live prefix has negative and positive saturated
completions of weights $k-1,k$. Each has exactly $n$ selected calls, once
per coordinate at a shortest occurrence root, and exactly one further
call, at $RLR$, before the last selected call. Both budgets in (PE.1)
are equalities, so that last selected call is followed directly by its
entry latch. At any live prefix a selected invocation is fresh and at
one of these roots; the only possible nonselected invocation is $RLR$,
and there is at most one in a live portion. This concerns individual
source paths; their union is not assumed acyclic.

For two live histories at one running state, with supports $S,T$, hit
counts $h,g$, and

$$
X=S\setminus T,\quad Y=T\setminus S,\quad
I=S\cap T,\quad U=[n]\setminus(S\cup T),
\qquad a=|X|,\quad b=|Y|,\quad u=|U|,
$$

[PCA, Theorem 35.1][PCA] supplies

$$
[0,u]\cap[k-h-b,k-h-1]\cap[k-g-a,k-g-1]
                    \cap\mathbb Z=\varnothing.       \tag{PE.5}
$$

It also excludes equal supports with unequal hit counts. Its argument
uses freshness while both histories remain live; it does not assign a
unique residual to every installed state. PCA Proposition 36.1 already
gives a balanced seven-coordinate, four-hit live merger, with
$H=47+r$ against the grid $20+r$. PCA Lemmas 38.3–38.4 give the nested
exclusion and reciprocal single-private-coordinate charge only in their
five-coordinate scope. The next two sections extend the consumed
exclusions and charges without assuming extreme residuals.

## 3. One-sided private exchange without extreme residuals

**Theorem 3.1 (one-sided necessary private charges).** Let $n\ge6$ and
$3\le k\le n-2$. Under Definitions 1.1–2.1 and Assumptions 1.3–1.4,
suppose two actual live cube histories reach one common installed
selected state. Suppose their supports $S,T$ are incomparable and their
hit counts satisfy $h<g$. Use $X,Y,I,U,a,b,u$ as in Definition 2.1.
Then the following implications hold, with no AND/OR residual premise:

1. If every old bit in $X$ on the $S$ history is zero, then
   $a\le b$ and $C_X\le C_Y$.
2. If every old bit in $Y$ on the $T$ history is one, then
   $b\le a$ and $C_Y\le C_X$.
3. If both conditions hold, then $a=b$ and $C_X=C_Y$.

Proof. First, every complete cube run, of any weight, requires an
invocation outside $\bigcup_iE_i$ of length at least three. The
all-weight comparison of PCA Lemma 38.2 extends without using the
number five: for a negative vector, keep $x_a=B_\theta$ and the other
three right branch values, and replace $x_c$ by beta and $x_{b_3}$ by
alpha. NBP Proposition 9.3 gives an actual $\Pi_3$ source with the
opposite prescribed bit. For a positive vector, replace only the beta
at $b_3$ by a fresh branch image, avoiding the other class values. This
is an actual $Z_*$ source of prescribed bit zero. In either comparison
all selected replies agree, every different-class disequality is
retained, and the exterior before depth three is identical. A run with
no distinguishing invocation would give the opposite-code source its
same entry latch. Thus the required extra invocation is on that very
cube run and has length at least three. No costs from different sources
are added.

We also need profile timing for any completion kept live until its last
fresh coordinate, rather than only the two particular completions chosen
in the saturation supplier. Such a run has $n$ distinct selected root
calls, paying $W$, and the preceding comparison forces one further call
of length at least three. The two caps force exactly these calls and
charges. If the further call were after the last selected call, the
preceding path would be selected-only. Keep its entire $x_a=B_\theta$
fixed and choose the three actual origins of PCA (PCA.85): one in $Z_c$
and one in each of $\Pi_3,\Pi_4$, with $x_c=\beta$ and fresh distinct
branch values at the other right classes except for the indicated alpha.
They follow that same selected-only path. Their prescribed bits are
$0,1,1$. Only one call and at most three letters remain. A word shorter
than three gives a common exterior branch; a length-three class root
other than $b_3,b_4$ is common to all three; either of those two roots
separates only its own positive origin. No such final call distinguishes
the zero origin from both positive origins. Thus the further call must
precede the last selected call. Its history is then live, so it is
$RLR$ by the live-prefix supplier, and the last selected call goes
directly to its latch. This proves the timing assertion for the two
adaptively constrained completions below as well.

Put

$$
q=k-h,\qquad v=k-g,\qquad \Delta=g-h=q-v>0.
$$

Liveness says $1\le q\le b+u$ and $1\le v\le a+u$.
The two integer intervals

$$
J_S=[\max(0,q-b),\min(u,q-1)],\qquad
J_T=[\max(0,v-a),\min(u,v-1)]
$$

are nonempty: $a,b>0$ and the preceding liveness bounds put their
lower endpoints below their upper endpoints. Their upper endpoints
are ordered with that of $J_T$ no greater. By (PE.5) they are disjoint,
so the upper endpoint of $J_T$ is strictly below the lower endpoint of
$J_S$. That lower endpoint is therefore positive and equals $q-b$.
The upper endpoint of $J_T$ is strictly below $u$, so it equals $v-1$.
Consequently

$$
q\ge b+1,\qquad v\le u,\qquad \Delta\ge b.           \tag{PE.6}
$$

These are deduced restrictions, not additional premises. In particular
there is enough common unread space for both completions used below.

For part 1, start at the $T$ history. Set every fresh $X$ bit to zero.
On successive first exposures in $U$, assign one to the first $v-1$
and zero to the rest. This is an adaptive proof of existence of one
completion, not a runtime choice facility. Since $v\le u$, these
assignments keep this history live until all $a+u$ unread coordinates
have been exposed. Indeed, until the first $v-1$ exposures in $U$ are
finished, there are at most $a\le a+u-v$ zeros and fewer than $v$
ones. Afterwards there are exactly $v-1$ ones in total, and a negative
certificate requires all $a+u-v+1$ zeros. The last necessary exposure
is therefore the last unread coordinate. The case $v=1$ is simply
all-zero unread replies.

The live freshness supplier excludes any query of old $T$, any selected
child or any second profile query during this suffix. It also forces
progress: a live latch is incorrect, and a repeated stationary state
would give nontermination on an actual completion. The resulting actual
$T$ source has weight $g+v-1=k-1$ and its run reads exactly $X\cup U$
once after the shared state. Its unique profile call is before its last
selected call. The caps leave no later invocation.

Now complete the $S$ history by giving $U$ these same assigned values
and giving $Y$ any values. Replay that entire $T$ suffix from the
common state. Its $X$ replies match the old zeros of the $S$ history;
its $U$ replies match by construction; its possible $RLR$ reply is the
cube-constant beta. It never queries $I$ or $Y$. Induction through the
fixed successors gives the identical suffix and terminal latch on this
actual $S$ source. Different old assignments on $I$ are immaterial.
In fact its weight is at most
$h+(v-1)+b=k-\Delta-1+b\le k-1$, by (PE.6).

Every prefix of a live history is live, so the selected prefix on $S$
has queried $S$ once at shortest roots. The full replayed run therefore
has selected invocation count and letter charge

$$
|S|+a+u=n+a-b,\qquad
C_S+C_X+C_U=W+C_X-C_Y.                              \tag{PE.7}
$$

The all-weight comparison at the beginning of the proof supplies at
least one further invocation and at least three further letters on
this same run. Applying both caps (PE.1) gives

$$
n+a-b+1\le n+1,\qquad
W+C_X-C_Y+3\le W+3.
$$

This proves $a\le b$ and $C_X\le C_Y$. Any repeat in (PE.7) is paid,
even when the $S$ source has already become certified. If the two
histories place their profile call differently, the replay must still
satisfy its own full-source charge; no identification of profile visits
or cancellation of their costs was made.

For part 2, start instead at the $S$ history and set every fresh $Y$
bit to one. On successive first exposures in $U$, put zero at the first

$$
z=b+u-q
$$

and one at the rest. Liveness and (PE.6) give $0\le z\le u-1$.
Until those $z$ zero exposures have occurred the number of ones is at
most $b<q$, and there are too few zeros to certify a negative answer.
Afterwards every remaining fresh bit is one. Reaching $q$ ones then
requires every unread coordinate. Thus the history remains live up to
its last selected call, its total weight is $h+q=k$, and its complete
suffix queries exactly $Y\cup U$ once at shortest roots, with the
unique profile call already paid before its final selected call.

Replay it on a completion of $T$ with the same $U$ values. Every $Y$
reply agrees with its old one; neither $I$ nor $X$ is queried in this
suffix. The complete actual $T$ run follows the same terminal latch.
Its weight is at least $g+(u-z)=k+\Delta-b\ge k$, so the replay also
has the required positive bit. Its selected count and charge are

$$
|T|+b+u=n+b-a,\qquad
C_T+C_Y+C_U=W+C_Y-C_X.
$$

Its own mandatory nonselected invocation contributes at least one call
and three letters. The two caps give $b\le a$ and $C_Y\le C_X$.
This proves part 2, and combining the two implications proves part 3.
No statement of this proof excludes paid discrimination after a history
has become constant. $\square$

## 4. The consumer in the original installed table

**Lemma 4.1 (general nested-support and equal-hit exclusion).** In the
scope of Theorem 3.1, two live cube histories at one running state
cannot have properly nested supports. If their supports differ and
their hit counts agree, they cannot share a running state either.

Proof. Suppose $S\subsetneq T$, put $b=|T\setminus S|>0$ and
$U=[n]\setminus T$, and retain hit counts $h,g$. Take the $T$
history to a negative saturated completion of total weight $k-1$.
Its suffix reads only $U$ and possibly $RLR$, and ends immediately
after its last selected call. Give the $S$ history the same $U$ values
and set every bit of $T\setminus S$ to one. This actual source
follows exactly the same suffix, even if the old assignments on $S$
and $T$ disagree. Correctness of their common zero entry gives

$$
h+b+(k-1-g)<k,\qquad h+b\le g.                      \tag{PE.8}
$$

For a positive saturated $T$ completion of weight $k$, give the $S$
history its same $U$ values and set $T\setminus S$ to zero. The
common suffix now returns one, giving

$$
h+(k-g)\ge k,\qquad h\ge g.                         \tag{PE.9}
$$

The two inequalities contradict $b>0$. Interchanging the histories
excludes the reverse containment. This is the general version of the
five-coordinate argument in PCA Lemma 38.3; no unfolding is counted.

For incomparable supports and equal hits put $q=k-h=k-g$.
Both clipped intervals in (PE.5) are nonempty by liveness and have
the same upper endpoint $\min(u,q-1)$. They therefore intersect,
contradicting (PE.5). Together with the nested case this proves the
second assertion. Equal supports and unequal hits are already excluded
by PCA Theorem 35.1. $\square$

**Theorem 4.2 (a necessary geometry for any strict subgrid improvement).**
Let $G=k(n-k+1)$ in the scope of Theorem 3.1. If an original-contract
preparer satisfying both caps has

$$
H<G+4+r,                                             \tag{PE.10}
$$

then its original installed table contains an incomparable collision of
two actual live histories at a selected state, oriented with $h<g$,
for which at least one of the following holds:

- $|S\setminus T|=|T\setminus S|$ and $C_{S\setminus T}=C_{T\setminus S}$;
- the $S$ history has an old one in $S\setminus T$, or the $T$ history
  has an old zero in $T\setminus S$.

If the original costs satisfy, for all $B,D\subseteq[n]$,

$$
B,D\ne\varnothing,\quad B\cap D=\varnothing,\quad |B|=|D|
             \quad\Longrightarrow\quad C_B\ne C_D,    \tag{PE.11}
$$

then some such collision must have the second, polarity-defect property.
This is a necessary condition; it asserts neither a strict improvement
nor sufficiency of any collision.

Proof. For every pair of integers

$$
0\le h\le k-1,\qquad 0\le z\le n-k,                 \tag{PE.12}
$$

choose one actual live history with $h$ exposed ones and $z$ exposed
zeros, ending just before a selected invocation. To see existence,
feed its first $h$ fresh selected queries ones and its next $z$ fresh
selected queries zeros. Every such prefix is live; arbitrary native
addresses cannot obstruct this choice, by the all-address saturation
facts. Between fresh selected queries the only possible live detour is
one paid $RLR$ call. After the prescribed replies, follow such a call
if present and stop just before the next selected query. Termination
and liveness guarantee that query exists. Every partial assignment has
actual cube completions. There are exactly $G$ pairs in (PE.12).
These histories are mathematical witnesses, not an installed rectangle
or an uncharged memory register.

There are also at least two installed running states disjoint from all
selected states. Here is the actual-source argument of [PCA, Lemma
7.1][PCA]. Choose $x_c=\beta$ and pairwise distinct branch images for
the other five classes. This is an actual $Z_c$ origin of code zero.
Replacing only $x_{b_3}$ by alpha gives an actual $\Pi_3$ origin of
code one, differing only in the $RLR$ occurrence cone. An installed
query in that cone is therefore necessary. Replacing only $x_{b_4}$
by alpha similarly forces a query in the disjoint $RRR$ cone. Both
cones are disjoint from every $E_i$ in (PE.2). The two original-entry
latches are different and both attained, and the $r$ mandated further
latches are distinct and counted. Thus, if $M$ is the number of all
installed selected states, including unused ones,

$$
H\ge M+2+2+r.                                       \tag{PE.13}
$$

This is a disjoint count in the installed alphabet; no path copies,
residual classes or reachable-message capacities replace $H$.

By (PE.10)–(PE.13), $M<G$. Two chosen histories must therefore end
at the same original selected state. They came from different pairs
in (PE.12). Equal supports and equal hits would make those pairs
equal. Equal supports with unequal hits are excluded by PCA Theorem
35.1; properly nested supports and different supports with equal hits
are excluded by Lemma 4.1. The collision is consequently incomparable
with unequal hits. Orient it by $h<g$. If it has no polarity defect,
every old $X$ bit is zero and every old $Y$ bit is one. Theorem 3.1
then forces equal private sizes and sums. Under (PE.11) this is
impossible because the private sets are nonempty and disjoint.

For an explicit admissible original input satisfying (PE.11), take
$c_i=5\,2^{i-1}$ and $s_i=c_i-4$. They are increasing positive
original positions. All subset sums differ: the greatest differing
power exceeds the sum of all lower powers. This uniqueness is an
input property, not a modification of an existing prescribed code.
Neither that property nor (PE.10) proves grid optimality. $\square$

**Corollary 4.3 (extreme balanced collisions cannot supply two boundary
thresholds).** Suppose a collision in Theorem 4.2 has no polarity defect
and its two live residuals are respectively AND on $Y\cup U$ and OR
on $X\cup U$. Then its equal private size $m$ satisfies

$$
2\le m\le\min(k-2,n-k-1).                            \tag{PE.14}
$$

In particular this extreme geometry cannot supply the necessary
collision at $k=3$ or $k=n-2$. This leaves the nonextreme and
polarity-defect alternatives of Theorem 4.2 in scope.

Proof. Theorem 3.1 gives $a=b=m>0$ and $C_X=C_Y$.
Since original positions have distinct individual costs, $m=1$ is
impossible. The common selected state queries a fresh coordinate for
both histories, so $u\ge1$. Write $j=|I|$. The extreme residuals give

$$
h=k-m-u,\qquad g=k-1.                               \tag{PE.15}
$$

The two histories must disagree on some old bit of $I$. Indeed, their
supports are incomparable, so neither path is a prefix of the other;
at their first different reply they query the same literal. A cube
constant cannot be that reply, so its coordinate is in both supports
and its bits differ. Stationarity and freshness justify this comparison
even though later query orders differ.

On $T$, the $I$ hit count is $g-m$. If it were zero, then
$g=m$, $k=m+1$, and $h=1-u$. Nonnegativity and $u\ge1$ force
$h=0,u=1$. Both histories would be all zero on $I$, contrary to the
preceding disagreement. Thus $g-m\ge1$, giving $m\le k-2$.
On $S$, the $I$ hit count is $h$. If $h=j$, then the $T$ hit count
on $I$ would be $g-m=h+u-1=j+u-1$. For $u>1$ this is impossible;
for $u=1$ both histories are all one on $I$, again contradicting
disagreement. Thus $j-h\ge1$. Since
$n=j+2m+u$ and $k=h+m+u$, this gives $n-k=j+m-h\ge m+1$,
proving the other upper bound. PCA Proposition 36.1 supplies the
already established onset $n=7,k=4,m=2$; it is not a new example
here. $\square$

## 5. Mixed private polarities with unequal private costs

**Theorem 5.1 (an infinite full-domain family of actual live sharing).**
Let $m\ge1$, $n=2m+5$, $k=m+3$ and $r\ge0$. Partition the original
coordinate indices as

$$
[n]=I\sqcup X\sqcup Y\sqcup U,\qquad
|I|=m+1,\quad X=\{x,x^\prime\},\quad
Y=\{y,y^\prime\},\quad |U|=m.
$$

Choose $t\in I$, put $d=c_t$, and suppose the original costs satisfy

$$
\begin{aligned}
d&\le c_{x^\prime},& d&\le c_{y^\prime},\\
c_x+d&\le c_y+c_{y^\prime},&
c_y+d&\le c_x+c_{x^\prime}.
\end{aligned}                                       \tag{PE.16}
$$

There is an original-contract preparer on the entire $\mathcal U_*$
with the exact whole-table count and attained execution maxima

$$
H=2^n-2^{m+3}+2m+9+r,\qquad
p=n+1,\qquad \ell=3+W.                              \tag{PE.17}
$$

Two actual live cube histories at one selected state have exposed data

$$
I=0^{m+1},\quad x=1,\ x^\prime=0,
\qquad\text{and}\qquad
I=1^{m+1},\quad y=0,\ y^\prime=1.                   \tag{PE.18}
$$

Their residuals are respectively AND on $Y\cup U$ and OR on $X\cup U$.
Both private polarity conditions of Theorem 3.1 fail. No equality of
private sizes and costs is asserted for a general merger.

Proof. Every selected state constructed below queries its one fixed
absolute literal $a_i=LLL L^{s_i}R$. In each Boolean successor table,
zero means three separately installed identical successors for alpha,
beta and absent; one means the branch successor. Thus the tables specify
all four native replies. Write $L_0=\widehat e_0,L_1=\widehat e_1$.

First form a complete binary decision tree of depth $n$, with a distinct
selected running state at every internal vertex and the two original
entry latches at its leaves according to the threshold of the whole
Boolean vector. Every path queries all coordinates once. At its first
$m+1$ levels use a fixed ordering of $I$. After an all-zero $I$ prefix,
query $x,x^\prime$ next; after an all-one $I$ prefix, query
$y,y^\prime$ next. After any other $I$ prefix use any fixed ordering
of the other coordinates. Finish every path by a fixed ordering of
its remaining coordinates. These choices specify literals at distinct
installed vertices; they do not compute addresses during a run.

There are $2^n-1$ selected running states in this full tree: level
$j$ has $2^j$ distinct states, $0\le j<n$. Delete the two disjoint
complete subtrees whose incoming histories are exactly (PE.18), each
at depth $m+3$. Each has $m+2$ levels of queries and
$2^{m+2}-1$ selected states. Replace both incoming edges by the start
of one common suffix, now specified in full.

Fix an order $u_1,\ldots,u_m$ of $U$. Install a state $V$ querying
$u_1$. For $1\le j<m$ install distinct states $Z_j,O_j$, each querying
$u_{j+1}$. Define their fixed successors by

| State | Zero successor | One successor |
| --- | --- | --- |
| $V$, $m=1$ | $B_X$ | $B_Y$ |
| $V$, $m>1$ | $Z_1$ | $O_1$ |
| $Z_j$, $j<m-1$ | $Z_{j+1}$ | $J$ |
| $O_j$, $j<m-1$ | $J$ | $O_{j+1}$ |
| $Z_{m-1}$, $m>1$ | $B_X$ | $J$ |
| $O_{m-1}$, $m>1$ | $J$ | $B_Y$ |

These are $2m-1$ states. The scan reaches $B_X$ if every $U$ bit is
zero, reaches $B_Y$ if every $U$ bit is one, and reaches $J$ as soon
as both values have been seen. No scan state contains a runtime count.
Install five more states, disjoint from all preceding states:

| State | Queried coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $B_X$ | $x$ | $B_{x^\prime}$ | $J$ |
| $B_{x^\prime}$ | $x^\prime$ | $L_0$ | $L_1$ |
| $B_Y$ | $y$ | $J$ | $B_{y^\prime}$ |
| $B_{y^\prime}$ | $y^\prime$ | $L_0$ | $L_1$ |
| $J$ | $t$ | $L_0$ | $L_1$ |

This suffix has exactly $2m+4$ selected states. State $J$ is an
ordinary paid query at the old coordinate $t$, with charge $d$;
it is not a hidden selector, stored phase bit or silent transition.
Both histories in (PE.18) enter $V$.

Verify the Boolean task first, for every vector in $\{0,1\}^n$.
Outside the two replaced subtrees the complete tree returns its exact
threshold. In the first history of (PE.18) there is one old hit, so
$k=m+3$ requires all $m+2$ unread bits in $Y\cup U$. In the second
there are $m+2$ old hits, so one unread hit in $X\cup U$ suffices.
The first history has $t=0$ and the second has $t=1$.

If $U$ contains both values, the first residual is zero and the second
is one; $J$ returns exactly these values. If all $U$ bits are zero,
the first history reaches $B_X$ with old $x=1$, hence goes to $J$ and
returns zero. On the second history, $t=1$, and $B_X$ computes
$x\lor x^\prime$: a hit at $x$ goes through $J$ to one, while a miss
reads $x^\prime$. If all $U$ bits are one, the first history with
$t=0$ obtains $y\land y^\prime$ from $B_Y$: a miss at $y$ goes
through $J$ to zero, while a hit reads $y^\prime$. The second history
has old $y=0$, hence goes through $J$ to one. These cases exhaust
all Boolean vectors, including $m=1$ when a mixed $U$ is impossible.

The proof gives the exact original full-domain preparer by adding the
following two distinct profile states, starting at $D$:

| State | Absolute literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $L_1$ | full-tree root | $T$ | $L_0$ |
| $T$ | $RRR$ | $L_1$ | $L_0$ | $L_0$ | $L_0$ |

On $Z_{b_3}$, the beta reply at $D$ enters the selected table. For
any branch image $x_a$, of arbitrary finite shape and depth, its
selected replies define a Boolean vector exactly as in Definition 1.2.
The identity (PE.3) makes every selected invocation the corresponding
native bit. The preceding all-vector proof therefore applies, including
alpha and absent selected replies. Outside $Z_{b_3}$, the full profile
partition of Definition 1.1 proves the profile table: alpha at $D$ is
$\Pi_3$, and, when $D$ returns branch, only $\Pi_4$ can still require
one, detected by alpha at $T$. Every other profile there requires zero.
All root-absence edges are installed. No address is removed from the
original legal address universe. The resulting latch is the exact
original entry for that identical source, and its fixed reader returns
the entire original canonical predecessor row.

For the execution bounds, a path that avoids the common suffix reads
all $n$ selected coordinates once and pays exactly $W$ selected letters.
A shared path has $m+3$ selected calls before $V$, at most $m$ in its
$U$ scan, and at most two after that scan. Its selected count is
therefore at most $2m+5=n$. It remains to charge every possible repeat
in absolute letters.

The two prefixes pay $C_I+C_X$ and $C_I+C_Y$, respectively. The scan
pays at most $C_U$. In the all-zero exit, the first prefix follows
$x,J$ and pays $c_x+d\le C_Y$ by (PE.16); the second prefix pays at
most $\max(C_X,c_x+d)=C_X$, since $d\le c_{x^\prime}$. In the
all-one exit, the first prefix pays at most
$\max(C_Y,c_y+d)=C_Y$, since $d\le c_{y^\prime}$; the second follows
$y,J$ and pays $c_y+d\le C_X$. In a mixed exit, the final charge is
$d\le C_X,C_Y$, again by (PE.16). Thus every shared path pays at
most

$$
C_I+C_X+C_Y+C_U=W                                  \tag{PE.19}
$$

selected letters on either history. A repeated $x$, $y$ or $t$ is
paid at its actual installed word; an omitted coordinate provides the
budget slack, without an uncharged observation or address operation.

Adding $D$ gives $q_P\le n+1$ and $\ell_P\le3+W$ on every selected
route. The other profile route has at most two calls and six letters,
which these bounds dominate. Both maxima are attained: because
$|I|=m+1\ge2$, choose a mixed $I$ vector. Its actual cube origin avoids
both deleted subtrees, and takes $D$ followed by all $n$ selected
queries. It pays $n+1$ calls and $3+W$ letters on that one source.

The exact selected-state count is

$$
(2^n-1)-2(2^{m+2}-1)+(2m+4)
             =2^n-2^{m+3}+2m+5.                     \tag{PE.20}
$$

Adding $D,T$, the two original-entry latches and all $r$ mandated
latches gives (PE.17). All states, including those not needed for early
certificates, are counted. Every specified graph is finite and acyclic,
so every run terminates; no acyclicity was imposed on competitors.
The full-tree path labels and scan subscripts name installed states,
not accessible work registers. The reader remains its separate fixed
eight-state apparatus with every complete whole-row output.

Finally each history (PE.18) has $m+3$ exposed coordinates, and its
unread AND or OR is nonconstant. Lemma 24.1 of PCA supplies actual
finite cube origins for every completion, proving actual liveness at
$V$. Their old private values are $(1,0)$ and $(0,1)$, and their hit
counts are $1<m+2$. The state $V$ is genuinely shared before
certification. The count (PE.17) exceeds $k(n-k+1)+4+r$: here the grid
has $(m+3)^2$ selected states, while (PE.20) exceeds that number.
For example, $2^{m+3}\ge(m+3)^2$ for $m\ge1$ by induction, and
$2^{2m+5}-2^{m+3}\ge7\,2^{m+3}$. Thus this construction supplies a
scope boundary, not a smaller installed table. $\square$

**Proposition 5.2 (distinct subset sums do not exclude mixed sharing).**
For every $m\ge1$, Theorem 5.1 applies to the following new original
input:

$$
\begin{gathered}
c_i=5\,3^{i-1},\qquad s_i=c_i-4\quad(1\le i\le2m+5),\\
t=1,\quad x=2,\quad y=3,\quad x^\prime=4,\quad y^\prime=5,\\
I=\{1\}\cup\{6,\ldots,m+5\},\qquad
U=\{m+6,\ldots,2m+5\}.
\end{gathered}                                      \tag{PE.21}
$$

All subset sums of these original costs are different, yet the whole
native table has the live sharing (PE.18), with

$$
C_X=150\ne450=C_Y.                                  \tag{PE.22}
$$

Proof. The sets in (PE.21) form the required partition with
$|I|=m+1$ and $|U|=m$. The original positions are strictly increasing
positive integers. The relevant costs are

$$
d=5,\quad c_x=15,\quad c_y=45,\quad
c_{x^\prime}=135,\quad c_{y^\prime}=405.
$$

Thus $5\le135,405$, $15+5\le45+405$, and
$45+5\le15+135$, verifying every condition in (PE.16). Theorem 5.1
therefore supplies all four-reply tables, the whole unbounded upper
domain, the unchanged original entries and reader, the exact whole-state
count and the attained caps. The displayed private sums are $15+135$
and $45+405$.

For subset-sum uniqueness, take the largest index $j$ at which two
subsets differ. Its term $5\,3^{j-1}$ exceeds the sum
$5(3^{j-1}-1)/2$ of all lower terms. Hence the difference cannot be
canceled by lower indices. This elementary positional argument is used
only to check an input property of the native construction, not as a new
standalone subset-sum theorem. Both polarity defects are present at its
common state. Consequently even uniqueness of every subset sum does not
justify dropping those hypotheses from Theorem 3.1 or replacing the
disjunction in Theorem 4.2 by an unconditional balance requirement.
$\square$

## 6. Scope of the installed-state obstruction

**Proposition 6.1 (the proved comparison and its boundaries).** Theorems
3.1 and 4.2 give necessary source-faithful private-exchange restrictions
at both original execution caps. Theorem 5.1 and Proposition 5.2 show
that the polarity qualification remains necessary even for original
costs with all subset sums distinct. These statements do not determine
$H_{\mathrm{exec}}(A,k;r)$ for general $n\ge6$, the unrestricted
$H_{\min}(A,k;r)$, grid optimality, or a no-larger whole-table replacement.

Proof. Theorem 4.2 counts collisions of original installed states and
uses the actual-source two-state overhead (PE.13). Theorem 3.1 bounds
the complete charged replayed executions, with no extreme-residual
assumption. Its two polarity implications may fail to apply to the same
collision. Proposition 5.2 provides exactly such an actual collision
with unequal private sums and distinct subset sums. Its table is larger
than the grid by Theorem 5.1, so it gives neither an attainable subgrid
point nor a counterexample to grid optimality. Conversely the necessary
collision condition does not prove a normalization or exclude all
polarity-defect collisions. Those whole-table questions remain open.

The success/failure grid and its count are the classical symmetric
read-once construction, reused here through [PCA, Theorem 26.1][PCA].
Wegener, *The Complexity of Boolean Functions*, Chapter 14 §4,
Definition 4.1 and Theorems 4.1 and 4.3, [printed pp. 423–425][WBP],
owns the synchronous BP1 optimum and residual count. His proof on
printed p. 424 explicitly says that graph-path realization holds for
BP1 and in general not for branching programs. Bryant,
*Graph-Based Algorithms for Boolean Function Manipulation*, [§2,
Definition 1][BRY], imposes increasing variable indices on every
nonterminal edge. Neither extra hypothesis is supplied by live-prefix
freshness. Sinha, *Some Topics in Parallel Computation and Branching
Programs*, [§2.1.3, printed p. 17][SINHA], permits union cycles when
no semantic path cycles; the stated Pippenger leveling construction
makes $l+1$ copies of each of $s$ states. Its $(l+1)s$ count supplies
no cardinality-preserving replacement here. No numerical bound from
these more restricted representations is imported into (PE.13).

The native suppliers are the image grammar and inverse of TMC
Proposition 22.2; the complete rows, disequalities, profiles and
all-address occurrence identity of NBP Propositions 9.3, 9.4 and 15.2,
Theorem 10.4 and (NBP.9.7); its fixed reader in Theorem 15.5; and the
actual cube, saturation, interval exclusion and original grid of PCA
Lemmas 7.1 and 24.1 and Theorems 26.1, 34.3 and 35.1. The general
one-sided charges, their original installed-table consumer and the
mixed-polarity family are the deductions proved here. The elementary
positional uniqueness and complete-tree counts are mature intermediate
tools, not independent originality claims. These are ordinary-paper
results; no kernel or worldwide-priority assertion follows.

Every application still requires Assumption 1.4. The equations prove
no acquisition, authentication, export, isolation, entry or stationary
continuity service and no physical resource transfer. In particular a
same-source map of allowed operations, legal histories, target updates
and prices would be needed before a stopped-access, quantum,
continuous-control, certificate or reselected-code theorem could price
this prescribed native preparer. No such different-contract resource
is used in these proofs. $\square$

[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[TMC]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[WBP]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[BRY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[SINHA]: https://dada.cs.washington.edu/research/tr/1995/08/UW-CSE-95-08-02.pdf

## 追加锚（本行以下为增补区）

## 7. Paired completions and paid discrimination

**Definition 7.1 (collision data and common-coordinate discrepancy).**
Retain Definitions 1.1–2.1 and Assumptions 1.3–1.4 in their entirety.
In particular the domain is the full finite-tree domain $\mathcal U_*$,
the handoff is the literal prescribed complete entry, the reader has its
original eight states, and both inequalities (PE.1) hold on every actual
source. All installed states and all invocations remain charged,
including unused states, the $r$ further mandated latches, repeats and
post-certification queries. No variable order, read-once property or
acyclicity of the union of source paths is assumed.

Let $n\ge6$ and $3\le k\le n-2$. Consider two actual live cube
histories ending at one installed selected running state. Their supports
$S,T$ are incomparable and their hit counts satisfy $h<g$. Write their
old assignments as $s:S\to\{0,1\}$ and $t:T\to\{0,1\}$, and use
$X,Y,I,U,a,b,u$ from Definition 2.1. Put

$$
\begin{gathered}
Q=k-h,\qquad V=k-g,\qquad \Delta=g-h=Q-V,\\
p=|\{j\in X:s_j=1\}|,\qquad y=|\{j\in Y:t_j=1\}|,\\
\varepsilon=\Delta-b,\qquad e=p+b-y,\qquad
D=\Delta+p-y=\varepsilon+e.                         \tag{PE.23}
\end{gathered}
$$

These sets and numbers describe mathematical histories; none is a
runtime register. The old hit counts on $I$ are $h-p$ and $g-y$, so
$D=(g-y)-(h-p)$. Theorem 3.1, specifically (PE.6), gives

$$
Q\ge b+1,\qquad 1\le V\le u,\qquad
\varepsilon\ge0.                                  \tag{PE.24}
$$

Also $e\ge0$, and $e>0$ means precisely that there is an old one in
$X$ on the first history or an old zero in $Y$ on the second. Thus
$D>0$ is equivalent to $\Delta>b$ or such a private polarity defect.

**Theorem 7.2 (paired completions, joint certificates and paid bounds).**
In Definition 7.1 let

$$
J=\bigl[\max(0,V-p),\ \min(u,Q-y-1)\bigr]
                              \cap\mathbb Z.        \tag{PE.25}
$$

This interval is nonempty exactly when $D>0$. For every assignment
$\tau:U\to\{0,1\}$ of weight $z\in J$, there are actual cube
completions of the two incoming histories which agree on $X,Y,U$,
differ only on $I$, and require respectively $L_0=\widehat e_0$ and
$L_1=\widehat e_1$. Starting from the common state, their first
different native reply is at a word in $E_i$ for some $i\in I$ with
$s_i\ne t_i$. Both histories are already mathematically certified,
with their different prescribed bits, strictly before this invocation.
The discriminator is a paid running state absent from both incoming
state histories, including their common endpoint.

For each of these paired completions there are sets, taken from that
same common continuation strictly before its first different reply,

$$
\begin{gathered}
A_1\subseteq\{j\in X:s_j=1\},\qquad
B_0\subseteq\{j\in Y:t_j=0\},\\
U_0\subseteq\{j\in U:\tau_j=0\},\qquad
U_1\subseteq\{j\in U:\tau_j=1\},
\end{gathered}
$$

such that, for the discriminator coordinate $i$ just specified,

$$
\begin{aligned}
|B_0|+|U_0|&\ge b+u-Q+1,\\
|A_1|+|U_1|&\ge V,\\
|A_1|+|B_0|+|U_0|+|U_1|+1
                   &\le\min(a+u,b+u),\\
C_{A_1}+C_{B_0}+C_{U_0}+C_{U_1}+c_i
                   &\le\min(C_X+C_U,C_Y+C_U).
\end{aligned}                                      \tag{PE.26}
$$

If $D>0$, at least $a+b+u+1$ distinct installed selected states occur
in the union of continuations, at or after the common state, over all
completions of either incoming history. This is a local union count.

Proof. The restrictions (PE.24) are consequences of the original
interval exclusion, rather than extra restrictions on competitors. For
completeness, its two clipped intervals are

$$
[\max(0,Q-b),\min(u,Q-1)],\qquad
[\max(0,V-a),\min(u,V-1)].
$$

They are nonempty by liveness and $a,b>0$. Since $Q>V$, the second
upper endpoint is no greater than the first. Their disjointness in
(PE.5) places the second interval strictly below the first. The first
lower endpoint must consequently be positive, hence $Q-b$; the
second upper endpoint must be below $u$, hence $V-1$. Their strict
separation yields $Q\ge b+1$, $V\le u$ and $\Delta\ge b$,
as in Theorem 3.1.

Suppose first that $D>0$. All quantities are integers, and

$$
Q-y-1\ge b-y\ge0,\qquad V-p\le u,\qquad
(Q-y-1)-(V-p)=D-1\ge0.
$$

These inequalities prove that the clipped lower endpoint in (PE.25)
does not exceed its upper endpoint. If $D=0$, nonnegativity of
$\varepsilon$ and $e$ forces

$$
\Delta=b,\qquad p=0,\qquad y=b,\qquad Q=V+b.
$$

Then (PE.25) has lower endpoint $V$ and upper endpoint at most $V-1$,
so is empty. Since $D\ge0$ always, this proves the asserted exact
nonemptiness criterion, including the balanced-tight boundary.

Fix $\tau$ of weight $z\in J$. Define two complete Boolean vectors
by

$$
\begin{array}{c|cccc}
 &I&X&Y&U\\ \hline
\theta^-&s|_I&s|_X&t|_Y&\tau\\
\theta^+&t|_I&s|_X&t|_Y&\tau.
\end{array}                                        \tag{PE.27}
$$

The first extends the $S$ history and the second extends the $T$
history. Their exposed replies are unchanged, including every
cube-constant reply, so determinism makes them follow those histories.
Definition 2.1 supplies simultaneous actual finite origins for both
vectors, with all original current-row disequalities. Their weights are

$$
|\theta^-|=h+y+z\le k-1,\qquad
|\theta^+|=g+p+z\ge k.                             \tag{PE.28}
$$

Indeed these are exactly the two opposite-output inequalities defining
(PE.25), together with $0\le z\le u$. Although both cube sources
have complete target row $R_0$, their prescribed preparation entries
are the different literal latches $L_0,L_1$.

From the common running state, fixed successors give identical state
sequences until a first different reply. If there were no such reply,
sourcewise termination would give the same latch, contradicting
(PE.28). The all-address classification (PE.2) says that this first
difference must occur in $E_i$ for a coordinate where the vectors
differ. By (PE.27), $i\in I$ and $s_i\ne t_i$. In both histories
this coordinate is old. A live cube history can query only a fresh
selected coordinate, by the saturation supplier in Definition 2.1.
Thus neither continued history is live immediately before this
invocation. As their actual completions are respectively negative and
positive, they already have at least $n-k+1$ distinct observed zeros
and $k$ distinct observed ones. This is certification of their
mathematical threshold residuals; the table receives no free
certificate bit or silent operation.

If the discriminator state had occurred on either incoming history,
the corresponding completed actual source would revisit that same
entire changing configuration. On a fixed source its absolute query
has the same reply and fixed successor each time. Iterating would
therefore repeat a deterministic cycle forever, contradicting
sourcewise termination. The same argument excludes equality with the
common endpoint. Its actual visit pays one call and its whole word
length, at least $c_i$. This proves distinctness only from these two
incoming histories, not from states used by other histories.

Take $A_1,B_0,U_0,U_1$ to be all the indicated coordinates queried in
the common continuation before that first different reply. They are
sets of distinct coordinates; repeated visits do not enlarge them and
remain charged. The negative source has $|S|-h$ old zeros. Its only
new observed zeros can be in $B_0$ or $U_0$. The positive source has
$g$ old ones; its only new observed ones can be in $A_1$ or $U_1$.
Old common coordinates queried earlier in the continuation cannot add
new exposed coordinates. The two certificates therefore give

$$
\begin{aligned}
|S|-h+|B_0|+|U_0|&\ge n-k+1,\\
g+|A_1|+|U_1|&\ge k.
\end{aligned}
$$

Since $n-|S|=b+u$, these are the first two inequalities of (PE.26).
The sets come from one actual shared continuation, not independently
chosen certificate optimizers.

Write $K=|A_1|+|B_0|+|U_0|+|U_1|$ and
$C=C_{A_1}+C_{B_0}+C_{U_0}+C_{U_1}$. Every prefix of a live history
is live. Consequently the incoming selected contributions are exactly
$|S|$ calls and $C_S$ letters, or $|T|$ calls and $C_T$ letters:
they exposed their supports once at shortest occurrence roots. These
are selected contributions, not assertions that a prefix had no paid
profile call. Disjoint coordinate classes require at least $K$
selected continuation invocations, in addition to the discriminator.
Their letter charge is at least $C+c_i$, even if some are longer
selected-child words after certification.

The all-weight comparison proved at the beginning of Theorem 3.1
supplies on each complete cube run at least one nonselected invocation
of length at least three. It is disjoint from all the selected visits
just counted. Apply both original caps first to the negative source
and then to the positive source, without adding the two executions:

$$
\begin{aligned}
|S|+K+1+1&\le n+1,& C_S+C+c_i+3&\le W+3,\\
|T|+K+1+1&\le n+1,& C_T+C+c_i+3&\le W+3.
\end{aligned}                                      \tag{PE.29}
$$

Since $n-|T|=a+u$, $W-C_S=C_Y+C_U$ and
$W-C_T=C_X+C_U$, (PE.29) proves the last two inequalities of
(PE.26). Other visits, including repeats and profile calls at different
times on the two sources, can only increase their own execution costs.
No post-certification freshness or free replay was used.

For the local state count, every unread coordinate of a live threshold
residual is relevant. If the residual has $d$ unread coordinates and
needs $v$ hits, $1\le v\le d$, assign $v-1$ hits to its other
$d-1$ coordinates. Flipping the remaining coordinate changes the
required latch. Both completions are actual cube sources. A correct
deterministic continuation must therefore query an address in that
coordinate's $E_j$, since all other replies agree. Apply this argument
to all coordinates in $X\cup U$ from the $T$ history and in
$Y\cup U$ from the $S$ history. Disjointness of the $E_j$ requires
at least $a+b+u$ selected states among those continuations. The
already forced discriminator has a coordinate in $I$, outside that
union, and contributes one further state. Its incoming query state for
that same old coordinate is different by the termination argument.
States counted here may serve other collisions or lie in other
witness images; the count is not globally additive. $\square$

**Corollary 7.3 (strict separation with a singleton private side).**
Under Definition 7.1, if $D>0$ then

$$
\Delta-b\ge2-\min(a,b).                              \tag{PE.30}
$$

In particular $\Delta=b$ with $D>0$ requires $a,b\ge2$.
Every collision with $\min(a,b)=1$, including the $D=0$ alternative,
satisfies the stronger necessary separation

$$
\Delta\ge b+1.                                      \tag{PE.31}
$$

Proof. Add the two certificate inequalities in (PE.26) to obtain
$K\ge b+u-Q+1+V=u+1-\varepsilon$. Its count inequality gives
$K+1\le u+\min(a,b)$, proving (PE.30). Now suppose
$\min(a,b)=1$ and $\Delta=b$. If $D>0$, (PE.30) is impossible.
If $D=0$, the exact boundary in Theorem 7.2 gives $p=0,y=b$:
all old $X$ bits on the first history are zero and all old $Y$ bits
on the second are one. Theorem 3.1 then gives $a=b$ and $C_X=C_Y$.
The sets must be disjoint singletons. Their original individual costs
are distinct because $s_1<\cdots<s_n$, a contradiction. Finally
$\Delta\ge b$ by (PE.24), so integrality yields (PE.31). No distinct
subset-sum hypothesis is needed. $\square$

## 8. Singleton private sharing for every original cost input

**Theorem 8.1 (a complete modified-grid family).** Let $m\ge2$,
$n=2m+2$, $k=m+1$ and $r\ge0$. For every original set of positions
$A=\{s_1<\cdots<s_n\}$ in Definition 1.2, there is a preparer on
all of $\mathcal U_*$ retaining the exact prescribed code, the literal
original entry latches and the unchanged eight-state reader, with

$$
\begin{gathered}
G=k(n-k+1)=(m+1)(m+2),\\
H=G+m+6+r,\qquad
\max_{v\in\mathcal U_*}q_P(v)=n+1,\qquad
\max_{v\in\mathcal U_*}\ell_P(v)=3+W.                \tag{PE.32}
\end{gathered}
$$

One actual source attains both maxima together. At a common selected
state there are actual live cube histories with singleton private sets
and exactly one private polarity defect. The table exceeds the original
grid count $G+4+r$ by $m+2$ states; it supplies no strict subgrid
example.

Proof. Partition the original coordinate indices as

$$
\begin{gathered}
I=\{1,\ldots,m\},\quad x=m+1,\quad y=m+2,\quad
X=\{x\},\quad Y=\{y\},\\
u_j=m+2+j\quad(1\le j\le m),\qquad
U=\{u_1,\ldots,u_m\},\qquad t=1.
\end{gathered}                                      \tag{PE.33}
$$

Strict individual cost order gives
$c_1<c_x<c_y<c_{u_1}<c_{u_2}$; the last term exists since $m\ge2$.
No constraint on subset sums is imposed.

Here is the entire installed preparation table. Each selected row with
coordinate $i$ queries the original absolute word $a_i=LLL L^{s_i}R$.
A row with zero successor $Z$ and one successor $O$ means the four
fixed successors

$$
(\mathsf{alpha},\mathsf{beta},\mathsf{branch},\mathsf{absent})
                  \longmapsto(Z,Z,O,Z).              \tag{PE.34}
$$

Thus alpha and absent replies are specified and charged, rather than
removed from the domain. Install every distinct grid state

$$
R_{h,z},\qquad 0\le h\le m,\quad0\le z\le m+1,
                      \quad(h,z)\ne(0,m+1).
$$

Except for the two overrides below, its coordinate is $h+z+1$, its
zero successor is $L_0$ if $z=m+1$ and $R_{h,z+1}$ otherwise, and
its one successor is $L_1$ if $h=m$ and $R_{h+1,z}$ otherwise.
Install these overrides and new selected states:

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $R_{0,m}$ | $x$ | $V$ | $R_{1,m}$ |
| $R_{m,0}$ | $y$ | $V$ | $L_1$ |
| $V$ | $u_1$ | $Z_2$ | $B_Y$ |
| $Z_j$, $2\le j<m$ | $u_j$ | $Z_{j+1}$ | $J$ |
| $Z_m$ | $u_m$ | $B_X$ | $J$ |
| $B_X$ | $x$ | $L_0$ | $L_1$ |
| $B_Y$ | $y$ | $J$ | $R_{2,m+1}$ |
| $J$ | $1$ | $L_0$ | $L_1$ |

For $m=2$ the intermediate $Z_j$ range is empty, and $Z_2=Z_m$
is its single separately installed scan state. All the indicated
indices are legal: generic coordinates are between $1$ and $n$;
$R_{2,m+1}$ is retained and queries coordinate $m+4=u_2$.
The only original predecessor of the omitted $R_{0,m+1}$ was the
zero edge of $R_{0,m}$, now redirected. Every successor therefore
names an installed state or a latch.

Install two further distinct profile states, with source-independent
start $D$:

| State | Absolute word | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $L_1$ | $R_{0,0}$ | $D_4$ | $L_0$ |
| $D_4$ | $RRR$ | $L_1$ | $L_0$ | $L_0$ | $L_0$ |

The latches are literally $L_0=\widehat e_0$ and
$L_1=\widehat e_1$. Install every one of the $r$ mandated further
distinct latches, even though no transition needs to enter them.
All listed grid, new selected, profile and latch states are distinct.
In particular $J$ is a new paid state querying the same word $a_1$
as an earlier grid state. Equal words do not identify states. Subscripts
name installed configurations and supply no hidden runtime counter,
phase coordinate or stored history.

First prove the Boolean threshold task on every vector of selected
branch indicators. The ordinary success/failure grid and its count are
reused from PCA Theorem 26.1, as in Section 6. Before a modified state
is reached, $R_{h,z}$ has exposed the first $h+z$ coordinates, with
$h$ ones and $z$ zeros. It returns one at $m+1$ ones and zero at
$m+2$ zeros. State $R_{0,m}$ is reached exactly after $I=0^m$;
its query at $x$ is unchanged except that zero now enters $V$.
State $R_{m,0}$ is reached exactly after $I=1^m$; it queries $y$
instead of $x$. A one there already supplies the $(m+1)$st hit and
correctly returns $L_1$. Its zero enters $V$. These are the only two
contexts entering $V$:

$$
\mathcal A:\ I=0^m,\ x=0,\qquad
\mathcal B:\ I=1^m,\ y=0.                           \tag{PE.35}
$$

Their residual tasks are AND on $Y\cup U$ and OR on $X\cup U$,
respectively. Each is live and has $m+1$ unread coordinates. Their
old coordinate $1$ is zero on $\mathcal A$ and one on $\mathcal B$.

If $u_1=0$, the first context is already negative. The $Z$ scan
reads $u_2,\ldots,u_m$ until a first one. Such a one certifies the
second context as positive. The paid state $J$ then rereads coordinate
$1$ and returns exactly the two required different bits. If all $U$
bits are zero, the scan instead reaches $B_X$. In the first context
its old $x=0$ correctly returns zero. In the second context the only
remaining OR variable is $x$, so $B_X$ gives the correct answer.

If $u_1=1$, the second context is already positive. State $B_Y$
reads $y$. A zero certifies the first context as negative, and $J$
again returns the correct respective bits. A one at $B_Y$ is possible
only in the first context: the second has old $y=0$, and stationary
native replies cannot change it. In the first context the exposed set
is now $\{1,\ldots,m+3\}$, with two ones and $m+1$ zeros. Entry at
$R_{2,m+1}$ thus has precisely its ordinary grid meaning. Its retained
AND tail $R_{2,m+1},\ldots,R_{m,m+1}$ queries
$u_2,\ldots,u_m$ and returns their conjunction. This proves the
threshold on every selected Boolean vector. Every other route retains
the ordinary grid interpretation up to its correct latch.

Now transfer this proof to the original full domain, without making
the cube a promise. On $Z_{b_3}$, the reply at $D$ is beta. For
an arbitrary finite branch image $x_a$, its selected native replies
at the $a_i$ define exactly the Boolean vector in Definition 1.2,
including zero indicators for alpha, beta and absent. The all-address
occurrence identity (PE.3) holds on that same source, even past a
leaf. The all-vector argument therefore gives its exact prescribed
threshold. Independence of those indicators on an arbitrary branch
image is unnecessary.

The eleven exhaustive actual profiles of Definition 1.1 account for
all other sources. On $\Pi_3$, $D$ returns alpha and goes to $L_1$.
On $Z_{b_3}$ it returns beta as above. On each of the other nine
profiles it returns branch. Among these, $\Pi_4$ is exactly the case
with alpha at $D_4$ and requires one. The remaining eight profiles
$\Pi_1,\Pi_2,Z_a,Z_{b_1},Z_{b_2},Z_c,Z_{b_4},Z_*$ require zero
and take zero entries at $D_4$. Root-absence edges are installed in
both profile rows. This reuses the profile argument of Theorem 5.1.
Handoff is the original literal entry, so the unchanged reader returns
the entire complete canonical predecessor row: ordered exterior,
occurrence holes, equality partition, all retained disequalities and
all strict-prefix blocking guards. No inverse or profile operation
has been added to the running table.

Both original execution caps can be checked on each actual route.
A prefix in either context (PE.35) has $m+1$ selected calls, with
letter charge $C_I+c_x$ or $C_I+c_y$, respectively. All of the
following charges include every later repeat.

If all $U$ bits are zero, the suffix makes $m$ queries in $U$ and
one at $B_X$. The total selected count is $2m+2=n$. Its selected
letter charges on the two contexts are respectively

$$
C_I+2c_x+C_U=W+c_x-c_y<W,\qquad
C_I+c_y+C_U+c_x=W.                                 \tag{PE.36}
$$

If $u_1=0$ and the first hit is $u_j$, $2\le j\le m$, the suffix
makes $j$ queries in $U$ and one at $J$. Its total selected count
is $m+j+2\le n$. Write $U_{\le j}=\{u_1,\ldots,u_j\}$.
The selected letter charges are

$$
C_I+c_x+C_{U_{\le j}}+c_1\le W,\qquad
C_I+c_y+C_{U_{\le j}}+c_1\le W,                     \tag{PE.37}
$$

because respectively $c_1<c_y$ and $c_1<c_x$ pay for the reread,
with any unqueried $U$ costs also omitted on that same run.

If $u_1=1$ and $B_Y$ returns zero, the suffix consists of
$V,B_Y,J$. The total selected count is $m+4\le2m+2=n$. In context
$\mathcal A$, its charge is

$$
C_I+c_x+c_{u_1}+c_y+c_1\le W,
$$

since $U\setminus\{u_1\}$ contains $u_2$ with $c_{u_2}>c_1$.
In context $\mathcal B$, its charge is

$$
C_I+2c_y+c_{u_1}+c_1\le W.                          \tag{PE.38}
$$

For the latter inequality it suffices that
$c_y+c_1\le c_x+C_{U\setminus\{u_1\}}$, which follows from
$c_1<c_x$ and $c_y<c_{u_2}\le C_{U\setminus\{u_1\}}$.
Thus the old $y$ and coordinate $1$ rereads are both fully paid.
If $u_1=1$ and $B_Y$ returns one, only context $\mathcal A$ is
possible. The suffix has $V,B_Y$ and at most $m-1$ retained tail
queries. The total selected count is at most $n$, and every selected
coordinate on that route is queried at most once, so its charge is
at most $W$.

A route avoiding $V$ has at most $n$ fresh selected queries and at
most $W$ selected letters. This includes the modified direct positive
certificate at $R_{m,0}$, which skips $x$ and reads $y$ once.
Every route entering the selected table also pays $D$ once: one call
and three letters. Hence $q_P\le n+1$ and $\ell_P\le3+W$ on each
of these same actual sources. The other profile routes make at most
two calls and six letters, dominated by both caps since $n\ge6$ and
the original $c_i=s_i+4\ge5$.

For simultaneous attainment take the actual cube completion

$$
I=0^m,\qquad x=0,\qquad y=1,\qquad U=1^m.
$$

It has weight $m+1=k$. Its selected route queries
$I,x,u_1,y,u_2,\ldots,u_m$, every coordinate exactly once.
Including $D$, this one source pays $n+1$ calls and $3+W$ letters.
The cube gives an actual finite origin with the original disequalities,
not just a formal indicator vector.

Every actual route terminates. Ordinary grid edges advance finite
indices; the modified prefix enters a finite scan or an immediate
terminal test. Its only new return to the grid is $R_{2,m+1}$, whose
finite AND tail cannot return to either modified prefix or the scan.
Both $J$ and $B_X$ go directly to latches. The four native replies
are fully covered by (PE.34) and the profile table. This proves
sourcewise termination without restricting the competitor class.

There are $G-1$ installed retained grid states and
$1+(m-1)+1+1+1=m+3$ new selected states. Consequently the complete
selected count is $G+m+2$. Adding the two profile states, both original
entry latches and all $r$ further mandated distinct latches gives
$H=G+m+6+r$. Unused retained states remain counted. The common
continuation uses its $m+3$ new states and the $m-1$ retained AND-tail
states, totaling $2m+2$, the same number as two separate chains on
$m+1$ variables. Legal sharing here does not itself save states.

Finally the histories (PE.35) are actual live cube histories at $V$,
with $h=0,g=m,a=b=1,u=m$. Their residuals are nonconstant and every
completion is actual. The old $X$ zero satisfies the first polarity
hypothesis of Theorem 3.1, with its correct consequence $c_x<c_y$;
the old $Y$ zero violates its second polarity hypothesis. Only one
defect is present. Since only strict individual cost order was used,
the construction also applies to every original input having distinct
subset sums. $\square$

**Corollary 8.2 (the six-coordinate boundary specialization).** For
$m=2$, Theorem 8.1 gives $n=6,k=3$ and $H=20+r$, whereas the
original grid has $16+r$ states. Its shared live histories attain
$\Delta=b+1$ in (PE.31).

Proof. Here $I=\{1,2\}$, $x=3$, $y=4$ and $U=\{5,6\}$.
The retained grid has $(2+1)(2+2)-1=11$ selected states. The five
new selected states are $V(a_5),Z_2(a_6),B_X(a_3),B_Y(a_4),J(a_1)$.
The one edge at $B_Y$ enters the retained $R_{2,3}(a_6)$, whose
zero and one successors are $L_0,L_1$. The total is therefore
$11+5+2+2+r=20+r$, compared with $12+4+r=16+r$ for the grid.
The simultaneous-attainment route is $1,2,3,5,4,6$ after $D$.
At $V$ the hits are $h=0,g=2$, and $a=b=1,u=2$, so
$\Delta=2=b+1$. These are symbolic substitutions in Theorem 8.1,
not an executed instance or an optimum assertion. $\square$

## 9. The remaining whole-table comparison

**Proposition 9.1 (local discrimination and the missing global charge).**
Theorems 7.2 and 8.1 leave the original universal grid-optimum problem
unresolved. More precisely, choose the $G=k(n-k+1)$ actual live
$(h,z)$ witnesses of Theorem 4.2, let $\mathcal W$ be their image
in the original selected-state alphabet, put $N=|\mathcal W|$, and
let $M$ count all installed selected states. A sufficient missing
whole-table implication is

$$
M-N\ge G-N,                                         \tag{PE.39}
$$

or, concretely, a charge assigning at least $G-N$ distinct installed
selected states outside the entire image $\mathcal W$ to the lost
witness multiplicities. It must account for both $D=0$ and $D>0$
collisions. Neither the local discriminator nor the local continuation
count in Theorem 7.2 supplies this implication.

Proof. The $G$ witnesses exist by Theorem 4.2. A collision loses one
or more multiplicities when those witnesses are mapped into their
$N$ distinct selected states. If the stated charge were available,
(PE.39) would give $M\ge G$. The independently forced two
nonselected running states, two original entry latches and $r$
mandated latches in (PE.13) would then give $H\ge G+4+r$.
The original grid attains that count under the original caps, but
the required charge is not established here.

Theorem 7.2 distinguishes the paid discriminator from only its two
incoming state histories. The state may belong to $\mathcal W$ as
the endpoint of a different live witness, or the same state may serve
several collisions. Likewise the local $a+b+u+1$ continuation sets
can overlap one another and $\mathcal W$. They cannot be summed
as disjoint charges. The $D=0$ balanced-tight case has no interval
(PE.25) at all, and distinct individual costs exclude it only when a
private side is a singleton, not for all larger private sets.
Thus even the existence of a paid common-coordinate reread in every
$D>0$ pair does not produce a global multiplicity charge.

Theorem 8.1 also rules out closing this gap merely by prohibiting all
singleton-private sharing, all polarity defects, or every such collision
at $k=3$. Its complete table obeys the full original contract. However,
it has $H=(G+4+r)+(m+2)>G+4+r$, so it neither refutes grid
optimality nor proves its own added states necessary.

An alternative completion would be a faithful whole-table comparison
or a cardinality-preserving normalization. Such a bridge must preserve
the entire original domain, all words and legal source paths, the
literal handoff, sourcewise termination and both paid caps. A unique
level or semantic residual per installed state is not established.
Union paths need not be actual paths on one source. Unfolding or
leveling with additional copies, or imposing increasing order, cannot
be used as a count-preserving bridge without proof. The restricted
literature results discussed in Proposition 6.1 therefore do not close
(PE.39). The general $H_{\mathrm{exec}}(A,k;r)$, unrestricted
$H_{\min}(A,k;r)$ and the separate full-$N$ unequal-tail target remain
unresolved. No overall completion follows. $\square$

The extra content is the exact paired-completion interval, the paid
common-coordinate discriminator after both certificates, the joint
same-continuation count and letter inequalities, singleton separation,
and the complete singleton-private family for every original ordered
cost input. Theorem 3.1 supplies (PE.6), the all-weight nonselected
charge and the two polarity implications; Lemma 4.1 and Theorem 4.2
supply the collision exclusions and installed-state witnesses.
Theorem 5.1 and Proposition 5.2 already establish mixed sharing and
its compatibility with distinct subset sums for other families. Their
profile gate and paid old-coordinate recovery are reused; mixed
sharing in general is not an additional discovery here.

The actual inverse, complete rows, profiles, occurrence identity,
simultaneous cube, live saturation, interval exclusion, unchanged reader
and classical threshold grid are used only at the explicitly stated
supplier scopes in Sections 1–2 and 6. Their nested source bodies are
not additional premises silently imported here. Threshold certificates,
deterministic indistinguishability and stationary cycling on a fixed
source are mature tools. The deductions above are ordinary proofs
relative to these credited premises, not kernel certificates or claims
of worldwide originality. No external novelty search is asserted.

All supplied services and separate prices of Assumption 1.4 remain
required. The results prove no acquisition, authentication, export,
isolation, initialization, handoff-storage or physical-resource service.
In particular $H,q_P,\ell_P$ yield no total physical cost conclusion,
no general neural-network theorem and no empirical machine-learning
claim. The original optimum and the remaining global charge are not
replaced by the larger constructed table.

## 追加锚（本行以下为增补区）
