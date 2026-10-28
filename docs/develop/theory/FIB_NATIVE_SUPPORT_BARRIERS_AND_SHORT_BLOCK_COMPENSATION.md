# Native support barriers and short-block compensation

The bounded increment in this volume is a strict unit of surplus on every
nonempty maximal block of one or two support-ambiguous depths, and the
resulting slack in the necessary global deficit. The complete current
[SI, Sections 9--10][SI] already supplies common-support cuts, localization
on the original installed coordinate-multiplicity vector, exact accounting,
nonnegative compensation through span four, no sharing in early-ending
gaps, the terminal span-four margin, enlarged qualified grid minima and
actual-prefix inheritance. These results are credited and proved below.
SI's stated nonnegative bounds at spans two and three leave the strict
short-block unit as an additional bounded inequality. The current remaining
frontier consists of late gaps of span at least five; the strict units
contribute to its exact compensation sum on one actual graph. The boundary
fixed-prefix statement composes [CP, Theorem 5.1][CP] with [Third, Lemma
7.1][Third]; the inherited-cut application also credits SI Theorem 10.8.
The weighted appendix reproduces [WTF, Section 11][WTF]. The unrestricted
intermediate-threshold comparison remains unresolved.

## 1. The unchanged model and its native transport

**Definition 1.1 (source fiber and complete target).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E=\langle\beta,\alpha\rangle,\quad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

A query reads the root type on the fixed current tree $\rho u$ at one
finite absolute word in $\{L,R\}^*$, including the empty word. Its four
replies are alpha, beta, branch and
absent; descent past a leaf gives absent. At $P=\{L,R\}^3$ the fixed
current row $R_*$ has whole-subtree equality classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
$$

Different classes are whole-subtree disequal. The source domain is exactly

$$
\mathcal U_* = \{u\in\mathcal T:R_P(\rho u)=R_*\},
$$

with no bound on finite size, depth or interior shape. The output to be
recovered is the complete predecessor row $R_P(u)$, including its ordered
exterior, every reached occurrence hole, canonical equality partition,
every surviving disequality and every concrete strict-prefix blocking guard.
Neither source selection nor a restriction to cube-shaped sources is allowed.

The image algebra is

$$
\mathcal I=\{\beta,E\}\ \cup
 \{\langle y,z\rangle:y,z\in\mathcal I\}.
$$

These are disjoint cases because $\alpha\notin\mathcal I$. Its recursive
inverse sends $\beta$ to $\alpha$, $E$ to $\beta$, and an image-child
pair to the pair of inverses. Induction gives both inverse identities.
In the fixed cut row the resulting eleven profiles are as follows.
For $j=1,2,3,4$, the positive profile $\Pi_j$ has right class $b_j$
equal to alpha, its left class equal to beta ($a$ for $j=1,2$ and $c$
for $j=3,4$, at both repeated occurrences), and all other classes branch.
For each $d\in\{a,b_1,b_2,c,b_3,b_4\}$, the zero profile $Z_d$ has
class $d$ beta and the other classes branch; $Z_*$ has all classes branch.
All class values must still satisfy the original disequalities and image
conditions. The classification follows by applying the disjoint image cases
at the four depth-two parents: an alpha child must be the right child of
$E$, with beta on its left, and distinct classes allow at most one such
collapse. Without a collapse the cut classes are image roots, hence beta
or branch, with at most one beta class.

Put $(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. On every zero profile the
complete predecessor row is $R_0=R_*$. On $\Pi_j$, it is $R_j$: replace
the two sibling holes at $q_jL,q_jR$ by the concrete beta at $q_j$,
canonically restrict the old equality partition to the surviving occurrences,
and retain all surviving disequalities and blocking guards. The other
occurrence of the repeated left class remains a hole. These complete rows
are the original five reader outputs; a root-type summary is insufficient.
This is the image/profile interface exposed in [WTF, Section 1][WTF].

**Definition 1.2 (native apparatus, code and feasibility).** Fix $n\ge6$,
$3\le k\le n-2$, original positions $A=\{s_1<\cdots<s_n\}$ that are
positive integers, and an integer $r\ge0$. Put

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,
\qquad C_B=\sum_{i\in B}c_i,\qquad W=C_{[n]}.
$$

For a branch image $B$ set
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$; alpha, beta and
absent each give zero. Keep the literal original prescription

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in another zero profile}.
\end{cases}
$$

A native preparer has finitely many installed running states, one
source-independent running start, one fixed finite absolute word at each
running state, and four separately specified fixed successors in reply order
alpha, beta, branch, absent. The current counted state is its entire changing
configuration. There are no silent running transitions: each running visit
makes and pays for its query before taking the indicated successor.
The installed set consists of these running states and the $2+r$ distinct
latches, with the running states disjoint from the latches; every successor
belongs to this installed set.
The register is fixed throughout. No free history, clock, counter, phase,
archive, source copy, equality test, inverse evaluation, reset, computed
address or source-dependent selection port is supplied.

Every actual source run must terminate at the original latch
$\widehat e_{\sigma_{A,k}(u)}$. Every installed running state, the two
original distinct latches and all $r$ further mandated distinct latches count,
including unused states. An invocation costs one call and its full absolute
word length. All visits count, including roots, constants, absent replies,
repeated words and work after certification. Sharing, repeats, union cycles
and inconsistent syntactic paths are permitted; termination is required on
every actual fixed input. A terminating stationary run cannot revisit a
running state, since its reply and subsequent suffix would then repeat forever.

For integer bounds, $\mathsf N_{A,k,r}(H,p,\ell)$ means existence of such
a complete correct preparer with at most $H$ installed preparation states
and, simultaneously on every $u\in\mathcal U_*$, at most $p$ calls and
$\ell$ letters. A negative bound is infeasible. The original execution caps
are $p=n+1$, $\ell=W+3$. Preparation ends at the latch $\widehat e_\sigma$;
the separately supplied code-only handoff then enters the original complete
reader entry $e_\sigma$ on this same current register.
Original register binding, same-version row acquisition and authentication,
pre-cut native permission, actual export, complete access isolation, paid
code-only handoff, lawful complete entry and stationary truthful service remain
separate supplied services, as in [WTF, Assumption 1.5][WTF]. Their costs
and physical implementations do not follow from installed-state cardinality.

**Definition 1.3 (Boolean model and feasibility).** A Boolean graph has a
finite installed running set $Q$, two distinct output terminals
$\mathsf0,\mathsf1$, one source-independent running start, one fixed
coordinate $i(q)\in[n]$ and two fixed successors $\delta(q,0),\delta(q,1)$
at each $q\in Q$. Its entire changing configuration is its current state.
A visit reads $\theta_{i(q)}$, pays one query and $c_{i(q)}$ letters,
and follows that successor, with no silent transitions. If its actual visited
running states on $\theta$ are $q_1,\ldots,q_{t_B(\theta)}$, define

$$
J_B(\theta)=\sum_{v=1}^{t_B(\theta)}c_{i(q_v)}.
$$

Thus every visit, including repeated-coordinate and certified work, is paid.
Every installed state counts in $m=|Q|$, including unused states.
Correctness means termination with $\mathbf1_{\{|\theta|\ge k\}}$ on
every Boolean input. Arbitrary sharing, coordinate orders, repeated queries,
paid certified continuations, union cycles and inconsistent graph paths are
allowed; an inconsistent path need not be realizable. There is no auxiliary
changing memory or control port. Write $\mathsf B_{c,k}(m,t,J)$ for
existence with running-state count at most $m$ and both uniform upper bounds
$t_B(\theta)\le t$, $J_B(\theta)\le J$ on every input; negative bounds
are infeasible. The terminals are outside $m$.

Unless other bounds are explicit, the Boolean caps below are $n,W$ on the
same input. Put

$$
K=k,\qquad L=n-k+1,\qquad
V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\},\qquad G=KL.
$$

The unrestricted original question concerns every $n\ge7$,
$4\le k\le n-3$, every original position set $A$ and every $r\ge0$.
The broader structural range above does not replace that intermediate target.

**Theorem 1.4 (exact full-fiber native--Boolean transport).** For every
integer triple $(H,p,\ell)$,

$$
\mathsf N_{A,k,r}(H,p,\ell)
\quad\Longleftrightarrow\quad
\mathsf B_{c,k}(H-4-r,p-1,\ell-3).
\tag{1.1}
$$

This is the uniform feasibility correspondence of [WTF, Theorem 4.1][WTF].
It does not assert pointwise domination of an arbitrary source's old charges
by a normalized preparer. The following proof records the actual-source
suppliers and lower offsets explicitly.

Proof. First construct the lower-test cube. Set $G_0=\langle\beta,\beta\rangle$,
$C_0=G_0$, $C_{v+1}=\langle C_v,\beta\rangle$ and take a comb depth
at least $s_n$. Replace its beta at the prefix-free $w_i$ by $G_0$ exactly
when $\theta_i=1$, producing a branch image $B_\theta$. Choose four fixed
pairwise distinct branch images $D_c,D_1,D_2,D_4$ outside the finite family
of all $B_\theta$. Use these as $x_c,x_{b_1},x_{b_2},x_{b_4}$,
use $x_a=B_\theta$ and $x_{b_3}=\beta$, fill the ordered cut exterior,
and apply the recursive image inverse. This yields an actual finite
$u_\theta\in Z_{b_3}$ with both repeated classes at both occurrences,
disequalities and guards. This is [WTF, Supplier 2.1][WTF], at the scope
exposed there; the inverse is a mathematical construction, not a controller
operation. For every cut occurrence $p$, the occurrence identity is
$r_{\rho u}(pv)=r_{x_{[p]}}(v)$. The only nonconstant words on this cube
are the pairwise disjoint sets

$$
E_i=\{p w_i v:p\in\{LLL,LRL\},\ v\in\{\varepsilon,L,R\}\}.
\tag{1.2}
$$

At their roots, bit zero/one gives beta/branch; at either child it gives
absent/beta. Proper prefixes stay branch and deeper extensions are absent
in both cases, so all other finite words are cube-constant. Every word in
$E_i$ has length at least $c_i$, with equality only at its occurrence roots.

Two offset arguments apply to an arbitrary native competitor, without
assuming it contains the displayed profile front. On each negative cube
input, keep $B_\theta,D_1,D_2,D_4$ and change $x_c$ to beta and
$x_{b_3}$ to alpha. The resulting actual $\Pi_3$ source has code one,
with all selected replies unchanged. On each positive cube input, change
only $x_{b_3}=\beta$ to a fresh branch image distinct from the other classes.
This actual $Z_*$ source has code zero and unchanged selected replies.
Both comparisons preserve the exterior before depth three and all row
constraints. If that cube run queried no distinguishing word, its comparison
source would follow the same fixed successors to the same latch. Correctness
therefore forces a nonselected call of length at least three on that very
cube run. This is a per-input charge, without adding costs across sources.

For installed states, take an actual $Z_c$ source with $x_c=\beta$ and
pairwise distinct branch images elsewhere. Changing only $b_3$ to alpha
produces $\Pi_3$, of opposite code, so some installed query word lies in
$RLR\{L,R\}^*$. Changing instead only $b_4$ to alpha produces $\Pi_4$
and forces an installed word in $RRR\{L,R\}^*$. These disjoint cones
are outside all $E_i$. If $M$ counts all installed selected running states,
including unused ones, adding these two states and the $2+r$ latches gives

$$
M\le H_P-4-r.
\tag{1.3}
$$

Now retain one Boolean running state for each selected native state reached
on at least one cube input, labeled $i$ for a word in $E_i$. Use its
beta/branch or absent/beta edges, according to its word. Bypass
cube-constant states along their unique constant-reply successors, starting
from the old fixed start and after each realized selected edge. A realized
constant chain is finite by actual native termination and ends at a retained
selected state or the appropriate original latch. The initial chain reaches
a selected state because the threshold is nonconstant. For a selected edge
unrealized on every cube input at that state, assign any output terminal.
For each fixed $\theta$, induction follows exactly the selected-state
subsequence on its own $u_\theta$; every edge so used is realized by that
same source. An arbitrarily completed impossible edge never becomes reachable
in this induction. This constructs a total correct terminating graph without
copying, unfolding, ordering or leveling states. Its count and same-input
charges satisfy

$$
m\le M\le H_P-4-r,\qquad
t_B(\theta)+1\le q_P(u_\theta),\qquad
J_B(\theta)+3\le\ell_P(u_\theta).
\tag{1.4}
$$

The selected lengths dominate the original $c_i$ on every visit, and the
extra call and letters come from the mandatory nonselected query on this
same run. Repeated selected visits are retained. Thus projection proves
all three bounds in the forward implication simultaneously.

Conversely, install every Boolean running state, including unused ones, at
$a_{i(q)}$. At each such state install its one successor for branch and,
separately for each of alpha, beta and absent, its zero successor. Replace
the terminals by $\widehat e_0,\widehat e_1$. Add the following two distinct
profile states, start at $D$, and retain every further mandated latch:

| state | literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | Boolean start | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

On every $Z_{b_3}$ source its arbitrary branch image defines one static
indicator vector. The occurrence identity makes every selected native visit
exactly its Boolean test, with the stated four-reply interpretation. This
covers noncomb images and absent selected addresses as well as the cube.
At $D$, alpha is $\Pi_3$, beta is precisely $Z_{b_3}$, and in the branch
case the only remaining code-one profile is $\Pi_4$, detected by alpha at
$T$. All other profiles require zero. Thus the lift is correct and
terminating on the entire original fiber with exactly $m+4+r$ states.
The selected routes have exactly $1+t_B(\theta)$ calls and $3+J_B(\theta)$
letters; the other routes use at most two calls and six letters.

For completeness, every correct Boolean threshold graph has one input
exposing all $n$ coordinates: give one to the first $k-1$ new coordinates
and zero thereafter, retaining old answers on repeats. Before the last
exposure both outputs remain possible. No terminal is correct there and
no actual state can recur. Finiteness forces progress to all coordinates.
Complete this consistent assignment to obtain the actual input. Its charges
are at least $n,W$ on that same run, so Boolean feasibility forces
$t\ge n$, $J\ge W$. The lifted bounds therefore also cover the two-call,
six-letter profile routes. Negative shifted bounds exclude a native witness
by (1.3)--(1.4); negative unshifted bounds are infeasible by definition.
This proves (1.1) for all integer triples. $\square$

**Remark 1.5 (the separate complete reader).** The unchanged reader has
$K_{\rm reader}=8$ installed states: three running states $e_0,Q_2,e_1$
and five distinct complete-row halts. For the supplied fixed order $i_1,i_2$
of $\{1,2\}$ its table is

| state | literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $e_0$ | $q_{i_1}R$ | $H_{i_1}$ | $H_0$ | $Q_2$ | $H_0$ |
| $Q_2$ | $q_{i_2}R$ | $H_{i_2}$ | $H_0$ | $H_0$ | $H_0$ |
| $e_1$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

The halts return the complete $R_0,\ldots,R_4$, including exterior,
occurrences, partition, repetitions, disequalities and guards. Preparation
first terminates at $\widehat e_\sigma$; code-only handoff then enters
literally $e_\sigma$ on the same register. The reader's at most two fresh
calls and six letters, and its eight states, are separate from preparation.
No reader entry is reselected and no reader state is counted as a preparation
latch. This retains [WTF, Convention 1.3][WTF].

## 2. Actual histories and the local separation suppliers

**Definition 2.1 (actual supports and incidence).** A history is an actual
finite prefix ending just before a running query. Its exposed support
$S\subseteq[n]$ consists of coordinates already queried, with assignment
$\eta_S$. Write $h=|\eta_S^{-1}(1)|$ and $z=|\eta_S^{-1}(0)|$.
The history is live exactly when $(h,z)\in V$, so both outputs have
completions. For $p=(h,z)\in V$ put

$$
\begin{aligned}
F_p&=\{q\in Q:\text{an actual live history with counts }p\text{ ends at }q\},\\
\mathcal S_p&=\{S:\text{such a history has support }S\},\\
\mathcal R&=\{(p,S,q):\text{one actual live history witnesses all three}\},\\
b_p&=|F_p|,\qquad a_p=|\mathcal S_p|.
\end{aligned}
$$

A live host of $p$ is a member of $F_p$. A cell is support-ambiguous when
$a_p>1$. These are mathematical indices of actual histories, with no extra
running memory. All statements below use one complete graph at both caps.

**Lemma 2.2 (live freshness and saturation).** Every query at a live
history is fresh. Its prefix has exactly $|S|$ queries and charge $C_S$.
It has negative and positive saturated completions of weights $k-1,k$,
each exposing all $n$ coordinates exactly once and halting immediately
after the last query.

Proof. Certification is monotone under consistent observations, so every
prefix of a live history is live. From a live history with $d=|S|$ and
residual need $Q=k-h$, answer the first $Q-1$ new exposures one and all
remaining new exposures zero. Before the last unread exposure both outputs
remain possible. Repeats retain old values. Correctness forbids a terminal,
and termination forbids revisiting a state; finiteness therefore forces all
$n$ distinct exposures. If a query at any live prefix were a repeat, this
consistent completion would require more than $n$ paid queries, a
contradiction. Hence all live queries and their live prefixes are fresh.
The resulting negative completion uses exactly $n$ queries and $W$ letters;
the query cap forbids any further running visit. Dually give zero to the
first $n-d-Q$ new exposures and one to the rest. It stays live until the
last exposure and gives the positive weight-$k$ completion with the same
exact charges. This restates the saturation argument exposed in [WTF,
Convention 6.1][WTF] and [Third, Lemma 5.2][Third]. It prohibits certified
work only on these saturated completions. $\square$

**Lemma 2.3 (support exclusions and the two-gap rule).** Live histories at
one state cannot have properly nested supports. Equal supports force equal
hits; different supports with equal hits cannot share a state. If different
count pairs share a state, orient them as $(h,z),(g,w)$ with $h<g$; then

$$
g-h\ge2,\qquad z-w\ge2.
\tag{2.1}
$$

For incomparable supports write

$$
I=S\cap T,\quad X=S\setminus T,\quad Y=T\setminus S,\quad
U=[n]\setminus(S\cup T),\qquad a=|X|,\ b=|Y|,\ u=|U|,
$$

and $Q=k-h$, $V'=k-g$, $\Delta=g-h=Q-V'$. If the old $X$ bits
are all zero, then $a\le b$ and $C_X\le C_Y$. If the old $Y$ bits
are all one, then $b\le a$ and $C_Y\le C_X$.

Proof. These are the local exclusions of [PE, Lemma 4.1 and Theorem
3.1][PE] and [WTF, Theorem 9.1][WTF]. We record the argument so that
neither graph-path realizability nor nonresonance is implicit.
If $S\subseteq T$ and $b=|T\setminus S|$, a negative saturated suffix
from $T$ queries only outside $T$ and halts. Replay it from $S$, putting
ones on $T\setminus S$ and using the same outside assignment. Determinism
from the common state makes the suffix identical, regardless of old
agreements on $S$. Correctness gives $h+b+(k-1-g)\le k-1$.
The positive saturated suffix with zeros on $T\setminus S$ similarly
gives $h+(k-g)\ge k$. Thus $h+b\le g\le h$, so $b=0$ and $h=g$.
Reverse containment is symmetric.

For incomparable $S,T$, the clipped integer intervals

$$
[0,u]\cap[Q-b,Q-1],\qquad [0,u]\cap[V'-a,V'-1]
\tag{2.2}
$$

are nonempty by liveness. They are disjoint: otherwise assign $U$ a common
weight in their intersection. Even after all $U$ is read, each history has
a nonconstant threshold on its private unread block. Every earlier prefix
is live too, so a common next query must be fresh for both, hence in the
as yet unread part of $U$. A terminal is impossible, and after $U$ is
exhausted there is no such fresh query. Each continuation is consistent
with its own incoming history; the old $I$ assignments need not agree.
If $h=g$, the intervals have the same upper endpoint, contradiction.
For $h<g$, their disjointness and $Q>V'$ put the second strictly below
the first, giving

$$
u\ge1,\qquad Q\ge b+1,\qquad 1\le V'\le u,\qquad\Delta\ge b.
\tag{2.3}
$$

If old $X$ is zero, complete $T$ with $X$ zero, first $V'-1$ fresh
$U$ replies one and the rest zero. This remains live until all of $X\cup U$
is read: while those ones are pending there are too few zeros for a negative
certificate, and afterwards every remaining bit is needed. It is a saturated
negative suffix with no further query. Replay it from $S$ with any $Y$
assignment. Its weight is at most $h+b+V'-1\le k-1$, and its charges
are $n+a-b$ and $W+C_X-C_Y$. Its own two caps give the claimed first
inequalities. Dually, when old $Y$ is one, complete $S$ with $Y$ one,
first $b+u-Q$ new $U$ replies zero and the rest one. The saturated positive
suffix on $Y\cup U$ replays from $T$, with weight at least
$g+Q-b\ge k$ and charges $n+b-a$, $W+C_Y-C_X$. Its caps give the
reverse inequalities. All repeated private queries in these replays are paid.

It remains to prove the two gaps. Let $\xi,\eta$ count the old ones on
$X,Y$ respectively, and put

$$
\delta_I=\Delta+\xi-\eta=(\Delta-b)+\xi+(b-\eta)\ge0,
\qquad \lambda=b+u-Q+1.
\tag{2.4}
$$

When $\delta_I>0$, the conflict band

$$
\max(0,V'-\xi)\le t\le\min(u,Q-\eta-1)
\tag{2.5}
$$

contains an integer: the outer endpoints are feasible by (2.3) and
$\eta\le b$, and $V'-\xi\le Q-\eta-1$. Choose any assignment on $U$
of that weight. On both completions use old $S$ values on $X$, old $T$
values on $Y$, and this same $U$ assignment; on $I$ retain each history's
own values. The resulting weights are $h+\eta+t\le k-1$ and
$g+\xi+t\ge k$. The common state sequence must eventually first receive
different replies, at an old coordinate $i\in I$. Before that invocation
both histories must be certified: querying this old coordinate while either
was live would violate Lemma 2.2. The negative certificate needs $\lambda$
new zeros, first exposed in $Y_0\cup U_0$, and the positive certificate
needs $V'$ new ones, first exposed in $X_1\cup U_1$. These are disjoint
coordinate sets on the common suffix; subscripts denote values in the
chosen assignments. Together with the discriminator they
give, separately on the two complete actual runs,

$$
|S|+\lambda+V'+1\le n,\qquad
|T|+\lambda+V'+1\le n,
$$

and, if $A_-,A_+$ are the chosen certificate sets,

$$
C_S+C_{A_-}+C_{A_+}+c_i\le W,\qquad
C_T+C_{A_-}+C_{A_+}+c_i\le W.
$$

Thus

$$
\lambda+V'+1\le u+\min(a,b),\qquad
C_{A_-}+C_{A_+}+c_i\le C_U+\min(C_X,C_Y).
\tag{2.6}
$$

No budgets of distinct inputs have been added. The discriminator state is
absent from either incoming path, including its endpoint, by live freshness
there and no-revisit on the completed runs. This does not exclude its being
live on another input. Substituting
$\lambda+V'+1=b+u-\Delta+2$ in (2.6) gives
$\Delta\ge2+\max(0,b-a)$ and
$z-w=\Delta+a-b\ge2$. If $\delta_I=0$, (2.4) forces
$\Delta=b$, $\xi=0$, $\eta=b$. Both private-polarity inequalities apply,
so $a=b=\Delta$ and $C_X=C_Y$. Nonempty disjoint private sets cannot
both be singletons of equal cost, since the individual $c_i$ are distinct.
Hence $a=b=\Delta\ge2$, also giving both gaps. Equal sums of larger
subsets remain allowed. This completes the proof. $\square$

**Lemma 2.4 (actual incidence and fixed successors).** For every $p=(h,z)\in V$,
$F_p$ and $\mathcal S_p$ are nonempty; their supports have size $h+z$
and their histories have exactly $h+z$ queries. At fixed $(p,q)$ there is
at most one support, so $b_p\ge a_p\ge1$. If $(p,S,q)\in\mathcal R$,
then $i(q)\notin S$, and whenever
$p_\varepsilon=(h+\varepsilon,z+1-\varepsilon)\in V$,

$$
(p_\varepsilon,S\cup\{i(q)\},\delta(q,\varepsilon))\in\mathcal R.
\tag{2.7}
$$

Every positive-depth live occurrence has an actual live predecessor.
Axis cells have one support and host: $a_{0,z}=b_{0,z}=a_{h,0}=b_{h,0}=1$.

Proof. Give $h$ successive fresh ones and $z$ fresh zeros. All prefixes
stay live, cannot halt and query fresh coordinates by Lemma 2.2, so they
are realized by consistent completions. Freshness gives sizes and exact
charges. Two different supports at fixed $p,q$ have equal hits, excluded
by the different-support/equal-hit part of Lemma 2.3. Each host therefore
determines one support at that cell, and every support has a host, giving
the surjection and $b_p\ge a_p$. Either reply at an unread coordinate
has completions following the old history; when its child counts are live,
its fixed successor must be running and witnesses (2.7). Earlier prefixes
are live, giving predecessors. The all-zero and all-one deterministic
reply spines give the axis claim. This is [SI, Theorem 2.2][SI], without
a unique-host premise. $\square$

## 3. Credited incidence identity and compatible block localization

**Definition 3.1 (incidence, cuts and maximal ambiguity blocks).** Put

$$
\begin{aligned}
Q_{\rm live}&=\bigcup_{p\in V}F_p,&
\nu&=|Q\setminus Q_{\rm live}|,\\
d(q)&=|\{p\in V:q\in F_p\}|\quad(q\in Q_{\rm live}),&
D&=\sum_{q\in Q_{\rm live}}(d(q)-1),\\
E&=\sum_{p\in V}(b_p-1).&&
\end{aligned}
$$

A depth $d\in\{0,\ldots,n-1\}$ is ambiguous if some cell at that depth
has $a_p>1$. Let $\mathcal C$ be the unambiguous depths together with
the formal endpoint $n$. For $t\in\mathcal C$ write $T_t$ for its
common support, proved below, and set $T_n=[n]$. There is no live cell
at $n$. The index set $\mathcal C$ need not contain every depth.
Let $B=[\ell,r]$ run over maximal nonempty consecutive ambiguous-depth
blocks. Its length $|B|=r-\ell+1$ counts interior depths. Define

$$
\begin{aligned}
E_B&=\sum_{p:\,h+z\in B}(b_p-1),\\
D_B&=\sum_{q\in Q}\max\bigl(|\{p:\,h+z\in B,\ q\in F_p\}|-1,0\bigr),\\
E_{\rm reg}&=\sum_{p:\,h+z\in\mathcal C\setminus\{n\}}(b_p-1),\\
b_{\rm short}&=|\{B:1\le |B|\le2\}|.
\end{aligned}
$$

Here $\nu$ counts every installed state never live, including unused and
exclusively certified states. A state live somewhere stays in $Q_{\rm live}$
even if other inputs use it after certification. In [SI, Section 9][SI],
our nonempty $B=[\ell,r]$ is the open cut interval $(\ell-1,r+1)$,
whose boundary spacing is $|B|+1$; SI also includes empty interiors.
Our $E_{\rm reg}$ is SI's cut excess. Thus a short block here corresponds
to spacing two or three there, not to an independent kind of table.

**Theorem 3.2 (exact identity on one graph).** For every qualifying graph,

$$
m-G=E-D+\nu.
\tag{3.1}
$$

Proof. The finite incidence relation gives

$$
G+E=\sum_{p\in V}b_p
=\sum_{q\in Q_{\rm live}}d(q)=|Q_{\rm live}|+D.
$$

Subtract using $m=|Q_{\rm live}|+\nu$. This is precisely the identity
of [SI, Theorem 5.2, (SI.19)][SI], with a single symbol $\nu$ for the
never-live count. Terminals are outside $m$. $\square$

**Theorem 3.3 (common supports and compatible block localization).**
For each $t\in\mathcal C\setminus\{n\}$ all cells at depth $t$ have
one common support $T_t$. The canonical chain is indexed only by
$\mathcal C$:

$$
T_0=\varnothing,\qquad T_n=[n],\qquad |T_t|=t\ (t\in\mathcal C),
\qquad T_s\subsetneq T_t\quad(s<t,\ s,t\in\mathcal C).
\tag{3.2}
$$

At each such cut $t$, supports at earlier live depths are contained in
$T_t$ and those at later live depths contain $T_t$. Every state with
multiple count-cell incidences lies entirely in one ambiguity block.
Consequently

$$
D=\sum_BD_B,\qquad E=E_{\rm reg}+\sum_BE_B,\qquad
m-G=\nu+E_{\rm reg}+\sum_B(E_B-D_B).
\tag{3.3}
$$

The stronger fixed-vector bookkeeping of [SI, Theorem 9.3][SI] also holds.
For consecutive cuts $a<b$ in $\mathcal C$, let $I=(a,b)$,
$X_I=T_b\setminus T_a$, and $V_I=\{p\in V:a<h+z<b\}$.
Put $E_I=\sum_{p\in V_I}(b_p-1)$, define $D_I$ by the same restricted
incidence formula as $D_B$, and put

$$
\begin{aligned}
m_i&=|\{q\in Q:i(q)=i\}|,&m(X_I)&=\sum_{i\in X_I}m_i,\\
E_a&=\sum_{p:\,h+z=a}(b_p-1),&g_I&=|V_a|+|V_I|,\\
\nu_I&=|\{q\in Q\setminus Q_{\rm live}:i(q)\in X_I\}|,
&V_a&=\{p\in V:h+z=a\}.
\end{aligned}
$$

Then the $X_I$ partition $[n]$ on this same original installed vector, and

$$
m(X_I)-g_I=E_a+E_I-D_I+\nu_I,\qquad
\sum_I\nu_I=\nu.
\tag{3.4}
$$

Proof. Adjacent cells $(h,z),(h+1,z-1)$ on one depth diagonal have the
common live parent $(h,z-1)$. Fork one actual parent history with the two
replies; (2.7) gives children with the same support. If their support
families are singleton, these singleton supports coincide. The admissible
hit counts on a diagonal form an integer interval, so this connects that
whole diagonal; a one-cell diagonal is immediate. No singleton hypothesis
on the parents is needed. This is the local diagonal argument of [SI,
Theorem 4.1][SI].

Every live history extends to any prescribed later depth at most $n-1$:
unless at the live corner $(K-1,L-1)$, at least one reply has live child
counts, and (2.7) makes it an actual fresh extension. Iterate, choosing a
completion of the resulting consistent finite assignment. Extending to a
later cut gives containment; taking the actual ancestor at an earlier cut
gives the reverse envelope. Sizes give strictness. At $n$ only containment
in $[n]$ is asserted, with no live depth-$n$ extension. This proves (3.2).
For $B=[\ell,r]$ every live support at a depth in $B$ lies between
$T_{\ell-1}$ and $T_{r+1}$; its next query lies in
$T_{r+1}\setminus S$. If $r+1<n$, extend through that live cut; if
$r+1=n$, use freshness.

At a cut all supports coincide, so unequal hits exclude a common host.
Across a cut the support envelopes make earlier and later supports properly
nested, also excluding sharing. Hence every multiple incidence is confined
to one block. Partitioning incidences proves (3.3). These are the cuts and
localization already proved in [SI, Lemma 9.2 and Theorem 9.3][SI]. In
particular, for consecutive cuts $a<b$, every live host at depth
$a\le d<b$ queries a label in $X_I$: if $b<n$, extend through that
cut, and if $b=n$, use freshness. The strict cut chain partitions $[n]$
by the $X_I$, so one installed state cannot be live in two such half-open
depth ranges. Within a range, cut hosts are disjoint from the interior
hosts and from one another. The cut pool therefore has size $|V_a|+E_a$;
the interior pool has size $|V_I|+E_I-D_I$ by the restricted double count.
Every state labeled in $X_I$ is either in these two pools or never live;
a live state from another range would have its label in a disjoint block.
Adding the three pools proves (3.4), including empty interiors. The fixed
labels partition the never-live states too, proving the last sum. This
retains SI's stronger bookkeeping, with its full original multiplicity vector.
No independent table is substituted for any block here. Actual certified
traffic need not follow these live envelopes and is still fully charged.
$\square$

## 4. Strict positive compensation on short blocks

**Theorem 4.1 (one ambiguous depth).** If $B=[\ell,\ell]$ is a maximal
ambiguity block, then $D_B=0$ and $E_B\ge1$.

Proof. Put $T_-=T_{\ell-1}$, $T_+=T_{\ell+1}$, using $T_n=[n]$
at the endpoint. Since depth zero is unambiguous, $\ell\ge1$.
Every support at depth $\ell$ adds one of the two coordinates in
$C=T_+\setminus T_-$. Its next fixed label is the other coordinate:
a live child stays inside $T_+$, or at depth $n-1$ freshness leaves
only that unread coordinate. Distinct supports therefore demand different
fixed labels and cannot share a state. Equal supports in distinct cells
have unequal hits and cannot share by Lemma 2.3. Thus $D_B=0$.
Ambiguity gives a cell with $a_p\ge2$, and Lemma 2.4 gives $b_p\ge2$,
so $E_B\ge1$. The no-sharing argument is the spacing-two case of [SI,
Theorem 9.4][SI]; retaining the positive ambiguity excess gives the strict
unit asserted here. $\square$

**Theorem 4.2 (two ambiguous depths).** If $B=[\ell,\ell+1]$ is a maximal
ambiguity block, then

$$
E_B\ge\max(2,2D_B-1),\qquad E_B-D_B\ge1.
\tag{4.1}
$$

Each shared state has exactly two cell incidences, both at depth $\ell$,
and those cells must be the admissible pair

$$
p_-=(\ell-L+1,L-1),\qquad
p_+=(K-1,\ell-K+1).
\tag{4.2}
$$

If either is inadmissible or the two-gap rule fails, there is no sharing.
In particular $D_B=0$ if this block ends at depth $n-1$.

Proof. Put $T_-=T_{\ell-1}$, $T_+=T_{\ell+2}$ and
$C=T_+\setminus T_-$; $|C|=3$, including at the formal endpoint.
At depth $\ell+1$, a support adds two coordinates of $C$ and the next
query is the omitted third. Different supports demand different labels;
equal supports in distinct cells cannot share. Thus no state there hosts
two cells. An earlier support adds one coordinate $x$. If a later support
contains $x$, they are properly nested. Otherwise its forced next label
is $x$, already read by the earlier history. Live freshness excludes this
common state too. Hence there is no cross-depth sharing.

At depth $\ell$, each hosted cell has a nonempty live-reply set, since
$\ell\le n-2$. If distinct hosted cells had a common live reply, their
actual fixed successor would host the two distinct child cells at depth
$\ell+1$, just excluded. Their nonempty live-reply sets must therefore
be disjoint subsets of $\{0,1\}$. A shared state has exactly two cells,
one with only a live one reply ($z=L-1$), and the other with only a live
zero reply ($h=K-1$). This gives (4.2); there can be no third hosted cell.
This is the classification from [SI, Theorem 9.4][SI]. It makes no claim
that a certified child halts or that this pair is actually shared.

Let $s$ count these shared states. Each has exactly two incidences and
all other hosts have one, so $D_B=s$. Both extreme cells have at least
$s$ hosts, and their diagonal excess is at least $2s-2$. Independently,
maximality of this two-depth block means that each of its depths really
is ambiguous. Each diagonal thus has excess at least one, by $b_p\ge a_p$.
For $s\ge1$ the first diagonal has excess at least
$\max(1,2s-2)$ and the last at least one; for $s=0$ both still have
excess at least one. Consequently
$E_B\ge\max(2,2s-1)$. If $s=0,1,2$, this implies respectively
$E_B-s\ge2,1,1$; for $s\ge3$ it implies $E_B-s\ge s-1\ge2$.
This proves the strict unit for every case. No host from another block is
charged. If $\ell+1=n-1$, then $\ell=n-2=K+L-3$, and (4.2) has
hit gap one. Lemma 2.3 forbids sharing, so $s=0$ there. $\square$

**Corollary 4.3 (retained increment over short nonnegative compensation).**
Every nonempty maximal ambiguity block with $|B|\le2$ satisfies
$E_B-D_B\ge1$. Current [SI, Theorem 9.4][SI] states $E_B-D_B\ge0$
for the corresponding spacing-two and spacing-three intervals. Its
classification and fixed-successor proof are retained; the strict bound here
uses the positive excess on every internal ambiguous diagonal, including
the last diagonal in the spacing-three case. Current SI Section 10 advances
the surrounding compensation and residual frontier, but states no strict
unit for each such nonempty span-two/three interval. Its early-ending
no-sharing result does imply positive excess there; the bound here also
covers the late-ending short intervals without that hypothesis. This is
the additional bounded inequality retained relative to the supplied SI10
statements, with no worldwide priority assertion or independent separator
charge. $\square$

## 5. Short-block slack and the credited current late-gap frontier

**Theorem 5.1 (short-block slack on one complete graph).** Every graph at
both original Boolean caps satisfies

$$
m-G\ge\nu+E_{\rm reg}+b_{\rm short}
 +\sum_{\substack{B\text{ maximal}\ |B|\ge3}}(E_B-D_B).
\tag{5.1}
$$

If there are no three consecutive ambiguous depths, then

$$
m\ge G+\nu+E_{\rm reg}+b_{\rm short}.
\tag{5.2}
$$

The minimum in this class is exactly $G$, attained by the fixed-order
grid. If $m<G$, the combined long-block deficit satisfies the sharper
necessary inequality

$$
\sum_{|B|\ge3}(D_B-E_B)
>\nu+E_{\rm reg}+\sum_{|B|\le2}(E_B-D_B)
\ge\nu+E_{\rm reg}+b_{\rm short}.
\tag{5.3}
$$

In particular some long block has

$$
D_B\ge E_B+1\ge |B|+1\ge4.
\tag{5.4}
$$

For this fixed graph, $m\ge G$ is equivalent to

$$
\sum_{|B|\ge3}(D_B-E_B)
\le\nu+E_{\rm reg}+\sum_{|B|\le2}(E_B-D_B).
\tag{5.5}
$$

Proof. Substitute Corollary 4.3 in the exact identity (3.3). Every
ambiguous depth contributes at least one to its block's $E_B$ because
some $a_p\ge2$ and $b_p\ge a_p$. This proves (5.1)--(5.4), including
integer strictness. Rearranging (3.3) gives (5.5). These are simultaneous
incidence statements on the same installed graph.

For the upper, install states $(h,z)\in V$, label each by coordinate
$h+z+1$, advance its counts on the reply, and terminate at zero after
$L$ zeros or at one after $K$ ones. Every path reads a prefix of the fixed
order, computes threshold, and pays at most $n,W$. A path with $K-1$
ones and $L-1$ zeros before its last query attains both caps on the same
input. Every cell is realized, has one support and one host, and there
are $G$ states. This is the existing grid upper exposed in [SI, Corollary
9.5][SI] and [CP][CP]. It has $\nu=E_{\rm reg}=b_{\rm short}=0$,
so it attains the minimum.

The conditional minimum and the exact residual comparison (5.5) already
belong to [SI, Corollary 9.5 and Proposition 9.6][SI]. The new information
in (5.1)--(5.3) is the explicit short-block unit of slack. A positive local
long deficit is necessary, not sufficient, for a saving: it must outweigh
all other terms. Four duplicate incidence units need not represent four
different states. A separator live elsewhere is in $Q_{\rm live}$ and
cannot automatically be charged to $\nu$. Proving $D_B\le E_B$ for each
long block would suffice, but is stronger than (5.5). The results below
prove compensation for some of those long blocks; compensation for every
remaining late gap of span at least five stays unproved.
$\square$

Theorem 5.1 remains valid, but its length-three-or-more block sum is a
coarser partition than the current frontier. The following deductions of
[SI, Section 10][SI] resolve every three-depth ambiguity block and every
early-ending interval, without restricting other intervals of the graph.

**Lemma 5.2 (credited right-cut separation).** Let $I=(a,b)$ be any
consecutive-cut interval of Theorem 3.3, of span $\beta_I=b-a$.
Write $Q_I=\bigcup_{p\in V_I}F_p$. Every host at depth $b-1$
hosts no other cell in $V_I$. If distinct cells $(h,z),(g,w)\in V_I$
share a host, orient them by $h<g$. Then

$$
g-h,\ z-w\ \ge\max(2,n-b+1).
\tag{5.6}
$$

Put $d_*=\min(K,L)$ and $e_*=\max(K,L)$. If $b\le e_*$,
then $D_I=0$, irrespective of the interval's span.

Proof. This is [SI, Lemma 10.2][SI], using the actual envelopes above.
At a depth-$b-1$ occurrence with support $S$ and host $q$, freshness
and the right envelope give $S=T_b\setminus\{i(q)\}$. Any other
occurrence of $q$ inside $I$ has support contained in this same set.
At an earlier depth it is properly nested, and at the same depth it has
the same support with unequal hits. Lemma 2.3 excludes both possibilities.
The argument includes $b=n$, where $T_n=[n]$ is only a formal boundary.

Lemma 2.3 gives the two gaps at least two. Suppose their minimum is at
most $n-b$. Set

$$
M=\max(h+z,g+w),\quad t=b-1-M,\quad
A_1=K-1-g,\quad A_0=L-1-z.
$$

All three capacities are nonnegative, and
$g+z-M=\min(g-h,z-w)$ implies
$A_1+A_0-t=n-b-\min(g-h,z-w)\ge0$.
Choose $t_1\le A_1,t_0\le A_0$ nonnegative with $t_1+t_0=t$.
Append the same word $1^{t_1}0^{t_0}$ to both actual histories.
Every intermediate count is live for both, since its counts are bounded
by their final live counts. Inductively the common state's fixed label
is fresh for both histories, each requested reply has an actual completion,
and their one fixed successor is again common. Thus these are actual
paired live extensions, even if their old assignments disagree.
At their ends the larger depth is $b-1$, the cell differences persist,
and both depths remain internal to $I$. This contradicts last-layer
exclusivity. The case $t=0$ is that same contradiction immediately.
Hence both integer gaps exceed $n-b$, proving (5.6).

If $b\le e_*$, then $n-b+1\ge d_*$. One of the two live count
ranges has diameter $d_*-1$, so no such shared pair exists. No arbitrary
syntactic path was assumed actual in this proof. $\square$

**Lemma 5.3 (credited span-four sharing classification).** Suppose
$I=(a,a+4)$ and put $d=a+1$. Define the following formal cells:

$$
\begin{aligned}
\alpha&=d-L+1,&\gamma&=K-1,\\
A&=(\alpha,L-1),&C&=(\alpha+1,L-2),\\
Y&=(K-2,d-K+2),&Z&=(K-1,d-K+1),\\
U&=(\alpha+1,L-1),&V'&=(K-1,d-K+2).
\end{aligned}
\tag{5.7}
$$

The first four have depth $d$ and the last two depth $d+1$.
Every state shared by distinct cells of $V_I$ hosts exactly two cells,
and its pair is among

$$
AZ,\quad CZ,\quad AY,\quad UV',\quad AV',\quad ZU.
\tag{5.8}
$$

Omit invalid cells, coincident endpoints and pairs failing Lemma 2.3's
two-gap rule. The depth $d+2$ is exclusive. Every $CZ$ host has its
actual zero successor at a shared $UV'$ host; every $AY$ host has its
actual one successor at a shared $UV'$ host. No successor injectivity
is asserted.

Proof. This is [SI, Lemma 10.3][SI]. The final internal depth $d+2$
is exclusive by Lemma 5.2. At depth $d+1$, two hosted cells cannot
have a common live reply: it would share their fixed successor at depth
$d+2$. Their nonempty live-reply sets must be opposite singletons,
forcing $UV'$. A pair across depths $d,d+1$ likewise cannot have a
common live reply, since its successor would share with the exclusive
last layer. Opposite singletons force $AV'$ or $ZU$.
At depth $d$, opposite singleton live replies give $AZ$. A common zero
reply instead gives $UV'$ children, whose parents are $C,Z$; a common
one gives parents $A,Y$. The same actual forks give the asserted
successors. Each of these earlier depths has a live reply; the possible
corner with none lies only on the last layer.

To exclude three incidences, put $H=\gamma-\alpha=n-1-d\ge2$.
If $H=2$, the two-gap rule removes all displayed pairs except $AZ$,
including the case $C=Y$. If $H\ge3$, the six formal cells are
distinct; among the first-depth cells the allowed pairs form the path
$C-Z-A-Y$, with no triple of mutually allowable pairs. There are at
most two second-depth cells, $U,V'$, with opposite singleton replies.
An earlier cell sharing with both would need a nonempty reply set disjoint
from both singletons, which is impossible. Two earlier cells sharing
with one later cell would both need the same opposite singleton; at
one depth only one cell has that singleton live-reply set. The earlier
cells would coincide. Last-layer exclusivity excludes all remaining
triples. Removing invalid cells or forbidden pairs cannot introduce a
triple. $\square$

**Theorem 5.4 (credited span-four compensation).** Every consecutive
span-four interval satisfies

$$
D_I\le E_I,\qquad |Q_I|\ge |V_I|.
\tag{5.9}
$$

Proof. We give the full compensation argument of [SI, Theorem 10.4][SI].
Let $e_1,e_2,e_3$ be the excess-host sums at its three internal depths.
Each depth is ambiguous because the cuts are consecutive. Thus
$e_j\ge1$ and $E_I\ge3$. By Lemma 5.3, if $s$ states are shared,
then $D_I=s$. View each shared state as an edge between its two cells
in (5.8), retaining parallel edges for distinct states. At most six cells
are incident. If their number is $v$, their host counts dominate their
degrees, so their total excess is at least $2s-v$. The last layer is
disjoint from these cells and has excess at least one. Hence

$$
E_I\ge2s-v+1\ge2s-5.
\tag{5.10}
$$

If $E_I<s$, integer strictness with $E_I\ge3$ and (5.10) forces
$s=4,E_I=3,v=6$. Therefore all six cells are distinct and valid,
each $e_j=1$, every incident host count equals its degree, and every
other cell on the first two layers has exactly one host. Any boundary
deletion or coincidence has already made this deficit impossible.

Write $x,y,z_*,u_*,v_*,w_*$ for the multiplicities of
$CZ,AY,UV',AZ,AV',ZU$. Since $C,Y$ are incident pendant
vertices, $x,y\ge1$. Their actual successors force $z_*\ge1$,
without any injectivity assumption. Counting degrees on the two layers
gives

$$
\begin{aligned}
x+y+z_*+u_*+v_*+w_*&=4,\\
2x+2y+2u_*+v_*+w_*-4&=1,\\
2z_*+v_*+w_*-2&=1.
\end{aligned}
\tag{5.11}
$$

The last equation forces $z_*=1,v_*+w_*=1$. The middle then
forces $x=y=1,u_*=0$. If $v_*=1$, only $A$ on the first
diagonal has multiple hosts. Every cell from $C$ through $Z$ has
one host, hence one support. Consecutive such cells have equal supports
by an actual parent fork, as in Theorem 3.3; the parent itself need
not have a unique support. The live diagonal is an integer interval,
so $C,Z$ have equal supports. Their shared $CZ$ state contradicts
equal-support/unequal-hit exclusion. If $w_*=1$, only $Z$ has
multiple hosts on that diagonal; the same argument from $A$ through
$Y$ contradicts the shared $AY$ state. These exhaust the possibilities,
so $E_I\ge s=D_I$. Restricted incidence counting gives
$|Q_I|=|V_I|+E_I-D_I$, proving the second assertion. All edges
and successors here are actual incidences of the one original graph;
certified traffic is still paid and unrestricted. $\square$

**Corollary 5.5 (credited terminal span-four margin).** If $(n-4,n)$
is consecutive, then $E_I-D_I\ge2$. The only possible shared pair
is $(K-3,L-1),(K-1,L-3)$. No attainment of this margin is asserted.

Proof. This is [SI, Corollary 10.5][SI]. Here $d=n-3,H=2$ in
Lemma 5.3, so only $AZ$ survives the two-gap rule. If $s$ states
share, then $D_I=s$ and the first diagonal has excess at least
$\max(1,2s-2)$; the other two have at least one each. Consequently
$E_I-D_I\ge2+\max(1,2s-2)-s\ge2$: the bound is three at
$s=0$, two at $s=1$, and $s\ge2$ for $s\ge2$. $\square$

**Theorem 5.6 (strict short-block slack at the current late-gap frontier).**
Let $\mathcal I$ be the consecutive-cut intervals, including empty
interiors, and define

$$
\begin{aligned}
\mathcal L_*&=\{I=(a,b)\in\mathcal I:b-a\ge5,\ b>e_*\},\\
\mathcal A_*&=\mathcal I\setminus\mathcal L_*,\\
\mathcal S&=\{I\in\mathcal I:\beta_I=2\text{ or }3\},\\
\tau&=\mathbf1_{\{(n-4,n)\in\mathcal I\}}.
\end{aligned}
\tag{5.12}
$$

Thus $|\mathcal S|=b_{\rm short}$. Define, with an absent terminal
interval contributing zero,

$$
\begin{aligned}
\Xi={}&\sum_{I\in\mathcal S}(E_I-D_I-1)\\
&+\begin{cases}E_{(n-4,n)}-D_{(n-4,n)}-2,&\tau=1,\\0,&\tau=0,\end{cases}\\
&+\sum_{I\in\mathcal A_*\setminus(\mathcal S\cup\{(n-4,n)\})}
 (E_I-D_I).
\end{aligned}
$$

Every summand defining $\Xi$ is nonnegative, and on the same graph

$$
m-G=\nu+E_{\rm reg}+b_{\rm short}+2\tau+\Xi
 -\sum_{I\in\mathcal L_*}(D_I-E_I).
\tag{5.13}
$$

In particular, if every gap ending after $e_*$ has span at most four,
then

$$
m\ge G+\nu+E_{\rm reg}+b_{\rm short}+2\tau.
\tag{5.14}
$$

This enlarged qualified class, and its subclass with every span at most
four, have exact minimum $G$. The terminal-gap conditional bound has no
attainment assertion. For an arbitrary original graph, $m\ge G$ is
equivalent to the still unresolved inequality

$$
\sum_{I\in\mathcal L_*}(D_I-E_I)
\le\nu+E_{\rm reg}+\sum_{I\in\mathcal A_*}(E_I-D_I)
=\nu+E_{\rm reg}+b_{\rm short}+2\tau+\Xi.
\tag{5.15}
$$

A strict saving reverses this inequality strictly. It therefore requires
some $I=(a,b)\in\mathcal L_*$ with

$$
D_I>E_I,\quad |Q_I|<|V_I|,\quad
D_I\ge E_I+1\ge\beta_I\ge5.
\tag{5.16}
$$

There are at least four consecutive ambiguous depths in this interval,
and $b\in\{e_*+1,\ldots,n\}$, with $d_*-1$ possible right
endpoints. These are necessary conditions, not a construction of a saving.

Proof. For a span-one interval the interior is empty and $E_I=D_I=0$.
Spans two and three are Theorems 4.1--4.2; span four is Theorem 5.4.
Every remaining interval in $\mathcal A_*$ ends at $b\le e_*$,
so $D_I=0$ by Lemma 5.2. Thus all safe contributions $E_I-D_I$
are nonnegative. For each early-ending nonempty gap this reasoning also
gives $E_I-D_I=E_I\ge\beta_I-1$. The short intervals and the
terminal span-four interval are disjoint members of the same interval
partition. Subtract their respective proved units and two-unit margin,
leaving exactly the nonnegative terms defining $\Xi$. Theorem 3.3
then gives (5.13), hence (5.14)--(5.15). No interval contribution has
been charged twice and no separate block implementation has been used.

If $m<G$, the sum on the left of (5.15) exceeds its nonnegative right
side, so some late gap has $D_I>E_I$. Every one of its $\beta_I-1$
internal depths is ambiguous and contributes at least one to $E_I$.
Integer strictness and the restricted incidence identity prove (5.16).
The endpoint count is $n-e_*=d_*-1$. Duplicate-incidence units need
not be distinct states. The fixed-order grid from Theorem 5.1 has every
depth a cut, belongs to both qualified classes, and attains $G$ at both
caps, proving their exact minima.

The enlarged class, its minima, the terminal two-unit margin and the
late-span-at-least-five necessity are credited to [SI, Corollaries
10.5--10.6 and Proposition 10.9][SI]. In particular (5.15) before its
explicit slack expansion is SI's current global sum. The additional
short-block content is the $b_{\rm short}$ contribution proved in
Section 4, which SI's stated span-two/three estimates leave nonnegative.
Keeping that contribution together with the credited terminal margin is
a deduction on one actual installed vector. Neither the bare existence
of a late gap nor a positive local deficit settles the global sum.
$\square$

**Proposition 5.7 (credited strict enlargement by span four).** If
$\min(K,L)\ge4$, a complete original graph at both caps can have
consecutive cuts $1,5$.

Proof. This is [SI, Proposition 10.7][SI]. Use a fully unfolded finite
tree with distinct internal vertices. Query coordinate $1$ first, then
$2,3,4,5$ in its zero subtree and $3,4,5,2$ in its one subtree.
Finish all other coordinates in one fixed order and attach the threshold
output at depth $n$. Each node has its fixed label and successors;
every node is counted. Every input pays exactly $n,W$, including any
certified suffix. At depths two, three and four, the two first-reply
branches respectively have supports
$\{1,2\},\{1,3\}$;
$\{1,2,3\},\{1,3,4\}$; and
$\{1,2,3,4\},\{1,3,4,5\}$.
In either branch choose total counts $(1,1)$, $(2,1)$ and $(2,2)$
at these respective depths. Such replies exist with either fixed first
reply, remain live since $K,L\ge4$, and give the same cell with
different supports. These depths are ambiguous. All depth-one supports
are $\{1\}$, and all depth-five supports are $\{1,2,3,4,5\}$;
a live depth-five history with two ones and three zeros exists.
Thus $1,5$ are consecutive cuts. Every later depth also has one support,
so all gaps have span at most four. This witnesses strict enlargement of
the span-at-most-three class, without asserting a saving, a minimum in
the terminal-gap subclass, or a new result of this volume. $\square$

## 6. Credited fixed-prefix applications and their strict slack

**Definition 6.1 (one actual residual cone).** Fix one actual live prefix,
its support $S_0$, its particular assignment $\eta_{S_0}$, its endpoint,
and its $h_0$ exposed ones. Put

$$
R=[n]\setminus S_0,\qquad N=|R|,\qquad q=k-h_0.
$$

Every completion in this cone retains this same old assignment and follows
this same prefix. Different actual prefixes are not identified by this
notation.

**Theorem 6.2 (boundary residual depth rigidity).** Suppose $N\ge6$ and
$q\in\{3,N-2\}$. Two live descendants of this same actual prefix that
end at one installed state have equal total exposed depth. At $q=3$,
distinct new-hit counts at a common live state can only be $0,2$; at
$q=N-2$ the dual statement holds for new-zero counts.

Proof. We first justify the residual graph using the actual-prefix
restriction of [CP, Theorem 5.1][CP]. By Lemma 2.2 the fixed prefix has
exact charges $|S_0|,C_{S_0}$, so every completion has remaining caps
$N,C_R$. Retain every $R$-labeled state reached on some completion after
this prefix, and suppress intervening chains of $S_0$-labeled states
using the fixed old assignment. A realized such chain is finite by actual
termination. It leads to another retained state or an output terminal.
The initial chain reaches a retained state since $1\le q\le N$ is
nonconstant. Complete any unrealized edge by an arbitrary terminal.
For each assignment on $R$, induction follows precisely its old
$R$-state subsequence; it never reaches an edge newly assigned in this
completion of the static table. The graph is correct, terminating and
satisfies both residual caps, with no copied states and with its labels
and costs inherited from $R$. All live descendant queries have labels in
$R$ by freshness, so their endpoints are retained literally and the
restriction preserves their newly exposed supports and counts.

For threshold three, the depth lemma is [Third, Lemma 7.1][Third]. Here
is its local argument in the residual graph. Equal hits at a common state
force the same support by Lemma 2.3 and therefore the same depth. For
different hits the two-gap rule leaves only $0,2$, so $\Delta=2$.
The lower private set $X$ is all old zeros, giving $a\le b$. If
$\delta_I=0$, the upper private set is all old ones and gives $b\le a$.
If $\delta_I>0$, now $Q=3$, $V'=1$, $\lambda=b+u-2$, and (2.6)
specializes to

$$
b+u=\lambda+V'+1\le u+\min(a,b),
$$

again giving $b\le a$. Thus $a=b$ and the support sizes are equal.
For $q=N-2$, interchange zero and one replies and swap terminal labels.
On $y$ the resulting graph computes
$1-\mathbf1_{\{|1-y|\ge N-2\}}=\mathbf1_{\{|y|\ge3\}}$,
with identical installed states and per-run charges. The threshold-three
argument gives the dual conclusion. Adding back the fixed $|S_0|$
exposures proves equality of total depth. Native selected histories obey
the same conclusion through the projection of Theorem 1.4. $\square$

**Corollary 6.3 (scope of the application).** Theorem 6.2 is a composition
of the prior live-depth lemma with the prior actual-prefix restriction.
It gives no cross-cone state disjointness, global levelization, unique
support, unique residual or permission to sum overlapping cone counts.
For $n=7,k=4$, a first-one cone has $N=6,q=3$ and a first-zero cone has
$N=6,q=4=N-2$; each is covered separately, while sharing between those
two cones remains an obligation. No new numerical optimum is asserted.

**Theorem 6.4 (inherited cuts on one actual prefix and residual slack).**
Fix the actual prefix of Definition 6.1 and put $t=|S_0|$.
Every original common-support cut $b$ with $t<b<n$ becomes a
common-support residual depth $b-t$, with support $T_b\setminus S_0$.
The formal endpoint $n$ becomes $N$. Form the increasing list consisting
of $t$, all original cuts strictly after $t$, and $n$. Suppose its
successive distances are at most four and $N\ge6$, $3\le q\le N-2$.
Let $P$ be the one residual graph constructed by the fixed-prefix
restriction in the proof of Theorem 6.2. On the original installed vector,

$$
m(R)\ge q(N-q+1)+\nu_P+E_{{\rm reg},P}
 +b_{{\rm short},P}+2\tau_P.
\tag{6.1}
$$

The suffix $P$ on a subscript specifies the incidence quantities of that
same residual graph, with its own parameters and cuts. In particular the
weaker $m(R)\ge q(N-q+1)$ is [SI, Theorem 10.8][SI]. Its qualified
residual grid minimum is exact. Neither simultaneous attainment of all
prefix constraints in one original graph nor disjointness of different
prefix restrictions is asserted. Gaps before this fixed prefix are
unrestricted.

Proof. The no-copy residual construction in Theorem 6.2 uses only the
fixed actual old assignment, and works for any nonconstant $q$.
It gives a complete correct terminating graph with at most $m(R)$
states and both residual caps $N,C_R$. At a live residual prefix with
$j$ new ones and $z'$ new zeros the original counts are
$(h_0+j,t-h_0+z')$. Residual liveness gives
$h_0+j\le k-1$ and
$t-h_0+z'\le t-h_0+N-q=n-k=L-1$.
Thus the corresponding original occurrence stays live. Its fixed label
is fresh by Lemma 2.2, so no intervening old-$S_0$ query is suppressed
on this live part. Induction identifies the residual live history with
an actual original extension, with the same endpoint and newly exposed
assignment. Conversely every such live extension appears in the residual
subsequence construction. Its arbitrarily completed unrealized edges
remain unreachable on actual completions.

At residual depth $b-t$ an original cut forces total support $T_b$,
so every residual support is $T_b\setminus S_0$. In particular
$S_0\subseteq T_b$. This proves inheritance, including the formal
endpoint separately. Residual depth zero is common even if the original
depth $t$ was ambiguous. The inherited cuts have spacing at most four;
additional residual cuts only subdivide them. Hence every gap of $P$
has span at most four. Its costs are exactly the distinct original
$c_i=s_i+4$ on $R$, reindexed in their original increasing order.
Apply Theorem 5.6 to this one residual graph and use $|Q(P)|\le m(R)$
to obtain (6.1).

The cut inheritance and numerical residual bound are precisely the
credited [SI, Theorem 10.8][SI] application of [CP, Theorem 5.1][CP].
The explicit short-block term in (6.1) follows from Section 4; its terminal
term is the credited SI margin. Repeating the proof for different actual
prefixes keeps the same original $m_i$ throughout. Their restricted
state sets can overlap; neither summing their lower bounds nor subtracting
lower bounds on overlapping coordinate sets assigns available states.
This graph restriction is mathematical and supplies no free runtime
reset, residual entry, address computation or transition. $\square$

## 7. Full-fiber consequences and credited boundary values

**Theorem 7.1 (native short-block slack).** Let a native preparer satisfy
the original caps and let $M_i$ be the number of its installed states with
word in $E_i$ of (1.2), including unused ones. Write $M=\sum_iM_i$.
Its cube projection has
$m\le M\le H-4-r$. If that projection has no three consecutive
ambiguous depths, then

$$
H\ge G+4+r+\nu+E_{\rm reg}+b_{\rm short}.
\tag{7.1}
$$

Any native $H<G+4+r$ forces (5.3)--(5.4) on this same projected graph.
The qualified minimum is $G+4+r$, attained on the full original fiber.

Proof. Apply (1.3)--(1.4) and Theorem 5.1 to this one projection. All
projected count quantities in (7.1) concern that graph, without claiming
them for an unrelated native history family. The fixed-order grid and the
full-fiber lift of Theorem 1.4 attain $G+4+r$, with original code,
$2+r$ latches, complete entries, literal four-reply tables and the
separate unchanged reader. The same actual cube input attains the two
native caps $n+1,W+3$. No shape promise is used in the upper. The
qualified minimum itself is already [SI, Corollary 9.5][SI]; the explicit
short-block slack is the added consequence here. $\square$

**Remark 7.2 (boundary optimum attribution).** At $k\in\{3,n-2\}$,
[CP, (CP.21)][CP] already gives

$$
\min m=3(n-2),\qquad H_{\rm exec}(A,k;r)=3(n-2)+4+r.
$$

The preceding [Third][Third] body supplies the threshold-three live-depth
lemma used in Theorem 6.2. Neither the numerical boundary result nor that
lemma is a new result of this volume. They do not settle the unrestricted
intermediate target.

**Theorem 7.3 (native current-frontier and prefix consequences).** For
the native preparer and its same cube projection in Theorem 7.1, if every
projected gap ending after $e_*$ has span at most four, then

$$
H\ge G+4+r+\nu+E_{\rm reg}+b_{\rm short}+2\tau.
\tag{7.2}
$$

The exact minimum for this projected qualified class, and for its
all-spans-at-most-four subclass, is $G+4+r$. If its projection has a
terminal span-four gap, the bound includes the credited two-unit margin;
no attainment with that gap is asserted. In any unrestricted native
strict saving $H<G+4+r$, that same projection strictly reverses
(5.15) and has a late span-at-least-five gap satisfying (5.16).

For an actual live prefix in that projection under Theorem 6.4's
conditions, its selected installed vector satisfies

$$
M(R)\ge q(N-q+1)+\nu_P+E_{{\rm reg},P}
 +b_{{\rm short},P}+2\tau_P.
\tag{7.3}
$$

Proof. Theorem 1.4 gives $m\le M\le H-4-r$ on one actual
projection. Apply Theorem 5.6 for (7.2). The same full-fiber grid lift
as in Theorem 7.1 attains the class minima and both native caps on a
single actual origin, while remaining correct on the full unbounded
fiber. Those numerical minima and the late-gap necessity are already
[SI, Corollary 10.6 and Proposition 10.9][SI]; the explicit short-block
slack uses Section 4 here. If $H<G+4+r$, then $m<G$ in this
projection, giving the strict global deficit without mixing histories
from other projections. Finally $m_i\le M_i$ for every selected
coordinate, so (6.1) implies (7.3). Its numerical part is SI Theorem
10.8, and its short-block slack is the corresponding proved deduction.
All these inequalities constrain the one original installed vector;
states in different cones need not be distinct. Native calls suppressed
by either mathematical restriction remain paid. The original literal
code, $2+r$ latches, four replies, complete entries and separately
priced eight-state reader remain those of Section 1. $\square$

## 8. The current weighted-frontier comparison

This appendix states the complete construction and quantifiers of [WTF,
Section 11][WTF]. Its examples are above the grid. They limit two universal
charging proposals and supply no strict-subgrid competitor or new optimum.

**Definition 8.1 (parameters and actual-history representatives).** Fix
$M\ge2$, $n=3M+5$, $k=M+4$, and partition the coordinate set as

$$
[n]=\{t\}\sqcup X\sqcup Y\sqcup R
\sqcup\{u_1,\ldots,u_M,v_1,\ldots,v_M\},
$$

where $X=\{x,x'\}$, $Y=\{y,y'\}$, $R=\{r_1,\ldots,r_M\}$.
Set $U_j=\{u_{M-j+1},\ldots,u_M\}$ and
$I_j=[n]\setminus(X\cup Y\cup U_j)$ for $1\le j\le M$.
Choose original distinct positive positions and costs satisfying

$$
c_t\le c_{x'},\qquad c_t\le c_{y'},\qquad
c_x+c_t\le C_Y,\qquad c_y+c_t\le C_X.
\tag{8.1}
$$

A permitted choice is $c_i=5\,3^{i-1}$, $s_i=c_i-4$, with
$t,x,y,x',y'$ the first five indices and the remaining indices in displayed
$R,u,v$ order. The first five costs are $5,15,45,135,405$, satisfying
(8.1), and all positions are positive and increasing. This is one allowed
input choice; no general nonresonance hypothesis is imposed.

A representative system chooses for each $p\in V$ an actual live history
with that count pair, ending before a running invocation. Its state map is
$f:V\to Q$. The histories, not just their marginal count labels, are part
of the choice. A collision is a pair of distinct cells with the same
representative state. A family is cell-disjoint if no cell is used twice.
For two fixed incoming histories in the notation of Lemma 2.3, an allowed
cross-fill retains each history's own old values on $I$, uses old $S$
values on $X$ and old $T$ values on $Y$ on both completions, and chooses
one common assignment on $U$ in (2.5). Its first separator is the first
common-suffix state with different replies. In the examples below
$\lambda=V'=1$. Its three-state first-exposure pack consists of this
separator, the state first exposing the new zero completing the negative
certificate, and the state first exposing the new one completing the
positive certificate. This fixes the pack before any charging assertion.

**Definition 8.2 (complete table with one fixed retained t separator).**
Start with a complete binary query tree of depth $n$, all internal vertices
distinct, and threshold terminals only at depth $n$. It queries every
coordinate once per path, including paid work after a certificate. First
query $r_1,\ldots,r_M$. The routing vector $e_j$ denotes the $j$th unit
vector and is unrelated to reader entries. In cylinder $R=e_j$, query
$t$ next, then $I_j\setminus(R\cup\{t\})$ in increasing coordinate-index
order. If $t=0$, query $x,x'$ next; if $t=1$, query $y,y'$ next. Finish
the remaining coordinates in increasing order. In $R=0^M$, use increasing
order among the remaining coordinates except that $t$ is last. Every other
routing cylinder uses increasing order among its remaining coordinates.
These rules assign one fixed label to each tree vertex.

Select two prefixes in each $R=e_j$. The low prefix has $t=0$, all old
$u_i$ zero, $v_1,\ldots,v_{M-j}$ one, the remaining $v_i$ zero, and
$(x,x')=(1,0)$. The high prefix has $t=1$, all old $u_i$ zero, all $v_i$
one, and $(y,y')=(0,1)$. Here old $u_i$ means only
$u_i\notin U_j$; $U_j$ is unread on both histories. Empty lists impose
no condition. Their supports are $I_j\cup X$, $I_j\cup Y$, both of
size $n-j-2$.

In the untouched $R=0^M$ cylinder, take the existing final vertex labeled
$t$ whose prefix gives one to every $v_i$ and to $x,x',y$, and zero to
every $u_i$ and to $y'$. Call exactly this vertex $J$. Its prefix has
$M+3=k-1$ ones. Thus its literal fixed table is

| state | coordinate | zero successor | one successor |
| --- | --- | --- | --- |
| $J$ | $t$ | $\mathsf0$ | $\mathsf1$ |

This vertex is retained and counted once; no new copy of $J$ is installed.
The identity $i(J)=t$ fixes its charge to $c_t$ on every incoming route.
Delete the remaining subtree, including its root, at each selected low and
high prefix, and redirect both incoming edges at scale $j$ to a new $V_j$.
Each deleted subtree has $j+2$ query levels. Add the following distinct scan
states, disjoint from all retained tree vertices:

| state | coordinate | zero successor | one successor |
| --- | --- | --- | --- |
| $V_1$ | $u_M$ | $B_X$ | $B_Y$ |
| $V_j$, $2\le j\le M$ | $u_{M-j+1}$ | $Z_{M-j+2}$ | $O_{M-j+2}$ |
| $Z_i$, $2\le i<M$ | $u_i$ | $Z_{i+1}$ | $J$ |
| $O_i$, $2\le i<M$ | $u_i$ | $J$ | $O_{i+1}$ |
| $Z_M$ | $u_M$ | $B_X$ | $J$ |
| $O_M$ | $u_M$ | $J$ | $B_Y$ |

Add four further distinct private states, disjoint from the tree and scans:

| state | coordinate | zero successor | one successor |
| --- | --- | --- | --- |
| $B_X$ | $x$ | $B_{x'}$ | $J$ |
| $B_{x'}$ | $x'$ | $\mathsf0$ | $\mathsf1$ |
| $B_Y$ | $y$ | $J$ | $B_{y'}$ |
| $B_{y'}$ | $y'$ | $\mathsf0$ | $\mathsf1$ |

All other retained tree transitions are unchanged. The two original terminals
are the only terminals. This completely specifies $B_M$, including $M=2$,
when the intermediate $Z_i,O_i$ lists are empty.

**Theorem 8.3 (correct weighted feasibility and exact above-grid count).**
The table $B_M$ terminates correctly on every Boolean input and satisfies
both same-input caps $n,W$. It has

$$
m_B=2^{3M+5}-16(2^M-1)+5M+1>G=2(M+4)(M+1).
\tag{8.2}
$$

One untouched input attains both caps. Its full-fiber native lift has
exactly $m_B+4+r$ preparation states and simultaneously attained maxima
$n+1,W+3$, with the original code and separate complete reader.

Proof. The unit cylinders are disjoint, and within each the two deleted
subtrees differ at $t$. All deletions are below routing depth $M$ and avoid
$R=0^M$, so $J$ remains. The low prefix has
$1+(M-j)+1=M-j+2=k-j-2$ ones, leaving AND on $Y\cup U_j$. The high
prefix has $1+1+M+1=M+3=k-1$ ones, leaving OR on $X\cup U_j$.
Both are live. The scan sends all-zero $U_j$ to $B_X$, all-one $U_j$
to $B_Y$, and any mixed assignment to $J$ at its first change.

For mixed $U_j$, low AND is zero and high OR is one, exactly their
respective old $t$ values queried at $J$. For all zeros, low has old $x=1$
and follows $B_X,J$ to zero; high computes $x\lor x'$, going through
$J$ to one when $x=1$, and otherwise reading $x'$. For all ones, low
computes $y\land y'$, going through $J$ to zero when $y=0$, and otherwise
reading $y'$; high has old $y=0$ and follows $B_Y,J$ to one. These six
cases exhaust every extension of either replaced prefix. Other inputs
follow the original full threshold tree. Scan indices increase and every
exit has at most two further calls, so termination follows too.

A replaced run makes $n-j-2$ prefix calls, at most $j$ scan calls and
at most two tail calls. Its prefix charge is $C_{I_j}+C_X$ or
$C_{I_j}+C_Y$, and the scan charge is at most $C_{U_j}$. With the fixed
$i(J)=t$, the exhaustive tail bounds are

| scan exit | low-prefix tail bound | high-prefix tail bound |
| --- | --- | --- |
| all zero | $c_x+c_t\le C_Y$ | $\max(C_X,c_x+c_t)=C_X$ |
| all one | $\max(C_Y,c_y+c_t)=C_Y$ | $c_y+c_t\le C_X$ |
| mixed | $c_t\le C_Y$ | $c_t\le C_X$ |

The maximum equalities use $c_t\le c_{x'}$ and $c_t\le c_{y'}$.
The mixed bounds follow from these inequalities as well. Hence each run
costs at most $C_{I_j}+C_X+C_Y+C_{U_j}=W$ and at most $n$ calls.
Repeated $t,x,y$ and all certified work are included. Every untouched
$R=0^M$ input still queries all coordinates exactly once and attains
$n,W$ together.

The original tree has $2^n-1$ running vertices. Exactly
$2\sum_{j=1}^M(2^{j+2}-1)$ vertices are deleted. The new vertices number
$M+2(M-1)+4=3M+2$, giving

$$
m_B=(2^n-1)-2\sum_{j=1}^M(2^{j+2}-1)+(3M+2)
=2^n-16(2^M-1)+5M+1.
$$

The existing $J$ is counted only in the retained tree. The untouched
zero-routing subtree alone has $2^{2M+5}-1$ vertices. Induction gives
$2^M\ge M+1$ for $M\ge0$, so this subtree has at least
$32(M+1)^2-1>2(M+4)(M+1)$ vertices for $M\ge2$. Thus $m_B>G$.
Finally apply Theorem 1.4 to this complete correct graph, retaining every
installed vertex. Its all-vector proof applies to the static indicators of
every arbitrary branch image in $Z_{b_3}$; the profile front covers the
other ten profiles. Actual cube origins realize the untouched inputs
attaining both caps. The complete predecessor rows, original literal
entries, four replies, $2+r$ latches and separate eight-state reader are
preserved. This is the feasible construction of [WTF, Theorem 11.3][WTF].
$\square$

**Theorem 8.4 (the same first separator under every allowed cross-fill).**
For $j=2,\ldots,M$, the two fixed histories at $V_j$ represent

$$
L_j=(k-j-2,n-k),\qquad H_j=(k-1,n-k-j-1).
\tag{8.3}
$$

All $2(M-1)$ cells are distinct. Their private sets are exactly $X,Y$,
common old set $I_j$, and common unread set $U_j$. Every allowed
cross-fill has first separator exactly the fixed retained $J$. Thus for
every joint choice $(\omega_j)_{j=2}^M\in\prod_{j=2}^M\{0,1\}^{U_j}$,
all $M-1$ first separators are this one state.

Proof. Subtract the displayed hit counts from $n-j-2$ to get (8.3).
The low hits vary below $k-1$, and the high zeros vary below $n-k$,
so the cells are pairwise distinct. Lemma 2.3's parameters specialize to

$$
a=b=2,\quad u=j,\quad Q=j+2,\quad V'=1,\quad
\xi=\eta=1,\quad\Delta=\delta_I=j+1,\quad\lambda=1.
$$

The band (2.5) is all weights $0,\ldots,j$. Cross-fill $(x,x')=(1,0)$
and $(y,y')=(0,1)$ on both inputs and choose any $U_j$ assignment of
weight $w$. The two totals are $k-j-1+w\le k-1$ and $k+w\ge k$.
They extend their own fixed histories, agree outside $I_j$, and have
actual cube origins. Both suffixes read the same $U_j$ replies. A mixed
assignment reaches $J$ directly; all zeros pass through common $x=1$
at $B_X$, and all ones through common $y=0$ at $B_Y$, before reaching
$J$. No differing old coordinate is queried earlier on that suffix. At
$J$, and specifically at its coordinate $t$, the replies are zero and
one. This is a fully paid old-coordinate requery on both runs. In the
native lift the literal is $a_t$, giving beta and branch. The argument
holds separately for every $j$ and every allowed assignment; the product
statement requires no single input common to different collisions. It
retains the exact quantifiers of [WTF, Theorem 11.4][WTF]. $\square$

**Proposition 8.5 (favorable and hostile actual representative systems).**
The same $B_M$ has an injective representative map using only retained tree
vertices. It also has one lawful fixed map choosing $L_j,H_j$ at $V_j$
for all $j\ge2$ and with $Z_M,O_M,B_X,B_Y,J$ in its image. For the
latter system the collision $L_2,H_2$ has exactly these packs:

| $(u_{M-1},u_M)$ | three-state first-exposure pack |
| --- | --- |
| $(0,0)$ | $\{V_2,B_X,J\}$ |
| $(0,1)$ | $\{V_2,Z_M,J\}$ |
| $(1,0)$ | $\{V_2,O_M,J\}$ |
| $(1,1)$ | $\{V_2,B_Y,J\}$ |

Every allowed pack for that one collision lies in the chosen image. For
all $j\ge2$, the one-hot-at-$u_M$ completions have exact packs
$\{V_j,Z_M,J\}$ in that same image.

Proof. For favorable representatives at cell $(h,z)$ put $d=h+z<n$.
If $d\le M$, choose any routing prefix with those counts. Deletions
begin at depths $n-j-2>M$, so its vertex remains. If $d>M$ and
$h\ge2$, set $a=\min(h,M)$ routing bits to one, for example the first
$a$. Here $M-a\le z$, since either $a=M$ or $d>M$ and $a=h$.
This routing cylinder has at least two ones and is untouched. In the next
$d-M$ positions put $h-a$ ones and $z-(M-a)$ zeros; these nonnegative
counts sum to $d-M$. If instead $d>M$ and $h\le1$, use $R=0^M$;
then $z\ge M$, and the next $d-M$ positions can contain $h$ ones
and $z-M$ zeros. All chosen vertices are running and live. Their earlier
prefixes are live because their counts cannot exceed the chosen live
counts. Actual completions realize them. Distinct cells cannot select the
same retained vertex because its inherited tree prefix has a fixed count
pair. This proves injectivity, without asserting that all lawful fixed
representative maps are injective.

For the hostile map use the fixed collision histories of (8.3) and the
following five additional actual histories:

| chosen state | live cell | actual prefix reaching it |
| --- | --- | --- |
| $Z_M$ | $(k-1,n-k-2)$ | high $j=2$ prefix, then $u_{M-1}=0$ |
| $O_M$ | $(k-3,n-k)$ | low $j=2$ prefix, then $u_{M-1}=1$ |
| $B_X$ | $(k-1,n-k-1)$ | high $j=2$ prefix, then $U_2=(0,0)$ |
| $B_Y$ | $(k-2,n-k)$ | low $j=2$ prefix, then $U_2=(1,1)$ |
| $J$ | $(k-1,n-k)$ | the untouched zero-routing prefix defining $J$ |

Starting from $H_2=(k-1,n-k-3)$ adds one or two fresh zeros; starting
from $L_2=(k-4,n-k)$ adds one or two fresh ones. Thus all five are
live, pairwise distinct and actual. They avoid (8.3): its low hits are at
most $k-4$, its high zeros at most $n-k-3$. Choose these and the
$2(M-1)$ collision histories, and use the favorable construction for all
remaining cells. No cell receives incompatible choices.

For $(0,0)$ the scan's first zero at $V_2$ completes the negative
certificate and $x=1$ at $B_X$ completes the positive one. For $(0,1)$
the corresponding first new one is at $Z_M$. For $(1,0)$ the first
new one is at $V_2$ and first new zero at $O_M$. For $(1,1)$ the first
new zero is at $B_Y$. The separator is $J$ in every case. These are the
exact packs in the table, with three distinct states. For the one-hot
completion at $u_M$ at any $j\ge2$, the first new zero is at $V_j$
and the first new one at $Z_M$, giving the asserted pack. We do not
assert that every allowed pack for every $j$ lies in the image. These
are the two separate representative results of [WTF, Propositions
11.5--11.6][WTF]. $\square$

**Theorem 8.6 (two universal fixed-representative charging shortcuts fail).**
There is no finite dimension-independent $C$ such that for every cap-feasible
table, every lawful fixed representative system and every cell-disjoint
family of the above collisions, allowed completions can be jointly selected
so that each installed state is first separator for at most $C$ collisions.
It is also impossible universally to choose an injective pack-state
representative outside the fixed representative image; even for a single
collision, dropping injectivity does not repair that assertion.

Proof. Given $C$, choose $M$ with $M-1>C$ and take the hostile system
in Proposition 8.5. Theorem 8.4 forces all $M-1$ first separators to be
$J$, under every joint choice. For the external-pack assertion, every
allowed pack for the one collision $L_2,H_2$ is already in the fixed
image, leaving no external candidate at all. This reproduces [WTF,
Theorem 11.7][WTF] with its universal quantifiers. $\square$

**Proposition 8.7 (exact boundary of the comparison).** The appendix
refutes the two universal claims in Theorem 8.6. It does not refute
favorable representative selection, a theorem restricted to minimum or
strict-subgrid graphs, another installed compensation scheme, or
$D\le E+\nu$. All examples satisfy $m_B>G$. The same state $J$ is
live at another actual history, so it belongs to $Q_{\rm live}$ rather
than automatically to $\nu$. Theorems 3.3--5.1 count all incidences of
one graph and do not require separator packs; the appendix is compatible
with them. Neither an unrestricted intermediate lower bound nor a correct
strict-subgrid graph is established here. $\square$

## 9. Attribution, proof scope and the original remaining obligation

**Definition 9.1 (supplier and increment map).** The following ownership
is part of the scope of the statements, with the complete supplied current
SI Sections 9--10 included in the comparison.

| content used here | credited supplier and retained scope |
| --- | --- |
| image/inverse, eleven complete-row profiles, original reader and native model | WTF Section 1; no bounded source-domain substitution |
| simultaneous cube, all-address $E_i$, same-run charges and exact native feasibility | WTF Supplier 2.1, Lemma 2.2 and Theorem 4.1; ordinary proof in Section 1 above |
| saturation, private exchanges, support exclusions and two gaps | PE Theorem 3.1 and Lemma 4.1; WTF Convention 6.1 and Theorems 7.1, 9.1; the arguments are recorded in Section 2 |
| actual host/support incidence and diagonal common support | SI Theorems 2.2 and 4.1 |
| exact $m-G=E-D+\nu$ | SI Theorem 5.2, (SI.19) |
| cuts, support envelopes and compatible block decomposition | current SI Lemma 9.2 and Theorem 9.3, which additionally partition the unchanged installed multiplicity vector by coordinate blocks |
| nonnegative compensation for spacing at most three; qualified minima; exact remaining sum | current SI Theorem 9.4, Corollary 9.5 and Proposition 9.6 |
| last-layer exclusivity, right-cut separation and early-ending no-sharing | current SI Lemma 10.2; Lemma 5.2 gives the full actual-extension proof |
| six-cell span-four classification and compensation | current SI Lemma 10.3 and Theorem 10.4; Lemma 5.3 and Theorem 5.4 reproduce the ordinary proof |
| terminal span-four margin, enlarged qualified minima and genuine class enlargement | current SI Corollaries 10.5--10.6 and Proposition 10.7; Corollary 5.5 and Theorems 5.6, 7.3, Proposition 5.7 reuse them |
| actual-prefix inheritance and conditional residual numerical grid constraint | current SI Theorem 10.8 with CP Theorem 5.1; Theorem 6.4 retains this on the same installed vector |
| late-span-at-least-five necessity and exact surviving global sum | current SI Proposition 10.9; equations (5.15)--(5.16) retain this frontier |
| strict $E_B-D_B\ge1$ for each nonempty maximal block with $|B|\le2$ and explicit short-block slack | Theorems 4.1--5.1 here; obtained by retaining ambiguity excess on every interior depth of the credited classification |
| short-block units in the current global sum and qualifying residual/native bounds | Theorems 5.6, 6.4 and 7.3 combine Section 4 with credited SI10 on each same actual graph; no extra independent-state allocation |
| boundary live-depth lemma and fixed-prefix restriction | Third Lemma 7.1 and CP Theorem 5.1; Theorem 6.2 here is their same-prefix application |
| boundary numerical optimum | CP (CP.21), not a new value here |
| weighted retained-$t$ construction and representative obstructions | complete current WTF Section 11, specifically Definitions 11.1--11.2, Theorems 11.3--11.4, Propositions 11.5--11.6 and Theorem 11.7 |

The separately named PCA, NBP and TMC volumes inside these suppliers are
unopened nested references, not separately supplied bodies. Only the
interfaces and deductions actually exposed in WTF, PE, CP, SI and Third are
used; no unseen stronger premise is imported. In particular SI's original
fixed-vector bookkeeping is credited rather than replaced by independent
counts from hypothetical block tables. All proofs here are ordinary analytic
arguments, without a kernel-certification claim or a worldwide priority claim.

**Theorem 9.2 (the original universal obligation at the current frontier).** For every
$n\ge7$, $4\le k\le n-3$, every original position set $A$ and all $r\ge0$,
the unresolved lower-bound assertion is

$$
D\le E+\nu,
\quad\text{equivalently}\quad
\sum_{I\in\mathcal L_*}(D_I-E_I)
\le\nu+E_{\rm reg}+\sum_{I\in\mathcal A_*}(E_I-D_I)
 =\nu+E_{\rm reg}+b_{\rm short}+2\tau+\Xi
\tag{9.1}
$$

for every correct terminating unrestricted graph at the simultaneous caps
$n,W$. The contrary alternative requires one complete graph with $m<G$,
all fixed labels and successors, correctness and termination on every
Boolean input, both caps on every same input, and the faithful full-fiber
lift preserving the original code, entries, reader and latches.

Proof. Theorem 3.3 gives the exact identity, and Theorem 5.6 gives (9.1),
the late-gap partition of [SI, Proposition 10.9][SI] with the proved
short-block units and credited terminal margin exposed. The older sum
(5.5) is still equivalent, but SI10 already proves nonnegative compensation
for every span-four gap and rules out sharing at all gaps ending at
$b\le e_*$. Thus an actual local deficit must have span at least five
and right endpoint greater than $e_*$. It has at least four internal
ambiguous depths and obeys (5.16). No upper bound on the total of those
late deficits is supplied by the nonnegative right side of (9.1).

In a four-coordinate window, abstract supports
$T_-\cup\{x\}$ and $T_-\cup\{y,z\}$ can leave a fourth
coordinate fresh for both. That pattern only defeats the simplest
nested-or-forced-old-label argument: the actual fixed-successor analysis
of Lemma 5.3 and Theorem 5.4 nevertheless compensates every such span-four gap.
At span at least five there are further internal support layers, so a
common live reply can reach another shareable internal layer. The six-cell
classification above supplies no compensation theorem there. Abstract
support sets alone provide no count-compatible histories or correct
counterexample; fixed labels and successors, old assignments, certified
exits and both whole-input budgets must still be jointly handled.

Theorems 6.2 and 6.4 concern individual actual prefixes on the same
installed vector. Their restrictions can overlap, so their lower bounds
cannot be summed or subtracted to allocate distinct states. Section 8
concerns above-grid graphs only and supplies no universal separator-capacity
premise. Theorem 1.4 transfers the two actual alternatives to the unchanged
native question at $G+4+r$, caps $n+1,W+3$, on the entire original
fiber. Neither alternative is settled by this volume.
$\square$

**Remark 9.3 (explicit qualifications).** The strict short-block result
and its slack are bounded additional deductions beyond the statements of
current SI Sections 9--10 at their stated scopes. The span-four results,
early-ending exclusion, terminal margin, enlarged minima, inherited-prefix
numeric bounds and late-gap frontier are credited reuse, as are the
boundary fixed-prefix composition and the weighted appendix. The explicit
short-block units in the combined safe-gap sum and qualifying prefix/native
bounds follow from the proved strict surplus; no independent novelty is
claimed for the underlying SI10 mechanisms. No normalization into either
qualified class is proved. The source allows arbitrary stationary sharing, repetitions,
paid certified continuations, union cycles and inconsistent syntactic paths,
requiring termination only on actual inputs. It imposes no ordered,
read-once, levelled, unique-host, unique-support, unique-residual,
nonresonance or cross-cone-disjointness premise. Distinct individual costs
remain the original ones and larger equal subset sums are permitted.
Installed cardinality proves no acquisition, authentication, export,
physical-memory, workspace, elapsed-time, service or physical-efficiency
claim. No neural-network or empirical result is asserted. The continuing
unrestricted objective is not declared complete.

[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[CP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md
[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[Third]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THIRD_THRESHOLD_OPTIMUM.md

## 追加锚（本行以下为增补区）
