# FIB three reads: a quantitative installed-state correctness gap

> This reference volume uses the `generic-v1` theory convention. Its
> numbered claims and proofs are ordinary mathematical input; they are
> not machine status declarations. Once incorporated, existing text is
> retained and subsequent additions begin after the final append anchor.

For the original stationary biased XOR source, every complete controller
with at most eight installed rows and almost-sure return within three
paid calls has correct classification mass at most

$$
S_3-\rho(p),\qquad
S_3=\frac a2+3a^2\eta+2\eta^3,
\qquad \rho(p)\ge\frac{d^2b^7}{2}>0.
$$

Here $a=\max(p,1-p)$, $b=\min(p,1-p)$, $\eta=ab$ and
$d=a-b$, for every fixed $0<p<1$, $p\ne1/2$. Section 3 defines
$\rho$ as the minimum of seven explicit positive losses. The proof
quantifies the inherited optimal geometry, then forces six distinct
actual Read rows and three distinct actual Halt rows whenever the loss
is smaller than that minimum. No finite-menu or nonattainment argument
is used to infer the numerical gap. The exact values at six, seven
and eight installed rows remain unresolved.

## 1. Evidence, ownership and the exact source

**Convention 1.1 (Reference and evidence boundary).** This volume
contains ordinary probability proofs; no Lean-kernel verification,
digestion, mathematical execution or numerical evidence is asserted.
The six owning project volumes retain the results identified in
Section 11. The additional mathematical content is quantitative
stability of the three-read geometry: loss below the threshold in
Section 3 forces the inherited optimal instruction and label pattern,
giving the installed correctness gap. The source, scalar optimum and
nine-row equality obstruction retain their existing ownership.
No literature-wide priority claim is made.

**Definition 1.2 (One stationary joint law).** Let $\varphi$ be
uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$. The four symbols in
$\mathcal A=\{a_0,a_1,b_0,b_1\}$ are distinct. Set, on the original
integer clock,

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this joint law. It is [Original, Proposition 2.1 and
(2.2)][O]. To check the stationary clock, put $\pi_0=1-p$,
$\pi_1=p$. An active transition takes $a_s$ to $b_t$ with
probability $\pi_t$, emitting $s\oplus t$; the next transition
copies $b_t$ to $a_t$, emitting zero. Incoming mass at each state
with spin $t$ is $\pi_t/2$. Thus the uniform phase gives the
original stationary emitted-bit law, including its separator sites.

Fix $j\in\{0,1\}$ before acquisition, and define

$$
\begin{array}{c|cc|cc}
 &h_0(s)&v_0&h_1(s)&v_1\\ \hline
j=0&a_s&0&b_s&0\\
j=1&b_s&1&a_s&0
\end{array}
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.2}
$$

In particular $v_0=j$ and $v_1=0$. The phase-specific label sets
are disjoint. Correctness for one returned state never adds the
correct masses of two different-phase states. Formula (1.1) describes
the law and grants no access to an unqueried spin or to its phase.

**Convention 1.3 (Parameters).** Throughout this volume set

$$
\begin{gathered}
a=\max(p,1-p),\quad b=\min(p,1-p),\quad
\eta=ab,\quad c=a^2+b^2=1-2\eta,\quad d=a-b,\\
R=a/b,\qquad
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2.\end{cases}
\end{gathered}
\tag{1.3}
$$

Thus $\mathbb P(S_\ell=\sigma)=a$. The following identities and
comparisons will be used over the entire declared range:

$$
\begin{gathered}
a+b=1,\quad 0<b<1/2<a<1,\quad 0<d<1,\quad 0<\eta<1/4,\\
1/2<c<a,\quad c>b,\quad a-c=bd,\quad c-b=ad,\\
2a^2-c=d,\qquad c-1/2=d^2/2,\\
t:=a^3+b^3=1-3\eta,\qquad a^2-t=bd>0.
\end{gathered}
\tag{1.4}
$$

These follow by substituting $b=1-a$; for example
$c-1/2=(a-b)^2/2$ and $a^2-(a^3+b^3)=b(a-b)$.
They justify the strict directions below for either bias direction.

## 2. The whole installed-table competitor class

**Definition 2.1 (Literal complete controller).** Keep an arbitrary
probability space $(\mathsf U,\mathcal U,\nu)$ independent of the
whole $J_p$ source, with its law unchanged. An installed table is
$(\mathcal K,\lambda,\delta,c_{\rm init})$, with finite nonempty
row set $\mathcal K$,

$$
\begin{aligned}
\lambda &:\mathcal K\longrightarrow
\{\operatorname{Read}(t):t\in\mathbb Z\}
\sqcup\{\operatorname{Halt}(h):h\in\mathcal A\},\\
\delta &:\mathcal K_{\rm R}\times\{0,1\}\longrightarrow\mathcal K,
&c_{\rm init}&:\mathsf U\longrightarrow\mathcal K.
\end{aligned}
\tag{2.1}
$$

The sets $\mathcal K_{\rm R},\mathcal K_{\rm H}$ are the Read and
Halt rows. The initialization is measurable for discrete $\mathcal K$.
At initialization
the current row becomes $c_{\rm init}(u)$. A Read row makes its
fixed literal call to the actual $X_t$, consumes the reply in its
immediate update $\delta(r,X_t)$, and enters that successor. A Halt
row returns its fixed actual four-state label. Each instruction takes
finite duration; there are no silent instructions. A nonreturning
installed execution therefore makes infinitely many paid calls.

After initialization the current row contains all runtime memory.
There is no separate program position, clock, counter, phase port,
archive, stack, saved reply, output latch, computed address, seed
reaccess or online coin. The public fixed $p,j$ may determine the
static table. All installed rows count in $|\mathcal K|$, including duplicate
instructions, duplicate labels, unused rows and rows reached only on
null histories. Both successors of every Read row are fixed. Cycles
and arbitrarily long formal executions are allowed.

Every actual call is paid, including separators, repetitions, ignored
replies, negative coordinates, disconnected placements and arbitrarily
distant addresses. There is no hidden-state, half-line or tail read,
source-dependent seed or timing, reset, law switch, endpoint movement
or erased-coordinate substitution. This is the interface of
[Two Endpoint, Definition 8.1][E2]. It is a subclass of [Original,
Definition 9.1][O]'s measurable acquired-record protocols. The latter
also allow internal nonreturn after finitely many calls; that larger
class is not identified with installed tables here.

**Definition 2.2 (Correct mass and installed budgets).** Let $\tau$
be return time, equal to infinity on nonreturn, and let
$N\in\mathbb N_0\cup\{\infty\}$ count every actual call. Put

$$
\begin{gathered}
E_3=\{\tau<\infty,N\le3\},\quad
q_3=(J_p\otimes\nu)(E_3),\quad
L_3=(J_p\otimes\nu)(A\ne H_j,E_3),\\
C_m=\sup\{q_3-L_3:|\mathcal K|\le m,\ q_3=1\},\qquad R_m=1-C_m.
\end{gathered}
\tag{2.2}
$$

An immediate halt makes each class nonempty. The requirement $q_3=1$
is almost sure. It retains exceptional null nonreturns, excess-read
paths, arbitrary null cycles and completed versions. It imposes no
all-input stopping cap. On this slice $L_3$ is unconditional
four-state classification error up to null extension, distinct from
visible-bit Brier loss. Total paid cost is the extended expectation
$\mathbb E N$, including every nonreturning path.

**Lemma 2.3 (Actual sections and finite initialization).** For an
installed table write $w_r=\nu(c_{\rm init}^{-1}\{r\})$. If
$q(r),C(r)$ are its return and correct-return source masses within
three calls from deterministic row $r$, then

$$
q_3=\sum_rw_rq(r),\qquad
q_3-L_3=\sum_rw_rC(r),\qquad \sum_rw_r=1.
\tag{2.3}
$$

If $q_3=1$, each $w_r>0$ has $q(r)=1$. At a deterministic start,
a consistent reachable finite history has exactly its acquired-reply
cylinder as source section. On every positive section after three
calls the actual current row must Halt.

Proof. The seed has no role after choosing the row. Independence
gives (2.3) on the finite measurable initialization cells. Since
$\sum_rw_r(1-q(r))=0$ has nonnegative summands, every positive
cell has the stated mass-one property. This uses no conditioning on
singleton seeds, regular conditional law, atomic-seed assumption,
divisibility of seed masses or additional randomness.

For sections, start with the whole source at the empty history.
At each prefix the instruction is fixed. A Read at $t$ with reply
$x$ intersects the old section with $\{X_t=x\}$. A Halt and its
finite duration add no source condition. Induction gives the cylinder
assertion, including adaptive paths through the table. Contradictory
repeated replies give empty sections. Further intersections keep them
empty. A Read after three calls on a positive section incurs a fourth
call on all of that section, contradicting $q(r)=1$. The instruction
set consequently forces a Halt there. Null destinations remain
unrestricted. Measurable completions give the same integrated masses:
representatives agree off product-null sets, whose source sections are
null for almost every seed by Tonelli. $\square$

**Convention 2.4 (Scalar bounds versus state counting).** For a source
event $B$ put

$$
M(B)=\max_{h\in\mathcal A}J_p(B,H_j=h).
\tag{2.4}
$$

This bounds every actual terminal label. Splitting $B$ at a
hypothetical further call gives

$$
M(B)\le M(B\cap\{X_t=0\})+M(B\cap\{X_t=1\}).
\tag{2.5}
$$

Indeed keep a label maximizing the old section on both subevents,
then maximize separately. Thus scalar caps for at most the remaining
calls include early halts. This comparison only bounds masses. It
does not add calls or states to the original table, preserve state
cost under padding, or identify tree occurrences with installed rows.
All row counting below uses its actual instructions and fixed updates.

## 3. The seven-loss threshold

**Definition 3.1 (Inherited caps and quantitative losses).** Use
[Three Endpoint, Sections 3–7][E3]'s quantities

$$
\begin{gathered}
K=a^2\eta,\qquad J=2a\eta^2,\qquad K_0=a^2c\eta,\\
Z=\frac a2+K_0+K,\qquad D=K+J,\qquad
S_3=Z+D=\frac a2+3a^2\eta+2\eta^3.
\end{gathered}
\tag{3.1}
$$

Define

$$
\begin{aligned}
g_1&=d\eta^2,&
g_2&=\frac{\eta(b^2+a^2d^2)}2,&
g_3&=\frac{a\eta dc}2,\\
g_4&=\frac{a^2\eta d^2}2,&
g_5&=ac\eta bd,&
g_6&=\frac{db^6}2,&
g_7&=\frac{b^7}2,\\
\rho(p)&=\min_{1\le i\le7}g_i.
\end{aligned}
\tag{3.2}
$$

Every $g_i$ is positive by (1.4). The roles of $g_1,g_2,g_3$
are the first-one, mixed-parity and adjacent-zero losses;
$g_4,g_5$ handle the remaining last-edge geometries;
$g_6,g_7$ handle unequal same-phase and wrong-phase labels.
Sections 4–8 prove the full forcing statement needed to use them.

**Theorem 3.2 (Universal quantitative installed gap).** For every
declared $p$, either fixed actual endpoint $j$, every unchanged
independent seed law, and every table of Definition 2.1 with
$|\mathcal K|\le8$ and $q_3=1$, its correct mass satisfies

$$
q_3-L_3\le S_3-\rho(p).
\tag{3.3}
$$

Consequently, for every $1\le m\le8$,

$$
C_m\le S_3-\rho(p),\qquad
S_3-C_m\ge\rho(p)\ge\frac{d^2b^7}{2}>0.
\tag{3.4}
$$

The proof concludes in Section 9. No term of $\rho$, and no minimum
of those terms, is asserted to be sharp or to have a matching
middle-budget attainer.

## 4. Product calculus and every scalar continuation

**Lemma 4.1 (Components, orientation and exhaustive last moves).**
In phase $\phi$, a literal address $2\ell+\phi$ queries the
edge $\{\ell,\ell+1\}$ of the integer spin line; the other parity
queries a separator. Distinct active edges form finite disjoint paths.
A consistent labelled component has exactly two complementary spin
assignments, with their actual Bernoulli product weights. Independent
components multiply. Adjoin the actual target vertex as a singleton
when it has not been queried. Every phase-specific full-law mass has
the factor $1/2$.

If the target component has complementary weights $U\ge V>0$ and
another component has weights $A\ge B>0$, a joining edge has
summed best target-spin mass

$$
\begin{aligned}
\max(UA,VB)+\max(UB,VA)
&=UA+\max(UB,VA)\\
&=\max\bigl(U(A+B),A(U+V)\bigr).
\end{aligned}
\tag{4.1}
$$

All other components supply common multiplicative factors.

Proof. Successive XOR labels determine the next spin from the
preceding spin. Choosing the first spin gives exactly the two
complementary completions. The original iid law gives their products
and independence between vertex-disjoint components. Separators must
reply zero, repeats impose their old constraint, and inconsistent
labels have zero mass. For a join the two possible relative
orientations give product pairs $(UA,VB)$ and $(UB,VA)$, in either
reply order. Since $UA\ge VB$, taking their two maxima proves
(4.1). Attachment orientation only exchanges the two reply cases.

A new active line edge can repeat an old edge, extend a component
by a fresh vertex, join two components, or be disjoint from them.
There is no unused chord inside a connected path, and an edge cannot
join three components. A newly reached target singleton counts as
an existing component for a join. This includes every target
incidence, either orientation, and all signs and distances of integer
addresses. A separator and a repeat add no information. A query
disjoint from the target component only partitions independent
common factors; summing its replies restores those factors.

A fresh vertex has weights $a,b$. If $U/V\ge R$, (4.1) yields
$U$, so a fresh extension gives no summed improvement. If $U=V$,
it yields $2aU$. These statements also hold with the untouched
component factors restored. If a join cannot exist in a particular
line placement, allowing it for a scalar comparison only enlarges an
upper bound; later forcing requires an actual existing edge.
$\square$

**Lemma 4.2 (One active edge and a mixed triple).** Conditional on
a phase, one active edge has the following target-spin joint masses:

| Target position | Zero reply | One reply |
| --- | --- | --- |
| In the pair | $a^2,b^2$ | $\eta,\eta$ |
| Outside the pair | $ac,bc$ | $2a\eta,2b\eta$ |

A single active-zero constraint gives maximal full-law state mass at
most $a^2/2$. A single active-one constraint with at most one further
call gives summed full-law correct mass at most $a\eta$. Two
adjacent active edges with at least one one label, with at most one
further call, give summed full-law correct mass at most $a\eta/2$
for every target position.

Proof. A zero pair has two constant assignments of weights $a^2,b^2$;
a one pair has two opposite assignments, both of weight $\eta$.
An exterior target supplies the independent factor $a$ or $b$.
This proves the table and the zero bound, since $ac<a^2$.

For an internal target on a one pair, its tie can gain only by a
fresh extension, giving $2a\eta$ before the phase factor. A repeat,
separator or query elsewhere leaves at most $\eta$. For an exterior
target, its singleton has weights $a,b$. Joining the tie pair gives
$\max(2a\eta,\eta)=2a\eta$; joining a fresh vertex leaves its
summed majority mass $a$ unchanged, times the one-pair probability
$2\eta$. Other queries only partition that independent factor.
These exhaust the last moves and prove the single-one bound.

For adjacent mixed edges the larger assignments, in left-to-right
vertex order for labels $01,10,11$, are respectively

$$
(\sigma,\sigma,1-\sigma),\quad
(1-\sigma,\sigma,\sigma),\quad
(\sigma,1-\sigma,\sigma).
\tag{4.2}
$$

Their weights are $a^2b=a\eta$, their complementary weights are
$ab^2=b\eta$, and their total is $\eta$. An internal target
has component odds $R$, so a fresh extension cannot increase its
best sum $a\eta$. No other component with a nontrivial constraint
is present; other operations leave at most this sum. For an exterior
target, joining its singleton to the triple gives
$\max(a\eta,a\eta)=a\eta$ by (4.1); joining a fresh
vertex or querying elsewhere also gives at most $a\eta$.
Restore the phase factor $1/2$. Both acquisition orders and all
target positions are included. Early halts obey the same caps by
(2.5), or directly by the displayed masses. $\square$

**Lemma 4.3 (Disjoint zero/one continuation, with all instructions).**
After vertex-disjoint active zero and one pairs, in either acquisition
order, the phase is certified. The cap with at most one further call
is $K=a^2\eta$. Its complete instruction and label rules for
attaining that cap are:

| Target position | Instructions attaining $K$ and their positive-section labels |
| --- | --- |
| In the zero pair | Halt, or make any last actual call; always output $h_\alpha(\sigma)$ |
| In the one pair | Read the joining edge between the two pairs; its replies have unique opposite preferred target spins |
| Outside both pairs | Read the edge joining the target singleton to the zero pair; output target spin $\sigma$ on zero and $1-\sigma$ on one |

In either of the last two rows every alternative instruction, including
an early halt, has correct mass at most $ac\eta$. It therefore
loses at least

$$
K-ac\eta=a\eta(a-c)=a\eta bd\ge g_5.
\tag{4.3}
$$

Proof. The pair weights are $(a^2,b^2)$ and $(\eta,\eta)$.
If the target is in the zero pair, its no-read best full-law mass is
$a^2\eta$. A fresh extension changes its odds $R^2$ to $R^3$
or $R$, both greater than one. A join to the tie pair preserves the
preferred orientation. A repeat, separator or query elsewhere only
partitions common factors. Thus every last call has the same best
summed mass, and the target is uniquely $\sigma$ on each positive
section. Halting with that label also attains it.

For a target in the one pair, no read gives $c\eta/2$. A fresh
extension gives $ac\eta$. A join to the zero pair gives
$a^2\eta$ by (4.1). Every other operation leaves at most
$c\eta/2\le ac\eta$, including a query extending the nontarget
zero pair. These exhaust the moves. For the required join, the zero
pair is constantly $\sigma$ in either heavier four-spin completion.
Each heavier completion has weight $a^3b$, versus complementary
$ab^3$. If the joining reply is $z$, the adjacent vertex of the
one pair is $\sigma\oplus z$, and its other vertex is the
complement. Either target position therefore has unique opposite
preferred values on the two replies. Each best full-law mass is
$a^3b/2=a^2\eta/2$.

For an exterior target the singleton weights are $a,b$. Joining it
to the zero pair gives the conditional best sum $a^2$ on their
combined component; the independent one pair and phase factor give
$a^2\eta$. A join to the tie pair, a fresh edge at the target,
or a query missing the target gives at most $ac\eta$. This last
category includes a join of the two nontarget pairs, which leaves the
target independent. An early halt has exactly $ac\eta$ at best.
On the required join to the zero pair, the heavier target is
$\sigma$ on zero and $1-\sigma$ on one. Its two best full-law
masses are $a^3\eta$ and $a\eta^2$, whose sum is $K$,
using $a^3\eta+a\eta^2=a^2\eta(a+b)$.

Both replies of a new joining edge have positive product weights.
Strictness of $a>b$ gives the stated unique labels. If the required
line join does not exist, only the losing alternatives are available.
Finally (4.3) follows from $a-c=bd$ and $c<1$. Minority and
wrong-phase labels cannot exceed the maxima just computed.
$\square$

**Lemma 4.4 (Disjoint one/one continuation and genuine ties).**
After two disjoint active one pairs, the cap with at most one further
call is $J=2a\eta^2$. If the target is in a pair, every instruction
other than a fresh extension of that pair outside the two pairs has
correct mass at most $\eta^2$, losing

$$
J-\eta^2=d\eta^2=g_1.
\tag{4.4}
$$

The required extension has both replies positive and unique opposite
preferred target spins. For an exterior target, a majority halt or
any last actual call can attain $J$. Its complete maximizing labels
are $\sigma$ on every positive section, except that an active fresh
edge from the target to a vertex outside both pairs and the target
has a unique $\sigma$ choice on zero and a genuine two-spin tie on
one. Every stated spin means the actual label $h_\alpha(s)$.

Proof. Each pair has weights $(\eta,\eta)$ and probability
$2\eta$. For an internal target, no read, a repeat, a separator or
a query missing its component leaves best mass $\eta^2$ after
the phase factor. Joining the two tie pairs also leaves a tie, by
(4.1). A fresh extension of its own pair makes a mixed triple of
weights $a^2b,ab^2$ for either reply. Multiplying the other pair's
probability and phase factor gives best mass $a\eta^2$ on each
reply, hence $J$ in total. Formula (4.2) shows that either vertex
of the original one pair has opposite preferred spins on the two
replies, uniquely since $a>b$. The line geometry of Lemma 4.1
leaves no other improving instruction. This proves (4.4).

For an exterior target the prefix probability is $4\eta^2$ and
its independent majority factor gives full-law best mass $J$.
A call missing the target only partitions independent constraints,
even if it joins the two nontarget components. A join of the target
to a tie pair contributes the same factor $\eta$ to either target
spin on each reply, retaining its strict $a:b$ preference. Repeats
and separators retain it as well. Finally a fresh edge at the target
has weights $(a^2,b^2)$ on zero and $(\eta,\eta)$ on one,
times the two old one-pair probabilities. Its best sum is unchanged,
but its one reply is genuinely tied. These are all last moves.
Wrong-phase labels never maximize a positive certified section.
$\square$

**Corollary 4.5 (Zero/one constraint without another call).** A
specified active zero and active one constraint has individual-state
maximum at most $K$. A repeated edge is contradictory; adjacent edges
give $a\eta/2$; disjoint edges give respectively

$$
a^2\eta,\quad c\eta/2,\quad ac\eta
\tag{4.5}
$$

for the target in the zero pair, in the one pair, or outside both.

Proof. These are the products in Lemmas 4.2–4.3 before making a
further call. The comparisons are $a/2<a^2$, $c<2a^2$ and
$c<a$ from (1.4). $\square$

## 5. Two zero constraints and the last-edge losses

**Lemma 5.1 (Adjacent zeros followed by one).** Suppose two distinct
adjacent active edges have label zero. On a third active one edge the
maximal full-law state mass is at most $a^3\eta$ for every target
position.

Proof. The zero triple is constant with weights $a^3,b^3$ and
total $t\le a^2$. A repeated third edge cannot reply one. A
third edge disjoint from the triple gives maxima

$$
a^3\eta,\quad t\eta/2,\quad at\eta
\tag{5.1}
$$

for target in the triple, in the one pair, or outside both. The
second is at most $a^3\eta$ because $t\le a^2$ and
$a\ge1/2$; the third is at most $a^3\eta$ because $t\le a^2$.
An extension gives four-spin weights $a^3b,ab^3$, whose sum is
$c\eta$. For an internal target, including the new vertex, its
maximum is $a^2\eta/2$; for an exterior target it is
$ac\eta/2\le a^2\eta/2$. These are at most $a^3\eta$.
A single line edge has no remaining incidence with that triple.
A separator cannot produce the required one. $\square$

**Lemma 5.2 (Disjoint zeros: complete final-one table).** Let $E,F$
be disjoint active zero edges, and consider a third active edge $G$
with reply one. The complete full-law maxima, and losses from
$K_0=a^2c\eta$, are bounded as follows:

| Third edge and actual target position | Maximum | Loss from $K_0$ |
| --- | --- | --- |
| Repeat of $E$ or $F$ | $0$ | $K_0>g_3$ |
| Disjoint from both; target in $E\cup F$ | $K_0$ | $0$ |
| Disjoint from both; target in $G$ | $c^2\eta/2$ | $c\eta d/2\ge g_3$ |
| Disjoint from all target incidences | $ac^2\eta$ | $ac\eta bd=g_5$ |
| Extends one pair; target in mixed triple | $ac\eta/2$ | $g_3$ |
| Extends one pair; target in untouched zero pair | $a^2\eta/2$ | $g_4$ |
| Extends one pair; target outside both components | $ac\eta/2$ | $g_3$ |
| Joins the two zero pairs; target internal | $\eta^2/2$ | at least $a^3\eta d\ge g_3$ |
| Joins the two zero pairs; target external | $a\eta^2$ | $a^3\eta d\ge g_3$ |

Thus the only way to avoid a loss of at least one of $g_3,g_4,g_5$
is a disjoint $G$ with target in $E\cup F$. Its unique maximizing
label on this one leaf is $h_\alpha(\sigma)$.

Proof. Each zero pair has constant weights $a^2,b^2$ and total
$c$. A disjoint final one pair has probability $2\eta$, and its
two internal target weights are equal to $\eta$. Multiply the
appropriate target weight, every other component probability and
the phase factor to get the three disjoint entries. Their losses are

$$
\begin{aligned}
K_0-c^2\eta/2&=c\eta(2a^2-c)/2=c\eta d/2,\\
K_0-ac^2\eta&=ac\eta(a-c)=ac\eta bd.
\end{aligned}
\tag{5.2}
$$

The first is at least $g_3$ since $a<1$. On extension the mixed
triple has weights $a\eta,b\eta$ and probability $\eta$.
The untouched zero pair contributes its full factor $c$ when the
target is in the triple, giving $ac\eta/2$. An exterior target
contributes its independent majority factor to $c\eta/2$, giving
the same value. A target in the untouched pair instead contributes
$a^2\eta/2$. Hence

$$
K_0-ac\eta/2=ac\eta(a-1/2)=g_3,
\qquad K_0-a^2\eta/2=a^2\eta(c-1/2)=g_4.
\tag{5.3}
$$

A join forces the two constant pairs to opposite orientations. Both
four-spin completions have weight $a^2b^2=\eta^2$. An internal
target therefore gives maximum $\eta^2/2$, and an external one
gives $a\eta^2$, which dominates it. The smaller loss is

$$
K_0-a\eta^2=a\eta(ac-\eta)=a^3\eta d\ge g_3,
\tag{5.4}
$$

where $ac-\eta=a(c-b)=a^2d$ and $2a^2>c$. Repetition
contradicts the prescribed one; its loss satisfies
$K_0/g_3=2a/d>1$. The listed line incidences are exhaustive by
Lemma 4.1. In the zero-loss entry the target's zero pair has weights
$a^2>b^2$ times common positive factors, proving the unique label.
Every row uses the same original source; none removes a disjoint
component's probability. $\square$

## 6. The full scalar partition of an actual execution

Fix a deterministic initialized row with $q(r)=1$. If it initially
reads, call its first parity $\alpha$, put $\beta=1-\alpha$,
write $E$ for its active edge in phase $\alpha$, and write
$T=v_\alpha$ for that phase's actual target. Let $C_0,C_1$ be
its actual correct masses on first reply zero and one. Continuation
masses always include every subsequent finite leaf within three
calls. Null histories contribute zero.

**Lemma 6.1 (First-one alternatives).** Universally $C_1\le D$.
Unless the actual next instruction reads an edge $H$ of parity
$\alpha$ disjoint from $E$, one has $C_1\le a\eta$ and loses
$D-a\eta=g_1$. In the disjoint case the actual continuations
at $10,11$ have caps $K,J$ respectively, summing to $D$.

Proof. First reply one certifies phase $\alpha$. An immediate halt,
separator or repeat leaves at most one further informative call, so
Lemma 4.2 bounds the sum by $a\eta$. If the second edge is
adjacent, either reply leaves a mixed triple. Each continuation is
at most $a\eta/2$, again totaling at most $a\eta$. If the
second edge is disjoint, Lemmas 4.3–4.4 give $K$ on $10$ and
$J$ on $11$, with independently chosen last addresses allowed.
There is no other parity or edge relation. Finally

$$
D-a\eta=a\eta(a-1+2\eta)=d\eta^2=g_1,
\tag{6.1}
$$

using $1-a=b$. The caps are individual-state joint masses, so
all actual label choices and early halts are included. $\square$

**Lemma 6.2 (First-zero alternatives, both later parities).**
Universally $C_0\le Z$. Define

$$
Q_0=\frac{a^2}{2}+a\eta+K,\qquad
A_0=\frac a2+a^3\eta+\frac{a\eta}{2}.
\tag{6.2}
$$

The complete relevant upper bounds are these:

| Actual zero-subtree alternative | Cap for $C_0$ |
| --- | --- |
| Halt on first zero | $a/2$ |
| Second call of parity $\beta$ | $Q_0$ |
| Second call of parity $\alpha$, halt on $00$ | $a/2+K$ |
| Second call of parity $\alpha$, third call on $00$ of parity $\beta$ | $Q_0$ |
| Second edge $F=E$, third call on $00$ of parity $\alpha$ | $a/2+K$ |
| Second edge $F$ adjacent to $E$, third call on $00$ of parity $\alpha$ | $A_0$ |
| Second edge $F$ disjoint from $E$, third call on $00$ of parity $\alpha$ | $a/2+K_0+K=Z$ |

Their positive deficits satisfy

$$
Z-Q_0=g_2,\qquad Z-A_0=g_3,\qquad
Z-(a/2+K)=K_0>g_3,\qquad Z-a/2>g_3.
\tag{6.3}
$$

Proof. With a first-zero halt no state can exceed its prior $a/2$.
Suppose the actual second call has parity $\alpha$, active edge
$F$ there. Its $01$ section certifies $\alpha$. If $F=E$ this
section is null. If adjacent, its continuation cap is $a\eta/2$
by Lemma 4.2; if disjoint, its cap is $K$ by Lemma 4.3. Thus
$K$ bounds it in every case, for any last call or early halt.

On $00$, an immediate halt has mass at most $a/2$. If a third
call has parity $\alpha$, the final-zero leaf contains the whole
of phase $\beta$. Its individual-state maximum is exactly $a/2$:
that phase's majority label has that mass, and no label exceeds its
prior. At the final-one leaf the cases are as follows. A repeated
second edge leaves only one distinct zero constraint; Corollary 4.5
bounds a subsequent one by $K$, while its $01$ continuation was
null. Adjacent distinct zeros give $a^3\eta$ by Lemma 5.1,
and their $01$ continuation gives $a\eta/2$. Disjoint zeros give
$K_0$ by Lemma 5.2, and their $01$ continuation gives $K$.
These prove the three same-parity rows and the halt-on-$00$ row.

Still with second parity $\alpha$, suppose its $00$ third call
has parity $\beta$. The final all-zero leaf has at least one
active-zero constraint in each phase. By Lemma 4.2 any particular
state has joint mass at most $a^2/2$; extra constraints cannot
increase a state's mass. The final one certifies $\beta$, where
both earlier calls were separators, so its best mass is at most
$a\eta$ from a single one edge. Add the $01$ cap $K$ to get
$Q_0$, regardless of repetition or adjacency in the other phase.

If instead the second call itself has parity $\beta$, its $01$
continuation is one active-one constraint in phase $\beta$ with
one call left, bounded by $a\eta$ in Lemma 4.2. On $00$ each
phase has one active-zero constraint. A third zero, of either
parity, gives individual-state maximum at most $a^2/2$. A third
one certifies its address's phase, where there is a zero and a one
constraint; Corollary 4.5 bounds that leaf by $K$, including
contradictory repeats. Thus this case also gives $Q_0$. If this
$00$ section halts early, its mass is already at most $a^2/2$,
so the same cap still holds. This covers both third parities and
all early halts in the mixed-parity case.

It remains to verify the comparisons, rather than assume the
largest cap. Using $a-a^2=\eta$ and (1.4),

$$
\begin{aligned}
Z-Q_0
&=\eta(1/2-a+a^2c)
=\frac\eta2(b^2+a^2d^2),\\
Z-A_0
&=a\eta\bigl(a(1+c)-a^2-1/2\bigr)
=\frac{a\eta dc}{2}.
\end{aligned}
\tag{6.4}
$$

For the first identity use
$b^2+a^2d^2=1-2a+2a^2c$. For the second, the bracket
equals $dc/2$ after inserting $c=1-2ab$. Also
$K_0/g_3=2a/d>1$. These prove (6.3) and $C_0\le Z$.
Every mixed-phase leaf has used the maximum of four individual
state masses. In particular no two phase maxima were added as one
output. The two actual target vertices in such a calculation remain
$v_\alpha$ and $v_\beta$ in their respective phase alternatives.
$\square$

**Corollary 6.3 (Inherited unrestricted scalar value).** Every eligible
deterministic installed start has correct mass at most $S_3=Z+D$.
The same holds for its initialization average. This upper value and
its unrestricted attainment are inherited from [Three Endpoint,
Theorem 7.1][E3].

Proof. An initial halt gives at most $a/2$. Otherwise add the
actual inequalities $C_0\le Z$ and $C_1\le D$. Finally

$$
Z+D=\frac a2+a^2\eta(2+c)+2a\eta^2
=\frac a2+3a^2\eta+2a(1-a)\eta^2
=S_3.
\tag{6.5}
$$

Average by Lemma 2.3. This derivation is included to expose the
nonnegative deficits needed next; it does not claim a new optimum.
$\square$

## 7. Quantitative margins for all terminal labels

**Lemma 7.1 (Certified-label margins, including ties).** On a positive
terminal acquired cylinder supported in one certified phase, with
$n\le3$ actual calls, a nonmaximizing same-phase label loses at
least $g_6$ in correct mass. A wrong-phase label loses at least
$g_7$. If the two actual target-spin masses are tied, either
same-phase spin label is maximizing and no preference is imposed.

Proof. Adjoin the target singleton if necessary. Let its component
have $v$ vertices and the other constrained components have $w$
vertices in total. Every call introduces at most two vertices, so

$$
v+w\le2n+1\le7.
\tag{7.1}
$$

The two target-spin masses are $1/2$ times a common product of
the other component probabilities times two complementary monomials.
If unequal, their heavier and lighter products have the form
$(ab)^\ell a^s$ and $(ab)^\ell b^s$, where $s\ge1$ and
$2\ell+s=v$. Their difference is at least $db^{v-1}$, since

$$
a^s-b^s=d\sum_{i=0}^{s-1}a^{s-1-i}b^i\ge db^{s-1},
\qquad (ab)^\ell\ge b^{2\ell}.
\tag{7.2}
$$

Each other consistent component has probability at least one
assignment product, hence at least $b$ to the power of its number
of vertices. Therefore the unequal full-law target-state difference
is at least

$$
\frac{db^{v+w-1}}2\ge\frac{db^6}2=g_6.
\tag{7.3}
$$

A positive best-state mass is at least one joint assignment weight,
so is at least $b^{v+w}/2\ge b^7/2=g_7$. A wrong-phase
answer has zero correct mass on this certified cylinder. Equal
complementary products are actual target-spin ties; this reasoning
does not break them. These are absolute joint masses of the original
source, rather than normalized posterior margins. Separators,
repeats and negative or distant placements obey the same vertex
bound. $\square$

**Lemma 7.2 (The mixed-phase zero-leaf margin after the forced
geometry).** If $E,F,G$ are disjoint parity-$\alpha$ edges and
$T\in E\cup F$, the $000$ leaf has unique maximizing label
$h_\beta(\sigma)$. Every other label loses at least $g_1$.

Proof. The four masses there are

$$
\frac a2,\quad\frac b2,\quad
\frac{a^2c^2}{2},\quad\frac{b^2c^2}{2},
\tag{7.4}
$$

with the first two belonging to phase $\beta$. Its reads are
all separators in that phase. In phase $\alpha$ the target is
in one zero pair, and the other two zero pairs contribute $c^2$.
The first mass exceeds the second by $d/2\ge d\eta^2=g_1$.
It exceeds the largest phase-$\alpha$ mass by

$$
\frac{a-a^2c^2}{2}\ge\frac{a-a^2}{2}
=\frac\eta2\ge d\eta^2=g_1,
\tag{7.5}
$$

using $d\eta<1/4<1/2$. Thus every minority or wrong-phase
choice on this mixed leaf has the required loss. $\square$

## 8. Small loss forces actual instructions and labels

**Proposition 8.1 (Quantitative forcing at a deterministic start).**
Fix any original installed table and deterministic start with
$q(r)=1$. If its correct mass $C$ satisfies

$$
\varepsilon:=S_3-C<\rho,
\tag{8.1}
$$

its actual positive-section execution has exactly the following
necessary pattern. It reads $E$ first, then parity-$\alpha$ edges
$F,H$ after zero and one respectively, both disjoint from $E$.
After $00$ it reads parity-$\alpha$ edge $G$ disjoint from
$E,F$, and $T\in E\cup F$. Its $000,001$ successors halt
with labels $h_\beta(\sigma),h_\alpha(\sigma)$.

All remaining instructions and positive terminal labels are specified
by this exhaustive table:

| Target incidence | Prefix $01$ | Prefix $10$ | Prefix $11$ |
| --- | --- | --- | --- |
| $T\in E$ | Optional Halt or any last read, always spin $\sigma$ | Required join of $E,H$, with opposite target labels from Lemma 4.3 | Required fresh extension of $E$ outside $E\cup H$, with opposite target labels from Lemma 4.4 |
| $T\in F\cap H$ | Required join of $E,F$, with opposite target labels from Lemma 4.3 | Optional Halt or any last read, always spin $\sigma$ | Required fresh extension of $H$ outside $E\cup H$, with opposite target labels from Lemma 4.4 |
| $T\in F\setminus H$ | Required join of $E,F$, with opposite target labels from Lemma 4.3 | Required join of $T$ to zero pair $H$, target spins $\sigma,1-\sigma$ on zero, one | Optional Halt or any last read, with exactly Lemma 4.4's exterior-target label and tie rule |

Every spin in the table means its actual label $h_\alpha(s)$.
Every required edge is an actual line edge that must exist. Both
replies at every required third read have positive source mass;
every positive third-reply successor must immediately Halt. Optional
calls are also actual paid calls, with the stated labels on every
positive reply. Null or inconsistent histories retain arbitrary
instructions and outputs.

Proof. An initial halt loses at least $S_3-a/2\ge K_0>g_3$
and cannot satisfy (8.1). Thus the root actually reads. Both first
replies have positive masses $1-\eta,\eta$. Lemmas 6.1–6.2 give
nonnegative deficits

$$
0\le Z-C_0\le\varepsilon<\rho,\qquad
0\le D-C_1\le\varepsilon<\rho.
\tag{8.2}
$$

Any first-one halt, second separator, repeat or adjacent edge loses
$g_1$ by Lemma 6.1. Thus its actual instruction reads a same-parity
disjoint $H$. Lemma 6.2 excludes a first-zero halt, second parity
$\beta$, repeated or adjacent same-parity second edge, by the
losses $g_2,g_3$ or $K_0>g_3$. Its actual instruction must read
a same-parity disjoint $F$. On $00$, a halt loses $K_0$, and
a parity-$\beta$ third call loses $g_2$. Hence this actual
instruction reads a parity-$\alpha$ edge $G$.

At this point the zero-subtree caps for $000,001$, and the whole
$01$ continuation are respectively $a/2,K_0,K$. They sum to
$Z$ and each bounds its actual term. Likewise $K,J$ bound the
$10,11$ continuations and sum to $D$. Every one of these five
nonnegative deficits is consequently less than $\rho$. Lemma 5.2
now excludes every repeat, extension, join and wrong target incidence
at $001$, with losses at least $g_3,g_4$ or $g_5$. Thus $G$
is disjoint from $E,F$ and $T\in E\cup F$.

Both $G$ replies are positive: in phase $\alpha$ the disjoint
zero pairs and either completion of the new pair have positive
product weights. The $000$ section also contains all of phase
$\beta$. Lemma 2.3 forces actual Halt successors there.
Lemma 7.2 forces label $h_\beta(\sigma)$ on $000$; any other
label would make its deficit at least $g_1$. On $001$ the phase
is certified and the target lies in a zero pair, whose preferred
spin is uniquely $\sigma$. Lemma 7.1 forces its actual label:
a nonmaximizer loses at least $\min(g_6,g_7)\ge\rho$.

It remains to force the continuations, with no inference from equal
scalar caps to instruction identity. On $01$ the zero pair is $E$
and the one pair is $F$. On $10$ the zero pair is $H$ and the
one pair is $E$. If the target belongs to a zero pair, Lemma 4.3
allows an actual halt or any last call, and uniquely requires
$\sigma$ on every positive terminal section. Otherwise that lemma
forces the specified actual join: every other instruction loses
at least $K-ac\eta\ge g_5$. This includes early halts,
separators, repeats, fresh extensions and all queries among
nontarget components. The joins' exact heavier completions give
their stated target labels.

On $11$ both $E,H$ are one pairs. For an internal target,
Lemma 4.4 forces a fresh extension of its own pair outside their
union: every other instruction, including a halt or join of the
two tie pairs, loses $g_1$. Its two heavier mixed triples give
opposite unique labels. For an exterior target, the same lemma
lists every permitted actual halt or call and the genuine tie at
a fresh target-neighbor one reply. It imposes no artificial
preference on that tie.

For precision, every optional instruction in these cases has scalar
best sum equal to its continuation cap, by Lemmas 4.3–4.4. The
required joins and extensions have that same equality. Hence the
deficit of such a continuation is the sum of its nonnegative
terminal-label deficits. Lemma 7.1 forces each actual terminal
label to maximize; a nonmaximizer cannot be compensated on a
different leaf. This justifies all optional-read labels as well
as the mandatory ones. All terminal sections other than $000$
are phase-certified, so Lemmas 7.1–7.2 cover every label case.

Every required prefix and both replies of its required new edge
have consistent finite spin completions in phase $\alpha$; all
their assignment factors are positive. Lemma 2.3 consequently
forces Halt after each actual third call. This proof concerns the
original rows reached at each prefix, with their fixed instructions;
no occurrence was substituted for a state. The three target
incidences exhaust $T\in E\cup F$ because $E,F$ are disjoint
and $H$ is disjoint from $E$. $\square$

## 9. Fixed-successor closure and the uniform bound

**Lemma 9.1 (Six distinct Read rows in all incidence cases).** The
actual pattern of Proposition 8.1 requires at least six distinct
installed Read rows, allowing arbitrary sharing across branches and
execution depths.

Proof. Name the actual root $r$, its second Read successors
$r_0,r_1$, and its required third Read at $00$ by $r_{00}$.
Their literal edges are $E,F,H,G$ respectively. Select two further
mandatory third-read occurrences according to the target case.
Their pairwise state distinctions are proved next, rather than
assumed from these names.

If $T\in E$, select $r_{10}$ at the join $P$ of $E,H$ and
$r_{11}$ at a fresh extension $W$ of $E$ outside $E\cup H$.
The edge $P$ meets $H$ and $W$ adds a vertex outside $H$,
so they differ. Both meet $E$, whereas $G$ is disjoint from $E$.
Thus $r_{00},r_{10},r_{11}$ are pairwise distinct by their
literal instructions. If $r_0=r_1$, their fixed zero successors
would identify $r_{00}$ with $r_{10}$, impossible because
$G\ne P$. Therefore $r_0\ne r_1$, even if $F,H$ share a
literal address.

If $T\in F\cap H$, select $r_{01}$ at the join $P$ of
$E,F$ and $r_{11}$ at a fresh extension $W$ of $H$ outside
$E\cup H$. The edge $P$ meets $E$, while $W$ and $G$
are disjoint from $E$. Hence $P\ne W$ and $P\ne G$.
The only possible equality among third literals is $G=W$.
Even then $r_{00}\ne r_{11}$: their zero replies are both
positive, and their fixed zero successors must Halt respectively
with $h_\beta(\sigma)$ and a phase-$\alpha$ label. One
fixed successor row cannot have both labels. Thus these are three
distinct actual rows even with equal literals. If $r_0=r_1$,
their literal instructions require $F=H$, and their fixed one
successors would identify $r_{01}$ with $r_{11}$, contradicting
$P\ne W$. This again proves $r_0\ne r_1$.

If $T\in F\setminus H$, select $r_{01}$ at the join $P$
of $E,F$ and $r_{10}$ at the join $W$ of $T$ to $H$.
The edge $W$ is disjoint from $E$ and meets $F$ at $T$.
In contrast $P$ meets $E$, and $G$ is disjoint from both
$E,F$. Thus the three third literals are pairwise different.
Here $F$ contains $T$ and $H$ does not, so their literal
instructions themselves give $r_0\ne r_1$.

To finish, exclude every identification across depths. In each
case $E$ differs from $F,H$ because those edges are disjoint
from it, so $r$ differs from both second rows. Every selected
third row has both replies positive, and both fixed successors
Halt. Each second row has at least one fixed Read successor:
use $r_{00}$ for $r_0$, and a mandatory third read after
$10$ or $11$ for $r_1$. A selected third row therefore
cannot equal either second row: on that same reply its fixed
successor would have to be both a Read and a Halt. It cannot
equal $r$, whose two successors Read. We have one root, two
distinct second rows and three distinct third rows, with all
cross-depth identifications excluded. Extra optional rows and
arbitrary sharing elsewhere cannot reduce these six. $\square$

**Lemma 9.2 (Three distinct Halt rows).** The same pattern forces
three distinct installed Halt rows, separate from all Read rows.

Proof. Positive $000$ and $001$ sections require respectively
$h_\beta(\sigma)$ and $h_\alpha(\sigma)$. If $T\in E$,
the required join on $10$ has opposite unique target labels;
if $T\in F$, use instead the required join on $01$.
Both replies are positive, so a Halt with
$h_\alpha(1-\sigma)$ is also required. The three actual
four-state labels differ. A fixed Halt row has one label and
cannot supply two of them; a Read row cannot be a Halt row.
This counts three rows of the original $\mathcal K$, without discarding
duplicate or unvisited rows. $\square$

**Proof of Theorem 3.2.** For any deterministic eligible start in
a table with at most eight rows, assume its correctness exceeded
$S_3-\rho$. Proposition 8.1 would force the pattern whose
actual-row closure is proved in Lemmas 9.1–9.2. That pattern
requires $|\mathcal K|\ge6+3=9$, a contradiction. Thus every such start
satisfies $C(r)\le S_3-\rho$.

For the original measurable initialization, Lemma 2.3 gives the
same $q(r)=1$ condition on every positive cell, and hence

$$
q_3-L_3=\sum_rw_rC(r)
\le\sum_rw_r(S_3-\rho)=S_3-\rho.
\tag{9.1}
$$

The constant is the same for every deterministic start. There is
no atomic-seed conditioning, new coin or changed initialization
law. Zero-weight cells contribute zero, while their installed rows
are still counted. The contradiction uses only positive actual
sections and fixed successors; it neither removes null cycles nor
imposes an all-input cap. Taking the supremum over all original
tables with $|\mathcal K|\le m\le8$ preserves the explicit constant,
proving the first inequality of (3.4) without needing attainment.

For the simpler bound put $L=d^2b^7/2$. From
$a\ge1/2$, $c\ge1/2$ and $\eta\ge b/2$,

$$
g_1\ge\frac{db^2}{4},\quad
g_2\ge\frac{b^3}{4},\quad
g_3\ge\frac{db}{16},\quad
g_4\ge\frac{d^2b}{16},\quad
g_5=a^2cb^2d\ge\frac{db^2}{8}.
\tag{9.2}
$$

The respective ratios of these five lower bounds to $L$ are

$$
\frac1{2db^5},\quad \frac1{2d^2b^4},\quad
\frac1{8db^6},\quad \frac1{8b^6},\quad
\frac1{4db^5}.
\tag{9.3}
$$

Each exceeds one because $0<d<1$ and $0<b<1/2$.
For the remaining terms,

$$
\frac{g_6}{L}=\frac1{db}>1,\qquad
\frac{g_7}{L}=\frac1{d^2}>1.
\tag{9.4}
$$

Every term therefore dominates $L>0$, so does their minimum.
This proves the whole theorem. Strict positivity is asserted for
each fixed allowed parameter only. $\square$

## 10. Actual lower points and the unchanged exact target

**Convention 10.1 (Inherited values and literal table notation).**
The existing [Installed Three, Sections 4–10][I3] owns

$$
\begin{gathered}
F=\frac a2+a\eta(1+c+c^2),\qquad
V=\frac a2+a\eta(3/2+a^2),\\
W=Z+a\eta=S_3-d\eta^2,\qquad
X_\star=S_3-\frac{ad\eta c}{2}.
\end{gathered}
\tag{10.1}
$$

The following four controllers and masses are inherited actual
lower realizations. They are included to identify exactly the lower
sides retained with the new upper bound. None is asserted to attain
$S_3-\rho$. Each displayed table is a separate installation.
Write $L(k)=\operatorname{Read}(2(j+k))$ for a fixed integer
literal chosen using public $j$, and use fixed Halt rows
$Z_H=\operatorname{Halt}(h_1(\sigma))$,
$P=\operatorname{Halt}(h_0(\sigma))$ and, when listed,
$Q=\operatorname{Halt}(h_0(1-\sigma))$.
There is no runtime address arithmetic. A dash denotes no update
at a Halt. Initialize constantly at the first row, on the given
unchanged seed space; each instruction can take duration one.

**Proposition 10.2 (Five- and six-row lower realizations).** The
following complete tables attain $F$ and $V$ respectively, with
their actual full-source terminal masses and costs.

| Row | Five-row instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $L(2)$ | $S$ | $P$ |
| $S$ | $L(4)$ | $U$ | $P$ |
| $U$ | $L(6)$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $01$ | $h_0(\sigma)$ | $c\eta$ | $ac\eta$ | $2$ |
| $001$ | $h_0(\sigma)$ | $c^2\eta$ | $ac^2\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+c^3)/2$ | $a/2$ | $3$ |

| Row | Six-row instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $L(1)$ | $S$ | $P$ |
| $S$ | $L(0)$ | $U$ | $Q$ |
| $U$ | $L(3)$ | $Z_H$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $01$ | $h_0(1-\sigma)$ | $\eta/2$ | $a\eta/2$ | $2$ |
| $001$ | $h_0(\sigma)$ | $t\eta$ | $a^3\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+tc)/2$ | $a/2$ | $3$ |

Proof. In phase zero the five-row table queries the three
mutually disjoint pairs beginning at $j+2,j+4,j+6$, all exterior
to target $j$. Their zero and one probabilities are $c,2\eta$.
Thus the first-three-record source masses follow by multiplying
preceding zero factors, the one probability and the phase factor.
The independent target gives factor $a$ for correctness. In phase
one all calls are paid separators, and $000$ succeeds precisely
on $S_0=\sigma$, giving $a/2$. The additional phase-zero
$000$ mass is an error for that fixed output. The source masses
sum to one using $\eta(1+c+c^2)=(1-c^3)/2$, and the correct
sum is $F$. Its exact cost law is

$$
\mathbb P(N=1)=\eta,\quad \mathbb P(N=2)=c\eta,\quad
\mathbb P(N=3)=1-\eta(1+c),\quad
\mathbb E N=3-\eta(2+c).
\tag{10.2}
$$

For the six-row table the phase-zero root pair is
$\{j+1,j+2\}$, exterior to the target. After zero it queries
$\{j,j+1\}$, introducing the target. On $01$ the heavier
triple in order $j,j+1,j+2$ is
$(1-\sigma,\sigma,\sigma)$, weight $a^2b=a\eta$,
with complementary weight $ab^2$. Its phase-weighted source and
correct masses are therefore $\eta/2,a\eta/2$, with the
displayed minority target output. On $001$ the first triple is
constant, probability $t$, and the disjoint last pair
$\{j+3,j+4\}$ disagrees, probability $2\eta$. Its source
mass is $t\eta$, and correctness requires the triple constantly
$\sigma$, giving $a^3\eta$. The $1$ mass uses root-target
independence; $000$ succeeds only in phase one. Normalization is

$$
\eta+\eta/2+t\eta+(1+tc)/2
=3\eta/2+(1+t)/2=1.
\tag{10.3}
$$

The correct sum is $V$. Its exact costs are

$$
\mathbb P(N=1)=\eta,\quad\mathbb P(N=2)=\eta/2,\quad
\mathbb P(N=3)=1-3\eta/2,\quad
\mathbb E N=3-5\eta/2.
\tag{10.4}
$$

Both tables halt on every formal binary input within three calls.
Their installed costs include all output rows. Equations (1.2)
verify both actual endpoints, and $\sigma$ verifies both biases.
Constant initialization leaves every given independent seed law
unchanged. $\square$

**Proposition 10.3 (Seven-row lower realization).** This complete
table attains $W$:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $L(2)$ | $S$ | $P$ |
| $S$ | $L(0)$ | $A_0$ | $B$ |
| $A_0$ | $L(4)$ | $Z_H$ | $P$ |
| $B$ | $L(1)$ | $Q$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $1$ | $h_0(\sigma)$ | $\eta$ | $a\eta$ | $1$ |
| $000$ | $h_1(\sigma)$ | $(1+c^3)/2$ | $a/2$ | $3$ |
| $001$ | $h_0(\sigma)$ | $c^2\eta$ | $a^2c\eta$ | $3$ |
| $010$ | $h_0(1-\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |
| $011$ | $h_0(\sigma)$ | $c\eta/2$ | $a^2\eta/2$ | $3$ |

Proof. In phase zero its root pair starts at $j+2$ and is
exterior to target $j$. After zero it reads the disjoint target
pair beginning at $j$. On $00$ the last pair beginning at $j+4$
is disjoint from both. Their masses are the indicated products.
On $01$ the last edge $\{j+1,j+2\}$ joins the first two
pairs. For joining replies zero and one the heavier completions
in order $j,j+1,j+2,j+3$ are

$$
(1-\sigma,\sigma,\sigma,\sigma),\qquad
(\sigma,1-\sigma,\sigma,\sigma).
\tag{10.5}
$$

Each has weight $a^3b$, complement $ab^3$, giving whole
source mass $c\eta/2$ and correct mass $a^2\eta/2$.
The displayed labels are the actual target spins. Phase one sees
only separators, and the all-zero output succeeds there with mass
$a/2$. The source masses normalize by
$\eta(1+c+c^2)+(1+c^3)/2=1$; the correct sum is
$a/2+a^2c\eta+a^2\eta+a\eta=Z+a\eta=W$.
All formal paths halt, with

$$
\mathbb P(N=1)=\eta,\qquad \mathbb P(N=3)=1-\eta,
\qquad\mathbb E N=3-2\eta.
\tag{10.6}
$$

There are four Read and three Halt rows. Both target endpoints,
both biases and the unchanged seed are checked as in Proposition
10.2. $\square$

**Proposition 10.4 (Eight-row lower realization).** This complete
table attains $X_\star$:

| Row | Instruction | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $L(1)$ | $R_0$ | $R_1$ |
| $R_0$ | $L(0)$ | $A_0$ | $Q$ |
| $R_1$ | $L(-1)$ | $P$ | $B$ |
| $A_0$ | $L(3)$ | $Z_H$ | $P$ |
| $B$ | $L(-2)$ | $Q$ | $P$ |
| $Z_H$ | $\operatorname{Halt}(h_1(\sigma))$ | — | — |
| $P$ | $\operatorname{Halt}(h_0(\sigma))$ | — | — |
| $Q$ | $\operatorname{Halt}(h_0(1-\sigma))$ | — | — |

| Record | Output | Source mass | Correct mass | Calls |
| --- | --- | --- | --- | --- |
| $01$ | $h_0(1-\sigma)$ | $\eta/2$ | $a\eta/2$ | $2$ |
| $001$ | $h_0(\sigma)$ | $t\eta$ | $a^3\eta$ | $3$ |
| $000$ | $h_1(\sigma)$ | $(1+tc)/2$ | $a/2$ | $3$ |
| $10$ | $h_0(\sigma)$ | $c\eta$ | $a^2\eta$ | $2$ |
| $110$ | $h_0(1-\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |
| $111$ | $h_0(\sigma)$ | $\eta^2$ | $a\eta^2$ | $3$ |

Proof. Its zero subtree is precisely the six-row table's zero
subtree with the same first edge and target. Proposition 10.2
proves those first three records and their masses. On first one
the root pair $\{j+1,j+2\}$ is disjoint from target pair
$\{j-1,j\}$. On $10$ their one/zero constraints give source
mass $c\eta$ and majority-target mass $a^2\eta$.
On $11$ the last edge $\{j-2,j-1\}$ freshly extends the
target pair. The heavier local triples in order $j-2,j-1,j$ are

$$
(\sigma,\sigma,1-\sigma),\qquad
(\sigma,1-\sigma,\sigma)
\tag{10.7}
$$

for final replies zero and one. Each has weight $a^2b$, versus
complement $ab^2$. Multiplying the independent root-one
probability $2\eta$ and phase factor gives source mass
$\eta^2$ and correct mass $a\eta^2$ on each leaf, with
the displayed target labels.

The first-one source mass is $c\eta+2\eta^2=\eta$, and
its correct mass is $D$. The zero subtree has source mass
$1-\eta$ by (10.3), and correct mass
$Z_V=a/2+a\eta/2+a^3\eta$. Hence the full law normalizes.
Moreover

$$
Z-Z_V=a\eta\bigl(a(1+c)-1/2-a^2\bigr)
=\frac{ad\eta c}{2},
\tag{10.8}
$$

so its correct sum is $Z_V+D=X_\star$. It has five Read and
three Halt rows, and halts on every formal path within three calls.
Its exact paid costs are

$$
\mathbb P(N=2)=\eta(c+1/2),\quad
\mathbb P(N=3)=1-\eta(c+1/2),\quad
\mathbb E N=3-\eta(c+1/2).
\tag{10.9}
$$

In particular $L(-1),L(-2)$ are actual charged integer calls,
including their negative values. Phase one still sees only paid
separators. The target and seed remain those in (1.2) and
Definition 2.1 for either $j$ and either bias. $\square$

**Corollary 10.5 (Updated valid middle-budget bounds).** For every
declared parameter, endpoint and unchanged independent seed,

$$
\begin{aligned}
\max(F,V)&\le C_6\le S_3-\rho,\\
W&\le C_7\le S_3-\rho,\\
\max(W,X_\star)&\le C_8\le S_3-\rho,
\qquad C_6\le C_7\le C_8.
\end{aligned}
\tag{10.10}
$$

The inherited exact low values are
$C_1=C_2=a/2$, $C_3=a/2+a\eta$,
$C_4=a/2+a\eta(1+c)$ and $C_5=F$; for $m\ge9$ the
inherited value is $C_m=S_3$. All exact $C_m$ are attained
and independent of the unchanged seed law by [Installed Three,
Theorems 10.1–10.2][I3]. That finite-menu theorem preserves
actual rows and successors and is separate from the proof of
the explicit upper gap.

Proof. The lower tables are Propositions 10.2–10.4, and every
smaller table is allowed at larger installed budgets. The upper
bound is Theorem 3.2. Class inclusion proves monotonicity.
The assertions of exact inherited values and attainment are the
stated results of Installed Three; they are not new conclusions
of the quantitative forcing argument.

For completeness, the full-range comparisons between the lower
points, with their original ownership, are

$$
\begin{aligned}
S_3-F&=d\eta^2(3-2\eta),\\
V-F&=\frac{a\eta d}{4}(2-3d-d^3),\\
W-F&=2d\eta^2(1-\eta)>0,\\
W-V&=ad\eta c/2>0,\\
X_\star-W&=\frac{ad\eta}{2}(1-2a^2).
\end{aligned}
\tag{10.11}
$$

To verify the first identity expand
$1+c+c^2=3-6\eta+4\eta^2$ and use $a^2-a=-\eta$.
For the second, subtract the definitions to get
$a\eta(1/2+a^2-c-c^2)$; substituting
$a=(1+d)/2,c=(1+d^2)/2$ makes the bracket
$d(2-3d-d^3)/4$. The third subtracts $d\eta^2$ from
the first deficit. The fourth is (10.8), since
$W=Z+a\eta$ and $V=Z_V+a\eta$. Finally
$X_\star-W=d\eta(\eta-ac/2)$ and
$\eta-ac/2=(a/2)(2b-c)=(a/2)(1-2a^2)$.
These compare actual attainable values and do not optimize the
unevaluated middle-budget classes. $\square$

**Open Problem 10.6 (The exact original target remains open).**
Determine the exact attained $C_6,C_7,C_8$ throughout every
fixed $0<p<1$, $p\ne1/2$, for both actual original $H_0,H_1$,
the same arbitrary unchanged independent seed law, and exactly
the complete runtime interface in Definition 2.1 under almost-sure
$q_3=1$. Completion requires upper bounds for every original
actual table, matched by complete common-source actual attainers
for every winning parameter branch. The possible equations

$$
C_6=\max(F,V),\qquad C_7=W,\qquad
C_8=\max(W,X_\star)
\tag{10.12}
$$

are neither assumed nor proved. The inherited lower points need
not exhaust the finite menu. No branch of this exact optimization
task is settled merely by (10.10), and $\rho$ has no asserted
matching attainer. Every candidate must respect one actual
installed instruction and both fixed successors at every reaching
positive section. Equal scalar values do not imply instruction
identity; equal literals need not be equal rows. Early stops,
minority and wrong-phase labels, all address geometries, unused
rows and exceptional null cycles remain in the upper-bound class.

## 11. Source correspondence and limits

**Attribution 11.1 (Exact mathematical ownership).** The inherited
results below belong to the six cited project volumes. Citations
refer to those volumes' stated results; their nested references are
not additional premises of this volume.

| Owning project volume and result | Exact correspondence in this source |
| --- | --- |
| [Original][O], Proposition 2.1, (2.2), Definition 9.1, (9.4), Sections 3 and 8–11 | The stationary joint law and both actual endpoint indices in (1.1)–(1.2); full paid arbitrary-address contract; finite acquired sections and complementary-product mechanism in Sections 2 and 4; zero-record and overlapping one-read results retain their ownership |
| [Paid Risk][P], Sections 1–5 | The same original source, return/error convention, terminal masses and one-read return-mass envelope with its seed-event criterion; its paid-probe/local-block family is unchanged |
| [Two Endpoint][E2], Theorem 6.1, Definition 8.1, Lemma 8.2 and Theorem 8.5 | Unrestricted two-read optimum, literal complete-controller semantics, finite initialization averaging and inherited three/six-row minima; Sections 1–2 here retain exactly that model |
| [Two Installed][I2], Theorems 6.1 and 10.1, Section 9 | At-most-two-read-row cap and exact two-read installed frontier; their actual realizations and one-read overlaps are inherited, without a new optimization claim here |
| [Three Endpoint][E3], Lemmas 3.1–3.5, 4.1–4.2 and 5.1–5.2, Theorem 7.1 | Component/orientation calculus, mixed and disjoint continuation caps, two-zero last-edge cases and $Z,D,S_3$ in Sections 3–6 here; their ordinary products are exposed for the quantitative proof, with ownership retained |
| [Three Endpoint][E3], Lemmas 10.1–10.3, Proposition 11.1, Lemma 12.1, Definition 12.2 and Theorem 12.4 | All optimal-policy geometries, optional calls and exterior-target tie; actual successor-closure obstruction, nine-row table and minimum $M_3=9$. Sections 8–9 quantify forcing before using that inherited closure mechanism |
| [Installed Three][I3], Theorem 5.4, Corollary 5.5, Sections 6–9, Theorems 10.1–10.2 and Corollary 10.3 | Exact $C_1$–$C_5$, exact five-row deficit, actual $F,V,W,X_\star$ lower tables and costs, nine-row tail, row-preserving finite menu, seed-independent attainment and qualitative strict gaps. Section 10 retains those values, realizations and exact remaining optimization target |

These are `repo-derived`, source-relative ordinary results. The
quantitative contribution here is the explicit all-competitor stability
threshold of seven losses (3.2), beyond Installed Three's qualitative
finite-attainment argument. Sections 4–9 give the complementary-product
calculations, both-parity scalar partition, absolute terminal-label
margins with all labels and ties, exhaustive strict-loss accounting,
quantitative forcing and every target-incidence sharing case.
Fixed-successor closure and initialization averaging give the uniform
same-seed conclusion; the seven-term comparison gives the simpler
positive bound. Existing scalar identities, low-budget optima, lower
tables, finite-menu theorem and equality obstruction remain attributed.
No external literature search or exhaustive originality claim is
asserted. The mathematical evidence is the ordinary proofs in this
volume.

**Boundary 11.2 (Preserved competitors and excluded conclusions).**
All universal bounds retain the original almost-sure competitor
class, including exceptional source/seed paths, unused rows,
duplicate rows, null cycles and arbitrary actual integer addresses.
The four inherited lower tables additionally halt on every formal
binary input; that stronger property of those constructions does
not narrow the universal comparison. Every actual call remains
paid. Their displayed expected costs are attained costs of those
tables, with no expected-cost optimality assertion.

The result does not evaluate the $q_3<1$ frontier, larger-read
optima, other runtime memory interfaces, fair or endpoint
parameters, physical storage, code size, writes, energy, timing,
empirical learning or general neural systems. Four-state
classification supplies no visible-bit Brier theorem. [Original,
Open Problem 6.4][O]'s whole-domain harmonic/Brier attainment
and separation problem is unchanged. No broader research-goal
completion follows from the explicit installed gap.

There is no uniform positive gap asserted at the excluded limits.
Indeed $\rho\le g_1=d\eta^2$ tends to zero at fairness,
and $\rho\le g_7=b^7/2$ tends to zero as $p$ tends to
either endpoint. Positivity in (3.4) has precisely the fixed-parameter
scope stated there. The evidence ceiling is the ordinary proofs
in this source: no mathematical execution, enumeration, experiment,
new test, formal compilation, kernel verification or digestion
result is used or claimed.

[O]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[P]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md
[E2]: FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md
[I2]: FIB_TWO_READ_INSTALLED_STATE_RISK_FRONTIER.md
[E3]: FIB_THREE_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md
[I3]: FIB_THREE_READ_INSTALLED_STATE_RISK_FRONTIER.md

## 追加锚（本行以下为增补区）
