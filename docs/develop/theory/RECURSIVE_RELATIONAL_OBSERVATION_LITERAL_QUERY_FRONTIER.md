# Literal current queries on complete acquired origin-code fibers

## 1. The complete entry and its actual histories

**Assumption 1.1 (the native retained-origin contract).** Use [NAR,
Assumption 16.1 and Reuse 16.2][NAR], including its initial acquisition,
complete early handoff, export and discard, and later stationary capture.
Thus $D,H\ge0$, $r=2^D$, $q=H+1$, $I=\{0,\ldots,r-1\}$,
$\lambda_0\in\{0,1\}$, and $W_D=(w_j)_{j\in I}$ is the ordered
list of depth-$D$ words. The original sources and their continuations are

$$
X_a=\mathcal B_D[(T_{jq+a_j})_{j\in I}],\qquad
Y_h=\rho^\ell X_a=\mathcal B_D[(T_{n_j(h)})_{j\in I}],\qquad
n_j(h)=jq+a_j+\ell,
\tag{LQF.1}
$$

where $a\in\{0,\ldots,H\}^I$, $\ell\in\mathbb N$, $\ell\ge\lambda_0$ and
$h=(a,\ell)$. Here $T_n=\rho^n\alpha$ and $\mathcal B_D$ is the
complete ordered binary skeleton. Each alternative history has its own
one fixed original source and its own pure-$\rho$ continuation.

An arbitrary installed encoder $e$ is a function on this finite age cube.
It is computed from the genuinely acquired initial literal row, before
the displayed set and lag are chosen. The supplied clock formula
$c(T_n)=n$ makes this possible. Its label is the entire surviving
source-bearing state after discard. A source-dependent table selection,
pointer, clock, log, epoch or controller state is not additional free
information. Installed tables common to all sources are allowed.

Fix a nonempty public menu of nonempty displayed sets, and a received
entry $\eta=(S,c,V)$, where $S$ belongs to that menu. Put
$Q_S=\{w_j:j\notin S\}$. The datum $V$ is the entire acquired
$R_{Q_S}$ row: literal exterior, labels, brackets, reached and absent
cut guards, and the full equality and disequality partition of hidden
subtrees. It supplies no hidden values or cross-row comparison.

Only a fresh original-root literal $\mathsf{Read}(p)$ on the stationary
current $Y_h$ is permitted. Its replies are
$\bot,\alpha,\beta,\mathsf b$, meaning absent, the two leaves and
branch. Every finite word is legal; every invocation costs one call,
including absence, repetition and a root query. Word lengths count
actual letters, including the whole prefix $w_j$. Local computations
and storage are unrestricted in the three prices below. There is no
update, reroot, old-source reread, subtree port or age oracle.

**Definition 1.2 (the actual entry fiber and local target).** Define

$$
\mathscr H_\eta=
\{(a,\ell):a\in\{0,\ldots,H\}^I,\ \ell\ge\lambda_0,
\ e(a)=c,\ R_{Q_S}(Y(a,\ell))=V\},
\qquad \tau(a,\ell)=\ell.
\tag{LQF.2}
$$

A locally correct controller is one deterministic controller, with this
entry and the common installation, that terminates with $\tau(h)$ on
every $h\in\mathscr H_\eta$. Its choices depend only on the acquired
entry and preceding actual replies. Distinct sources with the same lag
remain distinct members of the fiber. A terminal set need only have
constant $\tau$; it need not contain one history.

The principal theorems concern attained entries, meaning
$\mathscr H_\eta\ne\varnothing$. An empty set is an inconsistent
entry, not a recovery impossibility on an actual source. Unless stated
otherwise, all subsequent subsets of $\mathscr H_\eta$ are nonempty.

**Lemma 1.3 (finite histories from an entire acquired row).** For an
attained entry, parse each displayed literal subtree and put
$z_i=c(V|_{w_i})-iq$ for $i\in S$. Then

$$
\mathscr H_\eta=
\{(a,\ell):e(a)=c,\ \ell\ge\lambda_0,
\ a\in\{0,\ldots,H\}^I,
\ a_i+\ell=z_i\ (i\in S)\}.
\tag{LQF.3}
$$

This is equality of actual complete-row fibers. In particular, for any
fixed $i_*\in S$,

$$
\max(\lambda_0,z_{i_*}-H)\le\ell\le z_{i_*},\qquad
1\le|\mathscr H_\eta|\le q^r.
\tag{LQF.4}
$$

The cube and installed encoder determine a finite enumeration of the
whole joint set, without being told the actual lag.

Proof. For an actual history the displayed subtree is
$T_{iq+a_i+\ell}$, so its clock gives the stated equations. Conversely,
compare any candidate satisfying those equations with one history
attaining $\eta$. The displayed literal subtrees agree, because equal
exponents give equal $T_n$. Every depth-$D$ cut position is reached,
even when its filling is a leaf. At different slots the exponent bands
$[jq+\ell,jq+H+\ell]$ are disjoint, since $q=H+1$. The hidden
partition is therefore discrete in both histories. The skeleton, hole
addresses, all remaining labels and brackets, and all guards agree.
This is precisely the complete-row equality supplied by NAR (16.6),
not an inference from scalar equality for arbitrary rows. It proves
the reverse inclusion in (LQF.3).

For each cube point $a$, the one equation at $i_*$ forces
$\ell=z_{i_*}-a_{i_*}$; test its legality, code and all remaining
equations. This enumerates at most $q^r$ histories and proves (LQF.4).
For an arbitrary proposed row, first check its full skeleton, displayed
literals and hidden partition, or compare each constructed candidate's
entire row directly with $V$. If no candidate passes, report
inconsistency. Scalar checks alone do not certify such an input.
$\square$

## 2. All legal words, their reply cells and their literal lengths

**Definition 2.1 (the supplied atomic reply functions).** Use the
all-word formulas of [SLH, proof of Theorem 6.2 and §6.3][SLH], and
the $E,P_t,S_t$ notation and shortest words of [AOF, Definition
8.2][AOF]. For an age $n\ge0$ their replies are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
E&\text{never}&n=0&n=1&n\ge2\\
P_t\ (t\ge2)&n<t&n=t&n=t+1&n\ge t+2\\
S_t\ (t\ge2)&n<t&\text{never}&n=t&n\ge t+1.
\end{array}
\tag{LQF.5}
$$

These are functions realized by actual words, not new permitted tests.
$E$ is the empty suffix. A nonempty suffix $v$ of weight
$w(v)=\#L(v)+2\#R(v)$ gives $P_{w(v)}$ when it ends in $R$,
and $S_{w(v)+1}$ when it ends in $L$. The final-edge guard matters:
an $L$-ending word at $n=w(v)$ is absent, not alpha. This is the
existing guarded atomic formula, including ages zero and one.

**Theorem 2.2 (complete native experiment and length characterization).**
On any attained $\eta$, every original-root query has exactly one of
the following geometric descriptions.

1. If $|p|<D$, its reply is constantly branch.
2. Otherwise write uniquely $p=w_jv$. Its reply on history $h$ is
   $E(n_j(h))$, $P_t(n_j(h))$ or $S_t(n_j(h))$ according to
   Definition 2.1. If $j\in S$ this is already determined by the
   acquired literal exterior. If $j\notin S$ its actual cells are
   exactly the inverse images of (LQF.5) under $h\mapsto n_j(h)$.

For a fixed slot the complete literal length possibilities for these
types are

$$
\begin{array}{c|c|c}
\text{type}&\text{whole-word lengths}&\text{a shortest suffix}\\ \hline
E& D&\varepsilon\\
P_{2s},\ s\ge1&D+s,\ldots,D+2s-1&R^s\\
P_{2s+1},\ s\ge1&D+s+1,\ldots,D+2s&LR^s\\
S_{2s},\ s\ge1&D+s,\ldots,D+2s-1&R^{s-1}L\\
S_{2s+1},\ s\ge1&D+s+1,\ldots,D+2s&R^{s-1}LL.
\end{array}
\tag{LQF.6}
$$

Every listed length is realized by a literal word of that type on every
atomic age, and there are no other lengths for that type. Together with
the constant shallow and displayed queries, restricting this list to
$\mathscr H_\eta$ characterizes all legal labeled reply partitions
with their full lengths. Different types or slots can coincide after
restriction; their costs are still those of their submitted words.
There is no physical $P_1$.

Proof. The complete skeleton contains every word through depth $D$;
its nodes at lesser depths are branches. At depth $D$ its unique slot
prefix is reached on every history. The suffix is then read in the
actual $T_{n_j(h)}$. Apply the supplied guarded formula (LQF.5).
For a displayed slot this is a computation on the acquired literal
tree, including all absent replies beyond its leaves. This exhausts
whole-tree addresses, without moving the root or observing two slots
in a single query.

For an $R$-ending suffix of weight $t$, let $b\ge1$ be its number
of $R$ letters and $a\ge0$ its number of $L$ letters. Then
$a+2b=t$ and $|v|=t-b$, so precisely
$\lceil t/2\rceil\le|v|\le t-1$ are possible. For each integer
in that range choose these counts and arrange the last letter as $R$.
For an $L$-ending suffix realizing $S_t$, one has $a\ge1$,
$b\ge0$, $a+2b=t-1$ and $|v|=t-1-b$. The same length interval
results, and arranging one $L$ last realizes every value. The displayed
shortest words are the already supplied representatives; this counting
also identifies their nonshortest competitors. Prefixing costs exactly
$D$ letters. An $R$-ending word has weight at least two; the weight-one
word $L$ gives $S_2$, not $P_1$. Restriction forms the actual reply
cells on the same histories and adds no new experiment. $\square$

**Definition 2.3 (joint reply table).** For any finite literal menu
$\mathcal A$, the table is

$$
\{(h,\tau(h),(r_{Y_h}(p))_{p\in\mathcal A}):
                      h\in\mathscr H_\eta\}.
\tag{LQF.7}
$$

Each row comes from the one $X_a$ in that history. Separate sets of
possible slot replies or possible lag values cannot replace this joint
table. A function of lag alone need not describe even one query when
two compatible sources have the same lag and different hidden ages.
The table is common mathematical control data; only paid replies select
the actual row during execution.

## 3. A finite menu dominating every native controller

**Definition 3.1 (entry-dependent physical menu).** On an attained
entry put $J=I\setminus S$ and $U_j=\max_{h\in\mathscr H_\eta}n_j(h)$.
For $j\in J$ retain $w_j$ and the shortest whole words in (LQF.6)
for both $P_t$ and $S_t$, $2\le t\le U_j$. Call this finite
set $\mathcal A_\eta$. An empty threshold range contributes no words;
if $J=\varnothing$ the menu is empty. Every word in the menu is an
ordinary legal current-root request with the length specified above.

**Theorem 3.2 (all-comparator domination and exact local feasibility).**
For every locally correct deterministic adaptive controller $A$ there
is a finite $\mathcal A_\eta$ controller $B$ that halts at constant-lag
sets and otherwise strictly splits the surviving histories. It has at
most $|\mathscr H_\eta|-1$ Reads on a path. On each same actual
$h\in\mathscr H_\eta$ its call count, summed literal lengths and
peak literal length are no greater than those of $A$.

A locally correct controller exists if and only if

$$
\forall h,h'\in\mathscr H_\eta:\quad
\bigl(n_j(h)=n_j(h')\text{ for all }j\in I\bigr)
\ \Longrightarrow\ \tau(h)=\tau(h').
\tag{LQF.8}
$$

Thus a nonempty incompatible entry has an explicit two-history
obstruction; it is different from the inconsistent empty case.

Proof. Since the history set is finite and $A$ terminates on each
member, the union of its finitely many finite executions unfolds to a
finite reachable decision tree. No advance uniform bound on its word
lengths, number of calls or local computations is required. Determinism
ensures that a common actual transcript has one next action.

Use Theorem 2.2 at each read. A shallow or displayed query has a known
constant reply on the entry and can be simulated locally. At a hidden
slot, retain $E$ as $w_j$. A $P_t$ or $S_t$ with $t>U_j$ is
constantly absent and can also be simulated. Every remaining word has
a shortest representative in $\mathcal A_\eta$ with the identical
four-valued reply on every history and no greater length. Replace it
by that one actual call. Induction through the old controller's choices
preserves its simulated replies and output on each same history. A
simulated known reply is local data, not a new receipt from the source.

Now delete any query constant on its surviving set and follow its
unique possible child. Halt immediately if that set has constant lag.
These deletions preserve correctness and cannot increase any of the
three path costs. Every remaining query has at least two nonempty
reply cells; each child is a strict subset. Hence the depth is at most
$|\mathscr H_\eta|-1$. Absence is one of these cells whenever it
is attained. Repeated stationary queries have become constant and are
deleted; their original invocations were nevertheless charged in $A$.
The new source calls are all the materialized menu words. This proves
the claimed pointwise domination, including early stopping.

If (LQF.8) fails, the two histories have identical whole current trees
by (LQF.1), and identical entries by definition. Equal transcripts force
equal next words and equal replies, or the same halt. They cannot both
receive their different required lags. This is NAR Theorem 16.3's
indistinguishability argument on this particular attained fiber.

Conversely, under (LQF.8), two histories with different lags differ in
some current exponent. Displayed exponents are fixed, so that slot is
hidden. Put $m$ equal to the smaller of the two exponents. At suffix
$R^{\lfloor m/2\rfloor}$ the smaller age gives alpha or beta, and
the larger gives a different reply by (LQF.5). This is $E$ if
$m\le1$, otherwise $P_{2\lfloor m/2\rfloor}$, and belongs to
the menu. Thus whenever a surviving set has nonconstant lag some
menu query splits it. Query such a word and continue. Strict subset
descent terminates; a constant-lag set gives the correct output.
$\square$

The finite-source pruning and same-source cost argument are established
methods in [NPL §§7--8][NPL] and [AOF §§3--5][AOF]. Here the additional
native correspondence is (LQF.2)--(LQF.8): the complete multi-slot
origin-code fiber, all of its current word experiments, and the
reply-preserving substitutions with nonincreasing literal length before
pruning. No finite set of representative lags has been substituted for
the actual joint histories.

## 4. The attained three-coordinate frontier

**Definition 4.1 (prices on one actual history domain).** If a locally
correct controller $A$ submits $p_1,\ldots,p_k$ on $h$, put

$$
c_A(h)=\left(k,\ \sum_{i=1}^k|p_i|,
                     \max(\{0\}\cup\{|p_i|:1\le i\le k\})\right),
\qquad
b_\eta(A)=\left(\max_h c_A(h)_1,
                 \max_h c_A(h)_2,\max_h c_A(h)_3\right).
\tag{LQF.9}
$$

All three maxima range over the same $\mathscr H_\eta$ and use the
same controller. They can have different maximizing histories. Define
the finite upper-budget region

$$
\mathcal F_\eta=
\{b\in\mathbb N^3:\exists A\text{ locally correct},\ b_\eta(A)\le b\}.
\tag{LQF.10}
$$

The frontier means its coordinatewise minimal elements. Upward closure
is a statement about allowed upper budgets; it does not assert that
every larger integer vector is an exact cost vector of a controller.

**Theorem 4.2 (exact attainable frontier against all literal strategies).**
For every attained entry, the following finite recursion computes
precisely the frontier of (LQF.10), with a real locally correct strategy
attaining every reported vector. For $C\subseteq\mathscr H_\eta$,
let $C_{p,y}=\{h\in C:r_{Y_h}(p)=y\}$. If $\tau$ is constant on
$C$, set $\mathcal P(C)=\{(0,0,0)\}$. Otherwise set

$$
\begin{aligned}
\mathcal P(C)=\operatorname{Min}\!\bigcup_{
       p\in\mathcal A_\eta:\ p\text{ splits }C}
\left\{\left(1+\max_y k_y,\ |p|+\max_y s_y,
                   \max\bigl(|p|,\max_y m_y\bigr)\right):
 (k_y,s_y,m_y)\in\mathcal P(C_{p,y})\right\}.
\end{aligned}
\tag{LQF.11}
$$

Only nonempty reply cells occur in this expression. The choices are
one whole child vector for each such cell, never separate minimizers
of its coordinates. If some required child set of vectors is empty,
that product contributes nothing. The minimum of the empty union is
empty. Then

$$
\mathcal F_\eta=\uparrow\mathcal P(\mathscr H_\eta).
\tag{LQF.12}
$$

If (LQF.8) fails the frontier is empty. Otherwise it is finite and
nonempty. Its zero vector occurs exactly when the initial entry already
determines the lag.

Proof. Every recursive child has strictly fewer histories than its
parent. The menu is finite, so the recursion terminates, including
states with no correct continuation. A constant-lag state admits the
zero-call answer, dominating every further querying strategy.

For a splitting query $p$, select an actual child strategy for each
nonempty cell. On any $h$ exactly one of those strategies executes
after the one paid $p$. Consequently the count and total length have
the first two maxima in (LQF.11), and the largest submitted word has
the third. These are the exact worst coordinates of this one combined
tree. Conversely any strictly splitting menu tree has just this root
and child decomposition. Induction therefore enumerates its possible
minimal worst vectors. Replacing a dominated child by its dominating
strategy cannot increase any root coordinate; this justifies removing
dominated vectors at intermediate states. A retained vector has a
finite tree witness obtained by remembering its choices.

Every such witness is an allowed native controller: submit its actual
menu words, update the surviving set using each raw reply, and halt
with the common lag. The actual history remains in that set at every
step by (LQF.7). Conversely Theorem 3.2 dominates every locally correct
controller by a tree of this finite family, separately on every actual
history. Its worst vector is therefore dominated too. These two
directions prove (LQF.12), rather than merely defining a decision-tree
optimization problem. Minimal feasible budgets are exact attained
worst vectors: strict slack in any coordinate would itself give a
smaller feasible vector.

Theorem 3.2 proves the empty/nonempty alternative. With no calls a
deterministic controller has only its initial entry, so its output must
be common to every history; conversely such a lag can be output
immediately. Finiteness ensures a real history attains each reported
coordinate maximum, although the three witnesses need not coincide.
$\square$

The finite-tree method and monotone Pareto combination are reused from
[AOF §5][AOF], [NPL §8][NPL] and the literature described in §8.
The three coordinates here are calls, summed length and peak length,
not calls, updates and summed length. This recursion is a finite exact
description; it supplies no practical complexity bound.

For nonnegative weights $\lambda$, the different objective
$\max_h\lambda\mathbin{\cdot}c_A(h)$ must be evaluated by forming
the weighted cost on each actual path before maximizing. It is not in
general $\lambda\mathbin{\cdot}b_\eta(A)$. The same-history distinction
is already explicit in [JRF, Definition 1.3 and §6][JRF]. Theorem 4.2
does not replace either objective by independently optimized marginal
coordinates or claim that a weighted worst-run optimum can be recovered
by scalarizing its frontier.

## 5. The peak projection and shortest pair separators

**Theorem 5.1 (explicit native shortest separators and exact peak).**
For two histories in the same attained entry with different lags put

$$
d(h,h')=\begin{cases}
\displaystyle D+\min_{j\in J:\ n_j(h)\ne n_j(h')}
             \left\lfloor\frac{\min(n_j(h),n_j(h'))}{2}\right\rfloor,
 &\text{if this slot set is nonempty},\\
\infty,&\text{otherwise}.
\end{cases}
\tag{LQF.13}
$$

This is exactly the shortest length of a literal whole-tree word whose
two replies differ. With the maximum over no different-lag pairs
defined to be zero, the optimal worst peak is

$$
M_\eta=\max_{h,h'\in\mathscr H_\eta:\ \tau(h)\ne\tau(h')}d(h,h').
\tag{LQF.14}
$$

An infinite value means local impossibility. Every finite value is
attained by a real finite controller. Thus (LQF.14) is also the minimum
third coordinate of Theorem 4.2's nonempty frontier.

Proof. For atomic ages $n<m$, put $s=\lfloor n/2\rfloor$.
The actual word $R^s$ separates them: its reply at $n$ is alpha or
beta and at $m$ is a different constructor. If $|v|<s$, then
$n\ge2|v|+2$. Since $w(v)\le2|v|$, (LQF.5) says that both
ages reply branch, including the empty word when this inequality
applies. Hence the shortest atomic separator has exactly length $s$.
For $n=0$ or $1$ the root itself separates the pair and the same
formula gives zero. This is a full-reply argument; presence agreement
alone would not suffice.

In a complete entry, words above the slots and words in displayed
slots cannot distinguish the histories. A hidden slot with equal
exponents cannot distinguish them either. At any differing hidden
slot the atomic argument, with the mandatory $D$-letter prefix,
gives exactly the term in (LQF.13). Minimizing over these possibilities
proves that formula. A minimizing word is a literal $w_jR^s$.

Take any correct controller and a different-lag pair. Until their
first unequal reply, determinism gives the same queries and decisions.
They cannot terminate with a common output, so such a reply must occur
on their finite runs. Its word has length at least $d(h,h')$.
The controller's worst peak is consequently at least (LQF.14).

If the maximum is finite, choose a shortest separator for every
different-lag pair and query their finite union in a fixed order.
Histories sharing the resulting transcript cannot have different lags,
since their chosen separator would have different replies. Output
the common lag, stopping earlier if already determined. Every submitted
word has length at most (LQF.14), proving attainment. If there are no
such pairs, halt without reading. If a pair has no separator, Theorem
3.2 proves impossibility. Finally Theorem 3.2 normalizes the attaining
strategy and Theorem 4.2 includes a dominating frontier vector; the
peak lower bound forces that vector's peak to equal (LQF.14).
$\square$

The sufficiency argument is the ordinary finite pair-separation method,
now with the proved native distance (LQF.13). For the peak coordinate
alone, adaptivity does not improve on a suitable finite nonadaptive
list. Such a list may spend many more calls or letters in total.
Different pairs can require different words; their shortest separators
are not one simultaneous query. The three-coordinate frontier, rather
than this maximum alone, decides joint call and total-length budgets.

## 6. Local recovery versus a globally correct NAR service

**Theorem 6.1 (exact extension condition).** Fix the installed encoder
and the entire NAR source, menu and lag domain of Assumption 1.1. Let
$\mathcal F^{\mathrm{global}}_\eta$ mean upper budgets measured only
on $\mathscr H_\eta$, but of controllers correct on every promised
NAR input for that encoder. Then

$$
\mathcal F^{\mathrm{global}}_\eta=\mathcal F_\eta
\quad\text{if}\quad
e(a)=e(b),\ a-b=d\mathbf1\ \Longrightarrow\ d=0.
\tag{LQF.15}
$$

If this encoder condition fails, there is no globally correct service
and $\mathcal F^{\mathrm{global}}_\eta=\varnothing$, even at entries
where $\mathcal F_\eta$ contains zero. Under the condition, every
locally correct controller at a fixed attained entry, not only its
optimal replacements, has a globally correct extension with identical
runs on that entry.

Proof. NAR Theorem 16.5 supplies precisely the equivalence between the
displayed encoder condition and existence of a globally correct finite
current service. Its fallback reads hidden clock intervals with the
finite uniform call bound
$(r-|S|)\lfloor\log_2(2H+1)\rfloor$. This is a reused feasible
service, not a new optimality claim.

Fix any locally correct $A$ at $\eta_*$. Install one common controller
which compares its complete received $(S,c,V)$ to this fixed finite
entry. On equality run $A$; otherwise run the NAR fallback. The
comparison includes actual complete-row equality, not only selected
clock summaries. The equality branch has exactly the histories on
which $A$ is correct and preserves their queries, replies and costs.
Every other promised input is handled correctly by the fallback.
The fixed entry in the installation is a common constant, not an
additional chosen-source handle. Comparing or parsing an already
acquired entry adds no fresh Read under this contract. Restricting any
global service to the entry proves the reverse inclusion in (LQF.15).

If the condition fails, NAR Theorem 16.3 supplies a same-code,
different-lag pair with the identical whole current tree and hence the
identical complete row at any selected $S$. No global controller can
separate it. This leaves the local question at other entries untouched.
$\square$

**Proposition 6.2 (a genuine locally easy entry with no global service).**
Take $D=1,H=1,q=2$, positive lags, $S=\{1\}$ and the constant
encoder. At the complete row

$$
V_1=\bigl(\langle\square_L,T_3\rangle,\{\{L\}\}\bigr)
\tag{LQF.16}
$$

the exact fiber is $((0,0),1)$ and $((1,0),1)$, and its frontier is
$\{(0,0,0)\}$. Nevertheless the encoder has no globally correct
NAR service. This example also gives a zero-call terminal set with
multiple genuine original sources.

Proof. The displayed normalized clock is $z_1=1$. Positive lag and
$a_1\in\{0,1\}$ force $\ell=1,a_1=0$; either $a_0$ is allowed.
Their actual original trees are $\langle T_0,T_2\rangle$ and
$\langle T_1,T_2\rangle$, and their current left subtrees are
respectively $T_1,T_2$. Both complete rows are (LQF.16). Output one
immediately, without reconstructing the hidden original left value.

Elsewhere, the fixed originals with profiles $(0,0)$ and $(1,1)$,
at lags two and one, both have current tree
$\langle T_2,T_4\rangle$. Their code and entire later row agree but
their lags differ. They refute global correctness by actual full-tree
equality. This pair is also a nonempty locally impossible entry; it
is not an inconsistent proposed row. $\square$

**Proposition 6.3 (zero parameters, visibility and inconsistent rows).**
If $H=0$, every attained entry has zero frontier vector for every
encoder. If $S=I$, including the forced case $D=0$, an attained entry
either already has constant lag and zero frontier vector, or is locally
impossible. Full visibility alone does not remedy a bad encoder.
For $D=2,H=1,S=\{3\}$, a putative row with the native skeleton and
displayed $T_7$, but with two hidden slots declared equal, is
inconsistent even though its displayed normalized clock is legal.

Proof. At $H=0$ the only profile is zero, and any displayed normalized
clock equals the lag. If every slot is displayed, the current tree is
already fixed by the entry. Every new query is constant on its fiber,
so (LQF.8) is equivalent to constant lag. Nonempty selection at $D=0$
forces this case. For the proposed depth-two row, the clock at slot
three is $7-3\cdot2=1$, attainable at lag one with displayed age
zero. But at any history the distinct offset bands make all three
hidden subtrees pairwise unequal. The proposed equality partition
therefore has no actual witness. This demonstrates why the entire row
test in Lemma 1.3 cannot be dropped. $\square$

The root word always costs one call when actually submitted, even at
length zero. At a fully determined lag the optimum is instead a true
zero-call halt. The missing $P_1$ is also material: the already proved
zero-origin interval $[0,3]$ requires two calls, while $[1,4]$ permits
one, by [AOF §8][AOF] and [NARC §3.1][NARC]. Those results keep their
original contracts; a certified epoch from another service cannot fill this
missing threshold in the unknown-lag problem.

## 7. Genuine four-history entries and a joint tradeoff

**Definition 7.1 (the previously supplied mixed-word boundary).** The
four-age phenomenon $[2,5]$ is [AOF Theorem 9.2][AOF], and its
whole-tree embedding uses [NARC §§1--2][NARC]. In the present notation
take $D=1,H=3,q=4$, $e(a)=a_0$, positive lags, $S=\{1\}$,
code zero and displayed normalized clock five. The whole fiber consists
of the genuine originals

$$
X_{(0,5-\ell)}=\langle T_0,T_{9-\ell}\rangle,
\qquad \ell=2,3,4,5,
\tag{LQF.17}
$$

each at its own lag. Their entire later row is
$(\langle\square_L,T_9\rangle,\{\{L\}\})$ and their hidden ages
are $2,3,4,5$. Thus the existing mixed suffix $LR=P_3$ is the actual
whole word $LLR$, returning respectively $\bot,\alpha,\beta,\mathsf b$.
The supplied one-call result and pair $4,5$ give the single joint
frontier vector $(1,3,3)$: every correct service needs a word of
length at least three, hence also total length at least three. Pure
right suffixes need two calls here, as already established by AOF.
This is a reused interval example, not an additional four-age theorem.

**Proposition 7.2 (multiple hidden slots with two exact frontier points).**
Take $D=2,H=3,q=4$, positive lags and the singleton menu with
$S=\{3\}$. Install the encoder assigning one label $*$ to precisely
the following four profiles, and a different individual label to every
other profile. The rows list their compatible lags and current ages:

$$
\begin{array}{c|c|c|c}
\text{history}&a&\ell&(n_0,n_1,n_2,n_3)\\ \hline
h_1&(0,1,3,3)&2&(2,7,13,17)\\
h_2&(0,1,2,2)&3&(3,8,13,17)\\
h_3&(2,1,1,1)&4&(6,9,13,17)\\
h_4&(2,1,0,0)&5&(7,10,13,17).
\end{array}
\tag{LQF.18}
$$

At code $*$ and complete row with exterior
$\mathcal B_2[\square_{LL},\square_{LR},\square_{RL},T_{17}]$
and discrete hidden partition, these are exactly all histories. The
encoder is globally feasible. The exact local frontier, and the
frontier of restrictions of globally correct services, is

$$
\boxed{\mathcal P(\mathscr H_\eta)=\{(1,6,6),(2,8,5)\}.}
\tag{LQF.19}
$$

Proof of the source and entry assertions. Construct each original as
$\mathcal B_2[(T_{4j+a_j})_{j=0}^3]$. Its genuine $\ell$-fold
homomorphic continuation has exactly the current exponents in the
table. The three hidden positions remain reached and their values
are distinct; hence the stated row includes their complete equality
and disequality information. The displayed equation is $a_3+\ell=5$.
For each of the four profiles this fixes exactly the listed lag.
No other profile has the code, so this is the entire entry fiber.
The encoder is a function of the acquired initial ages and can be
installed before either the future selection or lag. In its only
nonsingleton code class all profiles have $a_1=1$. A common translation
between two of them would therefore have displacement zero and would
make them identical. All other code classes are singletons, proving
the encoder condition of Theorem 6.1.

Proof of attainment. One query at slot one with suffix $R^4=P_8$
is the literal word $LRRRRR$, of length six. On the ages
$7,8,9,10$ it gives four different replies and hence the four lags.
This attains $(1,6,6)$. Alternatively query $LLRRR$, the slot-zero
$P_6$ word of length five. Alpha and beta identify $h_3,h_4$.
On absence, query $LLR$, of length three, whose alpha and beta
replies identify $h_1,h_2$. The latter histories spend two calls and
eight letters; the others spend one call and five letters. The exact
worst vector is $(2,8,5)$.

Proof against all other literal strategies. By (LQF.13), the shortest
separator of $h_3,h_4$ has length five: slot zero needs three suffix
letters and slot one needs four; the other slots are constant. Thus
peak at most four is impossible. With peak at least six, every correct
strategy has at least one call and total length at least six, so its
worst vector is dominated by $(1,6,6)$.

It remains to consider peak five. Every informative query on the full
fiber has length at least three, since the skeleton and all slot roots
reply branch. A first separating query for $h_3,h_4$ must have length
five. If an earlier informative query occurred on their common path,
that path already costs at least $3+5=8$ letters. If none occurred,
remove the earlier constant queries for this lower-bound comparison.
The separating query is then the first informative query on the whole
fiber. It must be in slot zero; the allowed length-three suffixes
separating ages six and seven have types $P_5,P_6,S_6$ by (LQF.5).
All three give absence at both ages two and three. Those latter two
histories consequently need another query; their shortest separator
has length three. Some actual path again costs at least eight letters.

There is also no correct one-call strategy at peak five. In slot zero
no type in (LQF.5) separates all four ages $2,3,6,7$: four distinct
replies would require its two singleton ages to be the two middle
values three and six, which are not consecutive. An $S_t$ or $E$
has fewer than four replies. At slot one a suffix of length at most
three has weight at most six, and cannot distinguish all of
$7,8,9,10$; slots two and three are constant. Theorem 2.2 exhausts
the other words. Therefore every peak-five strategy has count at
least two and total length at least eight. The attained vector
$(2,8,5)$ dominates it. This proves exactly (LQF.19), and Theorem
6.1 gives its global-extension interpretation. $\square$

This finite-entry tradeoff fixes one encoder and one acquired row.
It neither optimizes the encoder's label alphabet nor takes worst costs
over every entry or unbounded lag. The common label in Proposition
7.2 is not a four-label encoding of the entire age cube. The displayed
table lists actual source histories, not four independently chosen
slot marginals. The example also distinguishes the peak optimum from
the call and total-length optima: no one strategy attains all three
coordinate minima $(1,6,5)$.

## 8. Supplier correspondence and the recovery boundary

**Definition 8.1 (mathematical provenance of the interface).** Repository
references below use the immutable snapshot
[`e8891b5bc48c50f494096810d09453c8ec81020f`][BASE]. The ordinary
native deductions in Theorems 2.2--6.1 and Proposition 7.2 are
`repo-derived`, with the following existing content retained as suppliers.

| Supplier | Exact mathematical use and boundary |
| --- | --- |
| [NAR §§16.1--16.10][NAR] | Actual age-cube sources, acquire/export/discard contract, complete row equality, whole-current collisions, global encoder feasibility and fallback, and the explicit remaining all-word/address gap. |
| [SLH §§6.2--6.3 and §13][SLH] | Guarded atomic replies for every finite word, odd/even threshold representatives, limitations of right-ray querying, and finite same-source reply games. These formulas and methods are not new here. |
| [AOF §§3--5 and §§8--9][AOF] | All-comparator normalization, Pareto combination and separate same-run prices; the zero-origin $E/P/S$ interface, shortest words, interval call/peak results and the $[2,5]$ mixed-word example. |
| [NARC §§1--3 and §24.3][NARC] | The already exact two-slot complete fibers and whole-address call/peak reduction. The present multi-slot three-price result does not optimize the separately constrained mutable-state controllers of §24.3. |
| [NPL §§7--8][NPL] and [JRF §2.1 and §6][JRF] | Finite physical menus, sourcewise domination, shortest words, and joint histories rather than marginally realizable tests. |
| [GenealogicalFiberTransport][GFT], `Source`, `substitution` | Actual finite ordered trees and the homomorphic native operation used in (LQF.1). |
| [ActualTreeReadoutAcquisition][ATR], `Address`, `Reply`, `readout` | Literal addresses and the four-valued constructor/absence port; not a clock or subtree oracle. |
| [DelayedOriginalReadout][DOR], `rightClock`, `rights`, `right_clock_iterate`, `right_clock_readout` | The acquired visible clocks and the actual right-word replies used for separators. Its certified-epoch original decoder does not supply the unknown lag in this contract. |
| [ActualCutPartitionDecoder][ACP], `literalRecord`, `canonicalRow_record_iff` | Complete literal exterior and hidden equality/disequality information. The private `eraseClasses` and `eraseClasses_literal` explain the exterior representation, rather than justify ignoring part of the row. |
| [NativeDepthPatterns][NDP], `original_present_transport`, `original_prefix_locality`, `Pattern`, `fill` | Reached original slots and their transported subtrees. Here the pattern is the complete depth-$D$ skeleton. |
| [ActualFibonacciSupportChain][AFS], `actual_fibonacci_support_chain` | A related bounded-address presence result. Presence equivalence is weaker than the full-reply equality used in Theorem 5.1; (LQF.5) supplies the latter. |
| [PassivePolicyNormalization][PPN], `execute`, `candidates`, `execute_transfer`, `result` | Deterministic transcript and finite-candidate pruning interfaces. Its packaged `result` includes finite-query and stopping-legality hypotheses; it is not asserted as a compiled three-price application to arbitrary literal words. The native reduction precedes the finite recursion here. |

The statements in this volume are ordinary conditional mathematical
proofs. They are not new Lean declarations or kernel-verified applications
of the listed source declarations.

**Definition 8.2 (bounded literature correspondence).** The following
are `literature-attested` methods used inside the native deductions,
not additional native recovery theorems.

| Primary source | Correspondence and limit |
| --- | --- |
| R. D. Nowak, *The Geometry of Generalized Binary Search*, [arXiv:0910.4397v5, §V.A][Nowak] | The disjoint-interval example distinguishes permitted point tests from stronger dyadic-subinterval queries. Here the permitted geometry is proved by (LQF.5)--(LQF.6); binary GBS bounds grant neither a new native test nor a missing $P_1$. |
| F. Cicalese, E. Laber and A. M. Saettler, *Diagnosis determination: decision trees optimizing simultaneously worst and expected testing cost*, [PMLR 32(1):414--422, §1, pp.414--415][CLS] | Finite objects, target classes, multiway priced tests and homogeneous-class leaves are the established discrete-function-evaluation framework. Objects here are actual histories, classes are lags, and tests must first pass the native correspondence. Their distributional and approximation objectives do not prove this exact call/sum/peak frontier. |
| J. G. M. van der Linden, M. M. de Weerdt and E. Demirović, *Necessary and Sufficient Conditions for Optimal Decision Trees using Dynamic Programming*, [arXiv:2305.19706v4, §4][LWD] | Established state transitions, combination operators and Pareto subtree sets explain the recursion method. The multiway native cells, whole-word lengths and max-type peak coordinate are instantiated and proved here; no complexity guarantee is transferred from its decision-tree learning algorithms. |

This comparison assigns no worldwide originality or priority claim.
The added interface is the complete multi-slot, arbitrary-encoder
history domain with its all-word literal prices, joint frontier,
shortest separators and conditional global extension. The generic
finite decision-tree and Pareto methods, atomic reply formulas and
the two-slot interval boundary are credited above.

**Proposition 8.3 (task-relative recovery and unrecovered relations).**
Under Assumption 1.1 the acquired boundary and retained code determine
the joint relation (LQF.2); the native address geometry determines its
allowed reply partitions and prices. That relation determines exactly
the feasible three-coordinate recovery budgets through Theorem 4.2,
and a selected attaining controller recovers the substitution lag under
its local feasibility condition. This does not in general recover the
hidden original source, the discarded row or the historical acquisition
process.

Proof. Lemma 1.3 gives the first determination from the acquired data
and installed encoder. Theorem 2.2 computes the permitted experiments
on the same histories, and Theorems 3.2--4.2 give both directions of
budget feasibility. In Proposition 6.2, however, two distinct original
left values have the same code, complete acquired row and recovered
lag. These data cannot reconstruct both original sources. No step
recovers how a row was acquired or authenticates its provenance;
truthful acquisition, same-source continuation and stationarity are
premises. $\square$

The spatial quantity here is the prefix geometry and literal length of
native addresses. The temporal quantity is an integer substitution lag
relative to the acquired original. The boundary is an already acquired
complete cut row. The memory quantity fixed here is the retained origin
code, with unrestricted later local computation and workspace. The
proved correspondences concern these specified relations and this lag
task; they imply neither physical spacetime reconstruction nor a total
memory or execution-cost law.

The encoder-wide memory/call/address optimum and a uniform joint
frontier over all acquired rows and unbounded lags remain separate.
In particular [NAR Theorem 16.6][NAR] already proves that a uniform
finite address cap for a globally correct encoder is possible exactly
when that encoder satisfies the zero-extra-read separation condition.
A finite $\mathcal A_\eta$ at each entry cannot supply a single
lag-uniform word bound. Nonstationary services, restricted workspace,
mutable-word geometry, acquisition and authentication prices, and
extensions to arbitrary native sources require their own interfaces.
The finite lag-recovery interface established here is one conditional
connection among boundary, memory, address geometry and temporal
recovery, not a completion of their general mutual-recovery programme.

[BASE]: https://github.com/the-omega-institute/trureturing/tree/e8891b5bc48c50f494096810d09453c8ec81020f
[NAR]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[SLH]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[AOF]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[NARC]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[NPL]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[JRF]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[GFT]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[ATR]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[DOR]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[ACP]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[NDP]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[AFS]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean
[PPN]: https://github.com/the-omega-institute/trureturing/blob/e8891b5bc48c50f494096810d09453c8ec81020f/D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization.lean
[Nowak]: https://arxiv.org/html/0910.4397v5
[CLS]: https://proceedings.mlr.press/v32/cicalese14.pdf
[LWD]: https://arxiv.org/html/2305.19706v4

## 追加锚（本行以下为增补区）
