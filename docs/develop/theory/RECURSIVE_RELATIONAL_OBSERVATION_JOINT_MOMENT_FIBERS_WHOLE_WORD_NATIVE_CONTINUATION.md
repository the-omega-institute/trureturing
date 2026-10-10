# 递归关系观察：联合矩纤维的全叶词原生续读与字面行容量

The original ordered sources, exact leaf-word fibers, address readout and cache semantics
are those of [parent chapters 52–60][JM52]; the actual shortlex branch prefix is that of
[parent chapter 66][JM]. References below to parent chapters 52–64 and 66 and equations
(JM.151)–(JM.201), (JM.214)–(JM.229) refer to that parent volume. Chapters 67–69 and
(JM.230)–(JM.237) are local to this continuation.

The effective-entry initialization of [public parent chapter 65][JMPublic] uses its own actual $(t,h)$ contract.
The [archival raw-fiber chapter 65][JMOldRaw] corresponds here to parent chapter 66, equations (JM.214)–(JM.229).
The universal manuscript statements in chapters 67–69 retain formal status OPEN.

The notations $F_t$ and $F(t)$ denote the same Fibonacci sequence,
$F(0)=0$, $F(1)=1$, $F(t+2)=F(t+1)+F(t)$. The raw symbols
$\mathsf{br}$ and $\mathsf{abs}$ denote the native `branch` and `absent` replies.
Chapter 67 uses its eligible Boolean $\operatorname{Pos}$ reader; the observer results in
chapter 69 use only Hypothesis 69.2. The separate total bit/raw-cache $Q$ consumer of
[parent chapter 66.2][JM] retains its own task contract.

The native source and word representation is [GenealogicalFiberTransport][Source];
readout, positivity and the finite Boolean decision are [ActualTreeReadoutAcquisition][Readout].
Address geometry is [ActualLeafHistoryRigidity][Geometry], and the coarse reply and history
maps are [ActualCoarseReadoutHistory][Coarse]. The observer, action, cache and actual-prefix
objects are [ActualFiniteObserverAbsentElimination][Native]; the all-history relation is
[ActualObserverPairReach][Pair], and nominal cache lifts are [ActualAcquisitionCacheFiber][Cache].

## 67. Whole-word target-leaf reduction and the native coarse optimum

**定义 67.1（Sources, labelled leaves and the original prefix）。** Use the nonempty ordered trees
$\mathcal T=\operatorname{FreeMagma}(\mathrm{Bool})$ of `GenealogicalFiberTransport.Source`, with
$\alpha=\mathrm{of}(\mathrm{true})$, $\beta=\mathrm{of}(\mathrm{false})$ and ordered pairing $\mathrm{mul}$.
The substitution is the original `substitution`: $\rho\alpha=\beta$, $\rho\beta=(\beta,\alpha)$,
$\rho(s,t)=(\rho s,\rho t)$. Put $T_n=\rho^n\alpha$ and use the exact ordered leaf word
$w(\alpha)=a$, $w(\beta)=b$, $w(s,t)=w(s)w(t)$. In `sourceEquiv` and `indexedEquiv`, fixing this
word fixes the label at each left-to-right leaf position on every ordered shape; it does not fix
the shape. The domain is $W_n=\{U:w(U)=w(T_n)\}$, the subset of the native composition fiber
with this entire word. Let $r$ be `ActualTreeReadoutAcquisition.readout`, on all addresses
$\mathcal A=\{L,R\}^*$ with $L=\mathrm{false}$, $R=\mathrm{true}$ and root $\varepsilon$.
Write $c_U(q)=\kappa(r(q,U))$, where `ActualCoarseReadoutHistory.kappa` retains the two leaf
labels and sends both `branch` and `absent` to `none`. Positivity means exactly
$\operatorname{Pos}(U)\iff U\in\rho^3[\mathcal T]$, the original `Positive` predicate.

Fix an integer $n\ge4$. With $B=T_3$ and $P_n=\{p:T_n|_p=B\}$, take exactly

$$
J_n=\{pL:p\in P_n\},\qquad
h_n=((q,\mathrm{branch}):q\in J_n\text{ in shortlex order}),\qquad N=F_{n+1}.
\tag{JM.230}
$$

These are (JM.214), with the superscript `raw` suppressed. In particular every $J_n$ address
is internal in $T_n$. The word has $N$ leaves, so every member of $W_n$ has exactly $N$ leaves.
Let $\Lambda_n$ be the target leaf-address set and put $\lambda_n(q)=(q,c_{T_n}(q))$ for
$q\in\Lambda_n$. The finite vertex carrier is $\mathcal L_n=\lambda_n[\Lambda_n]$; its vertices
retain both the literal address and its target label. Define

$$
\begin{aligned}
\mathcal F_n^\kappa&=\{U\in W_n:\forall q\in J_n,\ c_U(q)=c_{T_n}(q)\},\\
D_n(U)&=\{\lambda_n(q):q\in\Lambda_n,\ c_U(q)\ne c_{T_n}(q)\},\\
H_n&=\{D_n(U):U\in\mathcal F_n^\kappa,\ \neg\operatorname{Pos}(U)\},\\
\tau(H_n)&=\min\{|C|:C\subseteq\mathcal L_n,\ \forall D\in H_n,\ C\cap D\ne\varnothing\}.
\end{aligned}
\tag{JM.231}
$$

The empty family has transversal number zero. Every realized negative source in the entire
$W_n$ satisfying the displayed coarse prefix condition contributes its set, regardless of its
root split or child words. Here $W_n$ is finite: `GenealogicalFiberTransport.result` gives
finiteness of its containing composition fiber, with parameters $(F_{n-1},F_n)$.

An eligible reader is the original `ActualFiniteObserverAbsentElimination.Observer` on any
finite complete nominal carrier $E$, with source-independent initial row, actions, four-reply
transitions and raw decoder. Its initial decoder is empty, every decoder is address-Nodup,
and `Legal M U` holds at every actual prefix for each $U\in W_n$. It terminates from that common
initial row on every $U\in W_n$, with Boolean halt bit true exactly when $\operatorname{Pos}(U)$.
Its original `historyAction` factors through the original `kappa_hist` on all finite raw
histories. It actually produces $h_n$ on $T_n$ from the empty initial cache. For its terminal
trace $h_nt$, its extra cost is $|\operatorname{paid}(h_nt)\setminus J_n|$, with `paid` the
distinct literal-address support. Define $O_n$ as the infimum of these costs over eligible readers.
Raw caches retain first-occurrence order and all four replies under the original `cacheUpdate`;
repeats and absent reports remain in the chronological trace.

**定理 67.2（Uniform target-leaf dominance and faithful native attainment）。** For every $n\ge4$
there is a map $\pi_n:\mathcal A\to\mathcal L_n$, independent of the comparison source, such that

$$
\forall U\in\mathcal T\ \forall p\in\mathcal A,\qquad
c_U(p)\ne c_{T_n}(p)\ \Longrightarrow\ \pi_n(p)\in D_n(U).
\tag{JM.232}
$$

Here the formula defining $D_n(U)$ applies also outside $W_n$. Every finite extra-address
certificate against all negatives in $\mathcal F_n^\kappa$ therefore has a dominating target-leaf
certificate of no greater cardinality. Every eligible native reader pays at least $\tau(H_n)$
after its actual $h_n$ on $T_n$, and an eligible finite complete native reader attains this bound:

$$
O_n=\tau(H_n),\qquad
\exists M\text{ eligible},\quad
|\operatorname{paid}(h_nt_M)\setminus J_n|=\tau(H_n).
\tag{JM.233}
$$

Proof. First define the address underlying $\pi_n(p)$. If $p$ is a target leaf, choose $p$.
If $p$ is internal in $T_n$, choose the leftmost target leaf descending from $p$.
If $p$ is absent in $T_n$, choose the unique target leaf strictly preceding $p$ along its path.
Existence and uniqueness in the last case are the absent-address and leaf-prefix clauses of
`ActualLeafHistoryRigidity.actual_address_geometry`; existence in the internal case follows
by descending the finite nonempty subtree. Return the chosen address with its target label.

For a target leaf, (JM.232) is immediate. At an internal target address the target coarse reply
is `none`; a different coarse reply in $U$ must be a labelled leaf there. Every proper descendant
of that leaf is absent in $U$, including the selected target leaf, which has a non-`none` target
label. At an absent target address a different coarse reply again means that $U$ has a labelled
leaf at $p$. Its selected strict ancestor must consequently be internal in $U$, and hence have
coarse reply `none` instead of its target leaf label. This proves (JM.232) for every literal
address, including arbitrarily long ones, and every ordered source, without any common split.

For $U\in\mathcal F_n^\kappa$, disagreement at an address of $J_n$ is impossible. If a finite
$S\subseteq\mathcal A\setminus J_n$ distinguishes $T_n$ from every negative in this fiber,
then for each such $U$ some $p\in S$ disagrees. Formula (JM.232) gives
$\pi_n[S]\cap D_n(U)\ne\varnothing$, and $|\pi_n[S]|\le|S|$.
Conversely a hitting set $C$ distinguishes by querying its address projection. That projection
is injective on $\mathcal L_n$ and is disjoint from $J_n$, because $J_n$ contains internal target
addresses. These statements concern supports and their distinct costs.

Every edge $D_n(U)$ is nonempty. Otherwise all target leaves have matching coarse labels in $U$;
at these addresses coarse leaf equality is raw equality. The leaf reconstruction clause of
`ActualTreeReadoutAcquisition.source_foundation` then forces $U=T_n$. But
$T_n=\rho^3(T_{n-3})$ is positive. Thus the finite carrier itself hits all edges, and a minimum
$C$ in (JM.231) exists, including $C=\varnothing$ when there are no edges.

Now take any eligible $M$ and its finite terminal execution on $T_n$. Compare that run with its
actual $h_n$ one query at a time: the common row has the same action and the same cached reply,
so the run has the same head step. A halt cannot occur while that actual prefix still queries.
Cancelling these finitely many heads writes the run as $h_nt$. This uses the native actual-prefix
and `run_deterministic` semantics also used in theorem 54.2. Set
$S=\operatorname{paid}(h_nt)\setminus J_n$. Fix any negative $U\in\mathcal F_n^\kappa$.
Suppose no address of $S$ has a different coarse reply. Prefix compatibility then makes the
coarse replies agree at every address of the entire target execution. Replay from the common
empty initial row, maintaining equality of the chronological coarse histories. At each step,
`actualPrefix_semantics` identifies each actual row with its own `historyState`; the full-history
factorization forces their actions to agree. At a query, `Legal` and `queryReply_eq_readout`
identify each returned raw value with the readout of its own immutable source, whether the
request is fresh or repeated. Their coarse values agree, so the induction continues.

At the target halt the two actual actions are the same Boolean halt, necessarily true.
The replay is a finite native run on $U$; correctness and determinism contradict its negativity.
This argument uses equality of actions and coarse histories, while permitting different raw
rows, caches, branch/absent replies and hit values. Hence $S$ distinguishes every such $U$.
Its image under $\pi_n$ hits every edge, so $\tau(H_n)\le|\pi_n[S]|\le|S|$.
This is the native coarse replay of chapter 66.3, applied to every realized negative rather than
only the supplied disjoint-support subfamily; the ordered cache and actual-prefix semantics
are reused from the cited native declarations.

For attainment, fix a minimum $C$, and let $A$ be its injective address projection. Form a fixed
request list $s=(q_1,\ldots,q_L)$ by concatenating $J_n$ in its original shortlex order, $A$ in
shortlex order, and the entire window $\mathsf B_N=\{q:|q|\le N-1\}$ in shortlex order.
Keep every repetition in this list. Write $m=|J_n|+|C|$. Use the finite complete nominal carrier
$E=\bigsqcup_{i=0}^{L}\mathsf{Reply}^{i}$: every four-valued response word of every displayed
length is a row, including conflicting repeated replies and unrealizable words. The initial
row is the empty word. Decode $(y_1,\ldots,y_i)$ by folding the original `cacheUpdate` from
the empty cache over $(q_1,y_1),\ldots,(q_i,y_i)$. All nominal decoders are address-Nodup;
a repeated nominal report retains its first stored value.

At length $m$, halt true if $\kappa y_j=c_{T_n}(q_j)$ for all $1\le j\le m$.
At every other length $i<L$, query $q_{i+1}$; this includes length $m$ when the test fails.
At length $L$, use the total Boolean function determined by the coarse word as follows:
if $\{V\in W_n:\forall j\le L,\ c_V(q_j)=\kappa y_j\}$ is a singleton $\{V\}$, return
`finiteDecision V`; otherwise return false. Each query transition appends its received raw
reply, and each halt transition is a self-loop for each of the four replies. This defines
actions and transitions on every nominal row, including rows beyond an earlier possible halt.

On every actual $U\in W_n$, induction on queries gives truth of the decoded cache. A hit returns
its retained true value and a miss reads $r(q,U)$, so the next decoder is exactly the required
first-occurrence update. Thus the original `Legal` holds on every actual prefix. Each query
increases row length and no path exceeds $L$, proving finite termination on every original source.
An actual early halt entails coarse compatibility on $J_n$ and all queried vertices of $C$.
If that source were negative, its edge would meet $C$, contradicting the early test. It is
therefore positive, which is exactly the required Boolean conclusion.

The remaining actual executions acquire the complete window. The $N$-leaf depth bound and
complete labelled-frontier reconstruction are supplied by theorem 57.2 and (JM.173): all leaves
lie at depth at most $N-1$, and their labelled addresses determine the original source uniquely.
Hence the displayed terminal compatible set is exactly $\{U\}$ on every such execution.
`acquisition_foundation` supplies `finiteDecision U = true` exactly when `Positive U`.
This proves correctness on all of $W_n$.

For full-history factorization, relate two nominal rows when they have the same length and
pointwise equal coarse response words. Related rows have the same early test, terminal
compatible set and action. For any raw replies $y,z$ with $\kappa y=\kappa z$, their absorbing
`barStep` successors remain related: query rows append coarse-equal replies, and halt rows
both stay fixed. The common initial pair is related. This supplies `pairActionInvariant`, so
`ActualObserverPairReach.pairActionInvariant_iff_allHistoryFactorization` gives the original
all-history conclusion. Equivalently, `historyState` folds only the external response word;
arbitrary external address labels are ignored by that fold, and posthalt responses are absorbed.
Thus equal `kappa_hist` histories give equal actions even for inconsistent, wrong-address,
counterfactual, repeated and posthalt histories. No equality of the raw decoders is required.

On $T_n$, the first $|J_n|$ actual raw replies are all `branch`, producing exactly $h_n$ from
the common empty cache. The $A$ replies match their target labels and the row at length $m$
halts true. Since $A\subseteq\Lambda_n$ is disjoint from $J_n$, exactly $|C|=\tau(H_n)$ distinct
extra addresses were paid. Together with the universal native lower bound this proves (JM.233).
The finite rows and window reconstruction specialize the supplied constructions of theorem
57.2 and chapter 66.3; no reordering of the preorder `pureObserver` trace is used. $\square$

**数学引文 67.3（Intermediate suppliers）。** Chapters 52–60 of
[the original manuscript at 1590efae](https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md)
supply the actual word domain, leaf positions, cache replay and finite frontier attainment;
[chapter 65 at cf4b9edd](https://github.com/the-omega-institute/trureturing/blob/cf4b9edd2cf0b4410767cfd5e409b29753586105/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md)
supplies the exact prefix and its coarse replay. The named FibonacciAtomic declarations above
are taken at 1590efae55f93022396cb1984f0014bbc73b8f65. The native finite-table representation
is applicable to the attaining reader with bound $N$: all its requests and decoded addresses
are in $Q_N$. Its `Admissible(N)` normalization and coverage conclusions retain their larger
source-domain hypotheses. Buhrman–de Wolf, [Complexity Measures and Decision Tree Complexity:
A Survey](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf), §§4.1–4.2, supplies the classical
certificate and sensitive-support hitting principle used inside the replay argument.
Loday, [Realization of the Stasheff polytope](https://arxiv.org/pdf/math/0212126v1), §1 and §2.8,
supplies the planar ordered-tree and Tamari background for the source shapes.

The generic overlap with [ActualExactTraceCompiler.exactObserver, firstRaw and exact_all_history_factorization][ExactTrace]
is finite coarse control with chronological first-occurrence raw caches and absorbing halts. The source-specific
shortlex construction and complete-window reconstruction remain those of parent theorem 57.2 and chapter 66.3.
[ActualObserverFiniteTable.bounded_table_representation][FiniteTable] represents the already supplied attaining observer:
its bounds cover requests and decoded addresses on every nominal row, and its relabelling preserves the complete carrier.
This representation supplies neither actual reachability nor task correctness. The strategy, exact-competitor and phase
suppliers retain the larger-domain hypotheses stated in parent Mathematical Citation 66.6; none supplies the $W_n$-only
capacity conclusion, original prefix emission or observer acquisition.

## 68. Whole-word literal branch/absent fibres

**Definition 68.1 (original trees, addresses and masks).** Let $\mathcal T$ be all
nonempty finite ordered full binary trees with leaves $\alpha,\beta$. The substitution
and Fibonacci trees are

$$
\rho(\alpha)=\beta,\qquad \rho(\beta)=(\beta,\alpha),\qquad
\rho(s,t)=(\rho s,\rho t),\qquad T_n=\rho^n(\alpha).
$$

The leaf word $w$ reads leaves from left to right, writing $a$ for $\alpha$ and $b$ for
$\beta$. The address set $\mathcal A$ consists of finite words in $L,R$, including the root $\varepsilon$; $U|_q$
is its subtree when present. The native readout $r(q,U)$ is $\alpha$ or $\beta$ at the
corresponding leaf, $\mathsf{br}$ at a branch, and $\mathsf{abs}$ when the address is
absent. Every address is queryable, including descendants of absent nodes. Put

$$
\begin{gathered}
B=T_3=((\beta,\alpha),\beta),\qquad D=(\beta,(\alpha,\beta)),\\
P_n=\{p:T_n|_p=B\},\qquad J_n=\{pL:p\in P_n\},\qquad
W_n=\{U\in\mathcal T:w(U)=w(T_n)\},\\
\kappa(\mathsf{br})=\kappa(\mathsf{abs})=\mathsf{none},\qquad
\kappa(\alpha)=\mathsf{some\ true},\quad
\kappa(\beta)=\mathsf{some\ false}.
\end{gathered}
$$

Take $F(0)=0,F(1)=1,F(t+2)=F(t+1)+F(t)$. Write $q_1,\ldots,q_j$ for the original
shortlex list of $J_n$, ordered by length and then lexicographically with $L<R$, and
write $q_i=p_iL$. A literal mask is $\chi:P_n\to\{\mathsf{br},\mathsf{abs}\}$. Its
realization means one immutable $U\in W_n$ satisfies $r(pL,U)=\chi(p)$ at every
coordinate; a $\beta$ reply does not realize $\mathsf{abs}$. The tree, position and prefix objects are those of
[JM52.1, JM52.2 and JM66.1, (JM.214)–(JM.215)][JM]. The sources are comparison inputs;
the observer has only its native query and halt actions. Planar ordered-tree background:
Loday, *Realization of the Stasheff polytope*, §§1, 2.8 ([original][Loday]).

**Theorem 68.2 (every whole-word literal mask and every first restriction).** For every
$n\ge4$ and every literal mask $\chi$ there exists one $U_\chi\in W_n$ such that

$$
r(pL,U_\chi)=\chi(p)\quad(p\in P_n),\qquad j=|P_n|=F(n-2).
\tag{JM.234}
$$

For every $0\le k\le j$ and every $\sigma\in\{\mathsf{br},\mathsf{abs}\}^k$, one such
whole-word source satisfies $r(q_i,U)=\sigma_i$ for $1\le i\le k$.

Proof. The structural recurrence $T_n=(T_{n-1},T_{n-2})$ for $n\ge3$ and the position
facts are supplied by [JM52.2, (JM.153), (JM.156)][JM]. Their exact correspondence is
$P_2=\varnothing$, $P_3=\{\varepsilon\}$, $P_4=\{L\}$, $P_5=\{LL,R\}$, and

$$
P_n=LP_{n-1}\mathbin{\dot\cup}RP_{n-2}\quad(n\ge4),
\qquad |P_n|=F(n-2).
\tag{JM.235}
$$

Indeed, for $n\ge4$ the root has more than three leaves, so every $B$ occurrence lies in
exactly one child. The cardinalities start at one for $n=3,4$ and then obey the
Fibonacci recurrence. Distinct $B$ occurrences cannot be comparable by prefix: a proper
subtree has fewer leaves than its enclosing tree, whereas both occurrences have three
leaves. Thus $P_n$ is an antichain and its distinct address cones are disjoint.
Appending $L$ preserves distinctness and incomparability, so the $q_i$ are distinct. The
supplied $B/D$ replacement cube preserves the entire word $bab$ at each hole, but gives
$\mathsf{br}/\beta$ at $pL$; the following whole-source construction supplies the
literal absent values.

For $n=4$, the two bases are

$$
T_4=(B,(\beta,\alpha)),\qquad
Z_4=(\beta,((\alpha,(\beta,\beta)),\alpha)).
$$

Both words are $babba$. In $T_4$, $LL$ is the branch $(\beta,\alpha)$; in $Z_4$, $L$ is
the leaf $\beta$, hence $LL$ is absent. These are exactly the branch and absent sources
of [JM59.1, (JM.184)–(JM.185)][JM].

For the $n=5$ base inspection, display coordinates $(LLL,RL)$; their original shortlex
order is $(RL,LLL)$. The four sources are

$$
\begin{array}{c|c}
\text{source}&(r(LLL,\cdot),r(RL,\cdot))\\ \hline
T_5=(T_4,B)&(\mathsf{br},\mathsf{br})\\
X_5=(Z_4,B)&(\mathsf{abs},\mathsf{br})\\
Y_5=((B,(\beta,(\alpha,(\beta,\alpha)))),\beta)&(\mathsf{br},\mathsf{abs})\\
A_5=((\beta,(\alpha,(\beta,(\beta,(\alpha,(\beta,\alpha)))))),\beta)&(\mathsf{abs},\mathsf{abs})
\end{array}
$$

Every displayed word is $babbabab$. For $T_5$, $LLL$ is the left branch of $B$ inside
$T_4$, and $RL$ is the left branch of the right $B$. For $X_5$, $LL$ is a leaf while the
right $B$ is unchanged. For $Y_5$, $LL=B$ and $R$ is a leaf. For $A_5$, both $LL$ and
$R$ are leaves. These observations prove every entry, hence all four masks.

For $n\ge6$, restrict $\chi$ along the two components of (JM.235). Both indices $n-1,n-2$
are at least four, so induction supplies $U_L\in W_{n-1}$ and $U_R\in W_{n-2}$ realizing
those restrictions. Set $U_\chi=(U_L,U_R)$. Its word is $w(T_{n-1})w(T_{n-2})=w(T_n)$.
For $p=Ls$ the reply at $pL$ is $r(sL,U_L)$; for $p=Rs$ it is $r(sL,U_R)$. The disjoint
decomposition covers every original coordinate, proving (JM.234) simultaneously on one
source. This argument pairs whole components; it requires no observer modification of a
hole. Finally extend any first $k$ word to a full mask by assigning $\mathsf{br}$ at the
remaining coordinates and apply (JM.234). The antichain used here concerns actual $B$
subtrees, rather than overlapping $bab$ fields of the leaf word. The Boolean
block-sensitivity background in Buhrman–de Wolf, *Complexity Measures and Decision Tree
Complexity: A Survey*, §4.2 ([original][BdW]), supplies no tree-mask realization.
$\square$

**Theorem 68.3 (literal three-leaf boundary).** At $n=3$, $W_3=\{B,D\}$, $J_3=\{L\}$, and
no source realizes the absent mask.

Proof. A full ordered binary tree with three leaves has a root split of one plus two
leaves or two plus one leaves. Its fixed word $bab$ uniquely labels each split, giving
exactly $D$ or $B$. Their replies at $L$ are respectively $\beta$ and $\mathsf{br}$,
with coarse values $\mathsf{some\ false}$ and $\mathsf{none}$. Neither is absent. This
boundary uses the original [JM52.1][JM] trees and readout. $\square$

## 69. Original-native actual prefixes and row capacity

**Definition 69.1 (native observer and histories).** For a fixed $n\ge4$, let $M$ be the
original finite complete [Observer][Native] on all rows of $E$, with source-independent
$e_0$, action $E\to\mathcal A+\mathrm{Bool}$, transition
$E\times\{\alpha,\beta,\mathsf{br},\mathsf{abs}\}\to E$, and decoder
$E\to\mathrm{RawHistory}$. A raw history is an ordered list of literal-address/raw-reply
pairs, retaining repetitions; every row's decoded address list is duplicate-free. On a
query $q$, `queryReply` returns its stored raw value on a cache hit and $r(q,U)$ on a
miss. `cacheUpdate` leaves a hit unchanged and appends $(q,y)$ on a miss. Let $C(h)$
fold this update through $h$ from the empty cache.

The native `barStep` uses the response transition at a query row and fixes a halt row.
`historyState` folds `barStep` from $e_0$ through the replies of $h$, ignoring reported
address labels; `historyAction` is the action at that row. $\kappa_{\rm hist}$ keeps all
address labels and order and applies $\kappa$ to each reply. `ActualPrefix(M,U,e,h)`
starts at $(e_0,[])$ and extends only when the current action queries $q$, using
`queryReply(decoder(e),q,U)` for the next transition and appended report. It has no step
after halt. This is separate from native `Run`, which records finite execution ending at
a Boolean halt row.

`Legal(M,U)` asserts the empty initial decoder and, at every actual prefix, truth of
every decoded raw reply about the same immutable $U$ and the exact `cacheUpdate` decoder
law for the current queried address. Truth is required at actual prefixes; decoded
address distinctness is required on all nominal rows. Thus repeated and absent replies
remain raw evidence, while counterfactual response folds after halt are absorbing. All
these definitions retain their exact [native meanings][Native].

**Hypothesis 69.2 (original emission and coarse action contract).** Assume
$\operatorname{Legal}(M,U)$ for every $U\in W_n$; the common initial decoder is empty.
Assume `historyAction M` factors through $\kappa_{\rm hist}$ on all finite histories,
including unrealizable replies, arbitrary or repeated address labels, and posthalt
reports: $\kappa_{\rm hist}h=\kappa_{\rm hist}h'$ implies equal historyAction values.
Assume that on $T_n$ the actual execution emits exactly the original initial
query/reply list

$$
h_n=((q_i,\mathsf{br}))_{i=1}^{j},\qquad j=F(n-2),
\tag{JM.236}
$$

in the shortlex order of Definition 68.1, with no earlier halt. Equivalently, it reaches
an `ActualPrefix` with history $h_n$; the row after query $j$ may halt or continue. The
emission is exactly [JM66.1, (JM.214)][JM]. The factorization is the native relation
characterized by
[ActualObserverPairReach.pairActionInvariant_iff_allHistoryFactorization][Pair]. These
hypotheses impose no task correctness, finite termination on other sources, or extension
of legality to a larger `Allowed(N)` domain.

**Theorem 69.3 (derived actual-prefix transport).** Under Hypothesis 69.2, for every $0\le
k\le j$ and $\sigma\in\{\mathsf{br},\mathsf{abs}\}^k$, there are $U\in W_n$ and $e\in E$
with $\operatorname{ActualPrefix}(M,U,e,h_{k,\sigma})$, where
$h_{k,\sigma}=((q_i,\sigma_i))_{i=1}^{k}$. The execution makes all $k$ queries before
any halt, and its reached row satisfies $e=\operatorname{historyState}(M,h_{k,\sigma})$
and $\operatorname{decoder}(e)=h_{k,\sigma}$.

Proof. Choose one whole-word source by Theorem 68.2 and use it throughout. Induct on
$i=0,\ldots,k$. Initially `ActualPrefix.initial` gives the common row, and Legal gives
its empty decoder. Suppose the source prefix of length $i<k$ is actual. By
[actualPrefix_semantics][Native] its row is historyState and its decoder is $C(h)$,
where $h$ is that raw prefix. The actual $T_n$ prefix of length $i$ has the same coarse
history: the same $q_1,\ldots,q_i$
and only coarse-none replies. ALL-HISTORY factorization therefore equates their
historyAction values. By the supplied $T_n$ emission, the next action is the query
$q_{i+1}$, so this source has not halted. The exact prefix decoder contains only the
first $i$ distinct addresses, hence $q_{i+1}$ is a cache miss; its raw reply is
$r(q_{i+1},U)=\sigma_{i+1}$. Native `ActualPrefix.query` extends the actual prefix by
this pair. Legal appends it to the decoder, and actualPrefix_semantics identifies the
new row with its response fold. This proves the induction, including the last reached
row even if it halts. More generally [queryReply_eq_readout][Native] handles every
truthful hit; cacheUpdate retains the first occurrence, including raw absence. No
posthalt report is added to an actual prefix, although the all-history contract still
covers its absorbing counterfactual fold. $\square$

**Theorem 69.4 (actual reachable row capacity).** Under Hypothesis 69.2, let $\mathcal
R_n$ be the rows reached by actual prefixes $h_{k,\sigma}$ on sources in $W_n$, for all
$0\le k\le j$ and all such $\sigma$. Then

$$
|\mathcal R_n|\ge\sum_{k=0}^{j}2^k=2^{F(n-2)+1}-1,
\qquad |E|\ge|\mathcal R_n|.
\tag{JM.237}
$$

Proof. Theorem 69.3 supplies an actual row for every $(k,\sigma)$, including $(0,[])$,
with decoder exactly $h_{k,\sigma}$ in first-occurrence order. Different lengths give
different decoder support sizes. At equal length, different masks give different raw
values at an address. Thus no single row can serve two pairs, since decoder is a fixed
function of the row. There are $2^k$ masks at length $k$, yielding the geometric sum.
Every such row belongs to the original complete finite $E$, giving the second
inequality. The comparison uses actual source prefixes established in Theorem 69.3.
[ActualAcquisitionCacheFiber.cacheEquiv and compatible_cache_card][Cache] count all
nominal lifts of a coarse history, including unrealizable ones; here every lift of these
distinct-address coarse-none prefixes is realized by Theorems 68.2 and 69.3 before the
rows are counted. Contextual distinguishability background: Kozen, *On the Myhill–Nerode
Theorem for Trees* ([original][Kozen]); the separation here is by the actual raw
decoder. The premises provide the actual emission, not a minimum-state construction or a
physical memory, query, time, communication or termination bound. $\square$

[JM]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[Native]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.lean
[Pair]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPairReach.lean
[Cache]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.lean
[Loday]: https://arxiv.org/pdf/math/0212126v1.pdf
[Kozen]: https://www.cs.cornell.edu/~kozen/Papers/mn.pdf
[BdW]: https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf

[JM52]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[Source]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[Readout]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[Geometry]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.lean
[Coarse]: https://github.com/the-omega-institute/trureturing/blob/1590efae55f93022396cb1984f0014bbc73b8f65/D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.lean

[JMPublic]: https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[JMOldRaw]: https://github.com/the-omega-institute/trureturing/blob/cf4b9edd2cf0b4410767cfd5e409b29753586105/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[ExactTrace]: https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.lean
[FiniteTable]: https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lean

## 追加锚（本行以下为增补区）
