# Sparse acquisition of a native entry and its completed history

This continuation of [Rooted Boundary History Recovery, §44](RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md#44-sparse-acquisition-of-an-unknown-entry-and-its-native-history) concerns an unknown attained entry and one stationary actual source. It gives ordinary mathematical proofs, without a new Lean certification. Its acquired description is a finite semantic boundary for the existing executor; physical authority and controller completion remain separate premises.

## 1. The actual source and the paid controller

**Definition 1.1 (instance and accessible input).** Let $\mathcal T$ be the nonempty finite ordered binary trees with leaf labels $\alpha,\beta$. Put

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

An attained tree is obtained from alpha by finitely many original guarded promotions $P_p$ and splits $S_p$, at actual logical leaf addresses. Write $\mathcal D_+$ for these trees with alpha excluded. Equivalently, the root has birth sort $B$, a branch has children of sorts $B,A$, a $B$ leaf must be beta, and an $A$ leaf may be alpha or beta. This is the attained-domain characterization of Native Local Source Execution and Rooted §43.1. For a tree $u$ let $a(u),b(u),\ell(u)$ count its alpha, beta and total leaves, and put

$$
n(u)=a(u)+2b(u)-1,\qquad w(u)=a(u)+2b(u).
\tag{1.1}
$$

On an authentic attained entry, $n$ is the number of successful primitive events since alpha; it is not the number of macros, rho epochs or all controller events.

Fix an authentic integer $n_0>1$, an unknown attained entry $t$ with $n(t)=n_0$, and a finite chronological word $W=X_1\cdots X_m$ over $\{F,G\}$. Here $F$ is LAB Definition 9.3's sealed OLD-frontier substitution, and $G$ splits just the CURRENT leftmost beta. Every letter includes all its maintenance, full responses, acknowledgements, inner returns and genuine outer return. The current logical register is

$$
z=\operatorname{Run}(W,t).
\tag{1.2}
$$

The acquisition starts at an actual completed checkpoint, with a live callable controller before absorbing Stop. It receives ONLY $n_0$, common code and the permitted live interface to this one authentic root/source binding and certification epoch. It receives no $t,W,m$, expanded $z$, current depth, old syntax, source-dependent advice, or readable past chronology. The stationary interval permits every finite logical address, including absent addresses, and returns exactly alpha, beta, branch or absent. Beta's unary material marker is excluded. A reply has no timing or identity side channel. The source and epoch do not change during acquisition; actual access, response transport, isolation and sufficient finite backing are supplied conditions.

The same installation retains its old tapes, rights, source resources and protocol obligations. Inaccessibility of those tapes as acquisition advice does not erase them. Finite instances have finite paid supply; no fixed arena accommodates every $W$.

**Definition 1.2 (accounting).** Each actual literal call, repeated or absent included, contributes one to $Q$. If its fully submitted address is $p$, charge $|p|$ address letters; put $L=\sum|p|$ and $D=\max|p|$. Every address is submitted from the bound root, without a free cursor. All replies are retained in full. Controller computation uses finite binary strings with charged bit reads/writes, finite arithmetic, allocation, stacks, comparisons, copying, records and complete output. A unit cost is a bounded bit operation; unbounded integer arithmetic is not one operation.

Let $b$ be the complete size of the fixed live interface/binding metadata and saved caller linkage that must be carried or copied. It is paid, not an extra history oracle. Bounds for added controller work and backing below hold with constants for a fixed such interface; with varying metadata their displayed bound includes $b$. Actual field navigation, reference widths, service, ACK/return and existing installation/journal charges are additionally paid at their supplied prices. Those prices are not assumed to be functions of logical address length alone. In particular a concrete adapter using unary whole-installation ordinals, or a large old archive, is not assigned a polynomial total physical bill by this controller analysis.

Records here contain every new actual address, full reply and source/epoch binding, and the local actions required by the installed recording contract. Existing Native Literal Journal Adapter §§5–8 supplies pending/sealed/copied rows, Full/NextCompat and their same-source equations where that adapter is used. There is no replacement journal or omission of its additional fields and costs.

## 2. Coordinates that can be earned without the entry

**Theorem 2.1 (a bounded uncertainty window for the total substitution count).** Write $d=\lambda(t)$ for the leftmost binary depth of $t$, and uniquely write

$$
t=\operatorname{Sp}(r_1,\ldots,r_d)
 =\langle\cdots\langle\langle\beta,r_d\rangle,r_{d-1}\rangle\cdots,r_1\rangle.
$$

Thus $r_1$ is the outermost right subtree. Let $H=\lambda(z)$, $K=|W|_F$, and $k_j=|X_{j+1}\cdots X_m|_F$. Then

$$
\begin{gathered}
1\le d\le n_0-1,\qquad H=d+m,\qquad 0\le K\le m\le H,\\
z=\operatorname{Sp}(\rho^K r_1,\ldots,\rho^K r_d,
                       P_{k_1},\ldots,P_{k_m}),\qquad P_q=\rho^q\alpha,\\
n_0=1+\sum_{i=1}^d w(r_i),\qquad \ell(t)\le n_0.
\end{gathered}
\tag{2.1}
$$

The row at position $i$ has root address $a_i=L^{i-1}R$. Every subtree of $z$ has height at most $H+n_0$. If $h_1$ is the leftmost depth of the current first right subtree, then

$$
K\in J=\{\max(0,h_1-n_0),\ldots,\min(H,h_1+1)\},
\qquad |J|\le n_0+2.
\tag{2.2}
$$

Neither $H$ nor $h_1$ is initial input.

Proof. Rooted Lemma 42.2 already proves the spine expansion and $H=d+m$. Each macro preserves old spine branches and adds exactly one new terminal spine position; later $F$ acts on every old right subtree, while $G$ leaves it unchanged. The entry has at least one beta, so $n_0=\ell(t)+b(t)-1\ge\ell(t)$; it is multileaf because $n_0>1$. Its number of branches is $\ell(t)-1$, bounding $d$ and the height of every entry subtree. Summing weights along its spine, including the terminal beta of weight two, gives the third line of (2.1). Each $F$ or $G$ increases height by at most one, whence $\operatorname{height}(z)\le n_0-1+m\le H+n_0$.

The correct pure-tree recurrence is

$$
P_0=\alpha,\quad P_1=\beta,\quad
P_{q+2}=\langle P_{q+1},P_q\rangle\quad(q\ge0).
\tag{2.3}
$$

It follows first at $q=0$ from $\rho\beta$, and thereafter by applying the homomorphism $\rho$ to both children. Consequently $\lambda(P_q)=\max(q-1,0)$. Every branch satisfying either birth sort has a beta at the end of its left descent. Substitution preserves that descent and replaces its terminal beta by $P_{K+1}$. Therefore

$$
\lambda(\rho^K u)=
\begin{cases}
\max(K-1,0),&u=\alpha,\\
K+\lambda(u),&u\ne\alpha\text{ and }u\text{ satisfies a birth sort}.
\end{cases}
\tag{2.4}
$$

For $u=r_1$, its depth is at most $n_0-1$. In the alpha case $K$ is zero or $h_1+1$; in every other case $0\le h_1-K\le n_0-1$. These alternatives imply (2.2). All coordinates so far are mathematical projections; the next procedure obtains them through actual reads. $\square$

**Definition 2.2 (the depth and tail observations).** Read the root, then $L,L^2,\ldots$, following branch replies until the first leaf. A promised instance ends at beta. Its acquired address length is $H$; other terminal tags may be rejected. Set

$$
s=\min(n_0,H),\qquad B=H+n_0+2.
$$

For each $1\le i\le s$, obtain the first right subtree's root reply at $a_i$, and its exact leftmost depth $h_i$, as follows. If the root is a leaf, return depth zero. Otherwise query $a_iL^B$ and require a nonbranch reply. On the integer bracket $[0,B]$, with lower endpoint branch and upper endpoint nonbranch, repeatedly query its integer midpoint and retain the bracket for the FIRST nonbranch. At adjacent endpoints return the upper one and its actual reply. On a genuine finite tree that reply is its leftmost leaf. At most $2+\lceil\log_2(B+1)\rceil$ calls per row suffice, including root and upper endpoint.

Define a tentative pure level for these rows by

$$
\widehat q_i=
\begin{cases}
0,&\text{root alpha},\\
1,&\text{root beta},\\
h_i+1,&\text{root branch}.
\end{cases}
\tag{2.5}
$$

This assigns a number even to an impure branch; it does NOT certify purity.

If $H>s$, positions $s+1,\ldots,H$ are certainly born after attachment, since $d\le n_0-1$. Read $a_H$ and require alpha; set $\widehat q_H=0$. Scan $i=H-1,\ldots,s+1$. Given $q=\widehat q_{i+1}$, query $a_i$ if $q=0$, and $a_iL^{q-1}$ if $q\ge1$. At $q=0$ the replies alpha/beta select $q$/$q+1$; at $q\ge1$ the replies beta/branch select $q$/$q+1$. Reject other replies. This uses at most $H-s$ calls. If $H\le n_0$, this tail phase is empty.

**Theorem 2.3 (what these observations establish).** On every promised instance the depth and tail phases terminate. They earn $H$, all $h_i$ in their stated range, the window $J$, and the exact $\widehat q_i=k_{i-d}$ at EVERY born position $i>d$. They make at most

$$
H+1+s\bigl(2+\lceil\log_2(B+1)\rceil\bigr)+(H-s)
\tag{2.6}
$$

calls. Initial positions may still be impure; no row is discarded on the assumption that its assigned pure level describes that entire row.

Proof. The first phase literally follows the finite spine. For each head row, (2.1)'s height bound makes $B$ nonbranch. On a left descent, the branch predicate is true exactly below the first leaf depth. Bisection therefore returns that depth, including zero. Formula (2.3) shows that a genuinely pure row has exactly the level (2.5), with alpha and beta separating the two zero-depth cases.

On the guaranteed born tail, the last row is $P_0$. Consecutive born levels satisfy $k_{j-1}=k_j+\mathbf1_{X_j=F}$. At $q=0$, $P_0,P_1$ have root tags alpha,beta. At $q\ge1$, (2.3) gives beta at $L^{q-1}$ in $P_q$ and branch there in $P_{q+1}$. Induction backwards therefore proves all tail selections. Born rows among the first $s$ positions were covered by the depth phase. This proves the exact statement while leaving the nonborn rows unconstrained except by their actual reads. $\square$

## 3. A polynomial list that includes every consistent promised source

**Definition 3.1 (bounded inverse probes).** For a tested integer $K\in J$, a current row rooted at $a_i$, and a relative old address $p$, use the known-lag literal decoder of [Sparse Literal History Transport, Definition 2.1 and Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md). Prefix EACH of its one or two support addresses by the actually acquired $a_i$, and pay for the full current-root call. Denote the decoded old reply by $V_{K,i}(p)$.

Explicitly, $K=0$ reads $a_ip$. For $K>0$, put $u=\lfloor K/2\rfloor$, $v=\lceil K/2\rceil$. The leaf-tag coordinate is $a_ipR^v$. For nonempty $p$, the existence coordinate is $a_ip^-R^{u+1}$; its guard is nonabsent for even $K$, and beta-or-branch for odd $K$. A false guard returns old absent. Otherwise the even table returns alpha/beta/branch from those same tags, and the odd table maps absent to alpha, alpha to beta, beta or branch to branch. The impossible even guarded-absent case is assigned absent. At the relative root there is no existence guard. Coincident or repeated support calls may still be charged separately; the bound is two.

If the actual row is $\rho^K r$, that supplied theorem gives $V_{K,i}(p)=r_r(p)$ for EVERY $p$, including absent positions. For a wrong $K$ its output is just a numerical attempt. It is not an image or provenance test.

**Definition 3.2 (candidate generation).** Test each integer in the earned window $J$ once, in increasing order. For that $K$, parse consecutive entry-right candidates $r_1',r_2',\ldots$ using $V_{K,i}$ at their relative roots and at both children of every decoded branch. Use depth-first order. Reject an absent reply at a required node, a failed birth-sort test, or any attempt to process more than $2n_0$ virtual nodes in TOTAL for this $K$. In particular a nonterminating phantom branch expansion is cut off. Complete each parsed row before using it. Compute its positive leaf weight $w(r_i')$ with paid exact counters.

Stop at the first complete row $d'$ for which

$$
\sum_{i=1}^{d'} w(r_i')=n_0-1.
\tag{3.1}
$$

Reject an overshoot, exhaustion of the $H$ rows before equality, or more than $n_0-1$ rows. Set $t'=\operatorname{Sp}(r_1',\ldots,r_{d'}')$ and $m'=H-d'$. Require $0\le K\le m'$. If $m'=0$, require $K=0$ and set $W'=\varepsilon$.

If $m'>0$, use ONLY the assigned levels at positions $d'+1,\ldots,H$. Require

$$
\widehat q_H=0,\qquad
\widehat q_i-\widehat q_{i+1}\in\{0,1\}\quad(d'+1\le i<H),
\qquad K-\widehat q_{d'+1}\in\{0,1\}.
\tag{3.2}
$$

Set $X_1'=F$ exactly when the last difference is one. For $2\le j\le m'$, set $X_j'=F$ exactly when $\widehat q_{d'+j-1}-\widehat q_{d'+j}=1$; otherwise use $G$. Set $W'=X_1'\cdots X_{m'}'$. Thus $|W'|_F=K$ by telescoping. Keep the candidate $(t',W')$, together with its exact compact source value $z'=\operatorname{Run}(W',t')$.

Keep the complete actual read transcript from all phases and all tested $K$. After generating the list, discard EVERY candidate whose own exact compact source value disagrees with ANY recorded literal response. No numerical inverse is accepted without this check. This is still only a consistency check on finite observations; the discrimination phase below is essential.

**Theorem 3.3 (genuine survival and completeness of the list).** On every promised instance candidate generation uses at most $4n_0(n_0+2)$ additional raw calls and retains the genuine $(t,W)$. It produces at most $n_0+2$ candidates. More strongly, let $\tau$ be the full transcript at its end. The resulting list is EXACTLY

$$
\{(u,V):u\in\mathcal D_+,\ n(u)=n_0,\
           r_{\operatorname{Run}(V,u)}(p)=c
                 \text{ for every actual row }(p,c)\text{ of }\tau\}.
\tag{3.3}
$$

The conditioning includes common accessible input, stationary binding and interface. Formula (3.3) describes logical orbit possibilities, not alternative authentic identities or a license to instantiate all of them physically.

Proof. The true $K$ belongs to $J$ by Theorem 2.1. For its first $d$ rows the actual image is $\rho^K r_i$; the reused literal decoder therefore parses precisely $r_i$. The total number of nodes in these right subtrees is

$$
\sum_i(2\ell(r_i)-1)\le 2\sum_i w(r_i)=2(n_0-1)<2n_0.
$$

So the node cap cannot reject the genuine case. Positive weights and (2.1) make (3.1) occur exactly at $d$. Born levels are exact by Theorem 2.3, hence (3.2) reconstructs precisely $W$, including its first letter from $K$. All actual read rows agree with $z$, including queries made during unsuccessful candidate attempts. The true pair survives.

Each tested $K$ performs at most $2n_0$ virtual-node probes, at most two raw calls per probe. There is at most one parsed pair per $K$, and at most $n_0+2$ tested values. These prove the count bounds.

Every retained candidate has a completed finite parse, correct birth sorts and (3.1), so its entry is genuinely in $\mathcal D_+$ and has index $n_0$. It has a well-defined word and passes every transcript row. Thus it belongs to the right side of (3.3).

Conversely fix ANY pair $(u,V)$ on that right side. Because the controller is deterministic and uses only common inputs and replies, that source reproduces the same actual acquired query sequence, all brackets and the same generation control. In particular its acquired spine has length $H$ and its first head depth is $h_1$. Apply Theorems 2.1–2.3 to this pair: $|V|_F$ is one of the tested $K$, and its own born levels are the computed ones. During that test its first right rows are actual $K$ images of the right subtrees of $u$. The known-lag decoder therefore parses them exactly, within the same node budget; the weight stopping rule finds exactly $\lambda(u)$, and (3.2) reconstructs exactly $V$. This pair was generated and its assumed agreement with all of $\tau$ prevents discarding it. This proves the reverse inclusion and accounts for ALL ambiguity after the sparse observations. No exhaustive catalog of attained seeds is used. $\square$

## 4. Lawful discrimination without expanding the source

**Definition 4.1 (the finite candidate representation).** Use a ground acyclic term DAG: leaves alpha/beta, or a branch pointing to two earlier nodes. Its value is its fully unfolded ordered tree, but that unfolding is not computed. Store $P_0,\ldots,P_{H+1}$ with recurrence (2.3). For a candidate with count $K$, copy its parsed right-subtree skeletons, replacing each alpha leaf by a reference to $P_K$ and each beta leaf by a reference to $P_{K+1}$. Then form the $H$ spine branches, with the copied old right roots, the references $P_{\widehat q_i}$ at born positions, and terminal beta. Formula (2.1) and (3.2) prove that the resulting root is exactly $\operatorname{Run}(W',t')$. It uses $O(n_0+H)$ nodes per candidate.

For comparison, give alpha and beta distinct canonical identifiers. In a topological scan assign a branch the identifier of the ordered pair of its children's identifiers, reusing a previous identical pair and otherwise assigning a fresh one. A finite linear dictionary scan suffices; no probabilistic hash or constant-time unbounded integer is assumed. Equal canonical identifiers mean equal tree values by induction, and equal tree values give equal identifiers by their constructors. This is the standard equality procedure for supplied finite term DAGs, used here as an intermediate tool.

For different roots, find a literal separating address as follows. At the current pair, if their root tags differ, return the path already constructed. Otherwise both are branches; descend to the left child pair if their identifiers differ, and to the right child pair otherwise. At least one pair differs. Each descent shortens tree height. It stops at unequal tags, providing a concrete address where the two candidate values have different four-valued replies. Its length is bounded by their heights, at most $H+n_0$.

**Theorem 4.2 (exact sparse acquisition).** After Definition 3.2, while at least two candidates remain, choose two, construct the separating address of Definition 4.1, and submit it to the SAME live source. Retain only candidates whose compact value has the received full reply there. Continue until one candidate remains, and hand over that pair without executing Stop. On every instance of Definition 1.1 this is one effective source-blind procedure returning exactly $(t,W)$ and the exact current-source description

$$
\mathsf C=\bigl(t,W\bigr),\qquad
\operatorname{value}(\mathsf C)=\operatorname{Run}(W,t)=z.
\tag{4.1}
$$

It uses at most $n_0+1$ additional discrimination calls. An empty candidate list or a contradictory reply may return failure. A singleton on an OFF-promise source is not asserted to recognize that source.

Proof. Theorem 3.3 starts with a nonempty list containing the true pair and exactly every promised pair consistent with the transcript. Rooted Theorem 42.4, equivalently the injectivity conjunct of the existing `completed_history_recovery`, says that two different such pairs cannot have equal full source values when $n_0>1$. Thus any two different candidates have an effective separating address. Its read eliminates at least one of the chosen pair, even if the actual response agrees with neither. It never eliminates the true pair. The same equality (3.3), with the additional rows imposed, is preserved at each step. A list of at most $n_0+2$ therefore reaches a singleton within $n_0+1$ calls. That singleton is the true pair, and no other promised pair is consistent with the final transcript.

All selected addresses are finite and legal for the stated literal service, even when the true response is absent. Every local operation uses just already acquired finite strings or the finite candidate DAGs. Their equality comparison compares descriptions supplied by candidate generation, rather than asking for hidden equality with the source. Its witness then becomes a real paid source query. In particular the proof never promotes a guessed inverse, an untested pure row or a numeric count to certification of an unobserved entire subtree.

The input promise authenticates the actual orbit and completion cut. The reasoning does not test authenticity, occurrence identity or native provenance. Outside that promise a different source can agree with finite queried rows; the procedure's conditional guarantee does not become an off-promise recognizer. $\square$

## 5. Simultaneous query, address and local resource bounds

**Theorem 5.1 (explicit bill and compact output).** Let

$$
N=H+n_0+2,\quad A=\lceil\log_2(N+1)\rceil,\quad
\overline Q=2H+4n_0(n_0+2)+n_0(A+5)+8,\quad
\overline D=H+3n_0+4.
\tag{5.1}
$$

On every promised instance the complete acquisition above has

$$
\begin{aligned}
Q&\le\overline Q=O\bigl(H+n_0^2+n_0\log(H+n_0+2)\bigr),\\
D&\le\overline D=O(H+n_0),\\
L&\le\overline Q\,\overline D
 =O\bigl((H+n_0)(H+n_0^2+n_0\log(H+n_0+2))\bigr).
\end{aligned}
\tag{5.2}
$$

The fully emitted description (4.1), with the entry in literal constructor syntax and the chronological word in one fixed letter code, has $O(n_0+m)$ bits/symbols. It need not contain a separately stored list of binary exponents. Added local bit work, backing, complete local/read records, copying and output admit, for example, the conservative bound $O((b+1)N^8)$ under Definition 1.2. These are polynomial bounds in the NUMERIC parameters $n_0+H$ for a fixed live interface. No polynomial bound in the bit length of $n_0$ or on total installation physical time is asserted.

Proof of query and address bounds. Theorem 2.3 gives at most $2H+1+n_0(2+A)$ calls. Generation adds at most $4n_0(n_0+2)$ and discrimination adds at most $n_0+1$. Their sum is bounded by (5.1). No dictionary, consistency test or description evaluation makes a source call.

The initial spine reads have length at most $H$. Head-depth reads have length at most $s+B\le H+2n_0+2$. On the genuine far tail, a queried offset has $q\le H-i$, hence its length is at most $H+1$. During a wrong-$K$ parse the virtual-node cap bounds each relative path length by $2n_0$; a row index is at most $n_0-1$ and $K\le H$. The known-lag supports have length at most $|p|+\lceil K/2\rceil$, so their complete actual addresses have length at most $3n_0+\lceil H/2\rceil$. A separating address has length at most $H+n_0$. All are below $\overline D$. Charging EVERY complete submitted word gives the product bound for $L$; no sharper submitted-letter estimate is needed.

Proof of compactness and local bounds. The entry has at most $n_0$ leaves and $2n_0-1$ total nodes. A prefix constructor encoding uses a constant number of bits per node, and $W$ uses one bit per letter, with a finite framing of size $O(\log(n_0+m+2))$. This proves the stated output length, including a second paid copy if both the pair and a separate description packet are delivered. Formula (2.1) constructs a ground DAG from that packet with $O(n_0+H)=O(n_0+m)$ nodes. Pointer encodings have their additional logarithmic width; this auxiliary DAG size in nodes is not falsely reported as its bit size.

For an explicit polynomial implementation, keep all rows and all candidates. Write $C\le n_0+2$ for the candidate count and $S$ for their total ground-DAG nodes, including the shared pure table. Then $S=O(C(n_0+H))=O(N^2)$ and $Q=O(N^2)$, $\overline D=O(N)$. All levels, brackets, row indices, generation budgets, node identifiers and transcript indices have $O(\log N)$ bits. Counts inside each parsed seed are at most $O(n_0)$; no expanded event count or predecessor fuel is enumerated.

Building all parses and candidate words takes polynomial work: at most $2n_0C$ virtual nodes, $CH$ word positions, and at most $Q\overline D$ written address letters. Arithmetic and midpoint operations act on the bounded binary integers just described. Canonicalization by scanning all earlier node pairs uses at most $S^2$ comparisons of $O(\log N)$ bits. Evaluating a candidate reply to a recorded address follows at most $\overline D$ DAG edges, using absent on descent through a leaf. Comparing ALL candidates against ALL old and new rows costs $O(CQ\overline D\log N)$ bit work. At most $C-1$ witness descents each take $O(N\log N)$ bit work. These quantities are bounded by $O(N^5)$ before a choice of bit-tape representation and complete action-record overhead.

Arrays may instead be accessed by linear scans over their $O(N^3)$ encoded bits; allowing that factor and recording each bounded bit operation yields the deliberately conservative $O((b+1)N^8)$ work and backing bound. Address/reply rows alone occupy $O(Q(\overline D+b+\log N))$ bits. Recording local operations, continuation references, all discarded candidates and both complete output copies also fits the same conservative bound. Every retained bit is backed and every copy charged; an abstract source-dependent control state is never used to hide a seed catalog or arithmetic.

This accounts for the acquisition controller's added material. Binding, actual service, transport and recording machinery still consume their real resources. One may add their actual nonnegative bill to these controller charges. In particular neither a preexisting archive nor a concrete unary global journal counter is relabelled as free or proved small by $N$. $\square$

**Theorem 5.2 (deterministic worst-case query order and exponential expansion).** Fix any legitimate multileaf entry $t$, keep its binding and accessible common data independent of future choices, and supply no history-dependent advice. A deterministic acquisition correct on all its finite completed histories has worst-case raw-call count at least $\lceil m/2\rceil$ over the $2^m$ words of length $m$. Thus for fixed $n_0$ the construction has matching $\Theta(m)$ worst-case query order as $m\longrightarrow\infty$ (or $\Theta(m+1)$ with the empty case included).

For $W=F^m$, full expanded traversal has exponential size while the earned description has length $O(n_0+m)$ and the sparse call count is $O(m+1)$ at fixed $n_0$.

Proof. Rooted Theorem 42.4 makes all $2^m$ full endpoints, and their requested words, distinct. Compress only source-independent finite local work in the ANALYSIS of a deterministic query tree. Each actual call has at most four children. For this finite family all runs terminate, so their maximum query depth $q$ is finite. A four-ary tree of maximum depth $q$ has at most $4^q$ leaves, including variable stopping depths. Correct outputs for different words require different leaves; hence $2^m\le4^q$ and $q\ge\lceil m/2\rceil$. Address length and internal computation cannot create an extra observation branch. This is the familiar decision-tree counting argument used as an intermediate tool, with no randomized or error-tolerant extension asserted. The upper bound follows from $H=d+m$ and (5.2) at fixed $n_0$.

For the expansion comparison, $\ell(P_0)=\ell(P_1)=1$ and (2.3) gives the Fibonacci recurrence. In particular $\ell(P_{q+2})\ge2\ell(P_q)$, so $\ell(P_{m+1})\ge2^{\lfloor m/2\rfloor}$. The entry has a beta leaf; its image under $F^m$ contains $P_{m+1}$. Thus any full expanded output or once-per-node traversal writes/visits exponentially many nodes. The old full-syntax supplier, including Native Full Source Producer, pays for that expanded traversal. The new packet (4.1) is obtained through the source rather than presupposed as a supplied grammar. This comparison proves neither optimal elapsed physical time nor a reduced total LAB installation size. $\square$

## 6. Same-source handoff and maintained completed boundaries

**Theorem 6.1 (pre-Stop composition with the existing executor).** Supply Definition 1.1's live pre-Stop controller, the same root/source binding and valid certification lineage, its current rights, actual saved caller continuation, and the existing LAB executor and finite backing for the requested next finite calls. Replace acquisition's successful delivery by a finite local transfer into that saved continuation, carrying the earned packet (4.1). Do not execute an absorbing Stop between acquisition and transfer. This is an actual same-source handoff: the register at transfer is still $z$, and its packet is exact there.

At every subsequently completed outer $X\in\{F,G\}$ return, the paid semantic update

$$
(t,W)\longmapsto(t,WX)
\tag{6.1}
$$

is exact for the current source. The packet is valid at completed checkpoints; during Busy it is retained as the description of the LAST completed checkpoint, not falsely asserted to describe the partially edited current source. Source-edit completion alone does not authorize (6.1).

Proof. Acquisition has only literal reads and local operations, so actual register and epoch remain unchanged. Its terminating finite decision, copying and transfer can be the next local-control segment instead of a Stop instruction. This uses the live saved caller; it does not revive an already absorbed run. The packet's equality at transfer is Theorem 4.2.

For a next call, use the ACTUAL LAB Definition 9.3 procedure: $F$ acquires and seals the current old frontier, and $G$ acquires the current leftmost beta. Navigation, acquired operand references, current grants, reached-reference comparisons and original guards are all executed. The packet is not substituted for any operand or permission. LAB Theorems 9.4 and 11.2 already give the source effect and completion under their finite supply premises. LAB's accepted-event hooks, all ancestral tapes, arithmetic fields, full literal replies, ACKs, inner returns, outer response and genuine outer return are retained. Rooted §§42.5 and 43.3–43.5 already distinguish these phases, even when source effects coincide.

Only after that real outer return does the current source equal $X(\operatorname{Run}(W,t))$ at the next completed checkpoint with completed word $WX$. This proves (6.1) and its iteration by induction. Append/copy and complete response records are paid; the saved completion phase prevents duplicate appending. Between completed checkpoints the old packet remains typed as an old boundary. If source edits have finished but output, ACK or return is pending, $W$ has not changed. The actual phase/continuation supplies this distinction, not a predicted source reply.

These source operations preserve the actual occurrence through their existing binding/certification rules; any permitted certification renewal is recorded by those rules, not inferred from equal syntax. Records use the existing same-source contracts. Native Serial Machine supplies only localStep/read/applyRho/stop; the stationary read/local prefix corresponds to that menu, but its rho-only update theorem is not invoked as an implementation of $G$. The continuation here is LAB's already supplied local split executor. Nor is that split identified with a journal adapter root graft. $\square$

**Theorem 6.2 (short cases and excluded recovery claims).** The acquisition covers $W=\varepsilon$, $m=1$ and $H=1$ without an extra supplier. It does not extend to $n_0=1$ with no first-choice channel. It supplies the current source and completed native macro history as descriptions, together with the conditional handoff of Theorem 6.1. It does not supply full earlier primitive history, all controller/CPU/wait chronology, physical inverse edits, arbitrary busy-cut recovery, arbitrary effective-program execution, four individually minimal view kernels or an infinite coherent thread.

Proof. If $W$ is empty, $H=d\le n_0-1$, the far-tail phase is empty, and the true test $K=0$ parses each actual entry row directly; its weights reach $n_0-1$ at $d=H$. The $m'=0,K=0$ branch keeps precisely this pair, while discrimination disposes of any other consistent candidates. For $m=1$ the only born level is zero; (3.2)'s first difference recovers the one letter from $K\in\{0,1\}$. For $H=1$, $d\ge1$ forces $d=1,m=0$; head-depth zero still distinguishes its alpha and beta possibilities using actual root replies. No tail witness with negative exponent is submitted: $q=0$ is always handled at the row root.

At $n_0=1$ the entry is beta, and $F(\beta)=G(\beta)=\langle\beta,\alpha\rangle$. Their first request identities cannot be distinguished from any subsequent source-only literal transcript. Existing completed-history recovery gives exactly that first-bit pair for each nonempty endpoint and a separate empty endpoint. This is why $n_0>1$ is indispensable here; a genuine retained first-choice channel could condition a separate theorem.

The actual completed-history promise and same-source rights are hypotheses. The unchanged-source and incomplete-call collisions of Rooted §§42.5 and 43 demonstrate why syntax cannot establish them or recover the full controller. The packet omits pre-entry primitive shuffle and protocol/wait events. It grants no inverse source operation, Busy observation permission or universal program installation. Its finite families, bounds and induction at each supplied completed return construct no infinite physical execution or infinite coherent thread. The full RRO mutual-recovery and continuing-research obligations therefore remain open. $\square$

## 7. Source and literature correspondence

**Convention 7.1 (reused statements and the new interface).** [Rooted §§42.1–42.6](RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md#42-unknown-entry-native-histories-and-their-least-initial-reference) supplies exact spine form, unknown-entry uniqueness and the paid expanded-syntax supplier; §§42.7 and 43 supply outer-return distinctions, incomplete fibres, logical coordinates and lawful continuation. This volume uses that uniqueness to distinguish candidates, without running an exponential full-syntax inverse. Its added mathematics is the earned $H$ and bounded $K$ window, polynomial bounded parsing, the exhaustive finite transcript fibre (3.3), actual distinguishing reads and their simultaneous resource account.

The existing [Native Completed History Recovery source](../../../D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery.lean) and [owning Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery.scribe.cs) state `completed_history_recovery` on actually guarded-attained entries with eventIndex $n_0>1$. Its success equivalence, injectivity, original primitive expansion and beta first-bit fibre retain their exact hypotheses. Reading those statements supplies no new compilation or Lean verification of this volume.

[Sparse Literal History Transport, Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) is the known-lag decoder used literally in Definition 3.1, including its existence guard and actual root-prefixed addresses. [Native Dynamic Acquisition Frontiers §§19–24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DYNAMIC_ACQUISITION_FRONTIERS.md#19-原子共同入口上完整新记录的准确索引区间) already separates source-blind actual calls, total submitted letters, atomic substitution index, actual return and macro/event chronology. Those atomic acquisition results are reused boundaries, not advertised here as new results.

[Native Full Source Producer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) supply the expanded once-per-node stationary traversal. [Native Serial Machine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs) supply source-free local control, raw four-valued reads, truthful register execution and the absorbing stop boundary. [Native Local Source Execution](../../../D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution.scribe.cs) supply birth-sort attainment, exact primitive-event indices and original F/G source effects. [LAB §§9–13](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) supplies actual operands, source-preserving traversal, sealed-frontier execution, local splitting, controller phases, complete returns and resource obligations. [Native Literal Journal Adapter §§5–8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LITERAL_JOURNAL_ADAPTER.md#5-the-actual-journal-and-its-pending-complement) supplies its paid same-source record equations and capacity-safe Native correspondence. Its restricted Native correspondence is not extended to $G$ by a renaming of its grafts.

**Convention 7.2 (mature intermediate tools and contribution boundary).** Lohrey–Maneth–Reh, [*Traversing Grammar-Compressed Trees with Constant Delay*, arXiv:1511.02141v2, introduction and Proposition 3](https://arxiv.org/html/1511.02141v2), studies navigation after a grammar-compressed tree is SUPPLIED. Proposition 3 states polynomial-time equality of the values of two supplied TSLPs; it is not the constant-delay traversal proposition. Definition 4.1 needs only its elementary ground-DAG special case, whose exact identifier and witness construction is given there. Neither that paper's supplied-input preprocessing nor its register-cost assumptions acquire our unknown source or pay our submitted letters.

Engelfriet, [*Tree Automata and Tree Grammars*, arXiv:1510.02036v1, Definition 3.62](https://arxiv.org/html/1510.02036v1), defines ranked-tree homomorphisms by substitution of the recursively mapped children. Here the rank-zero images are beta and the beta/alpha branch, and the binary constructor maps to the ordered pair of its two variables. This is precisely the homomorphism behind (2.3) and candidate skeleton replacement, without an acquisition theorem attached to the definition.

Term-DAG equality, finite decision-tree counting, finite-tree parsing and integer bisection are credited intermediate methods. Relative to these methods and the cited repository results, Theorems 3.3–5.1 are a `repo-derived` source-specific acquisition interface with explicit proofs. No worldwide originality or fresh Lean claim is made. Provenance, whole-event chronology, physical recovery, minimal individual views and the infinite RRO target have exactly the unresolved scope described in §6.

## 追加锚（本行以下为增补区）
