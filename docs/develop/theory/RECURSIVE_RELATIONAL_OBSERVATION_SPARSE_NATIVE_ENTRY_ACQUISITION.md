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

The acquisition starts at an actual completed checkpoint, with a live callable controller before absorbing Stop. It receives ONLY $n_0$, common code and the permitted live interface to this one authentic root/source binding and certification epoch. It receives no $t,W,m$, expanded $z$, current depth, old syntax, source-dependent advice, or readable past chronology. Binding/certification tokens authenticate this interface; they supply no readable history counter or other source-dependent control input. The stationary interval permits every finite logical address, including absent addresses, and returns exactly alpha, beta, branch or absent. Beta's unary material marker is excluded. A reply has no timing or identity side channel. The source and epoch do not change during acquisition; actual access, response transport, isolation and sufficient finite backing are supplied conditions.

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

For each $1\le i\le s$, obtain the $i$th right subtree's root reply at $a_i$, and its exact leftmost depth $h_i$, as follows. If the root is a leaf, return depth zero. Otherwise query $a_iL^B$ and require a nonbranch reply. On the integer bracket $[0,B]$, with lower endpoint branch and upper endpoint nonbranch, repeatedly query its integer midpoint and retain the bracket for the FIRST nonbranch. At adjacent endpoints return the upper one and its actual reply. On a genuine finite tree that reply is its leftmost leaf. At most $2+\lceil\log_2(B+1)\rceil$ calls per row suffice, including root and upper endpoint.

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

The fully emitted description (4.1), with the entry in literal constructor syntax and the chronological word in one fixed letter code, has $O(n_0+m)$ bits/symbols. It need not contain a separately stored list of binary exponents. Added local bit work, backing, complete local/read records, copying and output admit, for example, the conservative bound $O((b+1)N^{10})$ under Definition 1.2. These are polynomial bounds in the NUMERIC parameters $n_0+H$ for a fixed live interface. No polynomial bound in the bit length of $n_0$ or on total installation physical time is asserted.

Proof of query and address bounds. Theorem 2.3 gives at most $2H+1+n_0(2+A)$ calls. Generation adds at most $4n_0(n_0+2)$ and discrimination adds at most $n_0+1$. Their sum is bounded by (5.1). No dictionary, consistency test or description evaluation makes a source call.

The initial spine reads have length at most $H$. Head-depth reads have length at most $s+B\le H+2n_0+2$. On the genuine far tail, a queried offset has $q\le H-i$, hence its length is at most $H+1$. During a wrong-$K$ parse the virtual-node cap bounds each relative path length by $2n_0$; a row index is at most $n_0-1$ and $K\le H$. The known-lag supports have length at most $|p|+\lceil K/2\rceil$, so their complete actual addresses have length at most $3n_0+\lceil H/2\rceil$. A separating address has length at most $H+n_0$. All are below $\overline D$. Charging EVERY complete submitted word gives the product bound for $L$; no sharper submitted-letter estimate is needed.

Proof of compactness and local bounds. The entry has at most $n_0$ leaves and $2n_0-1$ total nodes. A prefix constructor encoding uses a constant number of bits per node, and $W$ uses one bit per letter, with a finite framing of size $O(\log(n_0+m+2))$. This proves the stated output length, including a second paid copy if both the pair and a separate description packet are delivered. Formula (2.1) constructs a ground DAG from that packet with $O(n_0+H)=O(n_0+m)$ nodes. Pointer encodings have their additional logarithmic width; this auxiliary DAG size in nodes is not falsely reported as its bit size.

For an explicit polynomial implementation, keep all rows and all candidates. Write $C\le n_0+2$ for the candidate count and $S$ for their total ground-DAG nodes, including the shared pure table. Then $S=O(C(n_0+H))=O(N^2)$ and $Q=O(N^2)$, $\overline D=O(N)$. All levels, brackets, row indices, generation budgets, node identifiers and transcript indices have $O(\log N)$ bits. Counts inside each parsed seed are at most $O(n_0)$; no expanded event count or predecessor fuel is enumerated.

Building all parses and candidate words takes polynomial work: at most $2n_0C$ virtual nodes, $CH$ word positions, and at most $Q\overline D$ written address letters. Arithmetic and midpoint operations act on the bounded binary integers just described. Canonicalization by scanning all earlier node pairs uses at most $S^2$ comparisons of $O(\log N)$ bits. Evaluating a candidate reply to a recorded address follows at most $\overline D$ DAG edges, using absent on descent through a leaf. Comparing ALL candidates against ALL old and new rows costs $O(CQ\overline D\log N)$ bit work. At most $C-1$ witness descents each take $O(N\log N)$ bit work. These quantities are bounded by $O(N^5)$ before a choice of bit-tape representation and complete action-record overhead.

For a bit-tape implementation keep algorithmic workspace, actual read rows, and append-only local-action records on separate paid tapes. Arrays and read rows have $O(N^3)$ encoded bits apart from their repeated fixed binding metadata. They may be accessed by linear scans, adding at most an $O(N^3)$ factor. Sequentially appended local records are not rescanned as an algorithmic array. A record can store the fixed instruction tag and the bounded location/counter fields in $O(b+\log N)$ bits; recording those bit operations and their finite framing has at most a further $O((b+1)N^2)$ factor. Thus the preceding $O(N^5)$ bound gives the deliberately conservative $O((b+1)N^{10})$ work and backing bound. Address/reply rows alone occupy $O(Q(\overline D+b+\log N))$ bits. Saving continuation references, all discarded candidates and both complete output copies fits the same bound. Every retained bit is backed and every copy charged; an abstract source-dependent control state is never used to hide a seed catalog or arithmetic.

This accounts for the acquisition controller's added material. Binding, actual service, transport and recording machinery still consume their real resources. One may add their actual nonnegative bill to these controller charges. In particular neither a preexisting archive nor a concrete unary global journal counter is relabelled as free or proved small by $N$. $\square$

**Theorem 5.2 (deterministic worst-case query order and exponential expansion).** Fix any legitimate multileaf entry $t$, keep its binding and accessible common data independent of future choices, and supply no history-dependent advice. A deterministic acquisition correct on all its finite completed histories has worst-case raw-call count at least $\lceil m/2\rceil$ over the $2^m$ words of length $m$. Thus for fixed $n_0$ the construction has matching $\Theta(m)$ worst-case query order as $m\longrightarrow\infty$ (or $\Theta(m+1)$ with the empty case included).

For $W=F^m$, full expanded traversal has exponential size while the earned description has length $O(n_0+m)$ and the sparse call count is $O(m+1)$ at fixed $n_0$.

Proof. Rooted Theorem 42.4 makes all $2^m$ full endpoints, and their requested words, distinct. One concrete fixed entry is $t=\langle\beta,\alpha\rangle$, attained by the root promotion and split, with $n_0=2$; the argument applies equally to every stated multileaf entry. Compress only source-independent finite local work in the ANALYSIS of a deterministic query tree. Each actual call has at most four children. For this finite family all runs terminate, so their maximum query depth $q$ is finite. A four-ary tree of maximum depth $q$ has at most $4^q$ leaves, including variable stopping depths. Correct outputs for different words require different leaves; hence $2^m\le4^q$ and $q\ge\lceil m/2\rceil$. Address length and internal computation cannot create an extra observation branch. This is the familiar decision-tree counting argument used as an intermediate tool, with no randomized or error-tolerant extension asserted. The upper bound follows from $H=d+m$ and (5.2) at fixed $n_0$.

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

At that real outer return the next completed checkpoint has source $X(\operatorname{Run}(W,t))$ and its completed word becomes $WX$. This proves (6.1) and its iteration by induction. Append/copy and complete response records are paid; the saved completion phase prevents duplicate appending. Between completed checkpoints the old packet remains typed as an old boundary. The same source value can already hold when source edits have finished but output, ACK or return is pending; at that earlier cut $W$ has not changed. The actual phase/continuation supplies this distinction, not a predicted source reply.

These source operations preserve the actual occurrence through their existing binding/certification rules; any permitted certification renewal is recorded by those rules, not inferred from equal syntax. Records use the existing same-source contracts. Native Serial Machine supplies only localStep/read/applyRho/stop; the stationary read/local prefix corresponds to that menu, but its rho-only update theorem is not invoked as an implementation of $G$. The continuation here is LAB's already supplied local split executor. Nor is that split identified with a journal adapter root graft. $\square$

**Theorem 6.2 (short cases and excluded recovery claims).** The acquisition covers $W=\varepsilon$, $m=1$ and $H=1$ without an extra supplier. It does not extend to $n_0=1$ with no first-choice channel. It supplies the current source and completed native macro history as descriptions, together with the conditional handoff of Theorem 6.1. It does not supply full earlier primitive history, all controller/CPU/wait chronology, physical inverse edits, arbitrary busy-cut recovery, arbitrary effective-program execution, four individually minimal view kernels or an infinite coherent thread.

Proof. If $W$ is empty, $H=d\le n_0-1$, the far-tail phase is empty, and the true test $K=0$ parses each actual entry row directly; its weights reach $n_0-1$ at $d=H$. The $m'=0,K=0$ branch keeps precisely this pair, while discrimination disposes of any other consistent candidates. For $m=1$ the only born level is zero; (3.2)'s first difference recovers the one letter from $K\in\{0,1\}$. For $H=1$, $d\ge1$ forces $d=1,m=0$; a right leaf of depth zero is distinguished by its actual alpha/beta root reply, and a right branch uses the same bounded depth search. No tail witness with negative exponent is submitted: $q=0$ is always handled at the row root.

At $n_0=1$ the entry is beta, and $F(\beta)=G(\beta)=\langle\beta,\alpha\rangle$. Their first request identities cannot be distinguished from any subsequent source-only literal transcript. Existing completed-history recovery gives exactly that first-bit pair for each nonempty endpoint and a separate empty endpoint. This is why $n_0>1$ is indispensable here; a genuine retained first-choice channel could condition a separate theorem.

The actual completed-history promise and same-source rights are hypotheses. The unchanged-source and incomplete-call collisions of Rooted §§42.5 and 43 demonstrate why syntax cannot establish them or recover the full controller. The packet omits pre-entry primitive shuffle and protocol/wait events. It grants no inverse source operation, Busy observation permission or universal program installation. Its finite families, bounds and induction at each supplied completed return construct no infinite physical execution or infinite coherent thread. The full RRO mutual-recovery and continuing-research obligations therefore remain open. $\square$

## 7. Source and literature correspondence

**Convention 7.1 (reused statements and the new interface).** [Rooted §§42.1–42.6](RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md#42-recovering-an-unknown-native-entry-and-its-completed-macro-history) supplies exact spine form, unknown-entry uniqueness and the paid expanded-syntax supplier; §§42.7 and 43 supply outer-return distinctions, incomplete fibres, logical coordinates and lawful continuation. This volume uses that uniqueness to distinguish candidates, without running an exponential full-syntax inverse. Its added mathematics is the earned $H$ and bounded $K$ window, polynomial bounded parsing, the exhaustive finite transcript fibre (3.3), actual distinguishing reads and their simultaneous resource account.

The existing [Native Completed History Recovery source](../../../D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery.lean) and [owning Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery.scribe.cs) state `completed_history_recovery` on actually guarded-attained entries with eventIndex $n_0>1$. Its success equivalence, injectivity, original primitive expansion and beta first-bit fibre retain their exact hypotheses. Reading those statements supplies no new compilation or Lean verification of this volume.

[Sparse Literal History Transport, Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) is the known-lag decoder used literally in Definition 3.1, including its existence guard and actual root-prefixed addresses. [Native Dynamic Acquisition Frontiers §§19–24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DYNAMIC_ACQUISITION_FRONTIERS.md#19-原子共同入口上完整新记录的准确索引区间) already separates source-blind actual calls, total submitted letters, atomic substitution index, actual return and macro/event chronology. Those atomic acquisition results are reused boundaries, not advertised here as new results.

[Native Full Source Producer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) supply the expanded once-per-node stationary traversal. [Native Serial Machine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs) supply source-free local control, raw four-valued reads, truthful register execution and the absorbing stop boundary. [Native Local Source Execution](../../../D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution.lean) and its [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution.scribe.cs) supply birth-sort attainment, exact primitive-event indices and original F/G source effects. [LAB §§9–13](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) supplies actual operands, source-preserving traversal, sealed-frontier execution, local splitting, controller phases, complete returns and resource obligations. [Native Literal Journal Adapter §§5–8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LITERAL_JOURNAL_ADAPTER.md#5-the-actual-journal-and-its-pending-complement) supplies its paid same-source record equations and capacity-safe Native correspondence. Its restricted Native correspondence is not extended to $G$ by a renaming of its grafts.

**Convention 7.2 (mature intermediate tools and contribution boundary).** Lohrey–Maneth–Reh, [*Traversing Grammar-Compressed Trees with Constant Delay*, arXiv:1511.02141v2, introduction and Proposition 3](https://arxiv.org/html/1511.02141v2), studies navigation after a grammar-compressed tree is SUPPLIED. Proposition 3 states polynomial-time equality of the values of two supplied TSLPs; it is not the constant-delay traversal proposition. Definition 4.1 needs only its elementary ground-DAG special case, whose exact identifier and witness construction is given there. Neither that paper's supplied-input preprocessing nor its register-cost assumptions acquire our unknown source or pay our submitted letters.

Engelfriet, [*Tree Automata and Tree Grammars*, arXiv:1510.02036v1, Definition 3.62](https://arxiv.org/html/1510.02036v1), defines ranked-tree homomorphisms by substitution of the recursively mapped children. Here the rank-zero images are beta and the beta/alpha branch, and the binary constructor maps to the ordered pair of its two variables. This is precisely the homomorphism behind (2.3) and candidate skeleton replacement, without an acquisition theorem attached to the definition.

Term-DAG equality, finite decision-tree counting, finite-tree parsing and integer bisection are credited intermediate methods. Relative to these methods and the cited repository results, Theorems 3.3–5.1 are a `repo-derived` source-specific acquisition interface with explicit proofs. No worldwide originality or fresh Lean claim is made. Provenance, whole-event chronology, physical recovery, minimal individual views and the infinite RRO target have exactly the unresolved scope described in §6.

## 追加锚（本行以下为增补区）


## 8. An earned packet and an occurrence cut through a compressed source

**Definition 8.1 (attachment and the descriptive parameter).** Retain Definitions 1.1–1.2 and the pre-Stop same-source handoff of Theorem 6.1. At a genuine completed checkpoint the actually earned packet is $(t,W)$, its current source is $u=\operatorname{Run}(W,t)$, and

$$
N=n_0+|W|+2,\qquad h=\operatorname{height}(u),\qquad L=\ell(u).
\tag{8.1}
$$

Only after that acquisition construct Definition 4.1's ground DAG $D$ for $u$. Its nodes denote tree VALUES; two paths to one node still denote two distinct source occurrences. Write $s$ for its number of nodes. Unused candidate DAGs are not inputs to this continuation. The bound $s=O(N)$ follows from (2.1): at most $2n_0-1$ entry-skeleton nodes, $|W|+2$ pure-level nodes and $n_0-1+|W|$ spine nodes suffice, with a constant number of extra leaves. Also $h\le n_0-1+|W|<N$. Physical source objects and acquisition's actual records remain attached, independently of this representation.

A coherent old-row cut is Rooted Definition 43.1's $F_j(u)$, $0\le j\le L$. For an active native $G$ only $j=0,1$ is allowed. All old rows are those actually acquired and sealed by LAB Definition 9.3. Neither $D$ nor a computed address replaces such a row, its target reference, navigation, guard, authority or reference comparison. The compact description is initially at the supervisor that received the packet; driver-private fields have their own owner.

**Definition 8.2 (two tables and one cut).** In topological order store for each old DAG node $v$ its old root $O_v$, the exact binary integer $l_v=\ell(\operatorname{val}(v))$, and a transformed root $T_v$. The transformed table is

$$
T_\alpha=\beta,\qquad T_\beta=\langle\beta,\alpha\rangle,
\qquad T_{\langle v,w\rangle}=\langle T_v,T_w\rangle.
\tag{8.2}
$$

The leaf-count table uses $l_\alpha=l_\beta=1$ and $l_{\langle v,w\rangle}=l_v+l_w$, including TWO summands when $v=w$. It counts unfolded occurrences, not distinct DAG nodes.

For $0\le q\le l_v$ define a mixed root $M(v,q)$. At $q=0$ use $O_v$; at $q=l_v$ use $T_v$. Otherwise $v=\langle a,b\rangle$ and

$$
M(v,q)=
\begin{cases}
\langle M(a,q),O_b\rangle,&q<l_a,\\
\langle T_a,O_b\rangle,&q=l_a,\\
\langle T_a,M(b,q-l_a)\rangle,&q>l_a.
\end{cases}
\tag{8.3}
$$

The first and last cases descend into only ONE child occurrence. Distinct calls to a shared node with different $q$ are not identified. At most one unfinished recursive descent remains, whose left siblings have been wholly transformed and whose right siblings are still old. Its direction word is an occurrence address, not a source reference. A materialization of this recursion retains only its current path of mixed branch nodes, rather than every previously produced mixed root.

**Theorem 8.3 (compact coherent partial geometry).** From the earned packet and a backed valid integer $j$, (8.2)–(8.3) construct an exact description of $F_j(u)$ without any new source query or full expansion. A description of active $G$ is obtained by restricting to $j\in\{0,1\}$. The old and transformed tables and the live mixed branches together have at most $2s+h+3$ descriptive nodes. They use $O(N\log(N+2))$ bits, including the binary progress and the cut path, before the optional count table and binding metadata. The count table and computation workspace use $O(N^2)$ additional bits. These are live descriptive bounds, not bounds on the physical source, actual OLD list, archive or total local-action records.

Proof. Topological induction gives $\operatorname{val}(T_v)=\rho(\operatorname{val}(v))$. In an old branch, all leaves of the left child precede all leaves of the right child. If $q<l_a$ only the left child has been partly edited; if $q=l_a$ it has been wholly edited; and if $q>l_a$ the remaining $q-l_a$ edits lie in the right child. Induction on height therefore proves

$$
\operatorname{val}(M(v,q))=F_q(\operatorname{val}(v)).
\tag{8.4}
$$

This uses the original prefix operation, not its inverse or a redefinition of the executor. At an old alpha its one edit is $P$; at an old beta it is $S$. Distinct old leaf addresses are prefix-incomparable, so the source effects at all earlier rows preserve the next old operand, exactly as in LAB9.4. On $\mathcal D_+$ the first leaf is beta, hence $F_1(u)=G(u)$ as a source value, without identifying the commands or protocols.

There are $s$ old nodes, at most $s+3$ transformed nodes and at most $h$ mixed branch nodes. Every new mixed node points to fixed table roots or a lower mixed node, so no cyclic description is introduced. Topological node identifiers have $O(\log(N+2))$ bits. A binary tree of height $h$ has at most $2^h$ leaves, hence $j$ and every $l_v$ have at most $h+1=O(N)$ bits. Storing all $s$ counts therefore takes $O(N^2)$ bits; a recursion stack with at most $h$ such counters fits the same bound. The geometry graph, its path, roots and $j$ use the claimed smaller bound. For $G$, the same construction can stop after its one first-leaf edit; it need not transform the other occurrences. No source-dependent table was supplied before acquisition. $\square$

**Theorem 8.4 (explicit bit work and occurrence selection).** There is a finite binary-tape computation of the tables and of any one root in Theorem 8.3 using $O(N^4)$ bit work and $O(N^2)$ workspace. Recomputing the root after each actually completed old row costs $O(N^4)$ per such row; this does not make an entire $F$ call polynomial in $N$. The old address and tag of row $j+1$, if $j<L$, can be computed within the same bound, as descriptive data only.

Proof. Put the topological tables in a sequential array of $O(N^2)$ bits. A lookup by identifier can scan the entire array, using backed binary position counters. Computing one count uses two such lookups and an addition on $O(N)$ bits. Across $O(N)$ nodes this costs $O(N^3)$ bit work, with room in $O(N^4)$ for identifier framing, copying and the transformed table. To select the next old leaf, start at the root with zero-based rank $j$; at $\langle a,b\rangle$ descend left if $j<l_a$, and otherwise descend right with rank $j-l_a$. Append the corresponding direction bit and continue until an old leaf is reached. Its rank test and address distinguish occurrences even when table nodes are shared. At most $h$ descents, each with a full array scan and $O(N)$-bit arithmetic, again cost $O(N^3)$, conservatively $O(N^4)$ including all scratch copies and clearing. The recursion for $M$ has the same bounded number of accesses. It creates at most $h$ branches, which can be written sequentially in a separate reusable region. No algorithmic lookup requires scanning an ever-growing archive. These operations are on acquired strings and derived DAGs; the computed old address cannot be cast into a physical reference. $\square$

## 9. Material child edges during the actual source templates

**Definition 9.1 (material descriptions).** Let $E$ denote a terminal material vertex, $U(x)$ a vertex with only a left child $x$, and $V(x,y)$ a vertex with ordered left and right children. These describe rooted child-edge shapes, with repeated occurrences unfolded. AA Definition 17.3's materialization is

$$
C(\alpha)=E,\qquad C(\beta)=U(E),\qquad
C(\langle a,b\rangle)=V(C(a),C(b)).
\tag{9.1}
$$

Its support is the set of reachable $L/R$ words, including the empty word, and its boundary is the maximal-address antichain. Each present nonroot address $pd$ specifies the edge $p\longrightarrow pd$. Parent fields, source-header fields, headers, tape links and reserved but unattached objects are excluded. A raw material description may contain $U(U(E))$ and need not be $C(y)$ for any logical tree $y$.

**Theorem 9.2 (exact support at source-write cuts).** Fix the original ordered attachment template of AA Definition 20.2, with its field layout as counted in AA Proposition 22.1. Suppose the next actually acquired old operand is at $p$, after $j$ earlier old rows, and put $S_j=\operatorname{supp}(C(F_j(u)))$. The following are exactly the changes to rooted material support at that operand:

| Actual source-template cut | Material subtree at $p$ | Rooted support |
| --- | --- | --- |
| $P$, before its attachment | $E$ | $S_j$ |
| $P$, after attaching the new terminal left marker | $U(E)$ | $S_j\cup\{pL\}$ |
| $S$, before either new attachment | $U(E)$ | $S_j$ |
| $S$, after extending the reused marker, before attaching the right alpha | $U(U(E))$ | $S_j\cup\{pLL\}$ |
| $S$, after attaching the right alpha | $V(U(E),E)$ | $S_j\cup\{pLL,pR\}$ |

At every other field-operation cut between these attachments, the rooted child-edge support is unchanged. Each displayed support has an exact material DAG with $O(N)$ descriptive nodes and $O(N\log(N+2))$ bits. Its boundary is its maximal-address antichain and determines that support by prefix closure; an expanded enumeration is not included in the compact bound.

Proof. In $P$, the old logical alpha is a terminal vertex. AA20.2 initializes a fresh terminal marker and attaches it at the old root's left slot; this adds exactly $pL$. In $S$, the old beta already has its actual terminal marker at $pL$. The template reuses that vertex as the new left beta root, first attaching a fresh terminal at its left slot. Exactly $pLL$ becomes reachable. Attaching the new right alpha at the old root then adds exactly $pR$. Its final source shape is $C(\langle\beta,\alpha\rangle)$. All these objects are distinct in the actual source; the DAG's reuse of $E$ describes their equal shapes only.

Initializations of unattached objects cannot add a root-reachable edge. Parent-field initialization, binding the branch tape header, append-cell linking, advancing header tails, arithmetic, output and return affect excluded fields or no source fields. AA22.1 specifies precisely these source assignments, with no further child-edge modification. Thus the table covers the support at every cut of this specified source template, including cuts within initialization and between source completion and maintenance completion. It is not a theorem for a differently ordered source template, interrupts or a foreign writer.

Materialize the tables of §8 topologically; each logical node contributes a bounded number of material nodes. To replace the subtree at the ONE occurrence $p$, retain the siblings on its occurrence path and rebuild that path around the appropriate constant-size material subtree in the table. Since $|p|\le h$, this adds $O(h)$ nodes, regardless of other paths to the same descriptive node. The union formulas give the support and every child edge of that unfolded material DAG exactly. A finite rooted child tree is prefix closed in addresses, so support and terminal antichain recover one another. During the split's middle cut its unary child is nonterminal; arity parsing it as a logical beta would discard a real edge and is invalid. This is a raw material view, not a logical literal reply available during editing. $\square$

## 10. Paid maintenance with the original owners and original milestones

**Definition 10.1 (owner-local attachment).** Assume the original LAB supervisor and driver retain their original local memories, connections, guards and program counters, and permit finite local bookkeeping in their own arenas. They have the same no-crash, exclusive-rights and finite-supply hypotheses as AA20.1 and LAB11. This is an attachment of paid local work to the existing execution, not a replacement selector or a new request. A parent has no added right to inspect the driver's private arena. Original source operations and their order remain those of the sealed OLD list or the one acquired $G$ operand.

At the supervisor store the earned $(t,W)$, a root of $D$, the tables of §8, the active command identity, a binary base ordinal $j$, a pending-update discriminator and two backed descriptor banks with their construction cursors. The old $(t,W)$ remains a completed-checkpoint packet during Busy. The supervisor also retains its original actually acquired frontier rows/cursor or $G$ locator, received inner bits, full replies and saved continuation. Those original fields are not reconstructed from $D$.

At the driver retain its original acquired request, actual operand/reference, pending kind/address, source-template location, reserved objects, ancestral-maintenance and pending-append cursors, arithmetic banks and output/return fields. Added finite local notes distinguish the source attachments of Theorem 9.2 and the driver-local bookkeeping before/after them. Each note belongs to its actual received original frame; a previous call's archived note is not a patch for a new unaccepted frame. The last accepted call's kind/address and attachment note remain backed past original driver cleanup, until at least the next original call; its immutable record remains archived. This retention has its own bill and needs no new acknowledgement from the supervisor. Their values are written from that owner's ACTUAL actions, not inferred from a source query or read remotely. The existing addressed frame already supplies its $p$ and kind; no packet or private-state payload is smuggled into that frame. At a return, the supervisor learns only the original full reply, End and return through the existing bound connection. Its later ordinal update uses that acquired event.

Each owner gives its added work its own actual records: acquired operands used in a local computation, its routine/cursor, completed descriptor writes, local source-attachment notes, validation of the original returned kind/address, and once-only posting of inner and outer completion. Retained records have actual allocated backing. Their writing and copying are charged separately from the live descriptor; they are not asserted to equal the old local microhistory. Original old records and recipients remain intact.

**Definition 10.2 (the relation at a cut).** The maintenance invariant is a relation between these actually stored owner components, the original joint process and its source. A mathematical decoder of that relation uses the supervisor's base root/ordinal and, during an outstanding original inner call, the DRIVER'S OWN actual local attachment phase. It applies the corresponding patch of Theorem 9.2 at the outstanding operand. Original driver phase and local note disambiguate the interval after a source write but before a later bookkeeping mirror is posted. Before dispatch there is no driver patch. After a returned row has been posted, there is no pending patch for that row.

A bank under construction has no current-root status. Before a source-changing attachment, prepare its old and prospective constant-size material patches locally, retaining the original actual phase. Before posting a new ordinal or completed word, construct the new supervisor bank while retaining the old bank and a pending-completion flag. Every bit-write cut therefore has an old complete bank, actual progress in scratch and a stored original or local control location selecting its interpretation. A finite selector write publishes the completed bank; later clearing is charged. No multiword atomic arithmetic or free instantaneous copying is assumed.

This relation is not a single-observer collected state. In particular the supervisor alone need not know whether a driver-private source attachment has occurred. Gathering private notes into a requester, exporting a Busy read or admitting a query before an original return requires an additional, presently unsupplied communication/access contract. The material decoder is a mathematical relation on one joint execution, not a new physical operand or grant.

**Theorem 10.3 (maintenance at every update and return cut).** Under Definition 10.1, the compact relation can be maintained throughout each supplied finite native $F/G$ call. At a coherent cut it gives §8's exact logical source; during a source template it gives §9's exact rooted material child edges. Original logical legality, all-event ancestral records, arithmetic hooks, complete original replies, End/ACK, inner and outer return, old archives and local work remain accounted for. Posting the active letter into the completed packet happens exactly once at the genuine outer return.

Proof. At admission the previous source is $u$ and the base ordinal is zero. Receive/parser, stationary frontier acquisition and sealing have no source change. Before sealing there need not be a next-row operand; only the old root is asserted. Partial acquired frontier lists, path stacks and their growing backing remain original supervisor material. A complete original sealed list earns its first operand. $G$ instead earns its actual current leftmost beta by the original descent. The descriptive leaf selector may check correspondence with these acquired addresses/tags, but cannot dispatch an operand on their behalf.

For a row, original navigation reobtains the target from the same root, compares its reference and checks its guard. Before acceptance and during Reserve or arithmetic preparation, the source is unchanged. At acceptance LAB11.1 retains its actual kind/target and old arithmetic banks and computes successors from old operands. The new source-phase note is recorded locally; attaching one or two source edges gives exactly Theorem 9.2's successive patches. A cut before a note mirror catches up is interpreted by the original local control position, with the pending transaction still backed. The note alone is never used to pretend a write has happened. Source-complete but Maintain-pending cuts have the FULL new material source, even though ancestor tapes, arithmetic or local notes can still be incomplete.

Maintain uses the original actual parent-chain cursor, child-reference comparisons, headers and pending cell links. Header head/next can change before tail; those cuts retain the actual pending append and never count it twice. The old/new arithmetic banks and their write cursor remain meaningful while individual fields are overwritten; no assertion identifies a half-written residue pair with the final vector. All proper-ancestor appends, scalar and pair commits and pending-state discharge occur before original BuildAnswer. The descriptor changes neither their values nor this publication order. It has no authority to release a reply while those obligations remain.

BuildAnswer seals the original Growth kind/address word. Every Print prefix, End, supplied ACK, driver's Return and scratch cleanup is retained. Source geometry remains the same throughout them. The supervisor receives and backs every bit and validates the actual returned kind/address and its saved continuation. Before a complete real inner return it has no new completed-row milestone. After that return, its raw frontier cursor may still point to the returned row. Keep that row/pending flag while constructing and posting the bank for $j+1$; the pending patch continues to describe its already changed source. On posting, replace it by $M(\operatorname{root},j+1)$ and clear the patch exactly once. List advancement then follows the actual next link. If advancement precedes a later bookkeeping cleanup, the pending discriminator still retains the returned-row milestone; it cannot be mistaken for a new source action. This also covers the last row returning before exhaustion is posted, the cursor is cleared or consumed backing is released. No scan of an already released completed prefix is needed.

Induction on original inner returns proves the coherent source law. Each earlier old row leaves every later old address, tag and reference intact by LAB9.4, so every remaining original guard is still legitimate. At exhaustion the source is $\rho u$ for $F$ or $G(u)$ for $G$. Clearing the list is not outer completion. Keep the outer sealed response, emission cursor, End, pending ACK, return-to-root and cleanup. Until the actual outer return the old packet still says $W$. At that event retain a pending-outer-return note while constructing the packet $WX$ and its new compact checkpoint DAG from (2.1), then post it once; a cut before posting has a completed return with an explicitly unposted packet, rather than a false Busy packet or a duplicate letter. Rebuilding from (2.1) prevents repeated calls from accumulating old transformed tables as live geometry. Archives of their actual computations remain separate paid records.

Original source arithmetic is updated once per actual accepted $P/S$, not by a macro-end overwrite; reads, refusals, prediction and acknowledgements add no source event. Source geometry cannot replace the ancestral tapes or full returned payloads. All added work is finite local work with actual backing and its own records. Erasing only the added bookkeeping actions from the augmented execution leaves the original ordered LAB actions, inputs and full replies. The original local-event trace embeds in this augmented trace; the two complete microhistories are generally different. This establishes maintenance without altering the original menus, sealed frontier, rights or accepted-event hooks. $\square$

**Theorem 10.4 (separate live, per-row and full-call bills).** For a call with parameter $N$ in (8.1), let $k$ be its number of actually completed old rows. Apart from the inherited LAB bill and actual metadata/record costs, added descriptor computation has the bounds

$$
\begin{aligned}
\text{live geometry nodes}&=O(N),\\
\text{live geometry bits}&=O(N\log(N+2)),\\
\text{count/scratch bits}&=O(N^2),\\
\text{descriptor bit work through }k\text{ rows}&=O((k+1)N^4),\\
\text{one full }F\text{ descriptor bit work}&=O((L+1)N^4),\\
\text{one full }G\text{ descriptor bit work}&=O(N^4).
\end{aligned}
\tag{10.1}
$$

These include building the entry tables, constant-size patches along the acquired occurrence path, both descriptor banks, rebuilding at outer return and clearing/reuse. Counts, references, bindings, original protocol storage and archive lengths are distinct quantities.

More precisely let $T$ be the number of non-record-writer bit operations of the added descriptive routines, including actual hook/note work, let $B$ be the total bit length of actual variable metadata copied into their new records, and retain the fixed interface size $b$ of Definition 1.2. With sequentially appended records of operation tags, bounded locations/cursors, acquired operands and results, the extra record writing/backing admits the conservative bound

$$
O\bigl(B+(T+1)(b+\log(N+T+2))\bigr).
\tag{10.2}
$$

This is a bit-tape content-work/backing bound. Actual allocation, grants and reference-width-dependent links have their additional prices under Definition 1.2. The recording routines' own sequential reads/writes are charged by this bound; their deterministic serialization is not silently identified with the earlier local trace. If an installation imposes a richer recording contract, add its actual bill. In particular (10.1) is not a bound on $T$ for arbitrarily many original protocol actions or on all physical time.

Proof. Apply Theorem 8.4 at entry, once per completed row and at outer posting. Preparing a bounded number of raw patches or banks entails at most a bounded number of its occurrence-path computations. Reusable live buffers give the first three bounds. A fixed local routine can store a finite instruction tag, its finite-table location and cursor in $O(b+\log(N+T+2))$ bits per recorded bit operation, with copied variable payloads charged to $B$. Sequential append avoids rescanning earlier records. The resulting length bounds its material backing and the sequential writing/copying work, proving (10.2). Actual phase hooks beyond these routines contribute their actual bit operations to $T$ and their actual payload widths to $B$; they do not disappear in an $O(N)$ geometry count.

For a FULL $F$, the original sealed list has exactly $L$ rows, so even just their existence, actual inner calls and return milestones cost $\Omega(L)$. If the entry has counts $(a,b')$, its exact source additions are $a+2b'$ vertices and $b'$ headers. With $J_F=\sum_{p\in\operatorname{Leaves}(u)}|p|$, it adds $J_F$ side cells and has original inner request/reply lengths $2J_F+4L$ and $2J_F+5L$, with $L$ inner End/ACK pairs. These are LAB13.2's inherited prices, not new compression savings. The actually acquired OLD list has $L$ target rows and $J_F$ address letters, with actual reference/next-link widths additional. For $G$ the corresponding source additions are two vertices, one header and $|\lambda(u)|$ side cells, and one complete original inner call. Both calls retain outer traffic, Return and cleanup, old source/backing, all earlier ancestral records, arithmetic operands, reserved unattached resources and acquisition's records. Full source size, list size, total tape size and the growing new local archive can thus be exponential in $N$ or depend on earlier unrelated traffic. No fixed physical arena or polynomial whole-installation time follows. $\square$

## 11. Exact-current-source capacity at a fixed authentic checkpoint

**Definition 11.1 (the forward source task and exposed information).** Fix ONE authentic acquired checkpoint packet $(t,W)$ and its actual entry $u$, call identity $F$, binding and supplied execution contract. Choose one specified reachable coherent cut $c_j$ for each $j$ in an explicitly chosen nonempty set $J\subseteq\{0,\ldots,L\}$. For a more general set of concrete cuts, use the number of DISTINCT progress values in each exposed-information fibre; multiple phases with the same current source do not increase source capacity. This is the forward task of distinguishing the EXACT CURRENT LOGICAL SOURCE $F_j(u)$; it is different from Rooted §43.7's recovery of entry/history when the current source $y$ is fixed.

Let $Z(j)$ be ALL varying side information exposed to the proposed decoder at these selected cuts. This includes any readable actual phase, consumed/remaining-row count, address, row/list contents, full reply history, arithmetic residue, private note if lawfully collected, elapsed-output information if exposed, and any identity or archive whose variation is usable. An uncollected private driver state is not part of the decoder's input. If a checkpoint is reached with several possible retained chronologies, fix that actual checkpoint/chronology here, or include its varying exposed part in $Z$. For each realizable $z$ put

$$
J_z=\{j\in J:Z(j)=z\},\qquad q_z=|J_z|.
\tag{11.1}
$$

Widths below concern fixed-width binary supplement content conditional on this input. They do not count free side information twice or treat varying accessible fields as fixed constants.

**Theorem 11.2 (sharp conditional source capacity and a consumer).** On each nonempty fibre $J_z$, an exact-current-source supplement must have at least $q_z$ values, and $q_z$ values suffice. Its sharp fixed-width conditional capacity is $\lceil\log_2 q_z\rceil$ bits. A common alphabet for all $z$ must have at least $\max_z q_z$ values, and that many suffice if the finite fibres and their ranking are supplied or computable from the specified side-information map. If $Z$ is not fixed, the joint exposed pair $(Z,\text{supplement})$ must distinguish all $|J|$ sources. This is not an unconditional extra-memory requirement or a full-controller minimality theorem.

A concrete consumer, given the acquired checkpoint and a backed exact $j$, constructs §8's current-source DAG and evaluates any supplied finite logical address on that DESCRIPTION, returning alpha, beta, branch or absent. It performs no Busy source read. This consumer genuinely needs to distinguish every source in its conditional fibre if it must answer all such descriptive addresses exactly.

Proof. Every old-row primitive increases $n=a+2b-1$ by exactly one, so

$$
n(F_j(u))=n(u)+j.
\tag{11.2}
$$

Consequently all current trees in $J$ are distinct. If two indices in $J_z$ shared a supplement, an exact decoder would have equal inputs and unequal required sources. Conversely the rank of $j$ in the finite ordered set $J_z$ identifies it, and (8.3) supplies its source. This is finite-fibre injection and ranking, used as an intermediate coding fact. A rank is not thereby acquired from $z$ alone; a supplied effective map or earned progress is still necessary. For several $z$, the same ranks can be reused across fibres, proving the common-alphabet statement and the joint-information qualification.

The address consumer follows the chosen DAG root along its input, testing constructors; descent beyond a leaf returns absent. It reads only its backed description. With array scans its bit work is $O(N^4+(|p|+1)N^2)$, including construction and reading the entire submitted finite word; its scratch is $O(N^2+|p|)$. Distinct finite ordered labelled trees have a first differing constructor at some finite address, so one common exact all-address answer function cannot serve two unequal trees. Alternatively exact current $n$ is already a separating numerical consumer by (11.2). Neither consumer manufactures source rights, old physical operands, driver-private phases or chronology. $\square$

**Theorem 11.3 (attained exponential family and the size of progress).** Put $C=\langle\beta,\alpha\rangle$ and, for $r\ge0$, take the actually completed checkpoint

$$
t=C,\qquad W=F^r,\qquad u_r=\rho^r C=P_{r+2}.
\tag{11.3}
$$

It is attained from alpha by the root promotion and split and then the original completed $F$ calls; the packet is eligible for §§1–6's actual acquisition with $n_0=2$. Write $L_r=\ell(u_r)$. Then $L_0=2$, $L_1=3$, $L_{r+2}=L_{r+1}+L_r$, and

$$
2^{\lfloor r/2\rfloor}\le L_r\le 2^{r+1}.
\tag{11.4}
$$

Conditional on this fixed checkpoint and no distinguishing side information, the coherent prefix set $J=\{0,\ldots,L_r\}$ requires and attains exactly $\lceil\log_2(L_r+1)\rceil$ supplement bits. For the common interior between-row phase use $J=\{1,\ldots,L_r-1\}$; its sharp width is $\lceil\log_2(L_r-1)\rceil$, which grows as $\Theta(r+1)$ for $r\ge1$. At that phase, exposing $j$, an equivalent count or all identifying remaining-list information can instead make every fibre singleton. No contradictory lower bound survives that exposure.

Proof. Equation (2.3) gives both $u_r=P_{r+2}$ and the leaf recurrence. Its two-step doubling inequality gives the lower bound; each $F$ at most doubles leaves, giving the upper. All prefixes are legitimate prefixes of LAB's same sealed OLD execution, with finite supply for each chosen finite run. Each interior prefix can pause after the actual row advancement and before dispatch of its next row, so their original control location can be the same; its varying data are precisely what $Z$ must count. For attainment, apply Theorem 11.2 and encode the zero-based rank of the earned progress $j$ at the stated fixed binary width: use $j$ for $J=\{0,\ldots,L_r\}$ and $j-1$ for $J=\{1,\ldots,L_r-1\}$. For $r\ge1$, the recurrence also gives $L_r-1\ge L_{r-1}$, so the logarithmic widths grow linearly in $r+1$. These are conditional alphabets over reachable cuts, not simultaneous physical copies. Since the earned packet has length $O(r+1)$, the example explains why a binary progress value can need linearly many packet-size bits while the current expanded source and a full next $F$ have exponentially many occurrences. It also shows why an $O(N)$ number of descriptive nodes cannot be charged as $O(N)$ pointer bits or as a constant-size progress register. $\square$

## 12. Occurrences, continuation phases and the history retained by other menus

**Proposition 12.1 (sharing does not merge source occurrences).** There is an attained checkpoint whose compact DAG has two references to one beta node but whose two old beta rows require different actual source actions. A single in-place edit of that shared descriptive node gives the wrong partial source.

Proof. From alpha execute $P_\varepsilon S_\varepsilon P_R$ to obtain $v=\langle\beta,\beta\rangle$. It can be an earned entry with $n_0=3$ and empty completed word. Its DAG can share the beta VALUE. Its old leaves are the distinct actual references at $L$ and $R$. After its first old row,

$$
F_1(v)=\langle C,\beta\rangle,
\qquad F_2(v)=\langle C,C\rangle.
\tag{12.1}
$$

Editing the shared beta description everywhere would produce the second source at the first cut. Equation (8.3) instead rebuilds the root with transformed left occurrence and old right occurrence. The physical source has no sharing by AA17.1; its equal beta shapes, markers and eventual branches remain distinct actual objects. $\square$

**Proposition 12.2 (geometry does not determine phase or retained chronology).** Reachable executions settle three separate failures: equal source can have different next protocol instructions; equal source can have different remaining old-source schedules; and equal source can have different retained original generation chronology and later recall. The compact maintenance relation preserves these distinctions without claiming geometry recovers their private data.

Proof. Before the first edit an admitted $F$ and its preceding idle checkpoint share $u$. After the last source attachment the source can already be $\rho u$ while Maintain, arithmetic, Growth output, inner ACK/Return, list exhaustion or outer output/ACK/Return is still pending. These are reachable cuts of AA20.2 and LAB11, and Theorem 9.2 also gives the raw intermediate split cut. The completed word changes only on genuine outer return. Thus equal source is not a decoder for continuation phase. Even at the common interior phase, Rooted Proposition 43.6's fixed-$C$ $FG/GF$ witness has the same current source and different next marks ($R$ versus $LR$). Its full calculation and Rooted Theorem 43.7's growing family are reused; they are not a new completed-history inverse or a claim that their private tapes are equal.

For retained chronology, after the common prefix $P_\varepsilon S_\varepsilon$, the independent events $S_L$ and $P_R$ may occur in either order. Both original guarded words end at $\langle C,\beta\rangle$, but their indexed generation recall differs at the first swapped index. AA17.2's linear-extension theorem proves the legality, and AA19.2's actual full routing tapes retain their different serial orders. Each final tree is also a permissible entry with $n_0=4$ and empty completed word; the same compact entry packet cannot name which pre-entry chronology occurred. Finally inserting a completed original Tag request changes control traffic and records while preserving source and generation word, as AA21's witness already shows. A geometry descriptor, macro word and even successful-event word therefore have different kernels. Their old archives, full replies and actual control records are retained by §10 rather than recovered from geometry. $\square$

**Definition 12.3 (the parameter when other legal calls intervene).** The compact bound in §§8–11 is for a segment whose source-changing outer calls since acquisition are native $F/G$. The installation keeps ALL original legal legacy, scalar and pair menus, including queries, refusals, prediction, FetchGrowth and Next. To describe a finite serialized mixture, retain an explicit extended checkpoint description: the acquired entry, completed native macro letters, and every actual newly executed addressed primitive event of each other source-changing call, in its actual order, together with its enclosing-call/return delimiters. Do not replace an in-range Next event by its recalled old event. This description includes the already earned $W$ and all later actual instructions. At a non-native edit, retain the native-only packet as a historical checkpoint and use the extended description for the current source; the $F/G$ subsequence no longer denotes that source. Keep full original requests, replies and records separately, including zero-edit calls.

Let $A$ be the number of retained source-changing macro/primitive instructions in this extended description, counting one for a native macro letter and one for each primitive event outside those native macros, and let $P$ be the sum of the lengths of the explicit primitive addresses. Put

$$
\widehat N=(n_0+2+A+P)^2.
\tag{12.2}
$$

Call delimiters and any other retained event payloads have their actual additional encoded sizes; in particular arbitrarily many zero-edit calls cannot be bounded by $\widehat N$. The complete retained process parameter includes those sizes as well. Only the geometry-size claim below uses (12.2).

**Theorem 12.4 (finite mixtures with a growing parameter).** For the mixture of Definition 12.3, checkpoint geometry and a subsequent coherent or source-template partial native $F/G$ admit $O(\widehat N)$ live descriptive nodes, $O(\widehat N\log(\widehat N+2))$ geometry bits, $O(\widehat N^2)$ count/scratch bits and conservative $O(\widehat N^4)$ descriptor work per selected actual row. Additional mixed-call records, native expansion costs and every zero-edit call retain their actual bills. No bound in the native $F/G$ subsequence length alone is asserted for arbitrary mixtures.

Proof. Start from the literal entry skeleton and evaluate the retained instructions in order. For a full native $F$, form table (8.2), then keep only its reachable transformed DAG as the next checkpoint geometry. It has at most the old number of branch nodes plus the two leaves and the beta-image branch, hence at most $s+3$ nodes if the old DAG had $s$; the whole old table need not stay LIVE after that real return. A native $G$ copies only its current leftmost occurrence path, adding at most $h+3$ nodes. A primitive outside those macros at its actual address $p$ adds at most $|p|+3$ nodes by the same occurrence-path construction. Old unused descriptive buffers may be cleared/reused, while their actual computation records are archived separately. None of this deletes physical source vertices or old source records.

Height increases by at most one per retained primitive or native macro, so it is at most $n_0+A$. Summing the displayed node increments gives at most

$$
O\bigl(n_0+A(n_0+A+3)+P\bigr)=O(\widehat N)
\tag{12.3}
$$

live nodes. The original returned kind/address and accepted-event record supply each non-native instruction; its guard is still checked physically. Thus Theorems 8.3–9.2 and their sequential-array proof apply with the larger bound $\widehat N$ on DAG size and height. Reconstructing the checkpoint from all retained instructions has, for example, $O((A+1)\widehat N^4)$ descriptive work; it is additional preprocessing, not hidden in a per-row bound. For a subsequent pure native block one can again use (2.1) to rebuild a compact checkpoint, but no such optimization is needed for (12.3).

A scalar call's actual $P/S$ expansion is retained if it is outside a native macro; an in-range Next retains its newly executed kind/address AFTER its actual recall and current left descent. Source arithmetic, tapes and replies pass the same LAB11 hook for all of them. A query, refused call, prediction or out-of-range Next preserves geometry but adds its real traffic, continuation and record material. Original serialization admits these calls only at the original outer returned cuts, never inside a sealed active native call. Extending bookkeeping by their actual returned events therefore preserves the original legal menu and all histories without treating a native subsequence as the whole execution. $\square$

## 13. Source correspondence and the remaining relational boundary

**Definition 13.1 (mathematical attribution and scope).** The constructions of §§8–12 are `repo-derived` conditional mathematics on the actually earned packet and the original LAB execution. Their source-specific content is the one-path compact mixed-prefix representation, its raw material source-template refinement, the paid distributed maintenance relation and the forward exact-current-source capacity at a fixed checkpoint. The supplied finite-DAG method and finite-fibre counting are intermediate tools, not new general compression or coding theorems.

Engelfriet's [Definition 3.62](https://arxiv.org/html/1510.02036v1) supplies ranked-tree homomorphism by recursively substituted children. Equation (8.2) is its elementary ground-DAG evaluation for this particular $\rho$. Lohrey–Maneth–Reh, [introduction, Proposition 3 and §5](https://arxiv.org/html/1511.02141v2), distinguishes subtree-sharing DAGs from the more general supplied TSLP and states polynomial supplied-TSLP equality. Its computational model charges bounded-width word registers, with widths specified separately for navigation and equality. Here no constant-register, constant-delay, supplied-unknown-grammar or acquisition theorem is transferred. The occurrence-path recursion and the sequential bit-tape bill are proved in §§8–9 themselves; no uninspected zipper theorem is required.

Rooted §§42–43 supplies the completed inverse, native prefix/image distinctions, progress/entry/next-mark conversions, actual post-return cursor distinction and conditional CURRENT-SOURCE-fixed history fibres. Theorem 11.2 concerns the other direction with CHECKPOINT fixed and current source varying; it does not relabel that inverse as new. LAB9.3–9.4 supplies the authentic OLD list, its prefix-incomparable operands, original guarded effects and the one beta split for $G$. LAB10–11 supplies the actual full inner traffic, private continuations, old/new arithmetic banks, every-event hook and outer lock. LAB13 and AA22.1 supply the original located resource accounts. AA17.3 and AA20.2 supply exactly the rooted material projection and ordered attachment phases used in §9, including the temporarily non-native unary chain. Their auxiliary fields and reserved objects remain outside source support but inside physical backing.

The existing NativeLocalSourceExecution and NativeCompletedHistoryRecovery declarations mentioned in §7 remain suppliers with their stated scopes. The Native Literal Journal Adapter has a different installation/menu; its journal equations are not used to identify LAB's augmented local trace or private drivers. The finite DAG supplies neither pointer identity nor authority. Owner-local maintenance supplies no already collected external Busy state. Source support, terminal boundary and descriptive current logical geometry are mutually computable where stated; exact phase, all-event chronology and callable physical memory require their retained owner components and lawful access. No new Lean certification, worldwide originality, arbitrary observer access, physical inverse, reset, interrupt, new session, universal executor or infinite coherent thread is asserted. These remain boundaries on continuing the relational recovery programme.

## 追加锚（本行以下为增补区）

## 14. Literal ancestral words before their last append has finished

**Definition 14.1 (the source-complete single-event domain).** In §§14–18, $t$ denotes the CURRENT logical source, rather than the acquired entry of Definition 1.1. Retain one actual AA20.1 installation, its known-alpha origin, actual root/source binding, current exclusive source and auxiliary rights, original literal ancestral tapes, finite backing and local acknowledgement. A cut $c$ in the domain $\mathcal K$ belongs to the following original execution interval.

Before the selected event, the actual successful generation word is $w^-$, and every original tape equals its AA19.1 projection of $w^-$. The preceding accepted event has finished its maintenance and arithmetic hook; there is exactly ONE accepted but unfinished new event $e=(k,p)$, with its actual acquired kind, address and reference. It is an original enabled $P_p$ or $S_p$, possibly inside an original macro or Next. Reserve has supplied the required finite material. The WHOLE source template has finished, including parent fields, initialized auxiliary slots and, for a split, the initialized and bound empty header. Thus the source is the actual attained logical term after $e$, not the middle unary-chain cut of Theorem 9.2. The cut lies at entry to, or during, this event's original bottom-up Maintain interval, including the link-before-tail subphases. For a root edit include the degenerate zero-ancestor interval. Arithmetic, reply and return may still be owed. No competing writer, crash, interrupt, revocation, reset, new session, graft or inverse source action is admitted.

Write $w^+=w^-e$ for the successful-event word through this accepted source edit. It is not a claim that the event's call, or its enclosing macro, has returned. The original pending fields, banks, cursors, backing and private continuations exist, but are NOT supplied as a summary to the recovery map below. The literal append order is exactly AA20.2 and AA22.1: initialize a fresh cell's side and null next, link it from the previous tail or empty head, and only then advance the header tail. A pending append is completed before ascending to the next proper logical ancestor. All hypotheses concern one actual source and its records, not separately compatible descriptions.

**Definition 14.2 (head words and count deficits).** At each current logical branch address $v\in I(t)$, let $U_v(c)$ be the side word obtained by starting at that branch's actual bound header head and following actual next links to null. A null head denotes the empty word. This definition ignores the header TAIL and excludes reserved or initialized cells not yet linked from head. It is a mathematical projection of owned record fields; it is not a Busy query. New headers are included even when their words are empty.

Use the birth-typed counts of AA19.1, with the left child born beta and the right child born alpha:

$$
\begin{aligned}
x_v(t)&=e_\beta(t_{vL}),& y_v(t)&=e_\alpha(t_{vR}),\\
e_b(u)&=a(u)+2b(u)-1-\mathbf1_{\{b=\beta\}},\\
\delta_v^L(c)&=x_v(t)-|U_v(c)|_L,&
\delta_v^R(c)&=y_v(t)-|U_v(c)|_R.
\end{aligned}
\tag{14.1}
$$

Here $a(u),b(u)$ count alpha and beta leaves; the subscript $b$ in $e_b$ is a birth type. Differences in (14.1) are integers, not truncated natural subtraction. They compare the SAME current child occurrence with its actual attached record. A shared descriptive DAG node never identifies two headers at different source occurrences. The root's historical birth is alpha even when it belongs to syntax sort $B$; only its CHILDREN use the displayed beta/alpha birth types.

Define a word operation on the numerical domain $\delta^L,\delta^R\ge0$, $\delta^L+\delta^R\le1$ by

$$
\operatorname{close}_t(v,U)=
\begin{cases}
U,&(x_v-|U|_L,y_v-|U|_R)=(0,0),\\
UL,&(x_v-|U|_L,y_v-|U|_R)=(1,0),\\
UR,&(x_v-|U|_L,y_v-|U|_R)=(0,1).
\end{cases}
\tag{14.2}
$$

On other numerical inputs it is undefined. This numerical domain is NOT asserted to recognize actual reachable cuts. In particular it contains families whose deficits lie in unrelated branches, which cannot come from one pending original event.

## 15. Recovering the completed record without a phase capsule

**Theorem 15.1 (the unfinished-literal-memory bridge).** For every $c\in\mathcal K$, every head word is finite and well defined, every deficit pair in (14.1) is one of $(0,0),(1,0),(0,1)$, and

$$
\widehat W_v(c):=\operatorname{close}_t(v,U_v(c))=W_v(w^+)
\qquad(v\in I(t)).
\tag{15.1}
$$

Consequently current source plus current head words determine exactly the complete original successful-event word $w^+$, every indexed generation answer through that event, and the source/record state that this event's genuine completion will restore. Neither the accepted address nor a retained phase capsule is an input. The same statement holds with current source support replaced by its terminal boundary, at these source-complete cuts. It is a statement about the eventual RECORD, without discharging unfinished physical writes or returns.

More precisely, if $p$ has depth $d>0$, enumerate its proper ancestors from the root as $v_0,\ldots,v_{d-1}$. The branches with nonzero deficit form an initial segment of this list. At each such $v_i$ the unique missing symbol is the next direction of $p$ after $v_i$. There is no deficit at any other branch. A newly split $p$ has an empty head word, $x_p=y_p=0$, and no missing symbol of its own.

Proof. The correct pre-event invariant supplies the full projections of $w^-$. The source operation changes no logical branch outside the operand's ancestor chain, and produces one new branch only when the operand is split. For an old proper ancestor $v$ of $p$, the event belongs to exactly one of its child subtrees. Both $P$ and $S$ increase that child's birth-typed event count by one. Thus its required final multiplicities differ from the old tape's multiplicities by precisely ONE in the actual traversed side. The other child count is unchanged. At every old branch which is not a proper ancestor of $p$, both strict-descendant event counts and the required word are unchanged. A split at $p$ is a root event of that subtree, not an event strictly below $p$; its new beta/alpha children have zero events since their respective births. Its freshly installed empty header is therefore already correct.

Maintain visits proper ancestors from deepest to shallowest. At a visited ancestor, before the linking assignment the new cell is unreachable from head and the head word is still $W_v(w^-)$. Its payload and null next are initialized before linking, so the linking assignment extends the finite head chain by exactly the one actual side and no other symbol. From that assignment onwards the head word is $W_v(w^+)$. Tail advancement changes no head-reachable word. The original pending subphase prevents another append or ascent from treating the old tail as a finished append. No other writer can alter the chain. Induction over these original field assignments proves that every relevant word is either its full old projection or that projection with exactly this final symbol appended. It also proves finiteness, the deficit alternatives and the rootward initial-segment statement, including cuts before the first link and after the last link but before its tail update.

Formula (14.2) supplies precisely the missing final symbol in the first case, and changes nothing in the second. This proves (15.1). Apply AA Theorem 19.2's EXISTING inverse to the completed family: its forced local root prefixes and the now-complete child shuffles recover exactly $w^+$. This does not reprove that inverse. In particular, when needed, decoding its last index $n(t)=a(t)+2b(t)-1$ also recovers the accepted $(k,p)$; that identity was not an input to (14.2). Replaying the preceding finite word is a mathematical description of the predecessor, not a physical inverse operation.

At a source-complete cut the child-edge support is $C(t)$ of (9.1). Its terminal antichain recovers it by prefix closure, and AA17.3 parses it as the same $t$, including the material beta markers. Attaching the same head-word observations at their logical branch addresses therefore gives exactly the same calculation from either geometric view. All routes refer to this actual source and these actual records. $\square$

**Theorem 15.2 (only mixed child orders add eventual-record information).** Put

$$
\mathcal A(t)=\{v\in I(t):x_v(t)>0\ \text{and}\ y_v(t)>0\}.
\tag{15.2}
$$

On $\mathcal K$, the current source together with ONLY the original head words $U_v(c)$ at $v\in\mathcal A(t)$ still determines every completed word in (15.1). At other branches the completed word is forced by the source: $L^{x_v}$ if $y_v=0$, and $R^{y_v}$ if $x_v=0$, with the empty word when both vanish. No extra “which side is pending” bit, accepted-address string or ancestor-progress capsule is necessary for this eventual-record calculation. This is neither a claim that the original literal installation has fewer headers nor that evaluation needs no workspace.

Proof. At a mixed branch use (14.1)–(14.2) on its actual head word. At a nonmixed branch, every word with the prescribed final multiplicities has the displayed single-side form. AA19.2 gives those multiplicities to the actual completed word, and Theorem 15.1 identifies that word with the pending event's completion. Thus no observation of a nonmixed tape is needed for its EVENTUAL content. In particular an empty new header remains a physically required header even though its content is forced. Substituting these words into the same AA19.2 inverse recovers $w^+$. The construction uses the order of already acquired literal symbols, not a compressed-rank installation or a retained copy of the controller. $\square$

## 16. The exact future indexed-generation task on the actual image

**Definition 16.1 (completion before the selected future task).** Let $\mathcal K_{\rm ret}\subseteq\mathcal K$ consist of cuts for which the already accepted enclosing call has NO further successful source events before its next genuine outer returned cut. This includes a native $G$, a legacy addressed $P/S$, the single new event of an in-range Next, and the final row of a native $F$. For a macro retain its actual outer lock, full inner traffic, arithmetic hook, supervisor continuation and complete outer return. Write $\operatorname{ret}(c)$ for the original execution continued through all those outstanding obligations, with its supplied End/ACK and finite backing. There is no injected request during this continuation. By original completion, its source and tapes at that returned cut are $(t,\mathcal W(w^+))$.

The future task is exactly AA21.1's original $Q_g$: all seven complete request kinds, including guards/refusals, complete replies, FetchGrowth, and Next's recalled pair, new actual event and semantic successor. It starts only AFTER $\operatorname{ret}(c)$. It disregards fresh-name spellings, elapsed microsteps and private scratch as AA21.1 does, while retaining the actual common binding, current rights and declared finite supply. The residual output of the ALREADY accepted call, the time until return and its current phase are not outputs of this future task. They remain original obligations. Arithmetic moduli, connections and any immutable attachment data are kept fixed; equality for this legacy task does not assert recovery of a varying private arithmetic attachment or of the entire scalar/pair task.

For fixed current $t$ define the actually attained set and its explicit record coordinate by

$$
\begin{aligned}
\mathcal K_{{\rm ret},t}&=\{c\in\mathcal K_{\rm ret}:\operatorname{source}(c)=t\},\\
\Theta_t(c)&=(\widehat W_v(c))_{v\in\mathcal A(t)},\\
\mathcal I_t&=\{\Theta_t(c):c\in\mathcal K_{{\rm ret},t}\}.
\end{aligned}
\tag{16.1}
$$

Additional restrictions on the acquired checkpoint, active macro or original schedule restrict these actual sets as well. They do not license treating the full AA19.2 shuffle product as attained inside that restricted schedule. All equality below is on these images.

**Theorem 16.2 (source-specific exact task criterion).** Two cuts $c,c'\in\mathcal K_{\rm ret}$ have the same future $Q_g$ behavior after their respective original completions if and only if

$$
t(c)=t(c')\quad\text{and}\quad
\Theta_{t(c)}(c)=\Theta_{t(c')}(c').
\tag{16.2}
$$

In particular, for any proposed additional accessible relational observation $R(c)$ at fixed $t$, it supports exact answers to EVERY eventual indexed-generation request if and only if, on the actual domain,

$$
R(c)=R(c')\quad\Longrightarrow\quad\Theta_t(c)=\Theta_t(c').
\tag{16.3}
$$

Given the same source, this is also the criterion for the full future $Q_g$ task, including Next. Thus $\Theta_t$ is the precise distinction that must survive over geometry; any representation of it is a least distinction in the sense of observational refinement. The raw mixed head words suffice by Theorem 15.2, but may distinguish cuts which the future task identifies. No physical storage optimum follows.

Proof. By Theorems 15.1–15.2 the pair in (16.2) determines exactly the source and FULL completed tape family at $\operatorname{ret}(c)$. AA21.2 therefore supplies agreement of all future original guards, full replies, settled updates and finite request sequences, including Next's genuine current-source selection and its appended new event. This uses the completed-history result only AFTER proving its inputs from the unfinished words.

Conversely, different current sources remain different through this no-further-growth completion. A Tag at a first differing logical constructor separates them. At equal source, unequal $\Theta_t$ gives unequal full completed tape families. AA19.2's bijection gives unequal generation words. Their equal source fixes their common length $n(t)$, so FetchGrowth at their first differing index returns different literal kind/address pairs. This is an original legal request only after the corresponding outer return. It proves necessity even if a selected single Next happens to have the same new action in two histories; the original task also returns the old pair and permits every FetchGrowth index.

The same separation proves the necessity in (16.3). For sufficiency, each realized observation value specifies a unique normalized mixed family; supplement by the source-forced pure words and use the supplied indexed inverse. This factorization is a semantic existence statement on the actual image. A proposed executable decoder still needs an effective way of obtaining that family from $R$, its actual input access and charged finite work. For the concrete $R=(U_v)_{v\in\mathcal A(t)}$, equations (14.1)–(14.2) are such a finite computation on those observations. The substantive input theorem is the one-event deficit law, not a new general coding or behavioral-congruence theorem. $\square$

**Theorem 16.3 (recovery routes and their exact limitation).** On the image in (16.1), supplemented source support, supplemented terminal boundary, $w^+$, and the eventual original source-backed $Q_g$ memory recover the SAME semantic state at $\operatorname{ret}(c)$. Here the geometric supplements are the mixed head words interpreted by (14.2); equality is after their normalization. These routes recover one another only as future-task classes. They do not recover a particular raw unfinished layout, tail field, program counter or return phase.

Proof. Theorems 15.1–15.2 convert either supplemented geometric view to $(t,\mathcal W(w^+))$ and hence $w^+$. Conversely a finite legal $w^+$ determines its source, completed routing words, material support and terminal boundary by the existing AA19.2/21.2 round trips. Their mixed completed words represent the same class (16.2); they need not reproduce the earlier $U_v(c)$. The original callable memory exists at the actual returned cut by AA20.3–20.5 and LAB11, with its binding and rights retained rather than manufactured by that reconstruction. A head-link assignment followed by a tail assignment already supplies two distinct physical cuts with the same normalized words. The completed history cannot distinguish those cuts. $\square$

## 17. Original cuts and an actual G-to-Next continuation

**Theorem 17.1 (empty headers, root edits and zero-deficit pending writes).** A newly split operand's empty word is correct even while proper ancestors lack symbols. A root edit can have no multiplicity deficit anywhere while arithmetic and full return are outstanding. At a nonroot append all deficits can vanish before its last tail write. These cases belong to the stated original construction; none permits early return or a Busy request.

Proof. For a root promotion the new source is beta, has no branch tapes, and forces the word $P_\varepsilon$. For the following root split the new source $C=\langle\beta,\alpha\rangle$ has its initialized empty root header, $x_\varepsilon=y_\varepsilon=0$, and forces $P_\varepsilon S_\varepsilon$. Maintain has zero proper ancestors in both cases, but the source-complete cut precedes the original arithmetic commit, BuildAnswer, Print/End, ACK and Return. A native $G$ invoked at beta realizes the second case with an additional outer completion still owed.

For a nonroot example start with $C$ and accept $P_R$. After its whole source template the source is $\langle\beta,\beta\rangle$. The root's required counts are $(x,y)=(0,1)$ and its old head is null. Before linking, $U_\varepsilon=\varepsilon$ and the deficit is $(0,1)$. After writing the initialized cell into head, $U_\varepsilon=R$ and both deficits are zero, although tail is still null and the pending append has not been discharged. After the tail write the same head word persists. A later second append, for example from an original $S_L$ after this call has fully returned, instead writes the old tail's next before advancing the nonnull tail; the same distinction holds. Thus zero deficit certifies completed SYMBOL CONTENT, never completed pointer maintenance. A split's own fresh header has zero required child counts by Theorem 15.1 regardless of such ancestor deficits. $\square$

**Theorem 17.2 (incomplete order is consumed after a genuine original G).** There are two original reachable executions with the same earned entry/source packet and the same source-complete $G$ geometry, whose incomplete mixed head words determine different eventual FetchGrowth and Next replies. In each execution the claimed future request is enabled only after the actual complete $G$ return.

Proof. Put $C=\langle\beta,\alpha\rangle$ and $u=\langle C,\beta\rangle$. Use AA20.5's two actually legal words, with every preceding request fully completed:

$$
w_A=P_\varepsilon S_\varepsilon S_LP_R,\qquad
w_B=P_\varepsilon S_\varepsilon P_RS_L.
\tag{17.1}
$$

Both have source $u$ and event index four. They can be pre-entry histories of the same source geometry with earned native packet $(u,\varepsilon)$ and authentic $n_0=4$; the packet does not supply which chronology occurred. Their original root tapes are respectively $LR$ and $RL$, while the tape at $L$ is empty. This reuses the old separation; the continuation and its unfinished record below are the additional bridge.

Now execute the original pair $G$ request $01$ of LAB10.2 on each actual source. Its actual current-leftmost descent acquires beta at $LL$ and its actual reference. The supervisor sends the original internal $S_{LL}$ frame to the bound driver; Navigate compares the acquired reference and Guard accepts the actual beta. Finish the original source template, including binding the new empty header at $LL$. The common current source is

$$
z=\langle\langle C,\alpha\rangle,\beta\rangle.
\tag{17.2}
$$

The root's required counts are $(2,1)$, the branch $L$ has counts $(1,0)$, and the new branch $LL$ has counts $(0,0)$. Before either ancestral link, the actual words and their normalized completions are

| Branch | $U$ in execution A | $U$ in execution B | $\widehat W$ in A | $\widehat W$ in B |
| --- | --- | --- | --- | --- |
| $\varepsilon$ | $LR$ | $RL$ | $LRL$ | $RLL$ |
| $L$ | empty | empty | $L$ | $L$ |
| $LL$ | empty | empty | empty | empty |

Only the root is mixed in the final source. Reading its incomplete ORDER is necessary on this two-execution image; the source forces all other eventual words. The missing final $L$ at the root is forced by counts and needs no phase bit. Bottom-up Maintain first links $L$ at branch $L$, leaving only the root deficit; then it advances that header's tail and ascends. It links the final $L$ at the root before advancing the root tail. At this last link cut every deficit is zero and the root tail is still pending, exactly the obstruction of Theorem 17.1. The new $LL$ header remains correctly empty throughout.

Continue the ORIGINAL execution. Finish the root tail and pending cursor, all ancestral maintenance and the LAB11 all-event commit. This split increases $(a,b)$ by $(1,0)$ and quantity by two; scalar successors and pair successors are written from their own pre-edit banks, not replaced by a macro-end overwrite. The driver constructs and prints the FULL Growth reply with kind $S$ and address $LL$, then End, the supplied inner ACK, actual root Return and scratch cleanup. The supervisor backs and parses the entire reply and End, validates kind/address against its saved call, acknowledges and consumes the actual inner return. This $G$ has exactly one inner event. It then constructs and prints its original outer acknowledgement $00$, followed by End, outer ACK, real outer Return and cleanup, before releasing the lock. The earned completed native packet may now post its $G$ once. There is no query or parent-private read in this interval. Its original source additions are two vertices, one header and two ancestral side cells, with their actual initialization, references, links, grants and backing; the equal normalized words at an earlier cut waive none of them.

Only now supply a complete original public FetchGrowth$(3)$ request. The original handler scans the now-complete actual tapes and returns Recall with $(S,L)$ in A and $(P,R)$ in B. Its whole kind/address payload, End, supplied ACK and Return are consumed. A complete original Next$(3)$ request can then follow. Its INTERNAL FetchGrowth handler acquires that same old pair without an outer return, navigates from the SAME bound root to $L$ or $R$ in $z$, and performs the original current left descent. In A it reaches beta at $LLL$; in B it reaches beta at $R$. The actual enabled new events are therefore

$$
\begin{aligned}
\text{A: }&S_{LLL},&\text{Next reply: }&((S,L),(S,LLL)),\\
\text{B: }&S_R,&\text{Next reply: }&((P,R),(S,R)).
\end{aligned}
\tag{17.3}
$$

The corresponding source successors are different: A changes a proper descendant of the left subtree, while B changes the right beta into $C$. Each new event performs its original source edits, full ancestral appends, every-event arithmetic hook and complete Next payload/End/ACK/Return. The recalled old event is not counted as a second new edit. Previous indexed answers persist; at the next returned cut index six recalls the actual event in (17.3). Indices zero and greater than five before this Next are OutOfRange, with Next then making no edit. All connections and recipients are the original ones. This realizes the future task whose differing record was already mathematically determined at the unfinished cuts in the table. $\square$

## 18. Access, remaining obligations and the exact source correspondence

**Definition 18.1 (three meanings of evaluation).** The projections $U_v$, the integer counts and (14.2) first define mathematics on an actual cut. They do not grant the supervisor or an external requester access to driver-private headers during Busy. The original driver owns the source/record rights, but its original Maintain schedules its specified parent-chain appends, not a whole-source deficit traversal.

A separate finite evaluation on lawfully acquired source/record observations can compute these formulas: obtain child counts by finite postorder addition with birth typing, scan each selected actual head/next chain to null while counting its side bits, apply (14.2), insert the source-forced pure words, and use AA19.2's finite inverse. Running such an evaluation as owner-local bookkeeping would require expressly scheduled additional local work with stable inputs, paid field and bit reads/writes, backed counters and stacks, copying, allocation, any required records and cleanup. It is not installed or invoked by the theorem. An external evaluation requires its actual acquisition and communication contract; it cannot automatically collect the owners' components from §10. An earned compact source can supply descriptive counts, but it cannot supply an unread literal tape or a physical source reference.

The operative future evaluation in Theorem 17.2 is instead the UNCHANGED original FetchGrowth/Next scan after full original return. It reads its own bound records under AA20.1, uses its original acquired unary index marks, within-side counter, address and continuation backing, and pays AA22.3's traversal/output costs. No deficit checker is inserted into that execution. All claimed operative steps in that theorem are original scheduled actions.

**Theorem 18.2 (symbol recovery does not pay a physical obligation).** No statement in §§15–16 permits discharge of an original pending append, commit, output or return merely from equality of source counts and head multiplicities. In particular it gives neither an enabled Busy query nor a bound polynomial in the compact parameter $N$ for all original source/record work.

Proof. At depth $d$, the event owes one original cell append at each of its $d$ proper ancestors. Its head word can already include the cell while the tail assignment, pending-cursor advance or arithmetic commit remains enabled and unfinished. Theorem 17.1 supplies actual such cuts. AA22.1's initialized-cell, linking and tail assignments remain the specified physical work; (14.2) performs none of them. Before the original pending state is discharged, BuildAnswer cannot release the event reply. Original print backing, every payload bit, End/ACK, inner Return and, inside a macro, outer payload/End/ACK/Return retain their original order and price. Old/new arithmetic banks, reserved cells, private continuations and archived records remain simultaneously backed where their phases overlap.

Even when $\mathcal A(t)$ is empty, the original literal installation still retains every branch header and its actual side cells, including pure-side tapes. Restricting a mathematical observation to mixed nodes deletes no objects. Computing source counts or obtaining words also has its actual bill. A literal whole-source traversal visits unfolded occurrences, and head scans visit actual tape cells; neither cost is bounded by the number of compact DAG nodes alone. Theorem 10.4's existing distinction between compact descriptive work and original physical work therefore persists. The theorem removes a missing-symbol INFORMATION requirement under its hypotheses; it removes no original construction or protocol obligation. $\square$

**Definition 18.3 (suppliers and unresolved recovery boundaries).** The count law, full completed routing inverse and seven-request task are reused from [AA §§19–21](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#19-acquired-local-records-for-all-generation-events); the precise source/header template and located link-before-tail assignments are AA20.2/22.1. The actual $G$, private routing, arithmetic banks and all-event commit are [LAB §§9–11](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md#9-actual-pair-actions-and-exact-composition-reachability). Rooted §§42–44 and §§8–13 here supply the earned checkpoint, source geometry and coherent partial-frontier results. Their completed and partial source/history inverses are not reproved. NativeLocalSourceExecution.native_execution and NativeCompletedHistoryRecovery.completed_history_recovery remain previously formalized suppliers in their stated syntax/replay scopes, not certification of these unfinished physical-record claims.

The additional result is the `repo-derived` one-accepted-event head-word completion law and its actual-image future-task criterion for the ORIGINAL LITERAL installation. The count-based removal of forced pure-side words is an information projection only. AAII §§47–52 and §§75–80 already give installed compressed coordinates for other layouts; no rank bank, journal or replacement layout is installed here. Finite counting, source parsing, the old shuffle inverse and semantic factorization are reused tools, without a new general coding theorem or worldwide originality claim. These ordinary mathematical proofs have no fresh Lean certification and no digestion or freezing claim.

For an interior row of an unfinished $F$, Theorem 15.1 still recovers the record through that very accepted event. The remaining sealed OLD rows can cause more real events before any outer request is legal; they and their actual operands/continuation must still be executed. Theorem 16.2 deliberately concerns $\mathcal K_{\rm ret}$, not such an uncompleted suffix. Multiple outstanding accepted events, incomplete source/header installation, reordered linking, crash recovery, observable exhaustion and arbitrary access have no theorem here. Source completeness, the pre-event record invariant and one-event serialization are essential premises. Bare geometry still cannot recover serial order, physical phase or callable rights. Mutual recovery for the larger ongoing relational programme remains unresolved beyond the stated actual-image bridge.

## 追加锚（本行以下为增补区）

## 19. Synchronizing a positive-progress original F from unfinished words

**Definition 19.1 (the actual interior-F domain).** Let $\mathcal F_+$ be the following restriction of Definition 14.1's one-event domain. The actual enclosing call is the original native $F$, namely LAB9.3's $\mathsf R$ on its original pair connection. Its actual entry $u$ belongs to $\mathcal D_+$. Before dispatching any row, its original stationary acquisition has sealed the complete LEFT-FIRST OLD logical frontier of that very $u$, with the original tags, backed addresses, references and next links. No newly born leaf enters that list. Write its logical event list as

$$
\mathsf{Old}(u)=e_1\cdots e_L,\qquad
e_i=(k_i,p_i),\qquad L=\ell(u),
\tag{19.1}
$$

where $k_i=P$ at an entry-alpha leaf and $k_i=S$ at an entry-beta leaf. This is the logical projection of the acquired list, not a supplied replacement list. Word subscripts $1:i$ include both endpoints; $<s$ means the prefix strictly before position $s$.

At the selected cut exactly the first $j-1$ inner calls have genuinely returned, and the $j$th has accepted its original operand and finished its WHOLE source/header template, where $1\le j\le L$. Its original Maintain is entered or in progress as in Definition 14.1. There is exactly one accepted unfinished event. Every preceding event has its correct full ancestral tapes and finished arithmetic hook. Let $h$ be the actual successful alpha-origin word before this $F$. Thus the current source $t$ and successful-event word through the selected source edit satisfy

$$
u=\operatorname{Replay}_{\alpha}(h),\qquad
t=F_j(u),\qquad w^+=h e_1\cdots e_j.
\tag{19.2}
$$

Here $F_j$ is the existing logical prefix operation of Rooted43.1; equation (19.2) concerns its source projection and does not count the pending inner call as returned. The variables $h,u,j,L$ describe the actual execution in the domain premise. They are NOT arguments supplied to the recovery below. The only varying relational inputs are the current source, or its source-complete support/boundary, and the actual head words at its mixed branches. The active command $F$ and positive source progress are declared domain conditions, not conclusions inferred from those inputs.

Keep the actual same root/epoch, original private ownership, bindings, current exclusive source/record rights, original scalar/pair attachments, reserved material, pending fields, complete inner and outer traffic, supplied local ACK and sufficient finite backing for the WHOLE remaining call. All of Definition 14.1's exclusions remain. The pre-$F$ word $h$ may contain arbitrary earlier legal LAB growth; no particular pre-entry primitive shuffle or independently retained exact entry count is assumed.

**Lemma 19.2 (the last pure-left event marks the actual F entry).** For every $c\in\mathcal F_+$, put $N=|w^+|=n(t)$ and define

$$
s(w^+)=\max\{i\in\{1,\ldots,N\}:\operatorname{addr}(w_i^+)\in\{L\}^{*}\}.
\tag{19.3}
$$

The set includes the empty address as a pure-left address. It is nonempty, its maximum is $|h|+1$, and its event is $S$ at the actual leftmost beta of $u$. Consequently

$$
j=N-s(w^+)+1,\qquad h=w^+_{<s(w^+)}.
\tag{19.4}
$$

Proof. A finite ordered logical tree has exactly one leaf reached by repeatedly choosing its left child. Its address contains only $L$; every other leaf address contains $R$, since at its first departure from that descent it chooses a right child. On $\mathcal D_+$ that first leaf is beta by LAB9.4. The first original OLD row therefore executes its split, at a pure-left address, including the root split when $u=\beta$. Every other OLD row has an address containing $R$. Earlier edits preserve the addresses of all those disjoint old operands. In particular neither new child of the first split is inserted as another OLD row. It follows that among the actual current-$F$ events $e_1,\ldots,e_j$, exactly $e_1$ has a pure-left address. Whatever pure-left events occurred in $h$ precede it. This proves (19.3)–(19.4). The test concerns literal address letters and chronological position, not an elapsed-time readout or an allocation ordinal. $\square$

**Theorem 19.3 (entry, source progress and remaining actions without a private-stage input).** On $\mathcal F_+$, current source $t$ and ONLY $(U_v)_{v\in\mathcal A(t)}$ constructively determine the actual $h,u,j$, the entire remaining logical OLD suffix, and the source and successful history at the original eventual $F$ return. None of those targets is an extra input.

More explicitly first use Theorem 15.2 to form the completed family $\widehat{\mathcal W}$, and AA19.2's supplied inverse to obtain $w^+$. Then compute $s=s(w^+)$ and set

$$
\begin{aligned}
\widehat h&=w^+_{<s},&
\widehat j&=n(t)-s+1,&
\widehat u&=\operatorname{Replay}_{\alpha}(\widehat h),\\
\widehat L&=\ell(\widehat u),&
D(c)&=\mathsf{Old}(\widehat u)_{\widehat j+1:\widehat L},&
r(c)&=w^+D(c)=\widehat h\,\mathsf{Old}(\widehat u),\\
x(c)&=\rho\widehat u.
\end{aligned}
\tag{19.5}
$$

An exhausted suffix is the empty word. These formulas give $\widehat h=h$, $\widehat u=u$, $\widehat j=j$, $\widehat L=L$, and the ACTUAL remaining new source events $D(c)$. In particular, when $j<L$, they recover a nonempty suffix rather than assuming that the current event is the final row. They also satisfy the existing partial-inverse equation

$$
\widehat u=U^B_{\widehat j}(t),\qquad
n(\widehat u)=n(t)-\widehat j=s-1.
\tag{19.6}
$$

Proof. Theorem 15.2 supplies exactly the real full word through the pending source edit, despite unfinished ancestor links or tails. Lemma 19.2 locates its actual $e_1$. Its prefix before that event is therefore the actual $h$, and its suffix from that event has exactly $j$ events. Legal descriptive replay from the known alpha gives the actual $F$ entry. This identifies the target by a test of observed words, without presupposing an entry, progress counter, saved subphase, next mark or macro delimiter.

LAB9.4's disjoint-old-operand argument now applies to this recovered actual entry and the original acquired list: its remaining addresses still denote the same old leaves with the same tags and references. Enumerating the leaves of the recovered DESCRIPTION therefore gives the logical projection of precisely the retained actual suffix. It supplies no new physical references. The source of the current cut is $F_j(u)$ because each preceding row has acted once and the current row's source template is complete. Applying Rooted43.2, rather than reproving its partial inverse, gives (19.6). Executing the remaining original rows has final source $\rho u$ by LAB9.4 and appends exactly $D(c)$ to the successful word. This proves all identities in (19.5); Theorem 20.1 below accounts for the pending completion and real return.

At a source-complete cut, AA17.3 and Theorem 15.1 parse source support or terminal boundary into this same $t$. The head-word observations are attached at their actual branch occurrences. The identical computation therefore works from either geometric view. No shared descriptive node merges two different actual branch headers. $\square$

**Corollary 19.4 (an earlier authentic checkpoint remains recoverable).** Suppose in addition that an authentic $n_0>1$ identifies an earlier native entry $t_0$, that $h$ contains at least $n_0$ events, and that only genuinely completed native $F/G$ macros occur between that entry and the present $F$ admission. The recovered $u$ and $n_0$ determine the actual earlier $(t_0,W)$ by Rooted42.4. Equivalently replay of the first $n_0$ recovered events of $h$ gives $t_0$, and the existing completed inverse supplies $W$. The current $F$ is not posted into $W$ before its genuine outer return.

Proof. The additional premise is exactly the domain of Rooted42.4, now with its final source $u$ derived by Theorem 19.3. The primitive prefix length is the entry's event index by AA19.1. Both routes thus recover that same actual checkpoint. At $n_0=1$ the existing first-$F/G$ ambiguity is retained; (19.5) neither reconstructs a missing command bit nor claims to recover an unsupplied $n_0$. $\square$

## 20. Real completion and correspondence across successive original rows

**Theorem 20.1 (the recovered suffix is consumed by the original execution).** For $c\in\mathcal F_+$, continue the already accepted original call under its retained rights, actual continuations, finite supply and supplied acknowledgements, without injecting an outer request. It has a genuine returned cut $\operatorname{ret}_F(c)$ with

$$
\operatorname{source}(\operatorname{ret}_F(c))=x(c),\qquad
\operatorname{history}(\operatorname{ret}_F(c))=r(c),\qquad
\operatorname{tapes}(\operatorname{ret}_F(c))=\mathcal W(r(c)).
\tag{20.1}
$$

The future source edits are exactly $D(c)$, in that order. This conclusion includes the original work still owed by the current event and every inner/outer return; (19.5) does not execute or discharge any of that work.

Proof. First resume the actual pending Maintain at its retained append subphase. A fresh cell's side and null next are initialized, its link is written from the old tail or empty head, and only then is the header tail advanced. If the link has already been written, complete its pending tail/cursor work instead of appending a second symbol. Finish each remaining proper ancestor in the original bottom-up order. The recovered $w^+$ names the accepted event, but its equality to the eventual record never marks an unfinished physical write as done.

Complete LAB11's every-event hook from the retained pre-edit banks: a $P$ adds $(-1,1)$ to the pair and one to quantity, and an $S$ adds $(1,0)$ to the pair and two to quantity. The two scalar successors are those of LAB (LAG.11), each computed from its original old operands. Write every successor and discharge pending edit/append/commit state before releasing the reply. Immutable attachment fields remain fixed. A partially overwritten bank is not treated as a completed pair.

The driver then backs and prints its FULL original Growth reply, containing its actual kind and the whole address, followed by End, supplied inner ACK, real root Return and cleanup. The supervisor receives and backs every bit and End, validates kind/address against its saved original call, acknowledges and consumes the real inner return. Its saved row and continuation determine whether it still owes list advancement; a raw cursor on the returned row is not the next untouched operand. Follow its actual next link as Rooted43.5 specifies. The mathematical reconstruction does not access this private continuation or replace it with a guessed cursor.

For each remaining original row, its acquired tag/address/reference is still valid by LAB9.4. The bound driver really re-navigates from its root, compares that reference, tests the current guard and reserves sufficient material. A promotion uses its original marker initialization and attachment. A split uses the original marker reuse, new left marker and right alpha, all parent fields and auxiliary-slot initialization, and its bound empty header. There are no inverse edits or skipped fields. At depth $d$, the event completes all $d$ original ancestral appends with their initialized/link/tail assignments, the same arithmetic hook, and the full original inner reply/End/ACK/Return. Only after that return does the caller advance to the next old row. Induction gives exactly $D(c)$ and all its tape projections; no new leaf is inserted in the sealed list.

The finite suffix exhausts after $L-j$ such inner calls. This is LAB11.2's original completion proof applied to the actual residual, not a new executor. Finish the original outer pair acknowledgement $00$, its full backed output and End, outer supplied ACK, actual outer Return, root restoration and scratch/list clearing before releasing the arbiter. There is no macro-end overwrite by $Mv(u)$ after the per-event commits. Any maintained completed packet posts $F$ once at this outer milestone, as in Theorem 10.3. Thus the returned source, history and tapes are (20.1), with the original scalar and pair invariants restored. $\square$

**Proposition 20.2 (one returned semantic state along a changing row geometry).** Fix one actual admission with entry $u$ and preword $h$. After $i$ complete source templates, $1\le i\le L$, put

$$
t_i=F_i(u),\qquad w_i=h\,\mathsf{Old}(u)_{1:i}.
\tag{20.2}
$$

At a cut in $\mathcal F_+$ with this source progress, equations (19.3)–(19.5) return $u,i$ and the suffix after row $i$. They do so also at a coherent post-inner-return cut using its now-true complete head words. Across all such successive cuts,

$$
r_i=h\,\mathsf{Old}(u),\qquad x_i=\rho u,
\qquad n(t_{i+1})=n(t_i)+1.
\tag{20.3}
$$

The recovered remaining-event relation advances by deleting exactly its next event. Pure linking/tail, commit, output and return transitions do not change $t_i$ or $w_i$. At the final inner return the remaining-event word is empty, but the outer return is still owed.

Proof. All later OLD addresses contain $R$, so extending $w_i$ by the next original row preserves the pure-left maximum at index $|h|+1$. Formula (19.4) therefore increments source progress exactly once when that next source template finishes. At a coherent cut all head words are already $\mathcal W(w_i)$, so the same completion formula has zero deficits and yields $w_i$ directly. Theorem 15.1 gives that same normalized word at the preceding pending-append cuts. Original serialization provides the true prior tapes required when the next row enters $\mathcal F_+$. LAB9.4 gives the next source and AA19.1 gives its one-event count increment. Concatenating the already edited prefix and remaining suffix proves (20.3).

In particular, if $L\ge2$, different positive row cuts have distinct current geometry but the SAME final $(x_i,r_i)$. That final semantic state alone therefore cannot recover which of those row cuts was selected. Even with current geometry supplied, equal normalized words cannot recover a particular link-before-tail, arithmetic, printing or return subphase. Before the next whole source/header template finishes, a raw material cut such as Theorem 9.2's $U(U(E))$ is outside (20.2)'s logical domain. No claim silently fills that interval. $\square$

## 21. The exact eventual task, globally and at a fixed current source

**Definition 21.1 (the post-F task and its normalized mixed coordinate).** On $\mathcal F_+$ let the selected future task first allow the original $F$ to finish as in Theorem 20.1, and only THEN use the entire original $Q_g$ of AA21.1. It retains all seven requests, guards/refusals, full replies, FetchGrowth, Next's old/new pairs and semantic successors. Compare the same finite future request sequences. Fix the same installation/binding/rights and immutable arithmetic attachments and retain sufficient finite supply, exactly as in Definition 16.1. The residual traffic of the already accepted $F$, its time until return and its intermediate phases remain obligations, rather than outputs selected by this eventual task.

For a fixed current $t$ put

$$
\mathcal F_{+,t}=\{c\in\mathcal F_+:\operatorname{source}(c)=t\},\qquad
\Theta_t(c)=(\widehat W_v(c))_{v\in\mathcal A(t)}.
\tag{21.1}
$$

The words are those already derived by (14.2), not an independently supplied return record. Use only the actual image of $\mathcal F_{+,t}$, further restricted by any genuine checkpoint or schedule predicates in force. The full AA19.2 shuffle product is not presumed attainable inside this current-$F$ domain.

**Theorem 21.2 (global returned-history criterion and fixed-source criterion).** For any $c,c'\in\mathcal F_+$,

$$
\begin{aligned}
&\text{their post-F }Q_g\text{ tasks agree}
&&\Longleftrightarrow\quad r(c)=r(c'),\\
&c,c'\in\mathcal F_{+,t}:
&&r(c)=r(c')\quad\Longleftrightarrow\quad\Theta_t(c)=\Theta_t(c').
\end{aligned}
\tag{21.2}
$$

At fixed current $t$, this normalized mixed distinction also determines the actual entry, source progress and remaining logical OLD schedule. Raw unfinished head words can carry additional phase distinctions which (21.2) forgets. Globally, equality of $\Theta$ at different sources is not a task criterion, and equality of the returned task does not require equal current source or progress.

Proof. Theorem 20.1 gives the actual returned state $(x(c),\mathcal W(r(c)))$, and $x(c)$ is the source obtained by legal replay of $r(c)$. AA21.2 therefore supplies full future-task agreement when the returned words agree, including the real source-selected Next successor. Conversely unequal finite returned words are separated by FetchGrowth at a first different index, or by Recall versus OutOfRange when one word is a proper prefix. Such a request is supplied only after the respective genuine outer returns. Thus equality of $r$ is necessary and sufficient globally; this applies the existing settled task theorem to inputs now derived from the ongoing call.

At fixed $t$, equal $\Theta_t$ supplies equal full normalized families by filling the source-forced pure words. AA19.2 gives equal $w^+$, and Theorem 19.3 gives equal entries, progresses, suffixes and $r$. Conversely suppose $r(c)=r(c')$. Each current successful word is a prefix of this common returned word, and its length is the SAME $n(t)$. Consequently both equal its first $n(t)$ events. Theorem 15.1 identifies their normalized tapes with the projections of that same prefix, proving equality of $\Theta_t$. This direction neither inverts a physical source edit nor supposes equality of physical pending states. Proposition 20.2 supplies actual different-source row cuts with equal $r$, proving the asserted global qualification. $\square$

**Corollary 21.3 (the exact additional relation needed over geometry).** On the actual fixed-$t$ domain, an accessible relational observation $R$ supports exact eventual $Q_g$ behavior if and only if

$$
R(c)=R(c')\ \Longrightarrow\ \Theta_t(c)=\Theta_t(c').
\tag{21.3}
$$

The concrete raw mixed words meet this condition by their finite normalization. For any other $R$, sufficiency as a semantic factorization does not assert that its inverse is computable or that $R$ has actually been acquired. No product cardinality, bit optimum or layout replacement follows.

Proof. Necessity follows from the original FetchGrowth separator in Theorem 21.2. For sufficiency each realized $R$ value has one normalized mixed value, which specifies the actual entry, progress, remaining actions and eventual task by Theorems 19.3 and 21.2. The factorization principle is the existing finite-fibre/behavioral criterion; the additional source-specific premises establishing its concrete coordinate are Lemma 19.2 and the unfinished-word completion law. $\square$

**Proposition 21.4 (the conditional recovery routes).** Supplemented current support, supplemented current terminal boundary and current successful word $w^+$ recover one another as NORMALIZED semantic views on $\mathcal F_+$. Each determines the derived tuple $(u,j,D,x,r)$. The eventual original callable memory has exactly the global returned-word distinction $r$. Together with the supplied current source it recovers $w^+$ and hence the normalized active semantic view; alone it need not do so.

Proof. Source/boundary parsing and Theorems 15.2 and 19.3 give the forward maps. Conversely legal replay of $w^+$ gives its source, completed routing projections, source support and terminal antichain. The resulting supplemented views normalize to the originals, even when their earlier raw head words lacked a final symbol. Original callable memory at the genuine return reads the full actual tapes under AA20 and determines $r$ by AA19.2. With current $t$ supplied, take the first $n(t)$ events of $r$ to obtain $w^+$. Proposition 20.2 proves why $r$ alone loses the selected current cut. These are compatible maps for one actual source history, not freely chosen compatible representatives. The temporal coordinate is successful addressed-event order and row progress, not elapsed physical time, and none of these maps reconstructs authority from a description. $\square$

## 22. Strict interior progress and a nonempty-suffix F-to-Next consumer

**Proposition 22.1 (the synchronization separates the existing interior source collision).** Reuse Rooted43.6's two executions from $C=\langle\beta,\alpha\rangle$, whose known-alpha prefix is $P_\varepsilon S_\varepsilon$. After completed $FG$ versus completed $GF$, respectively, select the source-complete Maintain cut of active $F$'s third versus second row. Both lie in $\mathcal F_+$ and have the same current source

$$
y=\langle\langle\langle C,\beta\rangle,\beta\rangle,\beta\rangle,
\qquad n(y)=8.
\tag{22.1}
$$

Their recovered $(u,j,D)$ are respectively

$$
\begin{aligned}
u_A&=\langle\langle C,\alpha\rangle,\beta\rangle,&j_A&=3,&D_A&=S_R,\\
u_B&=\langle\langle C,\beta\rangle,\beta\rangle,&j_B&=2,&D_B&=S_{LR}S_R.
\end{aligned}
\tag{22.2}
$$

Proof. The entries, prefix effects and residual schedules are exactly Rooted43.6's supplied source collision. Every preceding inner row can fully return before the selected next original source template, giving Definition 19.1's cuts with one accepted unfinished event and correct prior tapes. Theorem 15.2 recovers their actual words, which after the common root prefix are

$$
\begin{aligned}
w_A^+ &: S_L\,P_R\,S_{LL}\,S_{LLL}\,P_{LLR}\,P_{LR},\\
w_B^+ &: S_L\,S_{LL}\,P_{LR}\,P_R\,S_{LLL}\,P_{LLR}.
\end{aligned}
\tag{22.3}
$$

The last pure-left events are $S_{LLL}$ at absolute indices six and seven. Formula (19.4) gives $j_A=8-6+1=3$ and $j_B=8-7+1=2$; replay before those indices gives precisely (22.2)'s entries. Their remaining schedules have different first addresses and lead to different fully replaced sources, with $\beta$ versus $C$ at address $LR$. This is the unfinished-record recovery and remaining-call interpretation of the attributed collision, not a new collision family or an assumption of an exposed progress field. $\square$

**Proposition 22.2 (actual incomplete memory consumed after the whole F).** Let $u=\langle C,\beta\rangle$ and reuse AA20.5's two legal prewords

$$
h_A=P_\varepsilon S_\varepsilon S_LP_R,\qquad
h_B=P_\varepsilon S_\varepsilon P_RS_L.
\tag{22.4}
$$

In each original execution invoke $F$ through its complete pair frame $00$, acquire and seal its actual OLD list, and pause during its FIRST row's source-complete Maintain. The recovered record determines a genuine continuation with TWO further inner events before the outer return, followed by different original FetchGrowth and Next behavior.

Proof. Both attributed histories end at $u$, with root words $LR$ and $RL$ and an empty tape at $L$. The same actual logical OLD projection is

$$
\mathsf{Old}(u)=S_{LL}\,P_{LR}\,S_R.
\tag{22.5}
$$

Its first actual operand is beta at $LL$. The bound driver compares the acquired reference, accepts its guard and completes the original split/header template. At the cut before either ancestral link, the current source is

$$
t=\langle\langle C,\alpha\rangle,\beta\rangle.
\tag{22.6}
$$

This reuses Theorem 17.2's first-split geometry and local count calculation, with the enclosing command now the original $F$. At the root, required counts are $(2,1)$ and the actual incomplete words are $LR$ versus $RL$. They normalize to $LRL$ versus $RLL$. Branch $L$ has forced final word $L$, and the new branch $LL$ has the correct empty word. Thus the only mixed observation needed is that actual root word. Theorem 15.2 recovers $w_A^+=h_AS_{LL}$ and $w_B^+=h_BS_{LL}$. Their last pure-left event is at index five in each case. Equation (19.5) recovers $u$, $j=1$, and the nonempty suffix $P_{LR}S_R$ from those inputs.

Finish the actual $LL$ event's two ancestral appends, pending tails/cursors, split arithmetic hook and full Growth$(S,LL)$ reply, End, inner ACK, root Return and cleanup. The supervisor validates the full payload and actual inner return. It advances from its still-backed original row along the actual next link to $LR$, not to either new $LL$ child. The original $P_{LR}$ re-navigates, compares its reference, checks alpha, supplies its fresh marker, completes its source/auxiliary initialization and appends $R$ at branch $L$ and $L$ at the root. Its all-event hook adds $(-1,1)$ to the pair and one to quantity from its own pre-edit banks. Its entire Growth$(P,LR)$ reply, End, ACK and inner Return precede the next advancement.

The final original row still denotes beta at $R$. Its $S_R$ performs the full split and new empty header, appends $R$ at the root, and adds $(1,0)$ to the pair and two to quantity. It emits Growth$(S,R)$ with its whole address, End, ACK and inner Return. The actual final source and records are

$$
\begin{aligned}
x&=\rho u=\langle\langle C,\beta\rangle,C\rangle,\\
r_A&=h_A S_{LL}P_{LR}S_R,&
r_B&=h_B S_{LL}P_{LR}S_R,\\
W_\varepsilon(r_A)&=LRLLR,&
W_\varepsilon(r_B)&=RLLLR,\\
W_L(r_A)&=W_L(r_B)=LR,&
W_{LL}(r_A)&=W_{LL}(r_B)=W_R(r_A)=W_R(r_B)=\varepsilon.
\end{aligned}
\tag{22.7}
$$

Only after the original outer $00$ acknowledgement, End, outer ACK, actual Return and cleanup may the arbiter admit another request. Every-event arithmetic has followed the successive exact count pairs $(1,2)$, $(2,2)$, $(1,3)$, $(2,3)$; no final overwrite stands in for those commits. This complete $F$ has one promotion, two splits and total old-address depth five. It adds five source vertices, two headers and five side cells; AA22.1/LAB13.2 give twenty located source-field assignments and thirty-one auxiliary-slot/header/tape assignments. Its three inner request frames contain twenty-two bits and their full Growth replies twenty-five bits in total, with three inner End/ACK/Return completions. Allocation, grants, actual reference widths, original traversal/list backing, arithmetic, outer traffic, output, return and cleanup remain additional costs. These are full-call counts from entry, including already performed writes at the selected cut.

Now supply an actual complete public FetchGrowth$(3)$. The original owned-tape handler returns Recall$(S,L)$ in A and Recall$(P,R)$ in B, with the full kind/address payload and its End/ACK/Return. After that genuine return, supply a complete original Next$(3)$. Its INTERNAL FetchGrowth acquires that old pair without an outer return. In A, navigation to $L$ in $x$ and current left descent reach beta at $LLL$; in B, navigation to $R$ and current left descent reach beta at $RL$. Its actual new events and complete Next payloads are

$$
\begin{aligned}
\text{A: }&S_{LLL},&\text{reply: }&((S,L),(S,LLL)),\\
\text{B: }&S_{RL},&\text{reply: }&((P,R),(S,RL)).
\end{aligned}
\tag{22.8}
$$

Each performs the original guarded source change on that same bound source, new header, all ancestral appends, split arithmetic hook, full output, End, supplied ACK, real Return and scratch clearing. The old recalled event is not another edit. The two successors differ at actual addresses $LLL$ and $RL$, and at the next returned cut index eight recalls precisely the corresponding new event. Before this Next, indices zero and greater than seven are OutOfRange; an out-of-range Next has no edit, and an incomplete frame still waits. All seven original request kinds and their original receivers are retained. Thus a literal distinction already recoverable during the first unfinished row is consumed after the ENTIRE original nonempty suffix and genuine outer return. $\square$

## 23. Lawful observation, paid local acquisition and the remaining boundary

**Proposition 23.1 (a permitted owner-local acquisition and its price).** Under the existing paid local-bookkeeping permission of Definition 10.1, with sufficient supplied finite backing for the additional work and its required records, a finite source-independent owner-local evaluation can be scheduled at the driver immediately after a complete source/header template and before its first ancestral append. On $\mathcal F_+$ it earns the inputs and performs (19.3)–(19.5), without reading a supervisor-private stage, acquiring an external Busy interface or changing an original source event. More generally the mathematical formulas apply to any cut in $\mathcal F_+$ when those observations have been lawfully acquired and kept stable during evaluation. The unaugmented original driver is not asserted already to run this evaluator.

Proof. At the specified scheduling point the driver already owns the actual root, source fields and bound records under AA20.1. The original supervisor is waiting on its still-unreturned inner call, and no competing writer or outer request is admitted. During this finite local routine postpone further Maintain assignments, so source and head-reachable words are stationary. Traverse owned source occurrences from that root, excluding material beta markers, and count each child's birth-typed events by finite postorder addition. Determine $\mathcal A(t)$ from those counts. At each selected actual branch follow its owned header head and next links to null, retaining the actual side order. No header tail is used as a last-cell oracle. These finite scans earn precisely the inputs of Theorem 19.3; unlinked reserved cells are not observations. The routine can compute the same formulas without testing a private caller identity. Their interpretation as the actual current-$F$ entry and residual is conditional on the declared $\mathcal F_+$ premise, not a recognizer of that premise.

Use backed finite counters, traversal stacks, address buffers and descriptive replay storage to normalize the words, invoke the supplied inverse, scan literal addresses for the last pure-left event, and enumerate the recovered entry's remaining OLD addresses. All loops consume finite acquired trees, words or addresses. Nothing reads a released OLD prefix or recasts a descriptive address into an actual target reference. Read/write work, full acquired operands and results, copying, arithmetic, allocation, required local records and their retained backing, and later clearing/reuse have their actual charges. The pending source event's reserved material, old/new arithmetic banks and original continuations coexist with this work; a pause does not erase them. The result remains driver-local and grants no other participant access to it.

Resume the original pending Maintain and Theorem 20.1's original continuation after this finite local computation. Erasing only the added local actions leaves the original ordered source/record/traffic trace, with all original fields and obligations. This uses the permission already stated in Definition 10.1; without that permission the computation is a finite evaluation on supplied observations, not installed acquisition. In either case the operative public FetchGrowth/Next consumer remains the original one AFTER the genuine $F$ return, as Proposition 22.2 exhibits. It reads the actual completed records; it does not receive an independently assumed $r(c)$.

If $V$ is the unfolded logical source size, $T$ the total number of actually scanned mixed tape cells, $E=n(t)$ and $A$ the sum of the full decoded event-address lengths, a direct acquired representation pays $O(V)$ constructor bits, the $T$ observed side bits and $E+A$ decoded kind/address bits, with word framing, indices, references and working buffers additional. A direct source traversal visits occurrences, and a literal tape scan visits cells, regardless of shared descriptive DAG nodes. For a complete $F$, the existing $L$ OLD rows, their addresses/references, every inner navigation and $J_F=\sum_i|p_i|$ ancestral appends remain paid. AA22.1 and LAB13 give the separate field, material, full traffic, arithmetic, allocation/grant and simultaneous-backing accounts. The compact parameter $N$ in Definition 8.1 is different from this $E$. No polynomial whole-call bill in that compact parameter, constant-width references, free control state or total-resource optimum is inferred. $\square$

**Definition 23.2 (suppliers and scope of the additional correspondence).** AA17–22 supplies the irreversible source lifecycle, material support/boundary parser, full ancestral-word inverse and counts, exact literal append order, original internal FetchGrowth/Next, complete returned $Q_g$ and its work/material contracts. LAB9.3–9.4 supplies the actual fixed-left sealed OLD list and preservation of every disjoint old tag/address/reference. LAB10–11 and 13 supplies the original caller/driver ownership, full traffic, every-event arithmetic hook, actual inner/outer return and resource obligations. Rooted42–44 supplies completed native recovery, the positive source domain, partial-prefix inverses and progress/next-mark equivalence, and resolution through the actual saved subphase/next link. Those results are reused rather than reproved.

Within this volume, §§14–18 supply the one-event source-complete head normalization and explicitly leave the interior-$F$ suffix outside their no-further-growth task. The additional `repo-derived` synthesis is the pure-left chronological synchronization on the ORIGINAL positive-progress $F$, the resulting recovery of actual entry/progress/residual without a private-stage input, and its join to the full original completion and returned consumer in §§19–22. The global returned-word distinction and the fixed-current-source normalized mixed distinction have different domains. Generic behavioral congruence, finite factorization, replay and the old shuffle inverse are suppliers, not new results attributed to this synthesis. The concrete source collision and pre-entry histories in §22 are attributed to Rooted43.6 and AA20.5; their new use is the unfinished-literal recovery and interior-$F$ continuation correspondence.

AAII47–52 and 75–80 already supply installed alternate local/global rank layouts and their paid consumers. No such layout, rank bank, replacement journal, free cursor or alternative return protocol is substituted here. NativeLocalSourceExecution's `oldFrontier`, `replay` and `native_execution` supply guarded syntax/replay and event counting; NativeCompletedHistoryRecovery's `recover` and `completed_history_recovery` supply its stated completed syntax inverse with the $n_0>1$ and beta qualifications. Neither module certifies unfinished physical records, private access, original scheduling or this append. These are ordinary conditional mathematical proofs, with no new Lean certification, digestion/freezing claim or worldwide novelty claim. The ranked-tree, marked-inverse and retained-history background cited in Rooted42.10/43.10 remains in its stated scope; no general recognizability theorem is imported as the missing source-specific synchronization.

Positive source progress and active $F$ remain declared domain premises for the displayed recovery statement. At zero progress the current $F$ has contributed no synchronizing event, so (19.3) cannot identify its admission. Rooted42.7's returned $G$ versus first-row-$F$ equality still prevents content from certifying command identity or outer completion. Arbitrary orderings of OLD rows, interleaved growth, newly born rows, several accepted unfinished events, incomplete source/header templates, changed link order, crashes, interruption, revocation and observable exhaustion are outside the hypotheses. Normalized content cannot recover a pending tail, arithmetic write cursor, exact next protocol instruction, full controller chronology or private bytes. Current geometry alone still does not determine primitive order or interior progress, and final returned memory alone does not recover a selected earlier geometry. No reset, interrupt, graft, physical inverse, new Busy query, source oracle, owner change or external private collector follows. Mutual recovery for the larger space/time/boundary/memory programme remains unresolved outside these explicitly conditioned actual images.

## 追加锚（本行以下为增补区）
