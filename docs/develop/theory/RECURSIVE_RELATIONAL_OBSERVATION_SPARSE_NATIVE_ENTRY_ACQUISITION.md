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
