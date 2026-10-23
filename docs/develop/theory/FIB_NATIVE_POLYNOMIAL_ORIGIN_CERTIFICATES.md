# Native polynomial actual-origin certificates and quantified synthesis bounds

This append-only `generic-v1` reference volume proves linear-node certificates for actual finite origins, polynomial direct semantic verification, and quantified upper bounds for explicit stationary tables and bounded native SOME-preparer synthesis. The source domain remains the entire original repeated-partner one-image fiber. The serving table and its original labeled entries remain fixed throughout each instance.

The evidence is ordinary mathematics under the stated model and supplied-service premises. This is not Lean or kernel evidence. All algorithms below are terminating mathematical specifications, with no execution used as evidence. Mathematical authorship is by Codex CLI. The inherited native classification, finite profile coverage, multiplicities, lawful acquired selector and arbitrary-program separation belong to *Finite-reader compatibility and lawful binary-code synthesis* (FCS). Literal normalization and its SAME-budget transfer belong to [*Bounded native preparer synthesis and linear literal normalization*][BPS] (BPS). Their upstream native ownership is retained in §12. The additional content is selected-vector witness-list sharing, explicit certificate bounds, the joint two-origin equality-matrix extension, and their complexity consequences. No literature-wide priority claim is made.

## 1. Finite ordered terms and the entire actual domain

**Definition 1.1 (native terms and truthful replies).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,\qquad
\rho\beta=E:=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\end{aligned}
\tag{POC.1}
$$

These are ordinary finite nonempty ordered trees. Equality retains both leaf labels, brackets and order. Native true/false denote alpha/beta and false/true address letters denote $L/R$; the exported bits $0,1$ keep their separate original labels. Every word in $\mathcal W=\{L,R\}^{*}$, including $\varepsilon$, is legal. The reply $r_t(w)$ is alpha, beta or $\mathsf{branch}$ at a reached root, and $\mathsf{absent}$ if descent continues below a leaf. All nonempty continuations of a leaf are absent. At a reached occurrence $p$,

$$
r_t(pw)=r_{t|_p}(w).
\tag{POC.2}
$$

Occurrences stay distinct when their whole subtrees are equal.

**Lemma 1.2 (inherited image and inverse).** The image $\mathcal I=\rho[\mathcal T]$ has disjoint grammar and finite inverse

$$
\begin{aligned}
\mathcal I&::=\beta\mid E\mid\langle\mathcal I,\mathcal I\rangle,\\
\delta(\beta)&=\alpha,\qquad \delta(E)=\beta,\\
\delta\langle y,z\rangle&=\langle\delta y,\delta z\rangle
\quad(y,z\in\mathcal I).
\end{aligned}
\tag{POC.3}
$$

In particular $\rho$ is injective, beta is the only image leaf, and every subtree of an image is alpha or an image. Write $\mathcal B=\mathcal I\setminus\{\beta\}$ for its branch images.

Proof. These are FCS Proposition 1.4 and BPS Lemma 1.2's native image facts. Every source constructor gives the indicated image case. Alpha is never a root image, so $E$ cannot be a pair of images. The cases are therefore disjoint. Recursion decreases finite size; induction proves $\delta\rho=\mathrm{id}$ and $\rho\delta=\mathrm{id}$ on their respective domains. The subtree assertion follows from the two children of $E$ and from the pair-of-images case. For later finite representatives set

$$
B_0=\beta,\qquad B_{j+1}=\langle B_j,B_j\rangle.
\tag{POC.4}
$$

For $j\ge1$ these are distinct branch images with height $j$. The distinct trees $\langle\alpha,B_j\rangle$ are nonimage branches, since they are neither $E$ nor pairs of images. Thus both branch types used below are infinite. The inverse is a mathematical construction, not a native port. $\square$

**Definition 1.3 (complete rows and repeated partners).** For a finite prefix-free cut $C$, replace each reached cut subtree of $t$ by its addressed occurrence hole. Retain every other exterior bracket and concrete leaf and the complete equality partition of reached whole subtrees. Different blocks assert disequality. An unreached cut has its concrete strict-prefix blocking leaf in the exterior. Sort reached holes lexicographically; name each block by the zero-based position of its first member. Names are recomputed upon restriction and need not be consecutive. This defines the whole canonical row $R_C(t)$.

Fix $C=\{L,R\}^{3}$ and the perfect depth-three exterior $C_*$. The complete current row $R_*=(C_*,\pi_*)$ has six classes:

| Class | All occurrence holes | Representative $p_d$ |
| --- | --- | --- |
| $a$ | $LLL,LRL$ | $LLL$ |
| $c$ | $RLL,RRL$ | $RLL$ |
| $b_1$ | $LLR$ | $LLR$ |
| $b_2$ | $LRR$ | $LRR$ |
| $b_3$ | $RLR$ | $RLR$ |
| $b_4$ | $RRR$ | $RRR$ |

Put $D=(a,c,b_1,b_2,b_3,b_4)$ and

$$
\mathscr S(x)=\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,\langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,\langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{POC.5}
$$

The domain, current tree and target are exactly

$$
\mathcal U_*:=\{u\in\mathcal T:R_C(\rho u)=R_*\},\qquad
t_u=\rho u,\qquad F(u)=R_C(u).
\tag{POC.6}
$$

Equivalently, all six whole values $x_d$ are pairwise different, $\mathscr S(x)\in\mathcal I$, and $u=\delta(\mathscr S(x))$. Extraction at the representatives is the inverse correspondence. Both occurrences of each partner use its one whole value. All fifteen unordered whole-class disequalities are required. There is no bound or additional promise on source size, height, rank or history.

**Proposition 1.4 (all eleven actual root profiles).** The following cases are disjoint, nonempty and exhaustive. Remaining values range over every permitted finite branch image, with all whole-class disequalities retained.

| Case | Forced coordinates | All remaining coordinates | Whole target |
| --- | --- | --- | --- |
| $\Pi_1$ | $x_a=\beta,\ x_{b_1}=\alpha$ | Four distinct members of $\mathcal B$ | $R_1$ |
| $\Pi_2$ | $x_a=\beta,\ x_{b_2}=\alpha$ | Four distinct members of $\mathcal B$ | $R_2$ |
| $\Pi_3$ | $x_c=\beta,\ x_{b_3}=\alpha$ | Four distinct members of $\mathcal B$ | $R_3$ |
| $\Pi_4$ | $x_c=\beta,\ x_{b_4}=\alpha$ | Four distinct members of $\mathcal B$ | $R_4$ |
| $Z_a$ | $x_a=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_c$ | $x_c=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_{b_1}$ | $x_{b_1}=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_{b_2}$ | $x_{b_2}=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_{b_3}$ | $x_{b_3}=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_{b_4}$ | $x_{b_4}=\beta$ | Five distinct members of $\mathcal B$ | $R_0$ |
| $Z_*$ | None | Six distinct members of $\mathcal B$ | $R_0$ |

Proof. This is the classification of FCS Proposition 1.4 and BPS Proposition 1.4. The root and two depth-one pairs of $\mathscr S(x)$ have branch right children and cannot be $E$. Each depth-two block is consequently $E$ or a pair of images. An $E$ block forces its right class to alpha and its left partner to beta. Otherwise its two coordinates are images. Thus $a,c$ are images, a right class can be alpha only with its indicated beta partner, and injectivity of the six-value assignment permits at most one alpha class and at most one beta class. With an alpha, the other four values must be branch images. Without alpha, all six are images and at most one is beta. These are exactly the displayed cases. Conversely each case makes all four blocks and then $\mathscr S(x)$ images, so its finite inverse is actual. Distinct positive-height $B_j$ realize every case. These witnesses demonstrate nonemptiness; they do not restrict the domain. The targets are calculated next. $\square$

## 2. All five complete predecessor outputs

**Definition 2.1 (literal exteriors).** Write $h_p=\square_p$ and $(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. The complete rows $R_j=(C_j,\pi_j)$ have exteriors

$$
\begin{aligned}
C_0&=\left\langle
 \left\langle\langle h_{LLL},h_{LLR}\rangle,\langle h_{LRL},h_{LRR}\rangle\right\rangle,
 \left\langle\langle h_{RLL},h_{RLR}\rangle,\langle h_{RRL},h_{RRR}\rangle\right\rangle
\right\rangle,\\
C_1&=\left\langle
 \left\langle\beta,\langle h_{LRL},h_{LRR}\rangle\right\rangle,
 \left\langle\langle h_{RLL},h_{RLR}\rangle,\langle h_{RRL},h_{RRR}\rangle\right\rangle
\right\rangle,\\
C_2&=\left\langle
 \left\langle\langle h_{LLL},h_{LLR}\rangle,\beta\right\rangle,
 \left\langle\langle h_{RLL},h_{RLR}\rangle,\langle h_{RRL},h_{RRR}\rangle\right\rangle
\right\rangle,\\
C_3&=\left\langle
 \left\langle\langle h_{LLL},h_{LLR}\rangle,\langle h_{LRL},h_{LRR}\rangle\right\rangle,
 \left\langle\beta,\langle h_{RRL},h_{RRR}\rangle\right\rangle
\right\rangle,\\
C_4&=\left\langle
 \left\langle\langle h_{LLL},h_{LLR}\rangle,\langle h_{LRL},h_{LRR}\rangle\right\rangle,
 \left\langle\langle h_{RLL},h_{RLR}\rangle,\beta\right\rangle
\right\rangle.
\end{aligned}
\tag{POC.7}
$$

**Definition 2.2 (partitions, names and guards).** Their whole-subtree partitions are

$$
\begin{aligned}
\pi_0&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_1&=\{\{LRL\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_2&=\{\{LLL\},\{LLR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_3&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RRL\},\{RRR\}\},\\
\pi_4&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL\},\{RLR\}\}.
\end{aligned}
\tag{POC.8}
$$

Every two different blocks assert disequality. The following data are also part of each entire output:

| Row | Ordered reached holes | First-member name vector | All absent cuts and concrete guard |
| --- | --- | --- | --- |
| $R_0=R_*$ | $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,0,3,4,5,4,7)$ | None |
| $R_1$ | $LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LLL,LLR$; beta at $LL$ |
| $R_2$ | $LLL,LLR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LRL,LRR$; beta at $LR$ |
| $R_3$ | $LLL,LLR,LRL,LRR,RRL,RRR$ | $(0,1,0,3,4,5)$ | $RLL,RLR$; beta at $RL$ |
| $R_4$ | $LLL,LLR,LRL,LRR,RLL,RLR$ | $(0,1,0,3,4,5)$ | $RRL,RRR$; beta at $RR$ |

**Proposition 2.3 (inherited whole-target calculation).** On $\Pi_j$, $F(u)=R_j$; on all seven zero cases, $F(u)=R_0$. The five rows are distinct and attained.

Proof. This is FCS Proposition 2.2 and BPS Proposition 2.3. In a zero case all four depth-two blocks are pairs of images; their inverses retain their old pairs and all eight cut holes. On $\Pi_j$ precisely block $q_j$ is $E$ and inverses to the concrete beta leaf, so precisely its two children were absent before the update. The partner's other occurrence remains an old hole. The other three blocks retain their pairs and holes. Injectivity of $\rho$ preserves equality and disequality of all surviving whole values. Restricting the occurrence partition and recomputing first-hole names gives exactly (POC.8) and the table. The beta at $q_j$ is the guard for both blocked cuts. Different reached supports distinguish all five rows, and Proposition 1.4 supplies each one. $\square$

## 3. Explicit apparatus, supplied services and binary encoding

**Assumption 3.1 (actual register and service boundary).** Exactly one genuine authenticated update binds actual $u$ to the same register $t_u=\rho u$. Its origin, root, cut and version are fixed. There are no resets, rerootings, source substitutions, copies of the source register, arbitrary edits or subsequent updates. Authentication certifies continuity and selects no source within $\mathcal U_*$. The complete current row is lawfully acquired.

Native preparation is separately permitted to query that stationary register before the access cut. Acquired trees, class values, old outputs, acquisition archive and trace are inaccessible to it. Its complete bit is actually exported; a paid code-only handoff makes all preparation material inaccessible and enters exactly the original serving entry for that bit. An absorbing preparation stop supplies no resume action: serving is a separately supplied invocation. Material need not be physically erased to become inaccessible. The same truthful stationary register serves both phases.

Acquisition and representation, authentication and continuity, pre-cut permission, installation, state/literal/whole-output storage, native service, actual export, complete isolation, handoff and lawful faithful new entry are separately supplied and priced. No certificate below supplies them. Source-bearing fields other than the current counted state are denied: acquired values, predecessor data, identity, alpha marker, cache, pointer, trace, allocation, order or count of acquisition, length, meter, timing, clock, phase, history and source-dependent table selection. There is no equality, inverse, image, provenance, generation or other source port.

**Definition 3.2 (immutable explicit serving table).** The input $T$ has installed set $K_T=Q_T\sqcup H_T$, one literal $a_T(q)\in\mathcal W$ per Read, four successors $n_T(q,r)\in K_T$ for every $r\in\mathcal A:=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$, and one fixed complete row $o_T(h)$ per Halt. Distinct installed entries $e_0,e_1$ retain their original labels and faithful inverse labeling. A Read makes one actual native call at its literal and takes the successor for its truthful reply; a Halt returns its literal entire row without a call. The current state is the whole accessible mutable source-dependent memory. There is no extra code bit, independent program counter, work or reply register, computed address, output decoder or free control transition.

Every installed state counts, including unused Reads, unused Halts and different Halts with equal outputs. Every Read has all four installed successors. Repeated literals, shared states, convergence, cycles and early Halts are permitted. All records, including unused words and paths from incorrect entries, are part of the input. $T,e_0,e_1$ remain unchanged. No bound of nine states or two calls is assumed.

**Definition 3.3 (explicit preparer and two-stage property).** An explicit preparer $A$ has nonempty installed $K_A=Q_A\sqcup H_A$, one common source-independent start $s_A$, fixed literals and four successors at Reads, and original bits $o_A(h)\in\{0,1\}$ at Halts. Its current state is all its mutable memory. A Halt replaces live control by its complete bit latch; no independent live register survives. Every installed state and every actual Read visit count, including duplicates, forced replies, $\varepsilon$, absent queries and leaf continuations.

For budgets $N,P,L\in\mathbb N_0$, full success means $|K_A|\le N$, preparation halts within $P$ calls on every actual source, its generated function $\sigma_A$ attains both original bits, and the handoff to $e_{\sigma_A(u)}$ returns the entire $F(u)$ within $L$ serving calls on that same source. Only the selected entry must succeed. The other entry may return a false row, exceed $L$ or diverge. SOME synthesis chooses such a generated function without an independently prescribed pointwise code.

**Definition 3.4 (full explicit size).** Use binary arrays of numbered state records with delimited or length-prefixed fields. Each Read stores a tag, its length, every letter of its literal and all four successor indices. A preparer Halt stores its original bit; a serving Halt stores the whole canonical row. Include the common start and distinct original serving entries. Rows store the exterior with addressed holes and concrete leaves and the canonical name vector in reached-hole order; names encode the full partition, with different blocks asserting disequality. Hole addresses, support, first-member names and blocking leaves must agree with the exterior. Indices, tags, lengths and row syntax are checked. Invalid encodings are rejected.

For witness and supplied-table validation statements, $s$ is the full bit length of the explicit tables, entries and budget fields. Literal letters use one bit each, so total literal length and installed state count are at most $s$. The signature, cut and required five rows are fixed constants. Budgets $P,L$ are ordinary positional binary integers, with zero encoded as $0$; their numeric values may be enormous. For synthesis write $s_0$ for the length of explicit $T,e_0,e_1$, binary $P,L$ and unary $1^N$ with a delimiter, including an empty block for zero. Explicit table validation needs no unary count promise.

**Definition 3.5 (joint attained behavior).** For arbitrary $A$, successful or otherwise, put

$$
\mathcal J(A,T)=\left\{
\left((r_{t_u}(a_A(q)))_{q\in Q_A},
      (r_{t_u}(a_T(q)))_{q\in Q_T},F(u)\right):u\in\mathcal U_*
\right\}.
\tag{POC.9}
$$

Vectors are in installed state order and include every duplicate and unused Read. Paths, generated bit and both possible serving behaviors are deterministic consequences of this one joint element. No response vector or target certificate is available to either apparatus at runtime. With one apparatus absent, use its empty observation menu in the mathematical statements.

## 4. Exact selected-vector witness lists

**Definition 4.1 (four types, indexed trie and caps).** Partition all finite terms into

$$
\mathsf A=\{\alpha\},\quad \mathsf H=\{\beta\},\quad
\mathsf I=\mathcal B,\quad
\mathsf O=\mathcal T\setminus(\mathsf A\cup\mathsf H\cup\mathsf I).
\tag{POC.10}
$$

A pair has type $\mathsf I$ exactly for child-type pairs

$$
\mathcal C_I=\{(\mathsf H,\mathsf A),
(\mathsf H,\mathsf H),(\mathsf H,\mathsf I),
(\mathsf I,\mathsf H),(\mathsf I,\mathsf I)\}.
\tag{POC.11}
$$

Every other ordered child-type pair gives $\mathsf O$; a pair is never a leaf type. In particular $(\mathsf A,\mathsf H)$ is not an image case. For threshold $K$ let $[X]_K=\min(K,|X|)$, taking $K$ for infinite sets.

Give each installed Read of absolute length at least three its own index $i$. Decompose its word uniquely as $p_iw_i$, $|p_i|=3$, retaining apparatus/state identity, occurrence $p_i$ and role $d_i=[p_i]$. Form one prefix trie of all suffixes $w_i$ across all roles. A node carries every ending index; an unobserved child is $\#$. Duplicate words remain separate indices even at one marker. Let $m$ be the number of indices and $V$ the number of explicit trie nodes, with $V=0$ for an empty menu. If nonempty,

$$
V\le1+\sum_i|w_i|\le s+1.
\tag{POC.12}
$$

All shorter absolute words have the common exterior branch reply. A $\#$ child means unrestricted finite child trees, not an absent child of a branch.

**Lemma 4.2 (exact capped arithmetic).** Finite disjoint union and Cartesian product commute with addition and multiplication saturated at $K$. Lists retaining up to $K$ different members per factor produce exactly the capped number of different ordered pairs. Unrestricted four-type capacities are $(1,1,K,K)$.

Proof. Below $K$ a disjoint sum retains every summand exactly; at or above $K$ one can select $K$ members across the disjoint summands. A product with a zero factor is empty. If a nonzero product has size below $K$, both factors have their exact finite counts below $K$. If its size is at least $K$, either both factors are below $K$ and their retained product already has at least $K$ members, or one retained factor has $K$ different members and pairing with one member of the other suffices. This proves both capped multiplication and the list statement. Lemma 1.2 supplies $K$ different $B_1,\ldots,B_K$ and $K$ different $\langle\alpha,B_j\rangle$; leaves are singletons. No nonempty cell is rounded to $K$ merely for being nonempty. $\square$

**Lemma 4.3 (complete recurrence for a selected vector).** Fix $r\in\{1,2\}$ actual origins and put $K=6r$. For each of their $K$ whole class values record its type and replies at all $m$ suffix indices, including indices assigned to other roles. There are at most $K$ selected full response vectors. For an explicit subtrie $v$ with descendant index set $J_v$, and each restriction $z$ of a selected vector to $J_v$, lists of exactly

$$
\min\bigl(K,\,|\{y\in\mathsf t:(r_y(w))_{\text{indices below }v}=z\}|\bigr)
\tag{POC.13}
$$

different actual finite terms can be retained for every type $\mathsf t$. Relative words in this formula start at $v$. At most $4K$ lists and $4K^2$ retained witnesses are needed at a node.

Proof. At $\#$ the constraint vector is empty and use the unrestricted lists of Lemma 4.2. At an explicit node let $J_0$ be the ending indices and $J_L,J_R$ the two child index sets. The alpha leaf contributes exactly one witness if all $J_0$ requests are alpha and all strict-descendant requests are absent, and otherwise none. Beta has the identical rule with beta. A branch is possible only when all ending indices request branch. Under that condition, for each ordered child-type pair combine its two child lists for the restrictions $z|_{J_L},z|_{J_R}$. Assign the parent type by (POC.11) and retain up to $K$ different parents of each required type. Equivalently its $\mathsf I$ count is

$$
\min\left(K,\sum_{(\mathsf t,\mathsf u)\in\mathcal C_I}
f_L(\mathsf t,z|_{J_L})f_R(\mathsf u,z|_{J_R})\right),
\tag{POC.14}
$$

using capped child counts, and the $\mathsf O$ count sums over the complementary ordered pairs. Failed branch conditions give zero. Ordered-pair decomposition is unique, the child-type cases are disjoint, and Lemma 4.2 proves exact capped cardinality. Induction up the finite trie proves the list invariant and realization. Each child restriction is again the restriction of an original selected vector, so no unlisted vector is needed. Equal restrictions may share a list. There are at most $K$ restrictions per node, four types and at most $K$ witnesses per list, proving the count.

This recurrence includes empty suffixes, root markers, inconsistent duplicate requests, impossible absent replies at a root, early leaves and every absent continuation. For an all-absent strict-descendant vector a leaf is retained even if the corresponding branch-child vector has no realization. The image whose right root is alpha is only $E$, so that image cell has capacity one and remains one. Fully exposed finite pieces and every finite nonsingleton capacity below $K$ remain exact. The recorded extra-role replies are mathematical selection data, with no additional runtime observations. $\square$

## 5. Linear DAG certificates and simultaneous distinctness

**Lemma 5.1 (shared finite witness representation).** All retained lists of Lemma 4.3 can be represented together by an acyclic ordered-term DAG with at most

$$
4K^2V+2K+2
\tag{POC.15}
$$

nodes. Equality in this DAG is equality of finite unfolded ordered terms.

Proof. Store alpha and beta once. The successive $B_j=\langle B_{j-1},B_{j-1}\rangle$, $1\le j\le K$, add $K$ nodes. The $K$ nonimage witnesses $\langle\alpha,B_j\rangle$ add $K$ more. This common $\#$ basis has $2K+2$ nodes. Process explicit trie children before parents. Each retained nonleaf parent adds at most one pair node pointing to already retained child witnesses; leaves reuse their two global nodes. There are at most $4K^2$ retained parents at an explicit node. Unselected candidate pairs need not be stored. This proves (POC.15).

All pair pointers can go to earlier nodes. Recursive unfolding therefore terminates in an ordinary finite tree, duplicating repeated pointers into separate ordered occurrences. For exact equality give the two leaf tags different identifiers and intern every pair by the ordered pair of its children's canonical identifiers. Induction on the topological order proves that two identifiers agree exactly when the finite unfolded terms agree. Interning can reduce the node count and never increases it. Neither cyclic nor rational trees enter this construction. $\square$

**Lemma 5.2 (global whole-value equality-matrix lifting).** The $r$ original tuples can be replaced by tuples from the retained root lists while preserving each class value's type and selected full vector and, for every pair of coordinates among all $6r$ coordinates, the truth value of their whole-term equality.

Proof. The root cells indexed by type and full suffix-response vector partition all finite terms. In an occupied cell let $h$ count distinct original whole values, identifying equal coordinates also across origins. Their existence gives capacity at least $h$, and $h\le K$. The retained list thus has at least $h$ different members. Assign different members to different original equality classes and one member to every coordinate of the same original equality class. Repeat for each occupied cell. Different cells are disjoint, so no additional equality arises between their choices. This preserves the entire equality and disequality matrix, including all fifteen whole-class negatives inside each tuple. Both occurrences of $a$ and both occurrences of $c$ use their one chosen class root. Exact finite capacities are essential: a singleton cannot furnish two distinct equality classes. No independently attainable marginal or childwise inequality substitutes for this simultaneous selection. $\square$

**Theorem 5.3 (one-origin and joint two-origin bounds).** Every element of $\mathcal J(A,T)$ has one actual finite origin with a DAG certificate of at most $300(s+2)$ nodes, including its six class roots, current root and source root. More strongly, any two original actual origins admit simultaneous replacements preserving their respective full joint elements and the entire cross-origin whole-value equality matrix, with a joint DAG of at most $1200(s+2)$ nodes. If the original origins are distinct, the replacements are distinct, including when their two joint elements coincide.

Proof. Use Lemmas 4.3–5.2 with $r=1$ or $2$ and $K=6r$. Each new six-value tuple has the same types and whole-class disequalities as its original tuple, hence belongs to the same one of the eleven profiles. Form $\mathscr S(x')$ with the repeated partners. Proposition 1.4 gives an image and its finite actual origin $u'=\delta(\mathscr S(x'))$ in the full original domain. Proposition 2.3 gives the same complete target, including every surviving occurrence, partition relation, first-member name and guard. For every installed index project its role's preserved full vector to that index. Equation (POC.2) and the fixed occurrence prefix give its original actual reply. Restore the constant branch components for shorter words. Thus one actual source realizes the entire preparer vector, serving vector and target together.

Each current exterior uses at most seven new pair nodes, adding $7r$. Image membership is parsed bottom-up by (POC.3). Memoized inversion adds at most one pair node per visited current node; beta maps to the already available alpha and $E$ to beta. Doubling the current DAG bound, with harmless slack, yields

$$
8K^2V+4K+14r+6.
\tag{POC.16}
$$

For $r=1$ this is $288V+44\le300(V+1)\le300(s+2)$. For $r=2$ it is $1152V+82\le1200(V+1)\le1200(s+2)$. The shared basis also proves these inequalities at $V=0$.

Finally different original origins have different six-value tuples: the tuple determines its current tree and its unique inverse. At least one corresponding coordinate pair is therefore unequal. Lemma 5.2 keeps that cross-origin inequality, so the new tuples, current trees and inverse origins remain different. This works even when all installed replies and the whole target agree at the two points. The statement supplies small representatives of behaviors; it imposes no height cutoff or source-size restriction on $\mathcal U_*$. $\square$

**Corollary 5.4 (polynomial bit encoding).** For $r=1$ use $M=300(s+2)$ and for $r=2$ use $M=1200(s+2)$. Put $w=\lceil\log_2(M+1)\rceil$. Certificates can be encoded in at most

$$
(M+32)(2+2w)+4s+512
\tag{POC.17}
$$

bits, hence $O(s\log(s+2))$ bits.

Proof. Encode the active node count in $w$ bits and provide $M$ slots, each with a two-bit alpha/beta/pair/reserved tag and two $w$-bit fields. Leaves have zero fields; pair fields are nonzero indices strictly smaller than their own index. Inactive slots have the reserved tag and zero fields. Include eight active root indices per origin, the claimed vectors in two bits per reply when required, and each complete target in a fixed 128-bit padded row field. Such a row field suffices: at most fifteen exterior nodes need two-bit tags; at most eight holes need three-bit addresses; a four-bit reached-hole count and eight three-bit names use fewer than 128 bits in total. The parse is prefix ordered, so brackets and blocking leaves are retained exactly. For $r\le2$ the vectors use at most $4s$ bits, rows at most 256, and header/root/padding overhead fits the displayed slack. These are certificate fields, not installed states or runtime memory. $\square$

## 6. Polynomial direct semantic verification and binary caps

**Definition 6.1 (actual-origin semantic verifier).** The verifier first checks explicit input syntax and certificate format, size, tags, canonical padding, root ranges and strict backward pointers. It jointly interns all active DAG nodes by leaf tag and ordered canonical child identifiers. This global interning is shared across both origins when present and across all subsequently constructed terms. It then performs the following finite checks:

1. Within each origin require six pairwise different class-root identifiers. Rebuild (POC.5), using the same $a/c$ root at both occurrences, and compare it with the current root. Parse image membership by the disjoint grammar; memoize $\delta$ and compare its canonical identifier with the source root. Alpha fails the image test, beta passes, and a pair passes exactly if it is literally $E$ or both children pass. These alternatives are disjoint.
2. Compute $R_C(t)$ and require the entire $R_*$. Independently compute $R_C(u)$ from the source root: descend at the fixed cut, keep early concrete leaves and every exterior bracket, record all reached occurrence holes, compare their subtree canonical identifiers, and assign each block its first reached position. Require equality with the claimed whole target and with the eleven-profile/five-row calculation. Guards and all negative partition relations are included.
3. From that same current root follow every installed literal in both arrays, in state order. At the end return the reached constructor; any attempted continuation below a leaf returns absent. Include unused states and duplicate literals separately. Compare every reply with the claimed full vectors.
4. When distinct origins are required, compare their source canonical identifiers and require inequality. When bit or good-entry witnesses are required, perform their actual bounded paths by Lemma 6.2 on those same sources.

Different pointer numbers alone never prove disequality. Conversely repeated pointers do not merge occurrence addresses. The verifier may equivalently memoize $\rho$ on the source and compare the resulting current term as an extra consistency check; this is local certificate work, not a source port.

**Lemma 6.2 (stationary no-revisit and binary-cap path test).** Fix one current source and starting state in an explicit table with $q$ installed Reads. Every halting path has at most $q$ Read visits. Its behavior under a positional binary call cap $C$ is decidable in polynomial time in the explicit table, reply-vector and cap lengths, without looping to the numeric value of $C$.

Proof. A Read has one literal and one fixed reply on that stationary source. Reentering it repeats the identical deterministic future forever. A terminating path therefore cannot revisit a Read. This is the sourcewise stationary principle of FCS Theorem 9.1 and BPS Lemma 3.4.

Inspect a state before attempting any call. A Halt uses zero calls, whether initial or immediately after the last permitted Read. At a Read fail the cap if $C$ calls have already been used; otherwise detect a previously visited Read as divergence, or follow its fixed-reply successor and increment the actual-call count. Inspect the successor immediately, including after the $C$th call. At most $q$ distinct Reads can be processed before a Halt, repetition or cap failure. The counter needs only $O(\log(q+1))$ bits; comparison with the binary representation of $C$ is polynomial. A wrong serving Halt fails by whole-row comparison. A Read still live at the cap fails; an initial correct Halt and a correct final-call Halt succeed without another call.

Apply this first to $A$ at $s_A,P$. If it halts with original bit $z$, apply it only to the unchanged $e_z$ at $L$ on the same source. A preparation failure already suffices to fail the two-stage property. A wrong, over-cap or divergent unselected entry imposes no condition. Cycles in installed graphs or in the union of paths across different sources remain permitted. Without supplied caps, sourcewise correct termination is equivalent to using $q_A,q_T$ as the respective caps. The verifier's visited set is not runtime storage granted to either apparatus. Every actual Read still costs a call under the original contract. $\square$

**Theorem 6.3 (sound, complete polynomial verifier).** Definition 6.1, with Lemma 6.2 for required paths, verifies exactly the claimed actual-origin behaviors within the bounds of Theorem 5.3 and Corollary 5.4, in deterministic polynomial time.

Proof. Backward pointers ensure finite ordinary unfoldings. Induction for global structural interning proves exact unfolded equality. The rebuilt exterior, full current row, image parser and inverse comparison establish a genuine actual $u$ and exactly $t=\rho u$ in $\mathcal U_*$. Fixed-cut occurrence extraction establishes its entire predecessor row. Literal descent establishes every indexed reply on that very current tree. Semantic source inequality establishes genuine distinctness. Lemma 6.2 establishes any asserted bounded bit or selected-serving run. Thus every accepted certificate is sound.

Conversely Theorem 5.3 constructs certificates within the node limits for every attained element and every required pair of origins, preserving the needed behaviors, full targets and distinctness. Corollary 5.4 encodes them in the accepted format. The verifier need not carry or exhaustively verify the internal list construction: that construction proves completeness of the size bound; direct finite semantics proves soundness of an individual certificate.

Even naive interning by comparison with earlier ordered child-identifier pairs is polynomial in the slot count. Image parsing and inversion are memoized per node and add at most linearly many nodes. Cut extraction has constant depth and breadth while keeping occurrences distinct. A length-$d$ literal needs at most $d$ descents, independently of its unfolded tree size, and total literal letters are part of $s$. Whole-row syntax, canonical padding and bounded paths are polynomial checks. All counters and identifiers have polynomial bit length. Hence the complete verifier is polynomial. No full inclusive-depth profile inventory or exponential response-vector enumeration is used by this verifier. $\square$

## 7. Precise supplied-table languages and upper bounds

**Definition 7.1 (languages and DP convention).** All languages reject malformed explicit encodings. JOINT-ATTAIN takes explicit $A,T$ and a proposed full pair of state-indexed reply vectors and complete target, and asks whether one actual $u$ realizes that joint element. UNIVERSAL-TWO-STAGE takes $A,T,e_0,e_1,P,L$ and asks whether every actual source has preparation termination within $P$ and correct selected serving termination within $L$. It does not require BOTH.

BOTH-PREPARER takes explicit $A,P$ and asks for an actual within-$P$ bit-zero run and an actual within-$P$ bit-one run. It imposes no universal or serving requirement. FULL-FINITE-TABLE-VALIDATION is the conjunction of UNIVERSAL-TWO-STAGE and BOTH-PREPARER, with any explicit $|K_A|\le N$ check included. Here

$$
\mathrm{DP}:=\{X\cap Y:X\in\mathrm{NP},\ Y\in\mathrm{coNP}\}.
\tag{POC.18}
$$

This is the class of intersections of an NP language and a coNP language, not the intersection of those two complexity classes.

**Theorem 7.2 (NP, coNP and DP ceilings).** JOINT-ATTAIN and BOTH-PREPARER are in NP, UNIVERSAL-TWO-STAGE is in coNP, and FULL-FINITE-TABLE-VALIDATION is in DP. The sourcewise uncapped correct-termination variant has the same ceilings.

Proof. For JOINT-ATTAIN guess a bounded one-origin certificate and run Theorem 6.3. Its soundness gives a real source and its completeness supplies a certificate for every attained element. For BOTH guess two-origin certificates, check their preparer paths within $P$ and respective original bits, and require semantic source inequality. Completeness follows from Theorem 5.3 with an empty serving observation menu. Distinctness also follows directly because one fixed source has a single deterministic common-start output. Requiring correct selected-serving runs at these two witnesses is still NP and is equivalent to BOTH when the universal property holds.

If universal two-stage validity fails, one real source has preparation failure, or a selected-serving failure after its actual bit. This may be divergence, cap excess or a wrong whole output. The failure depends only on that source's joint element. Theorem 5.3 replaces it by a bounded actual origin preserving that whole element, and Theorem 6.3 and Lemma 6.2 recognize its failure in polynomial time. Every accepted bad-source certificate is conversely a real violation. Malformed instances are accepted by the complement with a dummy certificate after a deterministic syntax check. Thus the complement is NP and universal validity is coNP.

Taking the intersection of this coNP language with the independent NP BOTH language proves DP membership as defined in (POC.18). The polynomial state-budget check can be conjoined to either part. Short BOTH witnesses do not certify universal coverage. For uncapped sourcewise termination substitute $q_A,q_T$ by Lemma 6.2. Every statement is an upper bound; no hardness or completeness claim is involved. $\square$

## 8. Lawful acquired selectors and distinct actual points

**Definition 8.1 (the separate acquired-term problem).** In the FCS acquired-data contract a producer genuinely possesses either the full finite current tree or $R_*$ and all six same-source, same-version class terms. Local structural inspection and whole-term equality on those acquired finite terms are permitted. A lawful code is a specified total finite deterministic acquired-term computation whose complete original bit is actually exported under the isolation and faithful-entry services. Its constants, workspace and computation are producer resources without a bound here. This acquired access is unavailable to a native preparer in §3.

For explicit immutable $T,e_0,e_1$ and binary $L$, put

$$
\operatorname{Good}_z(u)\iff
T\text{ at }e_z\text{ returns the entire }F(u)\text{ within }L\text{ calls}.
\tag{POC.19}
$$

SOME-LAWFUL-ACQUIRED-CODE asks whether some lawful total code attains both bits and always selects such a good entry. No native-preparer budget or program description is an input to this separate problem.

**Lemma 8.2 (FCS finite coverage and exact multiplicities).** For the finite installed menu of $T$, there is an exactly attained finite prefix-profile partition of $\mathcal U_*$ on which both good sets and the whole target are constant. Each retained closed profile has exactly one actual point; each retained live profile has countably infinitely many actual points.

Proof. This is FCS Propositions 4.3, 5.2 and Theorem 4.4; the needed mathematical ingredients are as follows. Let

$$
b=\max\bigl(\{0\}\cup\{|a_T(q)|-3:q\in Q_T,\ |a_T(q)|\ge3\}\bigr).
\tag{POC.20}
$$

Expose each class through inclusive relative depth $b$, stopping at early literal alpha/beta leaves with their absent cones. At a frontier branch place a live name filled only by a finite branch image. Different names are independent; the same whole partner pattern and its names recur at both partner occurrences. For the six resulting free terms $A_d$, retain the entire list $A_d\ne A_e$, $d\ne e$. The structural image predicate has alpha false, beta and names true, and a pair true exactly when it is literally $E$ or both children pass. It is exact under all branch-image fillings: a name cannot become a leaf, so it cannot create a new literal-$E$ alternative. Retain profiles passing this predicate on $\mathscr S(A)$ and whose different class terms have different free syntax.

To prove simultaneous attainment, let $h\ge1$ bound the free-term heights, treating names as leaves, and assign distinct names $z_i$ to $B_{N_i}$ with every $N_i>h$ and successive gaps greater than $h$. At a first syntactic mismatch different concrete constructors remain different and different names have different heights. A name against a ground term has height greater than $h$. Against a nonvariable term containing names, let $N_j$ be the largest assigned height present. If $N_j<N_i$, the evaluated subterm has height at most $\max(h,N_j+h)<N_i$; if $N_j>N_i$, it has height greater than $N_i$; if $N_j=N_i$, the name occurs at positive depth and again gives greater height. Thus every nontrivial whole-term negative holds simultaneously. The image test and inverse give one actual origin of precisely that exposed profile. With no live names, unequal free syntax is already unequal ground syntax. Conversely every actual origin exposes a unique passing profile; identical free class terms could not yield its required distinct values. This proves exact finite coverage, with no missing source.

A closed profile fixes the whole tuple and its unique inverse, hence is singleton. In a live profile increase every $N_i$ by $k\ge0$. Separation gaps and the exposed prefix remain fixed, and a chosen live occurrence has strictly increasing inserted height. The resulting tuples and inverse origins are all different. Finite terms are countable, so the cell is countably infinite. All installed literal replies are fixed by the prefix and short common exterior; class-root types fix the whole target. Lemma 6.2 consequently fixes each good set. This includes unused serving words in $b$ and leaves finite/closed pieces literal. $\square$

**Theorem 8.3 (reused lawful selector bridge and its DP consequence).** SOME-LAWFUL-ACQUIRED-CODE is equivalent to the conjunction

$$
\begin{aligned}
\mathrm{Coverage}:&\quad\forall u\in\mathcal U_*,\
\operatorname{Good}_0(u)\lor\operatorname{Good}_1(u),\\
\mathrm{DistinctPair}:&\quad\exists u_0,u_1\in\mathcal U_*,\
u_0\ne u_1\ \land\operatorname{Good}_0(u_0)\land\operatorname{Good}_1(u_1).
\end{aligned}
\tag{POC.21}
$$

It is in DP with $T$ part of the explicit input, and hence also for a literally fixed $T$.

Proof. The equivalence is the distinct-point form of FCS Theorem 6.1. Necessity follows by choosing one source from each of a both-attained deterministic code's two fibers; they are different. For sufficiency Lemma 8.2 supplies a finite exact profile partition. Coverage permits a fixed good default for each profile. Store the two actual finite current tuples $X^0,X^1$ from DistinctPair and define the acquired-term code

$$
\widehat\sigma(x)=
\begin{cases}
0,&x=X^0,\\
1,&x=X^1,\\
\min G_{\eta(x)},&\text{otherwise},
\end{cases}
\tag{POC.22}
$$

where $G_\eta$ is the nonempty good set of the exposed profile. Finite structural equality of entire acquired tuples, prefix extraction and finite lookup terminate. A representation check with fixed fallback makes the program total on malformed finite data as well. The tuple uniquely determines its origin, so the exceptions are disjoint and give exactly the intended two distinct actual witnesses. Defaults and exceptions all choose good entries. Actual export and entry are supplied services. This is a lawful acquired computation without a claim of bounded native generation or a small producer program. A singleton profile remains one point: if both witness profiles coincide, that cell must contain at least two points, and Lemma 8.2 excludes its being closed.

The new complexity consequence separates the two clauses. A failure of Coverage has a one-origin polynomial certificate on which both entries fail, recognized by Theorem 6.3 and Lemma 6.2, so Coverage is coNP. DistinctPair is NP: Theorem 5.3's cap-twelve construction preserves the entire equality matrix and genuine source inequality along with the two good behaviors, even inside one common behavior cell. Its joint semantic verifier checks both good runs and inequality. Their conjunction is DP. The finite lawful bridge is reused; this DP ceiling is its certificate-size consequence. $\square$

## 9. The exact BPS normalization used by synthesis

**Lemma 9.1 (canonical literal-only normalization, reused).** Let $q_T=|Q_T|$, let $b$ be (POC.20), and let $A$ be any explicit preparer with at most $N$ total installed states. BPS Theorems 8.3 and 9.1 supply a preparer $A'$ with exactly the old installed states, Read/Halt partition, common start, four successors and original Halt bits, replacing only literals, such that

$$
\begin{gathered}
\mathcal J(A',T)=\mathcal J(A,T),\qquad
|a_{A'}(q)|\le|a_A(q)|,\\
|a_{A'}(q)|\le D_0:=3+b+6(q_T+N)\quad(q\in Q_A).
\end{gathered}
\tag{POC.23}
$$

Every serving record and both original entries remain literally identical. Full success, including BOTH, transfers at the same $N,P,L$. The conclusion preserves attained sets and does not assert pointwise equality of the generated bit on an identical source.

Justification of the reused parameters and bridge. BPS uses the common trie of Definition 4.1 with a separate index for every installed long Read and cap six over all requested vectors. Its exact recurrence is (POC.14), including the leaf conditions. For an unmarked unary node with observed-child counts $(a,h,i,o)$, let $e$ indicate the all-absent requested vector, $S$ indicate $a+h+i+o>0$, and $G$ indicate $h+i>0$. Its two oriented actions are

$$
U_L=(e,e,6\mathbf1_G,6\mathbf1_S),\qquad
U_R=(e,e,\min(6,a+6\mathbf1_G),6\mathbf1_S).
\tag{POC.24}
$$

The right action retains the singleton-$E$ contribution $a$. Root leaves give $e,e$ even for an unrealizable child vector. With $e=0$, after the bottom two unary nodes both leaf counts vanish and the branch counts are fixed under either further action; the image count is six exactly when $G$ held initially or the bottom node was right-oriented with $a>0$. The nonimage count is six exactly when $S$ held. With $e=1$, the first node gives both leaves and the second gives $(1,1,6,6)$, also fixed. These are BPS Lemmas 6.1–6.3, not new normalization results here.

BPS pins every explicit trie node at depth at most $b$, keeping all serving words fixed, and contracts every longer below-pin unary run to its bottom two nodes with incoming and retained orientations unchanged. With $m$ indices there are at most $m$ marked nodes and $m-1$ binary nodes, because every trie leaf is marked and binary nodes equal leaves minus one. An endpoint tail has at most $2m-1$ essential nodes and at most twice as many unary nodes, giving depth at most $b+6m$. Here $m\le q_T+|Q_A|\le q_T+N$, including unused and duplicate records. Short preparer words may become $\varepsilon$ with the same branch reply and one paid call. This gives exactly $D_0$.

Equal capped full-cell capacities select six different whole values simultaneously, with one actual inverse origin for the entire joint triple, in either direction. Consequently on any new actual source one old actual joint witness has the same preparer path, bit, selected serving path, whole target and call counts. The reverse inclusion transfers witnesses for each original bit. State counts are unchanged. These are the actual-source and SAME-budget arguments of BPS Lemma 8.2 and Theorem 9.1; no new runtime operation or independently prescribed program is preserved by assertion. The $m=0$ case consists only of constant branch observations and is included. $\square$

## 10. Unary-state-budget SOME synthesis and constructive ceilings

**Definition 10.1 (bounded synthesis language).** SOME-PREPARER-UNARY-N takes explicit $T,e_0,e_1$, unary $N$ and binary $P,L$. It asks whether any nonempty finite installed native preparer, initially with arbitrary finite literal lengths, satisfies Definition 3.3 at those original upper budgets. It includes both universal two-stage validity and actual BOTH attainment. Serving resources and all services remain those of §3.

**Lemma 10.2 (polynomial complete candidate encoding).** For $N\ge1$, every successful arbitrary-literal preparer has a successful normalized description of polynomial length in $s_0$, with the same budgets and serving table. Put

$$
\begin{aligned}
w_N&=\lceil\log_2(N+1)\rceil,\qquad
w_D=\lceil\log_2(D_0+1)\rceil,\\
B&=2w_N+N(2+D_0+w_D+4w_N).
\end{aligned}
\tag{POC.25}
$$

A complete candidate fits $B$ bits.

Proof. Encode the installed count $n$ and start in the first two fields. Provide $N$ slots with a Read/Halt tag, Halt-bit field, literal-length field, $D_0$ padded letter slots and four successor fields. Require $1\le n\le N$, valid indices among the installed $n$ states, literal lengths at most $D_0$, canonical unused fields at Halts and zero padding outside the installed array and after each literal. Padding is syntax, not an installed state, port or extra field available to runtime. The first $n$ records contain every installed state, including unused or duplicate ones. Every bounded explicit candidate has this encoding after relabeling. Lemma 9.1 places a successful arbitrary-address preparer in it without changing any required budget or original bit label.

Since $N$ is unary, $N,q_T,b\le s_0$, and $D_0\le3+13s_0$. Thus $B$ is polynomial in $s_0$. Numeric values of $P,L$ never enter this bound. Reject $N=0$ directly. The combined candidate/serving explicit size, and hence all bounds from §5, are uniformly polynomial in $s_0$. $\square$

**Theorem 10.3 (exact existential/universal upper bound).** SOME-PREPARER-UNARY-N is in $\Sigma_2^P$.

Proof. Choose a fixed polynomial padding bound for every candidate of Lemma 10.2 and its certificates from Corollary 5.4. Let existential string $x$ contain a $B$-bit candidate and genuine bounded actual-origin certificates for its bit-zero and bit-one runs within $P$. The joint cap-twelve verifier may check their distinctness explicitly. Let universal string $y$ range over all one-origin certificate strings padded to the fixed polynomial bound. A header includes every shorter active certificate; malformed padding is rejected by the certificate parser.

Define the deterministic polynomial predicate

$$
\begin{aligned}
R(I,x,y)={}&\operatorname{ValidCandidate}(I,x)
\land\operatorname{GenuineBothWitnesses}(I,x)\\
&\land\bigl(\neg\operatorname{ValidActualSource}(I,x,y)
\lor\operatorname{CorrectSelectedTwoStageRun}(I,x,y)\bigr).
\end{aligned}
\tag{POC.26}
$$

Here valid actual-source certificates undergo all semantic checks of §6, including full current and target rows and indexed replies; their paths may succeed or fail. Invalid candidate or bit witnesses make $R$ false for every $y$. Invalid source strings impose no condition. Polynomiality follows from Theorem 6.3 and the binary-cap lemma, with the combined explicit size bounded by Lemma 10.2.

If $\forall y\,R(I,x,y)$ holds, the existential witnesses establish BOTH. Any real counterexample to the candidate's universal property has a short actual-origin certificate preserving its full joint failure by Theorem 5.3. That valid $y$ would falsify $R$. There is consequently no such counterexample, and the installed candidate meets the full original contract. Conversely if the candidate is universally valid, every valid $y$ denotes an actual source and its selected two-stage run succeeds; all invalid $y$ are harmless. Theorem 5.3 supplies the two existential bit witnesses whenever BOTH holds.

Finally any arbitrary-literal successful preparer normalizes by Lemma 9.1 at the SAME $N,P,L$ to a candidate of Lemma 10.2, retaining both original bits and the immutable serving table. Hence

$$
I\in\text{SOME-PREPARER-UNARY-N}
\quad\Longleftrightarrow\quad
\exists x\in\{0,1\}^{\operatorname{poly}(s_0)}\
\forall y\in\{0,1\}^{\operatorname{poly}(s_0)}\ R(I,x,y).
\tag{POC.27}
$$

This is the defining upper bound for $\Sigma_2^P$. It decides the original existence question, not an assumed finite-menu relaxation. Universal coverage and existential BOTH remain separate requirements inside the displayed predicate. $\square$

**Theorem 10.4 (constructive oracle and enumeration ceilings).** Returning a successful preparer description, or a no-solution outcome, is in $\mathrm{FP}^{\Sigma_2^P}$ for unary $N$. A direct unexecuted specification also uses deterministic time $2^{\operatorname{poly}(s_0)}$ and polynomial working space. If $N$ is binary, this argument supplies an alternating exponential-time upper bound with one existential-to-universal alternation, with no polynomial-hierarchy bound asserted for that encoding.

Proof. For unary $N$, first query existence. If positive, ask whether a successful $B$-bit candidate extends the current prefix followed by zero. This prefix-extension language has exactly the existential/universal expression of Theorem 10.3 with an additional polynomial prefix test on the candidate. Choose zero when possible, otherwise one; the invariant that some successful candidate extends the prefix ensures the alternative exists. After $B$ polynomially many polynomial-length queries the complete candidate is fixed. A negative first query supplies no solution. This proves the function-oracle ceiling. If certificates as well as the preparer are desired, constrain prefixes of the full existential string instead; it has the same polynomial bound and prefix predicate.

Alternatively enumerate all fixed-length $x$ and, for each, all fixed-length $y$ of (POC.27), evaluating the polynomial predicate. The product of their two exponential counts is $2^{\operatorname{poly}(s_0)}$. Store only the strings, counters and polynomial predicate workspace; this is polynomial working space and yields a candidate whenever one exists. This is a specification derived from the bounded quantifier lengths, not executed evidence or a claim about a previous exhaustive profile inventory's efficiency.

With binary $N$, its numeric value is at most $2^{s_0}$. The same $D_0$, $B$, combined explicit input, source certificates and predicate work are bounded by $2^{\operatorname{poly}(s_0)}$. Guess an existential block of that exponential length, then universally branch over the exponential-length source block and check in exponential time. This gives the stated one-alternation exponential ceiling. It does not make the candidate polynomial in the binary input or establish the unary theorem for binary $N$.

If the preparer graph, partition, common start and Halt labels are prescribed explicitly, the graph itself bounds the installed state count by its input length. Lemma 9.1 preserves exactly those data. Guess only its bounded literals and apply the same $\Sigma_2^P$ and oracle reasoning relative to the full explicit input, even if a redundant numeric state cap is binary. No arbitrary program-to-table extraction is performed. $\square$

## 11. Arbitrary-program separation and degenerate cases

**Proposition 11.1 (inherited promised-program obstruction).** The preceding bounds do not decide compatibility of an independently supplied acquired-term program. FCS Theorem 10.2 gives undecidability even when that program is promised total, BOTH-attained and finitely natively preparable, with one fixed eight-state serving table and $L=2$.

Proof of the reused separation. Install Reads $D_1,D_2,D_3$ and whole-row Halts $H_0,\ldots,H_4$, with $o(H_j)=R_j$, and use $e_0=D_1,e_1=D_3$:

| Read | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D_1$ | $LLR$ | $H_1$ | $H_0$ | $D_2$ | $H_0$ |
| $D_2$ | $LRR$ | $H_2$ | $H_0$ | $H_0$ | $H_0$ |
| $D_3$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

The baseline bit is one on $\Pi_3\cup\Pi_4$ and zero elsewhere. The table returns the required five entire rows within two calls for those selections. Given a finite deterministic machine description $e$, modify only $\Pi_1$: output one exactly if $e$ halts within $h(x_c)$ stages. Stage one includes the initial-Halt check, so any first halt stage $\tau$ is at least one. Height recursion on acquired finite terms and bounded simulation terminate. The program is total, with a fallback for malformed acquired input. Fixed $\Pi_2$ and $\Pi_3$ points supply bits zero and one for every $e$.

If $e$ never halts, this is the compatible baseline. If it first halts at $\tau$, take

$$
x_a=\beta,\quad x_{b_1}=\alpha,\quad
x_c=B_\tau,\quad x_{b_2}=B_{\tau+1},\quad
x_{b_3}=B_{\tau+2},\quad x_{b_4}=B_{\tau+3}.
\tag{POC.28}
$$

This injective $\Pi_1$ filling has its actual finite inverse. The code outputs one, but $e_1$ sees branch at $b_3$ and returns whole $R_4$ instead of $R_1$. Compatibility is therefore equivalent to nonhalting of $e$.

Every program in the family also has a finite native determining menu, by cases. The six class roots suffice in the nonhalting case. In the halting case add all $p_cw$ with $|w|=\tau$: a finite tree has height at least $\tau$ exactly if some node at that depth is nonabsent. A finite fixed-literal prefix/latch graph generates any function determined by a finite menu: each attained reply prefix is a counted state querying the next literal, each complete attained prefix enters its determined original bit latch, and unattained transitions enter a fixed existing latch. All four successors are installed; calls, prefix states, latch and paid handoff are counted or separately supplied. This proves existence of a finite preparer without uniformly choosing between the two cases or extracting $\tau$, its menu or its preparer from $e$. A promised-program compatibility decider would decide halting by complementing its answer. This is the FCS obstruction, not a new hardness result for the finite-table languages. $\square$

**Proposition 11.2 (zero budgets and constant observations).** Full native BOTH success requires $N\ge3$, $P\ge1$, $L\ge1$. If all installed preparer observations have length less than three, a halting preparation has constant output. Normalization and certificate statements still include unsuccessful graphs and empty menus.

Proof. $N=0$ provides no nonempty state set or common start. BOTH needs two different bit Halts. A common initial Halt is constant, so source-dependent choice also requires a Read and a positive call budget. Thus $N<3$ or $P=0$ cannot succeed. With $L=0$, only selected initial serving Halts can succeed. Two fixed entries provide at most two fixed whole rows, whereas all five are attained, so universal success is impossible. Short preparer observations all return branch and hence give a single deterministic source-independent path; any resulting bit is constant. Empty menus, no Reads, relative empty suffixes and repeated root markers are already covered by the list and normalization definitions. $\square$

**Convention 11.3 (unchanged execution and evidence boundaries).** A source DAG certifies an ordinary finite term; its unfolding can be exponentially larger than its encoding. Shared pointers do not remove occurrence holes or impose rational-tree semantics. Local interning, inverse parsing and literal following in a verifier are not native runtime facilities. There is no source-height cutoff, polynomial native-memory compression theorem or polynomial ordinary native-runtime conclusion.

Unused and duplicate installed states remain counted and indexed, and every actual invocation remains paid. Graph cycles fail only when a fixed-source selected path repeats a Read or otherwise exceeds its cap; cycles in unselected paths are allowed. Any false exterior, guard, canonical name or equality partition is a wrong whole output even if an informal target label agrees. Initial Halts and final-call Halts are checked without an extra probe.

SOME normalization preserves attained joint sets and SAME upper budgets, not a separately prescribed bit program at each source. Acquired selector constants and workspace, current row and term acquisition/representation, authentication and version continuity, installation and literal/whole-output storage, local transitions, actual export, isolation, latch/handoff/service storage, faithful new entry, stationary truthful native service, physical time and energy all retain their separate permissions and prices. Zero fresh native calls in a local acquired computation do not make acquisition free. A certificate gives no acquired-source port to preparation and no certificate-to-runtime transfer.

## 12. Attribution, additional content and limits

**Attribution 12.1 (canonical ownership).** The source correspondence used here is as follows:

| Canonical owner | Exact use |
| --- | --- |
| FCS §§1–3 and §5; BPS §§1–3 | Original finite ordered algebra, full actual inverse fiber, six whole distinct classes with repeated partners, eleven actual profiles, five complete occurrence-sensitive outputs, explicit immutable serving apparatus and source/service contracts. Their native upstream ownership is NBP, *Native cut-birth provenance and literal past-row recovery*, and PCA, *Native prescribed-code acquisition on the original one-image fiber*, as specified by those canonical volumes. |
| FCS §§4–6 and §9 | Exact finite profile coverage, singleton/countably infinite multiplicities, lawful acquired default-and-whole-tuple-exceptions selector, distinct actual points and stationary no-revisit. Section 8 exposes the needed coverage and lawfulness ingredients; it does not claim a new selector theorem. |
| BPS §§4–10, especially Lemma 8.2 and Theorems 8.3, 9.1 | Common indexed trie, four-type capped recurrence, finite representatives, oriented unary stabilization, pinned linear literal-depth bound, exact bidirectional joint-source realization and SAME-budget native SOME transfer. Section 9 applies that normalization with its original parameters and immutable serving table. |
| FCS §10 and §§11–12; BPS §§11–12 | Arbitrary promised-program compatibility obstruction; separation between acquired computation, native generation, prescribed pointwise code, determining certificates and explicit finite tables; paid realization limits. The direct reduction in §11 is inherited. |

The sources cited as NBP/PCA supply attribution through FCS/BPS; no additional theorem outside the stated supplied ingredients is needed for the proofs here. Their prescribed-code non-generation and non-extraction results are not superseded by SOME synthesis. In particular no finite configuration space, literal menu or correct determining assignment is extracted from arbitrary program text with computed addresses or hidden workspace.

**Attribution 12.2 (repo-derived additional deductions).** Witness retention itself is already present in BPS. The additional step in §§4–5 retains lists only for the at most six or twelve selected full response vectors and their restrictions and shares one pair node per retained parent. It proves the explicit $300(s+2)$ and $1200(s+2)$ node bounds and $O(s\log(s+2))$ bit bounds. The two-origin construction preserves every cross-origin equality and disequality, yielding genuine distinct witnesses even in a common behavior cell. Section 6 gives direct polynomial semantic verification; §§7–8 derive the NP/coNP/DP ceilings; §10 combines these bounds with canonical BPS normalization to prove the unary-$N$ $\Sigma_2^P$ and $\mathrm{FP}^{\Sigma_2^P}$ ceilings, their exact quantified predicates and the separate binary-$N$ ceiling.

Finite free term algebras, disjoint type analysis, saturated finite counting, acyclic structural interning, stationary deterministic paths, the Boolean-hierarchy definition of DP and the bounded-quantifier definitions of complexity classes are mature methods. These deductions are `repo-derived` ordinary proofs relative to the stated sources and premises. No external literature survey or worldwide originality assertion is part of that designation.

**Convention 12.3 (exact claim scope).** All class claims are upper bounds. No optimal constant, NP/coNP/DP/$\Sigma_2^P$ hardness or completeness, sharp Boolean-hierarchy classification, polynomial-hierarchy collapse, binary-$N$ polynomial-hierarchy ceiling or polynomial-size arbitrary acquired-code program is established. The oracle ceiling is not polynomial unrelativized runtime. These are neither executed verifier/synthesis results nor empirical machine-learning, physical implementation or broader-programme-completion claims. The supplied acquisition, authentication, installation, isolation, handoff and service premises remain conditions of every operational consequence.

[BPS]: FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md

## 追加锚（本行以下为增补区）
