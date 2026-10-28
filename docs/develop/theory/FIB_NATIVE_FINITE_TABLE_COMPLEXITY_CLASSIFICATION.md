# Native finite-table complexity classification

This append-only `generic-v1` reference volume gives exact complexity classifications for explicit stationary native tables on the entire finite repeated-partner inverse fiber. It supplies a polynomial joint-attainment algorithm, actual-origin Boolean realizations and full native completeness reductions. Its fixed eight-state validation slice, separately specified fixed ten-state validation slice, variable-table acquired-selector problem and literally fixed acquired-selector problem have different inputs and conclusions.

Mathematical authorship is by Codex CLI. The native model and upstream ownership, capped counting and DAG methods, semantic certificate bounds, selector bridge, stationary path principle and synthesis ceilings belong to the supplied FCS, BPS and POC sources identified in §12. The role-specific matching construction and explicit native reductions supply the additional deductions. These are ordinary mathematical proofs and algorithm specifications, without Lean/kernel verification, implemented-algorithm evidence or an external priority claim. Existing text is retained; subsequent corrections and extensions belong after the final append anchor.

## 1. Finite terms, truthful queries and the whole actual domain

**Definition 1.1 (ordered terms and update).** Let

$$
\mathcal T::=\alpha\mid\beta\mid[t,t'],\qquad
\rho(\alpha)=\beta,\quad \rho(\beta)=E:=[\beta,\alpha],\quad
\rho([t,t'])=[\rho(t),\rho(t')].
\tag{FTC.1}
$$

Terms are ordinary finite nonempty ordered trees. Equality preserves leaf labels, brackets and order. Native true/false name alpha/beta, and false/true address letters name $L/R$; these conventions do not relabel the exported bits $0,1$. Every word of $\mathcal W=\{L,R\}^{*}$, including $\varepsilon$, is legal. The truthful reply $r_t(w)$ is alpha, beta or $\mathsf{branch}$ at a reached root, and $\mathsf{absent}$ when descent continues below a leaf. In particular every nonempty continuation of a leaf is absent. If occurrence $p$ is reached, then

$$
r_t(pw)=r_{t|_p}(w).
\tag{FTC.2}
$$

Equal whole subtrees at different addresses remain different occurrences.

**Lemma 1.2 (reused image inverse).** The image $\mathcal I=\rho[\mathcal T]$ has disjoint grammar

$$
\mathcal I::=\beta\mid E\mid[\mathcal I,\mathcal I],\qquad
\delta(\beta)=\alpha,\quad \delta(E)=\beta,\quad
\delta([y,z])=[\delta(y),\delta(z)]\quad(y,z\in\mathcal I).
\tag{FTC.3}
$$

Both inverse identities hold, so $\rho$ is injective. Beta is the only image leaf; every subtree of an image is alpha or an image, and every branch subtree is an image.

Proof. Each source constructor gives the indicated image case, and each displayed image case has the indicated preimage. Alpha is not a root image, so $E$ is not a pair of images. Thus the cases are disjoint. The inverse recursion decreases finite size. Structural induction proves $\delta\rho=\mathrm{id}$ and $\rho\delta=\mathrm{id}$ on their respective domains. The subtree assertion follows from the children of $E$ and the image-pair case. These are the inherited native image facts of FCS §1, BPS §1 and POC §1. For later witnesses put

$$
B_0=\beta,\qquad B_{j+1}=[B_j,B_j].
\tag{FTC.4}
$$

For $j\ge1$, $B_j$ is a branch image of height $j$; the different heights distinguish these terms. The terms $[\alpha,B_j]$ are different nonimage branches: neither the literal $E$ nor pairs of images. Hence both branch types are infinite. The inverse is a mathematical witness construction, not a native port. $\square$

**Definition 1.3 (entire canonical row).** For a finite prefix-free cut $C$, replace every reached cut subtree by its addressed occurrence hole, retaining every exterior bracket and concrete leaf. Retain the complete partition of reached holes by equality of their whole subtrees. Different blocks assert whole-subtree disequality. A blocked cut retains its concrete strict-prefix blocking leaf in the exterior. Sort reached holes lexicographically; give each block the zero-based position of its first member as its canonical name. Restriction recomputes names, which need not be consecutive. The exterior, ordered support, partition, name vector and blocking guards together form the entire row $R_C(t)$.

Fix $C=\{L,R\}^{3}$ and the perfect depth-three exterior. The current row $R_*$ has the following six classes, ordered as $D=(a,c,b_1,b_2,b_3,b_4)$.

| Class | All occurrence holes | Representative $p_d$ |
| --- | --- | --- |
| $a$ | $LLL,LRL$ | $LLL$ |
| $c$ | $RLL,RRL$ | $RLL$ |
| $b_1$ | $LLR$ | $LLR$ |
| $b_2$ | $LRR$ | $LRR$ |
| $b_3$ | $RLR$ | $RLR$ |
| $b_4$ | $RRR$ | $RRR$ |

For a six-value tuple write

$$
\mathscr S(x)=
\bigl[\,[[x_a,x_{b_1}],[x_a,x_{b_2}]],
           [[x_c,x_{b_3}],[x_c,x_{b_4}]]\,\bigr].
\tag{FTC.5}
$$

The domain, current tree and required output are exactly

$$
\mathcal U_*:=\{u\in\mathcal T:R_C(\rho u)=R_*\},\qquad
 t_u=\rho u,\qquad F(u)=R_C(u).
\tag{FTC.6}
$$

Equivalently, choose any six pairwise different whole finite terms with $\mathscr S(x)\in\mathcal I$ and take $u=\delta(\mathscr S(x))$. Extraction at the six representatives reverses this correspondence. All fifteen whole-class disequalities are required; one value fills both $a$ occurrences and one value fills both $c$ occurrences. There is no source-size, height, rank, history or selected-family restriction.

**Proposition 1.4 (all eleven actual profiles, reused).** Put $\mathcal B=\mathcal I\setminus\{\beta\}$. Exactly the following disjoint cases occur. In each row all six whole values are different; the unspecified coordinates range over every permitted member of $\mathcal B$.

| Profile | Forced coordinates | Remaining coordinates | Whole target |
| --- | --- | --- | --- |
| $\Pi_1$ | $x_a=\beta,\ x_{b_1}=\alpha$ | Four branch images | $R_1$ |
| $\Pi_2$ | $x_a=\beta,\ x_{b_2}=\alpha$ | Four branch images | $R_2$ |
| $\Pi_3$ | $x_c=\beta,\ x_{b_3}=\alpha$ | Four branch images | $R_3$ |
| $\Pi_4$ | $x_c=\beta,\ x_{b_4}=\alpha$ | Four branch images | $R_4$ |
| $Z_a$ | $x_a=\beta$ | Five branch images | $R_0$ |
| $Z_c$ | $x_c=\beta$ | Five branch images | $R_0$ |
| $Z_{b_1}$ | $x_{b_1}=\beta$ | Five branch images | $R_0$ |
| $Z_{b_2}$ | $x_{b_2}=\beta$ | Five branch images | $R_0$ |
| $Z_{b_3}$ | $x_{b_3}=\beta$ | Five branch images | $R_0$ |
| $Z_{b_4}$ | $x_{b_4}=\beta$ | Five branch images | $R_0$ |
| $Z_*$ | None | Six branch images | $R_0$ |

Proof. The root and depth-one blocks of $\mathscr S(x)$ have branch right children and cannot be $E$. Image membership therefore forces each depth-two block to be $E$ or a pair of images. An $E$ block forces its right coordinate to alpha and its left partner to beta. Otherwise both coordinates are images. In particular $a,c$ are images. Distinctness allows at most one alpha right coordinate. If it occurs its beta partner excludes beta elsewhere, and the other four values are branch images. If no alpha occurs, all six values are images, with at most one beta. This gives precisely the eleven cases. Conversely each listed case makes every depth-two block, and hence the entire filling, an image. Its injective filling has row $R_*$ and the inverse gives an actual finite origin. Different positive-height $B_j$ realize each profile. They witness nonemptiness without restricting its other members. This is the FCS/BPS/POC actual-profile classification; §2 verifies the stated whole targets. $\square$

## 2. Five complete literal target rows

**Definition 2.1 (full row objects).** Let $h_p$ denote the occurrence hole at $p$. The literal exteriors $C_j$ of $R_j$ are

$$
\begin{aligned}
C_0&=[[[h_{LLL},h_{LLR}],[h_{LRL},h_{LRR}]],
       [[h_{RLL},h_{RLR}],[h_{RRL},h_{RRR}]]],\\
C_1&=[[\beta,[h_{LRL},h_{LRR}]],
       [[h_{RLL},h_{RLR}],[h_{RRL},h_{RRR}]]],\\
C_2&=[[[h_{LLL},h_{LLR}],\beta],
       [[h_{RLL},h_{RLR}],[h_{RRL},h_{RRR}]]],\\
C_3&=[[[h_{LLL},h_{LLR}],[h_{LRL},h_{LRR}]],
       [\beta,[h_{RRL},h_{RRR}]]],\\
C_4&=[[[h_{LLL},h_{LLR}],[h_{LRL},h_{LRR}]],
       [[h_{RLL},h_{RLR}],\beta]].
\end{aligned}
\tag{FTC.7}
$$

Their entire equality partitions are

$$
\begin{aligned}
\pi_0&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_1&=\{\{LRL\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_2&=\{\{LLL\},\{LLR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_3&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RRL\},\{RRR\}\},\\
\pi_4&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL\},\{RLR\}\}.
\end{aligned}
\tag{FTC.8}
$$

Each different pair of blocks asserts disequality. The remaining components of each output are explicit here.

| Row | Ordered reached holes | First-member names | All absent cuts; concrete guard |
| --- | --- | --- | --- |
| $R_0=R_*$ | $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,0,3,4,5,4,7)$ | None |
| $R_1$ | $LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LLL,LLR$; beta at $LL$ |
| $R_2$ | $LLL,LLR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LRL,LRR$; beta at $LR$ |
| $R_3$ | $LLL,LLR,LRL,LRR,RRL,RRR$ | $(0,1,0,3,4,5)$ | $RLL,RLR$; beta at $RL$ |
| $R_4$ | $LLL,LLR,LRL,LRR,RLL,RLR$ | $(0,1,0,3,4,5)$ | $RRL,RRR$; beta at $RR$ |

A symbol $R_j$ in a transition specification means that the entire fixed object above is installed at that Halt. It never means a runtime target index for a source-dependent decoder.

**Proposition 2.2 (whole-target calculation, reused).** On $\Pi_j$ the target is $R_j$; on all seven zero profiles it is $R_0$. The five entire outputs are distinct and attained.

Proof. In a zero profile each depth-two block is a pair of images. Its inverse retains a pair and both addressed cut occurrences. All eight holes remain. On $\Pi_j$ exactly the block at $q_j$, for $(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, is $E$. Its inverse is the concrete beta, blocking exactly its two child cuts. The other three blocks retain pairs and holes. The partner's other occurrence remains an old hole. Injectivity of $\rho$ preserves all equalities and disequalities among surviving whole values. Restricting the occurrence partition and recomputing first-member names gives exactly (FTC.8) and the table. The beta at $q_j$ guards both absent cuts. Different reached supports distinguish the five rows, and Proposition 1.4 attains all of them. This is the inherited occurrence-sensitive calculation, with no classwise deletion. $\square$

## 3. Explicit tables, languages, encodings and paid services

**Assumption 3.1 (operational premises).** Exactly one genuine authenticated update binds actual $u$ to the same register $t_u=\rho u$. Origin, root, cut and version stay fixed: no reset, rerooting, source substitution or source-register copy, arbitrary edit or later update is allowed. Authentication certifies continuity and selects no member within $\mathcal U_*$. The complete current row is lawfully acquired.

A native preparer has separately supplied pre-cut permission to query that stationary register. Acquired trees, class values, acquisition archive, old outputs and trace are inaccessible to it. Its complete bit is actually exported. A paid code-only handoff hides all preparation material and enters exactly the original serving entry for that bit. An absorbing preparation stop provides no resume action; serving entry is a separately supplied invocation. Material can be inaccessible without physical erasure. Both phases use the same truthful stationary register.

Acquisition and representation, authentication and continuity, pre-cut permission, installation, state/literal/whole-output storage, local operations, native service, actual export, isolation, handoff and faithful lawful entry remain separately supplied and priced. Neither proof nor certificate supplies a service. The current counted state is the sole accessible mutable source-dependent memory. There is no extra source identity, acquired term or tuple, predecessor row, alpha marker, cache, archive, pointer, trace, allocation, acquisition order/count, length, meter, timing, clock, phase, history, counter, reply register, address register or source-dependent table choice. There is no equality, inverse, image, provenance, generation or auxiliary source port.

**Definition 3.2 (immutable serving table and common-start preparer).** An explicit serving table $T$ has a finite installed disjoint set $K_T=Q_T\sqcup H_T$. Each Read $q$ stores one finite literal $a_T(q)\in\mathcal W$ and all four successors $n_T(q,r)\in K_T$, $r\in\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. Each Halt stores one entire canonical row $o_T(h)$. Distinct installed entries $e_0,e_1$ have their original recoverable labels. A Read makes one paid call at its literal and takes the successor for that truthful reply; a Halt emits its entire stored row without a call. There is no free control transition, extra program counter or output decoder. Table and labeled entries remain immutable.

A preparer $A$ similarly has nonempty $K_A=Q_A\sqcup H_A$, one common source-independent start $s_A$, fixed literals, four successors and original-bit Halts $o_A(h)\in\{0,1\}$. A Halt replaces live control by its complete bit latch. There is no independent live bit register beside it. Every installed record counts, including unused Reads, unused Halts, duplicate words and distinct equal-output Halts. All installed words and successors are explicit, including those used only from an incorrect entry. Shared states, convergence, cycles and early Halts are allowed. Every Read visit costs one call, including repeated literals, $\varepsilon$, forced replies, absent replies and leaf continuations. Only the actually selected serving entry must succeed; its unselected counterpart may be wrong, over cap or divergent.

**Definition 3.3 (POC encodings and exact languages).** Use POC §3's full explicit binary arrays of numbered state records, with delimited or length-prefixed fields. A Read stores its tag, literal length, every literal letter and four successor indices. Preparatory Halts store their original bits; serving Halts store entire row exteriors with addressed holes, concrete leaves and canonical names in reached order. Support, first-member names and guards must agree with the exterior. Include common start and distinct original entries; check tags, lengths, indices, rows and delimiters. Invalid encodings are rejected. A syntactically valid serving output outside the five required rows is permitted as a table record but is wrong whenever issued on this domain.

Budgets $P,L\in\mathbb N_0$ use ordinary positional binary fields, with zero encoded as $0$. Their numeric values need not be polynomial in their bit lengths. An optional installed-state bound $N$ is checked against every installed preparer record; explicit validation needs no unary-$N$ promise. In witness bounds $s$ is the complete explicit input bit length, including the tables, entries and any supplied vectors, row and budget fields. Thus total literal letters and installed state counts are at most $s$. The signature, cut and five required rows are fixed constants.

For any tables, successful or otherwise, define their full attained relation

$$
\mathcal J(A,T)=\left\{\left(
(r_{t_u}(a_A(q)))_{q\in Q_A},\,
(r_{t_u}(a_T(q)))_{q\in Q_T},\,F(u)\right):u\in\mathcal U_*\right\}.
\tag{FTC.9}
$$

Both vectors are in installed state order. Duplicate and unused Reads remain separate coordinates. One actual source determines both vectors and the target together. With one apparatus absent use an empty observation menu. These vectors are mathematical data, never runtime payloads.

The exact POC languages are as follows.

| Language | Variable input and acceptance condition |
| --- | --- |
| JOINT-ATTAIN | Explicit $A,T$ and a proposed pair of full reply vectors and entire target; some one actual source realizes that joint element |
| BOTH-PREPARER | Explicit $A,P$; actual within-$P$ runs attain original bit zero and original bit one, without universal or serving requirements |
| UNIVERSAL-TWO-STAGE | Explicit $A,T,e_0,e_1,P,L$; on every actual source preparation halts within $P$ and its actual selected entry returns all of $F(u)$ within $L$; BOTH is not required |
| FULL-FINITE-TABLE-VALIDATION | UNIVERSAL-TWO-STAGE and BOTH-PREPARER, with any specified $|K_A|\le N$ check |
| SOME-LAWFUL-ACQUIRED-CODE | Explicit $T,e_0,e_1,L$ under the separate acquired-data contract of §9; existence of a lawful total both-attained code selecting a good entry everywhere |

All reject malformed encodings. Write

$$
\mathrm{DP}:=\{X\cap Y:X\in\mathrm{NP},\ Y\in\mathrm{coNP}\}.
\tag{FTC.10}
$$

DP here is a class of intersections of languages, not the intersection of the two classes NP and coNP. Completeness throughout uses deterministic polynomial many-one reductions on binary strings.

**Lemma 3.4 (sourcewise no-revisit and binary-cap checking, reused).** For one stationary source, a halting path in a table with $q$ installed Reads uses at most $q$ calls. Bounded behavior is polynomially checkable from its explicit reply vector and a binary cap $C$, without iterating to the numeric value of $C$.

Proof. A Read has one literal and hence one fixed reply on the fixed source. Revisiting it repeats its deterministic future forever. Thus a halting run never revisits a Read. For checking, inspect a Halt before a call and immediately after every successor, including after the final allowed call. A correct initial Halt or correct final-call Halt succeeds without another probe. A wrong Halt fails. At a live Read with the cap already exhausted, fail; otherwise detect a repeated Read or make the vector-specified step and increment the actual-call count. At most $q$ distinct Reads are processed before Halt, repetition or cap failure. The count is at most $q$ and comparison with positional binary $C$ is polynomial. Apply this to preparation first and, only after its actual bit, the selected serving entry on the same vector/target element. No condition is imposed on the other entry. Uncapped sourcewise termination is equivalent to caps $|Q_A|,|Q_T|$. The principle fixes a source; cycles across different-source paths are allowed. A verifier's visited set grants no such storage to runtime. This is the FCS/BPS/POC stationary path argument. $\square$

## 4. Role-specific exact lists and semantic matching

**Definition 4.1 (four types and role constraints).** Partition all finite terms into

$$
\mathsf A=\{\alpha\},\quad \mathsf H=\{\beta\},\quad
\mathsf I=\mathcal B,\quad
\mathsf O=\mathcal T\setminus(\mathsf A\cup\mathsf H\cup\mathsf I).
\tag{FTC.11}
$$

A branch has type $\mathsf I$ exactly for ordered child-type pairs

$$
\mathcal C_I=\{(\mathsf H,\mathsf A),(\mathsf H,\mathsf H),
(\mathsf H,\mathsf I),(\mathsf I,\mathsf H),(\mathsf I,\mathsf I)\}.
\tag{FTC.12}
$$

All other ordered child-type pairs give $\mathsf O$. A branch is never a leaf type. The exceptional pair $(\mathsf H,\mathsf A)$ is precisely $E$.

Given proposed joint vectors, keep one index $i$ for every installed Read of length at least three. Decompose its literal as $p_iw_i$ with $|p_i|=3$, retain its actual role $d_i=[p_i]$, and denote its requested reply by $r_i$. All words shorter than three must request branch, or reject. For each whole role define

$$
C_d=\{y\in\mathcal T:r_y(w_i)=r_i\text{ for every index with }d_i=d\}.
\tag{FTC.13}
$$

Both occurrences of a repeated partner constrain this same set. Do not guess a full cross-role vector. Form the common prefix trie of all suffixes $w_i$, with all ending indices retained at each marker and $\#$ for an unobserved child. For a nonempty menu its explicit node count satisfies $V\le1+\sum_i|w_i|\le s+1$; for an empty menu set $V=0$ and use only $\#$. An unobserved child permits arbitrary finite child trees; it is not an absent child of a branch.

**Lemma 4.2 (exact role lists).** At every explicit trie node and for each of the six roles and four types, one can deterministically retain a list with exactly the number of compatible terms capped at six. Every member is an actual finite term. Below capacity six the list contains the entire language.

Proof. At a node $v$, restrict to indices of the chosen role below $v$, making their suffixes relative to $v$. Other roles' markers impose no condition. At $\#$ there are no constraints: use the four lists $\{\alpha\}$, $\{\beta\}$, $\{B_1,\ldots,B_6\}$ and $\{[\alpha,B_1],\ldots,[\alpha,B_6]\}$.

At an explicit node retain alpha precisely if every ending role index requests alpha and every strict-descendant role index requests absent. Use the same rule for beta with beta at the root. This leaf rule is independent of whether a corresponding child branch language is realizable. Permit a branch precisely if every ending role index requests branch. For each of the sixteen ordered child-type pairs, pair the retained compatible left and right witnesses, assign the parent type by (FTC.12), and keep up to six different parents per type. Fix orders of roles, types, child choices and retention to make the construction deterministic.

The invariant follows by induction. The leaves have exactly the stated replies at the root and all continuations. Every branch has a unique ordered child decomposition; left and right constraints are independent. Child-type alternatives are disjoint. For disjoint unions, exact counts below six retain all possibilities, while a union of size at least six supplies six choices. For a nonempty Cartesian product below six both factors are retained completely; at or above six either both smaller factors are fully retained or one retained factor supplies six choices paired with one member of the other. A zero factor yields no pair. Thus saturated sums and products, and the finite retained lists themselves, have the exact capped cardinality. Induction applies at every node and yields the desired root lists for $C_d$ and each type. Contradictory duplicate requests, empty suffixes, early leaves, all-absent cones and impossible root absence are included by the same rules. No capped subtraction or inclusion-exclusion is used. This reuses the BPS/POC capped recurrence with role-specific constraints. $\square$

**Lemma 4.3 (six-list truncation).** For any six sets $S_1,\ldots,S_6$, let $L_i\subseteq S_i$ contain exactly $\min(6,|S_i|)$ different members. A system of six distinct representatives exists in the $S_i$ if and only if one exists in the $L_i$.

Proof. A system in the lists is already one in the sets. Conversely start with distinct representatives $z_1,\ldots,z_6$ in the sets and process $i=1,\ldots,6$. If $z_i\in L_i$, keep it. Otherwise $L_i$ has six members, since a smaller list contains its entire set. At most five are occupied by the other five current representatives. Replace $z_i$ by an unoccupied member of $L_i$. The system stays distinct and all earlier processed choices remain in their lists. After six steps all choices lie in their lists. Infinite sets present no additional case. This is an elementary distinct-representative replacement argument. $\square$

**Lemma 4.4 (global semantic equality and list size).** All lists of Lemma 4.2 have one shared finite acyclic ordered-term DAG with at most $144V+14$ nodes. Its canonical identifiers agree exactly for equal finite unfolded terms, including across different role lists.

Proof. Give alpha and beta distinct global identifiers. Intern every retained pair by the ordered pair of its already canonical child identifiers. Structural induction proves equality of identifiers equivalent to equality of finite ordered unfoldings. New pairs point only to previously constructed children, so there is no cyclic or rational-tree semantics. Repeated pointers unfold into distinct occurrences when used at different addresses.

The shared unrestricted basis uses two leaves, six successive $B_j$ nodes and six $[\alpha,B_j]$ nodes, totaling fourteen. At an explicit node there are six roles, four types and at most six retained terms per list, so at most $144$ additional retained pair nodes. Discarded candidates need not become nodes: their canonical ordered child-pair keys suffice for comparison with retained keys and the global intern table. There are at most sixteen times thirty-six candidate pairs per role per node, a constant. Even naive key comparisons, endpoint and descendant constraint processing and list management take polynomial time. This gives the stated node bound. Pointer inequality alone is never used as whole-term disequality. $\square$

**Theorem 4.5 (polynomial exact JOINT-ATTAIN and actual-origin construction).** JOINT-ATTAIN is in deterministic polynomial time. For every positive instance of full explicit length $s$, a deterministic polynomial construction returns six class roots, the current root and an actual origin root in a finite DAG of at most $300(s+2)$ nodes and $O(s\log(s+2))$ bits.

Proof. Check the exact input syntax, entries, vector lengths and reply symbols. The proposed target must equal one of the five complete objects of §2; otherwise reject. Require the constant branch replies on short words and construct the lists of Lemma 4.2.

For each of the eleven profiles with the proposed entire target, take at each role the root list of its required type. Make a bipartite graph with six left vertices, one per role, and right vertices the global semantic identifiers in these lists. A role is adjacent to precisely its listed members. There are at most thirty-six right vertices and thirty-six edges. Find a matching covering the six roles, if one exists. For example repeatedly augment along an alternating path from an unmatched role to an unused value. If no such path exists, no larger matching exists: the symmetric difference with a larger matching would contain an augmenting path. At most six augmentations are required. Accept if any eligible profile has a covering matching.

For soundness, the matched values satisfy every actual role constraint and are pairwise different as entire terms. Repeat the selected $a,c$ roots at their prescribed two occurrences and form $\mathscr S(x)$. The tested profile proves it is an image with the original full current row; its inverse is an actual $u\in\mathcal U_*$. Its predecessor row is the proposed whole output. Every long installed literal has its requested reply by (FTC.2), and every short literal has branch. Thus one actual source realizes both full indexed vectors and the target simultaneously, including unused records.

For completeness, an actual realizing source has exactly one eligible profile. Its six distinct roots belong to the six required constrained type languages. Lemma 4.3 moves this distinct system into the retained lists, so their graph has a covering matching. The algorithm therefore accepts every attained joint element. Independent nonempty marginals would not suffice: in the all-branch-image profile, requiring right-root alpha for each of $a,c$ makes each language the singleton $\{E\}$, which cannot fill two different whole roles. Global matching rejects that collision.

Finally append at most seven exterior pair nodes to the list DAG. Parse image membership bottom-up and memoize $\delta$ to obtain the source root; at most one new inverse pair node is needed per visited current node, and inverse leaves reuse the basis. The total is at most

$$
2(144V+14+7)=288V+42\le300(V+1)\le300(s+2).
\tag{FTC.14}
$$

Backward pointers and the eight roots use $O(s\log(s+2))$ bits. Constraint processing, interning, eleven constant-size matching tests, exterior construction and memoized inversion are polynomial. The bound holds also for the empty menu. It bounds a semantic DAG certificate; its ordinary unfolding need not have polynomial size. No source-height promise or runtime DAG facility has been introduced. $\square$

## 5. Reused semantic certificates and membership bounds

**Lemma 5.1 (one-origin and two-distinct-origin certificate bounds, POC reuse).** One attained joint element has a finite semantic DAG certificate with at most $300(s+2)$ nodes. Two attained elements at genuinely distinct actual sources have a joint certificate with at most $1200(s+2)$ nodes, retaining distinctness even if their joint elements coincide. Both have $O(s\log(s+2))$-bit encodings and deterministic polynomial direct semantic verifiers.

Proof. The one-origin assertion follows also from Theorem 4.5. For the needed two-origin assertion, the POC selected-vector construction has the following complete argument. Given two actual six-tuples, put $K=12$. For each of their twelve coordinates record its type and full reply vector at all suffix indices, including other roles' indices. At a trie node only the restrictions of these at most twelve selected vectors are needed. For each restriction and four types retain exactly the capped-at-$K$ list by the leaf and disjoint-product recurrence of Lemma 4.2. At most $4K^2$ witnesses per explicit node suffice. The shared basis needs $2K+2$ nodes, so the list DAG has at most $4K^2V+2K+2$ nodes.

The root type/full-vector cells partition all finite terms. In each occupied cell let $h\le K$ be the number of different original whole values, identifying equal coordinates also across the two origins. Its retained list has at least $h$ members. Assign different members to different equality classes and the same member to every coordinate of the same class. Different cells are disjoint. This preserves the entire twelve-coordinate equality/disequality matrix, the types and full suffix vectors. Each tuple therefore retains its actual profile and target and gives an actual inverse origin. Project each role's full vector to its own installed indices to retain its entire joint element. Different original sources have different tuples, since a tuple determines its current tree and unique inverse; some corresponding coordinate inequality survives, so the new origins stay different.

Adding at most fourteen exterior nodes and memoized inverses gives at most $1152V+82\le1200(V+1)\le1200(s+2)$ nodes, with slack for shared leaves. For one origin the same construction with $K=6$ gives the stated $300$ bound. Backward pointers, constant-many roots, explicit reply fields and constant-size whole rows give the polynomial bit bound.

For direct verification check syntax and backward pointers, globally intern all nodes from both origins, require the fifteen semantic disequalities within each tuple, rebuild $\mathscr S(x)$ with its repetitions, parse its image and compare its inverse with the claimed source root. Compute the entire current row and require $R_*$. Independently extract the predecessor row from the source root at the fixed depth-three cut, retaining occurrence holes, early blocking leaves, semantic partitions and first-member names. Follow every literal on that same current root and check all indexed replies. If required, compare source identifiers and require inequality. Lemma 3.4 checks bounded paths. These operations are polynomial in the DAG and explicit input lengths: image/inverse work is memoized, cut extraction has fixed breadth and depth, and descent along a literal uses at most its stored length. Backward pointers ensure finite unfoldings, and global interning ensures exact semantic equality, proving soundness. The construction above proves completeness. This is POC §§4–6's certificate theorem and verifier; it is not additional classification content. $\square$

**Proposition 5.2 (POC membership facts).** BOTH-PREPARER is in NP, UNIVERSAL-TWO-STAGE is in coNP, and FULL-FINITE-TABLE-VALIDATION is in DP. The sourcewise uncapped variants have the same upper bounds.

Proof. For BOTH guess two actual-origin certificates and check within-$P$ preparer runs with original bits zero and one. Distinctness follows from deterministic common-start behavior and may also be checked semantically. Lemma 5.1 supplies certificates for every positive instance, using an empty serving menu. A universal violation has one actual source with preparation failure or, after its actual bit, selected-serving failure. The failure depends only on its full joint element. Lemma 5.1 supplies a polynomial certificate preserving that element; Lemma 3.4 recognizes cap excess, divergence or wrong entire output. Conversely every verified bad-source certificate is a real violation. The complement accepts malformed explicit inputs by a deterministic syntax check with a dummy certificate. Thus UNIVERSAL is coNP, and its intersection with NP BOTH is DP. An optional polynomial state-count check can be conjoined. Replacing caps by installed Read counts proves the uncapped upper bounds. These are credited POC Theorem 7.2 applications. $\square$

## 6. Actual-origin Boolean banks and a four-reply CNF compiler

**Lemma 6.1 (Boolean assignments on all sources and actual witnesses).** A polynomial list of fixed native literals defines a consistent Boolean assignment on every actual source. Every Boolean assignment has an actual finite witness in each of $\Pi_1,\Pi_2$, with all six whole values different.

Proof. Renumber each formula's distinct variable names in a fixed syntactic order as $1,\ldots,n$. For several formulas use $n\ge1$ at least their maximum variable count, renumbering each locally. Let $\ell=\lceil\log_2(\max(2,n))\rceil$ and choose the first $n$ distinct length-$\ell$ words $w_i$ in lexicographic order. For variable $i$ use the fixed literal $v_i=p_cw_i=RLLw_i$. On every actual source define

$$
b_i(u)=1\quad\Longleftrightarrow\quad r_{t_u}(v_i)=\mathsf{branch}.
\tag{FTC.15}
$$

Alpha, beta and absent all mean zero. Stationarity makes repeated occurrences consistent. No Boolean-source promise is imposed.

For any Boolean assignment $b$, take a perfect ordered skeleton of depth $\ell$. At frontier $w_i$ put $B_1$ if $b_i=1$ and beta otherwise; at unused frontier words put beta. Call the result $C_b$. Its leaves at the frontier are images and images pair to images, so $C_b$ is a branch image. Its height is at most $\ell+1$, its ordinary finite size is $O(2^\ell)=O(n+1)$, and it gives exactly the desired branch/zero replies at all $w_i$.

In $\Pi_1$ choose

$$
x_a=\beta,\quad x_{b_1}=\alpha,\quad x_c=C_b,\quad
x_{b_2}=B_{\ell+2},\quad x_{b_3}=B_{\ell+3},\quad x_{b_4}=B_{\ell+4}.
\tag{FTC.16}
$$

For $\Pi_2$ put alpha at $b_2$ and $B_{\ell+2}$ at $b_1$, leaving the other coordinates as above. The three fresh heights exceed that of $C_b$ and are mutually different; both leaves differ from all branches. Hence all six whole values differ. Repeated partners use their single assigned value. Proposition 1.4 gives the actual finite origin $\delta(\mathscr S(x))$ and target $R_1$ or $R_2$. These witnesses realize all assignments, while the domain still includes all other legal finite origins. A fixed unconditional $Z_*$ witness is the tuple $B_1,\ldots,B_6$ in $D$ order. $\square$

**Lemma 6.2 (literal CNF evaluator on every actual source).** For a well-formed CNF $G$ with $M$ literal occurrences and supplied continuation states $S,F$, a graph with exactly $M$ installed occurrence Reads reaches $S$ if $G(b(u))$ is true and $F$ otherwise, after at most $M$ calls. Its complete encoding is polynomial in the CNF encoding length.

Proof. Write the ordered clauses as $C_1,\ldots,C_m$. Install a Read $q_{j,k}$ for every literal occurrence, querying the fixed $v_i$ for that occurrence's variable. Define $E_{m+1}=S$. An empty clause has entry $E_j=F$; a nonempty clause has entry $E_j=q_{j,1}$. For a positive literal only branch is satisfying; for a negative literal alpha, beta and absent are satisfying. At $q_{j,k}$ every satisfying reply goes to $E_{j+1}$; every unsatisfying reply goes to $q_{j,k+1}$, or to $F$ if this is the last literal. This specifies all four successors at every occurrence. The evaluator entry is $E_1$. Install every occurrence, including unreachable ones.

If a clause has a satisfied literal the run takes its first such literal to the next clause; otherwise it reaches failure. Induction on remaining clauses and literal positions proves the claimed behavior on the one source-defined assignment (FTC.15). Clauses only advance and literal positions only advance, so at most $M$ occurrence Reads are visited. An empty conjunction has entry $S$ and an empty clause has entry $F$. These are compile-time aliases of installed states, not free runtime transitions; an entry can already be a continuation Halt or loop Read. Tautologies, repeated variables and arbitrary non-Boolean native replies are covered by the same proof.

There are $M$ explicit Read records, each with literal length $3+\ell$ and four explicit successor indices. Renumbering variables depends on the number of distinct names, not their numeric magnitude. Parsing and constructing the array are polynomial in the input encoding length, as is its total bit length. No tuple, acquired-term operation, computed address or auxiliary memory occurs in this graph. $\square$

**Proposition 6.3 (credited source hardness premise and paired source).** Use the mature premise that well-formed Boolean CNF satisfiability is NP-complete. The language

$$
Q=\{(\phi,\psi):\phi,\psi\text{ are well-formed CNFs},\
\phi\text{ is unsatisfiable and }\psi\text{ is satisfiable}\}
\tag{FTC.17}
$$

is DP-complete; the well-formed UNSAT language is coNP-complete.

Proof. SAT membership has a Boolean assignment certificate. For any NP language its SAT reduction may have well-formed outputs: replace a malformed output by a fixed contradictory CNF. This preserves SAT membership. If $Y\in\mathrm{coNP}$, reduce its NP complement to SAT by such a map $g$. Then $x\in Y$ exactly when $g(x)$ is a well-formed unsatisfiable CNF, proving well-formed UNSAT hardness. Its complement consists of malformed strings or satisfiable CNFs and is NP, so UNSAT is coNP-complete.

The displayed $Q$ is an NP/coNP conjunction with polynomial syntax checks. For any $X\in\mathrm{NP}$ and $Y\in\mathrm{coNP}$ choose well-formed-output reductions $f$ from $X$ to SAT and $g$ from the complement of $Y$ to SAT. Then $x\in X\cap Y$ exactly when $(g(x),f(x))\in Q$. This proves DP-hardness from the stated SAT premise. Empty conjunctions represent true; a CNF with an empty clause represents false. All source languages here reject malformed encodings. The SAT premise and these classical reduction methods are credited, without external research or primary validation. $\square$

## 7. Supplied-table validation is NP, coNP and DP complete

**Definition 7.1 (one separately specified fixed ten-state table).** Install five Reads $C_1,C'_1,C_2,C_3,C_4$ and five whole-row Halts $H_0,\ldots,H_4$. Each $H_j$ stores the entire $R_j$ of §2. For $j=1,\ldots,4$, Read $C_j$ queries $p_{b_j}$, has alpha successor $H_j$, and has successor $C_{j+1}$ for each of beta, branch and absent when $j<4$, or $H_0$ for each when $j=4$. The duplicate $C'_1$ has exactly the same literal and all four successors as $C_1$. Let

$$
T_{10}:\quad e_0=C_1,\quad e_1=C'_1,\quad L=4.
\tag{FTC.18}
$$

The entries are distinct installed records carrying the original labels. The duplicate counts. Every state, word, successor and whole output stays fixed across the validation family.

**Lemma 7.2 (both ten-state entries correct everywhere).** On every actual source both original entries of $T_{10}$ return the complete correct row within four calls.

Proof. In $\Pi_j$ precisely $b_j$ has root alpha, so the sequential classifier stops at $H_j$ in $j$ calls from either entry. On every zero profile no $b_j$ has root alpha, so either entry reaches $H_0$ in four calls. The eleven cases are exhaustive and §2 gives those exact whole outputs. The entries may converge after the first paid Read; no extra code register is needed. The original label remains recoverable from its distinct initial state at entry. $\square$

**Theorem 7.3 (complete supplied-table classifications).** BOTH-PREPARER is NP-complete, UNIVERSAL-TWO-STAGE is coNP-complete, and FULL-FINITE-TABLE-VALIDATION is DP-complete. UNIVERSAL and FULL hardness already hold with the one fixed $T_{10}$, original fixed entries and $L=4$, while the explicit preparer and binary $P$ vary.

Proof. For a well-formed pair $(\phi,\psi)$ install preparer mode Reads $U_1,U_2$, disjoint occurrence graphs for the two CNFs, a loop Read $D$ and bit Halts $Z_0,Z_1$. Start at $U_1$. It queries $p_{b_1}$: alpha goes to $\operatorname{Eval}(\phi;D,Z_0)$, and each other reply goes to $U_2$. Read $U_2$ queries $p_{b_2}$: alpha goes to $\operatorname{Eval}(\psi;Z_1,Z_0)$, and each other reply goes to $Z_0$. Here $\operatorname{Eval}(G;S,F)$ is exactly the compile-time entry and all occurrence records of Lemma 6.2. Read $D$ queries $\varepsilon$ and all four successors are $D$. Each $Z_z$ stores the original bit $z$. Every occurrence and continuation is installed, including unused records and both Halts. There are exactly $M_\phi+M_\psi+5$ preparer states. Set

$$
P=2+M_\phi+M_\psi
\tag{FTC.19}
$$

in binary and use (FTC.18). All nonloop paths terminate within $P$: the $\phi$ branch takes at most $1+M_\phi$ calls, the $\psi$ branch at most $2+M_\psi$, and the default branch two. Entering $D$ never terminates. An optional state bound can equal the exact installed count, in the encoding required for that separate field.

The following description holds on every actual source. The first gate enters the $\phi$ graph exactly on $\Pi_1$, since alpha at $b_1$ characterizes that profile. It loops exactly when $\phi(b(u))$ is true, and otherwise outputs zero. After a nonalpha first reply the second gate enters the $\psi$ graph exactly on $\Pi_2$. It outputs one exactly when $\psi(b(u))$ is true, and otherwise zero. Every other profile outputs zero. These converses use all eleven profiles and the evaluator on arbitrary actual replies, not just the specially constructed Boolean witnesses.

If $\phi$ is unsatisfiable no actual assignment enters the loop; all preparation paths terminate within $P$, and Lemma 7.2 serves either selected bit correctly. If $\phi$ is satisfiable, Lemma 6.1 gives an actual satisfying $\Pi_1$ source that loops. Therefore UNIVERSAL holds exactly when $\phi$ is unsatisfiable, independently of $\psi$.

The fixed $Z_*$ witness always outputs zero. An output-one source must be a $\Pi_2$ source satisfying $\psi$ on its source-defined assignment, so such a source implies satisfiability of $\psi$. Conversely an actual satisfying $\Pi_2$ witness exists for every satisfying assignment and reaches $Z_1$ within $P$. It differs from the $Z_*$ witness by profile. Thus BOTH holds exactly when $\psi$ is satisfiable, independently of $\phi$. FULL consequently holds exactly for $Q$. This proves DP-hardness with the displayed fixed ten-state table, and Proposition 5.2 supplies DP membership.

For NP-hardness of BOTH alone use one gate at $p_{b_2}$ whose alpha successor is $\operatorname{Eval}(\psi;Z_1,Z_0)$ and whose other three successors are $Z_0$. Install all occurrence records and the two bit Halts, and set $P=1+M_\psi$. This acyclic preparer halts on every actual source. The $Z_*$ witness gives zero and one is attained exactly for SAT by the same all-source converse and actual $\Pi_2$ construction. Proposition 5.2 supplies NP membership. Thus even universally terminating acyclic preparers give the NP lower bound.

For UNIVERSAL hardness fix $\psi$ to the empty conjunction in the paired construction. BOTH is then unconditional, with $\Pi_2$ and $Z_*$ witnesses; UNIVERSAL is equivalent to UNSAT of $\phi$. Proposition 5.2 supplies coNP membership. The constructions and binary caps have polynomial encoding length by Lemma 6.2.

To make every reduction total on binary strings, first check formula or paired-formula syntax. A malformed BOTH input maps to a fixed valid constant-zero preparer with $P=0$. A malformed UNIVERSAL input maps to a fixed valid loop preparer with, for example, $P=0$, paired with $T_{10},L=4$. A malformed paired FULL input maps to the constant-zero preparer with $T_{10},L=4,P=0$: its universal property holds but BOTH fails. These are rejecting outputs. Hence the maps are total many-one reductions to the exact languages, not promise maps. All nonloop paths of the well-formed constructions are bounded by their installed Read counts and the counterexamples loop forever, so the same reductions and Proposition 5.2 give the respective sourcewise uncapped completeness statements as well. $\square$

## 8. The unchanged eight-state slice is coNP complete

**Definition 8.1 (the original fixed eight-state serving table).** Keep exactly the FCS Definition 10.1 / POC Proposition 11.1 table, writing $D_j$ for its three Read names. Install those three Reads and five whole-row Halts $H_0,\ldots,H_4$, with the entire §2 outputs and original entries $e_0=D_1,e_1=D_3$.

| Read | Literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D_1$ | $LLR$ | $H_1$ | $H_0$ | $D_2$ | $H_0$ |
| $D_2$ | $LRR$ | $H_2$ | $H_0$ | $H_0$ | $H_0$ |
| $D_3$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

Call it $T_8$ and retain $L=2$. It is a different fixed table from $T_{10}$.

**Lemma 8.2 (baseline and forced attainment).** The baseline selection zero on $\Pi_1,\Pi_2$ and all zero profiles, and one on $\Pi_3,\Pi_4$, is correct everywhere for $T_8$ within two calls. Every universally successful preparer for this table at $L=2$ necessarily attains both bits within its preparer cap.

Proof. On $\Pi_1$, entry zero sees alpha at $b_1$ and emits $R_1$. On $\Pi_2$ it sees branch at $b_1$ and alpha at $b_2$, emitting $R_2$. On every zero profile, if $b_1$ is beta it immediately emits $R_0$; otherwise $b_1$ is branch and $b_2$ is beta or branch, again giving $R_0$. On $\Pi_3$, entry one sees alpha at $b_3$ and emits $R_3$. On $\Pi_4$ it sees branch there and emits $R_4$. This verifies the baseline on all eleven cases.

On every $\Pi_1$ source entry one instead returns $R_4$, a different whole row. Universal selected-entry success therefore forces preparer bit zero on every such source. On every $\Pi_3$ source entry zero sees branch at both $b_1,b_2$ and returns $R_0$, a different whole row. Success forces bit one there. Both profiles are actual and nonempty. Universal preparation termination supplies within-cap witnesses for these two forced bits. $\square$

**Theorem 8.3 (exact fixed-$T_8$ slice).** With the original fixed $T_8$, entries and $L=2$, FULL validation equals UNIVERSAL validation on size-eligible well-formed inputs, and is coNP-complete as a language rejecting malformed inputs. If an optional state cap is included, conjoin its deterministic check.

Proof. Lemma 8.2 shows that UNIVERSAL implies BOTH, so the two properties coincide on the indicated inputs. Their coNP upper bound follows from Proposition 5.2.

For hardness compile a preparer with four mode Reads $V_1,\ldots,V_4$ at $p_{b_1},\ldots,p_{b_4}$, the occurrence graph $\operatorname{Eval}(\phi;D,Z_0)$, loop $D$ at $\varepsilon$ with all four successors $D$, and bit Halts $Z_0,Z_1$. At $V_1$ alpha enters that evaluator and the other three replies go to $V_2$. At $V_2$ alpha goes to $Z_0$ and other replies to $V_3$. At $V_3$ alpha goes to $Z_1$ and other replies to $V_4$. At $V_4$ alpha goes to $Z_1$ and other replies to $Z_0$. Install all $M_\phi+7$ records and set binary $P=4+M_\phi$; if needed set the state cap to that exact count.

On every actual source this preparer is the verified baseline except that $\Pi_1$ enters a loop exactly for a true $\phi$ assignment. If $\phi$ is unsatisfiable every source follows the baseline and terminates within $P$, and serving succeeds by Lemma 8.2. If it is satisfiable an actual satisfying $\Pi_1$ source loops by Lemma 6.1, violating UNIVERSAL and FULL. Independently, $\Pi_2$ always supplies zero and $\Pi_3$ always supplies one. Thus both target properties are equivalent to well-formed UNSAT. A malformed formula maps to the fixed valid loop preparer, making the reduction total. This proves coNP-hardness and the stated completeness.

An unrestricted DP upper bound does not establish DP hardness for this slice. Indeed a DP-hard language in coNP would put NP, a subclass of DP, inside coNP by reduction closure; taking complements then gives NP=coNP. The independent SAT/UNSAT gates of §7 are proved for the separately specified $T_{10}$. No transition of $T_8$ is replaced in the present theorem. $\square$

## 9. Acquired selectors, exact finite cells and the lawful bridge

**Definition 9.1 (separate acquired-data language).** Under the FCS/POC acquired-data contract a producer genuinely possesses either the entire finite current tree or $R_*$ and all six same-source, same-version class terms. Local structural descent and whole-term equality on those acquired terms are permitted. A lawful code is a specified total finite deterministic computation on this finite acquired representation, whose complete original bit is actually exported under the separate isolation, handoff and faithful-entry services. Producer constants, workspace and computation have no bound here. These acquired terms are unavailable to native preparation.

For an explicit immutable $T,e_0,e_1$ and binary $L$ define

$$
\operatorname{Good}_z(u)\iff
T\text{ from }e_z\text{ returns the entire }F(u)\text{ within }L\text{ calls}.
\tag{FTC.20}
$$

SOME-LAWFUL-ACQUIRED-CODE asks for some lawful total code attaining both original bits and choosing a good entry on every actual source. There is no variable preparer $A$, native-preparation budget or arbitrary prescribed program text in its input.

**Lemma 9.2 (finite exactly attained partition, FCS reuse).** There is a finite exact partition of $\mathcal U_*$ on which both good sets and the full target are constant. Closed cells are singleton actual points; live cells are countably infinite.

Proof. Let

$$
b=\max\bigl(\{0\}\cup\{|a_T(q)|-3:q\in Q_T,\ |a_T(q)|\ge3\}\bigr),
\tag{FTC.21}
$$

using all installed words. Expose each of the six class terms through inclusive relative depth $b$, retaining literal early alpha/beta leaves and their absent cones. At a frontier branch place a live name that can only be filled by a finite branch image. Different frontier names are independent; a repeated partner repeats its whole pattern with the same names. There are finitely many such patterns. For their free terms $A_d$, retain all whole negatives $A_d\ne A_e$, $d\ne e$.

Define an image predicate on free syntax by $J(\alpha)=\mathsf{false}$, $J(\beta)=J(z)=\mathsf{true}$ for live names, and

$$
J([A,B])\iff
(A\text{ is literally }\beta\text{ and }B\text{ is literally }\alpha)
\ \lor\ (J(A)\land J(B)).
\tag{FTC.22}
$$

This is exact under every branch-image filling. In fact a name is always a branch and cannot create a new leaf needed by the literal-$E$ alternative; the other image alternative is exactly two images. Retain precisely tuples with $J(\mathscr S(A))$ true and unequal free syntax for every different pair of class terms.

Every actual source exposes one such retained tuple: branch subtrees of images are images, the image test is exact, and identical free class syntax would violate its whole-value disequality. Conversely a retained tuple has a simultaneous ground filling satisfying all negatives. Let $h\ge1$ bound all free-subterm heights with names treated as leaves. List live names $z_i$ and assign $z_i=B_{N_i}$ with $N_i>h$ and successive gaps greater than $h$. For unequal free terms descend to a first syntactic mismatch. Different concrete constructors remain different. Distinct names have different heights. A name against a ground term has greater height. Against a nonvariable term containing names, let $N_j$ be the largest assigned height occurring there. If $N_j<N_i$, its height is at most $\max(h,N_j+h)<N_i$. If $N_j>N_i$, it is greater than $N_i$. If $N_j=N_i$, that name occurs at positive depth and again gives height greater than $N_i$. Hence one assignment makes every nontrivial whole negative true at once. The exact image predicate gives an actual inverse with exactly the exposed profile. With no live names the already unequal ground tuple has its unique inverse. This proves exact coverage, not merely feasibility of selected samples.

A closed tuple determines one actual origin. In a live tuple replace all $N_i$ by $N_i+k$, $k\ge0$. Gaps persist, a selected live occurrence has strictly increasing height, and the tuples and inverse origins are all distinct. Finite terms are countable, proving countable infinity. Every installed literal reply is fixed by the inclusive prefix, and the root types fix the whole target. Lemma 3.4 therefore makes both good sets constant on the cell. This is the FCS finite-profile and multiplicity argument with its required filling details. No efficiency for constructing the full partition is asserted. $\square$

**Theorem 9.3 (exact lawful selector bridge and reused DP membership).** A lawful both-attained acquired code exists exactly when

$$
\begin{aligned}
\mathrm{Coverage}:&\quad \forall u\in\mathcal U_*,\
  \operatorname{Good}_0(u)\lor\operatorname{Good}_1(u),\\
\mathrm{DistinctPair}:&\quad \exists u_0,u_1\in\mathcal U_*,\
  u_0\ne u_1\ \land\operatorname{Good}_0(u_0)\land\operatorname{Good}_1(u_1).
\end{aligned}
\tag{FTC.23}
$$

Coverage is in coNP, DistinctPair is in NP, and their conjunction is in DP for variable explicit tables.

Proof. A compatible both-attained deterministic code chooses a good bit everywhere and attains its two values at different points, giving necessity. Conversely Lemma 9.2 supplies a finite exact cell partition and Coverage permits one stored good default per cell. Let $X^0,X^1$ be the two finite current class tuples of DistinctPair witnesses. Store them and define the acquired computation to output zero on $X^0$, one on $X^1$, and the stored good default of the input's cell otherwise. Whole-tuple structural equality, finite prefix extraction and lookup terminate on acquired finite terms. A representation check with a fixed fallback makes the computation total on other finite representations. On actual inputs the fallback is unused. A tuple determines its current tree and unique origin, so the two exceptions are disjoint and really attain the two original bits. Defaults and exceptions choose good entries. Export, isolation and faithful entry are supplied services, not consequences of the combinatorial criterion. This is the FCS selector theorem in the distinct-point form of POC §8; a singleton cell cannot supply both values of a function.

A Coverage violation has one actual-origin certificate on which both entries fail, recognized by Lemmas 5.1 and 3.4, so Coverage is coNP. DistinctPair has a two-origin certificate preserving genuine inequality and both good behaviors by Lemma 5.1, so it is NP. Invalid table encodings are rejected by both languages and handled by their respective syntax checks. The displayed conjunction is DP. These memberships and the lawful bridge are credited reuse, not separately invented results. $\square$

## 10. Variable-table acquired-selector DP completeness

**Theorem 10.1 (exact acquired-selector classification).** SOME-LAWFUL-ACQUIRED-CODE is DP-complete when the entire explicit serving table is input, with the same full actual domain, original labels, selected-entry criterion and separate acquired-data services.

Proof. Given well-formed $(\phi,\psi)$ install Reads $C_1,\ldots,C_4$, a separate gate $G$, disjoint occurrence graphs for the two CNFs, loop Read $D$, and five whole-row Halts $H_0,\ldots,H_4$. The $\phi$ evaluator is $\operatorname{Eval}(\phi;D,H_1)$ and the $\psi$ evaluator is $\operatorname{Eval}(\psi;H_2,D)$ with precisely the occurrence records of Lemma 6.2. Use these complete transitions:

| Read | Fixed literal | alpha successor | Each of beta, branch, absent successors |
| --- | --- | --- | --- |
| $C_1$ | $p_{b_1}$ | Entry of $\operatorname{Eval}(\phi;D,H_1)$ | $C_2$ |
| $C_2$ | $p_{b_2}$ | $H_2$ | $C_3$ |
| $C_3$ | $p_{b_3}$ | $H_3$ | $C_4$ |
| $C_4$ | $p_{b_4}$ | $H_4$ | $H_0$ |
| $G$ | $p_{b_2}$ | Entry of $\operatorname{Eval}(\psi;H_2,D)$ | $D$ |
| $D$ | $\varepsilon$ | $D$ | $D$ |

Each occurrence has all four successors from Lemma 6.2. Each $H_j$ stores the entire fixed $R_j$. Let $e_0=C_1$, $e_1=G$ and set

$$
L=4+M_\phi+M_\psi.
\tag{FTC.24}
$$

There are exactly $M_\phi+M_\psi+11$ installed records, including unused occurrences, the loop and all Halts. Every nonloop entry-zero run uses at most four classifier calls or $1+M_\phi$ calls. Every nonloop entry-one run uses at most $1+M_\psi$. Entering $D$ never halts. Thus the binary cap covers every nonloop path. All stored words have length three or $3+\ell$, except the paid empty loop literal. The full encoding, including all four successors and whole rows, is polynomial. Once constructed this instance's $T$, entries, words and labels are immutable during any execution or selector computation.

On every actual source, entry zero is good except exactly on $\Pi_1$ sources satisfying $\phi(b(u))$. On $\Pi_1$ a false formula reaches $H_1$ and a true formula enters $D$. On $\Pi_2,\Pi_3,\Pi_4$ the remaining classifier reaches the matching whole-row Halt. On all zero profiles it reaches $H_0$. Entry one is good exactly on $\Pi_2$ sources satisfying $\psi(b(u))$: its gate has alpha exactly in that profile, and there true reaches the correct $H_2$ while false enters $D$. Every other profile immediately enters $D$. These are all-source characterizations, including absences and unexpected leaf replies under (FTC.15).

If $\phi$ is unsatisfiable, entry zero is good everywhere, so Coverage holds. If $\phi$ is satisfiable, an actual satisfying $\Pi_1$ source exists by Lemma 6.1. Both entries fail there, since entry one rejects every $\Pi_1$ source at its gate. Therefore Coverage is equivalent to UNSAT of $\phi$, independently of $\psi$.

The fixed $Z_*$ tuple $B_1,\ldots,B_6$ is always good at entry zero. If $\psi$ is satisfiable, an actual satisfying $\Pi_2$ source is good at entry one and differs from that $Z_*$ source by profile. These give two genuinely distinct actual witnesses. Conversely DistinctPair includes a good entry-one source; by the complete characterization it is a $\Pi_2$ source whose consistent assignment satisfies $\psi$. Therefore DistinctPair is equivalent to SAT of $\psi$, independently of $\phi$.

Theorem 9.3 now gives selector existence exactly for $Q$. This proves DP-hardness, and its reused membership gives DP-completeness. For a malformed paired formula output the fixed valid table with two distinct Halt entries storing only $R_0,R_1$ and cap zero. An actual $R_2$ source is uncovered, so the output is negative. The reduction is a total map on binary strings. Its positive witnesses and universal counterexamples all have actual inverse origins and six whole-distinct values; the converse addresses the full unbounded domain.

The same construction shows Coverage is coNP-complete and DistinctPair NP-complete for variable explicit tables, using the memberships of Theorem 9.3. Fix $\psi$ to true to reduce well-formed UNSAT to Coverage, and fix $\phi$ to false to reduce well-formed SAT to DistinctPair. For a malformed Coverage source input use the two-Halt $R_0,R_1$ table at cap zero, which fails Coverage on an actual $R_2$ source. For a malformed DistinctPair source input use a fixed table with entry zero a Halt storing $R_0$ and entry one an empty-literal self-loop Read, with all four successors itself, at cap zero. Entry one has no good source, so DistinctPair fails. These are total maps for the separate predicate lower bounds. $\square$

## 11. Literally fixed acquired tables and finite cap saturation

**Theorem 11.1 (fixed acquired-selector cap language).** For a literally fixed finite $T$ and literally fixed original entries, with only binary $L$ varying, SOME-LAWFUL-ACQUIRED-CODE is in P. Its well-formed cap language is either empty or $L\ge\lambda$ for one fixed integer $\lambda\le|Q_T|$.

Proof. Put $q=|Q_T|$. On one stationary source every halting entry path uses at most $q$ calls by Lemma 3.4. Hence each good predicate depends only on $\min(L,q)$, as do Coverage, DistinctPair and selector existence. The finite exact criterion of Lemma 9.2 and Theorem 9.3 determines each of the $q+1$ answers for caps $0,\ldots,q$. For a literally fixed table these are fixed constants that can be built into a decider; no uniform polynomial preprocessing bound is asserted. Selector existence is monotone in the cap, since any code that works at $L$ still works at a larger cap. Thus either all answers are negative or there is a least positive $\lambda\le q$ and every larger cap is positive. Binary syntax and comparison with a fixed integer take polynomial time in the cap encoding length. If entries are allowed to vary only among the finite states of this literally fixed table, there are constantly many possible entry pairs; the same P conclusion follows. This result has no varying preparer input. $\square$

**Proposition 11.2 (exact fixed-table thresholds).** For the original $T_8$ entries the acquired-selector threshold is two. For the separately specified $T_{10}$ entries it is four.

Proof. On any $\Pi_2$ source, entry zero of $T_8$ needs two calls to reach $H_2$, while entry one emits the wrong $R_4$. Thus at caps zero or one Coverage fails. At cap two the baseline of Lemma 8.2 is a lawful acquired computation of the root types, selects good entries everywhere and attains both bits. Monotonicity gives exactly the threshold two.

On any $\Pi_4$ source both $T_{10}$ entries need four paid calls to reach $H_4$. At smaller caps neither is good, so Coverage fails. At four both are good everywhere by Lemma 7.2. Choose any two actual distinct tuples, for example the $Z_*$ witness and a $\Pi_1$ witness, and assign the two bits by whole-tuple exceptions with a good default. Theorem 9.3 supplies a lawful both-attained acquired computation. Thus the threshold is exactly four. These are fixed-table consequences of the displayed transitions, not additional independent novelty claims. $\square$

**Convention 11.3 (different inputs and retained edge cases).** Fixed-serving-table validation in §§7–8 still varies the arbitrarily large explicit preparer $A$ and binary $P$. Literally fixed-table acquired selection in Theorem 11.1 varies only $L$. Consequently the latter P result does not weaken the former DP-completeness result for fixed $T_{10}$. The variable-table acquired-selector reduction of §10 has its own scope.

Initial Halts, final-call Halts, empty CNFs, empty clauses, empty suffix menus, unused states and duplicate records retain their exact meanings in every construction. All cap fields are original binary upper budgets. No proof iterates through an exponentially large numeric cap for membership. Sourcewise no-revisit neither removes unused records nor makes the union of all source paths acyclic. A bound on certificate nodes is not an imposed bound on actual sources.

## 12. Credited reuse, additional deductions and remaining boundaries

**Attribution 12.1 (sources and mathematical ownership).** This source uses the following supplied mathematical owners. Their cited upstream ownership is retained through these sources; no nested source or external primary validation is needed for the exposed proofs.

| Owner | Exact reuse |
| --- | --- |
| FCS, *Finite-reader compatibility and lawful binary-code synthesis*, §§1–3; BPS, *Bounded native preparer synthesis and linear literal normalization*, §§1–3; POC, *Native polynomial actual-origin certificates and quantified synthesis bounds*, §§1–3 | Finite ordered algebra and native four replies; disjoint image inverse; full actual inverse fiber; six whole-distinct roles and repeated partners; all eleven profiles and five complete outputs; explicit immutable state-only apparatus, original labels, selected-entry semantics and separate paid services |
| FCS's NBP/PCA/TCR supplier attribution; BPS and POC supplier maps | Original native ownership belongs to *Native cut-birth provenance and literal past-row recovery*, *Native prescribed-code acquisition on the original one-image fiber*, and the named table-driven root-normalization suppliers within their stated scopes. Their results are not claimed as newly invented here. |
| BPS §§4–5 and §10; POC §§4–6 | Exact disjoint four-type recurrence, capped sums/products, finite witness retention, acyclic structural interning and actual-origin semantic certificates; one-origin $300(s+2)$ and two-origin $1200(s+2)$ bounds; cross-origin equality-matrix preservation and polynomial verification |
| FCS §§4–6; POC §8 | Exact finite attained prefix partition, singleton versus countably infinite cell multiplicities, lawful acquired defaults and whole-tuple exceptions, Coverage/DistinctPair equivalence and its membership consequences |
| FCS §9; BPS Lemma 3.4; POC Lemma 6.2 | Stationary sourcewise no-revisit, selected paths, binary-cap verification and the uncapped termination substitution |
| POC Theorems 7.2 and 8.3 | NP/coNP/DP upper bounds reused in the completeness results; those memberships are not separately packaged as new classification content |
| FCS Definition 10.1 and POC Proposition 11.1 | Original unchanged eight-state table and its compatible baseline |
| BPS §§6–10; POC §§9–10 | Linear literal-only normalization, SAME-budget transfer and bounded SOME-preparer synthesis and quantified/oracle ceilings, retained at their original scopes |
| Mature complexity and finite combinatorics | CNF SAT NP-completeness is an explicitly credited premise; complementation, paired reductions, DP's language-intersection definition, finite matching and augmenting paths, finite-term induction and deterministic compilation are classical methods |

The FCS/BPS/POC titles and section references above identify the supplied bodies. The BPS reference is [BPS]. These references establish the bounded provenance of reuse rather than an external literature survey. All new deductions are designated `repo-derived` ordinary mathematics; no `suspected-novel` or literature-wide priority claim is made.

**Attribution 12.2 (exact additional content).** The substantive additional step in §4 is to impose only each role's actual observational constraints, retain six exact witnesses per role/type, and prove that arbitrary such lists preserve the existence of a six-way distinct representative system. Global semantic matching, the eleven actual profiles and actual inverse reconstruction turn this into a polynomial exact JOINT-ATTAIN decision and witness construction without guessing cross-role responses or enumerating an exponential response inventory.

Sections 6–8 construct actual-source Boolean banks and all-source literal CNF graphs, then independently encode SAT-controlled bit attainment and UNSAT-controlled universal success. They establish NP-complete BOTH, coNP-complete UNIVERSAL and DP-complete FULL, including the separately specified fixed $T_{10},L=4$ slice. The unchanged $T_8,L=2$ slice is separately coNP-complete because universal success already forces BOTH. Section 10 gives a different immutable serving-table reduction independently controlling Coverage and DistinctPair and proves variable-table acquired-selector DP-completeness. Section 11 supplies the fixed-table cap consequence and exact thresholds, without presenting these elementary fixed-table consequences as separate inventions. These developments follow the supplied native complexity proposal with complete definitions, proofs and exact encoding boundaries here.

**Convention 12.3 (synthesis, programs and resources).** No hardness theorem for bounded SOME-preparer synthesis follows from validation hardness. POC's unary-$N$ $\Sigma_2^P$ existence ceiling, $\mathrm{FP}^{\Sigma_2^P}$ constructive oracle ceiling, direct exponential-time/polynomial-space specification and separate binary-$N$ one-alternation exponential ceiling remain upper bounds. The fixed-skeleton variant retains its own supplied upper bounds. No synthesis completeness, binary-$N$ polynomial-hierarchy bound, optimal constants or hierarchy collapse is proved.

A polynomial certificate DAG need not have a polynomial unfolding. Neither semantic interning nor inverse parsing is a native runtime privilege. No theorem here provides polynomial native memory, physical time/energy, a polynomial-size arbitrary acquired-selector program, a free determining menu or a bounded native implementation of an acquired selector. All acquisition, representation, producer constants and workspace, local computation, authentication, installation, literals and whole-output storage, export, isolation, handoff, faithful entry and authentic stationary native service retain their separate permissions and prices.

The explicit finite input contract must actually be supplied. No finite configuration space or literal table is extracted from arbitrary program text with hidden workspace or computed addresses. FCS's undecidability of checking an independently supplied code under totality, both-attainment and finite-preparability promises is not a finite-table hardness substitute and is unaffected. SOME acquired selection, bounded native generation and verification or recovery of a prescribed pointwise code are different problems. The present source establishes no kernel result, implementation, empirical machine-learning result, physical realization, exhaustive external originality result or completion of the broader programme. Independent delivery acceptance is not implied by the presence of these ordinary proofs.

[BPS]: FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md

## 追加锚（本行以下为增补区）
