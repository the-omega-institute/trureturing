# Contingent zero forcing at fixed cycle rank

## 1. Graphs, faults, and published intermediates

**Definition 1.1 (domain and forcing rule).** Let $G=(V,E)$ be a finite nonempty connected simple undirected graph, with $V=[n]=\{1,\ldots,n\}$, $m=|E|$, and cycle rank $q=m-n+1$. Let $k\geq1$ be an integer. A placement is a set $S\subseteq V$ chosen before any faults. Given $F\subseteq E$, ordinary zero forcing in $G-F=(V,E\setminus F)$ starts with exactly $S$ blue. A move $u\to v$ is legal when $u$ is blue and $v$ is its unique white neighbor in $G-F$. The placement is $k$-contingent if

$$
 \forall F\subseteq E\quad |F|\leq k\quad
 \exists\text{ a legal sequence from }S\text{ coloring every vertex of }G-F.
 \tag{1.1}
$$

The sequence can depend on $F$; $S$ cannot. Write $z_k(G)$ for the least size of such a placement. The set $V$ is always feasible, so this minimum exists. Deleted edges remain absent throughout a sequence; sources must be blue. Disconnected graphs $G-F$ and isolated vertices retain their original vertex labels.

This is the definition in Aksoy, Petyuk, Roy, and Young, “$(n-k)$-contingent Zero-Forcing for Power Grids,” in *Seven open problems in applied combinatorics*, [arXiv:2303.11464v1](https://arxiv.org/abs/2303.11464v1), `Sections/zero-forcing.tex`, definition of contingent zero forcing. Its $Z$ is our $S$ and its $E'$ is our $F$. The $n$ in the published name is not an additional restriction on $k$ in (1.1). Here arbitrarily long positive binary integers $k$ are allowed.

**Definition 1.2 (boundary statistic and mandatory vertices).** For $W\subseteq V$, put

$$
 \partial_1^G(W)=\{u\in V\setminus W:|N_G(u)\cap W|=1\},
 \qquad b_G(W)=|\partial_1^G(W)|,
 \qquad D_k(G)=\{v:\deg_G(v)\leq k\}.
 \tag{1.2}
$$

For a placement $S$, define

$$
 \lambda_G(S)=\min_{\varnothing\ne W\subseteq V\setminus S}b_G(W),
 \tag{1.3}
$$

with minimum of the empty family $+\infty$. Thus $\lambda_G(V)=+\infty$. An ordinary fort is a nonempty $W$ with $b_G(W)=0$. An $\ell$-leaky fort is a nonempty $W$ with $b_G(W)\leq\ell$. A vertex leak prohibits that vertex from acting as a source; it does not prevent the vertex from becoming blue.

The leaky-fort condition is the one in Bjorkman, Cao, Kenter, Moruzzi, Reinhart, and Vasilevska, *Leaky Forcing: Extending Zero Forcing Results to a Fault-Tolerant Setting*, [arXiv:2508.02564v1](https://arxiv.org/abs/2508.02564v1), §2, Proposition 2.5 and its preceding definition; the proposition says that an $\ell$-leaky forcing set meets every nonempty $\ell$-leaky fort. The same local condition and intersection criterion occur in Moruzzi, Shah, and Tripathi, *Leaky Zero Forcing on Subgraphs of d-dimensional Grid Graphs with an Application to Diamond Rectangles*, [arXiv:2509.21529v3](https://arxiv.org/abs/2509.21529v3), Definition 5 and Proposition 6. Nonemptiness is explicit here; the empty set is never an obstruction.

**Definition 1.3 (published tree intermediate and ordinary closure correspondence).** The tree intermediate used below is Alameda, Kritschgau, Warnberg, and Young, *On leaky forcing and resilience*, [arXiv:2008.06552v1](https://arxiv.org/abs/2008.06552v1), Theorem 4.4: for a tree $T$ and $\ell\geq1$, the vertices of degree at most $\ell$ form an $\ell$-leaky forcing set. It is consumed with exactly $\ell=k$, on a spanning tree with the original vertex set. For $1\leq k\leq|V(T)|$, any set of fewer than $k$ prohibited sources can be extended to a set of exactly $k$ sources; a successful sequence avoiding the latter also avoids the former. Thus the exact-leak and at-most-leak conventions agree in this range. For $k\geq|V(T)|$, every vertex is already in that degree set, so no convention about choosing more leaks than vertices is needed. The single-vertex tree is also handled directly. The leaky-fort intersection criterion in Definition 1.2 then gives, for every nonempty $W$ disjoint from those tree vertices, $b_T(W)>k$. No tree result is asserted as a new theorem here.

For ordinary closure, the repository sources at revision `122c987d276498783de7d873378a28b27ced8761` provide the following intermediates. In `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.lean`, the inductive `Black`, `IsZeroForcing`, `Black.mono`, and `IsFort.not_black_of_disjoint` respectively give blue-source closure, success, monotonicity in the initial blue set, and the impossibility of entering a disjoint fort. The definition `IsFort` in `ZeroForcingThreeFinite.lean` is exactly nonemptiness together with $b_G(W)=0$. Their graph parameter is our simple graph, their initial finite set is our $S$, and their fort is our $W$; all of these statements used here have arbitrary finite vertex types. On a finite graph, the inductive closure agrees with chronological forcing: repeatedly take a legal move until none exists; the resulting closed set contains every inductive derivation by induction on its constructors, while each move is itself an inductive derivation. This also identifies the closure with every terminal exhaustive sequence.

## 2. A bounded enlargement and the exact minimum formula

**Theorem 2.1 (minimum placements by a bounded enlargement).** Choose any spanning tree $T=(V,E_T)$ of $G$. Set

$$
 J=E\setminus E_T,\qquad
 X=\bigcup_{e\in J}e,\qquad r=|X|\leq2q,\qquad D=D_k(G).
 \tag{2.1}
$$

For every $k\geq1$ and every $G$ in Definition 1.1,

$$
 S\text{ is }k\text{-contingent}\quad\Longleftrightarrow\quad
 \lambda_G(S)>k,
 \tag{2.2}
$$

and

$$
 D\subseteq S\text{ for every feasible }S,\qquad
 |D|\leq z_k(G)\leq |D|+|X\setminus D|\leq |D|+2q.
 \tag{2.3}
$$

More precisely, define the finite family

$$
 \mathcal U=\{U\subseteq V\setminus D:|U|\leq2q,
                         \ \lambda_G(D\cup U)>k\}.
 \tag{2.4}
$$

It is nonempty, and

$$
 z_k(G)=|D|+\min_{U\in\mathcal U}|U|.
 \tag{2.5}
$$

Every $D\cup U$ attaining (2.5) is an actual minimum placement. The values $\lambda_G(D\cup U)$ are given by the finite recurrence in §3; thus (2.5) together with that recurrence determines the exact cardinality without an oracle for forcing or forts.

*Proof.* First consider an arbitrary $W\ne\varnothing$. To make $W$ an ordinary fort by deleting edges, every $u\in\partial_1^G(W)$ must lose its sole edge into $W$. These are distinct edges: every such edge has a unique endpoint outside $W$. Conversely, delete exactly these $b_G(W)$ edges. An outside vertex originally having zero neighbors in $W$ still has zero; one originally having one now has zero; one originally having at least two loses none of its edges into $W$. The last assertion holds because its own outside endpoint is not in $\partial_1^G(W)$. Hence $W$ becomes a fort. Consequently the minimum number of edge deletions making this fixed $W$ a fort is exactly $b_G(W)$.

If $W$ is disjoint from $S$ and $b_G(W)\leq k$, those deletions leave a disjoint ordinary fort. The fort obstruction in Definition 1.3 prohibits a successful sequence, so $S$ is not feasible. Conversely suppose some $F$, $|F|\leq k$, defeats $S$. Exhaust a sequence in $G-F$; at most $n-|S|$ moves occur, because each move colors a new vertex. Its nonempty remaining white set $W$ is disjoint from $S$ and is a fort in $G-F$. The fixed-set deletion bound just proved gives $b_G(W)\leq|F|\leq k$. This proves (2.2). This argument uses the actual deleted graph, including every disconnected component, and preserves the quantifier order in (1.1).

If $v\notin S$ and $\deg_G(v)\leq k$, deleting all edges incident with $v$ leaves an isolated white vertex. It cannot become blue. Thus $D\subseteq S$ is necessary.

Put $B_T=\{v:\deg_T(v)\leq k\}$. Whenever $v\notin X$, all incident edges of $G$ belong to $T$, so $\deg_T(v)=\deg_G(v)$. Therefore

$$
 B_T\subseteq D\cup X.
 \tag{2.6}
$$

Take any nonempty $W\subseteq V\setminus(D\cup X)$. It is disjoint from $B_T$. By the published tree intermediate and leaky-fort criterion in Definition 1.3, $b_T(W)>k$. Every edge of $J$ has both endpoints in $X$, and $W\cap X=\varnothing$. Thus no edge of $J$ has an endpoint in $W$, so every vertex has exactly the same neighbors in $W$ in $G$ and in $T$. It follows that $b_G(W)=b_T(W)>k$. Equation (2.2) proves feasibility of $D\cup X$. If no such $W$ exists, feasibility follows instead from $D\cup X=V$. When $T$ is a singleton, $D=V$ directly. This proves (2.3) in all cases.

The set $U=X\setminus D$ belongs to $\mathcal U$. Let $S_*$ be a minimum placement. Necessity gives $S_*=D\cup U_*$ with $U_*\subseteq V\setminus D$ and $|U_*|=z_k(G)-|D|$. Bound (2.3) gives $|U_*|\leq2q$, so $U_*\in\mathcal U$. Conversely every member of $\mathcal U$ gives a feasible placement by (2.2). These two implications prove (2.5) and the placement assertion. $\square$

The deletion/leak equivalence behind (2.2) is also a published intermediate, not a claim of priority: compare [arXiv:2303.11464v1](https://arxiv.org/abs/2303.11464v1), `Sections/zero-forcing.tex`, Lemma `L:equiv`, and Abbas, *Resilient Strong Structural Controllability in Networks using Leaky Forcing in Graphs*, [arXiv:2303.02366v1](https://arxiv.org/abs/2303.02366v1), Definitions 7–9 and Theorem 4.4. Here the direct fixed-set deletion argument supplies the correspondence for all binary $k$, including $k>n$ and $k>m$. Prohibiting use of specified edges leaves their adjacency constraints present, whereas deleting edges changes those constraints; these operations are not interchanged step by step. Alameda, Kritschgau, and Young, *Generalizations of leaky forcing*, [arXiv:2009.07073v1](https://arxiv.org/abs/2009.07073v1), §2 and Corollary 2.4, concern the former operation. The contribution of (2.3)–(2.5) is the bounded enlargement relative to degrees in the original graph and its combination with the recurrence below.

## 3. An exact finite recurrence for the obstruction minimum

**Definition 3.1 (saturation and tree coordinates).** Fix $T,J,X$ from (2.1) and a placement $S$. List $X$ in increasing vertex order. Root $T$ at vertex $1$, and order each list of children increasingly. Let $V_v$ be the vertices of the subtree rooted at $v$. Write

$$
 [a]_2=\min(2,a)\quad(a\in\mathbb N),\qquad
 a\oplus b=[a+b]_2.
 \tag{3.1}
$$

Vectors with coordinates in $\{0,1,2\}$ are added by $\oplus$ coordinatewise. The digit $2$ means “at least two”, not “exactly two”. For nonnegative integers,

$$
 [[a]_2+b]_2=[a+b]_2,
 \qquad a=1\Longleftrightarrow[a]_2=1.
 \tag{3.2}
$$

These identities follow by separating $a=0,1$ from $a\geq2$, and justify every saturation below.

Enumerate all functions $\sigma:X\to\{0,1\}$ with $\sigma(x)=0$ for $x\in X\cap S$. A binary assignment $w:V\to\{0,1\}$ represents $W=\{z:w_z=1\}$. Only assignments satisfying $w_z=0$ for $z\in S$ and $w_x=\sigma(x)$ for $x\in X$ are admitted. Define the fixed chord contribution

$$
 d_\sigma(x)=\left[\sum_{xy\in J}\sigma(y)\right]_2\quad(x\in X).
 \tag{3.3}
$$

For each $v$, a parent bit $p\in\{0,1\}$ is the prescribed membership bit of its parent; at the root use $p=0$. The vertex bit is $b\in\{0,1\}$. An internal-neighbor vector $a\in\{0,1,2\}^X$ and a nonemptiness bit $h\in\{0,1\}$ have meanings

$$
 a_x=\left[\sum_{\substack{xy\in E_T\\x,y\in V_v}}w_y\right]_2,
 \qquad h=\max_{z\in V_v}w_z.
 \tag{3.4}
$$

An empty sum is zero. In particular $a_x=0$ if $x\notin V_v$. The table $A_v(p,b,a,h)$ is the minimum of

$$
 \sum_{z\in V_v\setminus X}(1-w_z)
       \mathbf1\!\left\{\sum_{y\in N_T(z)}w_y=1\right\}
 \tag{3.5}
$$

over the admitted assignments on $V_v$ with $w_v=b$, vector and bit (3.4). If $z=v$, its possible parent contributes $p$ in (3.5). Every other neighbor occurring in (3.5) is inside $V_v$. For the root the nonexistent parent contributes zero. Set an impossible entry to $+\infty$. A vertex bit is allowed precisely when it respects $S$ and, at vertices of $X$, $\sigma$. Costs at vertices in $X$ are deliberately omitted from (3.5) and will be charged once at the end.

**Definition 3.2 (explicit evaluation of the tables).** Process vertices after all their children. For each $p$ and allowed $b$, initialize an accumulator $H$ indexed by

$$
 (t,a,h)\in\{0,1,2\}\times\{0,1,2\}^X\times\{0,1\}
$$

with value zero at $(0,0,b)$ and $+\infty$ elsewhere. Here $t$ records the saturated sum of the bits of processed children. Process the children $u$ in their fixed order. For every finite old accumulator entry $H(t,a,h)$ and every finite child entry $A_u(b,c,a',h')$, form

$$
 \begin{aligned}
 e_x&=\mathbf1\{x=v\in X\}\,c+\mathbf1\{x=u\in X\}\,b,\quad x\in X,\\
 \widehat t&=t\oplus c,\qquad
 \widehat a=a\oplus a'\oplus e,\qquad
 \widehat h=\max(h,h').
 \end{aligned}
 \tag{3.6}
$$

In a fresh accumulator at $(\widehat t,\widehat a,\widehat h)$ keep the least value of $H(t,a,h)+A_u(b,c,a',h')$ among all such pairs. Unreached entries are $+\infty$. Replace the old accumulator by the fresh one. After the last child, put

$$
 A_v(p,b,a,h)=\min_{t\in\{0,1,2\}}
 \left(H(t,a,h)+\mathbf1\{v\notin X,\ b=0,\ p+t=1\}\right).
 \tag{3.7}
$$

The condition $p+t=1$ is an equality of ordinary integers; $p+t\geq2$ never satisfies it. Disallowed $b$ give only infinite entries. This initialization also specifies the entire leaf computation.

For the root $o=1$, define

$$
 L_\sigma(S)=\min_{b,a}
 \left(A_o(0,b,a,1)+
  \sum_{x\in X}(1-\sigma(x))\mathbf1\{a_x\oplus d_\sigma(x)=1\}\right),
 \qquad L(S)=\min_\sigma L_\sigma(S).
 \tag{3.8}
$$

The condition $h=1$ is required. Empty sets are excluded even when they would have zero cost. Infinite entries are ignored in minima, and an entirely impossible minimum stays infinite.

**Theorem 3.3 (exactness and attainment of the recurrence).** For all $G,k,T,S$ in the stated domain, (3.6)–(3.8) terminate and give

$$
 L(S)=\lambda_G(S).
 \tag{3.9}
$$

Whenever $L(S)$ is finite, it is attained by an admitted nonempty set $W\subseteq V\setminus S$. The saturation loses no information needed to decide feasibility of $S$.

*Proof.* Fix $\sigma$. We prove the table meaning in Definition 3.1 by induction over subtrees, and, inside a subtree, over its processed children. Initially there is only the vertex $v$. It has bit $b$ and hence nonemptiness bit $b$; there are no internal tree edges and no selected child, giving $a=0,t=0$. No cost has yet been charged at $v$.

When a child $u$ is attached, a subtree assignment restricts uniquely to an assignment on the processed part and an assignment on $V_u$, with parent bit $b$ for $u$. Conversely any two such assignments with the same prescribed $b$ combine: the vertex sets are disjoint, all restrictions on $S$ and $\sigma$ are local, and $vu$ is the sole tree edge between them. The two old costs concern disjoint vertices; the cost at $v$ is still deferred. The new sum of child bits is given by $t\oplus c$, and nonemptiness by $\max(h,h')$.

For a coordinate $x\in X$, all newly internal edges are the old internal edges, the edges internal to $V_u$, and $vu$. The edge $vu$ contributes $c$ to the selected-neighbor count of $v$ if $v\in X$, and $b$ to that of $u$ if $u\in X$. These are exactly the two terms in $e_x$; if neither endpoint is in $X$, there is no vector contribution. Thus (3.6) gives precisely (3.4). This remains true when both endpoints lie in $X$: the two contributions occupy their two different coordinates. Identity (3.2) makes repeated saturation equivalent to saturating the complete sum.

It follows that every pair considered by the recurrence produces an admitted assignment of the new state, and every admitted assignment arises from a considered pair. Retaining a least cost therefore retains exactly the minimum for that state. Replacing one partial assignment by a cheaper one of the same state does not change any subsequent transition or final vertex charge, since those depend only on the displayed indices and the fixed bits. This proves the induction over children.

After all children, every $z\in V_v\setminus(X\cup\{v\})$ has already been charged correctly in its own subtree. If $v\notin X$, it has no incident edge of $J$, since both endpoints of every such edge belong to $X$. Its neighbor count in $G$ is therefore its tree neighbor count, namely its parent bit plus the sum of child bits. The indicator that this count is one is exactly the condition $p+t=1$, by (3.2). Its cost is one precisely when it is also outside $W$, namely $b=0$. Equation (3.7) supplies this remaining charge. If $v\in X$, no charge is due yet. This proves (3.5) and the subtree induction, including leaves and the root.

At the root, every tree edge is internal. Thus $a_x$ is the saturated count of all selected tree neighbors of $x$. All other neighbors of $x$ come through $J$, with contribution (3.3). The sum in (3.8) charges exactly the outside vertices in $X$ with one selected neighbor. All outside vertices not in $X$ have already been charged in (3.5). Their combined charge is consequently exactly $b_G(W)$, and the root condition $h=1$ is equivalent to $W\ne\varnothing$. Enumerating $\sigma$ enumerates every possible restriction of $W$ to $X$. This proves (3.9).

All choices range over finite sets; table operations use minima of finite lists. Finite entries at initialization are attained, and each finite update combines two attaining assignments. Induction therefore proves attainment of every finite entry and root minimum. A rooted tree has finitely many vertices and child edges, so all loops terminate. For reconstruction, retain one attaining pair whenever an entry is improved, choosing the first pair in the fixed order on ties; recursively following these pairs recovers the bits of an attaining $W$. Alternatively recompute the same finite minima when a witness is needed. No count larger than two affects an equality to one, which proves the last assertion. $\square$

## 4. Uniform exact placement algorithm and bit cost

**Definition 4.1 (representations and finite procedure).** A nonnegative integer $a$ is encoded as follows: let $s\geq1$ be the length of its usual binary expansion, with zero represented by the single bit $0$; write $s$ ones, a zero delimiter, and then its $s$ binary bits. An input consists of the encodings of $n$ and $m$, the list of $m$ edges, then the encoding of $k$. Each edge is an ordered pair $i<j$ of vertex labels represented by exactly $w=\lceil\log_2(n+1)\rceil$ bits each; pairs are in increasing lexicographic order and have no duplicates. The graph is promised to satisfy Definition 1.1. All bits, including all bits of $k$ and its length prefix, belong to the full input length $L$. The output is the encoding of $z_k(G)$ followed by the $n$-bit characteristic vector of one minimum placement in increasing vertex order. In particular the output specifies the placement, not just its size.

Read the entire input. While reading the value bits of $k$, compute $K=\min(k,n)$ by replacing each running binary prefix $a$ by $\min(n,2a+d)$ on the next bit $d$. Compute the degrees, and set $D=\{v:\deg_G(v)\leq K\}$. If $D=V$, output $(n,V)$. Otherwise choose a spanning tree by exploring from vertex $1$, always considering neighbors in increasing label order, and form $J,X$ and the root and child order of §3. For $j=0,\ldots,\min(2q,|V\setminus D|)$ in order, list the $j$-element subsets $U$ of $V\setminus D$ by increasing tuples. Evaluate (3.8) for $S=D\cup U$, and stop at the first one for which $L(S)>K$. Output $(|D|+j,D\cup U)$. This specifies one procedure with $q$ computed from the input; a separate algorithm is not supplied for each $q$.

**Theorem 4.2 (full-domain correctness, optimality, and finite bit bound).** The procedure in Definition 4.1 terminates on every input in its promised domain and returns exactly $z_k(G)$ and an attaining placement for (1.1). On a deterministic multitape Turing machine with binary work tapes there is an implementation of this procedure with time

$$
 O\!\left((2q+1)^6\,2^{2q}\,81^{2q}\,(L+2)^{2q+12}\right)
 \tag{4.1}
$$

bit operations and work storage

$$
 O\!\left((2q+1)^2\,3^{2q}\,(L+2)^4\right)
 \tag{4.2}
$$

bits, with absolute implied constants independent of $G,k,q,L$. Input reading, integer arithmetic, table access, choice of an actual placement, and output are included. For every fixed $q$, (4.1) is polynomial in the entire input length, even when the binary value $k$ is larger than $m$, $n$, or every polynomial in $n$.

*Proof.* Since $G$ is connected, one can explore it to obtain a spanning tree: begin with vertex $1$, add an edge from the explored set to a new vertex whenever that set is not all of $V$, and retain its first such edge as the parent edge. Connectivity guarantees such an edge; adding a new vertex cannot create a cycle. There are $n-1$ parent edges, so $|J|=m-n+1=q$ and $r\leq2q$. Increasing-neighbor exploration fixes all choices finitely.

For each prefix of the value bits of $k$, saturation at $n$ equals the minimum of that prefix value and $n$, as follows by induction from $\min(n,2\min(n,a)+d)=\min(n,2a+d)$. Hence $K=\min(k,n)$ after the entire value has been read. Every graph degree is at most $n-1$, so the computed $D$ equals $D_k(G)$. If $K=n$, every vertex is mandatory and output $(n,V)$ is exact. If $D=V$ for a smaller $K$, the same argument applies. Otherwise $K=k<n$. Thus every later comparison $L(S)>K$ is exactly the comparison in (2.2); no value of $k$ has been silently truncated in a nontrivial case.

By Theorem 3.3 the evaluation is exact. By Theorem 2.1 at least one $U$ in the enumerated range succeeds. Every feasible placement contains $D$ and some minimum placement has at most $2q$ further vertices. Because cardinalities $j$ are tried in increasing order, the first successful $U$ therefore has minimum possible size. It is stored explicitly as its increasing tuple, so its union with $D$ is the required actual minimizer. Every loop is finite, and some successful candidate is reached, proving termination and correctness.

We give a deliberately generous bit bound, including a sequential simulation of table access. Put $N=L+2$. The explicit edge list and connectivity imply $m\geq n-1$, so $n\leq L+1<N$; also $m\leq L<N$ because every edge occupies at least two bits. All vertex, edge, degree, and subtree indices use $O(\log N)$ bits. Input parsing, reading the whole prefix and value of $k$, saturated binary arithmetic, degree calculation, and construction of an adjacency matrix can be performed by repeated scans in $O(N^4)$ bit steps and $O(N^3)$ bits. For example, store the input on a tape, keep counters of at most $L+1$, and scan edge records to find any requested adjacency or degree; at most a quadratic number of such scans suffices. Alternatively the matrix has at most $n^2$ entries. The unary length prefix is read completely; no operation loops up to the value of $k$. The exploration and the sorting of the resulting child lists, even using repeated minimum selection, fit these same generous bounds.

Fix $S$ and $\sigma$. The number of states of $A_v$ is at most $8\cdot3^r$ and the number of accumulator states is at most $6\cdot3^r$ for fixed $p,b$. For a fixed parent bit and vertex bit, a child table has at most $4\cdot3^r$ entries, since its parent bit is then fixed. Consequently a child update considers at most a constant times $9^r$ pairs, and each pair requires $O(r+1)$ coordinate operations and a bounded number of cost additions and comparisons. There are $n-1$ child updates and four possible $p,b$ pairs. Initialization, (3.7), and the root evaluation use at most a constant times $n(r+1)9^r$ further elementary operations. Computing (3.3) requires at most $O((r+1)(m+1))$ elementary operations. Here an elementary operation reads or writes a record, compares bounded integers, or performs their addition, saturation, or binary counter update.

Every finite partial cost is at most $n$: costs count outside vertices in disjoint processed parts and possibly the current vertex. The final cost has this bound as well. Encode $+\infty$ by a separate flag; do not allow flag arithmetic to produce a finite value. A record, its coordinates, its address, and all numerical operands have at most $O(r+\log N+1)$ bits. In particular table indexing, including an index in $\{0,1,2\}^X$, does not assume constant-size machine words.

All complete subtree tables can be stored simultaneously, together with two accumulators and the input, graph, candidate tuple, and loop counters, in at most

$$
 M=C_0(r+1)3^rN^3
 \tag{4.3}
$$

bits for an absolute $C_0$, enlarged once if necessary. Indeed the tables require $O(n3^r(r+\log N+1))$ bits; all other listed objects require only a polynomial in $N$ of degree at most three. Reuse the same space for every $\sigma$ and candidate. No table for a previous candidate is retained, and the placement algorithm needs no witness backpointers. The list of all candidates or all $\sigma$ is never stored.

To justify a bit cost without a unit-cost random-access assumption, encode records consecutively on work tapes with their addresses and use a full sequential scan for each access. Comparing addresses, copying records, and binary addition or comparison can all be implemented by the usual left-to-right or right-to-left digit scans. With at most $M$ stored bits, even allowing a fresh scan of length $M$ for each compared or copied digit costs $O(M^2)$ bit steps per elementary operation. Arithmetic with at most $M$ operand bits also costs at most $O(M^2)$ using digit-by-digit addition, comparison, and multiplication if needed. Our recurrence needs only addition and comparison; base-three coordinate indices can instead be enumerated as strings. Thus this simulation is a concrete upper bound on access and arithmetic, rather than an assumption of instantaneous table lookup.

For the fixed candidate and $\sigma$, the elementary-operation count above is at most

$$
 C_1(r+1)^2\,9^rN^3.
 \tag{4.4}
$$

Combining (4.3), (4.4), and the scan simulation gives a time bound

$$
 C_2(r+1)^4\,81^rN^9.
 \tag{4.5}
$$

There are at most $2^r$ assignments $\sigma$, including the restrictions imposed by $S$. They can be generated with an $r$-bit counter. For candidate enumeration, use increasing tuples and lexicographic succession. At most

$$
 \sum_{j=0}^{\min(2q,|V\setminus D|)}\binom{|V\setminus D|}{j}
 \leq (2q+1)N^{2q}
 \tag{4.6}
$$

candidates are visited. Each next tuple, candidate bit vector, and union with $D$ can be formed by bounded scans and binary counters in $O((2q+1)N^3)$ bit steps, using at most $O(N^3)$ bits; a tuple never has more than $n$ entries. These costs and rebuilding the candidate-dependent tables fit the product of (4.5), $2^r$, and (4.6), or the larger bound (4.1), also when $q=0$. Substituting $r\leq2q$ in (4.3), and allowing the same scans and loop counters, gives (4.2). The extra powers of $N$ and $2q+1$ in (4.1)–(4.2) cover all preprocessing and enumeration overhead just described.

Finally, reconstruction of the placement requires only the current tuple $U$ and the stored characteristic vector of $D$, not an exponential search through past table choices. A scan emits the $n$ membership bits and counts them using $O(\log N)$-bit arithmetic. Encoding the resulting cardinality has $O(\log N)$ bits. Both reconstruction and output use $O(N^3)$ time within (4.1). This proves the claimed full-input bit and storage bounds. $\square$

## 5. Endpoints, forcing witnesses, and mathematical scope

**Proposition 5.1 (endpoints and recovery after a specified fault).** The algorithm and formula include the following cases. For a singleton, $z_k(G)=1$ with unique placement $V$. Whenever $k\geq\Delta(G)$, $z_k(G)=n$ with unique placement $V$. When $q=0$, the unique minimum placement is $D_k(G)$, of size $|D_k(G)|$. For any graph in the domain and the returned placement $S$, a successful chronological sequence for any subsequently supplied $F\subseteq E$, $|F|\leq k$, can be recovered in polynomial bit time in the explicit graph and fault-list lengths. Such a sequence need not be included among the outputs in Definition 4.1.

*Proof.* For a singleton the only vertex is mandatory, since its degree is zero, and there is no move that can color an initially white isolated vertex. If $k\geq\Delta(G)$, every vertex is in $D_k(G)$, so necessity in (2.3) proves the assertion, even for $k>m$. If $q=0$, $J=X=\varnothing$, and (2.3) forces equality with $D_k(G)$ and uniqueness. This tree endpoint is precisely the published tree intermediate from Definition 1.3, expressed in the deletion model by (2.2), rather than a separate new tree formula.

For the final assertion, delete the listed edges in an adjacency matrix. Starting with $S$, repeatedly scan all blue vertices and count their white neighbors. If a vertex has exactly one, append its force and color its target blue. If there is no such source, stop. Each successful iteration colors a new vertex, so there are at most $n$ successful iterations and one final scan. Each scan uses at most $n^2$ adjacency and color tests, with labels and counters of $O(\log(n+1))$ bits. Even sequential tape storage and repeated scans give a polynomial bit bound, and the force list has at most $n-|S|$ pairs of labels. If the procedure stopped with a white set $W\ne\varnothing$, it would be a fort in $G-F$ disjoint from $S$, and the first part of the proof of Theorem 2.1 would yield $b_G(W)\leq|F|\leq k$. This contradicts $\lambda_G(S)>k$. It therefore stops with every vertex blue and returns a valid sequence. The argument allows different orders for different $F$ and makes no claim that a single fixed order survives all faults. $\square$

**Definition 5.2 (parameter correspondence and scope of the inference).** The parameter $q$ throughout is the cycle rank $m-n+1$, not a number of leaves, a girth, the number of all simple cycles, or a bound on the fault budget. The $q$ used for the number of leaves in the unicyclic formulas of [arXiv:2508.02564v1](https://arxiv.org/abs/2508.02564v1), Theorems 3.6–3.7, is unrelated to our $q$; its leak parameter $\ell$ corresponds to our $k$. That paper already supplies leaky cardinality classifications on unicyclic graphs in Theorems 3.6–3.9. The definitions in §2 of that paper and the bridge in Theorem 2.1 specify the relevant model correspondence. The tree cardinality formulas and the fort intersection criterion are likewise attributed intermediates, not separate contributions of this volume.

The inference proved here combines the bound of $2q$ on the number of additional vertices above the original-graph mandatory set with a saturated-neighbor recurrence that computes the obstruction minimum and hence finds an actual optimum. The enumeration has exponent depending on $q$, while the fault budget is arbitrary input. The displayed time bound is a uniform fixed-parameter-slice polynomial bound; it does not assert a bound of the form $f(q)L^c$ with $c$ independent of $q$. The cited versions delimit the attribution; they do not establish worldwide absence or priority for the combined result.

The graph statements and bit bounds concern exactly the explicit finite encoding in Definition 4.1. A succinctly described graph with exponentially many vertices is a different input model, since even the characteristic-vector output can then have exponential length. Directed graphs, multigraphs, vertex deletions, white sources, time-varying faults, and faults occurring before the choice of $S$ have different definitions and are not substituted into (1.1). The bounds do not assert a typical size for a random graph family or any physical controllability or observability conclusion. The two few-cycle questions following Lemma `L:equiv` in [arXiv:2303.11464v1](https://arxiv.org/abs/2303.11464v1), `Sections/zero-forcing.tex`, motivate the cycle-rank parameterization; sparse large-diameter families with unbounded cycle rank and typical power-grid size questions require additional mathematical hypotheses and results.

## 追加锚（本行以下为增补区）
