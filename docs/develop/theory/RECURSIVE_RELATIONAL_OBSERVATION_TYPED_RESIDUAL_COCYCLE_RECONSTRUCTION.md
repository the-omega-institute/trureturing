# Recursive relational observation: typed residual cocycles and ordered-path reconstruction

The question is whether a final residual and an accumulated duration determine an executed ordered path. The carrier is one actual deterministic source image, with its declared types, legal operations and complete continuation responses. Completeness concerns those responses; it does not identify a residual with the source's entire past. The criterion below applies to all finite legal words from one fixed root.

## 1. One actual image and its complete residual graph

**Definition 1.1 (typed deterministic source).** Fix a type set $I$, actual source images $X_i$ and a typed alphabet of named operations $a:i\to j$. For each operation fix a legal domain $D_a\subseteq X_i$, a deterministic successor $T_a:D_a\to X_j$ and a complete declared output record $\ell_a(x)$ for each $x\in D_a$, which may contain state-dependent output, failure and reason fields. Fix the current declared readout $q_i$ on $X_i$. Every legal successor belongs to the same actual source image. These images are not replaced by a product of independently possible record fields.

Operation parameters belong to the name. An absent operation is illegal, rather than an executed failure. An executed failure with a successor is a legal transition whose output includes the failure tag and reason. A terminal outcome has its declared terminal type and no further transitions. Choosing to stop after a finite word is not an additional edge unless Stop itself belongs to the operation alphabet.

For every finite type-compatible operation word $u$, let $\operatorname{Resp}(x,u)$ retain the ordered declared records, all encountered legality and outcome distinctions, and the declared readouts at the successive cuts. In particular, a legal failure, an illegal attempt and normal termination remain distinct. An illegal attempt ends the response at the first missing transition. Records include any source, permission, archive or calibration field required by this fixed observation contract. A record already held by an observer is not erased when a later projection omits it.

This reuses the actual partial-process and writer conventions of [Process Geometry §§1–3](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), its same-source history carrier in §39.1, and its typed actual-image and response bridges in §§41–42. Here $X_i$ and the responses are fixed as part of the mathematical assumptions; no particular physical source is supplied by those conventions.

**Definition 1.2 (complete residual quotient).** The response comparison includes the empty word $\varepsilon_i$, whose response $\operatorname{Resp}(x,\varepsilon_i)$ retains the current declared readout $q_i(x)$. For $x,y\in X_i$, put

$$
x\sim y
\quad\Longleftrightarrow\quad
\operatorname{Resp}(x,u)=\operatorname{Resp}(y,u)
\text{ for every finite type-compatible word }u.
$$

Let $V=\coprod_{i\in I}X_i/{\sim}$, restricted to the fixed actual image, and write $\pi(x)$ for the residual vertex of $x$. The vertex retains its type. Equality of complete responses entails equal legal named menus and equal one-step output records. It also entails

$$
x\sim y,\quad x,y\in D_a
\quad\Longrightarrow\quad T_a x\sim T_a y:
$$

the responses after $a$ agree for every suffix, by comparing the responses to $au$. Consequently, legality and the successor residual descend to $V$.

The graph $G=(V,E,s,t)$ has one edge for each realized pair consisting of a residual vertex $v$ and a legal operation name $a$ at $v$. Its source is $v$ and its target is the successor residual. At a given vertex a given name determines at most one edge. Different names with the same source and target are distinct named parallel edges. Graph degrees count them separately.

A finite legal word in $G$ is an ordered sequence of composable named edges. Its endpoint from $v$ is denoted $v\cdot u$; the empty word $\varepsilon_v$ has endpoint $v$. Execution and concatenation run from left to right:

$$
r\cdot(uw)=(r\cdot u)\cdot w.
$$

Every such graph word lifts to a legal source execution from every representative of its starting residual. Indeed, a realized first edge is legal at every equivalent representative, its successor has the stipulated residual, and induction applies to the remaining word. Conversely, every legal source word projects to a graph word. This uses actual-image closure and residual congruence; realization of individual edges alone would not justify arbitrary concatenations.

**Assumption 1.3 (finite recurrent graph).** The full graph $G$ of this quotient has finitely many vertices and named edges, has at least one edge, and is strongly connected: for every $v,w\in V$ there is a finite directed path from $v$ to $w$. Fix $x_0\in X_{i_0}$ and $r=\pi(x_0)$. Write $\mathcal P_r$ for all finite legal words from $r$, including $\varepsilon_r$.

Strong connectivity concerns the full named-edge graph, not a graph obtained by forgetting some legal operations or merging parallel edges. A terminal vertex with no outgoing edges is incompatible with this assumption.

## 2. Duration on that quotient

**Assumption 2.1 (positive descended duration and cocycle).** Each realized edge has a fixed duration

$$
d:E\longrightarrow\mathbb R_{>0}.
$$

For a source execution of the edge $(\pi(x),a)$, its one-step duration is exactly $d(\pi(x),a)$, independent of the representative $x$. Durations use one declared unit and calibration. This constancy follows if duration is included in the complete one-step response of Definition 1.2; otherwise it is a separate required hypothesis.

For every $v$ and every legal word $u$ from $v$, the accumulated duration $\tau_v(u)$ obeys

$$
\begin{aligned}
\tau_v(\varepsilon_v)&=0,\\
\tau_v(e)&=d(e),\\
\tau_v(uw)&=\tau_v(u)+\tau_{v\cdot u}(w).
\end{aligned}
$$

Induction on word length gives

$$
\tau_v(e_1\cdots e_n)=\sum_{j=1}^n d(e_j).
$$

Thus this cocycle lives on the residual graph. A source-level identity involving $T_u x$ is insufficient unless its one-step durations descend to that graph. Positive duration is a property of each named edge, including a legal failure edge when present; it is not inferred from a numerical label or from word length.

The additive accounting convention is that of [Process Geometry §9.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md). Its §§9.2–9.3 already distinguish compositional path accounting, descent through path relations and a state potential. The distinction between time records and their numerical projections also appears in [Joint Relations Clocks §§1.1 and 3.1](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md). Those results supply these conventions, rather than the reconstruction criterion below.

**Definition 2.2 (the reconstruction readout).** Define

$$
F:\mathcal P_r\longrightarrow V\times\mathbb R_{\ge0},
\qquad F(u)=(r\cdot u,\tau_r(u)).
$$

Only its actual image $F(\mathcal P_r)$ is a possible readout. Recovering the executed ordered path means inverting $F$ on that image. Edge names, their types and their order belong to the recovered word. This is not a requirement to reconstruct an unspecified source state, to predict a future response law, or to recover unmodeled waiting and continuous motion.

## 3. The cycle criterion

**Theorem 3.1 (finite strongly connected residual-cycle criterion).** Under Definitions 1.1–1.2 and Assumptions 1.3 and 2.1, the following are equivalent:

1. $F$ is injective on $\mathcal P_r$, the set of all finite legal words from $r$.
2. $G$ is one directed cycle, counting named parallel edges separately.

Precisely, condition 2 means that for some $m\ge1$ there are distinct vertices $v_0,\ldots,v_{m-1}$ exhausting $V$, and edges $e_0,\ldots,e_{m-1}$ exhausting $E$, with

$$
s(e_j)=v_j,\qquad t(e_j)=v_{(j+1)\bmod m}.
$$

The case $m=1$ is one vertex with exactly one named loop. The equivalence holds for any fixed choice of strictly positive edge durations; no rational independence or equality of those durations is assumed.

Proof. First every vertex has an outgoing edge. With at least two vertices, a path to another vertex begins with such an edge. With one vertex, the edge assumption provides a loop.

Suppose every vertex has exactly one outgoing named edge. Repeatedly follow the unique edge from any starting vertex. Finiteness forces a repeated vertex and hence a directed cycle. Every outgoing edge from a vertex on this cycle remains on the cycle. Strong connectivity forces every vertex to lie on it, since a cycle vertex must reach every other vertex. The unique-outgoing-edge condition then says that these cycle edges exhaust $E$. It follows that if $G$ is not one directed cycle, some vertex $z$ has two distinct outgoing named edges $a\ne b$.

Take a legal path $p:r\to z$. Strong connectivity supplies paths $A:t(a)\to z$ and $B:t(b)\to z$, which may be empty. The return words

$$
u=aA,\qquad w=bB
$$

are nonempty, both start and end at $z$, and have different first named edges. The two words $puw$ and $pwu$ are legal from $r$ and distinct: after the common prefix $p$, their first edges are $a$ and $b$. They both end at $z$, whereas the cocycle gives

$$
\begin{aligned}
\tau_r(puw)&=\tau_r(p)+\tau_z(u)+\tau_z(w),\\
\tau_r(pwu)&=\tau_r(p)+\tau_z(w)+\tau_z(u).
\end{aligned}
$$

These numbers are equal by commutativity of real addition. Hence $F(puw)=F(pwu)$ and $F$ is not injective. The argument uses the same root and source image for both words, by the lifting property of Definition 1.2. It exchanges two actual legal return blocks; it does not assume that the underlying named words commute. This proves condition 1 implies condition 2.

Conversely suppose $G$ is one directed cycle. Index it with $v_0=r$. Let

$$
D=\sum_{j=0}^{m-1}d(e_j)>0,\qquad
S_j=\sum_{k=0}^{j-1}d(e_k)\quad(0\le j<m),\qquad S_0=0.
$$

Every legal word is the unique initial segment of the repeated cycle. Its length has a unique decomposition $n=km+j$, with integers $k\ge0$ and $0\le j<m$. Its endpoint and duration are

$$
F(u)=(v_j,kD+S_j).
$$

If two words have the same $F$, their endpoints first determine the same $j$, since the listed vertices are distinct. Their durations then give $kD+S_j=k'D+S_j$, so $k=k'$ because $D>0$. Their lengths coincide, and uniqueness of the legal initial segment makes their named words equal. Thus $F$ is injective.

For a readout $(v_j,t)$ in the actual image, the number of full laps is exactly $k=(t-S_j)/D$, an integer there, and the word is $k$ complete laps followed by $e_0\cdots e_{j-1}$. This also covers the empty word and $m=1$. $\square$

The proof makes no quantitative assertion about the lengths of the colliding words. It treats all finite words, not only a bounded catalogue. The branching obstruction needs additive descended durations; strict positivity is used for the converse through the positive lap duration $D$. Some zero-duration edges would still allow that converse if $D>0$.

## 4. Residual, boundary, spatial and time views

**Remark 4.1 (response sufficiency and chronology).** The complete residual supplies legal continuation menus and the declared future responses. The cocycle supplies lawful accumulated accounting along those continuations. At a branching recurrent vertex, Theorem 3.1 shows that their pair still loses the order of return blocks. It does so even if each edge has a different duration, and even if the final residual is complete for the declared future task.

This is compatible with [Future Response Sufficiency §§1–6](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md), which separates a retrospective consumer from a prospective response consumer, and [Transport–Memory Completion §2.1](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), which defines a task-relative future quotient with explicit access conditions. Their prediction-memory statements are reused only for that distinction. Theorem 3.1 neither proves a new minimum prediction-memory bound nor identifies chronological reconstruction with future-response sufficiency. An ordered archive can distinguish $puw$ from $pwu$ while $F$ cannot.

**Remark 4.2 (transport through an already faithful view).** Let a boundary or spatial coordinate $b:V\to Y$ already be known to be injective on this same actual residual image. Then the augmented readout

$$
u\longmapsto \bigl(b(r\cdot u),\tau_r(u)\bigr)
$$

has exactly the same equality fibers as $F$: equality of its first coordinates is equivalent to equality of residual vertices, and the duration coordinates are unchanged. Theorem 3.1 therefore applies to that augmented readout. Transport of the named graph itself also requires preservation of types, legal named edges and their durations. An arbitrary display of a boundary or a spatial record is not assumed to have these properties.

A known invertible recoding of $F(\mathcal P_r)$ likewise preserves this criterion. Its inverse must be valid on that actual joint image; inverses for separate numerical fields or for an unrelated product domain do not supply it. A richer view containing an ordered archive need not have the same fibers as $F$ and is outside this particular equivalence.

The actual-image qualifications reuse [Process Geometry §§39–43](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), in particular §43's distinction between a common view kernel and the task kernel. No general equivalence of four views is asserted here. Faithfulness to this residual, the lawful duration and the named transition structure must already be established before transporting the criterion. Labels or accumulated costs alone have no general ability to recover past chronology.

## 5. Omission counterexamples

**Proposition 5.1 (parallel names and independent durations do not restore order).** The one-vertex graph with two named loops $a,b$, with durations $d(a)=1$ and $d(b)=\sqrt2$, satisfies the finite, edge, strong-connectivity and positive-cocycle assumptions but has

$$
ab\ne ba,\qquad F(ab)=F(ba)=(*,1+\sqrt2).
$$

Proof. Both words end at the sole vertex, and addition has the same two summands. Each loop is deterministic for its own name. A source with one type, constant current readout and these two legal operations can realize this graph, with declared one-step records and durations fixed by the name. Its future residual has one vertex. The same collision occurs with any two positive loop durations. Replacing the named multigraph by its underlying adjacency relation would report a single loop and yield a false cycle test. $\square$

**Proposition 5.2 (failure and record distinctions are required for faithful descent).** Equal endpoint snapshots and equal one-step durations do not imply equal complete residuals, even for deterministic operations.

Proof. Take two actual states $x,y$ of one type, with the same current snapshot, and one operation $a$ which returns to its starting state with duration one. At $x$ it returns $\operatorname{success}(0)$; at $y$ it returns $\operatorname{failure}(f,0)$ with a declared continuing successor. The response to $a$ separates the residuals. A projection erasing the outcome and reason sees identical snapshots, payloads and durations and merges them. Its single-loop display is not a faithful representation of the complete quotient.

For a record-only variant, both outcomes are successes, but the emitted records are respectively $0$ and $1$; erasing that record again merges distinct residuals. For a legality variant, $a$ is absent at $x$ and is an executed failure loop at $y$. Identifying both reports with one undifferentiated failure symbol loses a distinction in the legal domains, so a successor operation cannot descend through that merged fiber. These examples show why the complete response comparison retains legality, failure and record fields separately. $\square$

**Proposition 5.3 (non-cocycle summaries can encode order on a branching graph).** Strictly positive single-edge values without the residual cocycle do not imply the necessity direction of Theorem 3.1.

Proof. On one vertex with loops $a,b$, encode $a$ as the bit $0$ and $b$ as the bit $1$. For a word $w$ of length $n$, let $\operatorname{val}_2(w)$ be its binary value, allowing leading zeros, and define the reported numerical summary

$$
C(\varepsilon)=0,\qquad C(w)=2^n-1+\operatorname{val}_2(w).
$$

Words of length $n$ occupy exactly the disjoint integer interval $[2^n-1,2^{n+1}-2]$. Thus $C$ determines both length and the complete word, and $(*,C(w))$ is injective despite branching. Moreover

$$
C(wa)=2C(w)+1,\qquad C(wb)=2C(w)+2,
$$

so every nonempty one-step extension strictly increases the summary, with positive singleton values $C(a)=1,C(b)=2$. Nevertheless $C(ab)=4\ne C(a)+C(b)=3$; $C(ba)=5$ also retains the reverse order. This is an order code, not an additive duration on the one-vertex residual graph. $\square$

The same construction pinpoints why source-level additivity alone is inadequate. On the actual prefix image $X=\{a,b\}^{*}$, define $T_u(w)=wu$ and

$$
L(w,u)=C(wu)-C(w).
$$

Then $L(w,uv)=L(w,u)+L(wu,v)$ is a genuine source cocycle. Its one-step increments are positive but depend on $C(w)$, so they do not descend to the one-vertex response quotient that omits durations. If durations are included in complete responses, distinct prefixes have distinct next-$a$ durations $C(w)+1$, and the residual quotient is infinite. Neither choice satisfies both requirements of Theorem 3.1 simultaneously: omitting durations breaks duration descent, while including them makes the complete residual quotient infinite.

**Proposition 5.4 (a non-cocycle summary can also fail on a cycle).** A single positive singleton value does not establish the sufficiency direction when the additive law is absent.

Proof. On the one-vertex one-loop cycle define a reported summary $H(\varepsilon)=0$ and $H(a^n)=1$ for every $n\ge1$. The singleton value is positive, but $H(aa)=1\ne H(a)+H(a)=2$, and $a,aa$ have identical endpoint-summary pairs. This summary is not the sum of the realized positive edge durations. $\square$

**Proposition 5.5 (zero lap duration loses lap count).** Without the positive-lap condition, a cycle need not permit reconstruction.

Proof. On one vertex with one loop $a$, take $d(a)=0$ and the additive duration $\tau(a^n)=0$. Then $F(\varepsilon)=F(a)$ although the words differ. This is an additive example; it violates strict positivity. Together with the converse proof, it isolates the needed nonzero lap duration rather than asserting that each individual positive edge is logically necessary. $\square$

**Proposition 5.6 (recurrence and the edge assumption delimit the criterion).** Removing strong connectivity or the requirement of an edge invalidates the necessity direction as stated.

Proof. Take vertices $r,z$ and two named edges $a,b:r\to z$, with durations one and two and no outgoing edges at $z$. The complete list of legal words from $r$ is $\varepsilon,a,b$; their readouts are $(r,0),(z,1),(z,2)$, all distinct. The graph is not a cycle and is not strongly connected. Separately, one vertex with no edges is strongly connected using the empty path. Its only word is empty, so $F$ is injective although there is no directed cycle as defined in Theorem 3.1. $\square$

## 6. Mathematical applicability limits

**Remark 6.1 (scope of the inverse).** The inverse in Theorem 3.1 uses the fixed root, known named cycle and exact edge durations. It is defined on the actual readout image. No algorithmic representation of arbitrary real durations, precision bound, acquisition permission, memory optimum or robustness under noisy time measurements follows from this set-theoretic inverse. A finite quotient does not bound the size of the accumulated duration or of an ordered archive.

If the declared current readout exposes the full growing archive, the complete residual quotient may be infinite and Assumption 1.3 must be checked again. If timing, permissions or outcomes depend on a hidden source coordinate, that coordinate must be retained in the response contract whenever it changes the legal menu or a declared response. Restricting a policy to one path, deleting legal failure transitions or forgetting parallel operation names changes the graph and cannot establish the criterion for the original graph.

**Remark 6.2 (derivation and interpretive boundary).** Theorem 3.1 is a repo-derived elementary consequence of the fixed typed actual-image interface and positive residual cocycle. The cited volumes supply the earlier residual, source, view and clock distinctions; they are not attributed the cycle criterion. The derivation makes no claim of priority in graph theory or automata theory. Its mathematical conclusion is confined to ordered finite named executions in the stipulated deterministic graph. It supplies no Lean/kernel result, physical spacetime law, metric, relativity principle or implementation of a clock. Physical interpretations require additional models and evidence beyond these hypotheses.

## 追加锚（本行以下为增补区）

## 7. Rational duration reconstruction with arbitrary condensation

**Definition 7.1 (root-reachable graph and exact accounting).** Retain the typed actual source, complete response comparison, named edges and execution lifting of Definitions 1.1–1.2. Replace Assumption 1.3 by the following hypothesis: the graph restricted to all vertices reachable from $r=\pi(x_0)$ has finite vertex and named-edge sets. Denote this restricted graph again by $G=(V,E,s,t)$. Retain every legal named edge whose source is reachable; its target is then reachable as well. Neither an edge nor strong connectivity is required, and terminal vertices are allowed. Let $\mathcal P_r$ include every finite legal named word from $r$, including $\varepsilon_r$.

A strongly connected component (SCC) is a mutual-directed-reachability class. It is cyclic if it contains a nonempty directed return word. Thus a singleton without a self-loop is acyclic. The condensation has these components as vertices and an arrow for each edge crossing between components; it is a directed acyclic graph. Paths in the condensation retain these crossing-edge names. A simple path in $G$ has no repeated vertex; the empty path is simple, whereas a nonempty return word is not.

For a candidate label $d:E\to\mathbb Q_{>0}$, fix it before choosing any word and put

$$
\tau^d_v(\varepsilon_v)=0,\qquad
\tau^d_v(e_1\cdots e_n)=\sum_{h=1}^n d(e_h),\qquad
F_d(u)=(r\cdot u,\tau^d_r(u)).
$$

This is a descended additive cocycle, with the concatenation law of Assumption 2.1. Its interpretation as a source duration still requires that assumption's representative-independent one-step duration and common-unit bridge. Existence of a label on this graph does not assert that a source's already fixed native durations equal that label. The actual-source and response supplies are Definition 1.2 and [Process Geometry §§41–42](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md); the accounting supply is its §9.1. None of these supplies asserts the criterion below.

**Theorem 7.2 (root-reachable rational weighting criterion).** Under Definition 7.1, the following three conditions are equivalent:

1. There exists $d:E\to\mathbb Q_{>0}$ for which $F_d$ is injective on $\mathcal P_r$.
2. There exists $d:E\to\mathbb Z_{>0}$ for which $F_d$ is injective on $\mathcal P_r$.
3. Both of the following structural requirements hold: every cyclic SCC has exactly one internal outgoing named edge at each of its vertices; every directed condensation path starting at the component of $r$ meets at most one cyclic SCC.

The internal edges of each cyclic SCC in condition 3 consequently form one directed named cycle. External exits, multiple entries, acyclic branching, reconvergence and named parallel crossing edges are permitted. Distinct cyclic SCCs may be reachable on different branches. The quantifier in conditions 1–2 is existence of a weighting, rather than injectivity for every fixed positive weighting. In contrast, Theorem 3.1 concerns any fixed positive real weighting on a strongly connected graph with an edge.

Proof. A positive integer weighting is a positive rational weighting. Conversely, finitely many rational edge weights have a common positive denominator; multiplying them all by it preserves equality fibers of $F_d$. This includes $E=\varnothing$.

For necessity, consider a cyclic SCC $C$. Every vertex of $C$ has an internal outgoing edge: for a nonsingleton component take an internal path to another vertex, and for a cyclic singleton take a loop. If there is exactly one such edge at each vertex, following it in the finite component yields a cycle; strong connectivity inside $C$ forces that cycle to exhaust its vertices and internal edges, as in Theorem 3.1. Otherwise a vertex $z\in C$ has distinct internal outgoing named edges $a,b$. Choose $p:r\to z$ and internal return paths $A:t(a)\to z$, $B:t(b)\to z$. Then $U=aA$ and $W=bB$ are nonempty return words with different first edges. The actual legal words $pUW$ and $pWU$ are distinct, end at $z$ and have equal accumulated weight for every additive edge label. This is the return-block obstruction of Theorem 3.1, now used inside a reachable component; external exits do not remove either word.

Suppose a condensation path from the root meets two cyclic components $C_1,C_2$ in that order. It lifts to a graph path: chosen crossing edges can be joined by internal paths within each SCC. Choose vertices $z_i\in C_i$, a path $p:r\to z_1$, a path $Q:z_1\to z_2$ following that component order, and nonempty internal return words $L_i$ at $z_i$. Write $A_i=\tau^d_{z_i}(L_i)>0$. For rational weights choose a positive integer $M$ with $MA_i\in\mathbb Z_{>0}$, and put $a_i=MA_i$. There exist positive integers $h_1,h_2$ with $h_1a_1=h_2a_2$, for example $h_1=a_2$ and $h_2=a_1$. Therefore

$$
F_d(pL_1^{h_1}Q)=F_d(pQL_2^{h_2}).
$$

Both words end at $z_2$. They differ because the first has additional internal edges of $C_1$, while the additional edges of the second lie in $C_2$. Execution lifting makes both words legal from the same actual root representative. Hence neither structural requirement can fail under condition 1.

For sufficiency, assume condition 3. Choose one marked edge $m_C$ in each cyclic SCC $C$. Enumerate all remaining named edges as $e_0,\ldots,e_{N-1}$, including every parallel edge separately. Define

$$
B=\sum_{j=0}^{N-1}5^j,\qquad D=2B+1,
$$

and set

$$
\begin{aligned}
d(e_j)&=5^j,\\
d(m_C)&=D-\sum_{\{j:e_j\text{ is internal to }C\}}5^j.
\end{aligned}
$$

Every marked weight is at least $D-B=B+1>0$. All weights are integers, and the total weight of one complete lap of every cyclic SCC is exactly $D$. If $N=0$, the sums are empty, $B=0$, $D=1$, and these formulas still apply, including to a sole marked self-loop or to the edgeless graph.

A word never leaves an SCC and returns to it, since the condensation is acyclic. Its component path therefore visits at most one cyclic SCC. All other visited components are singletons without loops. Within a cyclic component $C$, the internal segment is forced by its unique internal outgoing edges, until a chosen external exit or the end of the word. If $c$ is the first entry vertex and the segment has length $n$, write $n=k|C|+j$ with $0\le j<|C|$. That segment is uniquely $L_c^k\gamma$, where $L_c$ is one complete lap starting at $c$ and $\gamma$ is its first $j$ edges. Removing these $k$ laps leaves a unique simple root path $P$ with the same endpoint. More precisely, if $P=\alpha\gamma\beta$ at its entry into $C$, the original word is

$$
u=\alpha L_c^k\gamma\beta,\qquad
\tau^d_r(u)=\tau^d_r(P)+kD.
$$

The entry vertex remains on $P$, even when $\gamma$ is empty. If no cyclic component is visited, $u=P$ and $k=0$. Conversely, the simple path $P$ and its nonnegative lap count determine the named word by this insertion at the first entry. This also handles stopping at a cycle vertex, a self-loop, a cyclic root and the empty word.

It remains to separate simple paths modulo $D$. For a simple path $P$, let $x_e(P)\in\{0,1\}$ be its edge-incidence indicator. Put

$$
\begin{aligned}
b_j(P)&=
\begin{cases}
x_{e_j}(P)-x_{m_C}(P),&e_j\text{ internal to a cyclic }C,\\
x_{e_j}(P),&e_j\text{ otherwise},
\end{cases}\\
R(P)&=\sum_{j=0}^{N-1}b_j(P)5^j,\qquad
a(P)=\sum_C x_{m_C}(P).
\end{aligned}
$$

Then $b_j(P)\in\{-1,0,1\}$, $|R(P)|\le B$, $a(P)\in\{0,1\}$, and direct substitution gives

$$
\tau^d_r(P)=a(P)D+R(P).
$$

If $R(P)\equiv R(P')\pmod D$, the bound $|R(P)-R(P')|\le2B<D$ makes the two integers equal. Their coefficient vectors then agree. Indeed, if $h$ is the largest index with a nonzero coefficient difference, that difference has absolute value at least one, whereas

$$
5^h>2\sum_{j<h}5^j=\frac{5^h-1}{2}
$$

excludes cancellation by all lower indices. For $N=0$, equality of the empty vectors is automatic.

Suppose these coefficient vectors agree. In any cyclic component $C$, if $x_{m_C}(P)=1$ and $x_{m_C}(P')=0$, equality of the internal coefficients forces $x_{e_j}(P)-x_{e_j}(P')=1$ for every other internal edge. Thus $P$ contains every edge of that cycle, which is impossible for a simple path. A marked self-loop is itself already impossible on a simple path. Interchanging $P,P'$ excludes the reverse difference. Therefore all marked indicators agree, and the coefficient equations then give agreement of every unmarked indicator as well.

Finally, simple paths from the same root with the same edge set have the same order: at each visited vertex before the endpoint that set has exactly one outgoing path edge, so following it from the root uniquely reconstructs the path. This reasoning counts actual named edges; two parallel crossing edges have distinct indicators. The empty set reconstructs the empty path. In particular, different simple root paths with the same endpoint have different residues $R(P)\pmod D$, including paths entering a cycle at different vertices or traversing different proper cycle segments.

If $F_d(u)=F_d(u')$, their reduced simple paths have the same endpoint and the same weight modulo $D$, hence are equal by the preceding argument. The equality of full weights now yields $kD=k'D$, so $k=k'$ and the normal forms give $u=u'$. This proves condition 2 and completes the equivalence. $\square$

**Proposition 7.3 (constructive integer decoder).** For the integer weights constructed in Theorem 7.2, the inverse on $F_d(\mathcal P_r)$ can be computed from the known finite named graph, its root and an exact endpoint-integer pair $(z,t)$ by a finite simple-path table and one nonnegative lap count.

Proof. List all simple root paths $P$, keeping their endpoint, named edge sequence, weight $\tau^d_r(P)$ and signed integer $R(P)$. The list is finite because a simple path has at most $|V|-1$ edges and $E$ is finite. For an input $(z,t)$, first find the unique centered residue $\rho\in[-B,B]$ congruent to $t$ modulo $D=2B+1$. Choose a table row with endpoint $z$ and $R(P)=\rho$. The separation in Theorem 7.2 gives at most one such row, and an actual readout has exactly one. Compute

$$
k=\frac{t-\tau^d_r(P)}{D}
  =\frac{t-R(P)}{D}-a(P).
$$

For an actual readout this is a nonnegative integer. If $P$ visits a cyclic SCC, insert $k$ full laps at its first entry as in the theorem. If it visits none, require $k=0$ and return $P$. A missing row, a negative or nonintegral count, or a positive count without a visited cyclic SCC is rejected; otherwise the reconstructed word is legal and has readout $(z,t)$, so these checks also characterize the actual image among endpoint-integer pairs.

The decoder uses the full simple-path weight, which need not lie in $[0,D)$, so $\lfloor t/D\rfloor$ alone need not be the complete-lap count. For example, take the cycle $u\xrightarrow{g}v\xrightarrow{m}u$, an entry $r\xrightarrow{a}v$ and an exit $u\xrightarrow{b}z$. Mark $m$ and enumerate the other edges as $g,a,b$. Then $B=31$, $D=63$, $d(m)=62$, and the simple path $amb$ has weight $92$ with no full lap. Its raw quotient is one, whereas $(92-\tau^d_r(amb))/63=0$ gives the correct count.

For a branching example, take $r\xrightarrow{a}u$, $r\xrightarrow{b}v$, single loops at $u,v$, and $u\xrightarrow{c}z$, $v\xrightarrow{e}z$. Mark the loops and enumerate the other edges as $a,b,c,e$. Then $B=156$, $D=313$, the two simple paths to $z$ have weights $26$ and $130$, and their respective families have weights $26+313k$ and $130+313k$. The endpoint and centered residue choose the branch, and the displayed difference formula recovers the lap count. Thus multiple reachable cyclic SCCs are compatible with reconstruction when no root condensation path visits two of them. $\square$

**Proposition 7.4 (successive cycles and the rational boundary).** Requiring each cyclic SCC to be a single named cycle does not suffice for rational reconstruction. On the graph with vertices $r,z$, one loop $a$ at $r$, one loop $b$ at $z$, and one edge $c:r\to z$, no positive rational weighting makes $F_d$ injective. Positive real weights can instead make $F_d$ injective on this same graph.

Proof. The two cyclic SCCs are singletons, but a root condensation path visits both. For any rational weights, positive integers $h,j$ satisfy $h\,d(a)=j\,d(b)$. The words $a^hc$ and $cb^j$ have equal endpoint $z$ and equal weight, while their named orders differ. For the integer choice $d(a)=2$, $d(b)=3$, $d(c)=1$, the explicit collision is

$$
a^3c\ne cb^2,\qquad F_d(a^3c)=F_d(cb^2)=(z,7).
$$

For the real choice $d(a)=1$, $d(b)=\sqrt2$, $d(c)=1$, all words ending at $r$ are $a^n$ and have distinct weights $n$. All words ending at $z$ are $a^ncb^m$ and have weights $n+1+m\sqrt2$. Equality of two such weights forces both nonnegative integer indices to agree, by irrationality of $\sqrt2$. The empty word is among the words ending at $r$, so injectivity holds on the whole $\mathcal P_r$. This does not alter the internal-branching obstruction, which holds even for real weights as Proposition 5.1 shows. These graphs have deterministic actual realizations on $X=\{r,z\}$ with current readout the vertex, operation domains given by the displayed edges and fixed one-step records; the complete residuals are then exactly the displayed vertices. $\square$

**Proposition 7.5 (exact accounting and finite-range limits).** The inverse of Proposition 7.3 is an inverse for the exact typed endpoint and exact integer cocycle on the actual readout image. If a cyclic SCC is reachable, that image is infinite, and no readout into a fixed finite set is injective on all finite legal words from the root.

Proof. Reach a cycle entry $c$ by a fixed word $p$. The words $pL_c^k$ for $k\ge0$ are legal and distinct, and their weights are $\tau^d_r(p)+kD$ with $D>0$. Thus the image is infinite; a finite codomain cannot separate these words. In particular, the finite simple-path table does not bound the integer lap counter uniformly over all word lengths. A bounded counter with finitely many auxiliary states cannot itself retain all these readouts. $\square$

Theorems 3.1 and 7.2 use the same typed residual and additive-duration interfaces, but Theorem 7.2 removes global recurrence by a new rational-weight existence construction and a second obstruction between components. It is a repository-derived mathematical argument, with no claim of literature priority or Lean/kernel verification. Exact accounting here does not assert a native physical clock, a physical unification, a guarantee for noisy or finite-precision observations, or an equivalence of residual, boundary, spatial and time views. Transport to another view still requires the actual-image faithfulness and named-edge, type, legality and duration preservation of Remark 4.2 and [Process Geometry §§39–43](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md). Including the growing total or a full archive in the current response readout can change the quotient and requires its finiteness to be checked again, as in Remark 6.1.

## 追加锚（本行以下为增补区）

## 8. Fixed final clock error, native separation and robust designs

**Definition 8.1 (one final observation and its recovery target).** Use the finite root-reachable typed complete response graph of Definition 7.1, with the actual source, named-edge lifting and fixed actual root $x_0$ of Definitions 1.1–1.2. The weighting in this definition is the source's fixed native $d:E\to\mathbb R_{>0}$ satisfying Assumption 2.1. Write $z(u)=r\cdot u$ and $\tau(u)=\tau_r^d(u)$ for every $u\in\mathcal P_r$, including $\varepsilon_r$. Fix $\epsilon>0$ in the declared clock unit, independently of the word, its duration and its length. The possible observations of $u$ are exactly

$$
\mathcal O_\epsilon(u)
 =\{z(u)\}\times[\tau(u)-\epsilon,\tau(u)+\epsilon].
$$

The endpoint, including its type, is exact. There is one final real-valued clock observation $y$; its error is a bound on the total, not an independently repeated error on each edge. Negative reported values near the empty word are allowed by this contract. Uniform recovery means that there is a function

$$
D:V\times\mathbb R\longrightarrow\mathcal P_r\cup\{\bot\}
\quad\text{such that}\quad
D(z(u),y)=u
\quad\text{for every }u\in\mathcal P_r
\text{ and every }|y-\tau(u)|\le\epsilon.
$$

The symbol $\bot$ denotes rejection of an observation outside the possible observation image. The target is the entire finite ordered named root word, with its types. No policy restriction or maximum word length is imposed. A chronological memory target $m:\mathcal P_r\to M$ is lossless for this purpose when it is injective on this actual word image. This target differs from a complete residual for future prediction, as in Remark 4.1 and [Joint Kernel Minimal Predictive Core Bridge §§4–6,22–23](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md).

The observation model assumes availability of the exact residual endpoint, a known graph and native duration law, and the stated common-unit, origin and final calibration/error contract over all words. The source definitions alone do not supply those acquisitions. In particular, an unknown offset, drift proportional to elapsed time, saturation, endpoint confusion, or merely approximate knowledge of each native duration is not this contract. An application must establish the stated total bound rather than infer it by summing an unspecified collection of local errors. Neither a bounded clock range nor bounded storage is assumed.

**Theorem 8.2 (finite criterion for a fixed native weighting).** Under Definition 8.1, uniform recovery is equivalent to the following three conditions.

1. The structural condition of Theorem 7.2 holds: every cyclic SCC is a directed named cycle, and every root condensation path meets at most one cyclic SCC.
2. In the finite family decomposition below, any two cyclic families with the same endpoint have commensurable lap durations: their ratio belongs to $\mathbb Q_{>0}$. No commensurability between families with different endpoints is required.
3. Every number in the following finite separation list is strictly greater than $2\epsilon$.

Here is the decomposition and the complete list, all formed from the fixed native $d$. Let $\mathcal S$ be the finite set of simple root paths, including the empty path. Reuse the unique normal form in the sufficiency proof of Theorem 7.2: when $P\in\mathcal S$ visits a cyclic component $C$, a word in its family is

$$
u_{P,k}=\alpha L_c^k\gamma\beta,
\qquad P=\alpha\gamma\beta,\qquad k\in\mathbb N_0,
$$

where $c$ is the first entry into $C$, $L_c$ is its one full named lap, and $\gamma$ is a proper initial cycle segment. This includes entry at the last vertex of $P$, an empty $\gamma$, a cyclic root, a self-loop and $k=0$. Put

$$
a_P=\tau(P),\qquad D_P=\sum_{e\text{ internal to }C}d(e)>0.
$$

Its time family is the ray $a_P+D_P\mathbb N_0$. A simple path visiting no cyclic component has the singleton family $\{P\}$ with time $a_P$. These word families are disjoint and exhaust $\mathcal P_r$; write $z_P$ for their common endpoint. The normal form depends only on condition 1, so applies to native real durations without using the integer construction in Theorem 7.2.

Include $D_P$ for each cyclic family. For each unordered pair of distinct simple paths $P,Q$ with $z_P=z_Q$, include the following number, according to the two family types:

| Families | Separation number |
| --- | --- |
| Two singletons | $\lvert a_P-a_Q\rvert$ |
| A singleton $P$ and a ray $Q$ | $\min\{\lvert a_P-a_Q-n_0D_Q\rvert,\ \lvert a_P-a_Q-(n_0+1)D_Q\rvert\}$, where $n_0=\max\{0,\lfloor(a_P-a_Q)/D_Q\rfloor\}$ |
| Two rays | $\operatorname{dist}(a_P-a_Q,h_{PQ}\mathbb Z)$, where $D_P=p h_{PQ}$ and $D_Q=q h_{PQ}$ for relatively prime positive integers $p,q$ |

The last row is defined under condition 2. Its distance is a finite nearest-lattice calculation: with $j_0=\lfloor(a_P-a_Q)/h_{PQ}\rfloor$, take the minimum of the distances to $j_0h_{PQ}$ and $(j_0+1)h_{PQ}$. The minimum of the entire list is denoted $\delta_d$, with $\min\varnothing=+\infty$. Condition 3 is equivalently $\delta_d>2\epsilon$.

This is a finite mathematical criterion, involving a finite graph, finitely many exact rationality predicates on real ratios and finitely many separation comparisons. It does not assert a decision procedure for unspecified or arbitrarily presented real numbers. In particular, finite approximations alone do not decide whether an arbitrary ratio is rational or whether an equality at the threshold holds.

Proof. First, any two different words with the same endpoint must have disjoint closed clock intervals. Two closed intervals of radius $\epsilon$ about $s,t$ intersect exactly when $|s-t|\le2\epsilon$. An intersection gives one allowed observation requiring two different answers. Conversely, if all such intervals are disjoint, define $D(z,y)$ to be the unique word whose observation set contains $(z,y)$, or $\bot$ if none does. Thus the exact operational condition is

$$
|\tau(u)-\tau(v)|>2\epsilon
\quad\text{whenever }u\ne v\text{ and }z(u)=z(v).
\tag{8.1}
$$

This step is only the bounded-error separation principle; the graph and arithmetic arguments that follow reduce its infinitely many requirements to the stated finite criterion.

For necessity of condition 1, the return-block obstruction proved in Theorems 3.1 and 7.2 already applies to real additive weights inside any reachable cyclic SCC with internal branching. It produces different actual legal words with the same endpoint and exactly the same time. Reuse that obstruction, which directly violates (8.1).

If a root condensation path meets two cyclic SCCs, choose an actual legal prefix $p$ to a vertex $c_1$ of the first, a connecting word $Q:c_1\to c_2$ along that component route, and nonempty internal return words $L_1,L_2$ at $c_1,c_2$. Set $A=\tau_{c_1}(L_1)>0$ and $B=\tau_{c_2}(L_2)>0$. For every $\eta>0$ there are positive integers $n,m$ with

$$
|nA-mB|<\eta.
\tag{8.2}
$$

For completeness, the classical Dirichlet estimate in [Kleinbock–Weiss, §1, equation (1.1), p.1](https://arxiv.org/pdf/math/0612171v2) gives, with their dimensions both one and $Y=A/B$, integers $q\ne0,p'$ satisfying $|qY-p'|<e^{-t}$ for arbitrarily large $t$. Reverse both signs if needed so that $q>0$. Taking $e^{-t}<Y$ forces $p'>0$, and taking $Be^{-t}<\eta$ proves (8.2) with $n=q,m=p'$. This uses only that classical estimate, not the paper's almost-everywhere improvement results.

The words $pL_1^nQ$ and $pQL_2^m$ have the same endpoint $c_2$, and their time difference is $nA-mB$. They are different: their additional internal occurrences in the first component differ by $n|L_1|>0$, and a condensation path cannot return to that component. Both lift from the same actual root by Definition 1.2. Taking $\eta<2\epsilon$ contradicts (8.1). This proves the second structural requirement for real weights, extending the rational obstruction of Theorem 7.2 to fixed nonzero tolerance. It includes the successive-cycle example of Proposition 7.4 even when its exact map is injective.

Assume now condition 1. Its unique normal form gives the finite disjoint singleton/ray decomposition stated above; no weighting choices are made. It remains to analyze the time differences between these actual families.

Within one ray, distinct lap counts have absolute time difference $|k-\ell|D_P$, whose minimum is $D_P$, attained by consecutive counts including zero and one. A pair of singletons gives the first row of the list. Between a singleton and a ray, minimizing the distance to the increasing sequence $a_Q+kD_Q$, $k\ge0$, reduces to the two adjacent admissible indices stated in the second row. If the singleton lies below the ray's start, index zero is nearest. Otherwise the floor and its successor bracket it. All these minima are attained by actual nonnegative lap counts.

Consider two rays with the same endpoint. If their ratio is irrational, their mutual distance has infimum zero, whatever their offsets. Here is the exact use of the existing irrational rotation theorem: [Weyl, §1, Satz 2, p.315, with proof on pp.316–317, DOI 10.1007/BF01475864](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0077/LOG_0036.pdf) says that positive integer multiples of an irrational real number are uniformly distributed modulo one. Consequently every tail is dense modulo one. Apply it to $D_P/D_Q$ and the target residue $(a_Q-a_P)/D_Q$. Given $\eta>0$, arbitrarily large $n\ge0$ have an integer $m$ with

$$
\left|\frac{a_P-a_Q+nD_P}{D_Q}-m\right|
 <\frac{\eta}{D_Q}.
$$

Since $D_P,D_Q>0$, choose such an $n$ large enough that $m\ge0$. Then

$$
|a_P+nD_P-a_Q-mD_Q|<\eta.
$$

The corresponding words belong to disjoint families, so are different even if this difference happens to be zero. Equation (8.1) fails. Hence commensurability is necessary whenever endpoints agree. This argument supplies arbitrarily close *legal nonnegative* lap counts, rather than only unrestricted integer combinations.

If the periods are commensurable, write them uniquely as $ph,qh$ with $p,q$ relatively prime positive integers and $h=h_{PQ}>0$. Bézout's identity, followed by adding a sufficiently large common multiple, gives

$$
\{pn-qm:n,m\in\mathbb N_0\}=\mathbb Z.
$$

Explicitly, from any integer solution $(n_*,m_*)$ to $pn_*-qm_*=j$, replace it by $(n_*+qN,m_*+pN)$ for a large enough integer $N$ to make both coordinates nonnegative. Therefore the set of signed differences between the two rays is exactly

$$
(a_P-a_Q)+h\mathbb Z.
$$

Its least absolute value is precisely the third row, and is attained by two actual words. This remains true when the two families visit the same cyclic SCC, when $p=q=1$. Parallel crossing names, different cycle entries and zero-lap words remain different table rows through their different simple paths.

Under conditions 1–2, every possible same-endpoint comparison is one of the comparisons just listed. Each listed minimum is attained. Thus (8.1) holds exactly when every entry exceeds $2\epsilon$, proving necessity and sufficiency. If the list is empty, there are no distinct words with a common endpoint and recovery follows from the endpoint alone.

In particular, in this graph class $\delta_d=2\epsilon<\infty$ fails: an attaining pair has the common midpoint observation. One must not replace the strict inequality by $\ge$. Nor is a general inference from an unattained infimum being $2\epsilon$ being used; finiteness and the attained minima above justify the threshold here. On a single loop with lap duration $2\epsilon$, the empty word and one lap already share the permitted observation $y=\epsilon$. This also checks the closed-error equality case at the root. $\square$

The theorem's graph and arithmetic synthesis is repo-derived. The finite cycle normal form is reused from Theorem 7.2. Its established automata counterpart is the cycle-contraction and finite-union decomposition in the proof of Krieger–Rampersad–Shallit, [*Finding the growth rate of a regular language in polynomial time*, arXiv:0711.4990v1, §3.1, Theorem 5, pp.4–5](https://arxiv.org/pdf/0711.4990v1). In that correspondence each vertex is accepting because every finite root word is in scope, and names remain distinct transitions. That paper supplies the decomposition perspective, not the native clock separation criterion. Weyl supplies irrational rotation, and the cited Dirichlet estimate supplies small differences of positive lap multiples. No priority claim for the combined graph result is made.

**Theorem 8.3 (existence of robust mathematical design weights).** Fix the finite root-reachable graph and $\epsilon>0$. There exists a positive real *design* weighting $\widehat d:E\to\mathbb R_{>0}$ satisfying Definition 8.1's recovery property at tolerance $\epsilon$ if and only if the structural condition of Theorem 7.2 holds. Equivalently, the graph admits an exactly injective positive rational weighting. When the structure holds it admits robust real design weights for every prescribed finite $\epsilon>0$.

Proof. A robust weighting must satisfy condition 1 of Theorem 8.2, which is independent of the weighting. Conversely, reuse Theorem 7.2 to obtain a positive integer weighting $d_0$ for which $F_{d_0}$ is injective; its construction is not repeated. For different words with the same endpoint, the two integer totals are distinct, hence differ by at least one. Choose any real $\lambda>2\epsilon$ and set $\widehat d=\lambda d_0$. Their new time difference is at least $\lambda>2\epsilon$, so the disjoint-interval argument of Theorem 8.2 supplies the decoder. This also covers an edgeless graph and an empty separation list. The equivalence with rational exact design is exactly Theorem 7.2.

The existential weighting here changes mathematical edge data. It does not assert that the fixed source can tune those data, install $d_0$, multiply every duration by $\lambda$, or maintain the prescribed error over unbounded executions. A change of units multiplies both the native durations and the numerical error bound by the same factor and does not improve their ratio. Even a genuine positive multiplication of native durations cannot turn a zero infimum of same-endpoint gaps into a positive one. Source realization and calibration of a proposed design are additional premises.

If a cyclic SCC is reachable, the lap argument of Proposition 7.5 still applies: $pL^k$ has the same endpoint for every $k\ge0$ and native total $\tau(p)+kD$ with $D>0$. The error-zero readings allowed by Definition 8.1 are already unbounded above. A retained record with at most $2^b$ values distinguishes at most $2^b$ members of this infinite same-endpoint family. Uniform absolute tolerance therefore provides no bound on clock range or chronological storage; a finite physical acquisition or bounded-width realization is not a conclusion of the design existence proof. $\square$

**Proposition 8.4 (a finite native source with exact recovery and no positive tolerance).** There is an actual finite deterministic source satisfying the typed complete response and positive native cocycle contracts for which $F_d$ is injective on *all* finite legal root words, but uniform recovery fails for every $\epsilon>0$. Its graph nevertheless satisfies Theorem 8.3 and thus admits robust designs.

Proof. Take one type and the actual state set $X=\{r,u,v,z\}$, with initial state $r$ and declared current readout $q(x)=x$. The entire legal transition set is

$$
r\xrightarrow{a}u,\qquad r\xrightarrow{b}v,\qquad
u\xrightarrow{x}u,\qquad v\xrightarrow{w}v,\qquad
u\xrightarrow{c}z,\qquad v\xrightarrow{e}z.
$$

Each operation has the singleton source domain displayed, the displayed successor, and a fixed complete one-step record containing its name, successor and native duration. There are no other operations, failures, resets or archive fields, and $z$ is terminal. Because the empty response contains $q$, distinct states have distinct complete residuals; equal states have identical responses by determinism. Thus the complete residual graph is exactly this four-state actual source, without any fictitious combinations of fields. Set

$$
d(a)=d(b)=d(c)=d(x)=1,\qquad d(e)=\tfrac32,\qquad d(w)=\sqrt2.
$$

One-step durations are representative independent and strictly positive, and the native total is their sum. The following is the exhaustive classification by endpoint, with all indices nonnegative:

| Endpoint | All legal root words | Native totals |
| --- | --- | --- |
| $r$ | $\varepsilon_r$ | $0$ |
| $u$ | $ax^n$, $n\ge0$ | $1+n$ |
| $v$ | $bw^m$, $m\ge0$ | $1+m\sqrt2$ |
| $z$ | $ax^nc$ or $bw^me$, $n,m\ge0$ | $2+n$ or $\tfrac52+m\sqrt2$ |

Indeed, after choosing $a$ or $b$ at $r$, only that branch's loop can repeat until its exit, after which no further edge is legal. Choosing to stop gives the corresponding intermediate row. This proves exhaustiveness, including the empty word and both zero-lap exits $ac,be$.

Each nonconstant sequence within a row is strictly increasing. At $z$, equality between the two branches would require

$$
n-m\sqrt2=\tfrac12.
$$

For $m=0$ this would make the integer $n$ equal to one half. For $m>0$ it would express $\sqrt2=(n-1/2)/m$ as a rational number. Both are impossible. Different endpoint rows are separated by the exact endpoint, regardless of coincidences between their times. In particular $a$ and $b$ have equal total one and distinct endpoints, and the two zero-lap totals at $z$ are $2$ and $5/2$. These facts establish injectivity on the entire $\mathcal P_r$.

The two time rays at $z$ have incommensurable periods $1,\sqrt2$. The irrational-rotation argument in Theorem 8.2, now with the offset one half, supplies for every $\eta>0$ some $n,m\ge0$ with

$$
\left|(2+n)-(\tfrac52+m\sqrt2)\right|<\eta.
$$

These values are never equal by the preceding calculation, but their positive gaps have infimum zero. For any $\epsilon>0$, choose $\eta<2\epsilon$; the midpoint of the resulting two totals is an allowed observation for both words. Uniform recovery fails at that tolerance.

Finally, the only cyclic components are the singleton loops at $u$ and $v$, and no root condensation path visits both. Theorem 8.3 therefore supplies robust design weights on this graph at any prescribed tolerance. This last statement does not replace the displayed native durations or give this actual source a new control operation. $\square$

**Theorem 8.5 (transport of the observation contract and of chronological memory).** Suppose $b:V\to B$ and $s:V\to S$ are faithful typed boundary and spatial endpoint representations on the same reachable actual residual image: each is injective there. Their endpoint readings are exact. Use the same final clock reading $y$, the same native $d$, root and total error bound as in Definition 8.1. Then the following three observation contracts have uniform recovery for exactly the same graphs, weights and tolerances:

$$
(z(u),y),\qquad (b(z(u)),y),\qquad (s(z(u)),y),
\qquad |y-\tau(u)|\le\epsilon.
$$

Whenever they recover the word they also recover every lossless chronological memory target $m(u)$ of Definition 8.1. The recovered word determines the exact modeled endpoint and accumulated duration. It does not determine the realized clock error or an arbitrary pre-existing source history. These conclusions alone give no pairwise invertibility of the four unaugmented endpoint, time, boundary and memory coordinates.

Proof. Injectivity of $b$ gives an inverse $b^{-1}:b(V)\to V$ on its actual image. The map

$$
(z,y)\longmapsto(b(z),y)
$$

is a bijection of the possible noisy observation images, with inverse $(\beta,y)\mapsto(b^{-1}(\beta),y)$. It carries the full observation set of each word onto the boundary observation set of that same word, preserving intersections and disjointness. Composing either decoder with these maps proves equivalence in both directions. The same argument applies to $s$ and transports directly between the two augmented views. No independently possible endpoint and time values are inserted into the actual observation image.

Once $u$ is decoded, apply $m$ to get its chronological memory value; conversely its actual-image inverse recovers $u$ from $m(u)$. This is the lossless ordered-word target, not the potentially coarser minimal predictive core. Since $x_0$ and the deterministic source model are fixed, mathematical replay also determines the declared response sequence along $u$. It is evaluation of the fixed model, not authorization to reset, query a new source, or recover fields omitted from that model.

For a single fixed word $u$, all errors $\xi\in[-\epsilon,\epsilon]$ are allowed, with $y=\tau(u)+\xi$. At least two such values give the same decoded word. Thus neither $u$ nor $m(u)$ alone can recover the realized $\xi$ or $y$. If $y$ is additionally retained and the native model is exactly known, then $\xi=y-\tau(u)$ is determined by that *augmented* data. In particular, the noisy observation and the decoded word have a recovery map but need not be bijective records.

For an explicit failure of unaugmented recovery, on the one-vertex one-loop source all residual, boundary and spatial endpoint coordinates are constant, whereas the words $x^n$ and their chronological memories vary with $n$. With native loop duration one they are uniformly recoverable from endpoint plus time whenever $0<\epsilon<1/2$. The constant endpoint coordinates cannot recover these histories. Conversely, in the finite acyclic source with just $r\xrightarrow{a}u$ and $r\xrightarrow{b}v$, both durations one and current readout equal to the state, endpoint plus noisy time recovers all three words $\varepsilon_r,a,b$ for every tolerance because their endpoints differ. The unaugmented exact total time merges $a,b$. Therefore even a successful joint reconstruction does not make each coordinate individually sufficient.

For interpreting $b$ or $s$ as representations of the *process*, rather than just endpoint relabelings, additionally supply a rooted typed named-graph isomorphism onto its actual represented image, with both directions preserving legal menus, successors, complete declared outputs and durations. These are the same-source requirements of Remark 4.2, [Process Geometry §§39–43](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), and [Joint Kernel Minimal Predictive Core Bridge §23](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md). They give, by induction on the word, the same legal words and native totals in the represented process. Exact endpoint faithfulness then applies the preceding observation-set bijection. A view carrying extra history, a view with an unproved inverse, or a view with endpoint noise has not been supplied this contract. $\square$

**Proposition 8.6 (invertible recoding and newly imposed additive error).** Exact invertible recoding of endpoint-time values need not preserve the existence of a positive uniform additive tolerance in the recoded time coordinate. Preservation under the *transported* observation contract remains valid.

Proof. Use a one-vertex one-loop actual deterministic source with current readout its sole vertex and native loop duration one. Its words are exactly $x^n$, $n\in\mathbb N_0$, including the empty word at $n=0$, with times $n$. Adjacent same-endpoint times differ by one, so Theorem 8.2 gives uniform recovery for every $0<\epsilon<1/2$.

Recode time by $f(t)=\log(1+t)$ for $t\ge0$. It is strictly increasing with inverse $f^{-1}(v)=e^v-1$ on its image, and hence preserves exact recovery of every word. But

$$
f(n+1)-f(n)=\log\left(1+\frac1{n+1}\right)>0,
\qquad \lim_{n\to\infty}(f(n+1)-f(n))=0.
$$

For every newly imposed constant additive error $\eta>0$ around $f(n)$, two sufficiently late consecutive words have overlapping closed error intervals of radius $\eta$. Their midpoint observation prevents recovery. The recoded coordinate is not asserted to be a descended additive duration, so this is a counterexample to unrestricted recoding of the error model, not an exception to Theorem 8.2.

If instead the native observation $y\in[n-\epsilon,n+\epsilon]$ is passed through the same $f$, extend $f$ to $(-1,\infty)$; it contains all these observations when $\epsilon<1/2$. The actual transported interval is

$$
[f(n-\epsilon),f(n+\epsilon)].
$$

These intervals remain disjoint because $f$ is injective on the entire possible noisy observation domain. They shrink with $n$ and are not the newly stipulated intervals $[f(n)-\eta,f(n)+\eta]$ for a fixed positive $\eta$. Thus an invertible recoding preserves the observation contract when the contract is transported with it, but its exact inverse alone supplies no calibration guarantee for a different instrument error measured after recoding. $\square$

## 追加锚（本行以下为增补区）


## 9. Finite online clock-memory completion

**Definition 9.1 (finite clock-memory supplements and the acquisition boundary).** Keep the actual root-reachable typed graph, the fixed native positive duration \(d\), the complete set of finite legal words \(\mathcal P_r\), the exact typed endpoint \(z(u)=r\cdot u\), and the single final observation \(y\) with \(\lvert y-\tau(u)\rvert\le\epsilon\) from Definition 8.1. A parameterized operation name, including its declared type and all of its parameters, is one atomic symbol of a typed alphabet \(\mathcal A\).

A finite static supplement is a map \(h:\mathcal P_r\to H\) with finite range. It is admissible at \(\epsilon\) when there is a decoder
\[
D:V\times H\times\mathbb R\longrightarrow\mathcal P_r\cup\{\bot\}
\]
such that \(D(z(u),h(u),y)=u\) for every legal root word \(u\) and every \(y\) in its closed native error interval. The label is a final static value; it is not assumed to have a prefix-compatible update.

A finite online supplement is a finite set \(M\), a fixed initialization \(m_0\in M\), and one update map
\[
U:M\times\mathcal A\longrightarrow M.
\]
The register receives exactly the names of the operations that actually execute, in their execution order. Its value is
\[
\mu(\varepsilon_r)=m_0,\qquad
\mu(ua)=U(\mu(u),a).
\]
The decoder receives only the exact typed endpoint, the final register value and the one final clock value. It receives no endpoint or clock during the execution, no one-step duration, complete response record, permission result, archive, future operation or unexecuted branch, and no external event counter. Initialization is independent of the word. Every persistent phase, control bit and auxiliary variable is part of \(M\); there is no hidden persistent state. Updates on names that are illegal at the current source state may be chosen arbitrarily, since only finite legal words are in the contract.

Thus an online supplement induces the static map \(h=\mu\), but the converse requires a genuine prefix-compatible construction. The native \(d\), the actual source, the whole legal-word domain and the exact final endpoint are unchanged.

**Lemma 9.2 (the common-fibre separation test).** For either a static label \(h\) or an online value \(\mu\), a decoder with the stated closed error contract exists if and only if
\[
u\ne v,\quad z(u)=z(v),\quad h(u)=h(v)
\quad\Longrightarrow\quad
\lvert\tau(u)-\tau(v)\rvert>2\epsilon.
\tag{9.1}
\]

Proof. The two closed intervals of radius \(\epsilon\) about \(s\) and \(t\) intersect exactly when \(\lvert s-t\rvert\le2\epsilon\). If (9.1) fails, a point in the intersection has two legal explanations with the same endpoint and supplement, so no decoder can be correct on both. If (9.1) holds, every possible triple \((z,h,y)\) belongs to at most one word's observation set; define the decoder to return that word and to return \(\bot\) outside the union. The endpoint is typed, so equality here includes equality of its type. \(\square\)

**Theorem 9.3 (finite static labels, finite online registers and the native structural criterion).** For every fixed native \(d:E\to\mathbb R_{>0}\) and every \(\epsilon>0\), the following are equivalent:

1. An admissible finite static supplement exists.
2. An admissible finite online supplement exists under Definition 9.1.
3. The two structural requirements of Theorem 7.2 hold: every cyclic SCC has exactly one internal outgoing named edge at each vertex, and every root-starting condensation path meets at most one cyclic SCC.

Proof. An online register is a static supplement by taking \(h=\mu\), so \(2\Rightarrow1\).

Assume \(1\), and write \(q=\lvert H\rvert\). Suppose a reachable cyclic SCC has two distinct internal outgoing named edges at a vertex \(c\). As in Theorems 3.1 and 7.2, choose nonempty return words \(A\) and \(B\) from the two choices back to \(c\), with different first names. For any integer \(k\ge1\), every permutation containing \(k\) copies of \(A\) and \(k\) copies of \(B\) is a legal return word. There are \(\binom{2k}{k}\) such words, all with the same endpoint and the same native duration \(k(\tau_c(A)+\tau_c(B))\), while their named words are different. Choose \(k\) with \(\binom{2k}{k}>q\), prepend one fixed legal path from \(r\) to \(c\), and apply the pigeonhole principle to \(h\). Two distinct words have the same endpoint, label and time, contradicting (9.1). Hence every cyclic SCC has one internal outgoing named edge at each vertex.

Now suppose a root-starting condensation path meets cyclic SCCs \(C_1\) and \(C_2\) in that order. Choose a legal connecting route from a vertex of \(C_1\) to a vertex of \(C_2\), nonempty internal return words \(L_1,L_2\) on that route, and put
\[
A=\tau(L_1)>0,\qquad B=\tau(L_2)>0.
\]
For the finite range \(H\), choose an integer \(L\) with \(B/L<2\epsilon\). Take \(N+1>(q+1)L\) and divide the unit interval into \(L\) half-open bins. Among the fractional parts
\[
\left\{\frac{nA}{B}\right\},\qquad 0\le n\le N,
\]
one bin contains \(q+1\) distinct indices \(n_0,\ldots,n_q\). Choose \(K\) so large that
\[
m_i=K-\left\lfloor\frac{n_iA}{B}\right\rfloor\ge0
\]
for every \(i\). The \(q+1\) legal words
\[
p\,L_1^{\,n_i}\,Q\,L_2^{\,m_i}
\]
end at the same vertex of \(C_2\), are distinct, and have total durations
\[
\tau(pQ)+KB+B\left\{\frac{n_iA}{B}\right\}.
\]
Their durations lie in an interval of length \(B/L<2\epsilon\). Two receive the same label, again contradicting (9.1). This finite-bin argument covers rational and irrational period ratios and does not use an uninspected Diophantine theorem. Thus no root condensation path meets two cyclic SCCs, proving \(1\Rightarrow3\).

Assume \(3\). The canonical normal form in the proof of Theorem 7.2 gives a finite set \(\mathcal S\) of simple root paths. Each word is either a singleton family \(P\), or has a unique form
\[
u_{P,k}=\alpha L_c^k\gamma\beta,\qquad
P=\alpha\gamma\beta,\qquad k\in\mathbb N_0,
\]
where \(P\) visits one cyclic SCC, \(L_c\) is one named lap, and
\[
D_P=\tau(L_c)>0,\qquad \tau(u_{P,k})=\tau(P)+kD_P.
\]
Different \(P\)'s give disjoint named families, even when their endpoints agree. For each cyclic family put
\[
p_P=\left\lfloor\frac{2\epsilon}{D_P}\right\rfloor+1,
\]
and give \(u_{P,k}\) the static label \((P,k\bmod p_P)\). Give a singleton the label \((P,0)\). If two words have the same label and endpoint, they lie in the same family and their lap counts differ by a nonzero multiple of \(p_P\). Their native times therefore differ by at least \(p_PD_P>2\epsilon\). Lemma 9.2 supplies the decoder, proving \(3\Rightarrow1\).

It remains to make the label prefix-compatible. Let \(\mathcal R\) be the finite set of reduced-prefix records: a simple root prefix together with its current cut, and, when a cyclic SCC has been entered, the same finite skeleton together with the current cycle phase and a residue in \(\mathbb Z/p_P\). A complete lap is removed from the skeleton and increments its residue. The uniqueness of the normal form and the fact that a condensation path cannot return to a previously left SCC make this reduction unique. The current vertex and all phase information are retained in the record. Appending a name determines the next record from the current record and that name alone: it either advances the finite skeleton, increments the cycle residue when a lap closes, or follows an external exit. No endpoint, time or hidden edge identifier is read. Set \(M=\mathcal R\), initialize at the empty reduced record, and use this transition as \(U\). The final register state contains at least the family and residue used by the static construction, so Lemma 9.2 proves \(3\Rightarrow2\).

For a concrete finite bound, let \(\mathcal S\) be the simple-root-path set and put \(p(P)=1\) for an acyclic \(P\), and \(p(P)=\lfloor2\epsilon/D_P\rfloor+1\) for a \(P\) visiting a cycle. Retaining every possible cut gives the useful, deliberately nonminimal estimate
\[
\lvert M\rvert\ \le\ \sum_{P\in\mathcal S}(\lvert P\rvert+1)p(P)
\ \le\ \lvert\mathcal S\rvert\,|V|\,
\max_{P\in\mathcal S}p(P).
\tag{9.2}
\]
The estimate counts complete control state, phase, skeleton and residue; it does not count an uncharged auxiliary counter. It is an upper bound for one construction, not a general minimum. This completes the equivalence. \(\square\)

The theorem uses the fixed native durations throughout. It does not replace them by the design weights of Theorem 8.3. It also separates the arbitrary finite final label from the online register: the static construction may compute a lap residue from the completed word, whereas the online construction must carry the phase needed to know when a lap has completed. The criterion is exactly the §7.2 graph condition, even though the native clock itself can have arbitrarily small cross-family gaps; a finite residue register closes those gaps only when the one-cycle-per-root-path structure makes one lap counter sufficient.

**Theorem 9.4 (sharp names-only cycle minima).** Consider a single typed \(m\)-vertex directed cycle rooted at \(v_0\). Every edge carries the same parameterized operation name \(a\), so the feed supplies no edge identifier or endpoint. Let the positive native edge durations have total lap duration
\[
D=\sum_{j=0}^{m-1}d(e_j)>0.
\]
For a final static supplement, the exact minimum number of labels is
\[
s_{\min}=\left\lfloor\frac{2\epsilon}{D}\right\rfloor+1.
\tag{9.3}
\]
For a complete names-only online register, the exact minimum number of reachable states is
\[
o_{\min}
=\min\left\{p\ge1:\frac{p}{\gcd(p,m)}D>2\epsilon\right\}.
\tag{9.4}
\]

Proof. Write every word uniquely as the first \(n=km+j\) edges of the repeated cycle, with \(0\le j<m\). The endpoint fixes \(j\), and the native time is \(kD+S_j\), where \(S_j\) is the fixed partial-lap time.

For the static lower bound, inspect the \(q+1\) words completing \(k=0,\ldots,q\) full laps at \(v_0\). If \(qD\le2\epsilon\), two of them have the same label, and their time intervals overlap. Thus every admissible \(q\)-label supplement has \(qD>2\epsilon\), giving \(q\ge s_{\min}\). Conversely, label the word \(km+j\) by \(k\bmod s_{\min}\). Equal endpoint and equal label force a lap-count difference at least \(s_{\min}\), whose time gap is \(s_{\min}D>2\epsilon\). Lemma 9.2 proves (9.3).

For the online lower bound, because every input symbol is \(a\), the register follows one function \(f:M\to M\). Its trajectory from \(m_0\) is eventually periodic; let the eventual cycle have length \(\ell\). Necessarily \(\ell\le|M|\). Two equal states on that cycle separated by
\[
\operatorname{lcm}(\ell,m)
\]
input events have the same endpoint and time separation
\[
\frac{\operatorname{lcm}(\ell,m)}{m}D
=\frac{\ell}{\gcd(\ell,m)}D.
\]
This must exceed \(2\epsilon\) by Lemma 9.2. Hence some \(\ell\le|M|\) satisfies the inequality in (9.4), so \(|M|\ge o_{\min}\). Conversely, take \(p=o_{\min}\) states in one directed \(p\)-cycle and update by \(a\) to the next state. Equal register state and endpoint then require an event difference divisible by \(\operatorname{lcm}(p,m)\), whose time gap is \(pD/\gcd(p,m)>2\epsilon\). Lemma 9.2 gives a decoder. \(\square\)

The two minima can differ strictly because a static label may use the completed word's lap number, while a names-only update sees only one repeated symbol. For \(m=2\), edge durations \(d(e_0)=d(e_1)=1/2\), \(D=1\), and \(\epsilon=1/2\), the static minimum is \(2\). The online condition rejects \(p=1\) and \(p=2\), since \(p/\gcd(p,2)=1\) in both cases, and accepts \(p=3\). Thus \(s_{\min}=2<3=o_{\min}\). The static parity label separates equal-endpoint words by two laps; a two-state names-only register repeats after one lap and the closed error intervals meet at their midpoint. This is an actual strict gap, caused solely by the acquisition boundary and same-name feed.

**Proposition 9.5 (exact finite supplement cost for the native source of Proposition 8.4).** For the actual source and native durations displayed in Proposition 8.4, every \(0<\epsilon<1/2\) has static minimum \(2\) and complete online-state minimum \(2\).

Proof. At endpoint \(z\), the two legal families have native times
\[
2+n,\qquad \tfrac52+m\sqrt2,\qquad n,m\in\mathbb N_0.
\]
The irrational-rotation argument already used in Proposition 8.4 gives pairs from these two families with arbitrarily small positive time gap. A one-label static supplement therefore violates Lemma 9.2. A one-state online register is a one-label static supplement, so both minima are at least \(2\).

For the upper bound, use two labels \(A,B\). Give every word on the \(a,x,c\) branch label \(A\), every word on the \(b,w,e\) branch label \(B\), and give the empty root word either label because its endpoint is \(r\). Within each branch, two different words with the same endpoint differ by at least one native unit of time. Since \(2\epsilon<1\), Lemma 9.2 applies; the labels separate the two \(z\)-families. The same partition is online: initialize at \(A\), set \(U(\,\cdot\,,a)=A\), \(U(\,\cdot\,,b)=B\), preserve \(A\) on \(x,c\), and preserve \(B\) on \(w,e\). These are names-only updates, and all legal executions follow the displayed branch. Hence two states suffice. The result uses the actual source acquisition and native \(d\), not a redesigned weighting. \(\square\)

**Proposition 9.6 (what the finite register does and does not repair).** The finite supplement repairs only distinctions that remain in its declared feed and in the exact endpoint-time contract.

Proof. If two different executed events are projected to one token before the register sees them, the corresponding input words can become identical. For example, on a one-vertex source with two named loops \(a,b\), the words \(ab\) and \(ba\) have the same endpoint and additive native time. A names-only feed that erases the distinction between \(a\) and \(b\) presents the same token sequence to every online update, so no register can separate them. This is an acquisition failure, not a finite-state lower bound that may be overcome by adding hidden state.

If a boundary or spatial endpoint map is injective on the actual typed residual image and preserves the named graph, legal menus, complete responses and native durations, replace \(z(u)\) in Lemma 9.2 by that exact representation; the proof is transported by the same actual-image bijection as Theorem 8.5. If the map merges residual endpoints, the register must compensate for that additional merge, and the present theorem supplies no finite guarantee for it. Thus memory is complementary to a faithful boundary or spatial endpoint, not an automatic inverse for an arbitrary projection.

A finite register has finite current control state only. The legal word length, native clock range, source/archive size and any total chronological history may be unbounded. The register does not provide a free archive, a future read, an independently calibrated time source or a bound on total storage. The source acquisition, common unit, fixed origin, exact endpoint and one final closed total-error bound remain the assumptions of Definition 8.1. The mathematical result is a prose proof on the declared model; it is not a Lean/kernel validation or a physical-source verification.

The finite simple-path and cycle-family viewpoint overlaps the cycle-contraction and finite-union decomposition in Krieger--Rampersad--Shallit, [*Finding the growth rate of a regular language in polynomial time*, arXiv:0711.4990v1, Theorem 5, pp.4--5](https://arxiv.org/pdf/0711.4990v1), which is used here only as a literature supplier for finite path schemas. The structural obstruction and native clock-memory results are derived in this volume from Theorems 7.2 and 8.2, the actual source of Proposition 8.4, and the typed actual-image conventions of Process Geometry §§39--43. The repository's transport-memory and predictive-core volumes supply the distinction between chronological losslessness and future sufficiency; they do not contain the finite names-only update criterion or the two exact minima above. No literature-priority or world-level claim is made. \(\square\)

## 追加锚（本行以下为增补区）

## 10. Joint native clocks and complete finite memory on two successive loops

**Definition 10.1 (same-execution vector observation and names-only supplementation).** Retain the actual source, complete response quotient and legal-word lifting of Definitions 1.1–1.2, with the finite root-reachable convention of Definition 7.1. For an integer $r\ge2$, fix one native edge map $d:E\to\mathbb R_{>0}^r$, independently of the executed word. Its $j$th coordinate is a fixed, representative-independent positive additive readout on that same execution. Write

$$
T(u)=\sum_{e\text{ in }u}d(e),\qquad T(\varepsilon)=0.
$$

The sum counts occurrences. It obeys the vector version of Assumption 2.1's concatenation law. Fix $\epsilon>0$ and assume one final joint acquisition with possible observation set

$$
\mathcal O_\epsilon(u)
 =\{z(u)\}\times\bigl(T(u)+[-\epsilon,\epsilon]^r\bigr).
\tag{10.1}
$$

The endpoint, with its type, is acquired exactly. Every error vector $\eta\in[-\epsilon,\epsilon]^r$ is allowed for every legal finite root word. This is one closed box about the whole final vector: there is no probabilistic independence premise, independent acquisition of different executions, subdivision into segment errors, or inference of a total error bound from edge errors. The coordinates have their declared fixed origins, units and native calibrations.

A static supplement $h:\mathcal P_p\to H$ and a complete finite online register $(M,m_0,U)$ have exactly the acquisition restrictions of Definition 9.1, with $y\in\mathbb R^r$ replacing its scalar observation. In particular, $U$ reads only its current complete state and the actually executed typed parameterized operation name. It receives no intermediate endpoint, edge identifier, one-step readout, response record, clock, archive, future, stop token or hidden source reply. All persistent phase and control belong to $M$. The final decoder receives exactly $(z(u),h(u),y)$, or $(z(u),\mu(u),y)$, and must return $u$ for every error permitted by (10.1). In state cardinalities, restrict $M$ to values reached by legal root histories; arbitrary extra unused states cannot improve a minimum. The exact final supplement value is an acquisition assumption too.

The common-source requirement is the deterministic specialization of the joint-law distinction in [Process Geometry §29.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) and [Joint Relations Clocks §4.2](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md). Marginal laws alone do not specify (10.1).

**Definition 10.2 (the entire three-state actual source).** There is one type $i$, actual image $X_i=\{p,s,t\}$, fixed initial state $p$, and declared current readout $q_i(x)=x$. The whole operation alphabet consists of three names $a,c,e:i\to i$, with domains and successors

$$
D_a=\{p,s\},\quad T_a(p)=p,\quad T_a(s)=s,
\qquad D_c=\{p\},\quad T_c(p)=s,
\qquad D_e=\{s\},\quad T_e(s)=t.
\tag{10.2}
$$

There are exactly four named edges. The two occurrences of $a$ are the identical input token, not names qualified by their source vertex. There are no other legal operations, failure edges, resets or source archive fields; $t$ is terminal. Each complete one-step record consists of its success tag, executed name, successor and the fixed vector for that edge. Fix arbitrary

$$
A,C,B,E\in\mathbb R_{>0}^r,
\qquad d(p,a)=A,\quad d(p,c)=C,\quad
 d(s,a)=B,\quad d(s,e)=E.
\tag{10.3}
$$

The one-step record can depend on the state through these stipulated data; its extra fields are not supplied to the online register. Equality of complete responses is equality of states: the empty response already separates distinct states by $q_i$, and determinism gives equal responses from the same state. Thus this is its own complete residual graph, and the vectors descend without a representative ambiguity.

All actual root words and their joint native totals are exactly

| Exact endpoint | Entire legal word family | Native total |
| --- | --- | --- |
| $p$ | $a^m$, $m\in\mathbb N_0$ | $mA$ |
| $s$ | $a^mca^n$, $m,n\in\mathbb N_0$ | $C+mA+nB$ |
| $t$ | $a^mca^ne$, $m,n\in\mathbb N_0$ | $C+E+mA+nB$ |

Indeed, only $a$ can precede the unique possible $c$, only $a$ can follow it until the optional $e$, and nothing can follow $e$. The exponent $m=0$ in the first row is the empty word; $c,ce$ and all other zero-lap and terminal histories remain included. Choosing a finite cut adds no operation. The two exponents determine the ordered name word because the single $c$ marks their separation, even though $a$ has the same name on both sides. This is a concrete two-cycle path schema, using the established normal-form perspective of §§7–9 and Krieger–Rampersad–Shallit, [arXiv:0711.4990v1, Theorem 5 and its proof, pp.4–5](https://arxiv.org/pdf/0711.4990v1); neither path schemas nor their polynomial-growth characterization are new assertions here.

**Theorem 10.3 (native joint supplementation criterion on the whole source).** Fix the entire source of Definition 10.2, its arbitrary positive vectors (10.3), and any $\epsilon>0$. The following conditions are equivalent:

1. A finite admissible static supplement exists for (10.1) on all finite legal root histories.
2. A complete finite names-only online register exists for the same contract.
3. $A,B$ are linearly independent over $\mathbb R$.

When condition 3 holds, the rank-two integer lattice in its real span has a positive attained shortest maximum-norm length

$$
\Lambda=\mathbb ZA+\mathbb ZB,\qquad
\delta=\min_{(j,k)\in\mathbb Z^2\setminus\{(0,0)\}}
                 \|jA+kB\|_\infty>0.
\tag{10.4}
$$

The native endpoint-vector observation with no supplement recovers all histories if and only if $\delta>2\epsilon$. Moreover, with

$$
q=\left\lfloor\frac{2\epsilon}{\delta}\right\rfloor+1,
\tag{10.5}
$$

there is a common names-only update on exactly $q^2$ reachable complete states that recovers all histories. In particular, both finite minima are at most $q^2$. This is an attained construction bound, not a minimum formula for arbitrary independent $A,B$.

Proof. The vector form of Lemma 9.2 uses the same observation-intersection argument. Two closed boxes of radius $\epsilon$ about $v,w$ intersect exactly when $\|v-w\|_\infty\le2\epsilon$, since this is the interval-intersection condition in every coordinate. Their midpoint then belongs to both boxes. Consequently the necessary and sufficient condition for a static label is

$$
u\ne v,\quad z(u)=z(v),\quad h(u)=h(v)
\quad\Longrightarrow\quad
\|T(u)-T(v)\|_\infty>2\epsilon.
\tag{10.6}
$$

Sufficiency defines the decoder by the unique compatible word, rejecting outside the union of the possible observation sets. This reuses the static-confusability mechanism of [Transport–Memory Completion §§8.1–8.2 and 11.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), with the specified box geometry. It does not replace the overlap graph by equality fibers of a deterministic scalar readout.

Suppose $A,B$ are dependent. Positivity gives $B=\lambda A$ for a unique $\lambda>0$. The finite-bin obstruction in Theorem 9.3 applies on the $s$ row after scaling its scalar comparison by $\|A\|_\infty$. Explicitly, for a supplement with $Q$ values choose a positive integer $L$ with $\lambda\|A\|_\infty/L<2\epsilon$, and choose $N$ with $N+1>QL$. Put the $N+1$ fractional parts $\{m/\lambda\}$, $0\le m\le N$, into $L$ equal half-open bins. One bin contains $Q+1$ distinct indices $m_0,\ldots,m_Q$. Choose an integer $K\ge\max_i\lfloor m_i/\lambda\rfloor$, and put $n_i=K-\lfloor m_i/\lambda\rfloor\ge0$. The actual distinct words $a^{m_i}ca^{n_i}$ all end at $s$, and their totals are

$$
C+\lambda\left(K+\left\{\frac{m_i}{\lambda}\right\}\right)A.
$$

Every two have distance less than $\lambda\|A\|_\infty/L<2\epsilon$. Two must share the same label, contradicting (10.6). This covers both rational and irrational $\lambda$, uses legal nonnegative exponents, and is independent of $C,E$. Thus condition 1 implies condition 3. Every online register supplies a static label $h=\mu$, as in §9, so condition 2 implies condition 1 as well.

Now suppose $A,B$ are independent. Select two coordinates $i,j$ with $D=A_iB_j-A_jB_i\ne0$. For $w=xA+yB$, inversion of this two-row matrix gives

$$
\max\{|x|,|y|\}\le K_0\|w\|_\infty,
\qquad
K_0=\frac{\max\{B_i+B_j,A_i+A_j\}}{|D|}>0.
\tag{10.7}
$$

Thus a nonzero integer pair gives norm at least $1/K_0$. The set of integer pairs with $\|xA+yB\|_\infty\le\|A\|_\infty$ is finite by (10.7), nonempty since it contains $(1,0)$, and contains a global minimizing pair: outside this set the norm exceeds the value at $(1,0)$. Its least norm is positive and attained. These elementary lattice facts are used as a supplier inside the sourcewise proof, not as a separate new classification.

For equal endpoints $s$ or $t$, all native differences are integer combinations of $A,B$. Conversely every nonzero pair $(j,k)\in\mathbb Z^2$ is realized as a difference of two actual histories ending at $s$: choose nonnegative $(m,n),(m',n')$ with $m-m'=j,n-n'=k$, by taking positive and negative parts in each coordinate. Such histories are distinct. At $p$ differences are nonzero integer multiples of $A$, already included in the lattice comparison. Therefore the least same-endpoint distance on the entire source is precisely the attained $\delta$. Equation (10.6) for a single label proves the unsupplemented criterion, including failure at equality by an attaining pair's midpoint. The translations $C$ and $C+E$ cancel within their endpoint rows; different rows are separated by the exact endpoint.

For the online upper bound, take the entire persistent state space and unique initialization to be

$$
M=(\mathbb Z/q\mathbb Z)^2,\qquad m_0=(0,0).
$$

On this one space use the following total update for each operation name:

$$
U_a(x,y)=(x+1,y),\qquad
U_c(x,y)=(0,x),\qquad
U_e(x,y)=(x,y).
\tag{10.8}
$$

All coordinates are residues modulo $q$. In particular, $U_a$ is literally the same function at $p$ and $s$. Induction along the exhaustive word table gives

$$
\mu(a^m)=(m,0),\qquad
\mu(a^mca^n)=\mu(a^mca^ne)=(n,m)\pmod q.
\tag{10.9}
$$

The second coordinate captures the pre-$c$ count when the executed $c$ arrives, and the first then counts post-$c$ occurrences. No update tests which source vertex is current, whether $c$ has happened, or whether the word will end. A separately stored phase, mode, event index or terminal flag is absent: $(x,y)$ is the complete state. Updates on source-illegal names impose no obligation and remain the same total functions (10.8).

At endpoint $p$, equal register values for different words force a nonzero count difference divisible by $q$. At $s$ or $t$, they force both count differences divisible by $q$, and independence makes their underlying nonzero lattice vector nonzero. In every case the distance is at least $q\delta>2\epsilon$. Equation (10.6) therefore gives a decoder, simultaneously for all endpoint rows. Concretely, at $s$ subtract $C$ from $y$, at $t$ subtract $C+E$, and enumerate the nonnegative pairs satisfying $mA_1+nB_1\le y_1-b_1+\epsilon$, where $b$ is that endpoint offset. Positivity bounds both indices, so this is a finite candidate set whenever the right side is nonnegative; otherwise reject. Filter it by the final residues and all $r$ closed-box inequalities. At $p$ use the same procedure with $b=0$ and only $m$. The separation just proved gives exactly one surviving word on an allowed observation and none on an impossible one. This is a finite mathematical search with exact comparisons in the fixed real data, without a claim that unspecified real constants have an effective representation. Every pair $(x,y)\in M$ is reached at $s$ by choosing $n\equiv x,m\equiv y\pmod q$ with nonnegative representatives. Hence the construction has exactly $q^2$ reachable full states, including its initial, intermediate and terminal uses, without an extra control factor. Its induced static label has the same range, proving condition 3 implies both 1 and 2. $\square$

**Theorem 10.4 (a sharp fixed two-channel native law).** In the entire source (10.2), fix $r=2$, any $h>0$, arbitrary fixed $C,E\in\mathbb R_{>0}^2$, and the native loop vectors

$$
A=h(1,1),\qquad B=h(1,2).
\tag{10.10}
$$

For every $\epsilon>0$, the exact minimum static alphabet and exact minimum number of reachable complete online states are both

$$
s_{\min}=o_{\min}
 =\left(\left\lfloor\frac{2\epsilon}{h}\right\rfloor+1\right)^2.
\tag{10.11}
$$

The native pair without supplementation recovers all histories exactly when $h>2\epsilon$. For every integer $k\ge0$, throughout the closed-left, open-right range $kh\le2\epsilon<(k+1)h$ the common minimum is $(k+1)^2$; the case $k=0$ is restricted to $\epsilon>0$ as above. Equality $2\epsilon=kh$ is included in the larger value at that threshold.

Proof. The map from lap-count differences to normalized native differences is the integer matrix

$$
(j,k)\longmapsto(j+k,j+2k),\qquad
\begin{pmatrix}1&1\\1&2\end{pmatrix}^{-1}
 =\begin{pmatrix}2&-1\\-1&1\end{pmatrix}.
\tag{10.12}
$$

Its determinant is one, so $\Lambda=h\mathbb Z^2$ and $\delta=h$. Thus Theorem 10.3 supplies both the native criterion and an online construction on $q^2$ full states, with $q=\lfloor2\epsilon/h\rfloor+1$. It uses the already fixed (10.10), not newly assigned edge vectors.

For the matching static lower bound, set $k=\lfloor2\epsilon/h\rfloor$. For each $0\le i,j\le k$ choose the actual word

$$
u_{ij}=a^{\,k+2i-j}\,c\,a^{\,k+j-i}.
\tag{10.13}
$$

Both exponents are nonnegative, since their minima are respectively zero and zero. They give distinct words because (10.12) is invertible, and they all end at $s$. Their normalized two loop totals are

$$
(m+n,m+2n)=(2k+i,3k+j).
$$

In particular their $(k+1)^2$ final observation boxes all contain the same point

$$
y_*=C+h\left(2k+\frac{k}{2},\,3k+\frac{k}{2}\right),
\qquad
\|y_*-T(u_{ij})\|_\infty\le\frac{hk}{2}\le\epsilon.
\tag{10.14}
$$

Any smaller alphabet gives two words the same label, and the single actual permitted decoder input $(s,\lambda,y_*)$, with $\lambda$ their shared label, then has two different required outputs. This is a lower bound on every static assignment, without a linearity or periodicity restriction, and hence on every complete online register. It is an actual translated square inside the nonnegative history cone, not a clique imported from unreachable lattice points. Appending $e$ gives the same obstruction at $t$, translated by $E$.

The construction (10.8) attains the lower bound. Its $q^2$ values are all reached by legal histories at $s$, so no phase or unused-state discount enters the equality. At $p$, the empty word is initialized at $(0,0)$ and the other histories have $(m,0)$; equal-endpoint, equal-state comparisons have gaps at least $qh$. At $s$, $c$ has value $(0,0)$, and all choices with either exponent zero obey (10.9). At $t$, $e$ preserves that same full state, and there is no later operation to track. Thus the lower and upper arguments cover the empty, zero-lap, intermediate and terminal histories simultaneously.

At a positive equality threshold $2\epsilon=kh$, equation (10.14) still holds with closed boxes. Below that threshold the corresponding $k$-wide square is no longer forced by this argument, while the upper bound with the smaller $q$ applies. This proves the exact threshold law. $\square$

The maximum-metric lattice/coding mechanism used inside this proof is classical. Qureshi–Costa, [*On cube tilings of tori and classification of perfect codes in the maximum metric*, arXiv:1512.05908v2, §2, pp.3–4, Definition 2.7 and Proposition 3.1](https://arxiv.org/pdf/1512.05908v2), study codes in $\mathbb Z_Q^n$ with the circular maximum metric, integer packing radius $e$, and their perfect-code condition $Q=(2e+1)t$. Their Cartesian code and Construction A are suppliers for periodic lattice separation; those finite-torus and integer-radius conditions are not imposed on the real final box in (10.1), and no perfect-code classification is asserted here. Theorem 10.4 connects that familiar geometry to actual nonnegative root words, this source's single shared $a$ token, and a complete online implementation attaining the static lower bound. Generic rank, lattice separation and coloring alone would not establish that last acquisition-compatible equality.

**Proposition 10.5 (each native scalar coordinate fails on this same source).** Keep exactly the source, root, vectors and $C,E$ of Theorem 10.4. For either coordinate projection $\operatorname{pr}_j$, $j=1,2$, and every $\epsilon>0$, no finite static supplement and no complete finite online register can recover all finite legal histories from the exact endpoint, supplement and one scalar observation in the full closed interval of radius $\epsilon$ about $\operatorname{pr}_jT(u)$. Nevertheless joint acquisition obeys (10.11).

Proof. This is the scalar obstruction of Theorem 9.3 on a root path meeting two cyclic components. Here it has an infinite exact-collision witness, so does not depend on the size of the positive tolerance. For coordinate 1, fix any nonnegative integer $N$. The $N+1$ words

$$
a^mca^{N-m},\quad 0\le m\le N,
$$

all end at $s$ and all have native scalar total $C_1+hN$. For coordinate 2, the $N+1$ words

$$
a^{\,2(N-n)}ca^n,\quad 0\le n\le N,
$$

all end at $s$ and all have scalar total $C_2+2hN$. For a proposed finite alphabet of size $Q$, take $N=Q$. Pigeonhole supplies two different histories with the same label and scalar total, violating Lemma 9.2 even at error zero. An online register induces just such a label. Appending $e$ gives terminal witnesses with the same additional scalar offset $E_j$.

These two families use projections of the one fixed pair, rather than different graphs or separately tuned instruments. A scalar register with access to its scalar clock during execution, a source-state-qualified version of $a$, or a hidden archive is not the register in this proposition. Joint acquisition can cut distinctions that every individual coordinate leaves with unbounded multiplicity; it still requires the finite supplement of (10.11) once $2\epsilon\ge h$. $\square$

**Proposition 10.6 (duplicate channels and the error-metric boundary).** Retain the first two channels of (10.10). Additional channels $j=3,\ldots,r$ may have arbitrary fixed positive $C_j,E_j$, but suppose each loop pair $(A_j,B_j)$ is exactly one of $(h,h)$ and $(h,2h)$. Under the full $r$-dimensional box (10.1), both minima remain exactly (10.11). Without these hypotheses an additional positive channel need not preserve either minimum or the threshold.

Proof. For a same-endpoint difference, every added coordinate is a copy of either the first or the second difference. Since the first two remain present, the full maximum norm equals their two-coordinate maximum norm. Thus the source's confusability comparisons, including the lower-bound square, are unchanged. To see simultaneous overlap directly, extend (10.14) by the corresponding copied loop-coordinate center, adding the appropriate $C_j$ (and $E_j$ at $t$). Every error coordinate is bounded by $hk/2\le\epsilon$. The common register (10.8) remains valid and reaches exactly the same full states.

For a counterexample to unrestricted addition, let $r=4$ and append amplified loop-coordinate pairs $(Lh,Lh)$ and $(Lh,2Lh)$ for some $L>1$, with all connecting coordinates positive. The same-endpoint norm becomes $L$ times the original two-coordinate norm, its shortest length is $Lh$, and the translated-square and register arguments give the different exact minimum $(\lfloor2\epsilon/(Lh)\rfloor+1)^2$. For instance $L=2$ and $2\epsilon=h$ give minimum one instead of four. This compares different fixed native laws conditionally; it is not an operation that upgrades the original instrument.

Likewise, an invertible recoding of the acquired joint data preserves recovery when its entire observation sets are transported. It does not license replacing the transported sets by new boxes of the same numerical radius. This is the vector form of the calibration distinction in Proposition 8.6. Taking two calibrated coordinates from the same execution is not supplied by two marginal laws from unrelated executions. $\square$

**Proposition 10.7 (same-source endpoint transport and resource limits).** Replace the exact endpoint in Definition 10.1 by any already acquired faithful typed boundary or spatial representation $b:V\to Y$, injective on this same actual three-state residual image. Keep the same jointly acquired vector and final supplement. All existence criteria, achieved bounds and exact minima of Theorems 10.3–10.4 and Propositions 10.5–10.6 are unchanged. Whenever recovery holds, the observations determine every fixed lossless chronological memory target $m(u)$; the recovered word determines the modeled endpoint, exact native vector and declared response sequence from $p$. These statements give no inverse from each unaugmented coordinate individually, no bound on total chronological storage, and no physical spatial-dimension interpretation of $r$ or of rank two.

Proof. Apply the actual-image observation-set bijection of Theorem 8.5, leaving $H$ and $\mathbb R^r$ untouched:

$$
(z,\lambda,y)\longmapsto(b(z),\lambda,y),\qquad
(\beta,\lambda,y)\longmapsto(b^{-1}(\beta),\lambda,y).
$$

It preserves the complete observation set belonging to each actual word, and therefore preserves every static feasibility statement and its alphabet cost. The names-only online updates are unchanged, so it also preserves their complete-state feasibility and minima. If boundary or spatial data represent the entire process, their use additionally requires a rooted typed named-graph isomorphism preserving every legal operation, successor, complete response and each native vector coordinate, as in Remark 4.2 and Theorem 8.5. Induction then transports precisely the same words and totals. A bare endpoint relabeling does not prove this stronger process correspondence.

Losslessness of $m$ gives an inverse on its actual word image, while a decoder for $u$ can be followed by $m$. Replay evaluates the stipulated deterministic model from its fixed initial state, without a new source query. The realized error vector is not determined by $u$: for a single word every $\eta$ in the box is allowed. It is recovered only if the acquired $y$ is retained too, by $\eta=y-T(u)$. Endpoint, boundary or spatial coordinates alone cannot distinguish the infinitely many $a^m$ ending at $p$; Proposition 10.5 supplies the stronger failure of each native scalar coordinate even with finite memory. Thus these are conditional augmented recovery maps, not pairwise inverses of unaugmented time, space, boundary and memory.

For unbounded resources, $T(a^m)=mA$ is unbounded in every coordinate because $A$ is positive, and $y=T(a^m)$ is itself an allowed observation. The finite online state therefore does not bound clock range. Histories $a^m$ have arbitrarily long names-only input and unbounded decoded output length; a fixed finite retained record alone cannot encode all those distinct chronological targets. Source and decoder descriptions, exact endpoint and final-state acquisition, native vector knowledge, calibration, observation storage and output storage remain distinct assumptions or costs. Mathematical separation supplies no uniform decision procedure for arbitrary unspecified real constants, saturation tolerance, drifting calibration, or noisy endpoint or register acquisition.

The static/online distinction here reuses Definition 9.1 and [Transport–Memory Completion §§16–17](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md). Its stable-partition mechanism is supplied by `DynamicsDescent.dynamics_descends_iff` and `DynamicClosureMinimality.dynamic_closure_is_least`; the present construction verifies the common update explicitly on legal root words. [Arithmetic Refinement Memory §§1 and 3](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_REFINEMENT_MEMORY.md) instead require a source-canonical record: the same current integer must always carry the same value. Here the finite register is a function of root history and may take many values at the same source vertex. Conflating these contracts would change the minimum problem. `DefectGraphMinimumColoring` supplies finite deterministic-readout repair, whereas the boxes here use the nontransitive overlap relation already treated in Transport–Memory Completion §§8 and 11. `ExactRollbackInjectivityCriterion` supplies exact joint-record inversion; its exact deterministic input does not by itself establish bounded-error box separation. `ConfigurationPathTransport` concerns configurations and path transport, not the shared-name register cost. The exponential-orbit contract of `TwoClockKrylovClosure`, the visible action-output archives of `ArchiveClockRecovery`, and the time-parameterized affine updates of `TimeOrderedPrimeMemoryCocycle` supply no replacement for the names-only feed in (10.8).

The sourcewise joint criterion and its sharp complete-state realization are repo-derived ordinary mathematical consequences of these declared models and suppliers. The general path-schema, confusability, linear-rank and lattice/coding mechanisms are reused, without a literature-priority claim. No general finite-graph classification, general chain of $k$ cycles, sharp near-parallel native family, physical realization, physical spacetime law, model-diversity statement or Lean/kernel verification is asserted. $\square$

## 追加锚（本行以下为增补区）

