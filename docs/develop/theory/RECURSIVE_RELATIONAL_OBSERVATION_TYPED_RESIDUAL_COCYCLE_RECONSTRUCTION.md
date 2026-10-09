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
