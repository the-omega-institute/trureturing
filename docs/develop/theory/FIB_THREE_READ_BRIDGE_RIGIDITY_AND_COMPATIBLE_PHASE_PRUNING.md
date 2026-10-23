# FIB three-read bridge rigidity and compatible phase pruning

Analytical phase pruning transfers active-edge constructions to the original paid-read problem without deleting any actual call. It gives radius five whenever both pruned active trees have height at most two, even if the original finite total cap is larger. For cap three, a continuation-compatible placement gives radius seven for every input whose first edge touches its target spin in that edge's active phase. Separately, the full law of the inherited three-read bridge witness forces every representative to query the two ends of a detached three-edge path before its middle bridge. This classifies all its representatives and its four minimum-radius address triples.

These are partial results. The unrestricted three-read interval remains $7\le\rho_{\mathrm{law}}(3;p,j,\nu)\le15$, and the universal polynomial-versus-superpolynomial radius question remains unresolved. Ordinary proofs below carry the conclusions; neither a supplied checking disposition nor a formal certificate is a premise. The relative increments are those of the supplied Three-read proposal, with the independent Three-read check retaining its checking contribution. No external-literature priority is asserted.

**Text convention.** This is mathematical reference input using numbered `generic-v1` claims and GitHub math delimiters, without asserting ingestion or a ledger state. Subsequent additions belong beyond the terminal append anchor.

## 1. One source, the actual endpoint, and the law being preserved

**Definition 1.1 (Original stationary integer-clock source).** Fix any single

$$
0<p<1,\qquad p\ne\tfrac12,\qquad j\in\{0,1\},
\qquad \pi_0=1-p,\quad\pi_1=p.
$$

Let $\varphi$ be uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. With $\mathcal A=\{a_0,a_1,b_0,b_1\}$, the original joint law $J_p$ is

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

This is Original Proposition 2.1 and (2.2), on its actual emitted-bit clock. An active transition goes from $a_s$ to $b_t$ with probability $\pi_t$, emitting $s\oplus t$; a separator transition copies $b_t$ to $a_t$ and emits zero. The state masses are $\pi_s/2$ for both $a_s$ and $b_s$: the incoming mass at $b_t$ is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying gives the same mass at $a_t$. Independence of the next spin gives these ordered transition factors on every finite interval, including those beginning in either state class. Uniform phase and reindexing of the iid spins preserve the law under an integer shift. In particular $X_tX_{t+1}=0$ at every integer $t$. No separator is removed from the source.

**Definition 1.2 (Both actual endpoints).** The target is the unchanged $H_j$, written $h_{j,\varphi,S_{q_{j,\varphi}}}$. Its complete table is

$$
\begin{array}{c|c|c|c|c}
j&\phi&q_{j,\phi}&h_{j,\phi,s}&B_{j,\phi}=2q_{j,\phi}+\phi\\ \hline
0&0&0&a_s&0\\
0&1&0&b_s&1\\
1&0&1&b_s&2\\
1&1&0&a_s&1
\end{array}
\tag{1.2}
$$

Thus $q_{j,0}=j$, $q_{j,1}=0$, and every base $B_{j,\phi}$ is $j$ or $j+1$. At $j=0,\phi=1$, for example, coordinate zero is the separator following active coordinate $-1$, with hidden state $b_{S_0}$. This checks the negative-coordinate seam without moving the endpoint. The table is Original (9.4). At fixed $j$, the endpoint class $a$ or $b$ determines the phase as a mathematical event. A protocol does not observe that class for free.

**Definition 1.3 (All acquired-record rules and all paid calls).** Let $(\mathsf U,\mathcal U,\nu)$ be any given probability space independent of the entire $J_p$ source. Keep its variable $u$ and its law unchanged, and put $\mathbb P_p=J_p\otimes\nu$. All internal randomness and random public data belong to this same independent variable. Fixed public data may include $p,j$ and the cap.

A finite acquired record is an ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n.
\tag{1.3}
$$

A measurable next-event rule uses only the public data, $u$ and this record. Its next event is a read at an integer address, a finite return of a state in $\mathcal A$, or indefinite internal continuation without further read or return. A finite event may follow internal waiting; its occurrence, kind, address or output, and finite waiting time are measurable functions of these same available data. Waiting provides no further source observation. A call at $t$ receives only the actual $X_t$ of (1.1).

Every call costs one: negative, positive, remote and disconnected addresses, repetitions, and compulsory separator zeros are all charged. Ignoring a reply does not refund its call. Immediate returns, wrong-phase output states, and internal nonreturn after any finite count, including zero, are allowed. Null records and the usual measurable completion versions are included. Before imposing a total cap, infinite-read nonreturn is also allowed.

There is no new coin, source-dependent seed or timing, phase or spin oracle, hidden-state read, free half-line or tail observation, reset, source switch, moving endpoint, or erased-coordinate substitution. There is no connectedness, consecutiveness, predetermined-address or always-returning restriction. These are the operations of Original Definition 9.1 and Paid-return Definition 1.2.

**Definition 1.4 (Total cap, full law and radius).** Let $N$ count all actual calls and let $\tau$ be the return time, with $\tau=\infty$ on every nonreturn. A pathwise hard total cap $k\in\mathbb N_0$ means $N\le k$ on every execution, including nonreturns and exceptional source or seed paths. Set

$$
D=\mathbf1_{\{\tau<\infty\}},\qquad
O=\begin{cases}A&D=1,\\\bot&D=0,\end{cases}
\qquad Z=(H_j,O,D,N),\quad\bot\notin\mathcal A.
\tag{1.4}
$$

The required objective is exactly equality of the joint law of $(u,Z)$. Under cap $k$, the finite alphabet is

$$
\mathcal Z_k=\{(h,o,d,n):h\in\mathcal A,\ o\in\mathcal A\cup\{\bot\},
\ d=\mathbf1_{\{o\ne\bot\}},\ 0\le n\le k\}.
\tag{1.5}
$$

In particular every measurable seed event retains its correlations with the other coordinates. A nonreturn at count $n$ remains internal continuation forever after $n$ paid calls. A return-only cap is insufficient: $k+1$ repeated calls followed by nonreturn obey every cap restricted to returns but cannot have their $N$-law represented under total cap $k$.

A radius-$R$ rule uses only integer addresses with $|t-j|\le R$. Write $\rho_{\mathrm{law}}(k;p,j,\nu)$ for the least nonnegative radius representing every lawful total-cap-$k$ input with the same seed and full law. Literal records, numerical address names, tree shapes, potential replies at unvisited nodes, signatures, numerical finite return times, and equality on each original source sample are not preserved statistics. Upper constructions may retain some of these as sufficient construction properties; lower-bound competitors are not required to do so. Public dependence on the one fixed $p$ remains permitted throughout.

## 2. Semantic trees, finite products and the given seed

**Lemma 2.1 (Inherited tree and source-section interface).** A lawful total-cap-$k$ rule has a measurable representation $u\mapsto T(u)$ by a countable discrete space $\mathcal T_k$ of finite ordered binary read trees of height at most $k$. Read nodes have integer addresses. Terminals have labels in $\mathcal A\cup\{\bot\}$ and retain their exact paid depths. The representation preserves $Z$ and the actual read sequence, while capping every formal binary branch. A consistent terminal path with replies $x_i$ and successive addresses $t_i$ has source section exactly $\{X_{t_i}=x_i:1\le i\le n\}$.

Proof. Replace numerical finite internal waits by fixed finite waits, retaining finite events and indefinite internal continuation as different event types. At a formal record of length $k$, replace a further read request by internal nonreturn without that call, keeping a return or an existing nonreturn. No actual capped execution reaches a suppressed read request. A finite number of finite waits remains finite; thus return, output, count and the read sequence are unchanged.

At fixed $u$, unfold the resulting semantic choices. A read has two ordered children, one for each binary reply; a finite return or internal nonreturn is a terminal. There is no read at depth $k$, and at most $2^k-1$ read nodes if $k\ge1$. A repeated address is still a distinct paid node. A terminal's depth is its actual $N$, also when its label is $\bot$.

There are finitely many bounded-height shapes and terminal-label patterns, and a finite integer tuple for each shape, so $\mathcal T_k$ is countable. At any potential node the preceding record $r(u)$ has countable range. For a measurable action condition $F(u,r)$, evaluation at that record is measurable because its event is

$$
\bigcup_r\bigl(\{u:r(u)=r\}\cap\{u:F(u,r)\}\bigr).
\tag{2.1}
$$

Induction through the finitely many potential positions proves measurability of $T(u)$; absent positions may receive dummy labels. Finally, at fixed seed, the replies on a consistent path determine all its choices and finite versus indefinite events. Internal waiting adds no source condition, giving the cylinder assertion. For permitted completion versions choose measurable versions together over the countably many records; the resulting null changes leave the integrated laws unchanged. This is the semantic interface of Original Theorems 12.2–12.3, also used by Stopping and Two-read. It does not decide internal divergence of arbitrary code. $\square$

**Lemma 2.2 (Two directions of the same-seed argument).** Suppose a specified map $C:\mathcal T_k\to\mathcal T_k$ preserves each tree's source law of $Z$. Then $C(T(u))$ gives one lawful full-law representative on the unchanged seed space. Conversely, a full-law representative of an input ignoring $u$ has that input's deterministic source law at almost every seed.

Proof. Put $a_{T,p}(z)=J_p(Z^T=z)$. Every map on the countable discrete tree space is measurable. Select $C(T(u))$ using the seed and public data and run it with actual replies. On records inconsistent with that selected tree prescribe internal nonreturn. The countable measurable partition into selected trees and the finite record tests on each cell make this a total measurable rule. Its formal cap is inherited from the selected tree. For every $G\in\mathcal U$ and $z\in\mathcal Z_k$, independence gives

$$
\begin{aligned}
\mathbb P_p(u\in G,Z^{\mathrm{input}}=z)
&=\int_G a_{T(u),p}(z)\,d\nu(u)\\
&=\int_G a_{C(T(u)),p}(z)\,d\nu(u)\\
&=\mathbb P_p(u\in G,Z^{\mathrm{new}}=z).
\end{aligned}
\tag{2.2}
$$

The alphabet is finite, so these rectangle identities give the whole joint law.

For the converse, let $w_z$ be the seed-ignoring input's source vector and $a_z(u)$ the normalized competitor's measurable source masses. Full-law equality gives $\int_G(a_z-w_z)\,d\nu=0$ for every $G$. If $a_z-w_z$ were positive on a set of positive measure, one of the measurable sets where it exceeds $1/n$ would contradict that identity. Apply the same argument to its negative. Thus $a_z=w_z$ almost everywhere, and intersection over the finite $z$ alphabet gives a measurable full-measure set of good seeds with the exact deterministic vector $w$.

These are integrals of source sections, without regular conditional probabilities given singleton seeds. They work on arbitrary atomic or nonstandard spaces, split no seed atom, add no randomness, and survive the permitted completions. This is the inherited source-section method, including Stopping Lemma 2.2 and Two-read Lemma 2.2. $\square$

**Lemma 2.3 (Unordered spin-graph identity).** Fix one phase and its target spin index $q$. A bijection of finite occupied spin vertices fixing $q$ and carrying each labelled queried unordered edge to its replacement preserves the joint law of $S_q$ and those edge XORs.

Proof. Include $q$ as an isolated occupied vertex if necessary. For a spin assignment $s$ on the occupied vertices $V$, its probability is $\prod_{v\in V}\pi_{s(v)}$. Transporting $s$ along the bijection preserves this product, the target value and every labelled XOR. Sum over assignments. XOR is symmetric in its two endpoints, so reversal of an unordered edge is allowed. Distances and unqueried adjacencies between distinct vertices impose no spin equality and need not be retained. The identity holds at each $p$. Different incompatible continuation branches may use different proof bijections, provided the actual addresses at their common earlier nodes are identical. $\square$

## 3. The inherited two-active-read placement with arbitrary terminal tags

**Lemma 3.1 (Two-edge placement and its common root).** Fix $q\in\mathbb Z$ and a first unordered integer-line edge $E$. A tree of active height at most two admits a placement with every edge left endpoint in $[q-2,q+2]$, preserving each terminal's joint mass with $S_q$. Terminals may carry any finite set of tags. The root placement is common to all its second-node alternatives. The following complete table specifies the second edge $F$; numbers are left-endpoint offsets from $q$, and $w$ denotes the endpoint of $E$ other than $q$ when $q\in E$.

| First-edge relation | Second-edge relation | Root left offset | Second left offset |
| --- | --- | --- | --- |
| $q\in E$ | $F=E$ | $0$ | $0$ |
| $q\in E$ | $E\cap F=\{q\}$ | $0$ | $-1$ |
| $q\in E$ | $E\cap F=\{w\}$ | $0$ | $1$ |
| $q\in E$ | $E\cap F=\varnothing$ | $0$ | $2$ |
| $q\notin E$ | $F=E$ | $1$ | $1$ |
| $q\notin E$ | one shared vertex, $q\in F$ | $1$ | $0$ |
| $q\notin E$ | one shared vertex, $q\notin F$ | $1$ | $2$ |
| $q\notin E$ | disjoint, $q\in F$ | $1$ | $-1$ |
| $q\notin E$ | disjoint, $q\notin F$ | $1$ | $-2$ |

Proof. Two line edges are equal, meet in one vertex, or are disjoint. If the root contains $q$, a shared vertex is $q$ or $w$, and a disjoint child cannot contain $q$. If the root excludes $q$, a meeting or disjoint child either contains $q$ or excludes it. These alternatives exhaust the nine rows, including both orientations and arbitrary integer distances.

For equal edges identify their two endpoints, fixing $q$ if incident and keeping it isolated otherwise. For meeting edges identify the shared vertex and the two edge-labelled outer vertices. The displayed placements put $q$ respectively in the middle, at the root-side end, at the child-side end, or outside that path, exactly as required. For disjoint edges identify each pair separately, fixing $q$ on its incident edge or as an isolated vertex. In the last row the pairs are $\{q+1,q+2\}$ and $\{q-2,q-1\}$, genuinely disjoint and excluding $q$. In the touching-root disjoint row they are $\{q,q+1\}$ and $\{q+2,q+3\}$. Thus each row has the vertex bijection of Lemma 2.3 and preserves $(S_q,X_E,X_F)$.

Use the touching or detached root placement once. For each reading child separately choose its table row. A terminal on root reply $x$ has joint mass $J_p(S_q=s,X_E=x)$; a terminal on the second reply $y$ at child $x$ has mass $J_p(S_q=s,X_E=x,X_{F_x}=y)$. Each is preserved by the relevant marginal identity. The terminal events partition execution, so every terminal-tag mass is preserved. The proof does not require a joint potential-reply identity between the two second-node alternatives. A one-read tree uses the root marginal; a no-read tree is unchanged. All listed left endpoints lie in the asserted interval.

This is Two-read Lemma 3.1 and the one-phase branch argument of its Theorem 3.2, reused with arbitrary tags. The finite-tag extension follows from the same individual terminal masses, without a new probability theorem. $\square$

## 4. Phase pruning without deleting paid calls

**Definition 4.1 (Pruned analytical tree and original paid tag).** For a normalized finite tree $T$ and $\gamma\in\{0,1\}$, form $P_\gamma(T)$ recursively. Retain every parity-$\gamma$ read node with both children. Bypass each opposite-parity read node through its zero child. A retained terminal carries the tag

$$
\lambda=(v,\ell,n),
\tag{4.1}
$$

where $v$ is its original terminal position in $T$, $\ell\in\mathcal A\cup\{\bot\}$ its original label, and $n$ its original paid depth in $T$. Active height counts only retained reads. Tags keep the original paid depth rather than this active depth.

**Theorem 4.2 (Phase-pruning transfer).** Suppose each $P_\gamma(T)$ has a specified relabelling of its active integer-line edges preserving, conditional on $\varphi=\gamma$, the joint law of its actual target spin and terminal tag. The two relabellings combine into one lawful relabelling of the original $T$ preserving its source law of $Z$. Every original read node, label and paid terminal depth is retained. Specified choices on countably many trees yield the full same-seed law for arbitrary measurable inputs.

Proof. In phase $\gamma$, every opposite-parity read of the original source replies zero surely. Its execution therefore reaches exactly the original terminal recorded by $P_\gamma(T)$. This is an identity of analytical executions. The terminal's tag still records every original paid call, including bypassed separators and repeated reads, and distinguishes original terminals even if their output labels agree.

An original node has a single parity $\gamma$. If it occurs in $P_\gamma(T)$, assign it the actual new address $2e'_v+\gamma$ prescribed by that relabelling. If it is absent, assign it $B_{j,\gamma}$. Absence means that some opposite-parity ancestor was followed through its one child on the path to this node. Such a node is unreachable in its own active phase for every assignment retaining node parities. In the other phase it is a separator whenever visited, so its arbitrary same-parity placement changes no reply there. Thus no original position receives conflicting address demands from the two constructions.

Run the whole original tree with these one-time address assignments. In phase $\gamma$, its inactive nodes still reply zero, so its target/tag law is the preserved law of $P_\gamma(T)$. The tag determines $O,D,N$ using $\ell,n$, and (1.2) converts the target spin to the actual $H_j$. Average the two conditional identities using the original phase weights $1/2,1/2$. This proves equality of the whole source vector of $Z$.

No pruned tree is executed by the protocol. Every visited original node still makes and pays its actual call, and the original height caps every formal branch. In particular a terminal with label $\bot$ and original depth $n$ remains internal nonreturn after $n$ calls, even if its active depth was smaller. Selection never asks for the realized phase.

The prescribed operations define a map on the countable discrete space of original normalized trees. Composing with $T(u)$ is measurable, and Lemma 2.2 gives the full joint-law identity on every seed rectangle. If choices are specified only on a subclass, extend the map arbitrarily by a fixed capped tree off that subclass. No regular conditional distribution, new coin or atom splitting is involved. $\square$

**Corollary 4.3 (Bounded active height gives radius five at any finite cap).** For every finite original total cap $k$, every lawful input for which both pruned trees have active height at most two at each seed has a lawful full-law representative with addresses in $[j-4,j+5]\cap\mathbb Z$. It retains every original terminal label and paid depth, including nonreturn counts. A fixed supplied tree has one relabelling independent of $p$ working for all allowed $p$.

Proof. Apply Lemma 3.1 to each $P_\gamma(T)$ with target $q_{j,\gamma}$ and tags (4.1). The preserved individual terminal masses give exactly the conditional target/tag identity needed by Theorem 4.2. Each active left endpoint is in $[q_{j,\gamma}-2,q_{j,\gamma}+2]$, hence its actual address is in $[B_{j,\gamma}-4,B_{j,\gamma}+4]$. Absent positions use $B_{j,\gamma}$. Since every base is $j$ or $j+1$, all addresses lie in $[j-4,j+5]$, of radius five. Theorem 4.2 and Lemma 2.2 retain all counts and give the measurable lift. Geometry alone specifies the choices, and Lemma 2.3 holds at every $p$.

This hypothesis is not automatic. A tree making $k$ successive same-parity calls has matching-phase active height $k$. Thus the corollary does not give a general radius-five bound at larger budgets. $\square$

## 5. A target-touching first edge with compatible continuations

**Theorem 5.1 (Common first and second placements for every third alternative).** In one fixed phase, let $q$ be the distinguished target vertex and let the first unordered edge $E$ contain $q$. Write $w$ for its other endpoint. For every second integer-line edge $F$, there is a placement of $E,F$ such that every possible third integer-line edge $G$ individually has a placement preserving their finite labelled unordered graph with distinguished $q$. The first placement is always $E'=\{q,q+1\}$; the same second placement works for all alternatives $G$. Every placed left endpoint lies in $[q-3,q+3]$.

All numbers in the table are left-endpoint offsets from $q$. A repeated $G=E$ or $G=F$ always uses its already placed edge. A bridge means an actual line edge with one endpoint in each of two disjoint queried pairs; a fresh endpoint is outside $E\cup F$.

| Second-edge configuration | Second offset | Nonrepeated third-edge configuration and offset |
| --- | --- | --- |
| $F=E$ | $0$ | meets only $q$: $-1$; meets only $w$: $1$; disjoint from $E$: $2$ |
| $E\cap F=\{q\}$ | $-1$ | extends the outer $F$ endpoint: $-2$; extends at $w$: $1$; disjoint from both: $2$ |
| $E\cap F=\{w\}$ | $1$ | extends at $q$: $-1$; extends the outer $F$ endpoint: $2$; disjoint from both: $-3$ |
| $E,F$ disjoint, bridge incident to $q$ | $-2$ | bridge: $-1$; fresh extension at $w$: $1$; fresh extension of $F$: $-3$; disjoint from both: $2$ |
| $E,F$ disjoint, bridge incident to $w$ | $2$ | bridge: $1$; fresh extension at $q$: $-1$; fresh extension of $F$: $3$; disjoint from both: $-3$ |
| $E,F$ disjoint, no bridge | $3$ | fresh extension at $q$: $-1$; at $w$: $1$; at either $F$ endpoint: $2$; disjoint from both: $-3$ |

Proof. First prove exhaustion and then verify the common placements. Two line edges are equal, meet in one vertex, or are disjoint. For a root containing $q$, the shared vertex is $q$ or $w$. In the first three rows their union is a one-edge or two-edge path. A further edge repeats an existing edge, extends an outer endpoint, or is vertex-disjoint from that path. There is no new edge attaching at an internal vertex: its two incident line edges are already in the path.

In the first row the placed pair is just $\{q,q+1\}$ twice. Its endpoint extensions have offsets $-1,1$, and $\{q+2,q+3\}$ is disjoint. In the second row the placed path has vertices $q-1,q,q+1$, with $q$ in the middle. Its extensions have offsets $-2,1$, and $\{q+2,q+3\}$ is disjoint. In the third row the path has vertices $q,q+1,q+2$, with $q$ at its root-side end. Its extensions have offsets $-1,2$, and $\{q-3,q-2\}$ is disjoint. The edge labels distinguish the two path ends where necessary. These placements retain the distinguished target position and all specified edge intersections.

Now suppose $E,F$ are disjoint. An edge $G$ either repeats one of them, joins them, meets exactly one of them with its other endpoint fresh, or meets neither. A joining edge exists precisely when the nearest vertices of the two pairs are consecutive integers. It is then unique, and its endpoint on $E$ is $q$ or $w$. Otherwise no bridge exists. This proves exhaustion of the last three rows and their third-edge alternatives.

If the old bridge is incident to $q$, place $F$ at $\{q-2,q-1\}$. The bridge is $\{q-1,q\}$. The available fresh extensions are $\{q+1,q+2\}$ at $w$ and $\{q-3,q-2\}$ at the outer $F$ endpoint; $\{q+2,q+3\}$ is disjoint from both original pairs. There is no omitted fresh extension at $q$: its only non-$E$ incident edge is the bridge. Likewise, the inner $F$ endpoint has only its $F$ edge and the bridge, so the listed outer extension is the only fresh one there.

If the old bridge is incident to $w$, place $F$ at $\{q+2,q+3\}$. Its bridge is $\{q+1,q+2\}$, its fresh extension is $\{q+3,q+4\}$, and the root's available fresh extension is $\{q-1,q\}$. The pair $\{q-3,q-2\}$ is disjoint from both. The bridge occupies the only non-$E$ incident edge at $w$ and the only non-$F$ incident edge at its inner endpoint, so no further fresh extension case exists.

If there is no old bridge, place $F$ at $\{q+3,q+4\}$. Both root extensions $\{q-1,q\}$ and $\{q+1,q+2\}$ have fresh endpoints outside $F$. Represent a fresh extension at either old endpoint of $F$ by $\{q+2,q+3\}$. For that particular third-edge identity, map the old attaching endpoint of $F$ to $q+3$ and its other endpoint to $q+4$. This can interchange the endpoints of $F$ between two proof bijections; $F$ is unordered, disjoint from $E$, and excludes $q$, so its already placed edge is unchanged. The pair $\{q-3,q-2\}$ represents a third component disjoint from both. Any extra adjacency across an unqueried gap imposes no equality on the distinct iid spins.

In each case the indicated map is a bijection on occupied vertices, fixing $q$ and carrying all labelled edges $E,F,G$ to their specified replacements. On a connected path the shared vertices and labelled outer vertices determine the map. On a detached component its endpoints can be interchanged as just described. Repeated edges retain their two vertices. Lemma 2.3 consequently proves

$$
\operatorname{Law}(S_q,X_E,X_F,X_G)
=\operatorname{Law}(S_q,X_{E'},X_{F'},X_{G'}),
\tag{5.1}
$$

and its shorter marginals, for every allowed $p$ in the fixed phase. The actual $E',F'$ are common to all alternatives; only the proof bijection can vary. Therefore each identity is a genuine marginal identity for one set of actual earlier placements. No joint potential-reply identity between incompatible third alternatives is claimed. Every displayed left endpoint is between $q-3$ and $q+3$, including $F$ at $q+3$ and its extension at $q+2$ in the final row. This proves the theorem. $\square$

The extra information used to choose the second placement is whether and where a future bridge can exist. The two-edge law alone does not record that information. The theorem uses the target-touching hypothesis; it supplies no such placement theorem for detached first edges.

## 6. The radius-seven cap-three subclass

**Theorem 6.1 (Target-touching root upper bound).** Fix any allowed $p$, either $j$, and any unchanged independent seed space. Suppose a lawful hard-total-cap-three input has, at each seed, a normalized tree that is an immediate terminal or whose root edge contains $q_{j,\alpha}$, where $\alpha$ is that root address's parity. Then it has one lawful full-law representative with every address in $[j-6,j+7]\cap\mathbb Z$, hence radius at most seven. The representative keeps the original ordered tree, all terminal labels and all paid terminal depths, including $\bot$ at any depth. One relabelling of any fixed supplied tree works for every allowed $p$.

The root hypothesis is the public integer condition

$$
t_{\mathrm{root}}\in\{B_{j,\alpha}-2,B_{j,\alpha}\}.
\tag{6.1}
$$

It requires no observation of the realized phase.

Proof. Fix a normalized deterministic tree $T$. Keep an immediate terminal, including immediate nonreturn. Otherwise let $\alpha$ be the root parity and set $q=q_{j,\alpha}$. In its matching phase, $P_\alpha(T)$ retains the target-touching root $E$ and has active height at most three. Place that root at $\{q,q+1\}$. For each reading second node $F$ use its row of Theorem 5.1; for each reading third node $G$ below it use the appropriate third-edge entry. All second nodes share the one placed root, and both third alternatives below each second node share its one placed $F$. Thus this defines actual addresses of one tree before execution.

For a terminal after one active read, its joint mass with $S_q=s$ is a coordinate of $(S_q,X_E)$. After two active reads on replies $x,y$, it is a coordinate of $(S_q,X_E,X_{F_x})$. After three, its mass is

$$
J_p(S_q=s,X_E=x,X_{F_x}=y,X_{G_{x,y}}=z\mid\varphi=\alpha).
\tag{6.2}
$$

Each corresponding one-, two- or three-edge identity is supplied by Theorem 5.1. The terminal events partition execution, so these individual identities preserve the conditional target/tag law with tags (4.1). This uses neither relations between incompatible sibling replies nor a separate early placement for each final branch.

Put $\beta=1-\alpha$. In phase $\beta$ the original root is a separator and its zero branch has at most two original calls left. Hence $P_\beta(T)$ has active height at most two. Apply Lemma 3.1 at its own target $q_{j,\beta}$ with the same kind of original terminal tags. Its conditional target/tag law is preserved too.

Apply Theorem 4.2 to combine the two constructions. Every original node receives a single actual integer address from its own parity, or the fixed same-parity base if absent from its matching prune. Execution uses the original whole tree. In each actual phase the relevant conditional law holds, and averaging the original phase mixture gives the $Z$-law. Every separator and repeated occurrence still costs one at its visited original node; every original terminal depth still gives $N$. The height bound holds on all formal branches, including exceptional source and seed paths.

Matching-root-phase left endpoints are in $[q_{j,\alpha}-3,q_{j,\alpha}+3]$, so their actual addresses are in $[B_{j,\alpha}-6,B_{j,\alpha}+6]$. The other phase's constructed addresses are in $[B_{j,\beta}-4,B_{j,\beta}+4]$; absent nodes use their bases. By (1.2), their union is contained in $[j-6,j+7]$.

The finite incidence tests and listed placements are specified maps on the countable discrete tree space. Their composition with $T(u)$ is measurable. Lemma 2.2 proves the full $(u,H_j,O,D,N)$ identity for every seed event, including on atomic or nonstandard spaces with permitted completions. The choices use only integer geometry and $j$, and the product identities hold at every allowed $p$. If the input uses public $p$, apply them to its tree at that fixed parameter; no joint measurability in varying $p$ is needed. No phase oracle, additional randomizer or free observation enters the construction. $\square$

This is a subclass upper, without a claim that seven is its exact universal minimum. Together with Corollary 4.3 it covers inputs with both pruned heights at most two and cap-three inputs with a target-touching root. A detached-root active-phase tree of height three remains outside this construction.

## 7. The inherited bridge law and all-representative rigidity

**Proposition 7.1 (Bridge witness and its complete source vector, inherited).** Put

$$
\psi=1-j,\qquad q=j,\qquad B=2q+\psi=j+1,
\qquad d=p(1-p),\qquad c=\pi_0^2+\pi_1^2=1-2d.
\tag{7.1}
$$

The seed-ignoring rule $V_j$ first reads $j+7$, returning $a_0$ on one; on zero it reads $j+3$, returning $a_0$ on one; on two zeros it reads $j+5$, returning $a_1$ on one and $a_0$ on zero. All waits may be fixed finite waits. It returns on every branch and has total cap three. For both $s\in\{0,1\}$, its complete nonzero source masses are

$$
\begin{aligned}
J_p(H_j=b_s,O=a_0,D=1,N=1)&=\frac{\pi_s}{2}\,2d,\\
J_p(H_j=b_s,O=a_0,D=1,N=2)&=\frac{\pi_s}{2}\,2dc,\\
J_p(H_j=b_s,O=a_1,D=1,N=3)&=\frac{\pi_s}{2}\,2d^2,\\
J_p(H_j=b_s,O=a_0,D=1,N=3)&=\frac{\pi_s}{2}\,(c^2-2d^2),\\
J_p(H_j=a_s,O=a_0,D=1,N=3)&=\frac{\pi_s}{2}.
\end{aligned}
\tag{7.2}
$$

All other tuples have mass zero. Each mass jointly with $u\in G$ is multiplied by $\nu(G)$ for every $G\in\mathcal U$. This is the witness and law of Two-read Proposition 5.1.

Proof. In phase $\psi$, the endpoint is $b_{S_q}$ and the three zero-branch spin edges, in query order, have left endpoints $q+3,q+1,q+2$. The first two edges are disjoint from one another and from $q$. Each pair has XOR-one probability $2d$ and zero probability $c$. The first and second stopping probabilities are therefore $2d$ and $2dc$.

On two zeros both pairs are constant. The bridge XOR is one exactly when their constants differ. Each of the two opposite-constant assignments has product mass $\pi_0^2\pi_1^2=d^2$, giving $2d^2$. The remaining two-zero mass is

$$
c^2-2d^2=\pi_0^4+\pi_1^4>0.
\tag{7.3}
$$

All these events exclude the target spin and hence are independent of it. Their probabilities sum to $2d+2dc+c^2=1$, since $2d+c=1$. In the other phase every queried address is a separator and the rule returns $a_0$ at count three. The phase factors $1/2$ and target factors $\pi_s$ give (7.2), including its zero coordinates. Seed independence gives the rectangle masses. This verifies the supplied law directly. $\square$

**Theorem 7.2 (Necessary and sufficient geometry for every representative).** Fix any single allowed $p,j,\nu$. Every lawful hard-total-cap-three rule with the full $(u,H_j,O,D,N)$ law of $V_j$ has the following form at almost every seed, after the semantic normalization of Lemma 2.1. The first read and the next read on zero have parity $\psi$ and query the two end edges, in either order, of a consecutive three-edge spin path detached from $q$. Each of their one children returns $a_0$ at its own paid depth. On two zeros the third read has parity $\psi$ and queries the middle bridge, returning $a_1$ on one and $a_0$ on zero. Conversely these geometry and stopping conditions give exactly the full witness law, also under any measurable selection of such trees on the unchanged seed space.

The necessary conclusions concern actual positive-source executions. Numerical finite waits and actions on inconsistent source-null records are not fixed by the law; every such action remains subject to the hard total cap and to any asserted radius. No prefix, record, signature, tree shape or samplewise-preservation premise is imposed on the competitor.

Proof. Begin with an arbitrary competitor, allowing public-$p$ dependence, arbitrary measurable seed use, immediate or wrong-phase returns, internal nonreturn, and every integer address. Normalize it. Lemma 2.2 gives a measurable full-measure set of good seeds at which its entire deterministic source vector equals (7.2). Fix one good seed. Call $\varphi=\psi$ phase $B$ and the other phase $A$. By (1.2), these are the endpoint classes $b$ and $a$, respectively. This identification is used only for mathematical conditioning. Both target spin values have positive probability in either phase.

In phase $A$ the required output, return indicator and count are $(a_0,1,3)$ surely. In phase $B$, (7.2) requires the four positive terminal masses displayed there, conditional on each target value. There is no count-zero or nonreturn mass. The root must therefore read. If its parity were opposite to $\psi$, its phase-$B$ reply would be zero surely. The positive required count-one mass would force a finite return on its zero child. In phase $A$ this root would instead be active, with probability $c>0$ of reply zero. The same action on that zero child would return at count one on a positive phase-$A$ section, contradicting its required count three. Hence the root parity is $\psi$.

The root-zero child is reached surely in phase $A$, so cannot return or internally diverge there. Only the root-one child can supply the positive count-one mass in phase $B$. Its next event, determined at this fixed seed and record, must consequently be a finite $a_0$ return at count one. Call the root edge $E$. The full target law now requires

$$
J_p(X_E=1\mid\varphi=\psi,S_q=s)=2d
\qquad(s=0,1).
\tag{7.4}
$$

If $E$ contained $q$, the left side would be $\pi_{1-s}$, since its other spin is an independent Bernoulli$(p)$ spin. Equality for both $s$ would force $\pi_0=\pi_1$, contradicting the bias. Thus $E$ is detached from $q$, and its zero cylinder has probability $c$ given either target value.

A second read on root zero is forced by phase $A$'s count three. If that read had parity opposite to $\psi$, its phase-$B$ reply would be zero surely. Since the root-one child already returns, the prescribed positive count-two mass would force a finite return on the second-zero child. In phase $A$ the first read was a separator, imposing no spin condition; the newly active second edge gives reply zero with probability $c>0$ there. The same count-two return would contradict the phase-$A$ law. Hence the second parity is also $\psi$.

Its zero child is reached surely in phase $A$ and must continue to a third read. Its one child is the only possible source of the required count-two mass and must return $a_0$ at count two. Denote this second edge by $F$. Averaging the prescribed full target masses within phase $B$ gives

$$
J_p(X_E=0,X_F=1\mid\varphi=\psi)=2dc.
\tag{7.5}
$$

If $F=E$, this probability is zero. If $E,F$ share one vertex, their zero-one labels require two equal spins and one opposite, giving

$$
\pi_0^2\pi_1+\pi_1^2\pi_0=d.
$$

This calculation holds for either shared endpoint and either orientation. But

$$
0<d<\tfrac14,\qquad c>\tfrac12,\qquad 2dc-d=d(2c-1)>0,
\tag{7.6}
$$

so neither possibility gives (7.5). The two edges must be vertex-disjoint. If this disjoint $F$ contained $q$, the detached $E$ would be independent of $F$ and the target. The conditional count-two probability would be $c\pi_{1-s}$, whereas (7.2) requires $2dc$ for both $s$. Division by $c>0$ again contradicts $\pi_0\ne\pi_1$. Thus $F$ also excludes $q$.

Write

$$
C=\{X_E=0,X_F=0\}.
$$

The two pairs and the target have disjoint spin supports, so

$$
J_p(C\mid\varphi=\psi,S_q=s)=c^2\qquad(s=0,1).
\tag{7.7}
$$

The third read on this record is forced by phase $A$'s count three. A fourth call is forbidden by the total cap; nonreturn on a positive section is forbidden by $D=1$. If the third parity were opposite to $\psi$, it would be active in phase $A$, where both preceding replies were separators. Its two replies have positive probabilities $c$ and $2d$ there. Both terminal actions would therefore have to return $a_0$ at count three. In phase $B$ the third reply would then be separator zero and would use the same $a_0$ action. Every earlier terminal already returns $a_0$, leaving no possible $a_1$ mass, contrary to the positive $2d^2$ in (7.2). Thus the third parity is $\psi$.

Its zero child, reached surely in phase $A$, returns $a_0$. Its one child must be reachable in phase $B$ and return $a_1$. Let $G$ be its active edge. Equations (7.2) and (7.7) force

$$
J_p(X_G=1\mid\varphi=\psi,C,S_q=s)
=\delta,\qquad \delta=\frac{2d^2}{c^2},\qquad s=0,1.
\tag{7.8}
$$

This is a full-law consequence at the fixed public bias. The protocol is not permitted to choose different terminal actions according to an unobserved target value.

Under $C$, each of the two disjoint pairs is constant, with common spin Bernoulli$(r)$, where

$$
r=\frac{p^2}{c},\qquad 1-r=\frac{(1-p)^2}{c}.
\tag{7.9}
$$

Their two common spins are independent of each other, of $S_q$, and of all outside spins. Outside spins remain independent Bernoulli$(p)$. Indeed the conditioning indicator is the product of the equality indicators on the two disjoint pairs; dividing each finite iid product by $c^2$ gives precisely these factors. Further conditioning on $S_q=s$ fixes only that independent coordinate.

The following table covers every possible integer-line edge $G$. Here a fresh vertex lies outside $E\cup F\cup\{q\}$; only rows realizable by actual consecutive integer endpoints are available.

| Third edge type | One-probability given $S_q=0,C$ | One-probability given $S_q=1,C$ |
| --- | --- | --- |
| repeats $E$ or $F$ | $0$ | $0$ |
| joins the two conditioned pairs | $2r(1-r)=2d^2/c^2$ | $2r(1-r)=2d^2/c^2$ |
| joins target to a conditioned pair | $r$ | $1-r$ |
| joins target to a fresh vertex | $p$ | $1-p$ |
| joins a conditioned pair to a fresh vertex | $d/c$ | $d/c$ |
| joins two fresh vertices | $2d$ | $2d$ |

All probabilities in the table are also conditioned on $\varphi=\psi$. A repeat is zero because that pair is already constrained equal. Two different pair constants disagree with probability $2r(1-r)$. A fixed target compared with a pair constant gives $r,1-r$; compared with a fresh spin it gives $p,1-p$. For a pair-to-fresh edge the probability is

$$
p(1-r)+(1-p)r
=\frac{p(1-p)^2+(1-p)p^2}{c}=\frac d c.
\tag{7.10}
$$

Two fresh spins disagree with probability $2d$.

For exhaustion, the two distinct endpoints of $G$ lie in the first pair, the second pair, the singleton target, or the fresh vertices. Both endpoints in one conditioned pair give exactly its original edge. Endpoints in different pairs can give only their actual joining line edge, if one exists. An endpoint at the target gives exactly one of the two target rows. The remaining combinations are pair-to-fresh and fresh-to-fresh. There is no loop or pair of distinct target vertices on the integer line. Thus negative, remote, repeated, target-touching and disconnected choices are all included; no radius restriction has been used.

At the fixed allowed parameter, $c>2d$ as well as $c>1/2$, and therefore

$$
0<\delta=\frac{2d^2}{c^2}<\frac d c<2d.
\tag{7.11}
$$

The first strict comparison has ratio $2d/c<1$, and the second has ratio $1/(2c)<1$. Also $r\ne1-r$ and $p\ne1-p$. Both target values have positive probability, and (7.8) requires the same $\delta$ for both. Consequently neither target row works, and the repeat, pair-to-fresh and fresh-to-fresh rows fail by (7.11). The third edge must join the two conditioned pairs.

Two disjoint line edges joined by one line edge are the two end edges of a consecutive three-edge path. To see this explicitly, write the left pair as $\{L,L+1\}$. Its nearest vertex to the right pair is $L+1$; a joining edge forces the other pair to begin at $L+2$, so it is $\{L+2,L+3\}$, and the unique bridge is $\{L+1,L+2\}$. Since $q$ is in neither end pair, it is outside all four vertices, including both bridge endpoints. This establishes all asserted geometry, parities and stopping actions from Full alone. Positive-probability nonreturn has been excluded by the required law, not by a restriction of the competitor class. Source-null choices and null seed changes cannot alter these good-seed deductions.

For sufficiency, take any such detached path, querying its two end edges in either order, returning $a_0$ on either of their one replies, and reading the middle edge on two zeros with the stated final outputs. Its end pairs are independent of one another and of $S_q$. The same finite products as in Proposition 7.1 give the four phase-$B$ terminal probabilities $2d,2dc,2d^2,c^2-2d^2$. In phase $A$ all three calls are separators and give $(a_0,1,3)$. Multiplication by $\pi_s/2$ gives every coordinate of (7.2) and no other mass. Every formal branch returns after at most three paid calls. Thus each such deterministic tree has the same vector $w$. Any measurable selection of them using the original seed preserves Full by (2.2); arbitrary lawful exceptional null-seed choices do not change that law. This proves the converse and completes the classification. $\square$

## 8. Exact witness radius, minimum triples and prefix failure

**Corollary 8.1 (Minimum radius and all four attaining triples).** Among all lawful total-cap-three representatives of the full law of $V_j$, its exact minimum radius is seven, at each single allowed $p$, either $j$, and every unchanged independent seed space. At radius seven, the first, second-on-zero and third-on-two-zero address triple is, at almost every seed, exactly one of

$$
\begin{aligned}
&(j+3,\ j+7,\ j+5),\qquad (j+7,\ j+3,\ j+5),\\
&(j-7,\ j-3,\ j-5),\qquad (j-3,\ j-7,\ j-5).
\end{aligned}
\tag{8.1}
$$

Each triple with the forced stopping actions is a lawful attainer. Every measurable same-seed choice among the four gives the same full law without an additional randomizer.

Proof. At a good seed of any competitor, Theorem 7.2 gives path vertices $[L,L+3]\cap\mathbb Z$ with $q$ outside. If $L\ge q+1$, its right end edge has left endpoint $L+2\ge q+3$, hence actual address at least

$$
2(q+3)+\psi=j+7.
\tag{8.2}
$$

If $L+3\le q-1$, its left end edge has left endpoint $L\le q-4$, hence address at most

$$
2(q-4)+\psi=j-7.
\tag{8.3}
$$

In phase $A$ all three zero-branch calls are actually executed surely. Thus the forced extreme call is reached on a section of source mass at least $1/2$ at every good seed; it is not an unreachable formal-node obstruction. Integration over good seeds excludes any smaller radius, even if the radius were interpreted almost surely. Proposition 7.1 is already a radius-seven realization, proving equality.

At radius seven a parity-$\psi$ edge left endpoint satisfies

$$
|2e+\psi-j|\le7
\quad\Longleftrightarrow\quad q-4\le e\le q+3.
\tag{8.4}
$$

A detached right-hand three-edge path in this interval must have left endpoints $q+1,q+2,q+3$: its first is at least $q+1$ and its last at most $q+3$. A detached left-hand path must have endpoints $q-4,q-3,q-2$, since its last vertex is at most $q-1$. The two end orders and the forced middle last give exactly (8.1). The converse part of Theorem 7.2 proves each attains the full law.

More generally, a measurable integer choice $L(u)$ with $L(u)\ge q+1$ or $L(u)\le q-4$, together with a measurable binary choice of end order, selects lawful detached-path trees. Their source vectors are all $w$, so Lemma 2.2 gives the same full law. At the minimum radius the choice reduces to four measurable cells; neither prescribed cell measures nor splitting seed atoms is needed. Null seed or inconsistent-record modifications must still satisfy the cap and any asserted radius. $\square$

The number seven is already the inherited universal lower $2k+1$ at $k=3$. The new conclusion is the necessary and sufficient classification of this particular law and its attaining triples; it adds no universal lower bound above seven. The witness and its displayed radius-seven realization are supplier-owned.

**Corollary 8.2 (Identical prefix law need not admit continuation).** The inherited bridge witness's first two placements can be replaced by $j+3$ and $j-3$ on root zero while preserving the full joint law of the target and both potential prefix replies. They also preserve the stopped prefix law, with the second reply omitted when not acquired. Yet no lawful total-cap-three continuation of these fixed prefix actions preserves the full witness law. This remains true with unrestricted subsequent integer addresses and arbitrary measurable use of the original seed and fixed public bias, also when the prefix is required only at almost every seed.

Proof. In phase $\psi$ the original first two edges are $\{q+3,q+4\}$ and $\{q+1,q+2\}$. The replacement pair is

$$
E'=\{q+1,q+2\},\qquad F'=\{q-2,q-1\}.
\tag{8.5}
$$

Both configurations have two disjoint pairs, each detached from $q$. Given either $S_q=s$, their two potential replies are independent pair XORs with probabilities $c,2d$ for zero and one. In the opposite phase all these addresses are separators. The actual endpoint table and the phase weights therefore give the same target/potential-reply-pair law, including every seed rectangle. Applying the deterministic operation that acquires the second reply only on root zero gives the stopped-prefix law too.

If a full-law continuation existed, intersect its good-seed set from Lemma 2.2 with the full-measure set of prescribed prefix actions. Theorem 7.2 would force an actual line edge joining the two pairs (8.5). Their nearest vertices are $q-1,q+1$, which have the target $q$ between them and are not consecutive. No such joining edge exists. This contradicts the necessary classification at every good seed, regardless of the third address or any seed-dependent choice. The pair $(j+3,j+7)$, in contrast, has the actual bridge $j+5$ and is an attainer by (8.1).

The conditional calculation underlying this failure is explicit: after two zeros the pair constants are independent Bernoulli$(r)$ as in (7.9), and Full requires bridge-one probability $\delta$ at both target values. The exhaustive table in Theorem 7.2 allows that kernel only through an actual line edge between the pairs. Preserving the prefix distribution retains the pair XOR laws but need not leave that edge available in the chosen placement. This is why a prefix law does not imply extendability. No stronger prefix- or signature-preservation condition was imposed on the full-law lower argument. $\square$

The specified frozen-prefix example and its no-continuation conclusion already belong to Two-read Propositions 5.1–5.2 and Theorem 6.1. Corollary 8.2 relates them to the all-representative classification rather than claiming a new example.

## 9. Inherited comparisons and the exact remaining targets

**Proposition 9.1 (Unchanged unrestricted information).** For the complete original law-only problem and every fixed allowed $p,j,\nu$, the inherited exact values and bounds are

$$
\begin{aligned}
\rho_{\mathrm{law}}(0;p,j,\nu)&=0,\\
\rho_{\mathrm{law}}(1;p,j,\nu)&=3,\\
\rho_{\mathrm{law}}(2;p,j,\nu)&=5,\\
2k+1\le\rho_{\mathrm{law}}(k;p,j,\nu)&\le2^{k+1}-1
\qquad(k\ge1).
\end{aligned}
\tag{9.1}
$$

In particular the established unrestricted budget-three comparison remains

$$
7\le\rho_{\mathrm{law}}(3;p,j,\nu)\le15.
\tag{9.2}
$$

Justification and ownership. Stopping Corollary 6.1 supplies the all-$k$ linear lower against all lawful full-law representatives, and its Theorem 6.2 supplies the zero/one values. Address Theorem 4.1 supplies the upper $2^{k+1}-1$ by packing all potential nodes. Two-read Theorem 3.2 supplies the upper five at cap two, matching Stopping's lower, as stated in Two-read Theorem 4.2. These are inherited mathematical results with their owning proofs, not consequences of a checking verdict or newly claimed numerical bounds here. The subset and witness results of this volume change none of the unrestricted bounds. $\square$

**Boundary 9.2 (Whole-signature growth is a different objective).** Address Theorem 5.2 gives exact radius $2^{k+1}-1$ for preserving the entire oriented whole-tree signature, including potential relations between incompatible branches. It does not give that lower bound for Full. Its witness always returns $a_0$ with $D=1,N=k$. Make $k$ paid repetitions of the actual address $j$, ignore the replies and return $a_0$. This radius-zero rule has the same joint law of $(u,H_j,O,D,N)$ on the unchanged source and seed, proving the limitation directly. Neither the two-active-read construction nor Theorem 5.1 needs the entire potential-node signature. Each compares the target and replies on the particular executed path, with common actual earlier placements.

**Open question 9.3 (Unrestricted budget three).** Does every original hard-total-cap-three rule have a radius-seven full-law representative on its unchanged given seed space, or is there an obstruction above seven against every lawful full-law equivalent? Theorem 6.1 is restricted to target-touching roots. Corollary 4.3 handles both pruned heights at most two. In the root's inactive phase there are at most two original calls left; the remaining case for this construction route is a detached root with a three-active-read branch in its matching phase.

A sufficient extension of the route would give compatible common early placements for all such trees, or a different construction preserving Full. Retaining shape, parities and individual path laws would suffice, but those properties are not necessary requirements on a law-only representative. A failure of that stronger placement strategy would not refute the unrestricted law-only upper. The bridge classification treats one witness law and gives no lower obstruction above seven.

**Open question 9.4 (Unchanged all-budget growth problem).** Does every original total-cap-$k$ input have an exact full-law representative in a radius bounded polynomially in $k$, or is there a superpolynomial obstruction for Full against every lawful equivalent? All quantifiers remain those of Section 1: each fixed biased interior parameter, both actual endpoints, every unchanged arbitrary independent seed space, all measurable acquired-record rules, and every paid call on returning and nonreturning paths.

The general lower and upper in (9.1) decide neither alternative. The conditional active-height bound does not bound active height of a general input. A polynomial upper still needs one actual compatible adaptive tree across all branches and both phases and a measurable same-seed lift, or a different complete law-only construction. A superpolynomial lower still needs an invariant of the executed full law that survives every allowed change of tree, addresses and labels. An obstruction for a frozen prefix or whole signature does not supply that invariant. Neither this bounded partial result nor any inherited comparison settles the separate original finite-hidden attainment and separation problem.

## 10. Mathematical ownership, evidence and scope

**Attribution 10.1 (Source identities and the relative increments).** The names used in this volume refer to the following supplied mathematical bodies. Their ordinary proofs, definitions and hypotheses are the mathematical sources; their dispositions are not approval premises.

| Name and complete supplied identity | Retained mathematical ownership |
| --- | --- |
| Original: *FIB harmonic-edge load: fixed-state tail nonuniformity and an erasure-risk jump*, supplied as `current-original-source.md` | Proposition 2.1 and (2.2), Definition 9.1, (9.4), and Theorems 12.2–12.3 own the original stationary source, actual endpoint, acquisition semantics, semantic trees and same-given-seed interfaces. Sections 13–14 own the seed-partition image, compact attainment and budgeted-return projection; those background conclusions are not increments here. |
| Paid-return: *FIB paid reads: return mass and hidden-endpoint classification risk*, supplied as `current-risk-source.md` | Definitions 1.2–1.3 and Section 6 retain all-call charging, return/nonreturn distinctions and resource limits. Its risk inequalities and frontiers are separate from the address and rigidity arguments. |
| Address: *FIB finite paid reads: explicit address compression and the exact whole-signature radius*, supplied as `address-source.md` | Lemmas 3.1–3.2, Theorems 4.1 and 5.2, and Open question 5.3 own component packing, the exponential universal upper, the exact stronger-signature radius and its law-only limitation, and the all-budget radius target. |
| Stopping: *FIB stopping-law rigidity and sharp linear address radius*, supplied as `linear-stopping-source.md` | Theorems 3.2, 4.1, 5.1–5.2, Corollary 6.1 and Theorem 6.2 own its stopping witness, forced path and target detachment, exact witness radius $2k+1$, sharp remote-read probability, universal lower and zero/one values. The numerical universal lower seven at cap three is already included. |
| Two-read: *FIB two-read law radius and frozen-prefix obstruction*, supplied as `two-read-source.md` | Lemma 3.1 and Theorems 3.2, 4.2 own the universal two-read upper and exact value five, consolidating its proposal and checking contributions. Propositions 5.1–5.2 and Theorem 6.1 own the bridge witness, full masses, equivalent frozen prefix and its failure of continuation. |
| Three-read proposal: `proposed-three-read-results.json`, supplied from the three-read thinking conclusion | The relative increments P, E, U3-touch and B3-rigidity: tagged phase-pruning transfer, the common target-touching three-edge placement, its complete cap-three subclass upper, and all-representative bridge-law rigidity with its converse and minimum triples. This volume gives those results its own full exposition in Sections 4–8 and retains proposal ownership. |
| Three-read check: `independent-three-read-check.json`, supplied independent mathematical checking conclusion | Independent ordinary checking proofs of precisely P, E, U3-touch and B3-rigidity, including the exhaustive incidence and conditional third-edge cases. Their proof substance informs the exposition; support of a result is not used in place of a proof. |

The increment over the five prior theory bodies is precisely the four supplied three-read partial results, not the source, finite representative existence, two-read optimum, witness definition, frozen-prefix example or inherited numerical lower seven. Finite iid products, XOR symmetry, integer-line incidence and product-measure integration retain their usual mathematical meaning. The synthesis is `repo-derived` relative to the seven supplied bodies. No external-literature search, exhaustive novelty comparison, worldwide priority, prior-sterility or model-diversity claim supports it. Nested attributions are not promoted to independent certification.

**Boundary 10.2 (Parameters and lawful realization).** Every lower classification and strict comparison is at one fixed $0<p<1$, $p\ne1/2$, even against competitors using that public parameter. At fairness $2c-1=0$, the strict scalar comparisons fail and the two target-conditioned probabilities become symmetric. At $p=0,1$ the positive stopping masses vanish. Those parameters are outside the contract, and no varying-parameter identity is a substitute for the fixed-$p$ proof.

Analytical phase conditionings, hypothetical potential replies and pruned trees are devices for finite probability identities in the same original source. The actual upper representative is one original-shape integer-address tree and pays every visited call. The lower argument starts from all lawful representatives; its stopping and parity conclusions are deductions from Full. Nonreturn is included in the upper constructions at every original paid depth and is excluded on positive sections of bridge competitors only by the prescribed $D=1$ law. Source-null and seed-null changes cannot evade the total cap.

**Boundary 10.3 (Semantic existence and other resources).** For a supplied finite tree whose return and internal-nonreturn terminals are already specified, the incidence tables give finite explicit relabellings. The reduction from arbitrary measurable rules to such trees and the same-seed lift are semantic existence arguments. They neither decide divergence of arbitrary internal code nor compute a selector for arbitrary presentations of seed spaces, and hence supply no effective arbitrary-code compiler.

Full-law equality is not equality of original and replacement records or outputs on each realized source sample. Numerical finite return times are not preserved. A total hard cap is not an expected-cost-only constraint or a cap restricted to returns. No result here concerns unbounded-history compilation, an optimal larger-budget risk frontier, or optimal expected paid cost. Address radius does not bound internal work, address encoding, precision, persistent state, memory or physical storage. No empirical-learning or neural-transfer assertion follows. The separate original attainment target and the broader research objective remain unresolved.

All mathematical conclusions here rest on the ordinary finite-product, branch-mass and source-section proofs in the text. They assert no Lean-kernel validation, machine admission, numerical execution, experiment or test evidence. The authorized partial proof obligations are presented in full; independent mathematical assessment and the unrestricted targets remain distinct from this source's claims.

## 追加锚（本行以下为增补区）
