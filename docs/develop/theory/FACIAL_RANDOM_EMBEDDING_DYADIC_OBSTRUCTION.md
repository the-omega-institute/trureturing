# Dyadic obstruction to exact thirds under the Ghanbari–Šámal uniform sampler

## 1. Source and scope

Ghanbari and Šámal, *Facial diagrams and cycle double cover*, arXiv:2605.01410v1, Section 4, Conjecture 1, proposes exact expectations $m/3$ for each of the three edge types of a random embedding of a bridgeless cubic graph. The types are regular (the two edge sides are in different faces), good singular (one face traverses the edge twice in the same direction), and bad singular (one face traverses it in opposite directions).

The paper does not specify a probability law in its conjecture text. The authors' public notebook provides an explicit law: independently shuffle each vertex's neighbours to get a cyclic order, and independently choose a fair edge-sign bit. This note concerns that signed-rotation-system law. It does not claim a result for a different probability law on unlabelled topological embeddings.

Sources, verified 2026-10-06:

- Paper: https://arxiv.org/html/2605.01410v1, Section 4, Conjecture 1
- Author notebook pinned at repository commit `0d4404941894d3ef8dd9f27f1e61829bec2bcde5`: https://github.com/babakghanbari993/cdc-random-embeddings/blob/0d4404941894d3ef8dd9f27f1e61829bec2bcde5/notebooks/random_embedding_experiment.ipynb
- Notebook blob: `82fb13311d4c9ef254d644ab021346915e61618a`
- Relevant functions: `random_pi`, `random_lambda`, `random_embedding`, `count_good_bad_regular`

No Lean compilation, frozen theorem, or full repository admission is claimed. The proof below is mathematical prose, with exact integer checks from independent Python implementations.

## 2. A reusable finite-symmetry counting theorem

**Theorem 2.1 (Equivariant marginal denominator).** Let a group $H$ act on a nonempty finite set $E$ and on a nonempty finite probability space $\Omega$ with uniform law. Suppose the action on $E$ is transitive. Let $T:\Omega\times E\to\{0,1\}$ satisfy

$$
T(h\omega,he)=T(\omega,e)
\qquad(h\in H,\omega\in\Omega,e\in E).
$$

Write $N=|\Omega|$, $m=|E|$, and $C(\omega)=\sum_{e\in E}T(\omega,e)$. There is an integer $k$ with $0\le k\le N$ such that

$$
\mathbb E C = \frac{mk}{N}.
$$

Consequently, for relatively prime integers $a,b$ with $b>0$, the equality $\mathbb EC/m=a/b$ requires $b\mid N$. If it fails, the sharp arithmetic lower bound is

$$
\left|\frac{\mathbb EC}{m}-\frac ab\right|\ge\frac1{bN}.
$$

Proof. Fix $e_0\in E$. For each $e$, transitivity supplies $h$ with $he_0=e$. The permutation $\omega\mapsto h\omega$ is a bijection from the event $T(\omega,e_0)=1$ to $T(\omega,e)=1$. All these events therefore have the same integer cardinality $k$. Interchanging the two finite sums gives $\sum_\omega C(\omega)=mk$. If $k/N=a/b$, then $bk=aN$; coprimality implies $b\mid N$. If unequal, $|bk-aN|$ is a positive integer, hence at least one. ∎

**Corollary 2.2 (Fair-bit obstruction).** Under the hypotheses of Theorem 2.1, if $N=2^r$, no fixed type has expected count $m/3$.

Proof. Otherwise $3\mid2^r$, a contradiction. ∎

The denominator obstruction is sharp as an arithmetic bound: whenever coprime a,b and N admit integers k with |bk-aN|=1 and 0≤k≤N, an equivariant classifier with marginal k/N attains equality (take a trivial action on Ω and the same k-element event for every edge).

The result is about a uniform transitive marginal. An arbitrary aggregate integer-valued count on a dyadic space can have integer expectation $m/3$ when $3\mid m$. Thus edge transitivity cannot be omitted from this proof.

## 3. Signed rotation systems and relabelling

Let $G=(V,E)$ be a finite simple cubic graph. An outcome is a pair $(\rho,t)$:

- $\rho_v$ is a cyclic order on the three neighbours of $v$
- $t_e\in\{0,1\}$ is an edge-sign bit

There are exactly two cyclic orders at each vertex. Each of the six shuffled neighbour lists gives one of them, with exactly three lists per cyclic order. Thus the notebook's law is uniform on

$$
\Omega_G=\prod_{v\in V}\{\text{two cyclic orders at }v\}\times\{0,1\}^{E},
\qquad |\Omega_G|=2^{|V|+|E|}.
$$

Use flags $(v,w,s)$, where $vw\in E$ and $s\in\{0,1\}$. Each edge has four flags. Define two fixed-point-free involutions by

$$
P(v,w,1)=(v,\rho_v(w),0),
\qquad
L(v,w,s)=(w,v,s\mathbin\oplus t_{vw}),
$$

and extend the first formula by involutivity. The connected components of the graph whose edges are the $P$- and $L$-pairs are the physical boundary curves of the ribbon embedding. Equivalently, the cycles of the product $PL$ give two oriented representatives of each boundary curve. Capping the boundary curves by disks produces a cellular embedding in a connected closed surface when $G$ is connected. Orientability is not imposed, in agreement with the notebook's `do_twist=True` default.

**Theorem 3.1 (Automorphism equivariance of edge types).** Every graph automorphism $h$ permutes $\Omega_G$ in a probability-preserving way and sends each edge to an edge of the same type in the relabelled outcome.

Proof. Transport every cyclic order by the neighbour bijection induced by $h$, and set $t'_{h(e)}=t_e$. This is a bijection of outcomes, so it preserves the uniform law. The flag bijection $(v,w,s)\mapsto(hv,hw,s)$ conjugates both $P$ and $L$ to the involutions of the transported outcome. It therefore transports boundary components and their edge traversals. Equality or opposition of two directed traversals is preserved under vertex relabelling. Thus regularity, good singularity, and bad singularity are each preserved. ∎

**Theorem 3.2 (Edge-transitive cubic obstruction).** For every finite nonempty simple cubic graph whose automorphism group is edge-transitive, each of the three edge types has expected count different from $|E|/3$ under the author notebook's uniform signed-rotation law.

Proof. Apply Corollary 2.2 to each type indicator, using Theorem 3.1. ∎

This includes every graph in the theorem that is bridgeless. It does not require enumerating faces and does not rely on any sampled numerical estimate.

## 4. The K4 counterexample

**Theorem 4.1 (K4 refutes exact thirds under the author-implemented model).** Under the signed-rotation law specified above, the three equalities in Ghanbari–Šámal Conjecture 1 all fail for $K_4$.

Proof. The graph $K_4$ has four vertices, six edges, and degree three at every vertex. It is simple and connected, and every edge lies in a triangle, so no edge is a bridge. Its automorphism group is the full symmetric group on four vertices and is transitive on edges: any bijection between the endpoints of two edges extends to a permutation of all four vertices. Theorem 3.2 applies. More explicitly, each type marginal is $k/1024$ and its expected count is $6k/1024$. Equality with two would imply $3k=1024$, impossible modulo three. ∎

## 5. Exact finite certificate

The exact enumeration uses all sixteen choices of cyclic rotation and all sixty-four choices of twist bits. The totals, in the order (good singular, bad singular, regular), are

$$
(2208,1728,2208),
\qquad
(\mathbb E G,\mathbb E B,\mathbb E R)
=\left(\frac{69}{32},\frac{27}{16},\frac{69}{32}\right).
$$

For every one of the sixteen fixed rotation choices, the sixty-four twist outcomes have total counts $(138,108,138)$. Thus the exact deviation is $(5/32,-5/16,5/32)$ from $(2,2,2)$.

The histogram of (good,bad,regular) over the 1024 outcomes is:

| Triple | Multiplicity |
|---|---:|
| (0,0,6) | 32 |
| (0,2,4) | 48 |
| (0,3,3) | 64 |
| (1,0,5) | 96 |
| (1,1,4) | 96 |
| (2,0,4) | 48 |
| (2,1,3) | 192 |
| (3,3,0) | 256 |
| (4,2,0) | 192 |

Independent implementations agree separately on all 1024 outcomes:

1. [enumerate_signed_rotations.py](https://github.com/the-omega-institute/trureturing-experiments/blob/471d22e6b425bb7b810c697122060294b8bd90c5/experiments/facial-random-embeddings/enumerate_signed_rotations.py), using the doubled permutation face cycles
2. [verify_ribbon_boundaries.mjs](https://github.com/the-omega-institute/trureturing-experiments/blob/471d22e6b425bb7b810c697122060294b8bd90c5/experiments/facial-random-embeddings/verify_ribbon_boundaries.mjs), independently counting each physical ribbon boundary once

The full [integer certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/471d22e6b425bb7b810c697122060294b8bd90c5/docs/reports/facial-random-embeddings/k4_uniform_certificate.json) lists all 64 fixed-rotation representatives, the checks, and pinned source identifiers. [Reproduction instructions](https://github.com/the-omega-institute/trureturing-experiments/blob/471d22e6b425bb7b810c697122060294b8bd90c5/docs/reports/facial-random-embeddings/README.md) give the exact commands.

Both classify repeated oriented traversals and count each graph edge once. Neither requires SageMath, floating-point arithmetic, network access, or random sampling. The general proof in Section 4 remains independent of these finite calculations.

## 6. Gauge quotient and topology scope

A vertex-gauge switch reverses its cyclic order and toggles each incident edge sign. For a switch vector q:V→{0,1}, the flag bijection (v,w,s)↦(v,w,s xor q(v)) conjugates the corner involution to that for the reversed local orders and sends t(vw) to t(vw) xor q(v) xor q(w). It leaves the underlying directed graph traversals unchanged. Thus it is a coordinate change of the same ribbon embedding and preserves every edge type. For cubic graphs the group of all vertex switches acts freely on signed rotation systems: a nonempty switch subset reverses at least one nontrivial cyclic order. Every orbit has exactly one representative with a chosen fixed rotation system, obtained by switching precisely the reversed vertices. Thus the notebook law descends to uniform measure on the $2^{|E|}$ labelled gauge classes. For K4 it is uniform on 64 classes; the refutation and exact means persist on that quotient.

Quotienting further by graph automorphisms is different: orbit sizes need not be equal, so a uniform law on unlabelled maps is not the notebook law. No such uniform law is assumed in Theorem 4.1. Nor is any conditioning on orientability, genus, or a fixed face count assumed.

## 7. The surviving expectation identity

**Theorem 7.1 (Single-edge twist balances good and regular).** Under the uniform signed-rotation law, for every fixed edge $e$,

$$
\mathbb P(e\text{ good singular})=\mathbb P(e\text{ regular}).
$$

Consequently $\mathbb E G=\mathbb E R=(|E|-\mathbb E B)/2$. This law does not imply that any expectation equals $|E|/3$.

Proof. Fix all rotations and all signs except the sign at $e$. Delete the two side connections of that band. Boundary components not meeting its four attachment endpoints are unaffected. The remaining boundary arcs give one of three perfect matchings of the four endpoints. The two choices for reattaching the band also give two perfect matchings. If the remaining-arc matching agrees with one of the reattachment matchings, that choice produces two different boundary components through $e$ (regular), while the other produces one component traversing $e$ twice in the same direction (good singular). If the remaining-arc matching is the third matching, both choices give one component with opposite traversals (bad singular). Thus toggling the one sign is a bijection between the good and regular events and preserves the bad event. The two sign choices have equal conditional probability; averaging proves the formula. ∎

This is the probability consequence of the standard ribbon-band twist operation; the corresponding good/regular surgery is also described in Ghanbari–Šámal Section 2 and Section 3. It is included as reusable structure, not claimed as a new general twist theorem. The finite certificate additionally checks this involution for all six edges in all 1024 K4 outcomes.

## 8. Extension toward the D5 topology subtree

The existing D5 binary endpoint-differential and simple-cycle-space theorem supplies the graph-algebra root. The next actual content is a finite signed-ribbon model with its involutions, physical boundary components, and edge types. The natural branch is:

1. Existing SimpleGraphCycleSpace / binary character duality
2. Flag involutions and face-orbit pairing; vertex-gauge equivalence
3. Automorphism transport of signed rotations and boundary classification
4. Equivariant-marginal denominator theorem
5. K4 exact-expectation refutation
6. General local twist involution: good-singular and regular events have equal probabilities

The last node is proved in Section 7; it supplies a valid replacement identity, without implying thirds or any CDC theorem. Formalizing the actual rotation/flag carrier, rather than merely calling an unrelated cycle-space kernel “homology”, is the substantive outward bridge.

The classical Cycle Double Cover conjecture is not treated here as an unresolved leaf: Sang-il Oum's arXiv:2607.16356v3 (2026-08-01) presents an announced July 2026 proof. This note has not independently verified that proof. The random-embedding exact-expectation claim is a separate statement; the counterexample above concerns only the explicit source model and does not depend on the CDC proof.

## 9. Boundaries and attribution

The finite denominator theorem is elementary finite probability and transitive symmetry; it is not claimed as a new general mathematical principle. The contribution is its application to the exact expectation assertion and the reusable signed-rotation/flag bridge, together with exact counterexample counts. No priority beyond the searched sources is asserted. No correspondence with the authors has been sent.

**Proposition 9.1 (A nonuniform comparison law).** There is a nonuniform law on K4 embeddings with expected counts exactly (2,2,2).

Proof. The exact certificate contains a fixed-rotation outcome with twist mask 18 and type counts (0,0,6), and one with twist mask 3 and type counts (3,3,0), using its documented convention that bit zero is untwisted. Give these outcomes probabilities 1/3 and 2/3 respectively. Their weighted count vector is (2,2,2). Averaging the law over the 24 graph automorphisms also preserves this vector and makes the distribution relabelling-invariant. This law is not the independent fair-bit sampler. ∎

The paper's phrase “random embedding” by itself does not determine every possible distribution. The refutation applies to the explicit independently sampled rotations and signs implemented in the authors' notebook. If the intended law is different, that law must be stated before its corresponding expectation assertion can be judged.

## 追加锚（本行以下为增补区）

## 10. The graph-derived conditional inventory application

**Definition 10.1 (Labelled signed flags and the sign convention).** Let $V,E$ be finite sets, let $\mathbb F_2=\{0,1\}$, and put $H=E\times\mathbb F_2$. An incidence map $v:H\to V$ specifies the ends of each edge. The two half-edges $(e,0),(e,1)$ are distinct even if they are incident with the same vertex, so loops and parallel edges are retained. Let $\rho$ be a permutation of $H$ preserving $v$, with one cycle on each nonempty incidence fibre. The flag set is $X=H\times\mathbb F_2$, with last coordinate called its side. For $t\in\mathbb F_2^E$, define

$$
 s_\rho(h,1)=(\rho h,0),\qquad
 s_\rho(h,0)=(\rho^{-1}h,1),\qquad
 t_t((e,a),b)=((e,a+1),b+1+t_e),\qquad
 f_{\rho,t}=s_\rho t_t.
 \tag{10.1}
$$

Composition is right to left. Both factors are fixed-point-free involutions: $s_\rho$ changes side and $t_t$ changes the labelled end. In these sections, sign zero reverses side across a band. Thus

$$
 t_{\mathrm{here}}=1+t_{\S3}
 \tag{10.2}
$$

on every edge: this is the complement of the Section 3 and author-notebook lambda bit. A fixed reference vector $\tau$ is interpreted in this convention; its translation to Section 3 is $1+\tau$. Complementing preserves a fair bit, but not a specified fixed sign. No quotient by graph automorphisms is taken.

For $q\in\mathbb F_2^V$, let $\rho^q$ reverse $\rho$ at precisely the vertices with $q=1$, and define

$$
 h_q(h,b)=(h,b+q(v(h))),\qquad
 (\delta q)_e=q(v(e,0))+q(v(e,1)).
 \tag{10.3}
$$

**Definition 10.2 (Partial-sign sampling and the observed outside signs).** Fix a reference sign vector $\tau\in\mathbb F_2^E$ and a randomized edge set $B\subseteq E$. Choose $q\in\mathbb F_2^V$ and $\eta\in\mathbb F_2^B$ independently and uniformly. Extend $\eta$ by zero outside $B$ and sample

$$
 f_{\rho^q,\tau+\widetilde\eta},\qquad
 \sigma=\tau+\delta q+\widetilde\eta.
 \tag{10.4}
$$

When each vertex has three incident labelled half-edges, $\rho^q$ samples all cyclic orders independently and uniformly: there are two orders, each represented by three of the six lists of those half-edges. A loop contributes two distinct half-edges. For other degrees, (10.4) is only the stated reversal-bit sampler, not uniform sampling of all cyclic orders. Isolated vertices have no flags but their $q$-bits remain in the fibre counts.

Put $F=E\setminus B$. For any $A\subseteq E$, let $c(A)$ be the number of connected components of the spanning multigraph $(V,A)$, including isolated vertices. A cycle includes a loop of length one or a pair of parallel edges of length two. Cycle parity may equivalently be tested on closed walks, with edge occurrences counted modulo two.

Let $U\subseteq E$ be the unresolved edges and fix an outside vector $a\in\mathbb F_2^{E\setminus U}$ such that the event $\sigma|_{E\setminus U}=a$ has positive probability. Define

$$
 \begin{split}
 W_B&=\operatorname{im}\delta+\mathbb F_2^B,\\
 A(a)&=\{\xi\in\mathbb F_2^U:(a,\xi)\in\tau+W_B\},\\
 d_U&=|U\cap B|+c(F\setminus U)-c(F).
 \end{split}
 \tag{10.5}
$$

This is conditioning on *normalized outside signs*. It does not condition on the original $q$ or original rotations. Fixing $q$ instead leaves only the original $B$ coordinates random.

**Definition 10.3 (The actual cut and complete inventory).** Put $S_U=\{((e,j),b):e\in U\}$. Let $r_a$ fix $S_U$ pointwise and equal the band map with signs $a$ on its complement. Write $Q_a=s_\rho r_a$. For every $e\in U$, label its actual endpoints by

$$
 \lambda(e,0)=((e,0),0),\quad
 \lambda(e,1)=((e,0),1),\quad
 \lambda(e,2)=((e,1),1),\quad
 \lambda(e,3)=((e,1),0).
 \tag{10.6}
$$

Let $J_0=(0\ 2)(1\ 3)$ and $J_1=(0\ 3)(1\ 2)$. For $\xi\in\mathbb F_2^U$, let $J_\xi$ use $J_{\xi_e}$ on the four labels at $e$, and let $\widetilde J_\xi$ extend it by the identity outside $S_U$.

For a finite permutation $f$, let $p_f(x)$ be its least positive period and set

$$
 I_f(Z)=\sum_{x\in X}\frac{Z^{p_f(x)}}{p_f(x)}.
 \tag{10.7}
$$

Each cycle contributes one monomial, including singleton cycles. This is the inventory of permutation cycles. For the two free matchings an unoriented combinatorial boundary has two opposite oriented cycles; (10.7) does not silently divide by two.

The vertex-gauge normalization is the switch of Section 6. The proof combines the established four-endpoint band-cut correspondence, actual endpoint returns, the binary cut/cycle criterion and spanning-forest counts, and complete first-return segmentation. These are inherited mathematical ingredients. The application here couples them to the conditional law of normalized signs for simultaneous graph cuts and to the complete inventory; Section 11 supplies an observable separation.

**Theorem 10.4 (Graph-derived complete conditional inventory law).** In Definitions 10.1–10.3, the following assertions hold together.

1. The map $\lambda:U\times\{0,1,2,3\}\to\operatorname{Fix}(r_a)$ is a bijection, constructed from the labelled graph incidences, and

$$
 f_{\rho,(a,\xi)}=Q_a\widetilde J_\xi.
 \tag{10.8}
$$

For every original outcome in (10.4), $h_q$ conjugates its complete permutation to $f_{\rho,\sigma}$. If that outcome satisfies $\sigma|_{E\setminus U}=a$, it also conjugates its cut on all edges of $U$ to $Q_a$, transports each actual first-return endpoint and length, and maps the whole set of untouched cycles with their original iterates.

2. The vector $\sigma$ is uniform on $\tau+W_B$, with exactly $2^{c(F)}$ original pairs $(q,\eta)$ above each supported vector. Its support is characterized by

$$
 \sum_{e\in C}(\sigma_e+\tau_e)=0
 \quad\text{for every cycle }C\text{ of }(V,F).
 \tag{10.9}
$$

Conditional on the stated positive-probability outside event, $\sigma|_U$ is uniform on $A(a)$ and $|A(a)|=2^{d_U}$. This conditional law is independent fair bits on all of $U$ if and only if every edge of $U\setminus B$ is a bridge of $(V,F)$.

3. Let $P_a$ be the actual first-positive-return permutation of $Q_a$ on $S_U$ and, for $\xi\in A(a)$, define

$$
 \begin{split}
 N_\xi&=P_aJ_\xi,\\
 \ell_\xi(x)&=\min\{k>0:Q_a^k(J_\xi x)\in S_U\},\\
 L_\xi(x)&=\sum_{j=0}^{p_{N_\xi}(x)-1}\ell_\xi(N_\xi^jx).
 \end{split}
 \tag{10.10}
$$

Let $T_a$ be the union of the $Q_a$-cycles disjoint from $S_U$. Define

$$
 \mathcal I_a(\xi)=
 \sum_{z\in T_a}\frac{Z^{p_{Q_a}(z)}}{p_{Q_a}(z)}
 +\sum_{x\in S_U}\frac{\ell_\xi(x)}{L_\xi(x)}Z^{L_\xi(x)}.
 \tag{10.11}
$$

Then the conditional distribution of the entire original inventory is the uniform distribution, with multiplicities, of these polynomials over $\xi\in A(a)$. Equivalently, for every function $\Psi:\mathbb Q[Z]\to\mathbb Q$,

$$
 \mathbb E\left[\Psi(I_{f_{\rho^q,\tau+\widetilde\eta}})
       \mid\sigma|_{E\setminus U}=a\right]
   =2^{-d_U}\sum_{\xi\in A(a)}\Psi(\mathcal I_a(\xi)).
 \tag{10.12}
$$

Under the bridge condition in assertion 2, this is the independent fair average over all $2^{|U|}$ attachments. There is no claimed converse for equality of the *inventory* distributions: the inventory can identify different sign vectors.

*Proof.* First construct the simultaneous cut interface. Outside $S_U$, $r_a$ changes the end coordinate and has no fixed point; on $S_U$ it is the identity. The inverse of (10.6) reads the edge, end and side: at end zero the index is the side, and at end one it is three minus the side. The four flags are distinct even for a loop. Substitution in (10.1) gives exactly $J_0$ or $J_1$ on each cut edge, while the extension of $J_\xi$ is the identity on every other edge. This proves (10.8), with no supplied endpoint equivalence.

For a general full sign vector $t$, denote by $r_{U,t}$ its band map with $S_U$ fixed. The explicit vertex switch satisfies

$$
 h_qs_{\rho^q}h_q=s_\rho,\qquad
 h_qt_th_q=t_{t+\delta q},\qquad
 h_qr_{U,t}h_q=r_{U,t+\delta q}.
 \tag{10.13}
$$

Indeed $q\circ v$ is constant under $\rho$ and $\rho^{-1}$. At a vertex where $q=1$, the side flip and the reversal of the local rotation interchange the two corner formulas twice, giving the first identity. The two side flips at the ends of a band add $\delta q$ to its sign. For a loop they cancel. Finally $h_q$ preserves edge labels and therefore preserves $S_U$, proving the cut identity. This is the concrete flag calculation behind the standard switch of Section 6 and Ghanbari–Šámal, Lemma 2.1. For an original outcome with normalized outside signs $a$, its normalized cut is exactly $Q_a$.

The identities give equality of every conjugated iterate. Since $h_qS_U=S_U$, a first positive visit at time $k$ is transported with the same endpoint and the same time: all earlier positive times avoid $S_U$ on one side exactly when they do on the other. Conjugating the actual reattachment transports it as well. A proper return coordinate $(x,j)$ is sent to $(h_qx,j)$ and the represented flag $f^jx$ is sent to $(h_qfh_q)^jh_qx$. Orbits avoiding $S_U$ correspond in both directions, with identical periods and transported iterates. This proves assertion 1, including the untouched branch.

Next apply the classical endpoint-gradient fibre calculation to the actual sampler map (10.4). On $F$ the preimage equations are

$$
 q(v(e,0))+q(v(e,1))=\sigma_e+\tau_e.
 \tag{10.14}
$$

Summing around a closed walk makes each vertex label cancel. Conversely choose a spanning tree and a root in each component of $(V,F)$, assign each root a bit, and sum $\sigma+\tau$ along its unique tree paths to assign all other vertices. Tree edges then satisfy (10.14). A nonforest nonloop edge satisfies it precisely when its fundamental cycle has zero parity; a loop requires precisely that its own right-hand side vanish. Thus the argument includes loops and parallel edges rather than applying a simple-graph hypothesis to them. Two solutions differ by a constant on each component, so there are exactly $2^{c(F)}$ solutions. For each solution, the coordinates on $B$ determine $\eta$ uniquely. This proves the support and equal-fibre assertions.

We record the standard forest calculations as intermediate consequences of this step. Put $\beta_F=|F|-|V|+c(F)$. Each nonforest edge gives one independent fundamental cycle; they span the binary cycle space because an even edge subset of a forest is empty, by leaf removal. Therefore

$$
 |W_B|=2^{|V|+|B|-c(F)}=2^{|E|-\beta_F}.
 \tag{10.15}
$$

Full normalized signs are independent fair exactly when $F$ is a forest. Within the specified cubic-rotation/partial-sign sampler class, the least $|B|$ achieving this is $|E|-|V|+c(E)$, attained by the complement of a spanning forest: every forest $F$ has $|F|=|V|-c(F)\le |V|-c(E)$. These are the usual cut/cycle and spanning-forest counts used to evaluate this sampler, not separate new counting principles.

For the conditional calculation, all full vectors in the affine support have equal probability, so conditioning gives a uniform law on the nonempty set $A(a)$. Differences of completions are exactly $W_B\cap\mathbb F_2^U$. A vertex difference must have $\delta q=0$ on $F\setminus U$, so it is constant on each of its $c(F\setminus U)$ components. Its differential on $F\cap U$ has kernel consisting of the functions constant on each of the $c(F)$ components of $F$. It therefore gives $2^{c(F\setminus U)-c(F)}$ possible differentials. The coordinates in $U\cap B$ are free: choose $\eta$ there to give any value, and choose it on $B\setminus U$ to cancel $\delta q$ there. This proves $|A(a)|=2^{d_U}$.

The conditional support is the whole cube exactly when every coordinate unit vector on $U$ belongs to $W_B$. A unit vector on $B$ always does. For $e\in F$, the cycle condition (10.9) permits its unit vector exactly when no cycle of $F$ contains $e$, namely when $e$ is a bridge. A nonloop edge is on a cycle exactly when its ends remain connected after deleting it; a loop is on its length-one cycle and is never a bridge. This proves the criterion for every positive-probability outside value. It also exhibits why fair marginals are weaker: projecting to $U$ leaves free coordinates on $U\cap B$ and the gradient image of $(V,U\setminus B)$ on the rest. That marginal is the full fair cube exactly when $(V,U\setminus B)$ is a forest, even if its edges lie on cycles using outside edges. The corresponding conditional total variation from the fair cube is $1-2^{d_U-|U|}$; the unconditional full-sign value is $1-2^{-\beta_F}$, by comparing a uniform subset with its ambient uniform cube.

It remains to feed this exact conditional law into the complete actual-return inventory. Equation (10.8) says that a marked flag $x$ first moves by $J_\xi$ and then by $Q_a$. Until its next visit to $S_U$, the extension of $J_\xi$ is the identity. Its next marked point is thus $P_aJ_\xi x$ and its first-return length is exactly $\ell_\xi(x)$. The required minima exist by finite permutation recurrence. An orbit of (10.8) avoiding $S_U$ is also a $Q_a$-orbit with the same iterates, and conversely, since the maps agree at every unmarked point. Hence the untouched set is exactly $T_a$ for every $\xi$.

For clarity, the complete segmentation argument underlying the weighted-return identity is as follows. Every other orbit is partitioned by its successive visits to $S_U$. The proper segment beginning at $x$ has the $\ell_\xi(x)$ flags $x,fx,\ldots,f^{\ell_\xi(x)-1}x$. A point in a finite cyclic order has a unique most recent marked point, so these segments are disjoint and exhaust the orbit. The endpoint cycle through $x$ has $p_{N_\xi}(x)$ segments; their total length is $L_\xi(x)$. A smaller positive return to $x$ would contradict either the first-visit minimality of a segment or the least endpoint period. Therefore the original least period is $L_\xi(x)$, and the segment contributes $\ell_\xi(x)Z^{L_\xi(x)}/L_\xi(x)$ to (10.7). The untouched term is unchanged. This proves the identity (10.11) for every actual attachment before any averaging.

Finally the concrete $h_q$ transports the original permutation, its actual cut segments and its untouched cycles to these normalized ones. Ordinary lengths are preserved. The equal conditional weights proved above give (10.12) for an arbitrary test of the whole polynomial, retaining correlations between different cycle counts. This proves assertion 3 and the theorem. ∎

The standard cycle-character density gives a useful expression for the same application, without constituting an additional theorem. If $\mathcal C(F)$ is the binary cycle space extended by zero on $B$, then

$$
 2^{\beta_F}\mathbf1_{t\in\tau+W_B}
   =\sum_{C\in\mathcal C(F)}(-1)^{\langle C,t+\tau\rangle}.
 \tag{10.16}
$$

To see this, multiply $1+(-1)^{\langle C,t+\tau\rangle}$ over a fundamental cycle basis and expand. For $F_\Psi(t)=\Psi(I_{f_{\rho,t}})$, inserting that density gives

$$
 \mathbb E F_\Psi(\sigma)
 =2^{\beta_F-|E|}\sum_{t\in\tau+W_B}F_\Psi(t)
 =\sum_{C\in\mathcal C(F)}(-1)^{\langle C,\tau\rangle}
   \left[2^{-|E|}\sum_{t\in\mathbb F_2^E}
       F_\Psi(t)(-1)^{\langle C,t\rangle}\right].
 \tag{10.17}
$$

This last finite interchange is only the evaluation of the established density. It does not assert that a nonzero surviving cycle produces a nonzero bias for every inventory test.

If an additive statistic also uses a label-dependent weight $w(x)$, its transport requires $w'(h_qx)=w(x)$, or the extra hypothesis $w\circ h_q=w$ if weights are held fixed. Edge- and vertex-dependent weights have this invariance; arbitrary side-dependent weights need not. Theorem 10.4 concerns the ordinary period inventory and makes no stronger fixed-weight claim.

## 11. A cubic whole-inventory obstruction with an untouched component

**Proposition 11.1 (Three parallel edges distinguish the laws).** Let $G$ have two vertices, called $0,1$, and three parallel edges $i\in\mathbb Z/3\mathbb Z$. At each vertex use reference rotation $i\mapsto i+1$. In Definition 10.2 take $\tau=0$. Then uniform rotations alone ($B=\varnothing$) and uniform independent signs at the reference rotation have different full inventory laws:

$$
 \begin{array}{c|cc}
 \text{inventory}&\text{rotations alone}&\text{independent signs}\\\hline
 2Z^6&1/2&1/2\\
 2Z^2+2Z^4&0&3/8\\
 6Z^2&1/2&1/8
 \end{array}
 \tag{11.1}
$$

More sharply, take $B=\{0\}$ and leave $U=\{1\}$ unresolved after normalization. Each normalized sign is marginally fair. Conditional on $\sigma_0=\sigma_2=1$, an event of probability $1/4$, the actual inventory is deterministically $6Z^2$. Replacing the unresolved sign by an independent fair bit would instead give $6Z^2$ and $2Z^2+2Z^4$ with probability $1/2$ each. In this comparison the untouched inventory is exactly $2Z^2$ on both sides.

*Proof.* Write a flag as $(v,i,b)$. Formula (10.1) gives

$$
 f_{\rho,t}(v,i,b)=\bigl(1-v,\ i+(-1)^{b+t_i},\ b+t_i\bigr).
 \tag{11.2}
$$

Let $A_t(i,b)=(i+(-1)^{b+t_i},b+t_i)$. A cycle of $A_t$ of even length $k$ lifts to two $k$-cycles of $f$; one of odd length $k$ lifts to one $2k$-cycle, because the vertex coordinate flips at every step. For $t=000$, $A_t$ has the two 3-cycles given by the two sides. For $t=100$ it has the single cycle

$$
 (0,0),(2,1),(1,1),(0,1),(1,0),(2,0).
$$

For $t=110$ its cycles are

$$
 ((0,0),(2,1),(1,1),(2,0)),\qquad ((0,1),(1,0)).
$$

For $t=111$ it has the three 2-cycles $((i,0),(i-1,1))$. Cyclically relabelling the three edges covers all states of weight one or two. Consequently signs of weights zero and one give $2Z^6$, weight two gives $2Z^2+2Z^4$, and weight three gives $6Z^2$. Independent signs have the eight equally likely vectors. With rotations alone, $\delta q$ is either $000$ or $111$, each with probability $1/2$. This proves (11.1).

For $B=\{0\}$, the normalized support is exactly

$$
 \{000,100,011,111\},
$$

uniformly. Every coordinate is fair, but $\sigma_1=\sigma_2$ always. The outside condition selects only $111$ and has probability $1/4$. A hypothetical fair unresolved sign would also allow $101$, whose inventory is the weight-two case above.

To verify the untouched term directly, cut edge $1$ while keeping $t_0=t_2=1$. The two cycles

$$
 (v,0,0)\longleftrightarrow(1-v,2,1),\qquad v=0,1,
 \tag{11.3}
$$

avoid every flag of edge $1$ and are untouched. The remaining four nonendpoint flags $(v,0,1),(v,2,0)$ each belong to a return segment from an edge-$1$ endpoint; hence (11.3) is the complete untouched set. The cut return from $(v,1,b)$ has length two and endpoint $(1-v,1,b)$. At sign one the attachment also interchanges $v$ while preserving $b$, so the return successor is the identity on the four endpoints. The touched inventory is $4Z^2$. At sign zero the attachment changes both $v$ and $b$, so the return successor has two 2-cycles, each with total length four. The touched inventory is $2Z^4$. Adding the same untouched $2Z^2$ proves the final assertion directly from the actual cut, rather than from a sign-vector count alone. ∎

The vertex switch and binary cycle criterion are established mathematics. The application here identifies the exact normalized conditional sampler supplied to simultaneous actual graph cuts and to their complete weighted-return inventory. Proposition 11.1 gives an explicit inventory separation with the untouched term retained. The original all-edge fair-sign sampler remains uniform after normalization; this obstruction concerns omitting some of its independent signs. No graph-independent inventory probabilities, exact-thirds statement, cycle-double-cover conclusion, or external priority for the standard ingredients is asserted.

Mathematical references: [Ghanbari–Šámal, *Facial diagrams and cycle double cover*, Lemma 2.1](https://arxiv.org/html/2605.01410v1#S2); [Archdeacon, *Topological Graph Theory: A Survey*, §2.5](https://www.math.u-szeged.hu/~hajnal/courses/PhD_Specialis/Archdeacon.pdf); [Zaslavsky, *Glossary of Signed and Gain Graphs and Allied Areas*, “balance”, “Harary bipartition”, and “potential function”](https://people.math.binghamton.edu/zaslav/Bsg/glossary.html). These supply the standard switching and balance background. The conditional-inventory formula combines the switching, cycle-space and first-return ingredients on the same labelled flag carrier.
