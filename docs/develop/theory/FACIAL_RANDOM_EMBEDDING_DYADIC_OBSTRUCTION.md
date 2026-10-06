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

1. [enumerate_signed_rotations.py](../../reports/facial-random-embeddings/enumerate_signed_rotations.py), using the doubled permutation face cycles
2. [verify_ribbon_boundaries.mjs](../../reports/facial-random-embeddings/verify_ribbon_boundaries.mjs), independently counting each physical ribbon boundary once

The full [integer certificate](../../reports/facial-random-embeddings/k4_uniform_certificate.json) lists all 64 fixed-rotation representatives, the checks, and pinned source identifiers. [Reproduction instructions](../../reports/facial-random-embeddings/README.md) give the exact commands.

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

The paper's phrase “random embedding” by itself does not determine every possible distribution. The refutation applies to the explicit independently sampled rotations and signs implemented in the authors' notebook. If the intended law is different, that law must be stated before its corresponding expectation assertion can be judged.

## 追加锚（本行以下为增补区）
