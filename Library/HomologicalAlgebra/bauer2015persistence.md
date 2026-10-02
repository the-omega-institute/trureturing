---
bibkey: bauer2015persistence
authors: "Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot"
year: 2015
title: "Interval decomposition and induced matching for persistence modules"
doi: null
url: https://arxiv.org/abs/1311.3681v4
claim: "Finite-chain interval classification and the exact algebraic stability/isometry theorem, including essential intervals."
strata_touched:
  - D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit
  - D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition
  - D5/S3/HomologicalAlgebra/Persistence/RealExtension
  - D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness
  - D5/S3/HomologicalAlgebra/Persistence/RealDecomposition
license: citation-only
triage: anchor
---

# Finite-chain persistence and exact algebraic stability

## 1. Sources and objects

Crawley-Boevey, *Decomposition of pointwise finite-dimensional persistence modules*, arXiv:1210.0819v3, Theorem 1.1 and its proof, supplies interval decomposition over a field. Bauer and Lesnick, *Induced Matchings and the Algebraic Stability of Persistence Barcodes*, arXiv:1311.3681v4, Sections 4–6 and 8, supplies induced matchings, algebraic stability and its converse. Chazal, de Silva, Glisse and Oudot, *The structure and stability of persistence modules*, arXiv:1207.3674, supplies the general stability framework. These are known mathematical results, not claims of new discovery. This note is reference input, not a kernel-verified assertion.

Fix an arbitrary field $K$, a finite chain of finite-dimensional $K$-vector spaces $V_0,\ldots,V_{n-1}$, and arbitrary consecutive linear maps. Write $F_{ik}$ for the actual forward composites; $F_{ii}$ is the identity. The chain may be empty and the spaces may be zero. Given finite strictly increasing real breakpoints $t_0<\cdots<t_{n-1}$, its real extension is zero before $t_0$, equals $V_i$ on $[t_i,t_{i+1})$, and equals $V_{n-1}$ on the unrestricted last tail. Structure maps are the corresponding actual composites. No terminal zero is appended.

An interval has finite birth $b$ and death $d\in\mathbb R\cup\{\infty\}$ with $b<d$. Its module is $K$ on $[b,d)$ and zero elsewhere, with identity maps between supported points. A barcode is a finite multiset; repeated intervals have distinct occurrences.

## 2. Splitting a live interval

**Theorem 2.1 (earliest live interval splitting).** In a nonzero finite diagram with actual maps $F_{ik}$, there are indices $b\le j$, vectors $w_i\in V_i$ and linear functionals $p_i:V_i\to K$ satisfying the following properties. The support is exactly $b\le i\le j$. Outside it, $w_i=0$ and $p_i=0$. On it, $p_i(w_i)=1$. For $i\le k$,

$$
F_{ik}(w_i)=\begin{cases}w_k&b\le i\text{ and }k\le j,\\0&\text{otherwise},\end{cases}
\qquad
p_k\circ F_{ik}=\begin{cases}p_i&b\le i\text{ and }k\le j,\\0&\text{otherwise}.\end{cases}
$$

Consequently $x\mapsto p_i(x)w_i$ is a natural idempotent projection, its image is the supported one-dimensional interval, and its kernels form the complementary diagram. Vertexwise, the actual isomorphism to $\operatorname{span}_K\{w_i\}\times\ker p_i$ sends $x$ to $(p_i(x)w_i,x-p_i(x)w_i)$, with inverse given by addition. The total kernel dimension is strictly less than $\sum_i\dim_K V_i$.

**Proof.** Choose the earliest nonzero vertex $b$ and a nonzero $v\in V_b$. Let $j$ be the greatest index with $F_{bj}(v)\ne0$. On the support put $w_i=F_{bi}(v)$. Any zero image would force every later image to vanish, so every supported $w_i$ is nonzero. The scalar map $a\mapsto aw_j$ is injective. A linear left inverse gives a functional $\lambda_j$ with $\lambda_j(w_j)=1$. Set $p_i=\lambda_j\circ F_{ij}$ on the support and zero elsewhere. The composition laws prove the displayed equations. For an arrow entering the support from before $b$, its source space is zero. For an arrow leaving the support, maximality of $j$ kills the chosen vector. The splitting formulas follow from $p_i(w_i)=1$; rank-nullity removes one dimension at each supported vertex and none elsewhere.

**Theorem 2.2 (homogeneous interval basis of a finite diagram).** Every finite diagram over $K$ has a finite occurrence set $A$, indices $b_a\le j_a$, and vectors $w_{a,i}\in V_i$ that vanish outside $b_a\le i\le j_a$. At every vertex the supported vectors form a basis. For every actual arrow $F_{ik}$ with $i\le k$, the image of $w_{a,i}$ is $w_{a,k}$ if $b_a\le i$ and $k\le j_a$, and zero otherwise. The set $A$ is empty for a zero or empty diagram. Last-vertex survivors are allowed.

**Proof.** Induct strongly on the total vertex dimension. For a nonzero diagram, Theorem 2.1 gives a rank-one interval and its kernel diagram with smaller total dimension. Apply the induction hypothesis to that actual kernel diagram. At each vertex combine the singleton basis of the supported line with the kernel basis using the product splitting. The same occurrence set, enlarged by one, indexes these bases. The naturality equations in Theorem 2.1 and the kernel induction hypothesis give the arrow action for every occurrence. The resulting coordinate isomorphisms identify the diagram with the finite sum of these intervals, without assuming a preexisting barcode.

## 3. Classification and uniqueness

**Theorem 3.1 (finite-chain classification with arbitrary competing decompositions).** The real extension of every chain above is naturally isomorphic to a finite direct sum of positive-length intervals. The finite multiset of intervals is unique against all competing finite positive-length interval decompositions, even when their endpoints differ from the input breakpoints.

**Proof construction.** Strong induction on the sum of vertex dimensions uses Theorem 2.1 and its smaller kernel diagram. The empty and all-zero cases have no summands. The interval removed has birth $t_b$ and death $t_{j+1}$ if $j+1<n$, and infinite death otherwise. Actual composite ranks count intervals containing both sampled vertices. Integer finite differences recover each finite birth/death multiplicity; ranks at the last vertex recover essentials. A common refinement of all finite endpoints proves uniqueness for arbitrary competitors. Only the multiset is unique, not a chosen isomorphism.

## 4. Actual morphisms and ordered occurrence injections

**Theorem 4.1 (induced matching estimates).** Let $f:M\to N$ be an actual natural morphism between finite-constructible modules above, and $\eta\ge0$. Its factorization $M\twoheadrightarrow\operatorname{im}f\hookrightarrow N$ induces an occurrence-level partial matching. The monomorphism injection preserves deaths and orders births increasingly. The epimorphism injection preserves births and orders deaths decreasingly, with infinity first. They compose within the monomorphism and epimorphism classes respectively. If the cokernel is $\eta$-trivial, every target interval longer than $\eta$, including every essential, is matched and its birth differs from the intermediate birth by at most $\eta$. If the kernel is $\eta$-trivial, every source interval longer than $\eta$, including every essential, is matched and its death differs from the intermediate death by at most $\eta$.

Same-death counts for monos follow from actual birth-image/death-kernel intersections. Same-birth survival counts for epis follow from the surjection on $\operatorname{im}(V_b\to V_t)/\operatorname{im}(V_{b-}\to V_t)$. These are constraints on the same actual morphism, not assumed barcode functoriality or Hall bounds. Cokernel triviality gives

$$\operatorname{im}(N(t-\eta)\to N_t)\subseteq\operatorname{im}f_t\subseteq N_t.$$

The left diagram trims births by $\eta$ and removes lengths at most $\eta$. Kernel triviality gives $\ker f_t\subseteq\ker(M_t\to M(t+\eta))$, hence commuting epimorphisms from $M$ through $\operatorname{im}f$ to the shift-kernel quotient, which trims finite deaths by $\eta$. Ordered occurrence sandwiches give both estimates. The displayed structure map in the source's definition of $N^\eta$ must be the map of $N$, not $M$. No reflection into a left-continuous class is needed.

## 5. Exact stability and extended distances

**Theorem 5.1 (exact interleaving iff occurrence matching).** For every $\epsilon\ge0$, two real extensions above admit actual natural maps $M\to N(\epsilon)$ and $N\to M(\epsilon)$ whose shifted composites equal the actual $2\epsilon$ structure maps if and only if their finite interval multisets admit an occurrence-level partial matching with all the following properties:

- Matched finite births and finite deaths differ by at most $\epsilon$.
- Every essential is paired to an essential, with births differing by at most $\epsilon$.
- Every unmatched finite interval has length at most $2\epsilon$.

The interleaving equations make the kernel and cokernel of the first map $2\epsilon$-trivial. Apply Theorem 4.1 and undo the target shift. Conversely scalar interval maps are identity on valid shifted overlap and zero elsewhere. Their naturality and both composites are checked before taking the finite direct sum and conjugating by the constructed decompositions. A paired pair can use zero maps when both intervals are $2\epsilon$-trivial, not merely when one is short. The $2\epsilon$ structure map of $[b,d)$ vanishes exactly when $d-b\le2\epsilon$; this includes endpoint equality. In Lemma 8.1(ii) of the source, the parameter must follow the actual $2\delta$ shift, and the assembled maps have shifted targets.

**Corollary 5.2 (extended isometry).** The extended interleaving and bottleneck distances are equal, including infinity, because their feasible nonnegative $\epsilon$ sets are equal. This retains $\epsilon=0$, zero and empty diagrams, critical length $2\epsilon$, unequal essential counts and unrestricted tails. It is not merely an infimum-with-slack stability statement.

## 6. Formal supplier boundary

The project nilpotent Jordan-chain construction supplies ordinary ungraded Jordan chains over arbitrary fields. Its vectors need not be homogeneous in the vertex grading, so it does not supply this natural diagram splitting. Mathlib's scalar linear left inverses, complements, quotient/range equivalence and rank-nullity supply the ordinary linear algebra used inside the construction. Natural interval retraction and classification require compatible diagram constructions; arbitrary-endpoint uniqueness uses actual image recovery and common endpoint cuts. Actual-map matching estimates are a further obligation.

## 7. Actual image ranks and endpoint separation

For a finite occurrence family $A$ with real births $b_a$ and deaths $d_a\in\mathbb R\cup\{\infty\}$, $b_a<d_a$, define the interval-sum space at $r$ as the subspace of $K^A$ whose coordinates vanish outside $b_a\le r<d_a$. For $s\le t$, the actual arrow retains the coordinates with $t<d_a$ and kills the others. This is the finite sum of the scalar interval modules, including infinite-death intervals.

**Theorem 7.1 (arbitrary endpoint uniqueness from actual image ranks).** If two finite positive-length interval sums have the same actual arrow-image ranks for every $s\le t$, their multiplicities at every real birth and every finite or infinite death agree, without an assumed common endpoint set.

**Proof.** Surviving coordinates identify the actual image with $K^{\{a:b_a\le s,\ t<d_a\}}$: extend these coordinates by zero to produce a source vector and restrict the actual image vector for the inverse. Thus the actual image dimension is $\#\{a:b_a\le s,\ t<d_a\}$. This uses the same actual arrow, not a rank assigned independently of the map. For a proposed birth $b$, choose a source cut $s_-<b$ with no birth from either finite family in $(s_-,b)$. The difference of ranks at $(b,t)$ and $(s_-,t)$ counts precisely the intervals born at $b$ surviving $t$. For a finite death $d>b$, choose $b\le t_-<d$ with no death in $(t_-,d)$; subtract the two birth differences at $t_-$ and $d$. For death infinity choose $t\ge b$ past every finite death. These cuts are a common refinement of both finite endpoint sets. Positivity excludes deaths at or below birth, including zero-length intervals. The argument allows empty families and repeated occurrences. Naturally isomorphic interval sums have equal actual image ranks by the commuting arrow square and its component linear equivalences, so the theorem also gives uniqueness against arbitrary naturally isomorphic finite interval sums.

## 8. Neighboring universality question

Lesnick, *The Theory of the Interleaving Distance on Multidimensional Persistence Modules*, arXiv:1106.5305v4, Conjecture 5.7, asks: “For any field $k$ and $i\ge0$, $d_I$ is $i$-universal.” The definition concerns $n$-parameter persistence. For non-prime fields maximality among $i$-stable pseudometrics is asserted only on pairs in $\operatorname{im}(H_i S)$, the persistent homology realization image, not on all abstract modules. Conjecture 5.9 asks for geometric lifts of interleaved modules already in that image, with functions on one common CW complex at distance at most the interleaving parameter. Separate realizability does not supply such a common-space lift.

Theorem 5.5 proves universality over prime fields for $i\ge1$. Theorem 5.16 proves the pointwise finite-dimensional one-parameter arbitrary-field bottleneck-universality subcase. Neither settles the arbitrary-field multiparameter question. Botnan and Lesnick, *An Introduction to Multiparameter Persistence*, arXiv:2203.14289v2, revised March 13, 2023, Theorem 6.7 and Remark 6.8(4), identifies the arbitrary-field extension as open. Bauer, Brüstle and Scoccola, *An Algebraic Introduction to Persistence*, arXiv:2604.07022v2, revised June 10, 2026, Section 2.4, page 5, explicitly attests that universality for non-prime fields and in other settings remains open, referring to Lesnick Section 7. This is affirmative status evidence at that revision, not a certificate that no later resolution exists. The conjectures are research boundaries, not assumed suppliers or additional implementation targets. The finite one-parameter decomposition and exact stability/isometry endpoint in this note is solved mathematics.
