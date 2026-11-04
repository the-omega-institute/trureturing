---
slug: yu-et-al-2021-absolutely-entangled-all-partitions
bibkey: yuetal2021absolutelyentangled
doi: 10.1103/PhysRevA.104.032414
url: https://arxiv.org/abs/2106.16216v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.result
---

# A finite set supplies one state entangled for all fixed tensor partitions in every frame

## Problem

B. Yu, P. Jayachandran, A. Burchardt, Y. Cai, N. Brunner and V. Scarani, *Absolutely entangled sets of pure states for bipartitions and multipartitions*, Physical Review A 104, 032414 (2021), DOI 10.1103/PhysRevA.104.032414; arXiv:2106.16216v3, Section III, immediately after the Corollary (`main.tex`, line 509):

> This result guarantees that, given any $U$ and any partition $P$, there exists at least one entangled state. An interesting open question is whether one can find an AES, such that, for every $U$, there exists a state that is entangled according to all partitions. This would arguably be the strongest form of genuine multipartite entanglement.

The quotation is from the v3 source member `main.tex`, md5 `e11d4dc540598e9ef271fc11bad389a0`. Definition 3 is at lines 310–317, and the preceding Corollary at lines 499–508. The definitions and source locator are also in [the literature note](../Library/Entropy/yuetal2021absolutelyentangled.md).

Issue [#22238](https://github.com/the-omega-institute/trureturing/issues/22238) fixes the reading. A partition $p=(d_1,\ldots,d_k)$ is an ordered factorization with $k\ge2$, every $d_i\ge2$, and $\prod_i d_i=d$. Its tensor coordinates are fixed by `partitionEquiv`, the mixed-radix identification of local index tuples with the standard basis of $\mathbb C^d$. The matrix `productState p τ` has entries equal to the products of the corresponding local entries. `Separable p ρ` means membership in the real convex hull of such products with every local matrix positive semidefinite and of trace one.

The formal assertion is: for every $d,a,b\in\mathbb N$ with $a,b\ge2$ and $d=ab$, there is a finite set $S$ of positive semidefinite $d\times d$ complex matrices of trace one such that

$\forall U\in SU(d),\ \exists\rho\in S,\ \forall p\in\mathrm{Partition}(d),\ \neg\mathrm{Separable}(p,U\rho U^\dagger).$

The member may depend on $U$ and must serve every partition simultaneously. This fixed-coordinate assertion is proved. Purity is used in the construction; it is not an additional predicate in the type of `claim`.

## Motivation

The source's Definition 3(ii) has the quantifier order $\forall p\,\forall U\,\exists\rho\in S$: different partitions may require different members. The question asks for $\forall U\,\exists\rho\in S\,\forall p$. A positive answer therefore supplies a common witness of nonseparability across all the specified factorizations in each frame, rather than merely a witness for each partition separately.

## Gap

The bounded literature check is recorded in #22238:

- The orchestrator read the v3 source and verified that it states the question.
- The orchestrator reported one Crossref citing record, no Semantic Scholar citing records, and a web search covering the question, absolutely entangled sets, all partitions and the six authors; no settlement was found. The reported results included the source, its predecessor arXiv:2006.07165, SwissMAP publication pages and an abstract by Patra, Taoutioui and Vértesi.
- The search seat reported reading Patra, Taoutioui and Vértesi, arXiv:2609.13075v1, without finding an answer, and no match in formal-conjectures. It reported HTTP 403 from MathDB and HTTP 429 from OpenAlex.
- The preregistration records no existing repository issue, module, literature note or dossier for arXiv:2106.16216.

`not-found-in-searched-scope`. The source quotation was independently checked; the other reported search readings were not reproduced.

## Route

Write $C_d$ for the embeddings $c:\{0,1\}\times\{0,1\}\hookrightarrow\{0,\ldots,d-1\}$, and put $m=2|C_d|$. For any such embedding define $q_c(w)=w_{c(0,0)}w_{c(1,1)}-w_{c(0,1)}w_{c(1,0)}$.

1. **A corner for each partition.** For every $p:\mathrm{Partition}(d)$, including its requirements of at least two factors of dimension at least two and product $d$, `corner_injective` proves that varying the first two local indices over zero and one, with all other indices zero, gives an embedding in $C_d$.
2. **A polynomial for each frame.** For every complex $d\times d$ matrix $U$ and embedding $c\in C_d$, `minorPolynomial_eval` identifies the evaluation of `minorPolynomial U c` at $v$ with $q_c(Uv)$, and `minorPolynomial_degree` bounds its total degree by two. Under the additional hypothesis $U\in SU(d)$, `minorPolynomial_nonzero` proves it is nonzero: evaluation at $U^\dagger(e_{c(0,0)}+e_{c(1,1)})$ gives one. `framePolynomial_nonzero` proves that the product over $C_d$ is nonzero for $U\in SU(d)$; `framePolynomial_degree` bounds its total degree by $m$ for every complex $U$.
3. **One grid works for every frame.** For any $d,m\in\mathbb N$ and any nonzero complex multivariate polynomial on $d$ variables of total degree at most $m$, `grid_eval_nonzero` gives a nonzero evaluation on $\{0,1,\ldots,m\}^d$, using Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`. For $d\ge4$ and $U\in SU(d)$, `common_grid` therefore supplies a nonzero vector $v$ from this fixed grid with $q_c(Uv)\ne0$ for every $c\in C_d$. The condition $d\ge4$ supplies an embedding, so `minors_force_nonzero` excludes $v=0$ when all those minors are nonzero.
4. **Normalize the finite set.** For every nonzero $v\in\mathbb C^d$, `pure_density` proves that `pure v`, defined as $vv^\dagger/E(v)$ with $E(v)=\sum_i|v_i|^2$, is positive semidefinite and has trace one. For every complex matrix $U$ and every vector $v$, without invertibility or nonzero assumptions, `pure_transform` gives $U\,\mathrm{pure}(v)\,U^\dagger=E(v)^{-1}(Uv)(Uv)^\dagger$.
5. **Separate a rank-one matrix from the convex hull.** For every $p:\mathrm{Partition}(d)$, every vector $w$ and every real $t$, `separable_pure_minor` proves that separability of $tww^\dagger$ implies $q_{\mathrm{corner}(p)}(w)=0$; it also covers $w=0$. Its product-state ingredients are `productState_density`, requiring every local matrix to be positive semidefinite and of trace one, and `productState_column_minor`, which gives a zero corner minor for every column of a product of arbitrary local matrices.
6. **Conclude.** The hypotheses $a,b\ge2$ and $d=ab$ in `result` give $d\ge4$. Take the image of the nonzero grid under `pure`. Given $U\in SU(d)$, use `common_grid`; if its selected normalized state were separable for any $p:\mathrm{Partition}(d)$, `pure_transform` and `separable_pure_minor` would force the corresponding nonzero corner minor to vanish.

## Falsifier

A finite sample of frames would not settle the universal quantifier over $SU(d)$, and a separately chosen state for each partition would not settle the common-witness quantifier. The module uses a grid fixed before $U$ and proves simultaneous nonvanishing by the product polynomial.

The tensor identifications are part of the assertion. Allowing every possible tensor identification, chosen independently for each candidate state, changes the question. Likewise, `Separable` is the full convex hull of local density products; `result` does not state a separate predicate for genuine multipartite entanglement or biseparability. The conclusion is exactly nonmembership in that convex hull for every encoded ordered factorization.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.lean` (385 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.lean.json`, statement `sha256:dc719aad48926693e8f2f08104b723a2e62cf9b3a4fe5f085081ba49f6f6944b`.

Declaration statements:

- `result`: `sha256:87864b7e1670b48bab61f20d06700b89d6b4c6aa29da79907e0144dcdff10e97`;
- `claim`: `sha256:5ec2cc250ee3073c83db45d03e64f607a76da152ef2f0e895a016999b359db69`.

## Triage

Tier 1 open question of a 2021 journal article, preregistered in issue #22238 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $d,a,b\in\mathbb N$ with $a,b\ge2$ and $d=ab$, there is a finite set $S$ of positive semidefinite complex $d\times d$ matrices of trace one such that, for every $U\in SU(d)$, some $\rho\in S$ has $U\rho U^\dagger$ nonseparable for every ordered factorization with at least two factors, all of dimension at least two and product $d$, using the specified mixed-radix coordinates and real convex hull of local density products.

**Computed, not formalized** (direct enumeration): in dimension $d=4$, the construction's grid contains $5\,764\,800$ nonzero vectors before identifying vectors that define the same normalized state.

**Argued, not formalized.**

- *Decisive mechanism.* For $d\ge4$ and $U\in SU(d)$, `common_grid` gives one nonzero grid vector whose transformed minors are all nonzero. For any $p:\mathrm{Partition}(d)$, vector $w$ and real $t$, `separable_pure_minor` says that separability of $tww^\dagger$ forces the selected corner minor to vanish. These two statements explain why one vector serves all partitions: the product imposes all the minor constraints together, and each partition supplies one of the excluded embeddings.
- *Why positivity matters.* For a finite family of positive semidefinite matrices $A_i$ with nonnegative real weights $\lambda_i$, an equality $\sum_i\lambda_i A_i=tww^\dagger$ implies, for every $x$ orthogonal to $w$, that $\sum_i\lambda_i x^\dagger A_i x=0$. Every term is nonnegative, so any summand of positive weight annihilates $x$; this is `summand_kernel`, with arbitrary real $t$. For nonzero $w$ and a Hermitian matrix annihilating every vector orthogonal to $w$, `supported_column` makes every column a multiple of $w$. In a separable convex decomposition, the weights sum to one, so some weight is positive; its trace-one product matrix has a nonzero diagonal entry and hence a nonzero column. `productState_column_minor`, for arbitrary local matrices and any column, gives that column a zero minor. The column is $zw$ with $z\ne0$, so its minor is $z^2q_{\mathrm{corner}(p)}(w)$, forcing the latter to vanish. The case $w=0$ has zero minor directly.
- *All unitary frames.* In the same composite dimensions, any unitary $W$ can be multiplied by a scalar $\zeta$ with $|\zeta|=1$ and $\zeta^d=(\det W)^{-1}$. Then $\zeta W\in SU(d)$ and $(\zeta W)\rho(\zeta W)^\dagger=W\rho W^\dagger$. Thus the established special-unitary statement also gives the all-unitary version by this argument; that extension is not the type of `result`.
- *The coordinate boundary.* If every tensor identification is allowed, a density matrix's orthonormal eigenbasis can be identified with a product basis for any fixed factorization $d=ab$, $a,b\ge2$. Its nonnegative eigenvalues sum to one, making it a convex combination of product-basis projectors in that identification. Thus no density matrix is entangled for every such identification. Fixing the identifications is an essential part of the reading.
- *Size and neighbouring questions.* The type of `claim` supplies no optimal cardinality, and counting the raw grid does not establish the number of distinct normalized states or a minimum. Minimal size, a quantitative noise margin, and a formal relation to stronger multipartite-entanglement predicates remain open here.
- *Effect on the paper.* The Corollary at `main.tex`, lines 499–508, supplies the weaker $\forall p\,\forall U\,\exists\rho$ statement; the settlement adds a common witness under the fixed-coordinate reading. The source places the question after that Corollary; the following Conclusion section does not use its answer as a premise of another result. Its separate questions about minimal AES and minimal mixed-state AES in Section IV, lines 528–530, are not settled by this existence result.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The Crossref and Semantic Scholar counts, the web search, the search seat's reading of arXiv:2609.13075v1, the formal-conjectures search and the MathDB/OpenAlex access failures are the reports attributed in #22238; they were not independently reproduced. The journal text was not compared line by line with arXiv v3.

The computation and the arguments under their respective labels are not additional formalized conclusions of `result`. Purity is visible in the normalized rank-one construction but is not quantified in `claim`. The all-unitary extension, the assertion about unrestricted tensor identifications, cardinality optimization, noise robustness and any identification with genuine multipartite entanglement are outside the formal statement. The result settles the fixed mixed-radix reading registered in #22238; it does not certify a broader interpretation of the source's word “partitions”.
