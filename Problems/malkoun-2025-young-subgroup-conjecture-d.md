---
slug: malkoun-2025-young-subgroup-conjecture-d
bibkey: malkoun2025finitegraphs
doi: 10.1016/j.geomphys.2026.105993
url: https://arxiv.org/abs/2508.13472v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result
---

# Malkoun's Conjecture D fails for Young subgroups

## Problem

Joseph Malkoun, *Finite graphs and configurations of points* (2025 preprint; arXiv:2508.13472v3; Journal of Geometry and Physics, DOI 10.1016/j.geomphys.2026.105993), Section "A conjecture in matrix analysis", defines the setting as follows (TeX line 405):

> Given an equivalence relation, say $\sim$, on $[n]$, we let $P_\sim$ be the group of all permutations of $[n]$ which preserve the equivalence classes of $[n]$ under $\sim$. Let $\sim_i$, for $i = 1, 2$, be two equivalence relations on $[n] = \{1, \dots, n\}$, with associated permutation groups $P_1$, $P_2$, respectively (we write $P_i$ rather than $P_{\sim_i}$ to alleviate the notation).

At TeX lines 407–408:

> Let $H$ be a Hermitian positive semidefinite $n \times n$ matrix. We define
> $f_{\sim_1, \sim_2}(H) = \sum_{\sigma_1 \in P_1} \sum_{\sigma_2 \in P_2} \prod_{i = 1}^n H_{\sigma_1(i), \sigma_2(i)}.$

Conjecture D (TeX lines 410–412) reads, with the source's macro `\Real` expanded as $\operatorname{Re}$:

> Under the above hypotheses, we have
> $\operatorname{Re}( f_{\sim_1, \sim_2}(H) ) \geq |P_1 \cap P_2| \, \prod_{i = 1}^n H_{i i}.$

These quotations were checked in `finite_graphs_and_configurations_of_points_v5.tex` from the [v3 source archive](https://arxiv.org/src/2508.13472v3), md5 `3c520a352e066a90cdcffb75a2ee568c`. See also [the literature note](../Library/QuadraticForms/malkoun2025finitegraphs.md).

Issue [#22163](https://github.com/the-omega-institute/trureturing/issues/22163) fixes the reading: for every natural number $n$, every pair of equivalence relations $r_1,r_2$ on $\mathrm{Fin}\,n$, and every complex Hermitian positive semidefinite matrix $H$, the proposed inequality holds, with $P_j=\{\sigma:\forall i,\ r_j(\sigma(i),i)\}$. The real-valued formulation uses $\prod_i\operatorname{Re}H_{ii}$. The universal assertion is refuted.

## Motivation

The source connects this matrix inequality to graph amplitudes generalizing the Atiyah problem on configurations of points. Its theorem at TeX line 416 states:

> Conjecture D implies Conjecture C.

Thus Conjecture D was a proposed sufficient matrix inequality for the tree-amplitude conjecture. It also extends a permanent inequality: the source remarks at TeX line 414,

> We remark that by taking one of the equivalence relation to be the discrete one and the other one to be the indiscrete one, one recovers Marcus's permanent analogue of the Hadamard inequality (\cite{Mar1963}).

The settlement tests the proposed extension to two arbitrary class-preserving permutation groups.

## Gap

Issue #22163 records the bounded literature check before any Lean:

- the v3 source states Conjecture D without restrictions beyond the two equivalence relations and Hermitian positive semidefiniteness;
- the orchestrator reports that MathOverflow question 480580, Malkoun's "A conjectured generalization of Marcus's inequality", has no answer or refuting comment;
- the orchestrator reports no citing works in OpenAlex for the arXiv record, no citations reported by Crossref for the journal DOI, and no settlement in the stated web searches;
- the repository's existing arbitrary-subgroup refutation does not settle the restriction to the full class-preserving groups of equivalence relations;
- the search seat reports no published proof or counterexample.

`not-found-in-searched-scope`. The source quotations were reproduced; the other external search readings remain attributed to the issue.

## Route

Let $V$ have columns $(1,0)$, $(1,1)$ and $(1,i)$, and put $A=V^*V$. Thus $A=\begin{pmatrix}1&1&1\\1&2&1+i\\1&1-i&2\end{pmatrix}$. The module's `v` is this $2\times3$ matrix and `gram v` is $V^*V$.

For each $m\in\mathbb N$, identify $\mathrm{Fin}(3m)$ with pairs $(j,s)\in\mathrm{Fin}\,m\times\mathrm{Fin}\,3$ by $(j,s)\mapsto3j+s$. Let $H_m$ be the block diagonal matrix of $m$ copies of $A$. Within each block, the first relation has classes $\{0,1\},\{2\}$ and the second has classes $\{0\},\{1,2\}$; different blocks are never equivalent. These are `blockRelation m (seedRelation 2)` and `blockRelation m (seedRelation 0)`.

1. **Matrix hypotheses.** For every $m\in\mathbb N$, `block_posSemidef` states that this specified $H_m$ is positive semidefinite. Its Hermitian property supplies the other hypothesis of `claim`.
2. **Full subgroup factorization.** For every $m\in\mathbb N$ and every equivalence relation $r$ on $\mathrm{Fin}\,3$, `blockEquiv` identifies the full class-preserving group of `blockRelation m r` with the families of class-preserving seed permutations indexed by $\mathrm{Fin}\,m$. For every such $m$, every pair of equivalence relations $r,s$ on $\mathrm{Fin}\,3$, and every complex $3\times3$ matrix $a$, `block_factorization` states that the cross sum of `blockMatrix m a` for their block relations is the $m$th power of the seed cross sum; this identity requires no positivity hypothesis on $a$.
3. **Seed evaluation.** For the specified $V$ and the two specified seed relations, `seed_crossSum` gives $f(A)=9-i$ by enumerating each seed group as the identity and its single transposition.
4. **Intersection and diagonal.** For every $m\in\mathbb N$, `block_intersection` states that the intersection of these two specified block groups is the identity subgroup. For every $m\in\mathbb N$, `block_diagonal` gives $\prod_i\operatorname{Re}(H_m)_{ii}=4^m$ for the specified Gram matrix.
5. **Contradiction.** `power_value` gives $(9-i)^{15}=-20078071648128-224842906547072\,i$. Applying `claim` at $n=45$, with these two relations and $H_{15}$, would therefore give $1073741824\le-20078071648128$. The theorem `result : ¬ claim` derives the contradiction.

## Falsifier

The refutation would miss the source conjecture if it used smaller subgroups, a different normalization, or matrices outside the stated hypotheses.

- `classPreserving r` contains every permutation $\sigma$ with $r(\sigma(i),i)$ for all $i$. For a finite equivalence class, an injective self-map is onto, so this is precisely the source's class-preserving group, with the source's label $i+1$ corresponding to $i\in\mathrm{Fin}\,n$.
- `crossSum` is the full, unnormalized double sum over both subgroups of $\prod_iH_{\sigma(i),\tau(i)}$.
- For every natural $n$ and every Hermitian complex matrix $H$ on $\mathrm{Fin}\,n$, the reused `diagonal_product_eq_real` identifies $\prod_iH_{ii}$ with the complex embedding of $\prod_i\operatorname{Re}H_{ii}$. Thus the real-valued diagonal product does not change the conjecture.
- The intersection cardinality is that of the actual subgroup intersection, and the explicit witness has both Hermitian and positive-semidefinite certificates.

No smallest-dimension claim is made.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.lean` (285 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.lean.json`, statement `sha256:e186971c1d405f19926d11dc5fe8357fcf420cebe118cd262f7c65b2c9eb73a5`.

Declaration statements:

- `result`: `sha256:fa361fd75aac54a16e4cb161eaf92be028e132013897059d6c3bf6bb8fa3a39d`;
- `claim`: `sha256:74af6d59a0f453a735ddc90e2426a6ee3b02e8818b93e16ab40efd16e1cbd92f`.

## Triage

Tier 1 conjecture of a 2025 preprint retained in the arXiv v3 associated with the journal article, preregistered in issue #22163 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every natural number $n$, every pair of equivalence relations on $\mathrm{Fin}\,n$, and every complex Hermitian positive semidefinite matrix $H$, the real cross sum is at least the intersection cardinality times $\prod_i\operatorname{Re}H_{ii}$.

**Computed, not formalized** (independent exact arithmetic; the enumeration for $m=1,2,3$ and the power at $m=15$ are also recorded by the orchestrator in issue #22163):

- For $m=1,2,3$ in the specified block family, direct enumeration agrees with the power factorization and gives subgroup intersection cardinality one.
- For the tested block family with $1\le m\le15$, no violation was observed for $m\le14$, and a violation was observed at $m=15$.

**Argued, not formalized.**

- *Mechanism.* For the two specified seed relations and the specified Gram matrix, `seed_crossSum` gives $9-i$, and `block_factorization` at $m=15$ together with `power_value` gives a negative real cross sum. Writing $9-i=\rho e^{-i\theta}$ with $\theta=\arctan(1/9)$ explains the obstruction: $\operatorname{Re}((9-i)^m)=\rho^m\cos(m\theta)$, so the phase accumulates under independent block multiplication. A lower bound on each real part alone cannot be multiplied into a lower bound on the real part of the product. The source already describes the analogous phase mechanism for disconnected graph amplitudes at TeX lines 740–741; the present witness realizes it for the matrix conjecture.
- *Surviving source case.* Malkoun (2025, arXiv:2508.13472v3), TeX line 473, states: "If $H$ is Hermitian positive semidefinite and one of the two equivalence relations $\sim_i$ ($i = 1, 2$) is finer than the other, then Conjecture D holds." For $P_1\subseteq P_2$, reindexing by $\tau\sigma^{-1}$ gives $f(H)=|P_1|\prod_B\operatorname{per}(H[B])$, where $B$ ranges over the classes of the second relation. Each principal block is positive semidefinite, so Marcus's permanent inequality gives $f(H)\geq|P_1|\prod_iH_{ii}$, and $|P_1|=|P_1\cap P_2|$. If $P_2\subseteq P_1$, exchanging the two groups conjugates the sum for Hermitian $H$ and leaves its real part unchanged. Thus nested relations supply a sufficient extra structure; these two witness relations are not nested.
- *Positive definiteness does not repair the conjecture.* Fix the witness groups and put $H(\varepsilon)=H_{15}+\varepsilon I$. For every $\varepsilon>0$ this matrix is positive definite, since $x^*H(\varepsilon)x=x^*H_{15}x+\varepsilon\|x\|^2>0$ for $x\ne0$. The difference between the two sides of the conjectured bound is continuous in $\varepsilon$, being a finite sum of finite products, and is strictly negative at zero. It remains negative for all sufficiently small positive $\varepsilon$, so the same groups also admit positive-definite counterexamples.
- *Effect on the paper.* The source's conditional statement "Conjecture D implies Conjecture C" is not refuted, but its false universal premise cannot establish C. The source's tree construction at TeX lines 458–469 uses Gram vectors in $\mathbb C^2$. Each witness block has rank two, since the first two columns of $V$ are independent, and fifteen independent blocks have rank 30; this matrix therefore cannot be that two-dimensional Gram matrix. Consequently this witness does not refute C or the geometric conjectures A and B, and does not contradict the source's separately proved special cases. Whether Conjecture D survives a rank-at-most-two restriction or a restriction to real positive semidefinite matrices remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check in issue #22163 does not establish exhaustive worldwide novelty or priority. Its MathOverflow reading, OpenAlex and Crossref citation counts, web-search results, and search-seat report were not independently reproduced. The journal text and Marcus's original 1963 article were not read; the nested-case argument uses the permanent inequality as cited in Malkoun's v3 source.

The finite computations and the arguments in the two corresponding groups above are not formalized as additional Lean conclusions. The preregistration's random search in dimensions at most six was not reproduced. No computation establishes minimal dimension, classifies other block seeds, or settles the rank-at-most-two or real-matrix restrictions. No formal bridge from this witness to the source's geometric configuration space is claimed.
