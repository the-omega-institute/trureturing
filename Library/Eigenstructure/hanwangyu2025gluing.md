---
bibkey: hanwangyu2025gluing
authors: X. B. Han; S. Wang; C. Yu
year: 2025
title: "PageRank of Gluing Networks and Corresponding Markov Chains"
doi: 10.3390/math13132080
url: https://www.mdpi.com/2227-7390/13/13/2080
claim: "Glue Markov chains M_i = (S_i, A_i) to a Markov chain M = (S, A), then all the eigenvalues of A lie in the convex hull of the eigenvalues of all A_i on the complex plane."
strata_touched:
  - D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.3390/math13132080

Source: https://www.mdpi.com/2227-7390/13/13/2080

Publisher PDF: https://mdpi-res.com/d_attachment/mathematics/mathematics-13-02080/article_deploy/mathematics-13-02080.pdf

## Source statements

Definition 8, p. 10:

> For integers i = 1, 2, ⋯, k, let M_i = (S_i, A_i) be k Markov chains, and v_0^i be a fixed point in S_i. Assume θ = (θ_1, θ_2, ⋯, θ_k), 0 < θ_i < 1, and Σ_{i=1}^k θ_i = 1.

> The θ-gluing of M_i along v_0^i is the following Markov chain M = (S, A).

The state set is the disjoint union of the state sets with their selected roots identified. The transition rule is

$$
a_{vw}=\begin{cases}
a^i_{vw}&v\in S_i,\ w\in S_i\setminus\{v_0\},\\
\theta_i a^i_{vw}&v\in S_i\setminus\{v_0\},\ w=v_0,\\
\sum_i\theta_i a^i_{v_0v_0}&v=w=v_0,\\
0&\text{otherwise}.
\end{cases}
$$

Conjecture 1, §4.3, p. 17:

> Glue Markov chains M_i = (S_i, A_i) to a Markov chain M = (S, A), then all the eigenvalues of A lie in the convex hull of the eigenvalues of all A_i on the complex plane.

Indices in the formal statement run through `Fin k`. Each input chain has state set `Fin (n + 1)` with selected root 0; matrix entry `(v,w)` gives the probability from `w` to `v`. The glued state set is `Option (Σ i, Fin (M i).n)`, where `none` is the common root and `some ⟨i,v⟩` is state `v.succ` of chain `i`. Eigenvalues are `spectrum ℂ` of the entrywise complexification, and the convex hull is over ℝ in ℂ.

## Counterexample

Two identical copies of

$$
B=\frac1{54}\begin{pmatrix}43&9&2\\2&36&16\\9&9&36\end{pmatrix}
$$

with equal weights have a glued eigenvalue $4/9$. The input characteristic polynomial is $(\lambda-1)(\lambda-17/27)(\lambda-1/2)$, so every input eigenvalue has real part at least $1/2$. The vector $(0,-4,3,4,-3)$ is a nonzero glued eigenvector for $4/9$. Its root coordinate is zero and the two private blocks cancel in the root row. These facts yield the repository-derived refutation `result : ¬ claim`.

## Literature boundary

The preregistration at https://github.com/the-omega-institute/trureturing/issues/19143 records the source and the literature screen. Completeness is ASSUMED-UNVERIFIED: Rymkhanova et al. (2026), Schwenk (1974), Laffey–Šmigoc and Belardo–Li Marzi–Simić (2010) were not accessed. General families, similarity decompositions and reversibility conditions are not proved by this module.
