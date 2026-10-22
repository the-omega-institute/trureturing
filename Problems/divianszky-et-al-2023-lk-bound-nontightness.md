---
slug: divianszky-et-al-2023-lk-bound-nontightness
bibkey: divianszkymartonbenevertesi2023certification
doi: 10.1038/s41598-023-39529-0
url: https://arxiv.org/abs/2211.17185v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Optimization/PrepareMeasureLkBound.result
---

# The bound L_k(M) ≤ k L(M) is not tight for k ≥ 3

## Problem

P. Diviánszky, I. Márton, E. Bene and T. Vértesi, *Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant*, arXiv:2211.17185v2 (Sci. Rep. 13, 13200, 2023), Methods, after Lemma III.4:

> It is an open question whether Lemma~\ref{LkkL} is tight or not.

> Hence, for $k=2$ the upper bound in Lemma~\ref{LkkL} is tight. We conjecture that the bound is not tight for greater values of $k$.

Here, for a real $n\times m$ matrix $M$:
- $L(M)=\max_{v\in\{\pm1\}^n}\|vM\|_1$, the classical bound of the correlation expression $M$;
- $L_k(M)=\max_W\sum_i\|(W^{\mathsf T}M)_i\|_1$ over the $n\times k$ matrices $W$ whose rows are standard basis vectors, which groups the inputs into $k$ classes;
- Lemma III.4 states $L_k(M)\le kL(M)$.

The definitions are quoted in [the literature note](../Library/QuantumContext/divianszkymartonbenevertesi2023certification.md).

Issue [#20049](https://github.com/the-omega-institute/trureturing/issues/20049) fixes the reading: for every $k\ge3$ there is $c_k<k$ with $L_k(M)\le c_kL(M)$ for all matrices. This is proved.

## Motivation

The source certifies qubits in prepare-and-measure experiments by comparing quantum values with $L_k(M)$, the best value achievable with $k$-valued classical messages, and relates the resulting constants to the Grothendieck constant of order 3. Lemma III.4 controls how much a larger classical alphabet can gain over binary messages; its tightness decides whether the factor $k$ in the certification thresholds can be improved.

## Gap

The literature check before any Lean is recorded in #20049:
- the v2 TeX keeps the question and the conjecture;
- the search seat read the ten citing works listed by Semantic Scholar and found no settlement or improved constant;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Put $a_k=2^{-k}\sum_{\varepsilon\in\{\pm1\}^k}|\sum_i\varepsilon_i|$.
1. **The averaged norm.** $g(x)=2^{-k}\sum_\varepsilon|\sum_i\varepsilon_ix_i|$ is convex and invariant under sign changes and permutations, so $g(x)\ge(a_k/k)\sum_i|x_i|$.
2. **Comparison.** For $B=W^{\mathsf T}M$ and each $\varepsilon$, the row $\varepsilon^{\mathsf T}W^{\mathsf T}$ is a sign vector, so $\|\varepsilon^{\mathsf T}B\|_1\le L(M)$. Averaging over $\varepsilon$ gives $L(M)\ge(a_k/k)\sum_i\|B_i\|_1$, hence $L_k(M)\le(k/a_k)L(M)$.
3. **The constant.** $a_3=3/2$ and $a_k$ is nondecreasing, so $k/a_k\le2k/3<k$ for $k\ge3$.

## Falsifier

The proof would not answer the conjecture if the module's quantities differed from the source's. The module:
- defines $W_{n,k}$, the Manhattan norm, $L_k$ and $L$ exactly as the source's Methods section;
- proves a uniform constant below $k$, which excludes both a matrix attaining $L_k=kL$ and a sequence approaching ratio $k$.

## Evidence

The canonical source is `D5/S3/Quantum/Optimization/PrepareMeasureLkBound.lean` (295 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Optimization/PrepareMeasureLkBound.lean.json`, statement `sha256:35869074c43c870335cbd81aa1464350253c4c8cc362cc35c8c2fa500f09b773`.

Declaration statements:
- `result`: `sha256:7d6d5b60f9968f28ae22a6b1a4dca7efc9ff69c08dcf001518b41265a47026ef`;
- `claim`: `sha256:73c662c788f9fad8b43af8ba4ea5a77bd496b6953d39b433c1dd1175737899e8`.

## Triage

Tier 1 conjecture of a 2022 preprint kept in the 2023 journal version, preregistered in issue #20049 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $k\ge3$, $L_k(M)\le c_kL(M)$ with a constant $c_k<k$, for all real matrices.

**Computed, not formalized** (orchestrator, brute force, recorded in #20049):
- *The constant.* For $k=2,3,4$ and 900 random matrices, $L_k/L$ never exceeds $k/a_k$ ($2$, $2$, $8/3$).
- *Sharpness.* The $k\times2^k$ matrix whose columns are all sign vectors attains $L_k/L=k/a_k$ for $k=3,4$.
- *The source's family is extremal.* The source evaluates $L_k(M^{(k)})/L(M^{(k)})=2^{k-1}/\binom{k-1}{\lfloor(k-1)/2\rfloor}$ for its family $M^{(k)}$. Exact rational arithmetic gives $k/a_k=2^{k-1}/\binom{k-1}{\lfloor(k-1)/2\rfloor}$ for $k=2,\dots,13$, so on that range the proved constant is attained by the source's own matrices and is optimal.

**Argued, not formalized.**
- *Mechanism.* Grouping the inputs into $k$ classes and taking the $\ell_1$ norm of each class sum can beat a single sign assignment by at most the ratio of the $\ell_1$ norm to the average random-sign norm, which is $k/a_k$ rather than $k$. For $k=2$, $a_2=1$ and the bound is $2=k$, matching the CHSH case.
- *Growth.* $a_k=\mathbb E|\varepsilon_1+\dots+\varepsilon_k|\sim\sqrt{2k/\pi}$, so the optimal constant grows like $\sqrt{\pi k/2}$ instead of $k$.
- *The identity behind extremality.* $a_k=k\binom{k-1}{\lfloor(k-1)/2\rfloor}/2^{k-1}$ is the classical formula for the mean absolute value of a simple random walk; it turns the computed equality into an identity for every $k$.
- *Effect on the paper.* The factor $k$ in Lemma III.4 can be replaced by $k/a_k$, which improves every threshold that uses the lemma.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the citing works were read by the search seat. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; sharpness for $k\ge5$ was not computed.
