---
slug: guha-et-al-2016-multilayer-determinant-root-nonuniqueness
bibkey: guha2016multilayerpercolation
doi: 10.1103/PhysRevE.93.062310
url: https://arxiv.org/abs/1402.7057v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.result
---

# The multilayer percolation determinant can have three zeros in [0, 1]

## Problem

S. Guha, D. Towsley, P. Nain, Ç. Çapar, A. Swami and P. Basu, *Spanning connectivity in a multilayer network and its relationship to site-bond percolation*, arXiv:1402.7057v4 (Phys. Rev. E 93, 062310):

> Numerically, it is easy to verify that $\det (\bA (q))$ has a unique zero in $[0,1]$ for all $M \ge 1$ as long as $C > 1$. We conjecture that this is always true.

Here A(q) is the source's M × M matrix:
- A_ij = δ_ij − C (binom(M, j) − binom(M − i, j)) q^j (1 − q)^{M−j} for i, j ∈ {1, …, M};
- C = Σ_k (k − 1) k p_k / z for a degree distribution p with mean degree z.

The definitions are quoted in [the literature note](../Library/StatisticalMechanics/guha2016multilayerpercolation.md).

Issue [#19823](https://github.com/the-omega-institute/trureturing/issues/19823) fixes the reading: for every M ≥ 1 and every finitely supported degree distribution with C > 1, det A(q) would have exactly one zero in [0, 1]. The conjecture is refuted.

## Motivation

In the source, q_c(M) is the site-occupation threshold above which M independently site-percolated copies of a configuration-model graph have a giant spanning cluster. The source proves that q_c(M) is the smallest zero of det A(q) in [0, 1]. A unique zero would make q_c(M) the only root of a single polynomial equation, which is how the source computes it.

## Gap

The literature check before any Lean is recorded in #19823:
- the arXiv versions v1–v4;
- the seven OpenAlex citing works, read by the search seat, none of which treats the finite-M uniqueness;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **The matrix.** Take M = 3 and the point-mass degree distribution p = δ₆₅, so z = 65 and C = 64. With u = q(1 − q)², v = q²(1 − q) and w = q³, A(q) has rows:
   - (1 − 64u, −128v, −64w);
   - (−128u, 1 − 192v, −64w);
   - (−192u, −192v, 1 − 64w).
2. **Exact values.** det A(0) = 1, det A(1/4) = −36, det A(1/2) = 281 and det A(1) = −63.
3. **Three zeros.** det A(q) is a polynomial in q. By the intermediate value theorem it has a zero in each of (0, 1/4), (1/4, 1/2) and (1/2, 1).

## Falsifier

The counterexample would not answer the conjecture if the module's matrix or its C differed from the source's. The module:
- uses the source's entries with i, j ∈ {1, …, M} and binomials that vanish when the lower index exceeds the upper one;
- defines C from a finitely supported degree distribution exactly as in the source;
- quantifies over all M ≥ 1 and all such distributions with C > 1.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.lean` (137 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness.lean.json`, statement `sha256:1ef834f2de8b83b395216f7b71d168e8d365fcad1366a722031c25ca76d8fecd`.

Declaration statements:
- `result`: `sha256:74479876c718aeea21842851fbfbd76bdfa7207cd5b7ba1911c1b1b672cb433c`;
- `claim`: `sha256:3bb8bd750c4bef38794ccf35408fa198b79405e316bc949844bbbaf9d5af75d9`.

## Triage

Tier 1 conjecture of a 2016 paper, preregistered in issue #19823 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for M = 3 and p = δ₆₅ (C = 64), det A(q) has at least three distinct zeros in [0, 1], so the conjecture fails.

**Computed, not formalized** (orchestrator, sympy, recorded in #19823):
- **The three zeros.** For M = 3 and C = 64, the zeros in [0, 1] are 0.015178, 0.343759 and 0.909396.
- **Scan.** For M = 1, …, 6 and C ∈ {2, 4, 8, 10, 12, 16, 20, 32, 64, 128}, det A(q) has a single zero in [0, 1] when M ≤ 2. It has three zeros for M = 3 from C = 32, and for M = 4, 5, 6 from C = 64.
- **Thresholds.** The count changes from one to three at C ≈ 26.036 for M = 3 and at C ≈ 35.247 for M = 4.

**Argued, not formalized.**
- *Scope of the failure.* In every computed case with C ≤ 20 the zero is unique; the failure appears once C, the ratio of the second factorial moment to the mean degree, is large. So uniqueness holds only in a moderate-C range, not as a structural property of A(q). The exact threshold as a function of M is not determined here.
- *Effect on the paper.* The source's characterization of q_c(M) as the smallest zero of det A(q) in [0, 1] is proved there and is unaffected. Only the shortcut "the unique zero" fails: for dense degree distributions, a root-finder must select the smallest zero.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the seven citing works were read by the search seat, not by the orchestrator. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
