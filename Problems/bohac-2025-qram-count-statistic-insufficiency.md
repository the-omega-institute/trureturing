---
slug: bohac-2025-qram-count-statistic-insufficiency
bibkey: bohac2025biasclassqram
doi: 10.48550/arXiv.2512.17503
url: https://arxiv.org/abs/2512.17503v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result
---

# The plus-count statistic is insufficient for exact-weight discrimination

## Problem

L. Bohac, *Bias-Class Discrimination of Universal QRAM Boolean Memories*, arXiv:2512.17503v1, asks in Remark 5.3, “Open question: do collective measurements help?” The source TeX `bias_class_discrimination.tex`, lines 454–457, states:

> The $t$-copy induced state $\rho_p^{(t)}$ generally does not factor as $\rho_p^{\otimes t}$, so in principle a collective Helstrom measurement on $\rho_{p_0}^{(t)}$ vs.\ $\rho_{p_1}^{(t)}$ could outperform any separable strategy.
>
> An interesting open problem is to characterize the optimal error exponent for distinguishing these \emph{exchangeable} but potentially correlated mixtures, and to determine whether the ``$\ket{+}$-count'' statistic is sufficient for optimal discrimination in the exact-weight prior model.

The module formalizes the second question through `claim`. Its `weightClass n m` is the finite set of Boolean memories $f : \mathrm{Fin}(2^n) \to \mathrm{Bool}$ having exactly $m$ true addresses. Its `copyState n t m` averages the $t$-fold product of one `addressState n f` over that class, with the same $f$ in every copy. For every $n \ge 1$, $t \ge 1$, $m_0,m_1 \le 2^n$, every $e : \operatorname{Matrix}(\mathrm{Fin}(t) \to \mathrm{Fin}(2^n))(\mathrm{Fin}(t) \to \mathrm{Fin}(2^n))\,\mathbb{C}$ with `e.PosSemidef` and `(1 - e).PosSemidef`, and `successProb` as defined in the module, `claim` requires a Boolean rule $g : \mathrm{Fin}(t+1) \to \mathrm{Bool}$ such that
$\operatorname{successProb}(n,t,m_0,m_1,e) \le \operatorname{successProb}(n,t,m_0,m_1,\operatorname{countTest}(n,t,g))$.
This is the equal-prior special case: if the count were sufficient for every prior, it would in particular satisfy this equal-prior assertion.

## Motivation

The source's separable strategy measures the all-plus projector on each address register and retains only the number of plus outcomes. With a persistent memory, the copies are exchangeable mixtures and need not be independent, so a measurement can retain information about which non-plus outcomes occurred. Establishing count sufficiency would have made the simple statistic optimal for the exact-weight prior model; a counterexample shows that this information compression loses discrimination power. The source's separate question about the optimal collective error exponent is not settled by this dossier.

## Gap

Remark 5.3 leaves count sufficiency as an open question after observing that the induced state can be correlated. The bounded check recorded in issue [#24783](https://github.com/the-omega-institute/trureturing/issues/24783) found only arXiv v1 of the source, no citing works in the queried OpenAlex record, and no result answering this question in the companion preprint or in the searched repository. The prior works listed there concern different objectives or access models. The check is therefore `not-found-in-searched-scope`.

## Route

The refutation specializes `claim` to $n=2$, $t=2$, $m_0=1$, $m_1=2$ and to the private effect `witness`.

1. For every $y,z : \mathrm{Fin}\,4$, `walsh_orthogonal y z` proves the Walsh inner-product identity, and `plus_walsh` proves `plusState 2 = walsh 0`. The exact weight-one and weight-two classes are given by `class_one` and `class_two`. For every $f : \mathrm{Fin}\,4 \to \mathrm{Bool}$, membership hypothesis `hf : f ∈ weightClass 2 1`, and $y : \mathrm{Fin}\,4$, `one_overlap f hf y` proves the squared overlap $1/4$; `weight_one_law y z` then gives trace $1/16$ for every Walsh pair.
2. `class_two_states` gives the six exact Walsh-state equalities for the weight-two memories. `weight_two_state` identifies `copyState 2 2 2` with one third of `reject`. For every $y,z,u,v : \mathrm{Fin}\,4$, `pair_orthogonal y z u v` proves orthogonality of the product Walsh vectors. `reject_projector` has no hypotheses and proves `reject` is an `IsStarProjection`; `witness_valid` has no hypotheses and proves `witness.PosSemidef ∧ (1 - witness).PosSemidef`.
3. For every $f : \mathrm{Fin}\,4 \to \mathrm{Bool}$, `address_norm f` proves unit norm. `weight_one_trace`, `reject_trace`, and `weight_two_trace` have no hypotheses and give the relevant traces, and `witness_success` proves
$\operatorname{successProb}(2,2,1,2,\operatorname{witness}) = 29/32$.
4. For every $y,z : \mathrm{Fin}\,4$, `weight_two_law y z` gives the weight-two Walsh-pair trace as $1/3$ when $y=z$ and $y\ne0$, and zero otherwise. `complement_walsh` identifies the complement of the plus projector with the three nonzero Walsh projectors. For every $k : \mathrm{Fin}\,3$, `count_walsh k` expands the count projector in the Walsh-pair projectors, and `count_laws k` gives the two count laws. For every $g : \mathrm{Fin}\,3 \to \mathrm{Bool}$, `count_bound g` proves
$\operatorname{successProb}(2,2,1,2,\operatorname{countTest}(2,2,g)) \le 23/32$.
5. `result` applies `claim` at $n=2$ and $t=2$, with the side conditions $2\ge1$, $2\ge1$, $1\le2^2$, and $2\le2^2$, and with the two positivity hypotheses supplied by `witness_valid`. The resulting count rule contradicts `witness_success` and `count_bound`.

## Falsifier

The formal statement is the equal-prior exact-weight model encoded by `weightClass`, `copyState`, `successProb`, and the two positive-semidefiniteness hypotheses in `claim`. A source interpretation using a different prior, a memory resampled independently for each query, or a restricted class of effects would be a different question. The witness is a Walsh-basis product measurement, so the result refutes sufficiency of the plus count without determining the optimum over all collective Helstrom measurements. A claim that only the source's plus-count strategy is achievable is also a different statement and is not challenged by this result.

## Evidence

The canonical source is `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.lean.json`.

Declaration statements:
- `result`: `sha256:b6d2ebcb5c8888d4ae84b427285af0b045da17daf8cea15c7df81a3799d51ee5`;
- `claim`: `sha256:ebe0cb534ec1a6ffe00e7c3180180e2ad2c04263bafecd06061b12a3581fdc51`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open question in a December 2025 preprint, preregistered in issue #24783 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** `¬ claim`. Thus it is false that for every $n \ge 1$, $t \ge 1$, admissible pair $m_0,m_1$, and positive-semidefinite effect $e$ with positive-semidefinite complement, some deterministic rule on the $t+1$ possible plus counts has at least the equal-prior success of $e$. The proof exhibits the instance $n=2$, $t=2$, $m_0=1$, $m_1=2$ and a valid effect for which every $g : \mathrm{Fin}\,3 \to \mathrm{Bool}$ is bounded by $23/32$, while the witness has success $29/32$.

**Computed, not formalized.** None.

**Argued, not formalized.**
- **Mechanism beyond the witness.** A persistent-memory prior can correlate copies, so a statistic that records only plus-versus-nonplus counts can discard relations among the nonplus outcomes. The module establishes this mechanism for one witness but does not formalize a criterion for when such relations improve discrimination for arbitrary sizes, copy counts, or weights; that generalization is open.
- **Nearby scope.** The refutation is a single exact-weight instance. It does not establish failure for every $N$, every $t$, every pair of weights, or unequal priors, and it does not prove sufficiency in any restricted case.
- **Other source statements.** The source's separable measurement and its count distribution remain achievable statements; their validity does not require count sufficiency. The source's optimal error exponent, the collective Helstrom optimum, and any claim for a different prior model remain open. Any later argument that used count sufficiency to promote the separable strategy to an optimality or exponent result would need to be withdrawn or supplied with an additional restriction; no such dependent result appears in the bounded check.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The companion-preprint and prior-literature readings reported in issue #24783 were not reproduced here. The mechanism beyond the formal $N=4$, $t=2$ witness, all generalizations to other sizes, unequal-prior conclusions, the optimal collective success, and the optimal error exponent are not formalized. Any source interpretation outside the exact definitions and hypotheses of `claim` remains unverified.
