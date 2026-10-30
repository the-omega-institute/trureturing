---
slug: salek-hayashi-winter-2020-harrow-parallel-chernoff-exponent
bibkey: salekhayashiwinter2022adaptive
doi: 10.1103/PhysRevA.105.022419
url: https://arxiv.org/abs/2011.06569v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result
---

# The Harrow channel pair's parallel Chernoff exponent is not one

## Problem

F. Salek, M. Hayashi and A. Winter, *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*, arXiv:2011.06569v3 [quant-ph] (Phys. Rev. A 105, 022419 (2022)), study the two channels in Example 5 from two qubits $A\otimes C$ to one qubit $B$. The source text is the TeX member `cq-channel-PRXQ-revised.14jan22mh+aw.tex` of arXiv v3, md5 `f950feede0e95a6a2aa6ab8f74ee23d0`.

For these channels, the source defines the parallel error probability at lines 1305–1306 by
$P_{e,\mathbb P}^{(n)}=\frac12\left(1-\frac12\lVert\mathcal M^{\otimes n}-\overline{\mathcal M}^{\otimes n}\rVert_\diamond\right)$
and the non-adaptive Chernoff exponent at lines 1308–1315 by
$C^{\mathbb P}(\mathcal M,\overline{\mathcal M})=\lim_{n\to\infty}-\frac1n\log P_{e,\mathbb P}^{(n)}$, with the value $+\infty$ allowed. Example 5 gives
$\mathcal M(\rho\otimes\gamma)=|0\rangle\langle0|\langle0|\gamma|0\rangle+|0\rangle\langle0|\langle1|\gamma|1\rangle\langle0|\rho|0\rangle+\frac12I\langle1|\gamma|1\rangle\langle1|\rho|1\rangle$
and
$\overline{\mathcal M}(\rho\otimes\gamma)=|+\rangle\langle+|\langle0|\gamma|0\rangle+|1\rangle\langle1|\langle1|\gamma|1\rangle\langle+|\rho|+\rangle+\frac12I\langle1|\gamma|1\rangle\langle-|\rho|-\rangle$,
extended by linearity (lines 1406–1417).

After the upper bound $C^{\mathbb P}\le 13.83$, the source states at lines 1509–1514:

> Note that a lower bound is the Chernoff bound of the two pure output states $|0\rangle\langle0| = \mathcal{M}(|00\rangle\langle00|)$ and $|+\rangle\langle+| = \overline{\mathcal{M}}(|00\rangle\langle00|)$, which is $\log 2 = 1$, so $C^{\mathbb{P}}(\mathcal{M},\overline{\mathcal{M}}) \geq 1$. It seems reasonable to conjecture that this is optimal, but we do not have at present a proof of it.

The formal proposition is `claim`, namely $\operatorname{Tendsto}\;\operatorname{exponent}\;\operatorname{atTop}\;(\operatorname{nhds}(1:\mathrm{EReal}))$.

## Motivation

Example 5 exhibits a separation between adaptive and parallel discrimination: the source gives a two-use adaptive strategy with zero error and a finite parallel upper bound. If the product input $|00\rangle$ supplied the optimal parallel Chernoff rate, the lower bound $1$ would identify the exact non-adaptive exponent for this pair. Settling this conjecture determines whether that single input captures the best parallel rate.

## Gap

The literature check recorded in preregistration issue [#22662](https://github.com/the-omega-institute/trureturing/issues/22662) reports that arXiv versions v1–v3 retain the conjecture. Nineteen citing full texts were screened, including arXiv:2206.08350 and arXiv:2510.15506, without finding a parallel-rate refutation; searches of formal-conjectures and MathDB also found no result. The issue records the bounded outcome `not-found-in-searched-scope`.

## Route

1. The definitions `harrowM` and `harrowMbar` are complex-linear `MatrixMap`s on the input index `Fin 2 × Fin 2` and output index `Fin 2`. The theorem `channel_values` evaluates the matrix unit at $(0,1)$ as
   $\mathcal M(|01\rangle\langle01|)=\operatorname{diag}(1,0)$ and
   $\overline{\mathcal M}(|01\rangle\langle01|)=\operatorname{diag}(1/4,3/4)$.
2. For any types $\iota,\kappa$ with `[Fintype ι]`, `[DecidableEq ι]`, `[Fintype κ]`, any `MatrixMap` $\varphi$, any $n$, and strings $a,b:\mathrm{Fin}\,n\to\iota$ and $c,d:\mathrm{Fin}\,n\to\kappa$, `tensor_single` gives the matrix-unit entry as the product of the single-copy entries. For `tensor_diagonal`, the additional hypothesis is `[DecidableEq κ]` and a family $w$ satisfying $\forall k,\;\varphi(\operatorname{single}(a\,k)(a\,k)\,1)=\operatorname{diagonal}(w\,k)$; under these hypotheses it gives a diagonal tensor-power output. Instantiating these lemmas with `channel_values`, `tensor_values` proves the exact diagonal formula for the channel difference on the constant input string `input n`:
   $\operatorname{diag}\!\left(c\mapsto (\mathbf 1_{c=0^n}-\prod_k q(c_k))\right)$, where $q(0)=1/4$ and $q(1)=3/4$.
3. The theorem `input_density (n : ℕ)` proves, for every $n$, that the matrix unit at $(\operatorname{input} n,\operatorname{reference} n)$ is positive semidefinite and has trace $1$. The theorem `amplified_output (n : ℕ)` identifies the stabilized channel difference on this density matrix with the diagonal matrix whose entries are `difference n c`; entries at reference strings other than the fixed `reference n` vanish.
4. For every $n$, `weight_mass` proves the conjunction consisting of total weight $\sum_c\operatorname{weight}\,n\,c=1$, all-zero weight $\operatorname{weight}\,n\,0^n=(1/4)^n$, and the bounds $0\le\operatorname{weight}\,n\,c\le1$ for every $c$. Using this conjunction, `witness_norm` proves that the trace norm of the diagonal output is $2(1-(1/4)^n)$.
5. For every $n$, `diamond_lower` uses `le_sSup` with the density matrix supplied by `input_density n` and the output equality from `amplified_output n` and `witness_norm n`; it proves
   $\operatorname{ENNReal.ofReal}(2(1-(1/4)^n))\le\operatorname{diamondNorm}(\operatorname{tensorPow}\,\mathcal M\,n-\operatorname{tensorPow}\,\overline{\mathcal M}\,n)$.
   No attainment of the supremum is asserted.
6. For every $n$, `error_upper` converts that lower bound through the ENNReal definition of `parallelError` and proves
   $\operatorname{parallelError}(n)\le (1/4)^n/2$.
   The theorem `exponent_lower` has the explicit side condition $n:\mathbb N$ and $1\le n$; under that condition it weakens the error bound to $(1/4)^n$, applies monotonicity of `ENNReal.log`, and proves $2\le\operatorname{exponent}(n)$ in `EReal`.
7. Finally, `not_tendsto` assumes exactly
   $\forall n:\mathbb N,\;1\le n\to 2\le\operatorname{exponent}(n)$.
   It obtains eventual membership of this inequality from `eventually_ge_atTop 1`; if `claim` held, `ge_of_tendsto` would give $2\le1$, which is impossible. The public theorem `result` applies `not_tendsto` with `exponent_lower` and has type `¬ claim` via this route.

## Falsifier

The settlement would not match the source conjecture if the channel maps, the input ordering, the tensor powers, or the discrimination norm differed. The module keeps the source ordering $A,C$, defines both channels on every matrix entry, and uses the finite-coordinate tensor power on matrix units. Its `diamondNorm` is the supremum over matrices $\rho$ on the input-plus-reference index with $\rho$ positive semidefinite and $\operatorname{trace}(\rho)=1$, applying the channel map on the input factor and the identity map on a reference of the same index type, then taking the standard trace norm and `ENNReal.ofReal`. Its `parallelError` uses the source expression with ENNReal truncated subtraction, and `exponent` uses the natural logarithm normalized by $\log 2$ so that it is the source's base-two exponent in `EReal`. The formal `claim` is exactly convergence of this `exponent` to $1$ at `atTop`; `result` proves its negation.

The witness is the product input with each channel-use input equal to $|01\rangle$ and a computational-basis reference string equal to $|00\rangle$. A different normalization, an ancilla restriction, or use of only the source's $|00\rangle$ input would describe a different problem.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:9b22c7044de8d6fb38b5b6ba414dd7f0d76a11c5d8bb3bfc544719045472216e`;
- `claim`: `sha256:c960f6cc11eaa7e70db47b7c2329b0f9be10f3e6e88d997d5d69ed21ad249198`.

- **Proof.** The module defines the two channels, tensor powers, the stabilized norm, parallel error and exponent, and proves `result : ¬ claim`; the private `exponent_lower` route supplies the finite-`n` inequality used by `result`.
- **Axioms.** `#print axioms` for `result` reports only `propext`, `Classical.choice` and `Quot.sound`; the source contains no `sorry`, `native_decide` or new `axiom`.

## Triage

Tier 1 conjecture of a 2022 Phys. Rev. A paper, preregistered in issue [#22662](https://github.com/the-omega-institute/trureturing/issues/22662) before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** The exact proposition `claim`, namely $\operatorname{Tendsto}\;\operatorname{exponent}\;\operatorname{atTop}\;(\operatorname{nhds}(1:\mathrm{EReal}))$, is false because `result` has type $\lnot\,\mathrm{claim}$.

**Computed, not formalized** (orchestrator, recorded in issue #22662): the counterexample input was checked numerically before preregistration.

**Argued, not formalized.** The failure mechanism is that the source's $|00\rangle$ input probes only the $C=0$ sector, while the $|01\rangle$ product input probes the $C=1$ sector and produces a pure output for one channel and a mixed diagonal output with a $1/4$ eigenvalue for the other. Tensoring this pair makes the all-zero output weight $(1/4)^n$, which explains the rate-two lower-bound mechanism used in the private proof; the public result does not determine the exact optimal parallel exponent. Restricting attention to the source's $|00\rangle$ input leaves its rate-one Chernoff lower-bound calculation intact, but no global optimality statement for that restricted strategy is formalized here.

The source's adaptive statement $P_{e,\mathbb A}^{(2)}=0$ and its consequence $C^{\mathbb A}=+\infty$ are independent of the refuted parallel equality. The source's finite parallel upper bound $C^{\mathbb P}\le13.83$ and its adaptive/parallel separation use finiteness rather than equality to $1$, so they remain compatible with this settlement. The source's general question about conditions for optimality of non-adaptive protocols remains open. The exact value of $C^{\mathbb P}$, including whether it equals $2$, is not determined here.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in issue #22662 and does not establish exhaustive worldwide novelty, priority, or absence of an independent refutation. The 19 citing full texts, the arXiv-history assessment and the formal-conjectures/MathDB searches are seat-reported and were not independently reproduced here.

The correspondence between the source's channel notation and the matrix-entry implementation, and the treatment of the source's diamond norm and logarithmic conventions through `ENNReal` and `EReal`, is supported by the compiled declarations but has no separate semantic equivalence theorem. The source's assertion that all parallel error probabilities are positive, the exact value of the parallel exponent, and any sharpness or optimality claim beyond `result` are not formalized in this module. The numerical check under **Computed, not formalized** and the explanatory statements under **Argued, not formalized** are not additional public conclusions of `result`; the private helper lemmas supply the finite-n identities used in its proof.
