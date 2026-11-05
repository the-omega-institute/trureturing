---
slug: liu-et-al-2026-czx-parent-lindbladian-steady-state
bibkey: liuetal2026parentlindbladians
doi: 10.1103/1qyd-59z7
url: https://arxiv.org/abs/2501.10552v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.result
---

# The CZX parent Lindbladian reaches its conjectured even-ring steady state

## Problem

Y. Liu, A. Ruiz-de-Alarcón, G. Styliaris, X.-Q. Sun, D. Pérez-García and J. I. Cirac, *Parent Lindbladians for Matrix Product Density Operators*, arXiv:2501.10552v2, Phys. Rev. Research 8, 013210 (2026), DOI 10.1103/1qyd-59z7, Appendix F, “Evolution,” main.tex lines 5038–5042:

> Starting from a trivial state $\rho=\frac{1}{2^N}(\mathbb 1^{\otimes N}+\sigma_x^{\otimes N})$, we numerically verify that: when $N=4,6,8$, the resulting steady state is $\rho_\infty^{(N)}=\frac{1}{2^N}(\mathbb 1_2^{\otimes N}+\frac{1}{2^{N/2-1}}U_{CZX}^{(N)})$. We conjecture that this relation holds for general $N$.

For $n\in\mathbb N$, the module indexes computational-basis configurations by $C_n=\mathrm{Fin}(n)\to\mathrm{Fin}(2)$. Its `tensorX n` matrix flips every bit, `cz n` is the diagonal cyclic controlled-$Z$ phase, and `czxUnitary n = cz n * tensorX n`. The four-site channel is embedded at cyclic windows by `windowChannel`; `parentLindbladian n` is the sum of `windowSuperoperator n i - 1` over zero-based even starts, and `evolution n t a` is the matrix exponential of that superoperator acting on the entries of `a`.

The formal statement is `claim`: for every `n` with `Even n` and $4\le n$, the evolution from $((2:\mathbb C)^n)^{-1}\,\cdot\,(1+\mathrm{tensorX}\ n)$ tends at `atTop` to $((2:\mathbb C)^n)^{-1}\,\cdot\,(1+(2:\mathbb C)^{1-(n/2:\mathbb N):\mathbb Z}\,\cdot\,\mathrm{czxUnitary}\ n)$.

## Motivation

The source constructs a parent Lindbladian from the renormalization channels of a CZX matrix product density operator. The conjectured limit gives an explicit output for the global bit-flip state and identifies the coefficient of the CZX unitary for every even ring in the formal range. Establishing the formula determines the trajectory represented by the source's numerical observation while leaving the source's broader fixed-point and mixing questions separate.

## Gap

The bounded literature check recorded in preregistration issue [#23957](https://github.com/the-omega-institute/trureturing/issues/23957) found no earlier settlement in the searched scope. The source's v2 TeX retains the conjecture. Among the citing records checked there, 2605.04159 uses the CZX parent channels on states already carrying the $U_{CZX}$ symmetry but does not address the stated initial state or the coefficient $2^{1-N/2}$, while 2607.07857 does not discuss Lindbladians. Searches for the title and conjecture in the listed external sources and in the repository found no other settlement.

`not-found-in-searched-scope`.

## Route

1. The local channel calculation is supplied by `gauged_window_sector`, whose hypotheses are `n : ℕ`, `hn : 4 ≤ n`, `i : Fin n`, and `δ x : Fin n → Fin 2`. It states that the channel on a gauged matrix unit is the uniform average over the two middle sites when `goodWindow i δ` holds and is zero otherwise. `window_channels_commute` has hypotheses `n : ℕ`, `hn : 4 ≤ n`, `i j : Fin n`, and an arbitrary matrix `a`, and gives commutation of the two translated channels. `window_idempotent` has hypotheses `n : ℕ`, `hn : 4 ≤ n`, and `i : Fin n`, and gives idempotence of the corresponding superoperator. The entrywise bridge `window_superoperator_action` takes arbitrary `n`, `i`, `a`, `x`, and `y`, with no size hypothesis, and identifies the superoperator matrix-vector action with `windowChannel`; its proof uses `LinearMap.toMatrix_mulVec_repr` in the standard matrix basis.

2. The private `window_commute` used by the settlement additionally assumes `Even n`, `4 ≤ n`, and that both starting indices have even values. With these hypotheses the even-starting superoperators commute. `exponential_idempotent` applies to any finite decidable index type, any idempotent complex matrix, and any real `t`; it gives the exponential of the shifted idempotent. `finite_projection_limit` applies to any finite decidable index type, a list `es` of matrices, a proof that every member of `es` is idempotent, and a proof that `es` is pairwise commuting. `exponential_limit` then assumes `Even n` and `4 ≤ n` and shows that the exponential of `parentLindbladian n` tends to the product of the even-starting window superoperators.

3. The gauge and coverage calculation uses `all_good_iff_constant` with `n : ℕ`, `4 ≤ n`, and `δ : Fin n → Fin 2`; it characterizes goodness on every even-starting window by constancy of `δ`. `middle_sites_cover` assumes `Even n` and `4 ≤ n` and proves that the middle sites of those windows cover `Fin n`. `window_word_gauged` assumes `4 ≤ n`, an arbitrary list of starts, and `δ x : Fin n → Fin 2`; it reduces the product action on a gauged unit to the corresponding coordinate average when every listed window is good. Under `Even n` and `4 ≤ n`, `projection_formula` applies this reduction to an arbitrary matrix `a` and gives the projection as the normalized sum of its trace component and its CZX-unitary pairing.

4. The coefficient calculation uses `flip_diagonal` with `0 < n` and `symmetry_trace` with `0 < n` to show the relevant diagonal traces vanish. `coefficient_partition` rewrites the CZX pairing with `tensorX` as a cyclic sign sum, and `partition_transfer` assumes `0 < n` to identify that sum with the trace of the `n`-th power of $\begin{pmatrix}1&1\\1&-1\end{pmatrix}$. `transfer_coefficient` assumes `Even n` and `4 ≤ n` and evaluates the pairing as `(2 : ℂ) ^ (n / 2 + 1)`. `projection_initial`, with the same `Even n` and `4 ≤ n` hypotheses, evaluates the product projection on the specified initial matrix and obtains the target coefficient.

5. `evolution_limit` assumes a convergence hypothesis for the matrix exponential of `parentLindbladian n` to the projection and transfers it to the evolution of the specified initial matrix. The theorem `result` introduces exactly `n`, `hn : Even n`, and `hsize : 4 ≤ n`, supplies `exponential_limit n hn hsize`, rewrites with `projection_initial n hn hsize`, and returns `result : claim`.

## Falsifier

The settlement would not identify the source conjecture if the formal channel differed from the source channel. A falsifier would be a mismatch in the source-order four-bit convention, the explicit $4\times4$ matrix $U$, the signed $16\times16$ matrix $V$, the block projections or multiplicity factor in `renormS` and `renormT`, the cyclic window embedding, the even-start sum in `parentLindbladian`, or the matrix-vector action used by `evolution`. It would also be a mismatch in the quantifiers or in the integer exponent $1-(n/2:\mathbb N)$ of the target. The source definitions and these conventions are the ones used by the module; finite checks at selected sizes cannot by themselves establish the general statement.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.lean.json`.

Declaration statements:
- `result`: `sha256:b1bead68d09e339731ba94f191dde02bf8d4739875140a4af52b1bd9af4ab0bb`;
- `claim`: `sha256:31015ed94362de449e204d8f152259b759589578937b81f799b822514daa2468`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2025 preprint, published 2026 with the conjecture retained, preregistered in issue #23957 before any Lean.  
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every natural number `n` satisfying `Even n` and $4\le n$, the function $t\mapsto\mathrm{evolution}\ n\ t\ (((2:\mathbb C)^n)^{-1}\,\cdot\,(1+\mathrm{tensorX}\ n))$ tends as $t\to+\infty$ to $((2:\mathbb C)^n)^{-1}\,\cdot\,(1+(2:\mathbb C)^{1-(n/2:\mathbb N):\mathbb Z}\,\cdot\,\mathrm{czxUnitary}\ n)$ in the matrix topology.

**Computed, not formalized:** none.

**Argued, not formalized.** The result is a trajectory statement for one specified initial matrix, so it does not classify the full steady-state space, prove convergence from other initial states, or provide a mixing-time bound. The source's two-parameter steady-state discussion, Proposition F.1, other Appendix F bounds, other initial states, and its other examples remain outside this declaration. Any source use that needs only this displayed relation under the module's `Even n` and $4\le n$ hypotheses can use the proved formula; a use that requires the broader fixed-point space, a physical-state classification, or a rate of convergence remains open. The source's separate no-go statement about fully separable initial states is not settled by this module.

## ASSUMED-UNVERIFIED

The literature check is bounded by the citing records and external searches recorded in issue #23957; it does not establish exhaustive worldwide novelty or priority. The finite exact checks listed above are not formalized declarations. Positivity or density-operator interpretation beyond the matrix convergence stated by `result`, the full steady-state space, other initial states, mixing times, the remaining Appendix F claims, and the source's other examples are unverified here.
