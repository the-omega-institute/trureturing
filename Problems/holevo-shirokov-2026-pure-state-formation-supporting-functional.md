---
slug: holevo-shirokov-2026-pure-state-formation-supporting-functional
bibkey: holevo2026logsobolevformation
doi: null
url: https://arxiv.org/abs/2609.12667v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.result
---

# The entanglement of formation has a supporting affine functional at every pure state

## Problem

A. S. Holevo and M. E. Shirokov, *Log-Sobolev inequality, von Neumann entropy and Entanglement of Formation*, arXiv:2609.12667v3, Introduction:

> It is somewhat surprising that the above problem is nontrivial even in the case when the state $\rho$ is pure. We and GPT-5.6 have found neither a general proof nor counterexamples which would confirm or refute the hypothesis of the existence of a supporting affine functional for the EoF at any pure bipartite state.

Section 3.1 restates the finite-dimensional question. The verbatim passages are in [the literature note](../Library/Entropy/holevo2026logsobolevformation.md).

Issue [#19308](https://github.com/the-omega-institute/trureturing/issues/19308) fixes the reading: for all finite a, b and every unit ψ ∈ ℂ^a ⊗ ℂ^b, there is a Hermitian W with Tr(W P_ψ) = E_F(P_ψ) and Tr(Wσ) ≤ E_F(σ) for every density matrix σ. This is proved.

## Motivation

A supporting affine functional at ρ is equivalent to a one-sided Lipschitz lower bound for E_F at ρ. The authors' earlier work (arXiv:2608.27363) shows that such functionals fail at some mixed boundary states, and the source settles pure states with equal Schmidt coefficients.

## Gap

The literature check before any Lean is recorded in #19308:
- Song–Zong (arXiv:2609.31097) settles two-qubit states only;
- arXiv searches find no other work on the question;
- the repository had no record of it.

`not-found-in-searched-scope`.

## Route

Let R be the marginal of P_ψ, m its least positive eigenvalue, c = 1/m and K = 2bc, and put W = −(log₀ R) ⊗ I − K(I − P_ψ).
1. **Scalar bound.** −t ln t ≥ −t log₀ r − (t − r) − c(t − r)² for each eigenvalue r of R and each t ∈ [0, 1].
2. **Matrix bound.** Averaging with the doubly stochastic overlaps of the two eigenbases gives S(T) ≥ −Tr(T log₀ R) − c‖T − R‖²_HS for every density T.
3. **Pure states.** ‖Tr_B X‖²_HS ≤ b‖X‖²_HS, and ‖Q − P‖²_HS = 2(1 − Tr PQ) for pure Q. Together they give S(Tr_B Q) ≥ Tr(WQ), with equality at Q = P.
4. **Convex roof.** Averaging over pure ensembles gives Tr(Wσ) ≤ E_F(σ).

## Falsifier

The theorem would not settle the question if the module's E_F differed from the source's. The module uses the frozen E_F of `MoreauYosidaFormationSelectiveLoccRefutation`, the infimum over finite pure ensembles of the average marginal entropy. Because E_F takes values in [0, ∞], the inequalities are stated through `ENNReal.ofReal`. This is equivalent to the real inequality because E_F ≥ 0.

## Evidence

The canonical source is `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.lean` (428 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registration:** `Reg/D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.lean` (`result`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.lean.json`, statement `sha256:e737c6fcab8963681fefaef44d9b0911ded907b75571e52f37ccacd611433c55`.

Declaration statements:
- `result`: `sha256:f23e4348040e7cfac128c5c1ff0fb51bd369df0e61d9e4106fb8818155b378a9`;
- `claim`: `sha256:6034f7041d2ed70eb8a87196c23ca01a47e89da6d6df4e1f364ac0e221dcce55`.

## Triage

Tier 1 open question of a 2026 paper, preregistered in issue #19308 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** every pure state of a finite-dimensional bipartite system has a supporting affine functional for the entanglement of formation.

**Argued, not formalized.**
- *Mechanism.* The entropy of the marginal is controlled from below by the relative-entropy tangent at R plus a quadratic correction. The correction is quadratic in the Hilbert–Schmidt distance, and for pure states that distance is linear in 1 − Tr(PQ), which is affine in Q. The constant K = 2b/m depends on the least positive Schmidt coefficient, so it blows up as the Schmidt spectrum degenerates. Dividing E_F(P) − E_F(σ) by ‖P − σ‖₁ is therefore bounded at every pure state, though not uniformly.
- *Scope.* Mixed boundary states remain excluded, consistent with the earlier counterexamples.

**Effect on the paper.** The pure-state question of the Introduction and Section 3.1 is answered positively for all finite dimensions.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
