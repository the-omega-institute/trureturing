---
slug: carmeli-heinosaari-toigo-2025-upper-boundary-instrument-uniqueness
bibkey: carmeliheinosaaritoigo2025postponing
doi: 10.1088/1367-2630/adf87c
url: https://arxiv.org/abs/2502.19871v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.result
---

# The upper-boundary joint instrument is unique

## Problem

C. Carmeli, T. Heinosaari and A. Toigo, *Postponing the choice: advantage of deferred measurements in quantum information processing*, arXiv:2502.19871v1 (New J. Phys. 27, 094501, 2025), after the proof of the compatibility theorem for a sharp meter and the identity channel:

> We conclude that, when the point $(s,t)$ attains the second equality in \eqref{eq:QI_comp_neg}, the instrument $\tilde{\ii}^{(t)}$ is actually the unique $W$-covariant joint instrument for $\Qo_s$ and $I_t$. It is an open question whether in this case there exist other (necessarily not $W$-covariant) joint instruments.

Here:
- **The meter:** $\mathsf Q_s(x)=s|\varphi_x\rangle\langle\varphi_x|+(1-s)I/d$.
- **The channel:** $I_t=t\,\mathrm{id}+(1-t)\,\mathrm{tr}(\cdot)\,I/d$.
- **Joint instrument:** completely positive maps $J_x$ with $\sum_xJ_x=I_t$ and $\mathrm{tr}\,J_x(\rho)=\mathrm{tr}(\rho\,\mathsf Q_s(x))$.
- **The upper boundary:** $d^2s=(d^2-2)(1-t)+2\sqrt{(1-d^2)t^2+(d^2-2)t+1}$, for $t\in[-1/(d^2-1),1]$.

The definitions and the instrument $\tilde{\mathcal J}^{(t)}$ are quoted in [the literature note](../Library/QuantumContext/carmeliheinosaaritoigo2025postponing.md).

Issue [#20028](https://github.com/the-omega-institute/trureturing/issues/20028) fixes the reading: on the upper boundary, every joint instrument equals $\tilde{\mathcal J}^{(t)}$, for every $d\ge2$ and every orthonormal basis. This is proved.

## Motivation

The source quantifies the advantage of deferring the choice of a second measurement by the compatibility region of a noisy sharp meter and a noisy identity channel. The upper boundary is where the meter is as sharp as possible for a given channel quality. Uniqueness of the joint instrument there means the optimal sequential implementation is rigid: there is exactly one way to realize the boundary trade-off.

## Gap

The literature check before any Lean is recorded in #20028:
- arXiv lists only v1;
- OpenAlex lists no citing works;
- the uniqueness results the search seat found (noisy conjugate observables with rank-one effects; extreme marginals) do not cover this curve;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Work in the basis $(\varphi_x)$; a unitary transports any other basis. Let $C_x$ be the Choi matrices of a competitor.
1. **The source instrument.** Its Choi matrices are $A_x=(|v_x\rangle\langle v_x|+b^2\sum_{j\ne x}|e_{jx}\rangle\langle e_{jx}|)/d$, with $v_x=a\Omega+be_{xx}$, $b=\sqrt{1-t}$, $a=a_2(t)$ and $\Omega=\sum_ie_{ii}$.
2. **Support.** An explicit quadratic certificate, nonnegative by Cauchy–Schwarz and fixed in sum by the two marginal conditions, vanishes on every Gram row of every $C_x$. So each $C_x$ is supported on $\mathrm{span}\{v_x\}\oplus\mathrm{span}\{e_{jx}:j\ne x\}$. The endpoints $t=-1/(d^2-1)$ and $t=1$ use the degenerate forms of the same certificate.
3. **Elimination.** The channel condition fixes the $e_{jx}$ block of $C_x$ and kills its cross terms with $v_x$. The trace condition fixes the coefficient of $|v_x\rangle\langle v_x|$. So $C_x=A_x$, and Choi injectivity gives $J_x=\tilde{\mathcal J}^{(t)}(x,\cdot)$.

## Falsifier

The proof would not answer the question if the module's competitors were restricted. The module:
- allows every family of completely positive maps $J_x$, with no covariance assumption;
- states the marginal conditions exactly as the source's joint-instrument conditions;
- takes $s$ from the source's upper-boundary equation and $\tilde{\mathcal J}^{(t)}$ from the source's formula;
- proves both directions, so the characterization is not vacuous.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.lean` (998 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.lean.json`, statement `sha256:6b81822eb5c7d8791857b4a1c7df4e5e6adef559b49d5fdb172768627dd1b229`.

Declaration statements:
- `result`: `sha256:8dbbe0f78fb0d8a4a8a7ed99dc442b1e717d79db38205689fc672d508796a249`;
- `claim`: `sha256:fcfebe11e68e46ef1ddeee45606db099d50a0bfbbbc4fa8559cbbcaba4e50261`.

## Triage

Tier 1 question of a 2025 paper, preregistered in issue #20028 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** on the upper boundary of the compatibility region, the joint instruments for $\mathsf Q_s$ and $I_t$ are exactly $\tilde{\mathcal J}^{(t)}$.

**Computed, not formalized** (orchestrator, numpy, recorded in #20028): for $d=2,\dots,5$ and six values of $t$, the certificate is positive semidefinite with the predicted kernel, and the elimination system has nullity zero.

**Argued, not formalized.**
- *Mechanism.* The upper boundary is an extreme face of the compatibility region: the certificate is a dual optimal solution of the semidefinite program that defines the boundary, and its kernel is as small as the marginal conditions allow. Complementary slackness pins every competitor to that kernel, and the remaining freedom is removed by the two marginals.
- *Effect on the paper.* The covariance assumption in the source's uniqueness statement is unnecessary on the upper boundary. The source's remark on the lower boundary instruments, whose uniqueness is unclear even among covariant ones, is not addressed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the citing-work count and the related uniqueness results are seat-reported. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
