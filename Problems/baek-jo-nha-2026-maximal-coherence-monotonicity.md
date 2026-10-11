---
slug: baek-jo-nha-2026-maximal-coherence-monotonicity
bibkey: baekjonha2026maximalcoherence
doi: null
url: https://arxiv.org/abs/2607.05847v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result
---

## Problem

Baek, Jo and Nha, *Maximal coherence of quantum measurement and the resource theory of sharpness*, arXiv:2607.05847v1, asks whether $C_D^{\max}$ remains monotone under general CP unital maps for non-dichotomic POVMs. Table I marks the corresponding entry under any fuzzifying operations as open.

## Motivation

The question concerns the spectral distance $D_\infty$ and the tetrahedral SIC qubit POVM. The settling declaration is `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result`.

## Gap

The source leaves the general CP-unital, dimension-changing case unresolved. The settlement supplies a four-outcome counterexample using the discarding dual $J(X)=X\otimes I_2$.

## Route

The module defines POVMs, incoherent POVMs, $D_\infty$, fixed-basis coherence, maximal coherence, CP-unital duals and the source claim. It constructs the tetrahedral SIC effects, proves the simultaneous-basis upper bound $C_{D_\infty}^{\max}(\mathsf M_{\rm SIC})\le\frac12\sqrt{2/3}$, proves the Bell-basis lower bound $C_{D_\infty}^{\max}(J(\mathsf M_{\rm SIC}))\ge\frac12$, and derives `result : ¬ claim`.

The coordinates choose $\mathbb C^2\otimes\mathbb C^2\cong$ `Fin 4` through `finProdFinEquiv`, $(i,j)\mapsto2i+j$, in the order $|00\rangle,|01\rangle,|10\rangle,|11\rangle$. The module uses `open scoped ComplexOrder` for the complex positive-semidefinite calculations; these are Lean elaboration choices preserving the source meaning.

## Falsifier

The claim is falsified by the instance $d=2$, $e=4$, $n=4$, $\alpha=1$, $q_x=1/4$, the tetrahedral SIC POVM and $J$. The strict inequality $\frac12>\frac12\sqrt{2/3}$ is the final contradiction.

## Evidence

The SIC instance and `result` are kernel-checked in Lean with axiom closure contained in `{propext, Classical.choice, Quot.sound}`. The stabilization statement $C_D^{\max}(\mathsf P\otimes I_d)=S_D(\mathsf P)$, the characterization for jointly convex distances, and the $A_i(t)$ family are paper arguments from the preregistration's Consequences; they are not Lean declarations in this module. The exact sampled checks are computed evidence from [`check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/e79e3f95fef7b48c4474dbaf42991a0601a8dd05/docs/reports/baek-jo-nha-2026-maximal-coherence-ancilla-nonmonotone), run as `python3 check.py` with exit 0 and SHA-256 `b0d07f99a84ffde3e5a0285f79184a2e0dfe8cf0dcf4ad2c8c151bc7d971d96c`; it reports `bad= 0` for 20,000 random unitaries and Bell-diagonal POVMs, and for the stabilization sample tests 200 random qubit POVMs.

## Triage

| item | status | evidence |
|---|---|---|
| Tensoring an ancilla and choosing the Bell basis forces normalized partial traces of incoherent competitors to be scalar, so the ancilla coherence is at least sharpness; the SIC gap is removed. | proved | Kernel-checked `result`, with the SIC upper and Bell lower bounds on its proof path; the mechanism is explained by the Rayleigh argument. |
| For every unitarily invariant, CP-unital-contractive distance, $C_D^{\max}(\mathsf P\otimes I_d)=S_D(\mathsf P)$. | proved in prose | Preregistration Consequences derivation; the lower bound uses the Bell-basis normalized partial trace and the upper bound is the standard sharpness comparison. |
| For jointly convex such $D$, monotonicity under all fuzzifying operations iff $C_D^{\max}=S_D$ on every POVM. | proved in prose | Preregistration Consequences derivation: the forward direction uses monotonicity of sharpness and the reverse direction applies the stabilization map to a coherence–sharpness gap. |
| $A_i(t)=(I+t\,\vec n_i\cdot\vec\sigma)/4$, $0<t\le1$, has increase $\frac t2(1-\sqrt{2/3})$; effects are full rank for $t<1$. | proved in prose; computed | The formula and full-rank statement are derived in the preregistration Consequences. The numerical entry runs `python3 check.py` at the pinned experiment commit, exit 0, SHA-256 `b0d07f99a84ffde3e5a0285f79184a2e0dfe8cf0dcf4ad2c8c151bc7d971d96c`, over the stated finite sampling scope. |
| Whether $C_\diamond^{\max}(\mathsf M_{\rm SIC})<S_\diamond(\mathsf M_{\rm SIC})$. | open | No Lean declaration or computation in this delivery addresses the diamond distance. |
| Whether monotonicity also fails for dimension-preserving fuzzifying operations. | open | No Lean declaration or computation in this delivery changes the output dimension. |

### What the settlement shows

The general CP-unital monotonicity question is refuted for non-dichotomic POVMs when the fuzzifying map may change dimension. The stabilization and characterization statements remain prose derivations with the hypotheses stated above. The diamond-distance and dimension-preserving questions remain open.

## ASSUMED-UNVERIFIED

The literature screen establishes the cited source and its open wording in the searched scope. Exhaustive worldwide novelty beyond the cited source and the recorded literature search is not claimed.
