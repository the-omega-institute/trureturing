---
slug: de-boer-di-giulio-keski-vakkuri-tonni-2024-wigner-majorization-chains
bibkey: deboer2025wignermajorization
doi: 10.1103/w561-h3z5
url: https://arxiv.org/abs/2412.19698v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result
---

# Vacuum and one-photon Wigner-majorization chains

## Problem

De Boer, Di Giulio, Keski-Vakkuri and Tonni, *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*, arXiv:2412.19698v3, Section V.A.1, ask for an analytic understanding of ordered subsets of the vacuum/one-photon mixture family. The v1 question is: “It would be interesting to identify subsets of W̃_u in which all elements exhibit a Wigner majorization relationship with one another. We leave this question for future works.” The v3 conjecture concerns the branch above one half. Preregistration #18571 specifies DBKT-1: both closed intervals form chains under Proposal 1.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Fock Wigner function, Eq. (99) | `fockWigner n x p`, with the reused `genLaguerre 0 n` | Literal expression over real phase-space coordinates |
| Mixture, Eq. (100) | `mixtureWigner u x p` | $(1-u)W_0+uW_1$ |
| Positive-part functional, Eq. (97) | `levelFunctional W t` | Product Lebesgue integral on $\mathbb R^2$ of $\max(|W|-t,0)$ |
| Proposal 1, Eq. (98) | `WignerMajorizes W₁ W₂` | Every real threshold $t\geq0$ |
| DBKT-1(A) | First conjunct of `claim` and `result` | $1/2\leq u\leq v\leq1\Rightarrow\widetilde W_v\succ_W\widetilde W_u$ |
| DBKT-1(B) | Second conjunct of `claim` and `result` | $0\leq u\leq v\leq1/2\Rightarrow\widetilde W_u\succ_W\widetilde W_v$ |

Definitions of the functions are meaningful for every real parameter; the theorem imposes the source's physical parameter intervals. Endpoints and all nonnegative thresholds are included. No clause is dropped.

## Motivation

`D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result` proves the two chain assertions. `D5/S3/Analytic/Convexity/DerivativeHingeMajorization` supplies the general analytic statements. Its cancellation theorem treats continuous profiles with an everywhere derivative, an integrable derivative, one nonnegative peak position, the corresponding derivative signs, and zero endpoint values at zero and infinity.

## Gap

The paper's numerical chain on the Wigner-negative branch supplies individual comparisons. The universal statement requires every ordered pair on each branch and every nonnegative threshold. The vacuum-majorization theorem for Wigner-positive mixtures of the lowest three Fock states supplies a different endpoint comparison; it does not state either complete chain.

## Route

With $s=x^2+p^2$, $h(s)=s e^{-s}$, $k(s)=(1-s)e^{-s}$ and $c=1-2u$, the mixture satisfies $\pi\widetilde W_u=h+ck$. `mixture_closed` and `level_reduction` identify its level functional with $J_T(c)=\int_0^\infty\max(|h+ck|-T,0)\,ds$, where $T=\pi t$. The general `radial` identity supplies the polar factor. `boundary_cancellation` gives $\int k\mathbf1_{h>T}=0$; `concrete_cancel` applies it to this profile. `hinge_min` integrates a supporting-line inequality, while `hinge_convex` establishes convexity. `convex_rays` and `concrete_rays` give the opposite monotonicities on the rays meeting at $c=0$. `result` transfers them to the two parameter intervals.

## Falsifier

An ordered pair in either stated interval and a nonnegative threshold violating its inequality would refute DBKT-1. A failure of the source correspondence, integrability, cancellation, or the convex minimum would invalidate the proposed route. Strict inequalities and comparisons between the branches are separate assertions.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.lean`, supported by `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.lean`. Their Scribes display every public definition and theorem, including the expanded proposition of `result`. The source locator and literature scope are in `Library/ContinuousObservables/deboer2025wignermajorization.md`.

The four-slot escape audit is unfinished: [#20140](https://github.com/the-omega-institute/trureturing/issues/20140). Its targets are `radial`, `boundary_cancellation`, `hinge_min`, `hinge_convex`, `convex_rays`, and the settling `result`. A faithful compiled realization and readout for the full analytic telescopes is missing; no `declared_validated` registration is claimed.

### Experiment

[Independent numerical checks](https://github.com/the-omega-institute/trureturing-experiments/tree/fec5519e820aa7ae835e09692fb27fdccb2f49b7/docs/reports/deboer-digiulio-keskivakkuri-tonni-2025-vacuum-one-photon-wigner-majorization) use the pinned `check.py`, SHA-256 `26165b657205c4f6d509c5a79fbaa3a07a13ecab3c2a79a61cbe378b33b5cfd8`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/deboer-digiulio-keskivakkuri-tonni-2025-vacuum-one-photon-wigner-majorization/check.py`, exit 0. Each branch has 8610 pair/threshold comparisons: parameters on the $1/40$ grid and 41 thresholds in $[0,1/\pi]$, with zero violations. The maximum closed-form error for $I_0$ and $M$ is $7.1491\cdot10^{-30}$. The checker finds opposite signs of level-functional differences at tested thresholds for all 190 tested cross-branch pairs $0<u<1/2<v\leq1-u$. The five specified plane quadratures on $[-7,7]^2$ differ from radial values by less than $2\cdot10^{-7}$. The full-family and reversed-direction controls have their expected outcomes. These are finite numerical readings, not universal proofs.

## Triage

Tier 1: an explicit published question and conjecture, with settlement Proved under #18571. The literature reading checks source versions v1 and v3, Van Herstraeten–Jabbour–Cerf (Quantum 7, 1021), Upadhyaya et al. arXiv:2507.22986v2, the citing works and repository scope described in the preregistration. Completeness is `ASSUMED-UNVERIFIED`.

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| DBKT-1(A) and (B), including endpoints | Proved | Kernel-checked `result : claim`, all parameters and nonnegative thresholds |
| General derivative cancellation / escape witness | Proved | Kernel-checked `boundary_cancellation`, with its complete analytic hypotheses |
| Live cancellation path to the two chains | Computed | Compiled constant dependencies: `boundary_cancellation` → `concrete_cancel` → `concrete_rays` → `result`; both ray components retain the cancellation equality |
| Classification scope | Computed | Dependency propagation expands both delivered modules; the normalization/content boundary is a semantic judgement |
| Convex minimum and monotone rays | Proved | Kernel-checked `hinge_min`, `hinge_convex`, `convex_rays` |
| Plane and level integrability | Proved in transient Lean checks | Every real mixture parameter; every nonnegative threshold for the level integrand |
| Independent general instance | Proved in transient Lean checks | Cancellation and minimum for $h(s)=s^2e^{-s}$ with peak $p=2$ |
| Source-function fidelity | Proved in transient Lean checks | $L_0=1$, $L_1(y)=1-y$, and the stated closed form of the mixture |
| Strictness on each branch, as a universal extension | Open | No universal strictness declaration is part of this settlement |
| Complete cross-branch classification | Open | No uniform cross-branch classification is part of this settlement |
| General non-unimodal absolutely continuous chain rule | Open | The general cancellation theorem uses an everywhere derivative and one peak |
| Numerical branch comparisons | Computed | Pinned experiment: 8610 comparisons per branch, zero violations |
| Numerical closed forms and strictness witnesses | Computed | Pinned experiment: the stated $I_0$ and $M$ formulas and finite witnesses, maximum error $7.1491\cdot10^{-30}$ |
| Numerical cross-branch comparisons | Computed | Pinned experiment: opposite signs of level-functional differences at tested thresholds for the 190 specified grid pairs |
| Plane quadrature and negative controls | Computed | Pinned experiment: the five specified plane quadratures within $2\cdot10^{-7}$, and the stated reversed-direction/full-family controls |
| Four-slot escape registration | Open | The missing faithful realization/readout evidence for the six targets is identified in #20140 |

The decisive mechanism is the common minimum of every level functional at $u=1/2$, obtained by cancellation of the derivative direction over superlevel sets. The general lemmas allow other continuous nonnegative profiles when their derivative, integrability, sign and endpoint hypotheses are supplied. They do not assert strictness. The two chains identify mutually comparable subsets requested in v1 and include the v3 conjectured branch. They do not alter Proposal 1 or establish any claim for the paper's other preorders.

### Declaration classification

Classification expands both delivered modules and stops at protected-base owners and pinned Mathlib. The dependency edges and their propagation are computed from compiled proof terms; the normalization/content boundary is a semantic judgement. The equality from `boundary_cancellation` remains on the live proof path of both ray components and of the settling `result`. The tables identify the source declarations, omitting compiler-generated auxiliaries.

| Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.radial` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation` | content | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation` | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_cancel` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hingeIntegral` | bind-only | none | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_convex`, `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_min`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_integrable` | bind-only | none | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_convex`, `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_min` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_subgradient` | bind-only | none | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_min` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_min` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_convex` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.convex_rays` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.fockWigner` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.claim`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixtureWigner`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixture_closed`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixtureWigner` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.claim`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixture_closed`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.levelFunctional` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.WignerMajorizes`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.WignerMajorizes` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.claim`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.claim` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_cancel`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.h_deriv`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k_cont`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k_integrable`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixture_closed`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k_cont` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.h_deriv` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_cancel` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.h_integrable` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k_integrable` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.k_integrable` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_cancel`, `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_cancel` | content | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation` | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.concrete_rays` | content | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation` | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.mixture_closed` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.level_reduction` | bind-only | none | `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` |
| `D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization.result` | content | `D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation` | settling result |

## ASSUMED-UNVERIFIED

Literature-screen completeness and any claim of originality beyond the searched scope are unverified. The published question and the exact chain proposition are distinct from empirical physical claims. Four-slot registration remains unfinished under #20140. Strictness, complete cross-branch classification and the general non-unimodal absolutely continuous extension remain open.
