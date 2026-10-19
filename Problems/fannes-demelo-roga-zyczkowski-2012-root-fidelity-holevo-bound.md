---
slug: fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound
bibkey: fannes2011fidelity
doi: null
url: https://arxiv.org/abs/1104.2271v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.result
---

# The three-state root-fidelity Holevo bound

## Problem

M. Fannes, F. de Melo, W. Roga and K. Życzkowski, *Matrices of fidelities for ensembles of quantum states and the Holevo quantity*, arXiv:1104.2271v1, page 10, Conjecture 1:

> For any ensemble E₃ = {(pᵢ, ϱᵢ)} with K = 3 three states of arbitrary dimension d the corresponding Holevo quantity χ(E₃) is bounded from above by the entropy of the matrix C√F(E₃) defined in (16): χ(E₃) ≤ S(C√F(E₃)).

Here $S(X)=-\operatorname{Re}\operatorname{tr}(X\log X)$, $\chi=S(\sum_i p_i\rho_i)-\sum_i p_iS(\rho_i)$, and $C_{ij}=\sqrt{p_ip_j}\operatorname{tr}|\sqrt{\rho_i}\sqrt{\rho_j}|$. The logarithm is natural. The matrices are positive semidefinite of trace one; weights are nonnegative and sum to one.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Three states of arbitrary dimension | `claim` quantifies `d : ℕ`, three matrices indexed by `Fin 3` on `Fin d` | No invertibility assumption; dimension zero has no trace-one state |
| Density matrices | Each matrix is positive semidefinite and has trace one | Singular matrices included |
| Ensemble probabilities | Each weight is nonnegative, and their sum is one | Zero weights included |
| Fidelity and matrix (16) | The literal trace-norm/square-root expression in `rootFidelityMatrix` | The trace norm is the existing `FiniteTraceDistance.traceNorm` |
| Holevo quantity and entropy | `holevo`; the literal trace-log expression in `claim` | Ordinary complex matrices, with the L2 operator norm for functional calculus |
| Upper bound | `FannesRootFidelityHolevo.result` | The full expanded claim |

## Motivation

The settling declaration is `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.result`. It establishes the unrestricted three-state mixed-state bound. A common rank-one refinement preserves all three pairwise root fidelities, and entrywise modulus increases entropy for positive three-by-three Gram matrices.

## Gap

[Preregistration #19184](https://github.com/the-omega-institute/trureturing/issues/19184) records the source, quantifiers, Tier 1 classification and literature screen. The searched sources include the original paper, Zhang–Wu–Fei arXiv:1110.5979, Roga's thesis arXiv:1108.5065, Shirokov arXiv:1703.05671 and arXiv:2506.05335, Nuradha–Mishra–Leditzky–Wilde arXiv:2404.16101 §5.6.1, and Uhlmann quant-ph/0007018. The recorded partial results impose additional compatibility or qubit restrictions. No settlement was found in this searched scope. Completeness is ASSUMED-UNVERIFIED.

## Route

Two polar gauges make the first two cross products positive. Diagonalizing the remaining polar unitary supplies one common rank-one index for all three states. The scalar three-spectrum comparison fixes the first two elementary symmetric coefficients and orders the determinant; it gives the entropy comparison under entrywise modulus. Channel data processing supplies the log-sum inequality, and Gram-matrix entropy accounting combines these statements into the claimed bound.

The trace-log expression is literal in the claim. Proofs use `ChenKatoBrandaoCMIRefutation.entropy` through the private consumed correspondence `entropy_owner_eq_trace_log`. The public owners `ChenKatoBrandaoCMIRefutation.entropy_diagonal` and `PeritoTensorBlockBound.unitary_diagonalization` supply diagonal entropy and unitary diagonalization on the elaborated dependency path. `CanonicalRelativeModularModel` is an unfrozen dev dependency through `CanonicalChannelDPI`; it is not frozen by this delivery.

## Falsifier

A restriction excluding singular states or zero weights, a mismatch with the source fidelity, an unproved matrix-support obligation, or failure of either the common decomposition or the modulus comparison would invalidate the settlement. The settling proposition contains no added compatibility, rank or invertibility hypothesis.

## Evidence

`FannesRootFidelityHolevo.result` proves `claim`. `ThreeByThreeModulusEntropy.entryModulus_entropy_mono` proves the trace-log entropy comparison for arbitrary unnormalized positive semidefinite complex three-by-three matrices. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The Scribe resolution claim is Proved. The four-slot escape audit is unfinished for the settling theorem, the five public modulus theorems, and the two published owner theorems: [#19212](https://github.com/the-omega-institute/trureturing/issues/19212). No compiled source-faithful registration or `declared_validated` evidence is asserted.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f3702d38787bb44e22335abf5746e5768e6b7d18/docs/reports/fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound). Command: `python3 docs/reports/fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound/check.py`; exit 0. Script SHA-256: `e4a6970946d8482e8326b1200461dba8ddef55290a04b22b7e69536960474984`. The exact pinned bytes were rerun. Over 2,000 random ensembles in dimensions 2, 3, 4, 5 and 7, the maximum simultaneous-fidelity error is $9.104\times10^{-15}$, the maximum $\chi-\Xi$ is $6.286\times10^{-13}$, and the maximum $\chi-S(C)$ is zero. Across their Gram blocks and 20,000 normalized positive three-by-three matrices, the maximum $S(G)-S(|G|)$ is $3.893\times10^{-13}$. The rank-two equality example has error $1.110\times10^{-16}$ and $\chi=0.636514168295$. These are finite numerical checks, not equality-classification or uniform error theorems.

## Triage

### What the settlement shows

- **Kernel-checked:** the full three-state root-fidelity Holevo bound, including singular states and zero weights, is `FannesRootFidelityHolevo.result`.
- **Kernel-checked:** entrywise modulus increases trace-log entropy for every unnormalized positive semidefinite three-by-three matrix, by `ThreeByThreeModulusEntropy.entryModulus_entropy_mono`.
- **Kernel-checked private consumed helper:** `FannesRootFidelityHolevo.simultaneous_rank_one_decomposition` supplies one rank-one index preserving all pairwise root fidelities of three finite positive semidefinite matrices. This helper is conservatively bind-only after expanding its spectral and polar suppliers; it supplies no separate admission basis.
- **Computed:** the pinned experiment's three distinct rank-two states $\rho_i=|x_i\rangle\langle x_i|\otimes I_2/2$, for $x_i=0,+,1$ and $p_i=1/3$, attain equality within $1.110\times10^{-16}$. The matrices for $0$ and $1$ commute, while each fails to commute with the $+$ matrix. The example is therefore a noncommuting ensemble, not a pairwise-noncommuting triple. No exact equality-classification theorem is claimed.
- **Explanation of the proved mechanism:** two polar gauges and an eigenbasis for the remaining unitary preserve the three fidelities; fixed first two spectral coefficients and ordered determinant control modulus entropy; channel data processing supplies log-sum. These are the proof's structural steps, not additional public theorems.
- **Consequence by specialization:** the unrestricted three-state mixed-state statement contains the source's pure-state and qubit cases. The source's separate damped and subensemble estimates remain valid on their stated hypotheses; no separate formal implication to every damped estimate is claimed.
- **Open:** classification of all equality cases.
- **Open:** a corresponding bound beyond three states. For four or more states the source gives examples whose root-fidelity matrix is not positive, so a direct density-matrix entropy formulation needs additional hypotheses or a different object.
- **ASSUMED-UNVERIFIED:** completeness of the literature search for prior published settlements.

## ASSUMED-UNVERIFIED

The bounded literature screen does not establish exhaustive priority. The numerical checks cover only the finite scopes stated above. The equality classification and extensions beyond three states remain open. The four-slot escape audit remains unfinished under issue #19212; this does not alter the kernel-checked mathematical statements.
