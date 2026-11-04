---
slug: song-kwon-scarani-2025-steady-prior-reversibility
bibkey: song2025tabletop
doi: 10.1088/2058-9565/aea92d
url: https://arxiv.org/abs/2510.26895v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result
---

# A steady prior does not imply tabletop time reversibility

## Problem

M. Song, H. Kwon and V. Scarani, *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*, arXiv:2510.26895v1, Section V, question 2, page 9:

> In all of the examples we considered, a dynamics appears to be tabletop time-reversible whenever a prior state is a steady state. We do not have a proof that this is true in general, and leave it for a future investigation.

The [source note](../Library/Divergence/song2025tabletop.md) gives the definitions and locators. [Preregistration #20652](https://github.com/the-omega-institute/trureturing/issues/20652) specifies the finite-matrix statement. The universal assertion, including positive definite steady priors, is **Refuted** by `D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (1), forward dilation | `channel` | The environmental partial trace of $U(X\otimes\xi)U^\dagger$, with system-first product indices |
| Hilbert–Schmidt adjoint used in Definition 1 | `channelAdjoint` | The environmental partial trace of $U^\dagger(Y\otimes I_E)U(I_S\otimes\xi)$ |
| Definition 1, equation (2), Petz recovery | `petz` | $\sqrt\gamma\,N^\dagger(N(\gamma)^{-1/2}X N(\gamma)^{-1/2})\sqrt\gamma$; matrix inverse and `CFC.sqrt` |
| Definition 2, equation (3), same interaction | `tabletopReverse` | $\operatorname{Tr}_E[U^\dagger(X\otimes\eta)U]$; $U$ is fixed |
| Definition 2, equation (4), allowed environment | `IsTTR` | A positive semidefinite trace-one $\eta$ whose reverse equals the Petz map on every complex matrix $X$ |
| Finite system and environment | The types `S`, `E` and their `Fintype`, `DecidableEq` instances in `claim` | Matrix indices, with no dimension restriction on the universal claim |
| Physical forward dynamics | Unitarity of `U`, positivity and trace one of `xi` in `claim` | The source's unitary dilation and environmental density state |
| Full-rank prior | Positive definiteness and trace one of `gamma` in `claim` | A restriction of the source's priors; a refutation in this subclass refutes the general assertion |
| Steady state | `channel U xi gamma = gamma` in `claim` | Exact stationarity |
| TTR whenever steady | `IsTTR U xi gamma` conclusion of `claim` | Same interaction, arbitrary reverse environmental density matrix |
| Negative answer | `result` | Negation of the complete universal claim |

The public definitions keep the preregistered expressions. The proof reuses `PartialTraceMutualInformation.partialTraceRight`, `NMLWMeasuredFidelitySeparation.sqrt_diagonal`, and the public Fuchs qutrit-state positivity and trace lemmas. The environmental matrix is literal witness data.

## Motivation

Stationarity is a constraint on the forward channel and prior. Tabletop reversibility also constrains which reverse channels the same interaction can realize by changing the environment. The settling GID is `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result`; its admission basis is `open-problem-resolution (#20652; Refuted)`.

## Gap

The source's stationary examples satisfy additional structural conditions. They do not establish that stationarity alone permits the same interaction to implement the Petz map. Characterizing the additional conditions and formalizing the continuous Hamiltonian family remain open.

## Route

Take $S=E=\{0,1,2\}$, $\xi=\operatorname{diag}(1/2,1/3,1/6)$ and $\gamma=\operatorname{diag}(17/44,13/44,14/44)$. The interaction exchanges $(0,0)$ with $(1,1)$, $(1,0)$ with $(2,2)$, and $(2,0)$ with $(0,2)$, with amplitude $-i$, and fixes $(0,1),(1,2),(2,1)$.

For every complex environmental matrix $\eta$, the reverse output population at $1$ on input $|0\rangle\langle0|$ and at $2$ on input $|1\rangle\langle1|$ equals the same entry $\eta_{00}$. The Petz populations on those inputs are respectively $13/51$ and $7/39$. Their inequality excludes every environmental matrix, hence every environmental density matrix.

## Falsifier

The claimed refutation would fail if the stated interaction were nonunitary, either state failed its positivity or normalization condition, the prior were not stationary, or the two exact Petz entries agreed. These obligations are checked by the module's private lemmas and used in `result`. A different interaction implementing the Petz map does not refute this result, which fixes the original interaction.

## Evidence

### Kernel-checked instance

The module `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.lean` proves `result : ¬ claim`. Its private lemmas `U_unitary`, `xi_psd`, `xi_trace`, `gamma_pd`, `gamma_trace`, and `stationary` supply a physical stationary instance. `tabletop_10`, `tabletop_21`, `petz_10`, `petz_21`, and `not_ttr` supply the two-entry contradiction. The proof shape is `bind-only`: finite matrix normalization and existing diagonal square-root and state owners. Admission uses the external named open-problem resolution, not an escape witness.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Numerical experiment

The immutable experiment directory is [song-kwon-scarani-2025-steady-prior-reversibility](https://github.com/the-omega-institute/trureturing-experiments/tree/2f862f6a6250e3487932fb4a2b41243a41d57860/docs/reports/song-kwon-scarani-2025-steady-prior-reversibility). The file is `check.py`, SHA-256 `82b42509dcab4625b08ced9ce46a2cbee2a93850f3892c0e1dc8ce4e4d1a5ce8`. The command `python3 /Users/auric/.sshx/7eaa4d24e8a5c2989779abf4/attempt-1/experiment-check.py`, on the extracted immutable file, exits 0 and reports `ALL_CHECKS_OK`. The script uses NumPy and seed 20261023.

| Tested scope | Computed reading |
| --- | --- |
| Source Example 1, the script's unital dilation with maximally mixed environment | Steady-state residual $3.8\times10^{-16}$; TTR fit residual $2.0\times10^{-15}$ |
| Source Example 2, controlled-X with the script's diagonal states | Steady-state residual $5.6\times10^{-17}$; TTR fit residual $5.0\times10^{-16}$ |
| Fifty equally spaced times from $\pi/100$ to $\pi/2$, inclusive | Maximum stationarity residual $2.6\times10^{-16}$; minimum TTR fit residual $2.624\times10^{-4}$ |
| The same family at $t=\pi/2$ | TTR fit residual $0.3819$; maximum error in the exact rational Petz population matrix $2.2\times10^{-16}$ |
| Two hundred accepted Gaussian-QR unitary samples each for $(d_S,d_E)=(2,2),(2,3),(3,2)$, with the script's full-rank environmental states and stationary-prior cutoff | Minimum TTR fit residuals $0.0385$, $0.0564$, $0.1565$; maximum stationarity residuals $1.5\times10^{-15}$, $7.8\times10^{-16}$, $1.5\times10^{-15}$ |

The fits range over all complex environmental matrices. These finite floating-point samples are numerical evidence; they do not establish a uniform statement about time or random dilations.

## Triage

### What the settlement shows

- **Settlement — proved in Lean:** `result` refutes the literal binding claim using the single interaction at $t=\pi/2$. No continuous-family theorem is asserted in Lean.
- **Mechanism — proved in Lean:** `tabletop_10` and `tabletop_21` force both reverse entries to equal $\eta_{00}$ for every environmental matrix. `petz_10` and `petz_21` compute $13/51$ and $7/39$. `not_ttr` derives the contradiction; `stationary` shows that stationarity does not prevent it.
- **Scope — proved in Lean for the explicit instance; computed for the specified finite samples:** the kernel result is the fixed qutrit witness. The experiment entry supplies exactly fifty time samples and two hundred accepted samples in each of three dimension pairs. An all-times or generic-dilation theorem is open.
- **Surviving source results — literature reading:** Example 1 assumes a unital channel with maximally mixed environment; Example 2 specifies controlled-X and diagonal states. The counterexample does not contradict these additional-hypothesis results. The experiment entry checks one instance of each; it does not prove their universal forms.
- **Structural characterization — open:** stationarity alone is insufficient; necessary and sufficient additional conditions for fixed-dilation TTR are not supplied.
- **Full continuous family — open:** formalizing stationarity and failure for all relevant values of $t$ remains open. The finite time grid is only a computation.

### Other source results and literature status

No other source theorem is invalidated: the refutation addresses the general assertion in question 2, while the cited positive examples retain their hypotheses. The literature screen recorded in #20652 distinguishes nonstationary-prior counterexamples (Aw–Zaw–Balanzó-Juandó–Scarani, arXiv:2308.13909v2, Appendix B), construction of a different reversible dilation (Chen–Hu, arXiv:2608.11702v1), and particular photonic or Gaussian-loss families (arXiv:2606.12020v1 and arXiv:2511.05941v2). Those are literature readings recorded in the preregistration, not additional Lean theorems here.

## ASSUMED-UNVERIFIED

- Completeness of the literature screen recorded in #20652.
- Whether the journal version at DOI 10.1088/2058-9565/aea92d preserves question 2 unchanged; the quoted source is arXiv:2510.26895v1.
- Numerical extrapolation beyond the experiment's stated finite sample set.
