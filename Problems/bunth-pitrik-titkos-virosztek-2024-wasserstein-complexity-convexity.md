---
slug: bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity
bibkey: bunthpitriktitkosvirosztek2024wasserstein
doi: 10.1103/PhysRevA.110.022211
url: https://arxiv.org/abs/2402.13150v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result
---

# A qubit dephasing midpoint refutes convexity of Wasserstein complexity

## Problem

G. Bunth, J. Pitrik, T. Titkos and D. Virosztek, *On the metric property of quantum Wasserstein divergences*, Phys. Rev. A **110** (2024), 022211, [arXiv:2402.13150v4](https://arxiv.org/abs/2402.13150v4), Section 5.1, asks:

> We note that whether the Wasserstein complexity (37) is convex or not is an open question.

For a finite Hermitian observable family $\mathcal A$, the complexity is $C_W(\Phi)=\max_\rho d_{\mathcal A}(\rho,\Phi(\rho))$. The density matrices are positive semidefinite and have trace one. The couplings have marginals $\omega$ and $\rho^T$, and the quadratic cost and divergence are those of equations (eq:2-Wass-quant-def) and (eq:mod-qw-dist-def). [The literature note](../Library/QuantumChannels/bunthpitriktitkosvirosztek2024wasserstein.md) gives the definitions and locators. [Preregistration #15149](https://github.com/the-omega-institute/trureturing/issues/15149) specifies the universal convexity statement, its conventions and the qubit counterexample.

## Motivation

`D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result` refutes the universal channel-convexity assertion for the Pauli observables on $\mathbb C^2$. Its supporting module supplies coupling optimization, unitary covariance and the exact self cost. The obstruction already occurs between two unitary channels whose midpoint is a unital dephasing channel.

## Gap

The literature check in #15149 covers the arXiv versions, the journal source, a citing-work screen and searches for channel Wasserstein complexity with convexity. No settlement was found in that searched scope; the screen of citing works is search-seat-reported. Results on state divergences and on $W_1$ channel complexity concern different quantities. The self-cost identity is literature-attested: the source's Section 4.1, Proposition 3, equation (35), gives $D^2(\rho,\rho)=4(1-\sqrt{1-|b_\rho|^2})$. For eigenvalues $(1\pm r)/2$ this equals $8-4(\operatorname{tr}\sqrt\rho)^2$. The channel-complexity refutation supplies the settlement, without claiming that self-cost identity as a new literature result.

## Route

Use the Pauli triple $\mathcal A=(X,Y,Z)$, $t=1/4$ and mixture weight $s=1/2$. Define $U_\pm=\sqrt{1-t}I\pm i\sqrt t Z$, $\Phi_\pm=\operatorname{Ad}(U_\pm)$ and $\Psi=(\Phi_++\Phi_-)/2=(1-t)\operatorname{id}+t\operatorname{Ad}(Z)$.

The Pauli cost is $C=8(I_4-P)$ for the normalized Bell projector $P$. A diagonal state's self cost is attained by the vectorized square-root coupling; a principal-minor bound proves optimality. Transport by $V\otimes\bar V$ fixes the Bell vector and preserves the coupling constraints and cost. Spectral reduction gives the self-cost formula for every qubit state. For each endpoint, the vectorization of $U_\pm\sqrt\rho$ gives an admissible coupling and a uniform bound $C_W(\Phi_\pm)\le\sqrt2$. At $\rho=|+\rangle\langle+|$, the pure marginal fixes the coupling, giving cross cost $5$, input self cost $4$, output self cost $4-2\sqrt3$ and divergence $\sqrt{1+\sqrt3}>\sqrt2$.

### Source-faithful Lean conventions

The source's coupling-state condition lives on the tensor-product carrier. `IsDensity` is indexed by `Fin d`, whereas coupling matrices use `Fin d × Fin d`. Stating `pi.PosSemidef ∧ pi.trace = 1` directly on that product index type is the coupling-index Lean elaboration repair; it preserves the source's meaning. The reused `partialTraceRight` and `partialTraceLeft` are the explicit sums over the second and first factor. The dual-factor observable uses `Matrix.transpose`.

The literal $d=0$ case of the preregistered claim is retained. There is no trace-one state in dimension zero, and Mathlib's real supremum of the empty set is zero. Using that convention is a Lean elaboration repair of the literal universal statement; it does not restrict its quantifiers or change the source's meaning in positive dimension. Every witness in the refutation has $d=2$. `CW` is the supremum of the source maximum's values; `CW_bddAbove` proves boundedness. The proof needs the supremum's upper-bound and witness-lower-bound properties, without an extra attainment hypothesis.

## Falsifier

A transcription mismatch in the coupling constraints, transpose, observable cost, self-cost subtraction, complexity or mixture statement would invalidate this settlement. The formal channels are completely positive and trace preserving, the observables are Hermitian, and the mixture weight lies in $[0,1]$. The strict comparison is with both endpoint complexities, not just a computed sample. The exact dephasing complexity is not needed and is not asserted.

## Evidence

The canonical Lean sources are `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.lean` and `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.lean`, with matching Blueprint Scribes. The supporting module's admission basis is `escape-witness (self_cost)`; the settling module's is `open-problem-resolution (#15149; Refuted)`. The frozen owner `NandiMutualPredictabilityLOCCRefutation.hadamard_unitary` supplies the unitary Hadamard fact used by `H_unitary`. Its statement and proof are preserved by publication.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The other new public theorems and the newly public `hadamard_unitary` have unfinished escape audits recorded in [#15443](https://github.com/the-omega-institute/trureturing/issues/15443). No registration whose report decoding fails is delivered. This audit boundary does not assert completed registration.

### Experiment reading

[Experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/10a541e9aacff47302154c721e10ff180fda60aa/docs/reports/bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity): `docs/reports/bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity/check.py` in `the-omega-institute/trureturing-experiments` at commit `10a541e9aacff47302154c721e10ff180fda60aa`. SHA-256: `04787a6acc2c5bccda908bcb90ffd00d928e418e14cebc28bfa5f2d90f9c68db`. Run `python3 check.py` in that entry with NumPy and cvxpy; exit `0`, `bad= 0`. The implementation seat reran the pinned script with NumPy 2.5.4 and cvxpy 1.9.3.

The script uses random seed $3$, checks the self-cost formula against the SDP on $20$ random qubit states with tolerance $10^{-5}$, and samples both endpoint signs on $300$ random states and three specified states at $t=1/4$. The largest sampled squared divergence is $1.654607$, below the bound $8t=2$. At the plus state it computes the midpoint squared divergence $2.732051$, agreeing with $1+\sqrt3$ to the script's tolerance $10^{-4}$. It checks those comparisons and reports `bad= 0`. The solver reports possible numerical inaccuracy. These are approximate finite-sample readings, not an exact optimizer, a proof of a uniform bound, or a sweep over $t$.

The published helpers `trace_sqrt_sq_le_two` and `pure_diag_coupling` are consumed by the purify-and-clone refutation. Their four-slot escape audit is unfinished under [#19490](https://github.com/the-omega-institute/trureturing/issues/19490).

## Triage

Tier 1 published open question; settlement `Refuted`, witnessed by `WassersteinComplexityNonconvex.result`. Each claim below has one evidence kind.

### What the settlement shows

| Claim | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| At $t=1/4$, the midpoint cross cost is $5$, and the self costs are $4$ and $4-2\sqrt3$. | Proved; kernel-checked. | `WassersteinComplexityNonconvex.midpoint_cross`, `midpoint_self_input`, `midpoint_self_output` (private declarations). |
| Each endpoint has complexity at most $\sqrt2=\sqrt{8t}$. | Proved; kernel-checked. | `WassersteinComplexityNonconvex.phase_pure_coupling`, `endpoint_bound`, `CW_endpoint_bound` (private declarations) use the vectorized-square-root coupling. |
| The midpoint has complexity at least $\sqrt{1+\sqrt3}>\sqrt2$ and violates convexity. | Proved; kernel-checked. | `WassersteinComplexityNonconvex.midpoint_divergence`, `CW_midpoint_bound` and public `result`. This is a lower bound, not the exact midpoint complexity. |
| For every qubit density state $\sigma$, $D^2(\sigma,\sigma)=8-4(\operatorname{tr}\sqrt\sigma)^2$. | Proved; kernel-checked. | `QubitWassersteinCouplings.self_cost`; literature attestation is Proposition 3, equation (35), as described in Gap. |
| For every $0<t<1/2$, the cross cost at the plus state is $4+4t$, the input self cost is $4$, and the output self cost is $4-8\sqrt{t(1-t)}$. | Proved in prose. | The derivation below gives the pure-marginal and spectral computations; Lean specializes $t=1/4$. |
| For every $0<t<1/2$, $C_W(\Psi_t)^2\ge4t+4\sqrt{t(1-t)}>8t\ge C_W(\Phi_\pm)^2$. | Proved in prose. | The derivation below supplies the uniform endpoint bound and strict inequality. No all-$t$ Lean declaration is claimed. |
| The self-cost sample comparisons, the sampled endpoint maximum and the midpoint squared divergence at $t=1/4$. | Computed. | Exactly the pinned experiment entry and tested scope in Evidence; `python3 check.py`, exit $0$, the stated SHA-256. |
| Quasi-convexity and convexity restricted to unital channels. | Refuted; proved in prose. | The same midpoint exceeds both endpoints. $U_\pm$ are unitary, so their conjugations and their midpoint preserve $I$. Thus both proposed restrictions already fail for this witness. These items are settled by the witness rather than left open. |
| The exact value of $C_W(\Psi_t)$ for the dephasing family. | Open. | The argument gives a lower bound; the experiment computes one state's divergence and samples endpoint channels, not the supremum for $\Psi_t$. |
| Consequences for the source's metric results. | Proved in prose; scope statement. | The counterexample concerns the channel supremum and refutes no metric theorem on the state divergence. Those theorems do not acquire a convexity hypothesis from this settlement. |

### Family derivation

For $0<t<1/2$, let $S=\sqrt\rho$. Positivity gives real diagonal entries and $\operatorname{tr}S\ge0$. The vectorized $U_\pm S$ is a coupling of $\rho$ and $\Phi_\pm(\rho)$, and its Pauli cross cost is

$$8-4|\operatorname{tr}(U_\pm S)|^2.$$

Because $\operatorname{tr}(ZS)$ is real,

$$|\operatorname{tr}(U_\pm S)|^2=(1-t)(\operatorname{tr}S)^2+t(\operatorname{tr}ZS)^2\ge(1-t)(\operatorname{tr}S)^2.$$

Unitary covariance equates both self costs to $8-4(\operatorname{tr}S)^2$. Subtraction and $(\sqrt a+\sqrt b)^2\le2(a+b)=2$ for the two eigenvalues give $d_{\mathcal A}(\rho,\Phi_\pm(\rho))^2\le4t(\operatorname{tr}S)^2\le8t$, and hence the same bound for each endpoint complexity squared.

At $\rho_+=|+\rangle\langle+|$, the pure input marginal forces the product coupling. The output is $(1-t)\rho_++t\rho_-$ with eigenvalues $1-t,t$. The Pauli cost identity gives $D^2(\rho_+,\Psi_t(\rho_+))=4+4t$. The self costs are $4$ and

$$8-4(\sqrt{1-t}+\sqrt t)^2=4-8\sqrt{t(1-t)}.$$

The divergence squared at that state is therefore $4t+4\sqrt{t(1-t)}$, which lower-bounds $C_W(\Psi_t)^2$. Since $t(1-t)>t^2$ and $t>0$, this lower bound is strictly greater than $8t$. Mixing lowers the output self cost from the endpoint value $4$ while raising the cross cost. The endpoint bound and the self-cost and covariance identities survive; quasi-convexity and a restriction to unital channels do not.

## ASSUMED-UNVERIFIED

The literature screen establishes only `not-found-in-searched-scope`; exhaustive literature completeness and originality are unverified. The all-$t$ family is proved in prose, not a kernel-checked all-$t$ theorem. Exact dephasing complexity remains open. Escape audit registration remains unfinished under #15443.
