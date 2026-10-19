---
slug: rana-parashar-lewenstein-2016-l1-relative-entropy-coherence
bibkey: rana2016coherence
doi: 10.1103/PhysRevA.93.012110
url: https://arxiv.org/abs/1511.01854v2
triage: theorem
motivation_gids:
  - D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result
---

# Relative entropy coherence is bounded by l1 coherence

## Problem

S. Rana, P. Parashar and M. Lewenstein, *Trace-distance measure of coherence*,
Phys. Rev. A 93, 012110, arXiv:1511.01854v2, Section III.2, Conjecture 7:

> Conjecture 7. For all states ρ, C_{l1}(ρ) ≥ C_r(ρ).

The resolution is **Proved** for every finite dimension and every complex density
matrix, including singular states. [Preregistration #16965](https://github.com/the-omega-institute/trureturing/issues/16965)
fixes the conventions. [The source note](../Library/Divergence/rana2016coherence.md)
locates the conjecture and the definitions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every finite-dimensional state | `claim` quantifies over every natural `n` and every complex matrix on `Fin n`; `IsState` is positive semidefiniteness and trace one | No invertibility or rank hypothesis. In dimension zero the state premise is impossible. |
| Section II, Eq. (3b), off-diagonal absolute-value sum | `D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence` | The complex norm gives the absolute value; both indices range over the full basis. |
| Section III after Eq. (13), base-two entropy | `vonNeumann2` | Negative real trace of continuous functional calculus for $x\log_2x$, with its value zero at zero. |
| $C_r(\rho)=S_2(\Delta\rho)-S_2(\rho)$ | `coherenceRel` | The diagonal map retains exactly the diagonal entries. |
| $C_{l1}(\rho)\ge C_r(\rho)$ | `claim`, proved by `result` | Literal preregistered inequality. |

`IsState` and `vonNeumann2` have the unchanged defining bodies shared with
`QuantumTriangularJensenShannonRefutation`; the latter imports their general owner.
The claim uses the frozen `D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence`
for $\sum_{i\ne j}|\rho_{ij}|$; exchanging the branches of its diagonal test
gives the same off-diagonal sum term by term. The state and entropy definitions
retain the source conventions.

## Motivation

The comparison bounds the entropy gained by complete dephasing using only the
absolute values of off-diagonal entries. A sequence of binary coordinate
pinchings gives a stronger bound using the Euclidean norms of the upper rows.

## Gap

The supplied literature screen reports relevant-section checks of INSPIRE,
Semantic Scholar and OpenAlex citation graphs, 145 selected arXiv papers and
130 PDF text screens. The graphs have different scopes and overlapping records;
their counts are not added. The source, Rana–Parashar–Winter–Lewenstein
arXiv:1612.09234v3 (including Appendix F), Hu et al. arXiv:1703.01852 and
Zhang–Guo–Cao, Entropy 22, 297 retain the general bit-entropy comparison as
unsettled in the inspected statements. No general proof or counterexample was
found in that searched scope. Those screen counts and bounded search results
are supplied research-seat readings, not a new exhaustive screen.

The logarithmic estimate $C_r\le\log_2(1+C_{l1})$ does not imply the desired
comparison throughout $0<C_{l1}<1$. Literature completeness is
`ASSUMED-UNVERIFIED`. Full-text access gaps include DOI
10.1007/s10773-019-04011-z, 10.1016/j.physleta.2024.130106,
10.1142/S0219749926400010 and the published version of 10.1063/5.0209604;
its arXiv preprint 2301.12295v2 was included in the supplied screen.

## Route

[Audenaert's source note](../Library/Divergence/audenaert2014skew.md) locates
Theorems 8, 9 and 14 of *Quantum Skew Divergence*. The supporting theorem
`AudenaertBinaryHolevoBound.binaryHolevoBound` proves

$$
S_2((\sigma+\tau)/2)-\frac{S_2(\sigma)+S_2(\tau)}2
\le \frac{\|\sigma-\tau\|_{\rm tr}}2.
$$

Its resolvent integral and dominated differentiation give the differential skew
estimate; integration gives the uniform-positive-state bound. The normalization
$(\rho+\epsilon I)/(1+n\epsilon)$ and continuity of $x\log x$ extend it to
singular states.

For an orthogonal projection $P$, put $Q=I-P$ and $Z=2P-I$. Then
$P\rho P+Q\rho Q=(\rho+Z\rho Z)/2$. Unitary invariance and the binary Holevo
bound give an entropy increase at most $2\|P\rho Q\|_{\rm tr}$.
Coordinate pinching makes this off-diagonal block a rank-one row. Telescoping
and the Euclidean-to-l1 estimate give the result.
The private lemmas `pinch_entropy_le`, `coordinate_pinch_entropy_le`,
`entropy_telescope` and `row_bound_le_coherenceL1` are used by
`claim_of_binaryHolevo`; the public `result` supplies the proved binary bound.
The left/right trace-norm identities retain the Physlib attribution and license
in [the Meiburg note](../Library/QuantumStates/meiburg2025svd.md).

## Falsifier

A finite-dimensional positive semidefinite unit-trace matrix satisfying
$C_r(\rho)>C_{l1}(\rho)$ would contradict the conclusion. Rank-deficient and
near-diagonal states are included in both the theorem and the experiment's
stated finite sample. Numerical agreement alone is not the proof.

## Evidence

The settling declaration is
`D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result`; its supporting theorem
is `D5/S3/Divergence/AudenaertBinaryHolevoBound.binaryHolevoBound`.
Their compiled axiom closures are contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished for both public results and the newly published
owner declarations, including `FinitePathDynamics.sum_succ_sub_castSucc`.
[Issue #17312](https://github.com/the-omega-institute/trureturing/issues/17312)
names the targets, their declaration identities, and missing typed reconstruction,
enrolled readout and sensitivity evidence. No `declared_validated` registration
is claimed without its scoped-report reading.

### Numerical experiment

[Experiment directory at commit c0ec5da693d21aa2fc1c396ff0db721921175231](https://github.com/the-omega-institute/trureturing-experiments/tree/c0ec5da693d21aa2fc1c396ff0db721921175231/docs/reports/rana-parashar-lewenstein-2016-l1-relative-entropy-coherence).
The program is `check.py`, SHA-256
`e62db870ed83bfc269f3615451296d7da3c1398ac053edb95701bad40ef4075a`.
Executing `python3 check.py` on those pinned bytes exits 0 and reports `ALL_OK`.
It runs 40,000 iterations in dimensions $2$ through $8$. Each iteration
generates a base state from a Gaussian matrix with a rank parameter from $1$
through the chosen dimension, and a paired state for the binary comparison.
The base state is mixed with its diagonal using a scale in
$\{1,0.5,0.2,0.05,0.01\}$; this includes rank-deficient and near-diagonal
inputs, and the mixing can increase the rank. The largest signed violations are
$-3.610\cdot10^{-4}$ (binary Holevo), $-1.241\cdot10^{-9}$ (one pinching),
$-2.577\cdot10^{-7}$ (entropy versus row bound), and
$3.331\cdot10^{-16}$ (row bound versus l1, floating-point rounding).
The computation checks that sample only; it does not establish a universal bound.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved; kernel-checked `binaryHolevoBound`, private `pinch_entropy_le`, `pinching_row_traceNorm`, `coordinate_pinch_entropy_le` | One pinching costs at most twice the trace norm of the off-diagonal block. Coordinate pinching turns it into twice an upper-row Euclidean norm. |
| Strength | Proved in prose below, using kernel-checked `coordinate_pinch_entropy_le`, `entropy_telescope` and `row_bound_le_coherenceL1` | $C_r(\rho)\le 2\sum_k(\sum_{j>k}\lvert\rho_{kj}\rvert^2)^{1/2}\le C_{l1}(\rho)$ for every finite-dimensional state, including singular states. The row strengthening is an intermediate estimate in the compiled proof, not a separate public theorem. |
| Bu–Xiong consequence | Proved in prose below; original definitions read in arXiv:1604.06524v2, Eq. (4) and conclusion | Ordinary cohering powers satisfy $\mathcal C_r(\Phi)\le\mathcal C_{l1}(\Phi)$ for every finite-dimensional quantum operation. No generalized-power or de-cohering-power comparison is asserted. |
| Sharp row constant | Open | No optimality theorem or matching family is delivered. |
| Infinite-dimensional extension | Open | No infinite-dimensional entropy, convergence or summability theorem is delivered. |
| Experiment | Computed; the pinned program, command, exit code and SHA-256 in Evidence | The 40,000 iterations in dimensions $2$ through $8$ satisfy the four comparisons to the stated numerical precision. |
| Literature | Literature reading; supplied citation and PDF screens in Gap | No prior general settlement found in the searched scope; completeness `ASSUMED-UNVERIFIED`. |

For the row estimate, write $\rho^{(m)}=\operatorname{partialPinch}(m,\rho)$
and $s_m=S_2(\rho^{(m)})$, for $0\le m\le n$.
The identities `partialPinch_zero` and `partialPinch_final` give
$s_0=S_2(\rho)$ and $s_n=S_2(\Delta\rho)$.
For each $0\le k<n$, `coordinate_pinch_entropy_le` gives

$$
s_{k+1}-s_k\le 2\left(\sum_{j>k}|\rho_{kj}|^2\right)^{1/2}.
$$

Summing these inequalities and telescoping the left side, as in
`entropy_telescope`, proves the first row bound. The second inequality is
`row_bound_le_coherenceL1`. This derivation gives the full estimate; the delivered
Lean conclusion `result` states $C_r(\rho)\le C_{l1}(\rho)$.

Bu and Xiong, *A note on cohering power and de-cohering power*,
Quantum Information and Computation 17, 1206–1220,
[DOI 10.26421/QIC17.13-14-8](https://doi.org/10.26421/QIC17.13-14-8),
[arXiv:1604.06524v2](https://arxiv.org/abs/1604.06524v2), Eq. (4), define
$\mathcal C_X(\Phi)=\max_{\delta\in\mathcal I} C_X(\Phi(\delta))$.
For each incoherent input $\delta$, the output is a density matrix, so the proved
state inequality gives $C_r(\Phi(\delta))\le C_{l1}(\Phi(\delta))$.
Taking the maxima over the same input set proves the stated ordinary-power
comparison. Their conclusion asks for the relation between the two powers.
This corollary does not compare the differences used in generalized powers or
de-cohering powers: pointwise order of measures does not order their differences.
It is an application proved in prose, outside this delivery's Lean declarations.

The argument uses only finite-dimensional density-matrix hypotheses and does not
assume full rank. The source's earlier bounds and special cases remain valid;
where only Conjecture 7 is needed, `result` supplies that inequality. No other
conjecture or stronger infinite-dimensional assertion is claimed settled.

## ASSUMED-UNVERIFIED

- Exhaustiveness and priority of the literature search, including the stated
  full-text access gaps.
- Escape registration is unfinished under issue #17312; successful Lean
  compilation and freezing do not establish its four-slot reconstruction.
- The sharp row constant and infinite-dimensional extension remain open.
