---
slug: saleem-et-al-2025-noisy-curvature-of-entanglement
bibkey: saleem2025curvature
doi: 10.48550/arXiv.2504.13729
url: https://arxiv.org/abs/2504.13729
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result
---

# Noisy entanglement curvature can exceed quantum Fisher information

## Problem

Z. H. Saleem, A. Shaji, A. M. Babu, D.-W. Luo, Q. Langfitt, T. Yu and S. K. Gray,
*Quantum Fisher Information and the Curvature of Entanglement*, arXiv:2504.13729v4,
Section IV.B, p. 9:

> For the case with decay also there are more general examples we can consider but in all cases we conjecture that CoE ≤ QFI with equality at specific points.

[The source note](../Library/QuantumBounds/saleem2025curvature.md) locates Section II,
Eq. (7), the flip-flop Hamiltonian (21), the open evolution (41), the particular
examples (42)–(43), and Appendix B. [Preregistration #17681](https://github.com/the-omega-institute/trureturing/issues/17681)
fixes the literal conventions and the unrestricted-initial-density-matrix reading.
Section III explicitly introduces losses and mixed probe states after treating pure
lossless evolution. The resolution is **Refuted**.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Two qubits in the computational basis | Matrices indexed by $\mathrm{Fin}\,2\times\mathrm{Fin}\,2$ over $\mathbb C$ | The matrix type is written out, with no forwarding abbreviation. |
| Appendix B: $\sigma_-=(\sigma_x-i\sigma_y)/2=|1\rangle\langle0|$ | Reused `PronkoFredkinNonCyclicAnnihilation.sigmaMinus`; `jump1`, `jump2` | The two jumps are $\sigma_-\otimes I$ and $I\otimes\sigma_-$. |
| Eq. (21), $\eta_{xy}=1$ | `hamiltonian` | Only the $01,10$ and $10,01$ entries equal $g$. |
| Eq. (41), dissipator and commutator | `dissipator`, `generator` | Both jumps have the same positive rate $\kappa$. |
| Parameter-independent initial density matrix | `claim` quantifies over `rhoZero`; reused `StructuredNegativityCoincidenceRefutation.IsDensity` | Positive semidefinite, trace one. |
| Evolution with that initial state | `IsTrajectory` | Initial equality for every real $g$ and entrywise time derivatives for every real $g,t$. |
| Section II, Wootters concurrence | `sigmaYY`, `concurrence` | Characteristic-polynomial roots with multiplicity, real square roots in decreasing order, and $\max(0,\lambda_1-\lambda_2-\lambda_3-\lambda_4)$. |
| Eq. (7), $\mathrm{CoE}=-\partial_g^2C$ | `derivG` and the negative iterated scalar derivative in `claim` | Fixed observation time. |
| Hermitian SLD, $\partial_g\rho=(\rho L+L\rho)/2$ | `IsSLD`; every such matrix $L$ is quantified in `claim` | QFI is $\operatorname{Re}\operatorname{Tr}(\rho L^2)$. |
| Positive damping and observation time | `claim` hypotheses $0<\kappa$, $0<t$ | The witness uses $\kappa=\log2$, $t=1$. |
| Comparison where curvature is smooth | `ContDiffAt` of order two in `claim` | A twice continuously differentiable witness refutes even this restricted comparison. |
| In all cases, CoE $\le$ QFI | `claim`; `result` proves its negation | The witness coupling is $g=\pi/4$. |
| Equality at specific points | No universal equality assertion is added | Failure of the universal inequality refutes the quoted conjunction; the source's particular equality examples are not negated. |

## Motivation

A bound on entanglement curvature by QFI would connect the sharpness of dynamically
generated entanglement to metrological sensitivity. A diagonal, separable mixed probe
already separates these quantities under the source's symmetric amplitude damping.

## Gap

The source versions v1–v4 and the QUANTUM 2026 abstract retain the coincidence theme;
the abstract reports persistence under amplitude damping and gives no violation.
The literature readings supplied with the preregistration and research seat screen
Chatterjee arXiv:2508.12497, Saleem arXiv:2606.05696 and 2606.15484,
Saleem–Saleem arXiv:2606.18415, and Saleem et al. arXiv:2609.31853 without locating
a refutation for evolution (41). These follow-up screens are seat-reported.
The bounded search conclusion is `not-found-in-searched-scope`; literature completeness
is `ASSUMED-UNVERIFIED`. A coincidence established for particular probes does not
supply a universal inequality.

## Route

Take the parameter-independent state
$\rho_0=\operatorname{diag}(1,11,3,1)/16$ and evolve it by (41). At
$\kappa=\log2$, $t=1$, $g_*=\pi/4$, the state is

$$
\rho_* = \frac1{64}
\begin{pmatrix}
1&0&0&0\\
0&15&8i&0\\
0&-8i&15&0\\
0&0&0&33
\end{pmatrix}.
$$

In a neighbourhood of $g_*$ its concurrence is
$C(g)=\sin(2g)/4-\sqrt{33}/32$, so $-C''(g_*)=1$.
The Hermitian SLD $L=\operatorname{diag}(0,-16/15,16/15,0)$ gives
$F_Q=8/15$. Thus the universal inequality would require $1\le8/15$.

## Falsifier

The interpretation would fail if the conjecture excluded mixed initial probes or used
a different lowering convention. Section III's explicit mixed-state scope, Eq. (41)
and Appendix B fix those choices. A nonsmooth concurrence point would not refute the
smooth-point formal claim; `concurrence_smooth` proves the required regularity here.
The pure lossless theorem of Section III.B has different assumptions.

## Evidence

The settling declaration is
`D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result : ¬ claim`.
The consumed private theorems `rho0_density`, `trajectory`, `concurrence_smooth`,
`curvature`, `sld_point` and `qfi_point` establish the initial density matrix, exact
trajectory, regularity, curvature and SLD-QFI used by `result`.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
No other public theorem is introduced.

### Experiment

[The pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/75dbfafee01a748b83764044ebe12042bcdb48e2/docs/reports/saleem-et-al-2025-curvature-of-entanglement-noisy)
contains `check.py`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/saleem-et-al-2025-curvature-of-entanglement-noisy/check.py`;
exit 0; `ALL_OK`; script SHA-256
`205e590442177c267051f09ef129df7f7fead0f3be102714075a1a9dccada488`.
The checked blob belongs to commit `75dbfafee01a748b83764044ebe12042bcdb48e2`.
The exact symbolic checks cover the trajectory, trace, spin-flip polynomial and point
spectrum, concurrence, SLD equation and family QFI/curvature identities.
The numerical checks compare the mixed witness at finite-difference steps
$10^{-3},10^{-4}$, the pure product witness at $10^{-3},3\cdot10^{-4},10^{-4}$,
and the source's $|01\rangle$ formulas at three specified parameter triples.
The zero-damping control samples 3000 random pure states with seed 0, of which 20
pass the script's concurrence and finite-difference stability filters; their maximum
gap is $-12.1389$. This control is not a prevalence test at positive damping.

## Triage

Tier 1; resolution **Refuted**;
`admission_basis: open-problem-resolution (#17681; Refuted)`.
Utility is `kind=certified-instance; basis=refutes`: the instance contradicts the
literal universal claim. Every theorem is classified `bind-only` after expansion;
the external named settlement supplies the admission basis.

### What the settlement shows

1. **Mechanism at the point — kernel-checked.** `concurrence_smooth`, `curvature`,
   `sld_point`, `qfi_point` and `result` prove that smooth CoE is $1$ while QFI is
   $8/15$ at the stated positive-damping point. These statements concern the
   explicit witness, not a uniform family inequality.

2. **Counterfamily — computed identities, with positivity proved in prose.**
   The experiment verifies exactly
   $\mathrm{CoE}=2qt^2$, $F_Q=8qt^2/(8-q)$ and
   $\mathrm{CoE}-F_Q=2qt^2(4-q)/(8-q)$ for the displayed family,
   where $q=e^{-\kappa t}$. For $\kappa,t>0$, $0<q<1$, so all factors in
   this last quotient are positive. The same sign condition makes the positive
   concurrence branch smooth near $g_*=\pi/(4t)$.
   The block explanation is that curvature is linear in the imbalance $\Delta$,
   while QFI is quadratic in $\Delta$ divided by block weight $K$;
   $\mathrm{CoE}/F_Q=K/\Delta=2-q/4$ for $\Delta=1/2$, $K=1-q/8$.
   This is an explanation of the symbolic identities, not an additional Lean theorem.

3. **Pure product probe — computed.** The experiment's stable finite differences
   for $(|00\rangle+|10\rangle)/\sqrt2$ at
   $\kappa=0.3$, $t=3$, $g=2.9$ give gap $3.3708$ and concurrence $0.0505$.
   This supports a noisy pure-state violation numerically; it is not kernel evidence
   for a pure-state refutation or a proof of exact differentiability there.
   **Random pure-state prevalence — open.** The supplied research reading says
   about $7\%$ of sampled pure initial states violate the bound at smooth points.
   The pinned checker does not test that statistic; the population, sample size,
   positive-damping sampling rule and smoothness filter are unverified here.
   The estimate is `ASSUMED-UNVERIFIED`, not a reproduced experimental result.

4. **Consequences — proved in prose from the refutation and source scope.**
   Section III.B's pure lossless theorem cannot be extended to all initial states
   under (41): such an extension would imply `claim`, contradicted by `result`.
   The two noisy examples' coincidence properties remain statements about those
   probes; their validity does not imply an inequality for every probe.
   No lossless theorem or specific noisy coincidence formula is refuted.
   Any subsequent argument using the universal noisy bound needs an additional
   restriction or a different inequality.

5. **Neighbouring questions — open.** Classify initial states for which
   $\mathrm{CoE}\le F_Q$ holds under (41); find a corrected inequality such as
   $\mathrm{CoE}\le c F_Q$ with explicit admissible $c$ or a block-weight term;
   and determine what holds for other noise models. The nearest surviving
   statements are the source's pure lossless theorem and its particular noisy
   examples, each with its own original hypotheses.

6. **Literature — open completeness.** The source versions and conference abstract
   above give the context; the named follow-up screens locate no noisy violation
   in the searched scope. This is a literature reading with completeness
   `ASSUMED-UNVERIFIED`, not a proof that no prior refutation exists.

## ASSUMED-UNVERIFIED

Literature completeness, the reported $7\%$ prevalence and the unformalized pure-state
numerical extension remain unverified. Full-rank and separability properties are not
separate Lean predicates in this module: the initial diagonal entries are positive
and form a convex mixture of computational-basis product projectors, which gives
those properties by an elementary paper argument. The evolved-point eigenvalues
are $1/64,7/64,23/64,33/64$, all positive. The exact family and numerical observations
have the experiment's stated scopes. The kernel settlement is the closed negation
of the preregistered universal claim at one smooth positive-damping witness.
