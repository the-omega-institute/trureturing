---
slug: jones-aloy-entropy
bibkey: jones2026speedlimits
doi: 10.1103/bnrq-sp5w
url: https://arxiv.org/abs/2506.14526v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/JonesAloyEntropyConstancy.result
---

# Entropy constancy on fixed-difference correlation lines is false

## Problem

Caroline L. Jones, Albert Aloy, Gerard Higgins and Markus P. Müller, *Certified randomness from quantum speed limits*, PRX Quantum 7, 010349, arXiv:2506.14526v3, conjecture immediately after Appendix E(ii), Lemma 3 (journal Lemma E3):

> Indeed, we conjecture – and the numerics suggest – that $H^\star$ is constant on those lines, i.e. that we have equality in Lemma 3. However, we have not managed to prove this.

The lines have fixed $C_0-C_1$ in the characterized quantum correlation domain. [Preregistration #23268](https://github.com/the-omega-institute/trureturing/issues/23268) fixes the source, conventions and settlement criterion. The [source note](../Library/Entropy/jones2026speedlimits.md) supplies the locators. Settlement: **Refuted**, by `D5.S3.Quantum.JonesAloyEntropyConstancy.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $\Delta t=\hbar=1$; Eq. (9) uses cosine below $\pi/2$, zero above | `gamma` | Literal piecewise expression; labels have no upper cap. |
| Eq. (8) has two separate products of square roots | `fidelityExpression` | Both products and their factor $1/2$ are retained. |
| Correlations lie in $[-1,1]^2$ and satisfy the overlap inequality | `quantumSet` | All four coordinate inequalities and the overlap condition. |
| $p(x)=1/2$ and binary entropy in bits | `entropy` | Reuses `CloningMachine.binaryEntropyBits` at the two affine coordinates; the coordinate map is inlined. |
| Arbitrarily many finite hidden variables, with probabilities, correlations and energy labels | `Ensemble n` and quantification over every $n\in\mathbb N$ in `entropyValues` | No fixed ensemble-size bound. |
| Eq. (27): probability normalization, nonnegative weights and energies, coordinate means, exact mean energy, and branch domain membership | `Feasible` | All seven conjuncts are retained. |
| Minimize the weighted objective | `entropyValues` and `IsSourceRoof` | `IsLeast` specifies attainment and the lower-bound property. |
| Equality with the center of each fixed-difference line for $0\le E\le\pi/2$ | `claim` | The center's literal coordinate expression is inlined. |
| The source uses a minimum-valued function | The existence conjunct of `claim` | Explicit existence prevents a vacuous universal assertion about nonexistent roofs; the refutation does not independently establish global attainment. |
| Refute the assertion under these conventions | `result` | Negation of the complete `claim`; no additional theorem hypothesis. |

## Motivation

The midpoint inequality in Lemma E3 supplies lower bounds along the entire line. Constancy would upgrade that inequality to an exact evaluation. The settlement separates those two assertions on a uniform parameter interval. It uses the source's characterized correlation domain and exact mean-energy optimization; physical operator realizations are outside the Lean statement.

## Gap

Symmetry and convex averaging compare the midpoint with the boundary but do not force equality. An extremal first coordinate constrains every positive-weight branch of a boundary ensemble. Its combination with a strict supporting tangent and exact mean energy forces rigidity that an ensemble for the midpoint need not share.

## Route

Write $b$ for entropy in bits. For $24/25\le s<1$, put

$$E=\arcsin(s),\qquad B=(1,1-2s^2),\qquad M=(s^2,-s^2).$$

The private theorem `boundary_objective` proves that every feasible ensemble at $(B,E)$ has objective $b(s^2)/2$. The private theorems `midpoint_feasible` and `midpoint_objective` construct a three-branch ensemble at $(M,E)$ with objective $s\,b((1+s)/2)$. Its correlations are $(s,-s),(1,1),(-1,-1)$, with weights $s,(1-s)/2,(1-s)/2$ and common energy $E$.

The private theorem `entropy_gap` gives

$$s\,b((1+s)/2)+7((1-s)/2)^2<b(s^2)/2.$$

Thus `roof_separation` proves, for every `HStar` satisfying `IsSourceRoof`,

$$H^\star(M,E)+7((1-s)/2)^2<H^\star(B,E).$$

The public `result` specializes to $s=24/25$ and contradicts the asserted equality. These private declarations belong to namespace `D5.S3.Quantum.JonesAloyEntropyConstancy` and are consumed by the settling proof.

## Falsifier

The binding formal target is the complete `claim`, including its existence conjunct and its universal equality. The public theorem proves its negation. A roof-independent proof of global minimum attainment, an interior extension or an operator realization is not asserted by this result.

## Evidence

Kernel evidence: `D5.S3.Quantum.JonesAloyEntropyConstancy.result`, with frozen membership in `Golden/Frozen/state/D5/S3/Quantum/JonesAloyEntropyConstancy.lean.json`. The only direct D5 import is `D5.S3.Quantum.CloningMachine`; the entropy expression consumes its `binaryEntropyBits` definition.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). [Related audit issue #25630](https://github.com/the-omega-institute/trureturing/issues/25630) concerns registration of the complete negated roof proposition; this delivery makes no `declared_validated` registration claim and adds no Reg module.

Independent computation: [experiment directory at immutable revision ccb00b5a04747b370cd920d6e2b04a8ac5d30fbe](https://github.com/the-omega-institute/trureturing-experiments/tree/ccb00b5a04747b370cd920d6e2b04a8ac5d30fbe/docs/reports/jones-aloy-entropy-constancy). The program is `docs/reports/jones-aloy-entropy-constancy/check.py`; SHA-256 `51ccb46c16a399ee61618021c9af1656d48d2dd35037fb352a72c7e32d85bc35`. Its pinned bytes were rerun with `python3 /Users/auric/.sshx/ef8b47e0b02ad76562ae0d2e/attempt-1/experiment-check.py`, exit 0, ending in `ALL_CHECKS_OK`. It checks symbolic reflection and midpoint identities, the ensemble's exact means and tangent algebra, a rational logarithm enclosure at $s=24/25$, and the proposed Pauli/interior-effect algebra. It gives the nats gap greater than $4330451/100000000$. For the proposed interior effects it checks trace one and determinant $c^2t(2-t)/4>0$ for $0<t<1$, where $c^2=1-s^2$. These are computations, not Lean verification of physical realization or a proof checker for compact roofs.

## Triage

### What the settlement shows

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Mechanism: an extremal coordinate and exact mean energy force boundary rigidity; the midpoint admits a cheaper hidden-variable ensemble. | proved | Kernel-checked private `boundary_objective`, `midpoint_feasible`, `midpoint_objective` and `roof_separation` on the public `result`'s dependency path. |
| Extension: the full interval $24/25\le s<1$ has roof gap greater than $7((1-s)/2)^2$ under `IsSourceRoof`. | proved | Kernel-checked private `roof_separation`; its roof hypothesis is retained. The entropy unit is bits. |
| At $s=24/25$, $B=(1,-527/625)$ and $M=(576/625,-576/625)$, with objective gap greater than $4330451/100000000$ nats. | computed | The pinned experiment in Evidence, command exit 0 and SHA-256 as given there. This exact rational nats enclosure is not a separate Lean theorem. |
| Proposed Pauli/interior-effect algebra and positivity formulas. | computed | The pinned experiment in Evidence, command exit 0 and SHA-256 as given there; symbolic formulas on $0<t<1$. Physical realization is not Lean-verified. |
| Interior persistence via compact-roof lower semicontinuity. | open | Requires an independent compactness/lower-semicontinuity argument and its formalization; not needed for the closed refutation. |
| Global attained-minimum existence independently of `claim`, and complete equality-fibre classification. | open | Neither follows from negating the conjunction in `claim`; neither is proved in this module. |
| Source symmetry, midpoint lower bound, certified lower bounds and classical-region constancy. | open | They remain compatible with this refutation; their independent formalization is outside this delivery. The refutation invalidates the universal line-constancy assertion. The source's midpoint inequality remains compatible with it. |

The witness exposes a boundary-ensemble restriction absent from the midpoint's feasible set. Equality may still occur on particular lines or regions; the complete classification is open. Source results that use only symmetry or the midpoint lower bound retain their stated logical independence from the rejected equality. No separate downstream theorem is claimed invalid without a dependency argument.

Literature status: the preregistration's source and literature screen covers the explicit conjecture, related mean-energy randomness results, convex roofs and the author/citation searches recorded there. It found no direct settlement within that scope. Completeness is `ASSUMED-UNVERIFIED`; this is a recent appendix conjecture, not a claim that all later literature has been exhausted.

## ASSUMED-UNVERIFIED

Literature-search completeness; independent global attainment; compact-roof lower semicontinuity and interior persistence; complete equality-fibre classification; the Lean bridge from characterized correlations to physical operator realizations; and independent formalization of the source's surviving symmetry, midpoint-bound and classical-region statements.
