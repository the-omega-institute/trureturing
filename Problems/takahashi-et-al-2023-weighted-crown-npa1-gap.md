---
slug: takahashi-et-al-2023-weighted-crown-npa1-gap
bibkey: takahashietal2023su2sdp
doi: 10.48550/arXiv.2307.15688
url: https://arxiv.org/abs/2307.15688v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.result
---

# First-level SDP inexactness on the weighted-crown interval

## Problem

J. Takahashi, C. Rayudu, C. Zhou, R. King, K. Thompson and O. Parekh,
*An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*,
arXiv:2307.15688v3, Appendix C.1, leaves the interval
$(n+2)^2/(4(n+1))<x<(n+2)/3$ open for
$H=xh_{ab}+\sum_{j=1}^{n}(h_{aj}+h_{bj})$, with $n\geq3$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $n\geq3$ | `claim` binder `3 ≤ n` | Exact |
| $(n+2)^2/(4(n+1))<x$ | `claim` binder `L n < x` | Exact |
| $x<(n+2)/3$ | `claim` binder `x < U n` | Exact |
| Weighted crown Hamiltonian | `crownH n x` | Exact literal singlet sum |
| First-level SDP value | `npa1Value n x` | Exact real moment supremum |
| Strict inexactness | `result : claim` proves `lambdaMax (crownH n x) < npa1Value n x` | Exact |

The definitions of $\mathcal{Proj}(V,w)$ and $NPA_1$ and the real
level-one equality are recorded in the cited Library note.

## Motivation

The source proves exactness for $x\leq(n+2)^2/(4(n+1))$ and $x\geq n$
and failure for $(n+2)/3<x<n$. The result extends the failure range
to the strict intermediate interval; the joining point $x=U$ remains open.
The formal carrier uses
hubs `none` and `some none`, leaves `some (some i)`, two-element
pair subsets, the real moment matrix, and the literal qubit singlet
Hamiltonian.

## Gap

Appendix C.1 of v3 (9 April 2026) explicitly says that the interval is an
open problem. Preregistration issue #15210 records the source reading,
definitions, moment-matrix route and literature search. That search found
no settlement in its stated scope: the source, cited subsequent works,
related Quantum Max Cut papers, MathDB, Formal Conjectures and repository
search contain no resolution of this interval.

## Route

For $L=(n+2)^2/(4(n+1))$, put
$\delta=x-L$, $q=\delta/(16n)$, $p_0=(n+1)/(2n)$,
$c=(x+L)/(4n)$, $p=p_0-cq$, and $d=(np/2+q/4)/(n-1)$.
The supporting certificate constructs the real level-one moment matrix,
proves symmetry and positive semidefiniteness by centered and
singlet/antisymmetric blocks, and computes
$n+1+\delta^2/(32n)$. The spectral certificate proves
$\lambda_{\max}(H)\leq n+1$ whenever $x\leq1+n/2$. Since
$U<n/2+1$ for $n\geq3$, both apply on the whole open interval.

## Falsifier

A counterexample would be $n\geq3$ and $L<x<U$ for which the constructed
moment matrix is infeasible, its objective is not strictly above $n+1$, or
the Hamiltonian has maximum eigenvalue above $n+1$. Endpoint behavior and
the exact $NPA_1$ value are outside the settled strict-interior statement.

## Evidence

The kernel-checked declarations are
`WeightedCrownSpectralBound.crown_spectral_bound`,
`WeightedCrownMomentCertificate.moment_feasible`,
`WeightedCrownMomentCertificate.constructed_value_gap` and
`WeightedCrownFirstLevelGap.result`. Their axiom closures are contained
in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The settling result addresses the open problem in issue #15210 with
resolution kind Proved.

The experiment entry
[check.py](https://github.com/the-omega-institute/trureturing-experiments/tree/6febb702f761e7ccf925490225ed692e70c522f1/docs/reports/takahashi-et-al-2023-weighted-crown-npa1-gap)
was run with `python3 check.py`, exit 0, script SHA-256
`36a2b02707dc9575ab5824f762994a6a693e61074dfed5665e6d78fa53f5e005`,
and final reading `bad= 0`.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| A real level-one moment matrix is feasible throughout $L<x<U$ and has objective $n+1+(x-L)^2/(32n)$ | proved | Kernel-checked private `WeightedCrownMomentCertificate.moment_feasible` and `WeightedCrownMomentCertificate.moment_objective`, for every $n\geq3$ and $L<x<U$ |
| The Hamiltonian has maximum eigenvalue at most $n+1$, strictly below the first-level value | proved | Kernel-checked `crown_spectral_bound`, `constructed_value_gap` and `result`, for every $n\geq3$ and $L<x<U$ |
| The maximum eigenvalue equals $n+1$ on this interval | literature result | Source Eq. (C2); the delivered Lean statements prove only the upper bound needed for inexactness |
| The source's neighboring ranges give exactness for $x\leq L$ and $x\geq n$, and inexactness for $U<x<n$ | literature result | `Library/QuantumBounds/takahashietal2023su2sdp.md`; together with `result`, the established failure range is $(L,U)\cup(U,n)$ |
| Rational feasibility and spectral readings | computed | Pinned experiment entry above: $n=3,\ldots,10$, five rational interior points per $n$ for constraints and PSD; exact diagonalization at $n=3,4,5$ and three points per $n$; exit 0 and `bad= 0` |
| The exact value of $NPA_1$ on the open interval | open | The construction gives a strict lower bound, not an exact supremum |
| The point $x=U$, needed to join the two failure ranges into $(L,n)$ | open | Neither the new strict-interior theorem nor the source's strict $U<x<n$ statement includes it |
| Behavior of the construction at the interval endpoints | open | The strict-interior proof does not extend the certificate to either endpoint; source exactness at $x=L$ remains a literature result |

The four-slot escape audit is unfinished under
[issue #15610](https://github.com/the-omega-institute/trureturing/issues/15610).
The concrete missing evidence is actual observational dependence for the
registration readouts at $n=3,x=0$ and $n=3,x=8$, together with
source-selection and report-decoding evidence for the hub/leaf
registrations. The issue names all five public audit targets; no completed
registration is claimed.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish worldwide priority or
absence of every independent solution. The experiment supplies finite
rational and numerical readings only. The source's neighboring-range
claims are literature evidence, while the strict open-interval result is
kernel-checked here.
