---
slug: rossetti-mancini-winter-schindler-2025-w3-ppt-measurement-not-separable
bibkey: rossetti2025observational
doi: 10.1109/TIT.2026.3700031
url: https://arxiv.org/abs/2510.10058v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result
---

# The optimal W-state PPT measurement is outside SEP

## Problem

Rossetti, Mancini, Winter and Schindler, *Observational entropy of quantum
correlations and entanglement*, arXiv:2510.10058v1, Section X.0.4, ask:

> Nevertheless, none of the tests conducted so far have succeeded in detecting entanglement, leaving open the question of whether (M′, 𝟙 − M′) belongs to the SEP class.

The source and its equations (62), (79), and (83) are identified in the
[literature note](../Library/QuantumContext/rossetti2025observational.md).
The positive membership assertion is refuted under the literal conventions of
[preregistration #19016](https://github.com/the-omega-institute/trureturing/issues/19016).

### Statement echo

| Source clause | Lean counterpart | Meaning |
| --- | --- | --- |
| Three ordered qubits | `Fin 3 → Fin 2` | Eight computational basis configurations |
| Normalized W and anti-W vectors | `W3`, `W3bar` | The source's three-term vectors with real coefficient $\sqrt{1/3}$ |
| Weight-one and weight-two subspaces | `P1`, `P2` | Sums of the three corresponding basis projectors |
| Six invariant projectors | `Q1` through `Q6` | The six right-hand sides on printed page 22 |
| Equation (83) | `Mprime` | Coefficients $1,1/2,0,0,2/3,1/12$ |
| Equation (62): effects proportional to separable states | `IsSEPEffect` | A nonnegative real multiple of `IsFullySeparableLocal`, with three sites and two local basis states |
| Both effects belong to SEP | `claim` | `IsSEPEffect Mprime` and `IsSEPEffect (1 - Mprime)` |
| Negative answer | `result` | The negation of the entire conjunction |

`Pi.single` and `Matrix.vecMulVec` supply the basis vectors and rank-one
operators. The existing `PronkoFredkinNonCyclicAnnihilation.tensor` supplies
the tensor product in the proof. These choices preserve the source expressions.
The real scalar and density-state representation follow the source's explicit
gloss of equation (62); they impose no extra hypothesis on the asserted membership.

## Motivation

SEP membership of this optimal PPT measurement would give the analytic SEP
observational entropy claimed conditionally in the source. Its failure separates
this particular measurement from the SEP class. It does not determine whether a
different SEP measurement attains the same objective.

## Gap

Issue #19016 records the source and literature screen: arXiv v1, the INSPIRE
citation record, arXiv/MathDB/title and author searches, the repository and its
open-problem register, and the `Naixu-Guo/quantum-open-problems` and
`google-deepmind/formal-conjectures` corpora. No settlement was found in that
searched scope. The journal text was inaccessible. Completeness of the search
and whether the journal version changes the question are ASSUMED-UNVERIFIED.

## Route

Set $R=\mathbb 1-M'$, $w=|100\rangle+|010\rangle+|001\rangle$, and

$$
z_1=2|000\rangle+|110\rangle+|101\rangle,\qquad
z_2=2|000\rangle+|110\rangle+|011\rangle,\qquad
z_3=2|000\rangle+|101\rangle+|011\rangle.
$$

The four quadratic forms vanish: $\langle w,Rw\rangle=0$ and
$\langle z_i,R^{T_i}z_i\rangle=0$. For a hypothetical finite positive-product
sum, positivity makes every summand's four quadratic forms vanish separately.
The PSD zero-form criterion then gives four vector-kernel equations.
The direct-entry calculation, including vanishing local diagonals, forces each
product summand to have weight-two diagonal mass twice its weight-one mass.
Summation preserves that relation. For $R$ the two masses are $5/2$ and $2$,
which contradicts $5/2=2\cdot2$.

The private `product_mass_ratio` and `separable_mass_ratio` carry this implication;
`kernel_quadratics` and `remainder_masses` supply its concrete inputs. The public
`result` applies the implication to the complementary effect of `claim`.
The existing owner's `density_psd` transports density-state positivity and is
used by `separable_mass_ratio`; its statement and proof are preserved.

## Falsifier

A fully separable decomposition of $R$, an incorrect matrix coefficient, a
wrong partial-transpose convention, or a failure of the zero-form implication
would defeat this argument. The Lean statement fixes the exact source matrices,
and its proof checks the implication for arbitrary finite product mixtures.
No claim of optimality or entropy inequality is inserted as a Lean hypothesis.

## Evidence

The canonical Lean source is
`D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.lean`, with its Blueprint
Scribe. The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The published owner theorem
`D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.density_psd`
has an unfinished four-slot escape audit under
[issue #19102](https://github.com/the-omega-institute/trureturing/issues/19102).
No Reg mirror or `declared_validated` status is claimed for that theorem.

### Exact-arithmetic experiment

[Experiment directory at commit `e9a7bd12bab621fac9aa726605def50b3ecab0e5`](https://github.com/the-omega-institute/trureturing-experiments/tree/e9a7bd12bab621fac9aa726605def50b3ecab0e5/docs/reports/rossetti-mancini-winter-schindler-2025-w3-ppt-measurement-not-separable).
Command: `python3 /tmp/op-w3sep-check.py`, using the exact `check.py` extracted
from that commit and path; exit 0. Script SHA-256:
`0f67cf8ea123698ede88939d2587f06c93af4e49b152631a40e04528acb29659`.

The exact tested scope is the single three-qubit operator from equation (83),
its complement and their three single-qubit partial transposes. The computation
checks $\operatorname{Tr}M'=9/4$, the displayed $R$, all eight PSD tests, the four
kernel equations, the two masses, two sample product solutions, and the four-term
product decomposition of $M'$. The distinct eigenvalue sets of $R$ and $R^{T_i}$
are respectively $\{0,1/3,1/2,11/12,1\}$ and
$\{0,1/4,2/3,5/6,1\}$ for each of the three sites. These are computations,
separate from the Lean refutation; they assert no parameter-uniform family.

## Triage

Tier 1 external named open question; resolution Refuted. There is no atom or
coverage step. The settling module's admission basis is
`open-problem-resolution (#19016; Refuted)`. Its theorem and private helpers are
classified `bind-only`; no new escape witness is claimed. Every private helper
is consumed in the derivation of `result`. The existing frozen owner retains its
`escape-witness` admission basis and its `separable_exchange_zero` witness.

### What the settlement shows

| Item | Evidence kind | Result and boundary |
| --- | --- | --- |
| SEP membership of the specified POVM | Kernel-checked: `result` | Refuted: both effects cannot be SEP |
| $M'$ is fully separable | Computed: the pinned experiment | The identity $M'=\frac1{48}\sum_{k=0}^3|u_k\rangle\langle u_k|$, $u_k=(\sqrt2|0\rangle+\mathrm i^k|1\rangle)^{\otimes3}$, passes exact checking; `IsSEPEffect Mprime` is not separately proved in Lean |
| PPT of the complementary effect | Computed: the pinned experiment | $R$ and all three $R^{T_i}$ are PSD; no concrete Lean PSD theorem for $R$ is included |
| Failure mechanism | Kernel-checked: private `product_mass_ratio`, `separable_mass_ratio`, `kernel_quadratics`, `remainder_masses`, consumed by `result` | Four zero forms force mass ratio two, but the masses are $2$ and $5/2$ |
| Analytic value of $E_{\mathrm{SEP}}(W_3)$ | Open | The refutation gives no optimum over all SEP POVMs |
| Strict entropy gap between SEP and PPT | Open | A failure of this optimizer does not prove $E_{\mathrm{SEP}}(W_3)>E_{\mathrm{PPT}}(W_3)$ |
| Another SEP POVM attaining trace $9/4$ | Open | No alternative-attainment classification is supplied |
| Spectral-decomposition route | Literature/API reading: pinned Mathlib `spectral_theorem` | The API is available; the direct-entry proof uses no spectral decomposition |

The nearest surviving statements are the computed separability of $M'$ and PPT
of the full measurement. The source's PPT optimization is not contradicted by
this SEP refutation. Its proposed route to a SEP entropy formula through this
specific POVM is unavailable; the optimal SEP value, a strict gap, and other
attaining measurements remain open here.

## ASSUMED-UNVERIFIED

- Literature-screen completeness: no settlement was found in the recorded scope;
  this is not an exhaustive absence theorem.
- The IEEE journal version's treatment of the question is unverified because its
  full text was inaccessible.
- The computational PPT and $M'$ decomposition claims have exact SymPy evidence,
  without additional Lean theorems for those claims.
