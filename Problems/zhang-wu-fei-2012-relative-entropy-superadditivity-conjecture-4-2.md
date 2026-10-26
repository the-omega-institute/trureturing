---
slug: zhang-wu-fei-2012-relative-entropy-superadditivity-conjecture-4-2
bibkey: zhangwufei2013superadditivity
doi: 10.1016/j.physleta.2013.05.047
url: https://arxiv.org/abs/1210.4720v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result
---

# Zhang–Wu–Fei: relative-entropy superadditivity after unitary conjugation

## Problem

Zhang, Wu and Fei, arXiv:1210.4720v4, p. 6, §4, conjecture (4.2), state:

> Based on the above result, we propose the following conjecture: There exist unitary operators U_A ∈ U(H_A), U_B ∈ U(H_B) and U_AB ∈ U(H_A ⊗ H_B) such that S(U_AB ρ_AB U_AB† ‖ σ_AB) ⩾ S(U_A ρ_A U_A† ‖ σ_A) + S(U_B ρ_B U_B† ‖ σ_B), (4.2) where the reference state σ_AB is required to be full-ranked state. Indeed, our numerical calculations show that inequality (4.2) is true.

The source is recorded in [the Library note](../Library/Divergence/zhangwufei2013superadditivity.md).
The assertion ranges over every pair of finite subsystem dimensions and every joint density
$\rho_{AB}$ and full-rank joint reference $\sigma_{AB}$; all four marginals are actual partial traces.
The relative entropy is $S(\rho\Vert\sigma)=\operatorname{Re}\operatorname{Tr}(\rho(\log\rho-\log\sigma))$
with natural logarithms. The independent existential joint and local unitaries are unrestricted.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite $H_A,H_B$ | Natural dimensions `a`, `b`, with coordinates `Fin a`, `Fin b` | All finite dimensions; a density state supplies trace one |
| Joint density matrices $\rho_{AB},\sigma_{AB}$ | `DensityState (Fin a × Fin b)` | Positive semidefinite complex matrices of trace one |
| Full-ranked $\sigma_{AB}$ | `(CStarMatrix.ofMatrix.symm σ.1).PosDef` | Positive definiteness of the reference matrix |
| $\rho_A,\sigma_A$ | `marginalRight ρ`, `marginalRight σ` | Keeps the first product factor |
| $\rho_B,\sigma_B$ | `marginalLeft ρ`, `marginalLeft σ` | Keeps the second product factor |
| Three existential unitaries | `UAB`, `UA`, `UB` and `Matrix.unitaryGroup` membership proofs | The membership proofs express unitarity, with no extra hypotheses |
| Inequality (4.2) | `claim` | Sum of the two marginal divergences is at most the joint divergence |
| Refutation | `result` | The negation of the complete universally quantified `claim` |

## Motivation

The preregistration is [issue #18562](https://github.com/the-omega-institute/trureturing/issues/18562).
Unitary optimization does not repair relative-entropy superadditivity when the input is maximally mixed:
every unitary fixes that input and both of its marginals. A correlated reference approaching a pure
product state can therefore expose a strict negative gap that unitary choices cannot change.

## Gap

The delivered theorem settles (4.2) at the literal preregistered conventions.
The proof reuses the existing density-state, actual-partial-trace, unitary-conjugation and
diagonal functional-calculus interfaces. The original `diagonalState` definition in
`D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation` supplies the density constructor;
its defining expression and proofs are unchanged.

## Route

Choose $a=b=2$, $\rho=I_4/4$, and $\sigma=\operatorname{diag}(61,1,1,1)/64$,
in product order $(0,0),(0,1),(1,0),(1,1)$. Every reference eigenvalue is positive.
The input marginals are $I_2/2$, and both reference marginals are
$\operatorname{diag}(31,1)/32$. All three unitary orbits of the input states are constant.
The joint divergence is

$$
J=\log(1/4)-\tfrac14\log(61/64)-\tfrac34\log(1/64),
$$

and each marginal divergence is

$$
M=\log(1/2)-\tfrac12\log(31/32)-\tfrac12\log(1/32).
$$

Logarithm identities give $4(J-2M)=\log(923521/3997696)<0$.
The private diagonal-evaluation, invariance, marginal and sign lemmas are consumed by `result`.
They are applications and normalization of frozen owners and pinned Mathlib results.

## Falsifier

The preregistered overturn criterion is $J-2M\ge0$ for this witness, or a failure of
full rank, density normalization, actual marginal identities or unitary invariance.
The theorem `result` checks the negation with those conditions preserved.

## Evidence

The settling declaration is
`D5.S3.Quantum.Information.ZhangWuFeiSuperadditivityRefutation.result`.
Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Scribe displays the full negated claim and carries one `OpenProblemResolutionClaim` with
resolution `Refuted` on this declaration.

| Declaration | `proof_shape` | `escape_witness` | `admission_basis` |
| --- | --- | --- | --- |
| `D5.S3.Quantum.Information.ZhangWuFeiSuperadditivityRefutation.result` | bind-only | none | open-problem-resolution (#18562; Refuted) |

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The owner publication is a definition; no additional public theorem is authored.
Its escape audit is unfinished: [issue #20328](https://github.com/the-omega-institute/trureturing/issues/20328).
No decoded registration or `declared_validated` status is claimed for `diagonalState`.

### Numerical reproduction

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/cb7c67eb1cb775dd3f98962a0381bb2fbfa549b0/docs/reports/zhang-wu-fei-2013-modified-superadditivity-relative-entropy).
Command: `python3 docs/reports/zhang-wu-fei-2013-modified-superadditivity-relative-entropy/check.py`
from that experiments checkout; exit 0, `RESULT PASS`.
The SHA-256 of `check.py` is
`86869d20e70da499a3cdcb240a4a9b20ee0f27fcd4712862df2638a3c70c490b`.
The deterministic seed is 20261017. These are floating-point computations, separate from the Lean theorem.

The closed expression and direct matrix evaluation differ by at most $3.55\cdot10^{-15}$
for $(a,b)\in\{(2,2),(2,3),(3,2),(3,3),(2,5),(4,4)\}$ and
$t\in\{1/(4ab),1/(16ab),10^{-4},10^{-8}\}$.
At $a=b=2,t=1/64$, the computed gap is $-0.366320$ and its exponential $\exp(4\Delta)$ is $0.231013$.
The nondegenerate two-qubit calculation uses exactly
$\epsilon\in\{10^{-6},10^{-4},1/2048,1/1024\}$ and
$\eta\in\{10^{-7},10^{-5},1/8192,1/4096\}$.
The largest spectral supremum on these sixteen pairs is $-0.343656$;
twenty Haar-random unitary triples per pair stay below the corresponding supremum.
The product-reference controls at dimensions $(2,2)$ and $(2,3)$ give respectively
$-5.551\cdot10^{-17}$ and $1.665\cdot10^{-16}$, at floating-point precision.

## Triage

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Exact settlement | Proved in Lean: `ZhangWuFeiSuperadditivityRefutation.result` | Refutes the complete (4.2) claim |
| Same-witness (4.3) and follow-up Conjecture 3.1 | Proved in prose below | No separate Lean statements for those source formulations |
| All dimensions | Open | No uniform all-dimensional Lean theorem; the experiment checks only the six dimension pairs and four parameters specified above |
| Nondegenerate family | Computed by the pinned experiment | Sixteen parameter pairs and twenty random triples per pair; a uniform family theorem is open |
| Retention | Source inspection and compiled consumption | Reuses the original `diagonalState`; no unconsumed companion theorem is delivered |

### What the settlement shows

**Proved in Lean.** The source's full-rank condition does not suffice: the explicit reference
has four positive eigenvalues, yet no joint/local unitary triple satisfies the asserted inequality.
The mechanism is the fixed unitary orbit of the maximally mixed input together with the strict
negative relative-entropy gap. The proof uses the marginals of the same joint input and reference.

**Proved in prose.** For (4.3), the input spectra are uniform, so permuting either the reference
eigenvalues or the marginal reference eigenvalues leaves their classical relative entropies
unchanged. Thus (4.3) has the same values $J$ and $2M$, and fails by the same strict gap.
The follow-up arXiv:1305.2023v3, Conjecture 3.1, restricts the joint unitary to $U_A\otimes U_B$.
Such a product is a joint unitary; failure for every joint unitary entails failure for this restricted
choice. Neither inference is claimed as a separate kernel-checked source formulation.

**Nearest surviving statement, proved in prose.** With a product reference
$\sigma_A\otimes\sigma_B$ and the same maximally mixed input $I_{ab}/(ab)$,
the joint divergence equals the sum of the marginal divergences. Indeed, write the positive
reference eigenvalues as $x_i$ and $y_j$; summing
$\log(x_i y_j)=\log x_i+\log y_j$ with uniform weights gives that equality.
This restricted case has zero gap. The experiment's two product-reference controls reproduce it
within floating-point precision. The correlated reference is the structure that violates the
unrestricted conjecture.

**Source consequences.** The source's unitary-orbit extremum formulas (4.1) are compatible with
this witness; their use to express (4.3) does not make the proposed superadditivity inequality true.
The follow-up's numerical evidence for all qubit pairs does not extend to this witness.
No other source theorem is asserted invalid by this settlement.

**Open.** A kernel proof of the all-dimensional asymptotic family and a uniform nondegenerate
family theorem are outside the delivered statement. The finite numerical grid does not establish
either uniform assertion.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and literature screen recorded in
issue #18562 covers arXiv:1210.4720v4, arXiv:1305.2023v3, arXiv:1705.03521v3,
arXiv:1803.07580 and arXiv:1305.1472, together with the citing-work search described there.
The screen is attributed to that issue's producers; it does not certify that no other publication
settles the conjecture. The exact source statement, witness and convention correspondence are
specified above independently of that completeness assumption.
