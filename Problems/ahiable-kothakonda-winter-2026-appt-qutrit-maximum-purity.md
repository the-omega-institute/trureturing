---
slug: ahiable-kothakonda-winter-2026-appt-qutrit-maximum-purity
bibkey: ahiablekothakondawinter2026geometry
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result
---

# The exact maximum purity of absolutely PPT qutrit–qudit states

## Problem

Ahiable, Kothakonda and Winter, arXiv:2608.03390v2, Conjecture 6.7, asks:

> Let $\mathcal P_{m,n}\subseteq \mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\; n>2$. Then
> $$\max_{\lambda\in \mathrm{APPT}_{m,n}}\sum_{i=1}^{mn}\lambda_i^2=\max_{\lambda\in\mathcal P_{m,n}}\sum_{i=1}^{mn}\lambda_i^2$$
> and occurs at the spectra given by Eq. (44).

The resolved sector is $m=3$, every integer $n\geq3$. For a positive semidefinite, trace-one matrix $\rho$ on $\mathbb C^3\otimes\mathbb C^n$, APPT means $(U\rho U^\dagger)^\Gamma\succeq0$ for every unitary $U$, with $\Gamma$ the second-factor partial transpose. The purity is $\operatorname{Re}\operatorname{Tr}(\rho^2)$.

## Motivation

The supremum over these density matrices is
$$P_n=\max\left\{\frac{3n+8}{(3n+2)^2},\frac{3}{8n}\right\}.$$
It is attained by $(3,1,\ldots,1)/(3n+2)$ when $3\leq n\leq8$, and by $(2^n,1^{2n})/(4n)$ when $n\geq9$; the exponents denote multiplicities. `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result` proves the supremum equality and the prescribed computational-basis diagonal attaining matrix together.

## Gap

Preregistration #13345 fixes APPT-3, the source statements and the tier-3 research line. Tran, arXiv:2609.18568v1, remark following Theorem A, states: “Determining the exact maximum APPT purity remains open.” The literature search documented in that preregistration found no proof or refutation in its searched scope; it does not establish worldwide priority. The settlement addresses the qutrit sector of this gap.

## Route

The literal unitary definition implies both Hildebrand boundary LMIs through explicit Bell unitaries and principal compression. Spectral reduction preserves ordering, nonnegativity, total mass and the trace-square identity. Exact rational gap certificates bound the eight sectors $n=3,\ldots,10$. For $n\geq11$, the first LMI alone yields two scalar mass inequalities; gap reconstruction, thirty-three ray estimates and conical transfer yield the uniform upper bound. An antisymmetric Gram complement and a positive qutrit Kraus decomposition prove APPT for the two perturbation families. The explicit diagonal states give equality and nonemptiness of the purity set.

## Falsifier

A density matrix in any dimension $3\otimes n$, $n\geq3$, satisfying the literal unitary-quantified APPT predicate and having purity strictly above $P_n$ would contradict the proved claim. Ordering ties and zero spectral entries are included; neither simple spectrum nor strict positivity is a hypothesis.

## Evidence

The fourteen Lean modules under `D5/S3/Quantum/Entanglement/AbsolutePPT/` prove the result and its supporting constructions. The Scribe mirrors state the same dimensions, density and APPT hypotheses, purity quantities, spectral LMIs and attaining matrices. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The settling declaration is `QutritQuditMaximumPurity.result : claim`; its admission basis is `escape-witness`. Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

`theorem`; resolution `proved` in the $m=3$, $n\geq3$ sector.

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Exact maximum for every $n\geq3$ and the spectra $(3,1,\ldots,1)/(3n+2)$ for $n\leq8$, $(2^n,1^{2n})/(4n)$ for $n\geq9$ | proved | `QutritQuditMaximumPurity.result` retains the attaining diagonal matrix in the conclusion. |
| For $n\geq11$, $K_1\succeq0$ alone implies the upper bound | proved | `UniformSpectralBound.uniform_spectral_bound`, with $n=3+k$, $k\geq8$, assumes ordering, nonnegativity and mass one and uses no $K_2$ hypothesis. |
| Strictness of Tran's outer bound for every $3\otimes n$, $n\geq3$ | proved (source) | Tran's remark after Theorem A, quoted in `Library/QuantumStates/tran2026spectralappt.md`; this source result is outside the delivered Lean conclusions. |
| Conjecture 6.7 for $m\geq4$ | open | The qutrit Bell compression and Kraus construction establish only the $m=3$ sector. |
| Whether APPT equals absolute separability for $3\otimes n$ | open | The predicate quantifies positivity after partial transpose; no separable decomposition or equality with absolute separability is proved. |

### What the settlement shows

**Proved.** The decisive mechanism combines necessary boundary LMIs, sharp finite certificates, the $K_1$-only tail estimate and explicit APPT attainments. Thus the qutrit inscribed-polytope purity in Ahiable–Kothakonda–Winter is the global APPT maximum, rather than only a lower candidate. The two regimes meet the exact general formula above, including $n=8$, $n=9$ and the first uniform-tail dimension $n=11$.

**Proved.** The uniform estimate applies to every ordered, nonnegative, mass-one spectrum with $K_1\succeq0$ in $n\geq11$; its stated hypotheses do not require $K_2$ or the full APPT predicate. The finite-sector certificate theorems retain the density and APPT hypotheses. No relaxation of those finite hypotheses is claimed.

**Proved (settlement implication).** Any source argument whose only missing premise is Conjecture 6.7 restricted to $m=3$, $n\geq3$ can use this sector's maximum and attaining spectra. Tran's exact-purity gap closes in this sector, while the strict outer-bound conclusion remains a distinct source result. No other dependent source theorem is asserted to have been formalized here.

**Open.** Higher local dimensions, APPT versus absolute separability, and a classification of all maximizing states remain outside this conclusion. Attainment by the prescribed spectra does not assert uniqueness of every maximizer.

## ASSUMED-UNVERIFIED

The source priority and the absence of a worldwide independent settlement are not kernel facts. The preregistered literature check supports only `not-found-in-searched-scope`. The mathematical theorem uses the explicit APPT and density predicates; its proof does not import source prose or assume Hildebrand sufficiency. Tran's strictness statement is source evidence, not an additional kernel-checked theorem of this delivery.
