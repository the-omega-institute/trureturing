---
slug: guo-2024-partial-negativity-hhat-subadditivity
bibkey: guo2024completegenuine
doi: 10.1016/j.rinp.2024.107430
url: https://arxiv.org/abs/2301.00334v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.result
---

# Guo's partial-negativity subadditivity conjecture

## Problem

Y. Guo, *Complete Genuine Multipartite Entanglement Monotone*, Results in
Physics 57 (2024), 107430, arXiv:2301.00334v3, states the reduced function
$\hat h(\rho)=\sqrt{\delta_1\delta_2}$, where $\delta_1$ and $\delta_2$ are
the two largest eigenvalues of $\rho$, and conjectures in equation (24) that
$\hat h(\rho_{AB})\leq\hat h(\rho_A)+\hat h(\rho_B)$ for every bipartite
density matrix.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| two largest eigenvalues counted with multiplicity | `hHat` uses positions 0 and 1 of the decreasing `eigenvalues₀` list |
| every pair of local dimensions | `claim` quantifies `dA dB : ℕ` |
| every bipartite state | `claim` quantifies `ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ` and assumes `IsDensity ρ` |
| reduced states are the two partial traces | `ρ.traceRight` and `partialTraceFirst ρ` in `claim` |
| subadditivity inequality (24) | `claim` concludes `hHat ρ ≤ hHat ρ.traceRight + hHat (partialTraceFirst ρ)` |
| refutation | `result : ¬ claim` |

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

## Motivation

Equation (24) is used as an assumption for later constructions in the source.
A certified counterexample identifies the dimension at which the unrestricted
statement fails and separates that failure from restricted low-dimensional
questions.

## Gap

The source labels equation (24) as a conjecture. The counterexample must satisfy
the density condition, compute the two largest eigenvalues of the joint state,
and compute both partial traces in the same formal model.

## Route

For $r=0,1$, let $u_r(i,j)$ be the indicator of $j=i+r$ in `Fin 5` and set
$$
R=\frac1{10}\left(\operatorname{vecMulVec}(u_0,u_0^*)+
\operatorname{vecMulVec}(u_1,u_1^*)\right).
$$
The two supports are disjoint. Their squared norms are 5, their cross inner
products vanish, $R$ has trace one, and $R^2=\frac12R$. The spectrum therefore
has two entries $1/2$ and the remaining entries zero. Both partial traces are
the uniform matrix $(1/5)I$.

## Falsifier

The refutation would fail if the supports were not disjoint, if the witness were
not positive semidefinite with trace one, if the spectral calculation did not
force two entries equal to $1/2$, or if either partial trace differed from
$(1/5)I$. The formal proposition remains the unrestricted universal claim;
no numerical non-violation is treated as a proof of a restricted statement.

## Evidence

The kernel-checked declaration is
`D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.result`.
Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
The exact checker is published at
`https://github.com/the-omega-institute/trureturing-experiments/tree/`+
`b31f69539f11bf1fff6adf2a922c79d2fd0c9fae/docs/reports/guo-2024-partial-negativity-hhat-subadditivity`
with command `python3 docs/reports/guo-2024-partial-negativity-hhat-subadditivity/check.py`,
exit code 0, and script SHA-256
`2ac3c82d113fbf4923ebf2ee6e8513ebeb60b641a6c5a6b20d2846c61344a44a`.
It checks exact rational arithmetic for $d=5,\ldots,12$ and
$t\in\{0,1/10\}$, including the projector identity, both uniform marginals,
and a positive violation.

The literature screen is partial. Versions v1 through v3 retain (24) as a
conjecture; eight accessible citing works do not settle it. The erratum's
abstract concerns equations (36), (37), (39), (41), and (43), while v3 retains
(24). Literature completeness is `ASSUMED-UNVERIFIED`.

The unfinished escape audit for the non-result declarations is tracked in
[issue #19585](https://github.com/the-omega-institute/trureturing/issues/19585).
No `declared_validated` registration is asserted here.

## Triage

| Target item | Status | Evidence |
| --- | --- | --- |
| Settlement at $d_A=d_B=5$ | proved | Kernel-checked `result : ¬ claim` |
| Two disjoint maximally entangled supports retain eigenvalues $1/2,1/2$ and both marginals are uniform with eigenvalues $1/5$ | proved | The proof path of `result`, through the state identities and spectral computation |
| Whether the inequality holds for all states with both local dimensions at most 4 | open | No formal or numerical non-violation is a proof of this restricted universal statement |
| The $d\geq5$ family and positive-definite perturbations | computed | The published exact checker, tested for $d=5,\ldots,12$ and $t\in\{0,1/10\}$, exit 0; uniform extension is open |
| Consequences for source arguments using (24) in arbitrary dimensions | open | The source's later constructions need a replacement justification or a proven dimension restriction; no claim that every construction fails |

### What the settlement shows

The global witness reaches $\hat h(R)=1/2$ while the two marginal values sum
to $2/5$, so the gap is $1/10$. The failure mechanism is the coexistence of two
orthogonal maximally entangled supports in the joint state and uniform local
marginals. The unrestricted conjecture must therefore be replaced by a
dimension restriction or another hypothesis. The nearest surviving question
recorded here is the universal claim for local dimensions at most four, which
remains open.

## ASSUMED-UNVERIFIED

Literature completeness, priority, and the absence of an earlier settlement are
`ASSUMED-UNVERIFIED`; the published paper and erratum full texts and Guo's
related Physical Review A paper were not fully read in the bounded screen. The
formal result settles only the encoded equation (24) and makes no claim about
every later construction that used it.
