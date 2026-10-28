---
slug: song-chen-djokovic-2023-unique-basis-eof
bibkey: songchendjokovic2023uniquebasis
doi: 10.1109/TIT.2024.3435412
url: https://arxiv.org/abs/2307.01980v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result
---

# Formation is not constant on the Song–Chen–Đoković subspace

## Problem

Song, Chen and Đoković, *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*, arXiv:2307.01980v3, p. 3, asks:

> Further, by calculation one can see that every state in the span of the three states has entanglement more than 1.52 ebits. Hence, the entanglement of formation (EOF) of every mixed state whose range is contained in the span is also more than 1.52 ebits [19]. We don't know whether this EOF is exactly equal to that of the pure state |Ψ₁⟩.

The vectors are those of Eqs. (2)–(3), on $\mathbb C^3\otimes\mathbb C^9$. Write $P_j=|\Psi_j\rangle\langle\Psi_j|$, $S=\operatorname{span}_{\mathbb C}\{\Psi_1,\Psi_2,\Psi_3\}$ and $H_0=H(4/9,1/3,2/9)$, with entropy in bits.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Eq. (2), the twelve nonzero entries of $G$ | `UniqueBasisFormationRefutation.G` | Literal real square roots embedded in $\mathbb C$; indices decreased by one. |
| Eq. (3), the columns $r_{3a+j}$ | `Psi k (a,b)` | Entry $G(b,3a+k)$, with zero-based `Fin` indices. |
| The span of the three states | `spanPsi` | Complex linear span of `Set.range Psi`. |
| Every density operator supported in $S$ | `claim`: positivity, trace one, range inclusion | All matrices on `Fin 3 × Fin 9`, with no added restriction. |
| EOF equal to that of $\Psi_1$ | `FormationBounds.E_F`, `PureStateHandshake.rankOneDensity (Psi 0)` | Existing finite-ensemble formation in bits and rank-one density. |
| A negative answer | `result : ¬ claim` | Refutes the complete universal equality. |

## Motivation

The external named question is preregistered in [#16853](https://github.com/the-omega-institute/trureturing/issues/16853). The settling GID is `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result`; its admission basis is `open-problem-resolution (#16853; Refuted)`. There is no digestion atom and no coverage claim. The Scribe attaches one `OpenProblemResolutionClaim` with resolution `Refuted` to this declaration. The source locator is [the Library note](../Library/QuantumChannels/songchendjokovic2023uniquebasis.md).

## Gap

A locally distinguishable orthonormal basis need not minimize the finite pure-state ensemble cost. The universal equality would preclude any lower-cost nonorthogonal decomposition of a supported density operator.

## Route

Let $\phi_\pm=(\Psi_1\pm\sqrt3\Psi_2)/2$ and $\rho_0=(P_1+P_2+P_3)/3$. The explicit ensemble has vectors $\phi_+,\phi_-,\Psi_1,\Psi_3$ and weights $2/9,2/9,2/9,1/3$. The superposition marginals have spectrum $(17,10,9)/36$. Their entropy $H_*<H_0$ follows from
$2^{102}<17^{17}5^{10}3^6$ and the logarithm laws. Its cost is $(4/9)H_*+(5/9)H_0<H_0$. Positive-weight phase rigidity proves $E_F(P_1)=H_0$; zero-weight ensemble terms contribute zero. The finite-ensemble upper bound then contradicts the universal equality.

## Falsifier

A positive semidefinite trace-one matrix supported in $S$ with $E_F(\rho)<E_F(P_1)$ falsifies the question's proposed equality. `result` uses the explicit $\rho_0$ and its four-slot ensemble. The argument supplies a strict upper bound for $E_F(\rho_0)$, rather than its exact value.

## Evidence

The kernel-checked settling theorem is `D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation.result`. Its consumed private lemmas establish the density conditions, ensemble identity, marginal characteristic polynomials, entropy gap and pure-state equality. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The published owner theorem `D5.S3.Quantum.Matrix.CartesianVariance.density_eigenvalues_sum` is a separate audit target. Its four-slot escape audit is unfinished under [#17533](https://github.com/the-omega-institute/trureturing/issues/17533): dependent source reconstruction, whole-family variation, slot sensitivity and observational-dependence evidence are missing. No validated registration is asserted.

### Experiment

[Independent numerical and exact check](https://github.com/the-omega-institute/trureturing-experiments/tree/e0c03b28bb524e37942a1e8ae9687e92ffa7c0ac/docs/reports/song-chen-djokovic-2023-unique-basis-eof). Program: `check.py`; command: `python3 /Users/auric/trureturing-experiments/docs/reports/song-chen-djokovic-2023-unique-basis-eof/check.py`, exit 0, `ALL_OK`; script SHA-256 `320cfa969abe4a88c1156742c66c6d51ec9a5b7c8713351fff274a63c1ab1254`.

Tested scope: exactly the three source vectors, the two superpositions with signs $+1,-1$, their marginals, and the displayed four-slot decomposition of $\rho_0$. Exact arithmetic checks the orthonormality, projector decomposition, characteristic polynomials and integer gap $818637354117741584296712569121$. The computed decimal values are $H_0=1.5304930568$, $H_*=1.5244951608$, and ensemble cost $1.5278273252$. The program performs no parameter sweep of the diagonal-weight family and does not compute the exact convex-roof infimum.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Nonorthogonal mixing mechanism and strict refutation | proved | Kernel-checked: private `phi_unit`, `phi_projectors`, `phi_marginal`, `R_charpoly`, `entropy_strict`, `rho0_cost`, `psi0_formation`, and public `result` in the settling module. These prove the exact ensemble cost bound for $\rho_0$. |
| Every diagonal mixture with $\lambda_1,\lambda_2>0$ | proved in prose; not formalized | The argument below proves the route recorded in #16853 for $\lambda_j\ge0$ and $\sum_j\lambda_j=1$. No Lean family theorem is claimed. |
| Pure-state equality $E_F(P_1)=H_0$ | proved | Kernel-checked: private `pure_formation_eq` and `psi0_formation`, consumed by `result`. |
| Compatibility with the source's $1.52$-bit lower bound | computed | The experiment's three decimal readings all exceed $1.52$; neither that source bound nor an exact formation value for $\rho_0$ is asserted as a new Lean theorem. |
| Fixed-state experiment | computed | The pinned experiment entry above, exit 0, matching SHA-256, exact tested scope of three source vectors, two superpositions and one four-slot ensemble. |
| Later literature screen | literature reading | The screen recorded in #16853 covers 19 full texts, including later Song–Chen papers and Xu–Nie–Sun, arXiv:2501.05237; no answer was found in that scope. |
| Journal paragraph and completeness | open | Journal paragraph unread (IEEE access challenge; Firecrawl HTTP 402); literature completeness is `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Proved in the module.** The equality fails through unequal-amplitude nonorthogonal superpositions. The explicit supported density has a smaller ensemble upper bound than the formation of $P_1$. The pure-state equality survives. The module does not determine the exact infimum of $\rho_0$.

**Proved in prose, not a Lean family theorem.** For $\lambda_j\ge0$ summing to one and $\lambda_1,\lambda_2>0$, set $t=\min(4\lambda_1,4\lambda_2/3)>0$. Then $t\le\lambda_1+\lambda_2\le1$: indeed $t/4\le\lambda_1$ and $3t/4\le\lambda_2$. The projector identity gives
$$\sum_j\lambda_jP_j=\frac t2|\phi_+\rangle\langle\phi_+|+\frac t2|\phi_-\rangle\langle\phi_-|+(\lambda_1-t/4)P_1+(\lambda_2-3t/4)P_2+\lambda_3P_3.$$
All weights are nonnegative and sum to one. The three source marginals are the cyclic permutations of $(4/9,1/3,2/9)$: the second is $\operatorname{diag}(1/3,2/9,4/9)$ directly from the three nonzero coordinates of $\Psi_2$, and the other two are the diagonal marginals established in the module. Thus this ensemble costs $tH_*+(1-t)H_0<H_0$, proving $E_F(\rho)<H_0$. Boundary cases with $\lambda_1\lambda_2=0$ are outside this argument; it is a sufficient family, not a classification.

**Computed compatibility.** The experiment's $H_0$, $H_*$ and cost all exceed $1.52$ bits, consistent with the source's lower bound. The source's distinguishability conclusions do not depend on the proposed EOF equality; this refutation changes no claim about existence or uniqueness of those bases.

## ASSUMED-UNVERIFIED

Literature completeness and whether the journal version changes the question's paragraph are unverified. The 19-text screen is the bounded literature result recorded by the source-checking orchestrator in #16853. No exhaustive novelty claim is made. The separate owner escape audit remains unfinished under #17533.
