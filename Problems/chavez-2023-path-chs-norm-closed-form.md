---
slug: chavez-2023-path-chs-norm-closed-form
bibkey: chavez2023extremalpolynomialnorms
doi: 10.48550/arXiv.2311.04689
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result
url: https://arxiv.org/abs/2311.04689v3
---

# Complete homogeneous symmetric norms of paths

## Problem

Chávez et al., *Extremal polynomial norms of graphs*, arXiv:2311.04689v3, Section 5, Problem 1: “Compute ‖P_n‖_d for d ≥ 4.” The surrounding norm definition requires even $d$.

For $d=2m$, set $L=2m+n-1$ and interpret $\binom Lr$ as zero outside $0\le r\le L$. The answer is

$$h_{2m}(\lambda(P_n))=\sum_{k=0}^{\lfloor m/(n+1)\rfloor}\left[\binom L{m-k(n+1)}-2\binom L{m-k(n+1)-1}+\binom L{m-k(n+1)-2}\right].$$

The norm is the real $2m$-th root of this expression, for every $n\ge1,m\ge2$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Path adjacency | Literal matrix with entry one exactly at consecutive natural indices | `pathAdjHermitian` identifies a Hermitian path matrix. |
| Complete homogeneous symmetric polynomial | `chs`, using Mathlib `hsymm` at Hermitian eigenvalues | Exact source object; eigenvalue ordering is immaterial. |
| Norm from Theorem 1.4 | `chsNorm`, real power with reciprocal degree | Exact real-root convention. |
| Every even degree at least four | `claim`: all natural $n,m$, $1\le n$, $2\le m$ | $d=2m$. |
| Compute the value | Both equalities in `claim`, proved by `result` | Gives the power and the norm; no source clause is dropped. |
| Zero-extended binomial | Frozen `IntegerIndexBinomial.binom` | Its value is zero outside the natural binomial range. |

## Motivation

The settling GID is `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result`, preregistered in #18565. The two expressions of the later Bouthat–Chávez–Sheng Remark 4.3 are settled separately in #18566; its one-term simplification is refuted in #18567.

## Gap

The stated path-norm problem is settled under the source's even-degree convention. Literature completeness and independent priority remain `ASSUMED-UNVERIFIED`.

## Route

The path determinant satisfies the constant-weight continuant recurrence. Its reciprocal is the generating series for complete homogeneous symmetric values. Catalan substitution and the frozen Lagrange coefficient transform turn its coefficients into the displayed binomial second differences. The geometric-series inverse is supplied by `CompositionalIterateCongruence.geometric_inverse`, through the consumed adapter `geometric_mul_linear`. The imported owners are `IntegerIndexBinomial.binom`, `CiglerStripProductAlgebra.cont`, the coefficient transform in `P13CatalanLagrangeBridge`, and `ForbiddenNeighbourDeterminant.path_det_recurrence` and `ForbiddenNeighbourDeterminant.det_one_add_smul_hermitian`. The arbitrary-order invariant `continuant_change_variable` is content: from $x(1+q)^2=q$ it proves $(1+q)^n\operatorname{cont}(x;1,1;n)(1-q)=1-q^{n+1}$. Its consumers `model_subst_inverse`, `reciprocal_coefficient_model`, `reciprocal_closed_coefficient`, `chs_formula` and `result` are content with that escape witness. Admission is `open-problem-resolution (#18565; Proved)` and utility is `none`.

## Falsifier

A path with $n\ge1,m\ge2$ whose symmetric value or real-root norm differs from the formula would contradict `result`. Odd-degree expressions are outside the norm assertion.

## Evidence

`D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` proves the full literal `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit, including the published supplier `D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.geometric_inverse`, is unfinished: [#18981](https://github.com/the-omega-institute/trureturing/issues/18981). No validated registration is claimed. The missing evidence comprises exact source reconstruction, realization bridges, whole-family variation and sensitivity for the dependent finite spectra and ring-polymorphic identities.

Experiment: [the published exact-coefficient and numerical-spectrum check](https://github.com/the-omega-institute/trureturing-experiments/tree/d97c29bd2356ba3271c6ab11b319ff267167959c/docs/reports/chavez-et-al-2023-path-chs-norm). Command: `python3 /tmp/op-chavez/rework-51566/chavez-check.py`; exit 0. The file is the byte-exact `check.py` from that commit, SHA-256 `7114b92371dffb90520116d2dd1328b0fc5e32c903d7a56facf62a2578e60766`. It compares 375 exact coefficients for $1\le n\le15$, $1\le m\le25$ with zero mismatches, and checks numerical eigenvalues for $1\le n\le7$, $1\le m\le6$. Sample values are $8,21,55,16$ at $(n,m)=(4,2),(4,3),(4,4),(3,4)$. Omitting reflection terms changes 105 tested cases. These finite readings are independent of the Lean proof.

## Triage

- **Proved, kernel-checked — #18565.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` gives the finite binomial formula and its real-root norm for every $n\ge1,m\ge2$.
- **Proved, kernel-checked — #18566.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result` gives both displayed identities for every $n\ge1$ and even $d\ge2$.
- **Refuted, kernel-checked — #18567.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result` disproves the one-term universal claim using $n=2,d=6$; the utility classification is `certified-instance` with `basis=refutes`.
- **Literature — open completeness boundary.** The source and the preregistrations' bounded literature screens identify no prior settlement. Completeness is `ASSUMED-UNVERIFIED`.

- **Computed.** The exact coefficient, spectrum and reflection-control readings have precisely the scope given in Evidence.
- **Computed.** The exact-coefficient experiment records $h_8(P_3)=16$; no uniform boundary correction is asserted as a theorem of this module.
- **Open.** A uniform correction of the printed truncation and the one-term boundary rule is outside this claim. Odd degree is outside the source's norm definition.

### What the settlement shows

- **Proved, kernel-checked.** `chs_formula` gives the symmetric-value identity for all natural $n,m$, including $m=0$; `result` supplies the source's norm statement in its declared range.
- **Explanatory mechanism.** The reciprocal continuant and Catalan substitution organize the reflection terms. This explanation is not an additional Lean theorem.
- **Computed.** Reflection terms are necessary in the 105 control cases of the published finite experiment.
- **Source dependence.** The result answers Problem 1; it does not invalidate Theorem 1.4 or Proposition 5.14. The later paper's two unproved identities hold, whereas its final simplification has a separate counterexample.
- **Open.** Classification of all boundary corrections, alternate graph families and minimal reflection ranges.

## ASSUMED-UNVERIFIED

Literature completeness, priority and exhaustive coverage of subsequent papers are unverified. The source v3 and the bounded screens in #18565–#18567 are the literature evidence. The escape audit remains unfinished under #18981.
