---
slug: zhang-jing-2025-block-criterion-power-case-theorem-2-3
bibkey: zhangjing2025positive
doi: 10.13001/ela.2025.9201
url: https://doi.org/10.13001/ela.2025.9201
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result
---

# Zhang–Jing Theorem 2.3: the upper power interval

## Problem

Feng Zhang and Hefang Jing, More inequalities for positive semidefinite matrices, Electronic Journal of Linear Algebra 41 (2025), 595–601, state after Remark 2.13:

> “Due to the limitations of our research method, we cannot solve the problem that Theorem 2.3 holds for $1/2 \le a \le 1$.”

Their Theorem 2.3 states:

> “Let $A \in M_n$. Then $[[|A|^{2a}, A^*], [A, |A|^{2(1-a)}]] \ge 0$, for $0 \le a \le 1/2$ if and only if $A$ is normal.”

The notation is “$|A| = (A^*A)^{1/2}$ and $A^*$ is the conjugate transpose of $A$” (p. 595). The delivered claim extends the displayed equivalence to every real $a$ with $1/2 \le a \le 1$, every natural dimension, and every complex square matrix, using the existing block construction with $|A|=\operatorname{CFC.sqrt}(A^*A)$ and real powers.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $|A|=(A^*A)^{1/2}$ and $A^*$ is conjugate transpose | The reused ZhangJingBlockNormalityRefutation.block owner | The source expression is preserved through the frozen owner; no duplicate absolute-value definition is introduced. |
| $1/2\le a\le1$ | claim quantifies a, with both inequalities | Both endpoints are included. |
| Every n and $A\in M_n$ | claim quantifies n and A : Matrix (Fin n) (Fin n) Complex | The full finite-dimensional family is retained, including n=0. |
| The block is positive semidefinite iff A is normal | claim uses Matrix.PosSemidef and $A^*A=A A^*$ | Every block and the normality equality are retained. |
| $1/2\le a<1$ survives | claimBelowOne uses the strict upper bound | This is the proved neighboring statement. |
| The closed interval fails | result : \lnot claim | The conclusion is the literal refutation. |

## Motivation

The source left the upper interval open. The settling result is D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result, with admission basis open-problem-resolution (#18757; Refuted at a = 1; Proved below one).

## Gap

At $a=1$, the lower-right power is $x^0=1$, so the block is positive semidefinite for every matrix. The interval therefore needs a sharp endpoint distinction. For $a<1$, the positive exponent $2(1-a)$ makes the scalar power injective on nonnegative singular values.

## Route

The proof uses a finite singular-value decomposition $A=VDW^*$ with nonnegative diagonal $D$. It transports the block by unitary coordinates to diagonal powers and a unitary conjugate. The Schur-complement calculation gives a positive-semidefinite difference whose trace is zero, hence the difference vanishes. Injectivity of the positive real power forces the conjugating unitary to commute with $D$, which is equivalent to normality. The converse writes the balanced diagonal block as a Gram matrix. The endpoint uses the Gram identity for $[A,I]$ and a fixed nonnormal matrix.

## Falsifier

The refutation would fail if result did not prove the negation of the full closed-interval claim, or if below_one did not prove the strict interval with singular matrices and dimension zero included. Both declarations compile in the delivered module.

## Evidence

The kernel-checked declarations are:

- D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result : \lnot claim, the designated refutation result.
- D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.below_one : claimBelowOne.

The public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The escape audit for below_one is unfinished under issue #19914; no declared_validated registration is claimed.

Experiment: zhang-jing-2025-theorem-2-3-power-case at commit 03fcc97da76c2b464b6ab79d8383aa17c8910f07, https://github.com/the-omega-institute/trureturing-experiments/tree/03fcc97da76c2b464b6ab79d8383aa17c8910f07/docs/reports/zhang-jing-2025-theorem-2-3-power-case. Command: python3 check.py; exit 0; script SHA-256 fd68b9499f5e398726827824c3abee5776b1ce07c86a7f7eaae01ed59b8a0b3d. The checked scope is $a\in\{0.5,0.55,0.6,0.75,0.9,0.99\}$, $n\in\{2,3,4\}$, ranks $n,n-1,1$, 1350 random normal/nonnormal pairs, the singular $a=3/4$ example, and the endpoint Gram witness. These computations support the formal result; they do not establish a uniform theorem.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Refutation at $a=1$ | Proved in Lean: result refutes claim. | The block is a Gram matrix for every finite complex square matrix; the fixed nonnormal witness supplies the failure of the equivalence. |
| Equivalence for $1/2\le a<1$ | Proved in Lean: below_one proves claimBelowOne. | Every finite dimension, including zero, every complex square matrix, including singular matrices. |
| Failure mechanism | Proved in prose and used by Lean: the endpoint has constant lower-right power $x^0=1$, while below one the positive exponent is injective on nonnegative singular values. | Endpoint versus strict interval. |
| Whole source interval $0\le a<1$ | Proved in this delivery for the upper half; literature reading for the lower half: published Theorem 2.3 covers $0\le a\le1/2$. | The lower half was not independently formalized here; the combined equivalence is stated with that boundary. |
| Correction to #18699 | Proved in prose: $g(x)=x^{2(1-a)}$ is injective on $[0,\infty)$ for $a<1$ in this range and is constant at $a=1$. | The endpoint qualification corrects the corresponding open-case discussion. |
| Infinite-dimensional operators | Open: no statement is made by the delivered declarations. | Operators on infinite-dimensional spaces are outside the finite-matrix theorem. |
| Parameters outside $[0,1]$ | Open: no statement is made by the delivered declarations. | The source interval is the only parameter range settled here. |
| Literature novelty beyond the supplied screen | ASSUMED-UNVERIFIED: the issue's literature screen is the evidence boundary. | Completeness of later literature checking is not claimed. |

### Triage coverage

| Target item | Dossier evidence | Status | Evidence kind |
| --- | --- | --- | --- |
| Refuted at $a=1$; proved for $1/2\le a<1$, singular matrices included | What the settlement shows, first two rows | proved | kernel-checked declarations result and below_one |
| Together with published Theorem 2.3 for $0\le a\le1/2$, equivalence throughout $0\le a<1$ | What the settlement shows, whole-source row | proved for the upper half; literature reading for the lower half | kernel-checked upper-half theorem plus source reading |
| $g(x)=x^{2(1-a)}$ injective for $a<1$ and constant at $a=1$ | What the settlement shows, correction row | proved | proof mechanism in the delivered argument and source correction |
| Infinite-dimensional operators | What the settlement shows, open row | open | scope boundary |
| Parameters outside $[0,1]$ | What the settlement shows, open row | open | scope boundary |
| Literature novelty beyond the supplied screen | What the settlement shows, final row | ASSUMED-UNVERIFIED | literature screen |

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source was screened together with the literature named in issue #18757; later articles listed there were not independently read beyond the recorded screen. No priority or exhaustive novelty claim is made.

