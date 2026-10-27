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
| $1/2\le a<1$ survives | The owning Scribe displays the full strict-interval quantified application | Both directions, singular matrices, the half endpoint and dimension zero are retained as an application of canonical suppliers. |
| The closed interval fails | result : \lnot claim | The conclusion is the literal refutation. |

## Motivation

The source left the upper interval open. The settling result is D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result, with admission basis open-problem-resolution (#18757; Refuted at a = 1). The complete positive interval is an application in the same owning Blueprint Scribe, not a retained companion declaration.

## Gap

At $a=1$, the lower-right power is $x^0=1$, so the block is positive semidefinite for every matrix. The interval therefore needs a sharp endpoint distinction. For $a<1$, the positive exponent $2(1-a)$ makes the scalar power injective on nonnegative singular values.

## Route

The proof uses a finite singular-value decomposition $A=VDW^*$ with nonnegative diagonal $D$. It transports the block by unitary coordinates to diagonal powers and a unitary conjugate. A block congruence, without an invertible Schur-complement assumption, gives a positive-semidefinite difference whose trace is zero, hence the difference vanishes. Injectivity of the positive real power forces the conjugating unitary to commute with $D$, which is equivalent to normality. The converse writes the balanced diagonal block as a Gram matrix. The endpoint uses the Gram identity for $[A,I]$ and a fixed nonnormal matrix.

## Falsifier

The refutation would fail if result did not prove the negation of the full closed-interval claim, or if the strict-interval application failed to establish both directions with singular matrices, the half endpoint and dimension zero included. The exact temporary application must compile from canonical suppliers and local calculations without importing any removed positive helper; until then its bridge is unverified/open. Checkpoints do not certify mathematics.

## Evidence

Current verification boundary: the revised endpoint imports and complete positive application require a successful current scoped check. The existing state pins and a local checkpoint do not certify this revision. The full Renyi equality remains in scope and also requires the current report; no interrupted or mismatched prior report is evidence for it.

The retained Lean refutation and the distinct application are:

- D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result : \lnot claim, the designated refutation result.
- The owning ZhangJingPowerCaseSettlement Scribe displays the literal positive telescope and complete source-to-supplier derivation in both directions. This application has no theorem Describe, GID, resolution marker or registry.

The public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The public canonical CFC supplier's dependent/pointwise arena, exact source reconstruction, whole-family intervention and sensitivity audit remains unfinished under issue #19914; removing a positive application declaration does not settle that historical audit. No declared_validated registration is claimed.

Experiment: zhang-jing-2025-theorem-2-3-power-case at commit 03fcc97da76c2b464b6ab79d8383aa17c8910f07, https://github.com/the-omega-institute/trureturing-experiments/tree/03fcc97da76c2b464b6ab79d8383aa17c8910f07/docs/reports/zhang-jing-2025-theorem-2-3-power-case. Command: python3 check.py; exit 0; script SHA-256 fd68b9499f5e398726827824c3abee5776b1ce07c86a7f7eaae01ed59b8a0b3d. The checked scope is $a\in\{0.5,0.55,0.6,0.75,0.9,0.99\}$, $n\in\{2,3,4\}$, ranks $n,n-1,1$, 1350 random normal/nonnormal pairs, the singular $a=3/4$ example, and the endpoint Gram witness. These recorded computations support the application and endpoint witness; they do not establish a uniform theorem and were not rerun here.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Refutation at $a=1$ | Proved in Lean: result refutes claim. | The block is a Gram matrix for every finite complex square matrix; the fixed nonnormal witness supplies the failure of the equivalence. |
| Equivalence for $1/2\le a<1$ | Application of existing canonical results in the owning Scribe; exact temporary compilation unverified/open. | Every finite dimension, including zero, every complex square matrix, including singular matrices. |
| Failure mechanism | Proved in prose and used by Lean: the endpoint has constant lower-right power $x^0=1$, while below one the positive exponent is injective on nonnegative singular values. | Endpoint versus strict interval. |
| Whole source interval $0\le a<1$ | Derived application for the upper half, with its exact compile still unverified; literature reading for the lower half: published Theorem 2.3 covers $0\le a\le1/2$. | The lower half was not independently formalized here; the combined equivalence is stated with that boundary. |
| Correction to #18699 | Proved in prose: $g(x)=x^{2(1-a)}$ is injective on $[0,\infty)$ for $a<1$ in this range and is constant at $a=1$. | The endpoint qualification corrects the corresponding open-case discussion. |
| Infinite-dimensional operators | Open: no statement is made by the delivered declarations. | Operators on infinite-dimensional spaces are outside the finite-matrix theorem. |
| Parameters outside $[0,1]$ | Open: no statement is made by the delivered declarations. | The source interval is the only parameter range settled here. |
| Literature novelty beyond the supplied screen | ASSUMED-UNVERIFIED: the issue's literature screen is the evidence boundary. | Completeness of later literature checking is not claimed. |

### Triage coverage

| Target item | Dossier evidence | Status | Evidence kind |
| --- | --- | --- | --- |
| Refuted at $a=1$; derived application for $1/2\le a<1$, singular matrices included | What the settlement shows, first two rows | retained refutation; application unverified/open | retained result plus complete supplier application; exact application compilation unverified/open |
| Together with published Theorem 2.3 for $0\le a\le1/2$, equivalence throughout $0\le a<1$ | What the settlement shows, whole-source row | derived upper-half application, exact compilation unverified/open; literature reading for the lower half | canonical-supplier application plus source reading |
| $g(x)=x^{2(1-a)}$ injective for $a<1$ and constant at $a=1$ | What the settlement shows, correction row | proved | proof mechanism in the delivered argument and source correction |
| Infinite-dimensional operators | What the settlement shows, open row | open | scope boundary |
| Parameters outside $[0,1]$ | What the settlement shows, open row | open | scope boundary |
| Literature novelty beyond the supplied screen | What the settlement shows, final row | ASSUMED-UNVERIFIED | literature screen |

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source was screened together with the literature named in issue #18757; later articles listed there were not independently read beyond the recorded screen. No priority or exhaustive novelty claim is made.
