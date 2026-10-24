---
bibkey: zhangjing2025positive
authors: Feng Zhang; Hefang Jing
year: 2025
title: More inequalities for positive semidefinite matrices
doi: 10.13001/ela.2025.9201
url: https://doi.org/10.13001/ela.2025.9201
claim: Question 2.14 asks whether positivity of the functional-calculus block is equivalent to normality under three scalar conditions on f and g.
strata_touched:
  - D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation
  - D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement
license: citation-only
triage: anchor
---

# More inequalities for positive semidefinite matrices

## Verified locator

DOI: 10.13001/ela.2025.9201

Source: https://doi.org/10.13001/ela.2025.9201

Electronic Journal of Linear Algebra 41 (2025), 595–601. The notation is on p. 595; Question 2.14 is on p. 601.

## Source statement

> |A| = (A*A)^{1/2} and A* is the conjugate transpose of A

> Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) and g(x) ≥ f(x) (0 ≤ x ≤ 1).

The first quotation is the notation on p. 595; the second is Question 2.14 on p. 601. In the formal encoding, the absolute value is `CFC.sqrt (Aᴴ * A)`, scalar functions use `cfc`, the four blocks use `Matrix.fromBlocks`, positivity is `Matrix.PosSemidef`, and normality is `Aᴴ * A = A * Aᴴ`. All admissible scalar pairs, natural dimensions, and complex matrices are quantified.

## Refutation and boundary

The fixed example uses $g(x)=1+(x-1)/(1+(x-1)^2)$, $f(x)=x^2/g(x)$, and $A=\begin{pmatrix}0&3/2\\3&0\end{pmatrix}$. The two distinct singular values $3$ and $3/2$ have the same $g$-value $7/5$. The block has the Gram certificate $(5/7)Q^*Q$ for $Q=[A,(7/5)I]$, while $A^*A\ne AA^*$. Here $f(0)=0$; strict positivity of $f$ is restricted to positive inputs.

This refutes the universal equivalence in Question 2.14. An injectivity repair, the general counterexample family, and the singular-matrix classification are outside this formal statement. The motivating power case at exponent $a=1$ has constant $g$ and must be separated from $1/2\le a<1$.

## Source statements

Notation, p. 595: “|A| = (A*A)^{1/2} and A* is the conjugate transpose of A”.

Theorem 2.3, p. 597: “Let A ∈ M_n. Then [[|A|^{2a}, A*], [A, |A|^{2(1−a)}]] ≥ 0, for 0 ≤ a ≤ 1/2 if and only if A is normal.”

After Remark 2.13, p. 601: “Due to the limitations of our research method, we cannot solve the problem that Theorem 2.3 holds for 1/2 ≤ a ≤ 1.”

The matrix absolute value is `CFC.sqrt (Aᴴ * A)`. Real powers use `Real.rpow`, including the value x⁰ = 1, and matrix functions use the real continuous functional calculus. Normality is `Aᴴ * A = A * Aᴴ`. The formal statements quantify over every natural dimension and all complex square matrices, with no invertibility assumption.

## Mathematical consequences

The repository proves the equivalence for 1/2 ≤ a < 1, including singular matrices. At a = 1 the block is the Gram matrix of [A,I], so it is positive semidefinite for every A. The nonnormal matrix [[0,1],[2,0]] refutes the extension to the closed upper endpoint. The paper's lower interval is cited here and is not independently formalized by this module.

## Supporting computation

The experiment [zhang-jing-2025-question-2-14](https://github.com/the-omega-institute/trureturing-experiments/tree/3324a54f7ffe4ef83526feecd6983cc5b30cda06/docs/reports/zhang-jing-2025-question-2-14) contains the exact rational Gram check and numerical comparisons. Its `check.py` has SHA-256 `0f3353dca9ba3cf9f1f1fe34d524ea1e07756e3dae7ad117701ac124f7f8cb4d`; `python3 check.py` exits 0 with `RESULT PASS`. These computations support the example; the formal refutation is the Lean theorem.

## Literature boundary

Preregistration #18699 records the source reading and literature screen. Completeness and the unsettled status in later literature are ASSUMED-UNVERIFIED. The later articles with DOIs 10.1002/mma.70420, 10.1007/s13226-026-00949-z and 10.1007/s13226-026-00960-4 were not independently read by this implementation seat. No claim of exhaustive novelty is made.
