---
slug: zhang-jing-2025-block-normality-question-2-14
bibkey: zhangjing2025positive
doi: 10.13001/ela.2025.9201
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result
url: https://doi.org/10.13001/ela.2025.9201
---

# Zhang–Jing Question 2.14: block positivity and normality

## Problem

Feng Zhang and Hefang Jing, *More inequalities for positive semidefinite matrices*, Electronic Journal of Linear Algebra 41 (2025), 595–601, Question 2.14, p. 601:

> Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) and g(x) ≥ f(x) (0 ≤ x ≤ 1).

The notation on p. 595 is “|A| = (A*A)^{1/2} and A* is the conjugate transpose of A”. The assertion quantifies over every admissible pair of real functions, every natural dimension, and every complex matrix in that dimension. Preregistration: [#18699](https://github.com/the-omega-institute/trureturing/issues/18699).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $|A|=(A^*A)^{1/2}$ | `CFC.sqrt` of the conjugate-transpose product, inlined in `block` | Literal expression; the existing `CFC.abs` construction is not redeclared. |
| Four displayed blocks, in their given order | `block`, using `Matrix.fromBlocks` and `cfc` | Every block is retained. |
| $f(x)g(x)=x^2$ for $x\ge0$ | First quantified premise of `claim` | Same range and equality. |
| $f(x)\ge g(x)$ for $x\ge1$ | Second quantified premise | Same inequality and range. |
| $g(x)\ge f(x)$ for $0\le x\le1$ | Third quantified premise | Both endpoints included. |
| Every $A\in M_n$, block nonnegative iff $A$ normal | Final quantifiers and equivalence in `claim` | `Fin n` labels the indices; positivity is `Matrix.PosSemidef` and normality is $A^*A=AA^*$. |
| The universal assertion is false | `result` | Its conclusion is the literal negation of `claim`. |

No continuity, invertibility or spectral injectivity premise is added. The counterexample functions are continuous and satisfy the three required scalar conditions.

## Motivation

The settling declaration is `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result`. It refutes the universal equivalence using one fixed two-dimensional matrix. Its admission basis is `open-problem-resolution (#18699; Refuted)`.

## Gap

The scalar conditions permit two distinct positive singular values to have the same value under $g$. Commuting with $g(|A|)$ consequently need not force commuting with $|A|$.

## Route

Set $g(x)=1+(x-1)/(1+(x-1)^2)$ and $f(x)=x^2/g(x)$. Take $A=\begin{pmatrix}0&3/2\\3&0\end{pmatrix}$. The proof verifies all three scalar conditions, obtains $|A|=\operatorname{diag}(3,3/2)$ using `CFC.sqrt_unique`, and applies the frozen `EntropyProductionCoherenceDeletionIdentity.cfc_diagonal` to evaluate both functional calculi. It verifies the block identity $M=(5/7)Q^*Q$, where $Q=[A,(7/5)I]$, and applies `Matrix.posSemidef_conjTranspose_mul_self`. The unequal $(0,0)$ entries of $A^*A$ and $AA^*$ contradict normality.

## Falsifier

The refutation would fail if the scalar premises, square-root identification or Gram identity failed. They are checked inside `result`; the theorem has no additional hypotheses. No family-level or injectivity classification is claimed as a Lean theorem.

## Evidence

The Lean module and its Blueprint mirror give the fixed-instance refutation. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment: [zhang-jing-2025-question-2-14 at `3324a54f7ffe4ef83526feecd6983cc5b30cda06`](https://github.com/the-omega-institute/trureturing-experiments/tree/3324a54f7ffe4ef83526feecd6983cc5b30cda06/docs/reports/zhang-jing-2025-question-2-14). Command: `python3 check.py` in that directory; exit 0. Script SHA-256: `0f3353dca9ba3cf9f1f1fe34d524ea1e07756e3dae7ad117701ac124f7f8cb4d`.

The computation checks admissibility on a grid in $[0,20]$; exactly verifies $|A|=\operatorname{diag}(3,3/2)$, nonnormality, $g(3)=g(3/2)=7/5$ and $cM=Q^{\mathsf T}Q$ at $s=2$; numerically checks block positivity and nonnormality for $s\in\{1.5,2,3,5,10,100\}$; and obtains minimum eigenvalue $-0.387192$ for the contrast $f(x)=x^{3/2}$, $g(x)=x^{1/2}$ at $s=2$. The finite grid and six numerical matrices do not prove uniform claims.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Settlement | **Proved in Lean:** `result` refutes `claim`. | One admissible pair and $n=2$ suffice to disprove the universal equivalence. |
| Failure mechanism | **Proved in prose:** the explicit evaluations in Route give $g(3)=g(3/2)=7/5$, $M=(5/7)Q^*Q$, and unequal normality entries $9$ and $9/4$. | Explains the fixed witness; these evaluations occur inside `result`, without separate named theorems. |
| Exact $s=2$ certificate | **Computed:** the experiment's exact rational check in Evidence. | Only $s=2$. |
| Family checks | **Computed:** positive blocks and nonnormal matrices for the six $s$-values in Evidence. | No uniform conclusion follows from this finite computation. |
| All-$s$ family | **Proved in prose:** the derivation below. | Every real $s>1$; not formalized here. |
| Dimensions $n\ge2$ | **Proved in prose:** direct sums as below. | Not formalized here. |
| Injectivity repair | **Proved in prose:** the invertible Schur-complement argument below, with positivity of $f,g$ on the positive spectrum. | Invertible matrices only; not formalized here. |
| Motivating power cases, invertible matrices | **Proved in prose:** the injectivity argument below. | $1/2\le a<1$; not formalized here. |
| Power endpoint $a=1$ | **Refuted in prose:** the block is the Gram matrix $[A,I]^*[A,I]$ for every $A$. | A nonnormal $A$ disproves the endpoint. |
| Motivating power cases, singular matrices | **Open in this delivery:** tracked separately in #18757. | $1/2\le a<1$. |
| Singular-case classification | **Open:** no classification is proved here. | The invertible argument uses inverses. |
| Positivity at zero | **Proved in prose:** $g(0)=1/2$ and $f(0)=0$ by substitution; $g>0$ and $f>0$ for $x>0$. | The claim requires precisely the three scalar conditions; it requires no strict positivity at zero. |
| Other results in the source | **Literature reading:** Theorem 2.3 covers $0\le a\le1/2$; the question is the concluding extension question. | Refuting the question does not refute that stated theorem. Its proposed extension at $a=1$ fails. |
| Literature status | **ASSUMED-UNVERIFIED:** the screen in #18699 found no settlement in its searched scope. | Later listed articles and completeness remain unverified. |

### Prose derivations and surviving statements

For $t=x-1$, $(t\mp1)^2\ge0$ gives $|t|/(1+t^2)\le1/2$, hence $1/2\le g(x)\le3/2$. Also $g(x)-x=(1-x)(x-1)^2/(1+(x-1)^2)$. Thus $0<g(x)\le x$ for $x\ge1$ and $g(x)\ge x\ge0$ for $0\le x\le1$. Dividing the corresponding square inequalities by positive $g(x)$ proves the two required inequalities for $f=x^2/g$; the product condition follows immediately.

For $s>1$, put $a=1+s$, $b=1+1/s$, $A_s=\begin{pmatrix}0&b\\a&0\end{pmatrix}$, $D=\operatorname{diag}(a,b)$ and $c=1+s/(1+s^2)>0$. Then $a>b>1$, $|A_s|=D$, $g(a)=g(b)=c$, and $f(D)=D^2/c$. The block row $Q=[A_s,cI]$ satisfies $Q^*Q=cM$, so $M\ge0$. Yet $A_s^*A_s=\operatorname{diag}(a^2,b^2)\ne\operatorname{diag}(b^2,a^2)=A_sA_s^*$. For higher dimensions append identity scalar blocks to $A_s$: $f(1)=g(1)=1$, the extra source blocks are positive semidefinite, and a simultaneous index permutation presents their direct sum with $M$. The unequal entries persist.

For invertible $A=UD$ with positive $D=|A|$ and unitary $U$, assume $f,g>0$ on the spectrum and $fg=x^2$. Write $F=f(D)$ and $G=g(D)$. Since $DF^{-1}D=G$, the Schur complement says $M\ge0$ iff $G-UGU^*\ge0$. Its trace is zero; a positive semidefinite matrix of trace zero is zero. Therefore $M\ge0$ iff $UG=GU$. If $g$ is injective on the finite spectrum of $D$, polynomial interpolation expresses $D$ as a polynomial in $G$, so $UG=GU$ implies $UD=DU$, equivalently normality. Conversely, normality gives commutation and a zero Schur complement. A collision $g(a)=g(b)$ at distinct positive $a,b$ permits a swapping unitary on those two eigenspaces and disproves the universal equivalence. This is a prose argument, not a Lean classification theorem.

For $f(x)=x^{2a}$ and $g(x)=x^{2(1-a)}$, $1/2\le a<1$ makes $g$ strictly increasing on $(0,\infty)$, so the invertible repair applies. At $a=1$, $g=1$ and $f=x^2$; the block is $[A,I]^*[A,I]$ for every $A$, so any nonnormal $A$ refutes the endpoint. For normal matrices, simultaneous diagonalization reduces the block to scalar positive semidefinite $2\times2$ blocks whenever $f,g\ge0$ on the spectrum and $fg=x^2$; this survives without invertibility under these nonnegativity assumptions. No statement here classifies the singular converse.

## ASSUMED-UNVERIFIED

The source and literature screen are recorded in #18699. Literature completeness is ASSUMED-UNVERIFIED. The later articles DOI 10.1002/mma.70420, DOI 10.1007/s13226-026-00949-z and DOI 10.1007/s13226-026-00960-4 were not independently read by this implementation seat. No claim of exhaustive novelty is made. The all-$s$, direct-sum, Schur-complement, interpolation and power-case arguments above are prose proofs; the delivered Lean theorem proves the universal assertion false using its fixed witness.
