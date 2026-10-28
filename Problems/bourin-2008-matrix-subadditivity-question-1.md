---
slug: bourin-2008-matrix-subadditivity-question-1
bibkey: bourin2008matrixsubadditivity
doi: 10.1142/S0129167X09005509
url: https://arxiv.org/abs/0805.1954v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result
---

# Bourin's matrix subadditivity Question 1

## Problem

Jean-Christophe Bourin, *Matrix subadditivity inequalities and block-matrices*, arXiv:0805.1954v1, p. 3, Question 1; published as *Matrix subadditivity inequalities and block-matrices*, International Journal of Mathematics 20 (2009), 679–691, DOI 10.1142/S0129167X09005509. The source note is [bourin2008matrixsubadditivity](../Library/QuantumContext/bourin2008matrixsubadditivity.md).

> Let Φ : M_n → M_k be a positive linear map between the algebras of matrices of size n and k and let F_n and F_k be the sets of non-expansive, positive operators in M_n and M_k respectively. Does Φ⁻¹(F_k) ⊂ F_n imply ‖f ∘ Φ(M)‖ ≤ ‖Φ ∘ f(M)‖ for all M ≥ 0, all symmetric norms and all non-negative concave functions on the positive half line?

The matrix algebras are over $\mathbb C$. Write $F_j=\{X:0\preceq X\preceq I_j\}$. The inclusion means non-strict set inclusion, and the inverse image is taken in the entire domain algebra. A symmetric norm is invariant under left and right multiplication by unitaries. The preregistration is [#18573](https://github.com/the-omega-institute/trureturing/issues/18573).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Matrix sizes $n,k$ and positive linear map $\Phi:M_n\to M_k$ | `claim` quantifies over natural sizes and complex `LinearMap`; its first premise is positivity | All sizes and all positive maps |
| $\Phi^{-1}(F_k)\subseteq F_n$ | Full-domain preimage of the literal sets $\{X\mid 0\le X\land X\le1\}$ | No extra predicate or domain restriction |
| Every $M\ge0$ | Universal matrix binder and nonnegativity premise | Loewner order |
| Every symmetric norm | Frozen `D5.S3.Quantum.Schatten.UINorm k` and its field `N` | The six preregistered norm and two-sided unitary-invariance laws |
| Every nonnegative concave function on the positive half line | Real function, `ConcaveOn` on `Set.Ici 0`, pointwise nonnegativity there | Both function premises retained |
| $\|f(\Phi(M))\|\le\|\Phi(f(M))\|$ | Norm evaluations of the two `cfc` expressions in `claim` | Same inequality direction |

There is no additional public hypothesis. The positive-contraction condition is inlined literally; the existing `UINorm` supplies the preregistered norm structure.

## Motivation

The question asks whether reflecting positive contractions suffices to extend an expansive-congruence inequality to positive linear maps. The negative answer distinguishes control of one amplification block from control of a norm that measures every block.

## Gap

The reflection condition controls membership in $F_n$, but does not require every output block to have an expansive weight. The source asks this question explicitly. The literature screen in #18573 found no answer in the searched later works; completeness remains `ASSUMED-UNVERIFIED`.

## Route

Take $n=1$, $k=2$, $\Phi(x)=\operatorname{diag}(x,x/4)$, $M=1$ and $f(t)=\sqrt t$. Positivity of $\Phi$ follows entrywise. The first diagonal entry of $\Phi(x)$ gives both $x\ge0$ and $x\le1$ whenever $\Phi(x)\in F_2$.

The functional-calculus values are

$$f(\Phi(1))=\operatorname{diag}(1,1/2),\qquad
\Phi(f(1))=\operatorname{diag}(1,1/4).$$

Their squared Frobenius norms are $5/4$ and $17/16$. Since $5/4>17/16$, the proposed inequality fails. The Frobenius norm is packaged with the frozen `UINorm` laws. The proof applies `CommutatorGap.frobSq_unitary_left`, `CommutatorGap.frobSq_unitary_right`, `GNSMatrix.frobenius_norm_sq_eq_trace`, and `EntropyProductionCoherenceDeletionIdentity.cfc_diagonal` through their imported owners.

## Falsifier

A failure of positivity, contraction reflection, the functional-calculus evaluations, the symmetric-norm laws or the strict numerical inequality would invalidate this witness. The kernel-checked `result` proves the negation of the complete public `claim`, with no additional hypotheses.

## Evidence

The settling declaration is `D5.S3.Quantum.Schatten.BourinQuestionOneRefutation.result`. Its conclusion is the literal negation of `claim`. All proof steps are instantiation and normalization of existing results; admission is `open-problem-resolution (#18573; Refuted)`. There is no claimed escape witness.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Declaration judgement

Names below are in `D5.S3.Quantum.Schatten.BourinQuestionOneRefutation`. All helpers are private. The consumer map is obtained from elaborated type and value constants; same-delivery helpers are expanded for the judgement.

| Declaration | Kind | proof_shape | escape_witness | Consumer |
| --- | --- | --- | --- | --- |
| `claim` | Public definition | bind-only laws | none | `result` |
| `phi` | Private definition | bind-only laws | none | `phi_positive`, `phi_reflect`, `cfc_phi_one`, `result` |
| `frobeniusNorm` | Private definition | bind-only laws | none | `result` |
| `phi_positive` | Private theorem | bind-only | none | `result` |
| `phi_reflect` | Private theorem | bind-only | none | `result` |
| `cfc_phi_one` | Private theorem | bind-only | none | `result` |
| `cfc_one` | Private theorem | bind-only | none | `result` |
| `result` | Public theorem | bind-only | none | External Question 1 settlement |

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/e4a97025cfec0f4b281199aa6c48ddfe55a553f5/docs/reports/bourin-2008-question-1-positive-contraction-reflection). Command: `python3 /tmp/op-bq1-experiment.py`, using exactly the pinned `check.py` bytes extracted by `git show`; exit 0. Script SHA-256: `11a92112da69ef903f629b2209e7946195633e65064197971bd195829d06ca3a`.

The fixed witness gives trace norms $1.5$ and $1.25$, Frobenius norms $1.118033988749895$ and $1.0307764064044151$, and operator norms $1$ and $1$. The program also checks 3000 random amplification-weight vectors with seed 20261017, one to four blocks, weights in $[0.05,2.5)$, and one to three input eigenvalues in $[0,5)$. Of these, 2118 with weight sum at least the number of blocks satisfy its tested inequalities for five concave functions and every Ky Fan norm; 882 with smaller weight sum fail at the program's selected truncated-linear witness. The five functions are $\sqrt t$, $\min(t,1)$, $\log(1+t)$, $t^{0.3}$ and $t/(1+t)$; Ky Fan comparisons use additive tolerance $10^{-10}$. An additional 2000 random weight vectors in the same block and weight ranges check the scalar comparison $1/\max_i a_i\le1\iff\max_i a_i\ge1$. These are finite computations, not a proof of a uniform amplification classification.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Conclusion and boundary |
| --- | --- | --- |
| Reflection versus the small block; exact Frobenius failure | Kernel-checked: private `phi_positive`, `phi_reflect`, `cfc_phi_one`, `cfc_one`, consumed by public `result` | The first block certifies the reflection premise; $\sqrt{1/4}=1/2$ enlarges the second block. `result` rejects the universal symmetric-norm inequality. |
| Operator norm on the fixed witness | Computed: pinned experiment above, exit 0 | Both matrices have operator norm $1$. This witness does not refute the operator-norm restriction. |
| General amplification-weight classification and complete positivity | Open as formalization; the finite experiment has exactly the tested scope above | Neither a uniform classification theorem nor a complete-positivity theorem is supplied by this module or used by `result`. |
| Scope of the settlement | Kernel-checked: `result` under `claim`'s binding conventions | The verbatim Question 1 is refuted. Question 2 and stronger replacement hypotheses remain outside this conclusion. |

The mechanism is that a positive-contraction test reads the first block, while the Frobenius norm also reads the smaller block. Proved in prose for this witness: $0\le x\le1$ implies $\Phi(x)\in F_2$, and the first block gives the converse, so $\Phi^{-1}(F_2)=F_1$. This equality is an explanatory strengthening of the inclusion actually used in Lean.

The operator-norm equality is also explained by the diagonal entries: each positive diagonal matrix has largest entry $1$. A restriction of the original claim to the operator norm is a separate question, left open here. Bourin's Theorem 1.1a assumes an expansive congruence; that hypothesis is different from contraction reflection, so this witness supplies no counterexample to that theorem. No claim that depends on a positive answer to Question 1 is used; this settlement gives no conclusion about Question 2.

## ASSUMED-UNVERIFIED

Literature-screen completeness and originality of this negative answer are `ASSUMED-UNVERIFIED`. The screen recorded in #18573 reads arXiv:0805.1954v1 and searches arXiv:0906.1447, arXiv:1109.2384, arXiv:1012.5171 and arXiv:2307.03064 for Question 1 and its inverse-image hypothesis. The additional Bourin–Hirzallah–Kittaneh and Bourin–Lee readings are reported by the search seat in that issue. Other answers to questions of Bourin cited there have different hypotheses.

The general amplification classification, the complete-positivity label and any universal replacement condition are unverified here. The experiment proves no statement beyond its finite tested cases; the kernel-checked settlement uses only the fixed positive map and Frobenius witness.
