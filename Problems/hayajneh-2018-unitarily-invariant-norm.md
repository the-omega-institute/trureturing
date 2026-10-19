---
slug: hayajneh-2018-unitarily-invariant-norm
bibkey: hayajneh2018uinorm
doi: 10.7153/mia-2018-21-81
url: https://doi.org/10.7153/mia-2018-21-81
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result
---

# Hayajneh–Hayajneh–Kittaneh: mixed-power monotonicity for unitarily invariant norms

## Problem

M. Hayajneh, S. Hayajneh and F. Kittaneh, *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*, *Mathematical Inequalities & Applications* 21(4) (2018), 1175–1183, DOI 10.7153/mia-2018-21-81, §1, Conjecture 1, printed p. 1177. See [hayajneh2018uinorm](../Library/Eigenstructure/hayajneh2018uinorm.md).

> CONJECTURE 1. Let A be a positive semidefinite matrix and B be a Hermitian matrix. Then for 1/2 ⩽ s ⩽ t ⩽ 1 and for every unitarily invariant norm, we have |||A^s B + BA^{1−s}||| ⩽ |||A^t B + BA^{1−t}|||.

The formal statement retains every quantifier: every natural dimension $n$, all $A,B\in M_n(\mathbb C)$ with $A$ positive semidefinite and $B$ Hermitian, all real $1/2\le s\le t\le1$, and every unitarily invariant norm on $M_n(\mathbb C)$. Real powers are interpreted by continuous functional calculus. No lower spectral bound $A\ge I$ is part of the conjecture.

## Motivation

The source proves this monotonicity for the Hilbert–Schmidt norm and proves the endpoint $s=1/2,t=1$ for every unitarily invariant norm. Conjecture 1 asks whether these special cases extend to every allowed parameter pair and every such norm.

## Gap

Hilbert–Schmidt control does not force the sum of singular values to increase. The trace norm detects a strict decrease even for positive definite $A$ and $B$ in dimension two.

## Route

Set

$$
A=\begin{pmatrix}1/81&0\\0&1\end{pmatrix},\qquad
B=\begin{pmatrix}1&3/4\\3/4&1\end{pmatrix},\qquad s=\frac12,\quad t=\frac34.
$$

Their eigenvalues are $1/81,1$ and $1/4,7/4$, so the required positivity and Hermitian conditions hold. Diagonal functional calculus yields powers $\operatorname{diag}(1/9,1)$, $\operatorname{diag}(1/3,1)$ and $\operatorname{diag}(1/27,1)$ at exponents $1/2,1/4,3/4$. Therefore

$$
L=A^{1/2}B+BA^{1/2}=\begin{pmatrix}2/9&5/6\\5/6&2\end{pmatrix},\qquad
R=A^{3/4}B+BA^{1/4}=\begin{pmatrix}10/27&7/9\\1&2\end{pmatrix}.
$$

For every complex two by two matrix $T$,

$$
\|T\|_1^2=\operatorname{tr}(T^*T)+2|\det T|.
$$

Using $\det L=-1/4$ and $\det R=-1/27$ gives

$$
\|L\|_1^2=\frac{481}{81},\qquad
\|R\|_1^2=\frac{4240}{729},\qquad
\|L\|_1^2-\|R\|_1^2=\frac{89}{729}>0.
$$

## Falsifier

The trace norm is a unitarily invariant norm and both norms are nonnegative. Hence $\|L\|_1>\|R\|_1$, contradicting the asserted inequality at $n=2$, $s=1/2$, $t=3/4$. No approximation is required for this strict comparison.

## Evidence

`D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result : ¬ conjecture` targets the complete universally quantified conjecture. `D5/S3/Quantum/Schatten/TraceNorm` supplies the trace-norm instance of the unitarily invariant norm interface and the two-dimensional identity used in the comparison. The singular-value sum is the full prefix in dimension two, so the same counterexample refutes the corresponding weak-majorization claim.

## Triage

**PROVED — Refutation of Conjecture 1.** The displayed positive definite pair reverses the trace-norm inequality at $s=1/2,t=3/4$ by an exact difference of squares $89/729$.

**PROVED — The Hilbert–Schmidt case remains valid.** This case is proved in the source, §2; the trace-norm counterexample does not contradict it.

**PROVED — The endpoint $s=1/2,t=1$ remains valid for every unitarily invariant norm.** This case is proved in the source, p. 1179; the counterexample has $t=3/4$.

**COMPUTED — Schatten $p\in\{1.5,2,3,\infty\}$ do not fail for this pair.** Numerical values $(\|L\|_p,\|R\|_p)$ are approximately $(2.34487039,2.39704819)$, $(2.33201021,2.39627054)$, $(2.32961548,2.39622090)$ and $(2.32953957,2.39622069)$, respectively. These are finite numerical checks, not universal proofs.

**OPEN — Schatten $p\ge2$ on arbitrary admissible inputs.** The displayed finite computation does not decide this restricted universal inequality.

**OPEN — The operator norm on arbitrary admissible inputs.** The operator-norm comparison for this pair does not establish the universal statement.

**PROVED — Weak majorization fails at $k=2$.** The sum of both singular values is the trace norm, and the exact reverse inequality violates the full-prefix comparison.

## ASSUMED-UNVERIFIED

The literature check covered the DOI and title with conjecture/counterexample/proof; "Hayajneh" "Conjecture 1"; and A^s B + BA^{1−s} with unitarily invariant norm. Related work checked: S. Hayajneh, *Filomat* 38(19) (2024), 6891–6896, on a related scalar trace inequality; and Bottazzi–Elencwajg–Larotonda–Varela, arXiv:1403.7472, on A^tB^{1−t} + B^tA^{1−t}. No settlement of Conjecture 1 was found within that scope. Citation indexes were not exhaustively checked. Absence of subsequent settlements and worldwide priority are not established. The universal Schatten $p\ge2$ and operator-norm restrictions are not settled by this result.
