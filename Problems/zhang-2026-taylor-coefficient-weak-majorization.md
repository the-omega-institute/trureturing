---
slug: zhang-2026-taylor-coefficient-weak-majorization
bibkey: zhang2026weakmajorizationtaylor
doi: 10.48550/arXiv.2601.07286
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/TaylorMajorization/Result.result
url: https://arxiv.org/abs/2601.07286
---

# Taylor-coefficient weak majorization for Hermitian matrices

## Problem

T. Zhang, *Weak majorization inequalities for the cubic and quartic
coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*, arXiv:2601.07286v1,
Section 5, Conjecture 5.5:

> For A, B ∈ Hₙ and every k ≥ 5, λ(H^k) ≺_w λ(R_k).

Here $H_n$ consists of all complex Hermitian $n\times n$ matrices,
$H=A+B$,

$$Q_k=\sum_{p=0}^k\binom{k}{p}A^pB^{k-p},\qquad
R_k=\operatorname{Re}Q_k=\frac{Q_k+Q_k^*}{2}.$$

The list $\lambda$ is nonincreasing, and $x\prec_w y$ means
$\sum_{i=1}^r x_i\le\sum_{i=1}^r y_i$ for every $1\le r\le n$.
The paper proves the comparisons for $k=3,4$. Its conjecture imposes
no positivity assumption on $A$ or $B$.

### Formal reading

All Lean names below have prefix `D5.S3.Quantum.Matrix.TaylorMajorization`;
the Pauli matrices are from `D5.S3.Quantum.FiniteDimensional`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $H_n$, $n\ge1$ | `Matrix (Fin n) (Fin n) ℂ`, `Matrix.IsHermitian` | `Defs.claim` explicitly requires `1 ≤ n` and both Hermitian hypotheses. |
| $Q_k$ | `Defs.taylorQ` | The ordered binomial sum, with the $A$ powers on the left. |
| $R_k$ | `Defs.taylorR` | Complex Hermitian symmetrization; `Defs.taylorR_isHermitian` supplies its Hermitian proof. |
| $\lambda$, $\prec_w$ | `Defs.weakMaj` | Mathlib's nonincreasing `eigenvalues₀`, compared by all initial sums up to $n$. The extra $r=0$ sum is automatically zero. |
| All dimensions, inputs, orders and partial sums | `Defs.claim` | Every natural $n\ge1$, Hermitian $A,B$, natural $k\ge5$ and $1\le r\le n$. |
| $\Delta_k=\operatorname{Tr}R_k-\operatorname{Tr}(A+B)^k$ | `Defs.defect` | Real parts of traces; both compared matrices are Hermitian, so their traces are real. |
| $Z=\operatorname{diag}(1,-1)$, $X=\left[\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right]$ | `qubitZ`, `qubitX` | The existing two-dimensional Pauli matrices. |
| Refutation | `Result.result` | Exactly `¬ Defs.claim`, without additional assumptions. |

## Motivation

The settling declaration is
`D5/S3/Quantum/Matrix/TaylorMajorization/Result.result`.
The source note is `D5/L/Eigenstructure/zhang2026weakmajorizationtaylor`.
The question asks whether the cubic and quartic spectral comparisons
extend to every higher Taylor coefficient for arbitrary Hermitian inputs.

## Gap

Status: **Refuted** for the unrestricted Hermitian conjecture.
Already at $n=2$, $k=5$, $A=Z-I$, $B=X$, the full spectral sum has the
opposite strict inequality. Every odd $k\ge5$ and every $A=Z-tI$ with
$t>0$ give the same obstruction. Positive semidefinite inputs and even
orders $k\ge6$ are outside this refutation family.

## Route

Write $\Delta_k(A,B)=\operatorname{Tr}R_k(A,B)-\operatorname{Tr}(A+B)^k$.
Scalar translation gives

$$Q_k(A+sI,B)=\sum_{j=0}^k\binom{k}{j}s^{k-j}Q_j(A,B),\qquad
\Delta_k(A+sI,B)=\sum_{j=0}^k\binom{k}{j}s^{k-j}\Delta_j(A,B).$$

Left multiplication by $A$ and right multiplication by $B$ commute.
Their binomial power, applied to $I$, is $Q_k$; adding $sI$ to $A$
adds the scalar identity to this endomorphism. Taking real traces and
subtracting the ordinary binomial transform of $(A+B)^k$ proves the
second identity for real $s$.

For the Pauli pair, $Z^2=X^2=I$ and $ZX=-XZ$. The product traces reduce
to the four parity cases, while $(Z+X)^2=2I$. Consequently

$$\Delta_0(Z,X)=0,\qquad \Delta_{2m+1}(Z,X)=0,\qquad
\Delta_{2m}(Z,X)=4^m-2^{m+1}\quad(m\ge1).$$

For odd $k\ge5$ and $t>0$, the translation identity becomes

$$\Delta_k(Z-tI,X)=-\sum_{m=2}^{(k-1)/2}
\binom{k}{2m}t^{k-2m}(4^m-2^{m+1})<0.$$

Every summand inside the minus sign is nonnegative, and the $m=2$
summand is strictly positive. The $r=n$ instance of weak majorization
is the trace inequality, which this negative defect contradicts.

## Falsifier

The universal claim requires a nonnegative defect for every permitted
input and order. The concrete Hermitian inputs $A=Z-I$, $B=X$ give
$\Delta_5=-40$, a strict violation at the full initial sum $r=n=2$.
The eigenvalue ordering cannot remove a failure of the full sum.

## Evidence

`D5/S3/Quantum/Matrix/TaylorMajorization/Result.result` proves exactly
`¬ Defs.claim`. Its principal dependencies are `Defs.weakMaj_trace`
and `Pauli.defect_shift_negative`. The family theorem consumes
`Shift.defect_shift`, `Shift.taylorQ_shift`, `Shift.trace_taylorR`,
`Pauli.defect_even` and `Pauli.defect_odd`, together with the private
Pauli moment and power reductions. Existing dependencies include
`FiniteDimensional.qubit_weyl_star`,
`StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair`,
`Commute.add_pow'`, `RHLinalg.rtrace_eq_sum_eigenvalues`,
`RHLinalg.sum_eigenvalues_reindex` and `IncoherentCone.trace_hermitianPart`.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The refutation route was derived with the assistance of the ChatGPT Pro model.
The searched literature scope includes the source identifier, title,
author and counterexample searches. The source proves $k=3,4$ and gives
a sufficient commutator-decomposition condition for higher $k$;
no settlement of Conjecture 5.5 was found in that scope.
The nearby arXiv:2609.09749 concerns Huang's Hadamard-product
weak-majorization conjecture, a different statement. These results do
not establish exhaustive literature coverage or priority.

## Triage

- **PROVED.** For $Z=\operatorname{diag}(1,-1)$,
  $X=\left[\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right]$,
  every odd $k\ge5$ and every $t>0$,
  $\operatorname{Tr}R_k(Z-tI,X)<\operatorname{Tr}(Z-tI+X)^k$.
  Thus the $r=n$ inequality fails, by `Pauli.defect_shift_negative`
  and `Result.result`.
- **PROVED.** Translation covariance of $Q_k$ and of the trace defect
  is `Shift.taylorQ_shift` and `Shift.defect_shift`.
- **PROVED in prose.** For every non-commuting Hermitian pair and every
  odd $k\ge5$, a sufficiently negative scalar shift violates the
  comparison. Cyclicity of trace gives $\Delta_j=0$ for $0\le j\le3$
  and $\Delta_4=2\operatorname{Tr}(A^2B^2-ABAB)
  =\|AB-BA\|_F^2>0$, where $\|C\|_F^2=\operatorname{Tr}(C^*C)$.
  In the translation polynomial with $s=-t$, the leading nonzero term
  is $-\binom{k}{4}\|AB-BA\|_F^2t^{k-4}$; every remaining term has
  lower degree. It is therefore negative for all sufficiently large
  $t>0$. For commuting Hermitian pairs the binomial theorem gives
  $Q_k=(A+B)^k=R_k$ for every order and every real scalar shift,
  hence equality of all spectral partial sums.
- **COMPUTED.** Exact rational matrix arithmetic gives
  $\Delta_5(Z-I,X)=-40$, $\Delta_7(Z-I,X)=-616$ and
  $\Delta_9(Z-I,X)=-7056$.
- **OPEN.** The even orders $k\ge6$, the conjecture under positive
  semidefiniteness of $A$ and $B$, and the source's singular-value
  Problem 1.1 are not settled here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded search scope does not imply that no other
settlement exists. The general commutator argument above is a prose
proof; the Lean refutation uses the exact shifted Pauli family.
