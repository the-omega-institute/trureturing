---
slug: johnson-mondal-tsatsomeros-2026-embeddable-pick-refutation
bibkey: johnson2026powersroots
doi: 10.48550/arXiv.2609.06298
url: https://arxiv.org/abs/2609.06298v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result
---

# Pick functions do not preserve embeddable matrices

## Problem

C. R. Johnson, S. Mondal, and M. J. Tsatsomeros, *Powers, Roots, and Positivity*, arXiv:2609.06298v1, Table 2, “Behavior of Matrix Classes under Pick Functions and Fractional Powers”, p. 22, row 13 reads verbatim:

> Embeddable Matrix | Open | Yes

The note below the table states verbatim:

> The entries marked Open indicate cases for which preservation under Pick functions remains an open question.

Remark 3.28, p. 17, states verbatim:

> The embedding problem, introduced in [11], asks whether a given stochastic matrix A can be realized as the transition matrix of a continuous-time Markov process. It was shown in [24] that a nonsingular stochastic matrix A is embeddable if and only if A = e^B for some essentially nonnegative matrix B satisfying Be = 0.

## Motivation

Row 13 records preservation by fractional powers. Preservation by positive Pick functions would additionally require entrywise nonnegativity of their images of embeddable stochastic matrices.

## Gap

A single embeddable stochastic matrix with an image having a negative entry disproves preservation. The restriction to upper-triangular matrices with positive diagonal ensures spectrum inside $(0,\infty)\subset D$, as required by Remark 2.9. Refuting this restriction refutes the general preservation statement.

## Route

Let

$$
P=\begin{pmatrix}0&1&0&0\\0&0&1&0\\0&0&0&1\\0&0&0&1\end{pmatrix},
\qquad Q=\begin{pmatrix}0&0&0&1\\0&0&0&1\\0&0&0&1\\0&0&0&1\end{pmatrix}.
$$

The generator $B=P-I$ has nonnegative off-diagonal entries and zero row sums. Since $P^3=Q$ and $QP=Q$, the exponential series gives

$$
A=e^{P-I}=e^{-1}\left(I+P+\tfrac12P^2+(e-\tfrac52)Q\right)
=\begin{pmatrix}
1/e&1/e&1/(2e)&1-5/(2e)\\
0&1/e&1/e&1-2/e\\
0&0&1/e&1-1/e\\
0&0&0&1
\end{pmatrix},\qquad e=\exp(1).
$$

This matrix has nonnegative entries, row sums 1, positive diagonal, and determinant $e^{-3}>0$. It is therefore embeddable in the sense of Remark 3.28. Set $a=1$, $b=0$, $t=(1)$, and $w=(1)$, so $f(z)=2z/(1+z)$. This is the finite-measure representation in Lemma 2.8. Its pole is outside $D$, its imaginary part is $2\operatorname{Im}z/|1+z|^2$, and its real values are positive on $(0,\infty)$.

## Falsifier

Writing $d=1+e$, the explicit inverse is

$$
(A+I)^{-1}=C=\begin{pmatrix}
e/d&-e/d^2&e(1-e)/(2d^3)&(-e^3+2e^2+2e+1)/(2d^3)\\
0&e/d&-e/d^2&(1+2e-e^2)/(2d^2)\\
0&0&e/d&(1-e)/(2d)\\
0&0&0&1/2
\end{pmatrix}.
$$

Exact multiplication verifies $(A+I)C=I$. The Pick calculus gives $f[A]=2I-2C$, hence

$$
f[A]_{1,4}=\frac{e^3-2e^2-2e-1}{(1+e)^3}<0.
$$

The inequality follows from the certified rational bounds $2.718<e<2.72$. Thus $f[A]$ is not stochastic and cannot be embeddable.

## Evidence

`D5/S3/Quantum/Matrix/EmbeddablePickRefutation.lean` defines `IsStochastic`, `IsEmbeddable`, and `claim`, and proves `result : ¬ claim`. The companion frozen module `InfinitelyDivisiblePickRefutation` provides the reused public definitions `pickFun` and `pickCalc`. All witnesses and helper lemmas are private.

The proof checks the power tail, sums the exponential series, uses commutation to identify the generator exponential, and verifies stochasticity, nonsingularity, generator conditions, triangularity, positive diagonal, the explicit inverse, and the negative entry. The matrix exponential is Mathlib's topology-based `NormedSpace.exp`. The designated result has only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; it uses no `sorry` or additional axiom. Complex analyticity, the spectrum description, and the general analytic representation are mathematical explanations rather than separately formalized assertions here.

## Triage

### What the settlement shows

1. **Proved (Lean) — embeddable preservation fails.** `D5/S3/Quantum/Matrix/EmbeddablePickRefutation.result` shows that the embeddable stochastic matrix $e^{P-I}$ is mapped by the positive Pick function $2z/(1+z)$ to a matrix with negative $(1,4)$ entry. Under the source's finite-measure calculus identification, row 13 is answered No.

2. **Reasoning — the shared mechanism.** Rows 12 and 13 share the mechanism that Pick functions positive on $(0,\infty)$ do not preserve entrywise positivity on non-normal matrices. The row-12 theorem uses a nilpotent shift exponential; the present theorem uses an absorbing Markov generator. The exact inverse gives the sign obstruction in each case. These witnesses give no classification of all smaller matrices or all Pick functions.

3. **Open — semipositive matrices.** Row 7 is not settled by these results.

## ASSUMED-UNVERIFIED

No exhaustive literature or priority claim is established. Lemma 2.8 and Remark 2.9 identify the finite sums with Pick functions and their matrix calculus; the general analytic representation is cited rather than formalized. The settlement concerns arXiv:2609.06298v1, Table 2, row 13.
