---
bibkey: johnson2026powersroots
authors: C. R. Johnson; S. Mondal; M. J. Tsatsomeros
year: 2026
title: "Powers, Roots, and Positivity"
doi: 10.48550/arXiv.2609.06298
url: https://arxiv.org/abs/2609.06298v1
claim: "The entries marked Open indicate cases for which preservation under Pick functions remains an open question."
strata_touched:
  - D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation
  - D5/S3/Quantum/Matrix/EmbeddablePickRefutation
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2609.06298v1>.
- DOI: https://doi.org/10.48550/arXiv.2609.06298

C. R. Johnson, S. Mondal, and M. J. Tsatsomeros, *Powers, Roots, and Positivity*, arXiv:2609.06298v1, Definition 2.7, Lemma 2.8, Remark 2.9, Definition 3.25, and Table 2, p. 22.

## Pick functions and strong infinite divisibility

Definition 2.7 states verbatim:

> Let D := C\(−∞, 0]. A complex function f analytic on D is called a Pick function if ℑf(z) ℑz ≥ 0, ∀z ∈ D

Definition 3.25 states verbatim:

> A nonnegative matrix A ∈ Mn(R) is said to be an infinitely divisible matrix (IDM) if, for every positive integer m, there exists a nonnegative matrix Km such that (Km)^m = A. If, in addition, A is invertible, then A is called a strongly infinitely divisible matrix (SIDM).

Table 2, “Behavior of Matrix Classes under Pick Functions and Fractional Powers”, p. 22, row 12 reads verbatim:

> Strongly Infinitely Divisible Matrix (SIDM) | Open | Yes

Remark 3.28, p. 17, states verbatim:

> The embedding problem, introduced in [11], asks whether a given stochastic matrix A can be realized as the transition matrix of a continuous-time Markov process. It was shown in [24] that a nonsingular stochastic matrix A is embeddable if and only if A = e^B for some essentially nonnegative matrix B satisfying Be = 0.

Table 2, “Behavior of Matrix Classes under Pick Functions and Fractional Powers”, p. 22, row 13 reads verbatim:

> Embeddable Matrix | Open | Yes

The note below Table 2 states verbatim:

> The entries marked Open indicate cases for which preservation under Pick functions remains an open question.

The framing question in §1 is verbatim:

> Given A ∈ C and a Pick function f, is f[A] ∈ C?

Lemma 2.8 represents a Pick function by

$$
f(z)=a+bz+\int_0^\infty\frac{tz-1}{t+z}\,d\mu(t),
\qquad a\in\mathbb R,\quad b\ge0,\quad\mu\ge0.
$$

Remark 2.9 gives, for spectrum in $D$,

$$
f[A]=aI+bA+\int_0^\infty\left(tI-(1+t^2)(A+tI)^{-1}\right)\,d\mu(t).
$$

## Repository-derived result

The companion theorem `result : ¬ claim` refutes preservation restricted to finitely supported positive measures, functions positive on $(0,\infty)$, and upper-triangular SIDM matrices with positive diagonal. Their spectrum is their diagonal, inside $(0,\infty)\subset D$, so Remark 2.9 applies. The general preservation statement implies this restriction; refuting it therefore refutes the general statement. Take $a=1$, $b=0$, and $\mu=\delta_1$, so $f(z)=2z/(1+z)$. The pole lies outside $D$, and

$$
\operatorname{Im}f(z)=\frac{2\operatorname{Im}z}{|1+z|^2}.
$$

Let $N$ be the $4\times4$ shift with ones on its first superdiagonal and put

$$
E(s)=I+sN+\frac{s^2}{2}N^2+\frac{s^3}{6}N^3,\qquad A=E(1).
$$

The identity $E(s)E(u)=E(s+u)$ supplies nonnegative roots $E(1/m)$ of every positive integer order. The determinant of $A$ is 1, and $A$ is upper triangular with diagonal 1, hence spectrum $\{1\}\subset(0,\infty)\subset D$. Moreover,

$$
(A+I)^{-1}=\frac12I-\frac14N+\frac1{48}N^3,
\qquad f[A]=I+\frac12N-\frac1{24}N^3.
$$

Thus $f[A]_{1,4}=-1/24$, and $f[A]$ is not nonnegative and hence not SIDM. The answer to Table 2, row 12, is No. The Lean module proves the real-axis positivity, roots, determinant 1, upper triangularity, positive diagonal, inverse identity, and negative entry; complex analyticity and the displayed imaginary-part identity are mathematical explanations of the source representation, not separately formalized there.

## Neighboring references

The source's Table 2, rows 7 and 13, concerns semipositive and embeddable matrices. Neither row is settled by the companion theorem.

## ASSUMED-UNVERIFIED

The supplied quotations and locators bind to arXiv:2609.06298v1; their agreement with the author text is ASSUMED-UNVERIFIED. No exhaustive literature or priority claim is established. The finite-measure encoding uses Lemma 2.8 and Remark 2.9; their general analytic statements are cited rather than formalized.
