---
slug: johnson-mondal-tsatsomeros-2026-sidm-pick-refutation
bibkey: johnson2026powersroots
doi: 10.48550/arXiv.2609.06298
url: https://arxiv.org/abs/2609.06298v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result
---

# Pick functions do not preserve strong infinite divisibility

## Problem

C. R. Johnson, S. Mondal, and M. J. Tsatsomeros, *Powers, Roots, and Positivity*, arXiv:2609.06298v1, §1, ask verbatim:

> Given A ∈ C and a Pick function f, is f[A] ∈ C?

Table 2, “Behavior of Matrix Classes under Pick Functions and Fractional Powers”, p. 22, row 12 reads verbatim:

> Strongly Infinitely Divisible Matrix (SIDM) | Open | Yes

The note below the table states verbatim:

> The entries marked Open indicate cases for which preservation under Pick functions remains an open question.

Definition 2.7 states verbatim:

> Let D := C\(−∞, 0]. A complex function f analytic on D is called a Pick function if ℑf(z) ℑz ≥ 0, ∀z ∈ D

Definition 3.25 states verbatim:

> A nonnegative matrix A ∈ Mn(R) is said to be an infinitely divisible matrix (IDM) if, for every positive integer m, there exists a nonnegative matrix Km such that (Km)^m = A. If, in addition, A is invertible, then A is called a strongly infinitely divisible matrix (SIDM).

## Motivation

Fractional powers preserve SIDM according to row 12. A Pick function positive on the positive real axis is a broader test of whether a matrix class retains entrywise nonnegativity and nonnegative roots.

## Gap

The source marks preservation under Pick functions as open. A single upper-triangular SIDM with positive diagonal whose image has a negative entry refutes preservation, even when the function is positive on $(0,\infty)$. Such a matrix has spectrum equal to its diagonal, inside $(0,\infty)\subset D$, as required by Remark 2.9. The general preservation statement would imply this restriction, so refuting the restriction refutes the general statement.

## Route

Choose $f(z)=2z/(1+z)=1+(z-1)/(1+z)$. In Lemma 2.8 this is $a=1$, $b=0$, and $\mu=\delta_1$. It is analytic on $D$, satisfies $\operatorname{Im}f(z)=2\operatorname{Im}z/|1+z|^2$, and is positive for positive real $z$.

For the $4\times4$ shift $N$, take

$$
E(s)=\begin{pmatrix}
1&s&s^2/2&s^3/6\\
0&1&s&s^2/2\\
0&0&1&s\\
0&0&0&1
\end{pmatrix},\qquad A=E(1).
$$

$E(s)E(u)=E(s+u)$ and $E(0)=I$ imply $E(s)^m=E(ms)$. For $m>0$, $E(1/m)$ is a nonnegative $m$th root of $A$. Since $\det A=1$, $A$ is SIDM. It is upper triangular with diagonal 1, so its spectrum is $\{1\}\subset(0,\infty)\subset D$ and it satisfies the matrix restriction.

## Falsifier

The shifted matrix has determinant 16 and inverse

$$
C=(A+I)^{-1}=\begin{pmatrix}
1/2&-1/4&0&1/48\\
0&1/2&-1/4&0\\
0&0&1/2&-1/4\\
0&0&0&1/2
\end{pmatrix}.
$$

Remark 2.9 yields

$$
f[A]=2I-2C=\begin{pmatrix}
1&1/2&0&-1/24\\
0&1&1/2&0\\
0&0&1&1/2\\
0&0&0&1
\end{pmatrix}.
$$

The $(1,4)$ entry is negative, so $f[A]$ is not SIDM.

## Evidence

The public declarations in `D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.lean` are `IsSIDM`, `pickFun`, `pickCalc`, `claim`, and `result`. All matrices and supporting lemmas are private. `IsSIDM` requires entrywise nonnegativity, a unit determinant, and nonnegative roots of every positive integer order.

`pickFun` and `pickCalc` encode the finite-sum instances of Lemma 2.8 and Remark 2.9. `claim` quantifies over all finite supports with $b\ge0$, positive support points, nonnegative weights, and real-axis positivity. For each upper-triangular SIDM with positive diagonal it asserts the calculated image is SIDM. The spectrum of an upper-triangular matrix is its diagonal, so these matrices have spectrum inside $(0,\infty)\subset D$, satisfying Remark 2.9. Thus the general preservation statement implies this restriction, and refuting it refutes the general statement. The positive diagonal and support points also make every shifted matrix invertible. The theorem `D5.S3.Quantum.Matrix.InfinitelyDivisiblePickRefutation.result` has type `¬ claim`.

The proof verifies the multiplication identity and the root formula for arbitrary positive integers, the determinant 1, upper triangularity and positive diagonal, the explicit right inverse, positivity of $2x/(1+x)$, and the image entry $-1/24$. The module's axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. Complex analyticity, the spectrum description, and the general integral representation are not separately formalized in this module.

## Triage

### What the settlement shows

1. **Proved (Lean) — SIDM preservation fails.** The Pick function $2z/(1+z)$ maps the displayed $4\times4$ SIDM $E(1)$ to a matrix with a negative entry. Under the source's finite-measure functional-calculus identification, Table 2, row 12, therefore has answer No.

2. **Computed (exact mathematical reasoning, not separately formalized) — the mechanism.** On the unipotent matrix $A=e^N$, the finite nilpotent power series gives $f[A]=I+\tanh(N/2)$. The quadratic coefficient vanishes and the cubic coefficient is $-1/24$. Thus order 4 is the first size in this shift family where a negative entry appears. For the $3\times3$ shift, $f[E(1)]=I+N/2$ is nonnegative; this observation alone makes no SIDM assertion for that image.

3. **Computed (numerical, not formalized) — the embeddable neighbor.** For the Markov generator $B=N-\operatorname{diag}(1,1,1,0)$, the same function applied to $e^B$ gives a matrix with row sums 1 and $(1,4)$ entry approximately $-0.0219644568959024$. The value comes from a 64-term exponential series and Gaussian elimination in double precision. Its negative entry means the image is not a stochastic matrix, suggesting that row 13 also has answer No. This computation is not a formal resolution of row 13.

4. **Open — neighboring classes.** Row 7 (semipositive matrices) and row 13 (embeddable matrices) are not settled by this theorem.

## ASSUMED-UNVERIFIED

The supplied source quotations and locators bind to arXiv:2609.06298v1; their agreement with the author text is ASSUMED-UNVERIFIED. No exhaustive literature or priority claim is established. Lemma 2.8 and Remark 2.9 are cited to identify the encoded finite sums with Pick functions and their matrix calculus; the general analytic theory is not formalized here. The Markov-generator computation has no certified error bound or Lean proof.
