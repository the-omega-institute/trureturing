---
slug: tang-zhang-2025-real-order-schoenberg
bibkey: tang2025schoenberg
doi: 10.48550/arXiv.2508.10341
url: https://arxiv.org/abs/2508.10341v3
triage: theorem
motivation_gids:
  - D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result
---

# Tang–Zhang: real-order reciprocal critical-point moments

## Source and statement

Q. Tang and T. Zhang, *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*, arXiv:2508.10341v3, Conjecture 1.13. The source locator and requested statement are supplied by the task brief. The preregistration is [issue #18789](https://github.com/the-omega-institute/trureturing/issues/18789). The library reference is [tang2025schoenberg](../Library/Zeros/tang2025schoenberg.md).

For every natural $n\ge1$ and every family $z_1,\ldots,z_n\in\mathbb C\setminus\{0\}$, put

$$
P(Z)=Z\prod_{j=1}^n(Z-z_j),\qquad
c(n,p)=\frac{(n+1)^p+n-1}{n}.
$$

Let $w_1,\ldots,w_n$ be all roots of $P'$, counted with algebraic multiplicity. No distinctness, simplicity, reality or common argument hypothesis is imposed on the nonzero roots. The target consists of all three clauses:

1. For every real $p\ge1$,
   $$\sum_{k=1}^n|w_k|^{-p}\le c(n,p)\sum_{j=1}^n|z_j|^{-p}.$$
2. For every real $p>1$, equality holds if and only if $z_i=z_j$ for every $i,j$.
3. The proposed universal equality characterization at $p=1$ is false: for $n=2$ and $(z_1,z_2)=(1,2)$, equality holds although $z_1\ne z_2$.

The formal `claim` is the conjunction of these clauses. Its third conjunct is exactly the negation of

```lean
∀ (n : ℕ) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
  (((Polynomial.derivative (P z)).roots.map
      (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
    c n 1 * ∑ j, ‖z j‖ ^ (-(1 : ℝ)) ↔ ∀ i j, z i = z j)
```

Every norm power is a real `Real.rpow`; the exponent ranges are real, including nonintegral values. The result targets the corrected complete statement. It does not assert that the source's equality characterization is true at the endpoint.

## Mathematical route

The polynomial and its multiplicity-preserving reciprocal-root spectral reduction are reused from `TangZhangOrderMinusTwo`. With $b_j=1/z_j$, $D=\operatorname{diag}(b_j)$ and $H=I+J$, the matrix $A=H^{1/2}DH^{1/2}$ has characteristic roots $1/w_k$. Since $P'(0)=\prod_j(-z_j)\ne0$, the critical points are nonzero.

The explicit powers

$$
H^\zeta=I+\bigl((n+1)^\zeta-1\bigr)J/n
$$

reduce matrix complex powers to scalar exponential functions. A scalar trace function in a fixed Schur basis has boundary bounds $1$ and $M=c(n,p)\sum_j|b_j|^p$ on the vertical strip. At $\zeta=1/p$, its value is $(\sum_k|1/w_k|^p)^{1/p}$. The three-lines theorem yields the real-order inequality. A rank-one trace estimate gives the endpoint $p=1$.

For $p>1$, interior equality and the maximum modulus principle force equality on the entire right boundary. The rank-one columns have pairwise nonzero inner products. Their equality condition forces

$$
u_i\exp(ipy\log t_i)=u_j\exp(ipy\log t_j)
\quad\text{for every }i,j\text{ and }y\in\mathbb R,
\qquad b_j=u_jt_j,\quad t_j>0.
$$

The index quantifier here means every $i,j\in\{1,\ldots,n\}$ and every real $y$. At $y=0$ the phases coincide; variation in $y$ forces equal moduli. Thus every $b_j$, and hence every $z_j$, is equal. Conversely, for $z_j=a\ne0$, the derivative roots are $a$ with multiplicity $n-1$ and $a/(n+1)$, giving equality directly.

For the endpoint counterexample,

$$
P'(Z)=3Z^2-6Z+2,
\qquad w_{1,2}=1\mp\frac{\sqrt3}{3},
\qquad \frac1{|w_1|}+\frac1{|w_2|}=3
= c(2,1)\left(1+\frac12\right).
$$

## Formal binding and evidence boundary

The settling target is `D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result : claim`. Its Scribe node binds this dossier with `OpenProblemResolutionClaim(Proved)`: “Proved” refers to the corrected conjunction, including the negation of the endpoint equality clause. The inequality and strict-order equality directions retain the original quantifiers.

Admission basis is `open-problem-resolution` under issue #18789. The exact polynomial, complex-power, rank-one trace, Schur interpolation and endpoint statements are mathematical proof obligations; a paper proof or a source label is not a Lean compilation result. Actual kernel verification and allowed axiom closure must be read from the compiled declarations and current checks.

No network access is used. The supplied source brief is the evidence for the conjecture locator and its scope. No independent current search for subsequent resolutions, exhaustive literature absence, or worldwide priority is asserted. The existing library note documents the separate order-minus-two Conjecture 6.3 and does not supply an independent verification of the Conjecture 1.13 quotation.
