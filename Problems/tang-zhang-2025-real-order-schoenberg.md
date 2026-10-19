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

## Problem

Q. Tang and T. Zhang, *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*, arXiv:2508.10341v3, §1.3, Conjecture 1.13. The source is [tang2025schoenberg](../Library/Zeros/tang2025schoenberg.md).

> Conjecture 1.13. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n be the zeros of P′(z). Then for every real number p ≥ 1 we have Σ_{k=1}^n 1/|w_k|^p ≤ ((n+1)^p + n − 1)/n · Σ_{j=1}^n 1/|z_j|^p. Moreover, equality holds if and only if z_1 = ⋯ = z_n.

For every natural $n\ge1$ and every family $z_1,\ldots,z_n\in\mathbb C\setminus\{0\}$, put

$$
P(Z)=Z\prod_{j=1}^n(Z-z_j),\qquad
c(n,p)=\frac{(n+1)^p+n-1}{n}.
$$

Let $w_1,\ldots,w_n$ be all roots of $P'$, counted with algebraic multiplicity. No distinctness, simplicity, reality or common argument hypothesis is imposed on the nonzero roots. The result proves the following three clauses:

1. For every real $p\ge1$,
   $$\sum_{k=1}^n|w_k|^{-p}\le c(n,p)\sum_{j=1}^n|z_j|^{-p}.$$
2. For every real $p>1$, equality holds if and only if $z_i=z_j$ for every $i,j$.
3. Conjecture 1.13 as stated is false: at $p=1$, $n=2$ and $(z_1,z_2)=(1,2)$ give equality although $z_1\ne z_2$.

The formal `claim` is the conjunction of (i), (ii), and `¬ conjecture`, where the original conjecture has its full dimension, root and order quantifiers:

```lean
def conjecture : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 ≤ p →
      (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum ≤
        c n p * ∑ j, ‖z j‖ ^ (-p)) ∧
      ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
        c n p * ∑ j, ‖z j‖ ^ (-p)) ↔ ∀ i j, z i = z j)
```

Every norm power is a real `Real.rpow`, including nonintegral orders. The named conjecture is refuted by its endpoint equality clause. The sharp inequality for all $p≥1$ and the strict-order equality case are proved in the same result.

## Motivation

Conjecture 1.13 asks for a sharp real-order extension of reciprocal critical-point inequalities. Its coefficient is attained when all nonzero roots coincide. The external problem is identified in [issue #18789](https://github.com/the-omega-institute/trureturing/issues/18789).

## Gap

The original statement combines the moment inequality and an equality equivalence for every $p≥1$. These have different endpoint behavior: the inequality holds at $p=1$, while equality there does not force coincident roots. The result proves the sharp bound at every stated order, proves the equivalence for $p>1$, and refutes the original full conjecture.

## Route

The polynomial and its multiplicity-preserving reciprocal-root spectral reduction are reused from `TangZhangOrderMinusTwo`. With $b_j=1/z_j$, $D=\operatorname{diag}(b_j)$ and $H=I+J$, the matrix $A=H^{1/2}DH^{1/2}$ has characteristic roots $1/w_k$. Since $P'(0)=\prod_j(-z_j)\ne0$, the critical points are nonzero.

The explicit powers

$$
H^\zeta=I+\bigl((n+1)^\zeta-1\bigr)J/n
$$

reduce matrix complex powers to scalar exponential functions. For $p>1$, a scalar trace function in a fixed Schur basis has boundary bounds $1$ and $M=c(n,p)\sum_j|b_j|^p$ on the vertical strip. At $\zeta=1/p$, its value is $(\sum_k|1/w_k|^p)^{1/p}$. The three-lines theorem yields the real-order inequality. A rank-one trace estimate gives the endpoint $p=1$.

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

## Falsifier

A nonempty finite family of nonzero complex roots and a real $p≥1$ violating the bound would refute (i). Equality for a nonconstant family at $p>1$, or failure of equality for a constant nonzero family, would refute (ii). Root sums include algebraic multiplicity. The exact family $(1,2)$ at $p=1$ refutes the original conjecture's equality characterization.

## Evidence

`D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.result : claim` proves all three clauses. `SchurMomentInequality.spectral_bound_and_rigidity` supplies the real-order matrix estimate and rigidity, and `SchurMomentNormalization.reciprocal_moment` supplies the polynomial-to-matrix correspondence. The explicit derivative and root calculation gives the endpoint counterexample. The named Conjecture 1.13 is **REFUTED**; the sharp inequality for every $p≥1$ and equality equivalence for $p>1$ are **PROVED** by the same result.

## Triage

**PROVED — (i), the sharp inequality for all real $p≥1$.** No degree cutoff, simplicity or common argument hypothesis is required. Constant nonzero roots attain the coefficient, so it is sharp.

**PROVED — (ii), equality for $p>1$ if and only if all nonzero roots coincide.** Interior equality propagates to the strip boundary; varying the imaginary parameter fixes both the phases and the moduli of the reciprocal roots.

**REFUTED — the original $p=1$ equality characterization and hence Conjecture 1.13 as stated.** The family $(1,2)$ has equality at $p=1$ but distinct roots. Thus the endpoint equality implication cannot be used in subsequent deductions, while the moment bound and strict-order rigidity remain valid.

**OPEN — equality at $p=1$ if and only if all $z_j$ lie on one ray from zero.** The counterexample lies on such a ray and is compatible with this proposed replacement. These modules do not prove the ray characterization.

## ASSUMED-UNVERIFIED

The source version and locator identify the named conjecture; absence of subsequent settlements and worldwide priority are not established here. The proposed ray characterization at $p=1$ has no Lean proof in these modules.
