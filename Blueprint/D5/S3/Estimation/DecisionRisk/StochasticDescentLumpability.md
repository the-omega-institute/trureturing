# Zero Descent Defect and Exact Lumpability

## Abstract

Zero finite same-fiber descent defect is equivalent to strong lumpability, which is equivalent to exact quotient factorization and yields zero uniform descent error.

**Theorem 1.1 (Zero descent defect characterizes strong lumpability).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}\operatorname{descentDefect}\left(q, K\right) = 0 \iff \operatorname{StronglyLumpable}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.descent_defect_zero_iff_strongly_lumpable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The descent defect is the largest total-variation separation between rows indexed by source states in the same q-fiber. It vanishes exactly when every such pair of rows agrees, which is strong lumpability along q.

In one direction, separation of total variation turns a zero pairwise distance into equality of rows. In the other, fiberwise constancy makes every term in the finite maximum zero; a diagonal pair supplies the matching lower bound.

**Lemma 1.2 (Strong lumpability is exact quotient factorization).**

$$\begin{gathered}\forall X, B,\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}\operatorname{StronglyLumpable}\left(q, K\right) \iff \operatorname{ExactQuotientKernel}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.strongly_lumpable_iff_exact_quotient_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A kernel is constant on q-fibers exactly when its row assignment factors through the readout space B. Thus one may assign to each attained readout value the common row of its fiber and choose arbitrary rows outside the image of q.

Conversely, any quotient kernel that reproduces K at q(x) gives identical rows to source states with the same readout. This equivalence needs no finiteness or stochasticity assumptions.

**Lemma 1.3 (An exact quotient kernel has zero uniform descent error).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}Kbar: B \to B \to \mathbb{R},\\{}(\forall x: X, K(x) = Kbar(q(x))) \Rightarrow\\{}\operatorname{uniformDescentError}\left(q, K, Kbar\right) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.uniform_descent_error_eq_zero_of_exact_quotient_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When Kbar evaluated at q(x) reproduces the row K(x) for every source state, every total-variation discrepancy in the uniform descent error is zero. The finite maximum is therefore zero.

The conclusion depends only on exact row reproduction. In particular, it does not require either K or Kbar to be row-stochastic.

**Lemma 1.4 (Strong lumpability admits a zero-error exact quotient).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}\operatorname{StronglyLumpable}\left(q, K\right) \Rightarrow\\{}\exists Kbar: B \to B \to \mathbb{R},\\{}(\forall x: X, K(x) = Kbar(q(x))) \land\\{}\operatorname{uniformDescentError}\left(q, K, Kbar\right) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.strongly_lumpable_has_zero_uniform_descent_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong lumpability supplies a kernel on the readout space whose row at q(x) equals the original row at x. For this same quotient kernel, the uniform descent error vanishes.

The result packages exact factorization and zero approximation error into one witness. Strong lumpability alone is sufficient; no stochasticity hypothesis is imposed.

**Lemma 1.5 (At zero defect the best descent error is nonnegative).**

$$\begin{gathered}\forall X, B, \operatorname{Fintype}\left(X\right), \operatorname{Nonempty}\left(X\right), \operatorname{Fintype}\left(B\right),\\{}q: X \to B, K: X \to B \to \mathbb{R},\\{}\operatorname{IsRowStochastic}\left(K\right) \land \operatorname{descentDefect}\left(q, K\right) = 0 \Rightarrow\\{}0 \leq \operatorname{bestDescentError}\left(q, K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.best_descent_error_nonneg_of_zero_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a row-stochastic kernel, the general lower bound places half of the same-fiber descent defect below the best quotient-descent error. When that defect is zero, the bound reduces to nonnegativity.

This is a boundary specialization of the defect lower bound, rather than an additional assertion that an optimizing quotient kernel exists.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.best_descent_error_nonneg_of_zero_defect`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.descent_defect_zero_iff_strongly_lumpable`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.strongly_lumpable_has_zero_uniform_descent_error`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.strongly_lumpable_iff_exact_quotient_kernel`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.uniform_descent_error_eq_zero_of_exact_quotient_kernel`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](DescentDefectBounds.md)
