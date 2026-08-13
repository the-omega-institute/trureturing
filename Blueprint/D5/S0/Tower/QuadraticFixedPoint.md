# Quadratic Fixed Point

## Abstract

A nonzero real satisfies x^2 = x + 1 exactly when it satisfies x = 1 + 1/x.

**Theorem 1.1 (Quadratic and reciprocal fixed-point forms).**

$\forall x \in \mathbb{R},\ x\neq 0 \Rightarrow (x^{2} = x + 1 \iff x = 1 + \frac{1}{x})$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/QuadraticFixedPoint.quadratic_fixed_point_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero real, clearing the denominator turns the reciprocal equation into the quadratic equation.

This is an honest partial closure of the leading algebraic clause in the source atom only; its tower, self-application, and Fibonacci interpretations remain unresolved.

## References

- Truth anchor: `D5/S0/Tower/QuadraticFixedPoint.quadratic_fixed_point_iff`
