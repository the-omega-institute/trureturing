# Nonnegative Laplace Continuation

## Abstract

Holomorphic extension of a nonnegative Laplace germ forces convergence across its original margin.

**Theorem 1.1 (Convergence throughout the real radius of a holomorphic extension).**

Lean statement: `D5/S3/Analytic/Laplace/NonnegativeContinuation.integrable_exp_of_laplace_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/NonnegativeContinuation.integrable_exp_of_laplace_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be any measure and X a real function which is nonnegative almost everywhere. Suppose -a lies in the interior of the exponential integrability set. Let H be complex differentiable on the open ball with real center a and radius R, and agree in a complex neighborhood of a with the original Laplace transform z ↦ complexMGF X mu (-z). For every 0<t<R the function exp((t-a)X) is integrable, and H(a-t) is its real integral embedded in the complex numbers. No upper bound on t from the old convergence margin is imposed.

Reflecting the variable reduces to the moment-generating convention. Germ equality identifies all derivatives at the center with the weighted moments supplied by Mathlib. The Taylor theorem on the entire extension ball gives convergence of the series with coefficients t^n/n! integral X^n exp(-aX). Positivity turns that convergence into finiteness of the integral of the exponential series by Tonelli. Interchanging the convergent integral series identifies the value of the same extension H.

This is a generic local analytic supplier. It makes no claim that the complete notRH, Robin, or 5040 supplier is formalized. The global abscissa argument, the original psi-clock construction, its error costs and the ODE boundary terms remain separate obligations. The argument is classical; no literature originality is claimed.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/NonnegativeContinuation.integrable_exp_of_laplace_extension`
