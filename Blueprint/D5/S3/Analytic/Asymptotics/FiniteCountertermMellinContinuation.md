# Finite Counterterm Mellin Continuation

## Abstract

Finite local counterterms give a meromorphic Mellin continuation.

**Theorem 1.1 (Finite counterterms continue the Mellin transform).**

$$\begin{aligned}\forall m: \mathbb{N}, \theta: \mathbb{R}\to\mathbb{C}, a: \operatorname{Fin}(m)\to\mathbb{C},\\{}\alpha: \operatorname{Fin}(m+1)\to\mathbb{R}, \Delta: \mathbb{R};\\{}let R: \mathbb{R}\to\mathbb{C}, R(t) = \theta(t) - \sum_{j:\operatorname{Fin}(m)} a(j) (t:\mathbb{C})^{-\alpha(j)};\\{}let \theta_{reg}: \mathbb{R}\to\mathbb{C}, \theta_{reg}(t) = if t \le 1 then R(t) else \theta(t);\\{}let M_{m}: \mathbb{C}\to\mathbb{C}, M_{m}(s) = \operatorname{setIntegral}(\operatorname{Ioc}(0, 1), (t:\mathbb{C})^{s-1} R(t)) + \operatorname{setIntegral}(\operatorname{Ioi}(1), (t:\mathbb{C})^{s-1} \theta(t)) + \sum_{j:\operatorname{Fin}(m)} \frac{a(j)}{s-\alpha(j)};\\{}\operatorname{StrictAnti}(\alpha) \land 0 < \Delta \land\\{}\operatorname{LocallyIntegrableOn}(\theta_{reg}, \operatorname{Ioi}(0)) \land\\{}\operatorname{IsBigO}(nhdsWithin(0, \operatorname{Ioi}(0)), R, t\mapsto t^{-\alpha(last(m))}) \land\\{}\operatorname{IsBigO}(atTop, \theta, t\mapsto exp(-\Delta t)) \Rightarrow\\{}\operatorname{MeromorphicOn}(M_{m}, \{s \in \mathbb{C}: \alpha(last(m)) < \Re(s)\}) \land\\{}\forall s: \mathbb{C}, \alpha(0) < \Re(s) \Rightarrow \operatorname{MellinConvergent}(\theta, s) \land M_{m}(s) = \operatorname{mellin}(\theta, s).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation.finite_counterterm_mellin_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let theta be a complex-valued heat trace, let a be a finite family of local coefficients, and let alpha be a strictly decreasing list of real exponents with one additional residual exponent. The displayed regularized trace is constructed by subtracting the finite principal part only on the interval ending at one.

The hypotheses state local integrability of that exact piecewise trace, the residual power bound at zero, and exponential decay of theta at infinity. These analytic assumptions are all explicit in the Lean signature; none is hidden in a named source object.

The continued function is the literal sum of the two split integrals and the finite rational pole ledger. It is meromorphic on the half-plane to the right of the residual exponent, and on the original convergence half-plane theta has a convergent Mellin transform equal to this continuation.

Repository search found no theorem with this general finite-counterterm carrier. The proof applies Mathlib's Mellin convergence and differentiability theorem for simultaneous power and exponential bounds, the exact Mellin transform of a power on (0,1], and the standard closure rules for finite sums of meromorphic functions.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation.finite_counterterm_mellin_continuation`
