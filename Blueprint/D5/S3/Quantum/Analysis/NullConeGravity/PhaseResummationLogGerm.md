# The logarithmic germ of the resummed phase

## Abstract

The imaginary part of the resummed phase has an exact cubic logarithmic germ at zero coupling.

The sine series can be integrated after geometric damping. Removing the damping gives the sine-log integral. The bound on log(sin(t)/t) controls the remainder. The singular term g³log|g| gives the divergent slope of the second derivative.

**Definition 1.1 (Resummed phase).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.F`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For each real g, F(g) is the sum of the radial mode terms at g.

**Definition 1.2 (Clausen sine series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.clausen2`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.clausen2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Clausen2(θ) is the sum over positive integers n of sin(nθ)/n².

**Definition 1.3 (Cubic logarithmic term).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.cubicGerm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.cubicGerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The two-sided cubic logarithmic term is g³(log(2|g|) − 1).

**Theorem 1.4 (Imaginary part as a sine series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_neg_clausen`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_neg_clausen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For every real g, Im F(g) = −(g²/2) Clausen2(2g).

**Theorem 1.5 (Real part on the principal interval).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_re_eq_bernoulli`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_re_eq_bernoulli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For |g| ≤ π, Re F(g) = π²g²/12 − π|g|³/2 + g⁴/2.

**Theorem 1.6 (Logarithmic integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For 0 ≤ g ≤ π, Im F(g) equals g² times the integral from 0 to g of log(2 sin t).

**Theorem 1.7 (Explicit fifth-order error).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_cubic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_cubic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For |g| ≤ 1, the absolute difference between Im F(g) and the cubic logarithmic term is at most |g|⁵/15.

**Theorem 1.8 (Exact right-hand germ).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_right_germ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_right_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

As g approaches zero from above, Im F(g) = −g³ log(1/g) + (log 2 − 1)g³ + O(g⁵).

**Theorem 1.9 (First derivative at zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_hasDerivAt_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The real derivative of the complex-valued resummed phase at zero is zero.

**Theorem 1.10 (Derivative of the first derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_deriv_hasDerivAt_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_deriv_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The first derivative of the resummed phase has real derivative π²/6 at zero, viewed as a complex number.

**Theorem 1.11 (Second iterated derivative at zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_iteratedDeriv_two_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_iteratedDeriv_two_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The second iterated real derivative of F at zero is π²/6, viewed as a complex number.

**Theorem 1.12 (Twice continuous differentiability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffOn_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffOn_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The resummed phase is twice continuously differentiable on the open interval (−π, π).

**Theorem 1.13 (Twice continuous differentiability at zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffAt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffAt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The resummed phase is twice continuously differentiable at zero.

**Theorem 1.14 (Imaginary third derivative obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_second_not_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_second_not_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The second iterated derivative of the imaginary part is not differentiable at zero.

**Theorem 1.15 (Complex third derivative obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_second_no_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_second_no_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

No complex number is a derivative of the twice differentiated resummed phase at zero.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.F`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.clausen2`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.cubicGerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffAt_two`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_contDiffOn_two`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_deriv_hasDerivAt_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_hasDerivAt_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_cubic_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_integral`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_eq_neg_clausen`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_right_germ`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_im_second_not_differentiable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_iteratedDeriv_two_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_re_eq_bernoulli`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm.phase_second_no_hasDerivAt`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation](NonperturbativePhaseResummation.md)
