# Singularity at the actual Laplace convergence cut

## Abstract

The finite infimum of the actual nonnegative Laplace convergence domain admits no holomorphic extension of the same transform.

**Definition 1.1 (Actual convergence domain).**

Lean statement: `D5/S3/Analytic/Laplace/AbscissaSingularity.convergenceSet`

*Formalization.* `D5/S3/Analytic/Laplace/AbscissaSingularity.convergenceSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary measurable space Omega, measure mu and function X : Omega to the reals, convergenceSet X mu is the set of real s for which exp(-s X) is integrable with respect to mu. This definition concerns integrability, independently of the totalized value of a Bochner integral.

**Theorem 1.2 (No extension across the actual finite convergence cut).**

Lean statement: `D5/S3/Analytic/Laplace/AbscissaSingularity.no_holomorphic_extension_at_abscissa`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/AbscissaSingularity.no_holomorphic_extension_at_abscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be any measure on any measurable space Omega. Let X : Omega to the reals be AEMeasurable with respect to mu and nonnegative mu-almost everywhere. Suppose C = convergenceSet X mu is nonempty and bounded below, and put sigma = sInf C. For every real R > 0 and every H : complex to complex, it is impossible that H is complex differentiable on the open complex ball B(sigma,R) and that, for every complex z in this ball with sigma < Re z, H(z) = complexMGF X mu (-z). The equality is on the full complex right-hand part of the ball.

If s belongs to C and s <= r, nonnegativity gives exp(-r X) <= exp(-s X) almost everywhere. Explicit a.e. measurability of X makes the dominated exponential measurable, so r belongs to C without assuming mu finite. The infimum is a lower bound for every member of C. For every s > sigma, the defining property of the infimum supplies a member r < s; domination then gives the entire open half-line (sigma,infinity) inside C and hence inside its interior. Every s < sigma is outside C. Reflection maps this genuine convergence half-line into integrableExpSet X mu.

Assume the claimed extension and set a = sigma + R/4. The ball B(a,3R/4) is contained in B(sigma,R), while -a lies in the interior of the actual exponential integrability set. The open intersection of B(sigma,R) with Re z > sigma is a complex neighborhood of a, giving equality of the ordinary complex germs. Apply NonnegativeContinuation.integrable_exp_of_laplace_extension at a with radius 3R/4 and t = R/2. Its integrability conclusion puts a-t = sigma-R/4 in C, contradicting the lower-bound property of sigma. The real parameter arithmetic, ball inclusion, reflection and neighborhood obligations are proved in Lean.

This is the classical Landau positivity argument, with no literature originality claim. Nonempty and bounded-below are assumptions on the actual convergence set; they exclude empty or all-real convergence without an extra restriction on the measure. This theorem supplies a global singularity obstruction. Signed-tail ODE continuation, zeta prime-power meromorphy, the integer psi-clock crossing, Robin's criterion at 5040 and RH remain separate obligations.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/AbscissaSingularity.convergenceSet`
- Truth anchor: `D5/S3/Analytic/Laplace/AbscissaSingularity.no_holomorphic_extension_at_abscissa`
- Dependency: [D5/S3/Analytic/Laplace/NonnegativeContinuation](NonnegativeContinuation.md)
