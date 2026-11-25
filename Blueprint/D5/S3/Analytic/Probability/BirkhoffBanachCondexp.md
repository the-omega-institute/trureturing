# Banach-valued Birkhoff conditional-expectation limits

## Abstract

On every finite measure space, integrable Banach-valued time averages converge almost everywhere in norm and in L1 to invariant conditional expectation.

**Theorem 1.1 (Pointwise norm convergence and mean norm convergence).**

Lean statement: `D5/S3/Analytic/Probability/BirkhoffBanachCondexp.birkhoff_conditional_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BirkhoffBanachCondexp.birkhoff_conditional_expectation` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Let u and v be independent universes. Let alpha : Type u carry an arbitrary measurable-space structure, let mu be a finite measure on alpha, and let E : Type v be a complete normed additive commutative group with a real normed-space structure. Let T : alpha -> alpha preserve mu and let g : alpha -> E be Bochner integrable. Write I = MeasurableSpace.invariants T and C = mu[g | I], the actual version of invariant conditional expectation. For every natural n, define A_n(x) = birkhoffAverage Real T g n x. This is the average of g(T^j x) for j<n, with the canonical convention A_0(x) = 0.

For every natural n, both A_n and the real function x maps to norm(A_n(x)-C(x)) are Bochner integrable with respect to mu. For mu-almost every x, the full sequence A_n(x) converges to C(x) in the norm topology as n tends to infinity. The real integrals of norm(A_n-C) tend to zero along the same natural-index atTop filter. These are simultaneous conclusions for the given g; no common exceptional set for all observables and no convergence rate is asserted.

The total mass may be zero or any finite nonnegative value. No ergodicity, invertibility, standard-Borel carrier, global separability or reflexivity of E is assumed. No measurable-space structure on E is an extra premise. Bochner integrability supplies the almost-everywhere strong measurability needed by the proof. Completeness supports Banach-valued conditional expectation and L1 approximation; finite mass supports the scalar finite-measure theorem and indicator approximations; measure preservation transports integrability along all iterates of T.

The almost-everywhere argument uses density in L1. For an integrable approximation s and residual e = g-s, the measure of the set where norm(A_n(g)-C(g)) is at least epsilon infinitely often is bounded, after multiplication by epsilon, by twice the L1 norm of e. The scalar conditional-expectation theorem applied to norm(e), conditional Jensen's inequality and Markov's inequality give this bound. Arbitrarily close approximations make each positive-level exceptional set null. A countable family of levels then gives norm convergence of the full sequence.

Integrable indicator functions multiplied by a fixed vector satisfy the pointwise conclusion by the scalar theorem and the scalar multiplication laws for averages and conditional expectation. Addition preserves the conclusion. The exceptional-set bound makes the class closed in L1, and almost-everywhere equality preserves both averages and conditional expectation. Integrable-function induction therefore gives the Banach-valued almost-everywhere conclusion without a countable global spanning family in E.

For mean convergence, put u_n = A_n(norm(g)), c = mu[norm(g) | I], d_n = norm(A_n(g)-C), r_n = abs(u_n-c), and b = abs(c)+norm(C). The norm-average inequality and the triangle inequality give d_n <= r_n+b at every point and every time, including zero. Define F_n = max(d_n-r_n,0). Then 0 <= F_n <= b and F_n <= d_n. All of d_n, r_n, b and F_n are integrable, and the pointwise norm convergence implies F_n tends to zero almost everywhere. Dominated convergence gives integral(F_n) -> 0. The real scalar theorem applied to norm(g) gives integral(r_n) -> 0. Integrating 0 <= d_n <= F_n+r_n and squeezing proves integral(d_n) -> 0.

Durrett's fifth edition, Section 6.2, supplies the classical scalar probability-space theorem. The Banach-valued approximation proof adapts Lua Viana Reis and Oliver Butterley's Pointwise.lean from Mathlib PR 42078 at revision ebc0f703f74bec1576e2ca3b078fb173ba11039f, with its copyright and complete Apache-2.0 license retained. The finite-measure scalar result is called directly from BirkhoffCondexp.birkhoff_conditional_expectation. The additional finite-measure Banach L1 argument combines scalar convergence for norm(g) with fixed-dominator convergence of the truncated norm error. This is an attributed classical extension and synthesis, without a claim of mathematical originality.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BirkhoffBanachCondexp.birkhoff_conditional_expectation`
- Dependency: [D5/S3/Analytic/Probability/BirkhoffCondexp](BirkhoffCondexp.md)
