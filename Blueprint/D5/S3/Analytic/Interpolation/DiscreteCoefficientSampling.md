# Discrete coefficient sampling

## Abstract

A uniform discrete coefficient-energy lower bound for complex polynomials.

**Theorem 1.1 (One degree-dependent constant controls every allowed grid and polynomial).**

Lean statement: `D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling.discrete_coefficient_sampling_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling.discrete_coefficient_sampling_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d>0 there exists a real kappa>0 such that for every natural N with 2*d<=N and every complex polynomial p with p.natDegree<d, kappa*(N : Real)*(sum over r in Finset.range d of norm(p.coeff r)^2) is at most the sum over m in Finset.Icc (N+1) (2*N) of norm(p.eval((m : Complex)/(N : Complex)))^2. The constant is chosen before N and p and depends only on d. The zero polynomial and d=1 are included.

The proof chooses B=(6*(d : Real))^(d-1) and kappa=1/(2*(d : Real)^2*B^2). Put q=N/d in natural-number division. Then q>=2, d*q<=N and N<=2*d*q. For each r<q the d modes N+r+1+j*q, j<d, belong to the required integer interval. Reduction modulo q identifies r, and cancellation of the positive q identifies j, so the q grids have disjoint modes.

The scaled nodes x(j)=(N+r+1+j*q)/N lie in [1,2]. Distinct indices are separated by at least q/N>=1/(2*d). For each normalized Lagrange factor, the existing real coefficient one-norm is at most (2*d)*(1+abs(x(j)))<=6*d. Submultiplicativity gives coefficient one-norm at most B for each Lagrange basis, including the empty product when d=1.

Mathlib Lagrange.eq_interpolate gives exact complex interpolation at the real-cast nodes. Mapping the real bases into complex polynomials preserves their coefficients. The triangle inequality, finite sum interchange and each real basis budget give sum over k<d of norm(p.coeff k)<=B*sum over j<d of norm(p.eval(x(j))). The sum of squared nonnegative coefficient norms is at most the square of their sum. Finite Cauchy-Schwarz therefore bounds the coefficient energy by d*B^2 times one grid's sample energy.

Sum this estimate over all q residues. Injectivity lets the double sample sum be identified with the sum over its finite image, which is at most the energy on the whole interval because every omitted square is nonnegative. Thus q times the coefficient energy is at most d*B^2 times the full sample energy. The floor estimate N<=2*d*q and division by the positive 2*d^2*B^2 give the stated result.

This is mature finite interpolation and a quantitative sampling argument. It directly reuses Mathlib and the existing UniformCoefficientBudget real coefficient one-norm implementation, whose Causalean attribution and Apache-2.0 notices stay with that imported owner. The new owner supplies the disjoint-grid geometry and the uniform complex lower estimate. It makes no RH, physical-operator, or uniform-tail claim.

The exact theorem and its full-law coefficient registration have passed native Lean verification and a scoped report with only Classical.choice, Quot.sound and propext. This document retains the exact declaration handle and uses WithoutFormula, so its prose is not a compiled formula projection. Scribe emission, required CI and official acceptance are separate validation stages; this paragraph makes no claim about their final completion.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling.discrete_coefficient_sampling_lower`
- Dependency: [D5/S3/Analytic/Interpolation/UniformCoefficientBudget](UniformCoefficientBudget.md)
