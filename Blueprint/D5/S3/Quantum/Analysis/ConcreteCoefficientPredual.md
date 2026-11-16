# Concrete coefficient closure

## Abstract

Restricted vector coefficients and their norm closure provide concrete normal functionals and a hereditary target for the actual posterior L1 map.

**Definition 1.1 (Actual vector coefficients).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient`

*Formalization.* `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any complete complex Hilbert space H, any concrete von Neumann algebra M acting on H, and arbitrary vectors xi and eta, coefficient(M,xi,eta)(a) is the actual inner product <xi,a eta>. Its operator norm is at most ||xi|| ||eta||. All norms on the functional space are inherited from the continuous complex dual of M.

**Definition 1.2 (The closed complex coefficient span).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace`

*Formalization.* `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E is the norm closure, in the actual continuous dual of M, of the complex linear span of all restricted vector coefficients. This definition imposes neither separability nor a countable dimension condition on H. A separate theorem is required to identify this closure with the independently defined square-summable-series class; the definition itself does not establish that identification.

**Definition 1.3 (Bounded left translation).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate`

*Formalization.* `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a unital complex C-star algebra A and b in A, leftTranslate(b)(phi)(a)=phi(b-star a). It is a bounded complex-linear operator on the actual dual. The adjoint identity sends a vector coefficient to the coefficient with first vector b xi.

**Theorem 1.4 (Translation preserves the coefficient closure).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b in M and phi in E, leftTranslate(b)(phi) belongs to E. The adjoint coefficient identity proves invariance on the generating set. Complex linearity and the closed preimage under this bounded operator extend invariance to the entire norm closure.

**Theorem 1.5 (GNS positive heredity).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.positive_mem_of_domination`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.positive_mem_of_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a unital ordered complex C-star algebra. Let E be a dual-norm closed complex submodule stable under every leftTranslate(b). If phi belongs to E and 0<=psi<=phi on every positive element, then psi belongs to E. Positivity of phi is explicit. Cauchy-Schwarz bounds psi as a functional on Mathlib's pre-GNS space of phi. Extension to its Hilbert completion and Riesz representation give a vector w. Approximate w by an algebra vector b. The functional a maps to phi(b-star a) belongs to E, and its dual-norm distance to psi is at most ||w-b|| times the pre-GNS norm of 1. This estimate includes zero mass and uses no Radon-Nikodym commutant-operator premise.

**Theorem 1.6 (Heredity in E).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_hereditary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_hereditary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The GNS heredity theorem applies to the actual coefficient closure, using its proved translation invariance. The hypothesis is membership of the dominating positive functional in E; no equivalence between intrinsic normality and a selected predual is assumed.

**Theorem 1.7 (The actual realized Gamma has range in E).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.posterior_L1_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.posterior_L1_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose rho+sigma belongs to E and F is an actual full continuous-moment posterior family. For any continuous whole-complex-L1 map Gamma agreeing on every continuous function with linearMap(F), every Gamma(h) belongs to E. For positive continuous g, positivity gives 0<=Jg<=||g||J1, and GNS heredity puts Jg in E. Four positive parts handle all complex continuous functions. The closed preimage of E under Gamma contains the dense continuous-function image in L1, so it is the whole L1 space. The theorem applies to the exact Gamma returned by compact_normal_posterior_family. CodRestrict therefore changes only its codomain, preserving its actual values, positivity, every complex mass, contraction bound and both posterior moments; it does not manufacture another source or assume range membership.

**Theorem 1.8 (Internal positive directed suprema are strong limits).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.internal_lub_strong`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.internal_lub_strong` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty directed set of positive elements of M and an M-internal least upper bound a, the vector nets converge in norm to a(v) for every v. The generalized directed-positive-net supplier constructs an ambient strong limit using only the upper bound. Every commutation identity passes to that limit by continuity on vectors. The double commutant identity puts the limit back in M. Leastness in M and in the ambient algebra then identifies it with a. No ambient least-upper-bound premise is silently substituted for the internal one.

**Theorem 1.9 (Intrinsic normality of coefficients).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient_order_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient_order_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every restricted vector coefficient is order-normal along all positive directed sets having a least upper bound internal to M. Strong convergence against the second vector implies convergence of the actual coefficient difference. The tail condition is on every element above one witness, rather than a sequential substitute.

**Theorem 1.10 (Forward normality for the entire closure).**

Lean statement: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_le_normalDual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_le_normalDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All of E is contained in the intrinsic normal dual. This uses coefficient normality and the existing norm-closed complex normal-dual theorem. It proves the forward interface only, with no full converse, abstract chosen-predual identification or Sakai uniqueness assertion.

These are classical operator-algebraic interfaces consumed by ConcreteCoefficientSeries and the standard concrete-predual reverse-test endpoint in GeneralConvexReverseTestAttainment. The former proves equality with the independently defined standard series class. The latter proves the standard-original cost equality and attainment using the same Gamma and its codRestriction. Source universes, arbitrary complex L1 inputs and extended cost conventions of the original problem are unchanged. No converse from every intrinsic-normal functional or worldwide-priority assertion is made.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_hereditary`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficientSpace_le_normalDual`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.coefficient_order_normal`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.internal_lub_strong`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.leftTranslate_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.positive_mem_of_domination`
- Truth anchor: `D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.posterior_L1_range`
- Dependency: [D5/S3/Quantum/Analysis/NormalMomentFamily](NormalMomentFamily.md)
- Dependency: [D5/S3/Quantum/Measurements/DirectedPositiveNet](../Measurements/DirectedPositiveNet.md)
