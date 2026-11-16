# Entire complex L1 realization

## Abstract

A positive complex-linear continuous-function map with normal unit value and scalar mass measure has a positive, mass-preserving, contractive normal-valued realization on the entire complex L1 space.

**Theorem 1.1 (Norm equals mass for a positive functional).**

Lean statement: `D5/S3/Quantum/Analysis/NormalL1Realization.positive_norm_eq_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalL1Realization.positive_norm_eq_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex unital C-star algebra A with a partial order and StarOrderedRing compatibility, and any continuous complex-linear functional phi that is nonnegative on every positive a, ||phi||=Re(phi(1)). The proof applies Mathlib's PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one. This is a reused supplier, consumed by exists_normal_L1_extension and by the actual all-coordinate bound in NormalMomentFamily, rather than new mathematical content. Zero functionals and the zero algebra are included.

**Theorem 1.2 (The positive normal whole-L1 extension).**

Lean statement: `D5/S3/Quantum/Analysis/NormalL1Realization.exists_normal_L1_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NormalL1Realization.exists_normal_L1_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any unital complex C-star algebra with a partial order and StarOrderedRing compatibility. K is any compact metric Borel space. The measure nu is finite and weakly regular. J is an actual complex-linear map from C(K,C) to the continuous complex dual of A. For every pointwise nonnegative continuous g and every positive a in A, J(g)(a)>=0. The functional J(1) is order-normal in the all-directed sense of NormalFunctionals.IsOrderNormal. For every complex continuous g, J(g)(1)=integral g dnu. No continuity of J, support condition, nonzero total mass, nontriviality of A, finite dimension or chosen predual is assumed. Normality of all J(g) is derived from normality of J(1), so in particular the theorem applies when all values are given normal.

There exists a continuous complex-linear map Gamma from the entire complex L1(nu) to StrongDual C A. It agrees exactly with J on ContinuousMap.toLp 1 nu C g for every continuous complex g. Every Gamma(h) is order-normal. For every L1 class h that is nonnegative almost everywhere, Gamma(h)(a)>=0 for every positive a. For every complex L1 class h, Gamma(h)(1)=integral h dnu. Its actual operator norm is at most one. Positivity, mass and normality hold for all L1 inputs in their stated domains, rather than only bounded, simple or positive source inputs.

For positive continuous g, 0<=J(g)<=||g||J(1), and domination gives normality. Decomposition into positive and negative parts of the real and imaginary components then gives normality for every complex g. The same decomposition and the exact Mathlib identity for the norm of a positive functional give ||J(g)||<=2 integral ||g|| dnu=2||toLp(g)||. LinearMap.extendOfNorm factors through the null kernel of toLp and extends the map directly into the complete closed normalDual submodule. Thus vanishing mass on an open set, the zero measure and the zero algebra need no separate support or injectivity argument.

Positive continuous L1 classes are dense in the almost-everywhere positive cone: approximate a positive h by continuous complex g and replace g pointwise by ofReal(max(Re(g),0)). Projection onto the positive real ray decreases the distance to each positive complex number, hence decreases the L1 error. Closedness of positive scalar evaluations passes positivity to Gamma(h). Continuity and ContinuousMap.toLp_denseRange pass the scalar mass identity to every complex L1 class.

For a measurable set E, positivity and mass give ||Gamma(1_E)||=nu(E). Complex linearity therefore bounds Gamma(c 1_E) by its L1 norm for every complex c. On disjoint simple pieces the input L1 norms add, while output norms satisfy the triangle inequality. The existing Mathlib Lp.induction principle and closedness of the norm inequality extend this sharp bound to all complex L1 classes, proving ||Gamma||<=1. The initial constant two is only used for construction.

For the posterior consumer take K=Set.Icc (0 : ℝ) 1. Exact continuous source expressions are p : C(K, ℂ) := ⟨fun t => (t.val : ℂ), by fun_prop⟩ and q : C(K, ℂ) := 1 - p. If e=ContinuousMap.toLp 1 nu ℂ, the agreement clause yields Gamma(e p)=J p and Gamma(e q)=J q; linearity also gives e q=e 1-e p. Both source classes are nonnegative, and zero total mass is included. These are the actual posterior moments, with no normalized-state or full-support hypothesis.

The theorem starts with an actual scalar mass measure and does not construct that measure by Riesz representation. Its downstream consumer NormalMomentFamily.compact_normal_posterior_family constructs the actual compact compatible family and scalar finite regular Riesz measures, proves their weak continuity, and applies this extension to every family point on an arbitrary concrete von Neumann algebra. Full arbitrary-source attainment still requires normalization and exact cost-set comparison with every original sigma-finite whole-complex-L1 reverse test, and endpoint-complete extended minimization including the +infinity branch. No chosen-predual identification, RNP, vector density or operator-convex assumption is introduced.

The source reuses Mathlib's positive-functional norm identity, continuous-function density, LinearMap.extendOfNorm and existing simple-function Lp induction. It does not construct a vector measure or a second L1 completion. This is a supporting realization theorem for the full attainment problem; it is not a solution of that problem or a claim of new literature priority.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NormalL1Realization.exists_normal_L1_extension`
- Truth anchor: `D5/S3/Quantum/Analysis/NormalL1Realization.positive_norm_eq_mass`
- Dependency: [D5/S3/Quantum/Analysis/NormalFunctionals](NormalFunctionals.md)
