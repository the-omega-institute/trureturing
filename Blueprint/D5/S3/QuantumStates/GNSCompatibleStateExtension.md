# Compatible states and normalized cyclic GNS expectations

## Abstract

Compatible local C-star states on a dense increasing union and their completed GNS representation.

**Theorem 1.1 (Unique continuous extension with normalized cyclic representation).**

$$(\forall A: \operatorname{Type}\left(\right), [\operatorname{CstarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] (\forall S: \operatorname{Function}\left(\operatorname{Nat}\left(\right), \operatorname{StarSubalgebra}\left(\operatorname{Complex}\left(\right), A\right)\right), (\forall omega: \operatorname{DependentPositiveFunctionals}\left(S\right), ((((\operatorname{Monotone}\left(S\right) \land (\forall n: \operatorname{Nat}\left(\right), ((\operatorname{Closed}\left(\operatorname{Apply}\left(S, n\right)\right) \land \operatorname{InheritedStarOrder}\left(\operatorname{Apply}\left(S, n\right)\right)) \land (\operatorname{Apply}\left(omega, n, 1\right) = 1)))) \land (\forall n: \operatorname{Nat}\left(\right), (\forall m: \operatorname{Nat}\left(\right), (\forall a: \operatorname{Apply}\left(S, n\right), ((n \le m) \implies (\operatorname{Apply}\left(omega, m, \operatorname{Include}\left(n, m, a\right)\right) = \operatorname{Apply}\left(omega, n, a\right))))))) \land \operatorname{DenseUnion}\left(S, A\right)) \implies (\exists ! f: \operatorname{PositiveLinearFunctional}\left(A\right), ((((((\operatorname{Apply}\left(f, 1\right) = 1) \land (\forall n: \operatorname{Nat}\left(\right), (\forall a: \operatorname{Apply}\left(S, n\right), (\operatorname{Apply}\left(f, a\right) = \operatorname{Apply}\left(omega, n, a\right))))) \land (\forall a: A, (\operatorname{Norm}\left(\operatorname{Apply}\left(f, a\right)\right) \le \operatorname{Norm}\left(a\right)))) \land (\operatorname{Norm}\left(\operatorname{cyclicVector}\left(f\right)\right) = 1)) \land (\forall a: A, (\operatorname{Inner}\left(\operatorname{cyclicVector}\left(f\right), \operatorname{Apply}\left(\operatorname{gnsStarAlgHom}\left(f\right), a, \operatorname{cyclicVector}\left(f\right)\right)\right) = \operatorname{Apply}\left(f, a\right)))) \land \operatorname{DenseOrbit}\left(\operatorname{gnsStarAlgHom}\left(f\right), \operatorname{cyclicVector}\left(f\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/GNSCompatibleStateExtension.compatible_state_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christopher J. Fewster, Kasia Rejzner (2019). *Algebraic Quantum Field Theory — an Introduction*. DOI: [10.48550/arXiv.1904.04051](https://doi.org/10.48550/arXiv.1904.04051). URL: <https://arxiv.org/abs/1904.04051v2>.

*Commentary.*

Let A be a unital C-star algebra, and let S(n) be increasing closed unital star subalgebras whose union is dense in A. Each S(n) has the inherited star order, and omega(n) is a positive complex-linear functional normalized at the common unit. Compatibility means that inclusion from S(n) to S(m), for n<=m, preserves omega(n). Finite-dimensional local algebras are closed by Submodule.closed_of_finiteDimensional. In a closed star subalgebra, functional calculus retains the ambient positive square root; its square equals the positive element. Hence the inherited order is a star order. Both interface obligations are constructed in the finite-local exact application, rather than added as independent hypotheses. Taking A to be the norm closure of the algebraic union supplies the density condition.

Positivity gives Cauchy-Schwarz in the pre-GNS carrier. Together with the bound on omega(a* a), normalization implies |omega(a)|<=norm(a). On the directed union choose a stage containing a. Compatibility makes its value independent of the stage; a common maximum stage proves additivity and complex linearity. LinearMap.extendOfNorm extends this contractive functional to A. Its values on a* a remain nonnegative by continuity and density. Every positive element of a C-star algebra is a square of this form, so the extension is positive. A continuous positive functional agreeing on the dense union is equal to this extension.

For the resulting normalized functional f, use the pinned Mathlib PositiveLinearMap.PreGNS quotient, completion GNS, and representation gnsStarAlgHom. The null ideal and bounded left multiplication are supplied by Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal; they are not extra axioms. Omega is the completion image of f.toPreGNS(1). Its norm is one, and the completed expectation inner(Omega,pi(a)Omega) equals f(a). Left multiplication sends Omega to the image of f.toPreGNS(a). The quotient map is surjective and the completion image is dense, so this orbit is cyclic. The theorem concerns this exact completed Hilbert space and this exact extension.

A nonzero equal coefficient on every finite word cannot be square summable. The words consisting of n repetitions of one fixed letter form an injective sequence. Summability on all words would give summability of the same positive constant along this sequence, contradicting infinitude. Hence finite normalized equal-weight history vectors cannot be extended by placing an infinite clock directly in ell2. This is a compiled application of Memlp and the constant-summability boundary, not an additional state assumption.

## References

- Truth anchor: `D5/S3/QuantumStates/GNSCompatibleStateExtension.compatible_state_extension`
