# Completed Product L2 Unitary

## Abstract

The completed complex Hilbert tensor of sigma-finite L2 spaces is the product L2 space by multiplication of AE representatives.

**Theorem 1.1 (Actual function-product unitary).**

$$\forall X\in\operatorname{MeasurableSpaces}\left(\right),\ \forall Y\in\operatorname{MeasurableSpaces}\left(\right),\ \forall \mu\in\operatorname{SigmaFiniteMeasures}\left(X\right),\ \forall \nu\in\operatorname{SigmaFiniteMeasures}\left(Y\right),\ \exists U\in\operatorname{UnitaryC}\left(\operatorname{Completion}\left(\operatorname{HilbertTensor}\left(\operatorname{L2}\left(X, \mu\right), \operatorname{L2}\left(Y, \nu\right)\right)\right), \operatorname{L2}\left(X \times Y, \mu\times\nu\right)\right),\ \forall f\in\operatorname{L2}\left(X, \mu\right),\ \forall g\in\operatorname{L2}\left(Y, \nu\right),\ \operatorname{aeEqual}\left(\mu\times\nu, \operatorname{Representative}\left(\operatorname{U}\left(\operatorname{iota}\left(\operatorname{tensor}\left(f, g\right)\right)\right)\right), (x,y)\mapsto\operatorname{f}\left(x\right)\operatorname{g}\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CompletedProductL2.exists_completed_product_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monica Omar; Floris van Doorn; Rémy Degenne; Mathlib contributors (2025). *Tensor products of inner product spaces and product-measure L2 APIs*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean>.

*Commentary.*

MeasurableSpaces ranges over arbitrary types with measurable-space structures. SigmaFiniteMeasures(X) comprises all sigma-finite measures on X. L2(X,mu) means complex Lp at exponent 2. HilbertTensor is the algebraic complex tensor with its actual inner-product tensor norm, Completion is its metric completion, and iota is the canonical completion embedding. UnitaryC(A,B) denotes the complex linear isometric equivalences from A onto B. Representative chooses an AE representative, and aeEqual(eta,a,b) is equality eta-almost everywhere.

Both measures are arbitrary sigma-finite measures. The domain is the actual completion of the algebraic tensor with Mathlib's inner-product tensor norm. The target is complex L2 of the actual product measure. The naturality clause holds for every pair of factor L2 vectors and is an almost-everywhere representative equality.

Square integrability of the product and complex Fubini give an inner-preserving algebraic lift for all finite sums. The existing completion extension preserves its isometry. Finite measurable rectangle tests, localization to finite exhaustive rectangles, and pi-system induction show that its closed range has zero orthogonal complement; orthogonal projection gives surjectivity.

Finite Euclidean factors, including empty coordinate types, satisfy these hypotheses. Physical coordinate pullback and the mass-one scalar empty factor are applications of existing measure-preserving and constant-L2 APIs. No basis, density, desired unitary, finite total volume or finite Hilbert dimension is assumed.

This theorem supplies the completed function-space tensor bridge. Physical Hamiltonian domains, selfadjointness, metaplectic covariance, the same-H Gibbs trace and thermal operator factorization require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CompletedProductL2.exists_completed_product_unitary`
