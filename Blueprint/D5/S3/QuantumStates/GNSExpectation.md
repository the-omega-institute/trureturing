# GNS Expectation as Squared Length

## Abstract

A positive functional evaluates a star-square as the squared length of its pre-GNS vector.

**Theorem 1.1 (Positive-functional expectation is a pre-GNS norm square).**

$$\forall A,\ [\operatorname{NonUnitalCStarAlgebra}(A)],\ [\operatorname{PartialOrder}(A)],\ [\operatorname{StarOrderedRing}(A)],\ \forall omega\in \operatorname{PositiveLinearMap}(A,\mathbb{C}),\ \forall x\in A,\ omega(x^{*} x)=\Vert\operatorname{toPreGNS}(omega,x)\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/GNSExpectation.expectation_eq_preGNS_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a partially ordered non-unital C-star algebra whose order is compatible with its star structure. For every positive complex linear functional omega and element x, omega applied to star x times x is the squared norm of the pre-GNS vector represented by x.

The proof is the exact specialization and symmetric orientation of Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal.PositiveLinearMap.preGNS_norm_sq. No second proof of the GNS construction is introduced.

This declaration closes only the GNS squared-length clause of the source atom. It makes no claim about the atom's Tsirelson decomposition, two-source classification, or narrative synthesis.

## References

- Truth anchor: `D5/S3/QuantumStates/GNSExpectation.expectation_eq_preGNS_norm_sq`
