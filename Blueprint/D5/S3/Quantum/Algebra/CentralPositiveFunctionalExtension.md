# Norm-additive positive ambient extensions

## Abstract

Positive ambient extensions represent every bounded real functional on a self-adjoint real subspace with exact total mass.

**Theorem 1.1 (Positive extensions with total mass equal to the operator norm).**

$$\forall A \in \operatorname{Type}\left(\right)*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall X \in \operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right),\; \left(\forall x \in X,\; \operatorname{IsSelfAdjoint}\left(\operatorname{val}\left(x\right)\right)\right) \Rightarrow \left(\forall phi \in \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), X\right),\; \exists psiPlus \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \exists psiMinus \in \operatorname{PositiveContinuousLinearMap}\left(\operatorname{Complex}\left(\right), A, \operatorname{Complex}\left(\right)\right),\; \left(\forall x \in X,\; phi\left(x\right) = \operatorname{re}\left(psiPlus\left(\operatorname{val}\left(x\right)\right)\right) - \operatorname{re}\left(psiMinus\left(\operatorname{val}\left(x\right)\right)\right)\right) \land \operatorname{re}\left(psiPlus\left(\operatorname{one}\left(A\right)\right)\right) + \operatorname{re}\left(psiMinus\left(\operatorname{one}\left(A\right)\right)\right) = \operatorname{norm}\left(phi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A have exactly the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. Let X be any real Submodule of A, let hX assert that every element of X is self-adjoint, and let phi be any StrongDual real X, with its inherited norm and topology. There exist positive continuous complex-linear maps psiPlus and psiMinus from A to Complex whose real difference agrees with phi on every x in X and whose real values at the unit sum to the operator norm of phi.

X need not contain the unit, be closed, or be complete. The zero subspace, zero functional, subsingleton ambient algebra and zero total mass are included, without a nontriviality or normalization hypothesis. In the display, val is the inclusion of X in A, one(A) is the ambient unit, re is the real part, and norm(phi) is the continuous real functional's operator norm.

For a nontrivial ambient algebra the self-adjoint spectral estimate gives the exact product norm of (x+t1,-x+t1) as norm(x)+abs(t). On its actual linear range in A x A, the functional phi(x)+norm(phi)t is bounded by norm(phi). Mathlib's exists_extension_norm_eq supplies a real Hahn-Banach extension G. StrongDual.extendRCLike preserves its norm and real part; equality of norm and unit value then supplies positivity through ContinuousLinearMap.monotone_iff_opNorm_eq_map_one. Restriction to the two product coordinates gives the same pair satisfying both conclusion clauses.

This is a repository-derived composition of the cited spectral and extension interfaces, with no novelty claim. It supplies analytic machinery for the central-response problem. The full signed overlap budget of 95.1 and identification of the original coset slope with the kernel response in 96.1 remain separate mathematical obligations; this theorem asserts neither conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive`
