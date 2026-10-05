# Explicit factors and scalar fibers

## Abstract

Explicit factors and scalar fibers

**Theorem 1.1 (Explicit factors and scalar fibers).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers.pencil_parameter_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers.pencil_parameter_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every field F, every natural k at least one, every ClosureFullRank face pair T has factors A,B with T0=A E0 B and T1=A E1 B. Every factor pair produces ClosureFullRank faces. Scalar shifts preserve factorMap; any two factor pairs with the same image differ by such a shift; for each fixed pair the shift is injective. The normalization uses the finite observability map over the algebraic closure, descends its injectivity to F, and constructs the standard chain basis. Intertwiners of the two standard faces are scalar. Thus the actual fibers are exactly the multiplicative units of F, including in characteristic two.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers.pencil_parameter_fibers`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs](MaskedFacesDefs.md)
- Dependency: [D5/S3/Observer/Hankel/HankelRankMinimality](../../Observer/Hankel/HankelRankMinimality.md)
