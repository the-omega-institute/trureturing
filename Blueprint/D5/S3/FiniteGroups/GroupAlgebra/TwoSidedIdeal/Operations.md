# Ideal extension and contraction in the tensor-simplicity argument.

## Abstract

Ideal extension and contraction in the tensor-simplicity argument.

`D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/Operations`

The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.

$\forall R \in Type*,\; \forall S \in Type*,\; \forall F \in Type*,\; [NonUnitalNonAssocRing\left(R\right)], [NonUnitalNonAssocRing\left(S\right)], [FunLike\left(F, R, S\right)], [NonUnitalRingHomClass\left(F, R, S\right)], \forall f \in F,\; \forall I \in TwoSidedIdeal\left(R\right),\; \forall J \in TwoSidedIdeal\left(S\right),\; \operatorname{TwoSidedIdeal}.\operatorname{map}\left(I, f\right) \le J \Leftrightarrow I \le \operatorname{TwoSidedIdeal}.\operatorname{comap}\left(J, f\right)$

For a function carrying a nonunital ring-homomorphism structure, extension of a two-sided ideal is left adjoint to contraction. The formula retains both nonassociative ring assumptions and the function-class hypotheses. The additional zero, kernel and surjective-image identities in the source are the ideal calculations used by the tensor-simplicity proof.
