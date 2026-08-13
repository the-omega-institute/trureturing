# Properness of the Composite Matrix-Cone Inclusions

## Abstract

The exchange operator and the unnormalized antisymmetric singlet witness the properness of both inclusions in the composite matrix-cone chain.

This module closes an open left by the frozen CompositeCones module. That module said of itself: "The source writes the chain with PROPER inclusion symbols, SEP subset PSD subset SEP*. This module proves only the two INCLUSIONS. That either of them is proper ... is NOT established here and no witness is exhibited." What was missing was precisely a witness, and the present module supplies one for each inclusion.

The elegant point is that one matrix does both jobs. The exchange operator SWAP is itself the block-positive-but-not-positive-semidefinite witness, and it is also the entanglement witness that certifies the singlet matrix is not separable. Thus the same separating functional resolves both properness directions.

**Theorem 1.1 (The exchange operator is block positive).**

$$\operatorname{blockPositive}(\operatorname{swapMatrix})$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.swapMatrix_blockPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a product vector a times b, the quadratic form of SWAP is the squared absolute value of the sum over i of conjugate(a_i)b_i. This expression is manifestly nonnegative, so the exchange operator is block positive.

**Theorem 1.2 (The exchange operator is not positive semidefinite).**

$$\neg\operatorname{PosSemidef}(\operatorname{swapMatrix})$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.swapMatrix_not_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antisymmetric vector e_01 - e_10 is an eigenvector of SWAP with eigenvalue minus one. Its quadratic form is therefore negative, which rules out positive semidefiniteness.

A tempting substitute does not work: the Bell vector e_00 + e_11 is symmetric, SWAP fixes it, and its quadratic form is plus two. Only the antisymmetric singlet is detected. This trap was checked by compiling a temporary Lean audit before the module was written and was also recomputed independently as a numerical matrix calculation.

**Theorem 1.3 (A block-positive matrix need not be positive semidefinite).**

$$\exists W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}), \operatorname{blockPositive}(W) \land \neg\operatorname{PosSemidef}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.exists_blockPositive_not_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking W to be swapMatrix combines the preceding two theorems. Consequently the positive-semidefinite cone is a proper subset of the block-positive cone SEP*.

**Theorem 1.4 (The unnormalized singlet matrix is positive semidefinite).**

$$\operatorname{PosSemidef}(\operatorname{singletMatrix})$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.singletMatrix_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singlet matrix is the rank-one outer product of e_01 - e_10 with its conjugate and is therefore positive semidefinite. It is deliberately the unnormalized singlet, equal to twice the normalized rank-one projector. Positive scaling preserves both positive semidefiniteness and nonseparability, while this choice removes all square-root arithmetic.

**Theorem 1.5 (The unnormalized singlet matrix is not separable).**

$$\neg\operatorname{separableCone}(\operatorname{singletMatrix})$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.singletMatrix_not_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The detector is again SWAP. For positive semidefinite factors C and D, the trace of SWAP times the Kronecker product C times D equals the trace of CD, whose real part is nonnegative. Every finite sum admitted by the definition of separability must therefore have a nonnegative detector value.

The unnormalized antisymmetric singlet instead has detector value minus two. No finite sum of positive-semidefinite Kronecker products can attain that value, so the singlet matrix is not separable. This is the second role of the same exchange operator used above.

The argument stays at generality G. It does not use the duality theorem from the sibling CompositeConeDuality module, which has generality I; only the definition of separability and the two elementary trace facts are needed.

**Theorem 1.6 (A positive semidefinite matrix need not be separable).**

$$\exists W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}), \operatorname{PosSemidef}(W) \land \neg\operatorname{separableCone}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeConeProperness.exists_posSemidef_not_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking W to be singletMatrix combines its positive semidefiniteness with its failure of separability. Hence the separable cone SEP is a proper subset of the positive-semidefinite cone, completing the proper chain SEP subset PSD subset SEP*.

All six displays are authored legally because no pinned projectable statement fixture exists for any of these declarations. Document construction records a ProjectionGap for each one.

## References

- Truth anchor: `D5/S3/Resource/CompositeConeProperness.exists_blockPositive_not_posSemidef`
- Truth anchor: `D5/S3/Resource/CompositeConeProperness.exists_posSemidef_not_separable`
- Truth anchor: `D5/S3/Resource/CompositeConeProperness.singletMatrix_not_separable`
- Truth anchor: `D5/S3/Resource/CompositeConeProperness.singletMatrix_posSemidef`
- Truth anchor: `D5/S3/Resource/CompositeConeProperness.swapMatrix_blockPositive`
- Truth anchor: `D5/S3/Resource/CompositeConeProperness.swapMatrix_not_posSemidef`
- Dependency: [D5/S3/Resource/CompositeCones](CompositeCones.md)
