# Supported contextual kernel extraction

## Abstract

Finite contextual Hahn convolution fibers for signed collision kernels.

**Theorem 1.1 (Every complete Hahn convolution fiber has finite support).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction.contextual_kernel_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction.contextual_kernel_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For any field K, any prefix and suffix lengths pre and post, any integer diagonal exponent r, any supported Hahn series W and any output exponent g, the coefficient at g of contextPair(K,pre,post,kernelZX(K,r)) times W is its natural-index binomial convolution. Its summand at j is (-1)^j choose(r,j) times the coefficient of W at g-pairIndex(pre,post,(j,r-j)). The theorem proves finite support of that convolution and its exact coefficient equation together. Every spectator coordinate remains fixed.

The nonzero terms embed injectively in the finite full Hahn multiplication antidiagonal. Conversely, the binomial support parametrization represents every nonzero antidiagonal term. This gives a finite bijection without a cutoff on either ordered part of an intermediate field.

The nested Q fiber calculations use this coefficient identity inside the complete inner residue. Identification of complete outer Q residues with the finite same-numerator Taylor coordinates requires further local-coordinate equalities; this theorem establishes no such outer identification.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction.contextual_kernel_extraction`
- Dependency: [D5/S3/VertexAlgebra/OrderedCollisionCoordinates](../OrderedCollisionCoordinates.md)
