# Product-effect pairing and the actual tensor isometry

## Abstract

The actual preparation is the product effect under trace duality and induces an onto real linear isometry of the Hilbert tensor product.

**Theorem 1.1 (Exact four-vector trace pairing).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.prep_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.prep_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Under Marginals and Spans, the joint pairing of M(f,g) with M(x,y) equals the product of the local pairings of f with x and g with y. Here M(f,g) is N(f,g) by (16). The identity quantifies over all four Hermitian inputs, as in (17).

**Theorem 1.2 (The actual product of proper effects is proper).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.product_effect_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.product_effect_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

For f and g in their full local PSD unit intervals, M(f,g) is in the joint PSD unit interval. Its complement is M(I-f,g) + M(I,I-g).

**Theorem 1.3 (Full local effect intervals separate joint vectors).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.proper_effects_separate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.proper_effects_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

If the trace readings of two joint vectors agree against the actual adjoint Jordan products for all proper local f and g, the two joint vectors are equal. Local frame projections suffice for the spectral extension, and real product spanning completes the argument.

**Definition 1.4 (The actual preparation defines an onto real linear isometry).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry`

*Formalization.* `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The domain is the real Hilbert tensor product of the trace inner product spaces H(a) and H(b). Its codomain is the whole H(d). Equation (17) extends from simple tensors to the entire tensor space, and product spanning gives surjectivity.

**Theorem 1.5 (The underlying linear map is precisely the lift of M).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry_toLinearMap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry_toLinearMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The linear map of the isometry is TensorProduct.lift M. In particular tensorIsometry_tmul gives M(x,y) on the simple tensor x tensor y.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.prep_pairing`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.product_effect_interval`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.proper_effects_separate`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.tensorIsometry_toLinearMap`
- Dependency: [D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition](PositiveMarginalMatrixComposition.md)
