# Positive binary marginals on full Hermitian matrices

## Abstract

Global positive trace-preserving marginals and product spanning determine the joint size and the actual commuting Jordan embeddings on full complex Hermitian matrix carriers.

Each H(n) is the full real vector space of n by n complex Hermitian matrices with its PSD cone, canonical unscaled trace and trace pairing. The assumptions of Library equation (15) are Marginals and Spans. M is positive and real bilinear. Both real-linear marginals are positive on the whole joint cone and preserve trace on all vectors. Their readbacks on M(x,y) are tr(y)x and tr(x)y on all real vector inputs. Spans means real linear spanning by all prepared products.

**Theorem 1.1 (Orthogonal preparations before spanning).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.frame_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.frame_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The M-preparations of distinct pairs from any two orthonormal rank-one frames have zero matrix product. The adjoint effects of the two actual marginals read the local labels deterministically on the prepared states.

**Theorem 1.2 (Joint size bound from readback).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The joint matrix size d is at least the product ab of the local matrix sizes. The orthogonal prepared supports each contribute a nonzero direction. The hypothesis is Marginals.

**Theorem 1.3 (Exact joint rank and real dimension).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

With Spans as well, d = ab and dim_R H(d) = dim_R H(a) dim_R H(b), as in (18). The linearization of M is onto. The dimensions of full Hermitian matrix spaces are the squares of their matrix sizes, which gives the opposite bound.

**Theorem 1.4 (The actual preparation preserves the product unit).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_unital`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_unital` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

M(I,I) is the joint identity after completing the prepared product frame. The saturated frame consists of mutually orthogonal trace-one rank-one projections.

**Theorem 1.5 (The actual M preserves rank one).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_rank_one_preserver`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_rank_one_preserver` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

M(x,y) has matrix rank one for any rank-one Hermitian x and y. This includes signed rank-one inputs. Applying prep_rank_one to positive trace-one rank-one inputs gives a positive trace-one rank-one product.

**Theorem 1.6 (Global positivity of the trace adjoint).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

For a real-linear marginal positive on the entire PSD cone, its adjoint for the canonical trace pairing is positive on every PSD input.

**Theorem 1.7 (Trace preservation gives a unital adjoint).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_unital`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_unital` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

When the marginal preserves the canonical trace on all vectors, its trace adjoint sends the local identity to the joint identity.

**Theorem 1.8 (The left adjoint is injective).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveA`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

With a nonzero right matrix carrier, a trace-one spectator and the left preparation readback give injectivity of the actual left marginal adjoint.

**Theorem 1.9 (The right adjoint is injective).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveB`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

With a nonzero left matrix carrier, the right preparation readback gives injectivity of the actual right marginal adjoint.

**Theorem 1.10 (The marginal adjoints multiply to the preparation).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

For all local Hermitian x and y, the ordinary matrix product of the two marginal adjoint images equals the matrix underlying M(x,y). The product-frame identity extends to all vectors by spectral expansion.

**Theorem 1.11 (The actual adjoint ranges commute as matrices).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The left adjoint image of every x commutes with the right adjoint image of every y in the ambient complex matrix algebra.

**Theorem 1.12 (The left adjoint preserves Jordan multiplication).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanA`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The left adjoint preserves the symmetrized product (XY+YX)/2 on the whole left carrier. The joint frame gives its square law, and polarization gives its Jordan law.

**Theorem 1.13 (The right adjoint preserves Jordan multiplication).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanB`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The right adjoint preserves the same symmetrized product on the whole right carrier.

**Theorem 1.14 (The two Jordan multiplication operators commute).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordan_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordan_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The Jordan multiplication operators of the two adjoint images commute on every joint Hermitian input z, as required by (16).

**Theorem 1.15 (The Jordan effect product is the actual preparation).**

Lean statement: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

For all f and g the Jordan product of the two marginal adjoint images equals M(f,g). This identifies N in (16) using the canonical trace pairing.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_commute`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveA`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_injectiveB`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanA`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordanB`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_jordan_commute`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_mul`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_pos`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_product`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.effect_unital`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.frame_orthogonal`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_rank_one_preserver`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.prep_unital`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_dimension`
- Truth anchor: `D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.rank_lower_bound`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](../QuantumChannels/TwoPositiveTransitionTrace.md)
