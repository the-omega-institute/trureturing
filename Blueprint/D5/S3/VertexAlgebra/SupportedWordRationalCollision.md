# Actual supported-word rational reconstruction and collision

## Abstract

The genuine uniform numerator reconstructs both actual complete words and transports the all-integer collision.

Let V be a complex module, D actual GradedLocalFields with energy covariance, creation, vacuum energy zero and a uniform operator locality order. Let the idempotent output selector satisfy both energy-d intertwining laws and fix energy-d vectors. Choose any full nodup original label order, any submodule W containing its selected coefficients, and any linear lambda. These hypotheses are generic graded-local laws, not an unconditional assertion for every VOA.

**Theorem 1.1 (Finite polynomial action is Hahn multiplication).**

Lean statement: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_clearing_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_clearing_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The native polynomialAction is the finite e-b convolution, and ordered_mul_coeff proves it equals Hahn multiplication. ActualWord coefficients are the real coefficientDistribution in modes -e-1. Scalarization of the finite vector numerator gives its exact coefficient at every integer exponent, including zero at negative coordinates.

**Theorem 1.2 (Reconstruct every order from the same derived numerator).**

Lean statement: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_all_order_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_all_order_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The proof invokes uniform_graded_local_correlator on the original full nodup order and proves that List.ofFn sigma is a permutation for every sigma. The same finite P has total degree d-sum weights+k*number of labelled pairs, all coefficients lie in W, and negative degree forces P=0. OriginalQ_ne_zero and injective ordered polynomial/fraction embeddings allow cancellation in the supported Hahn field. No reconstruction equality or support certificate remains a premise.

**Theorem 1.3 (Both actual words satisfy the complete all-integer collision).**

Lean statement: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_word_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_word_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Explicit firstOrder and secondOrder permutations realize pre,z,x,post and pre,x,z,post. Their exponent equivalences and fraction-field squares identify both actual Carnahan words applied to D.vacuum and evaluated by lambda composed with selector.map with the complete expansions of lambda(P)/Q. For every integer r and every remaining labelled exponent, the expanded rational local u-residue equals the difference of the supported z=-1 fibres of those actual weighted words. No actual fused-state, state-iterate, Monster carrier or physical spacetime identity is proved.

The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association is background, not a claim that these new rational proofs are supplied by that paper.

Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide residue-product locality and reconstruction background. Their reconstruction requires additional creative generators and a common translation operator. Carpi and Codogni, arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, CFT/anomaly/fusion, string theory or AdS/CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_all_order_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_clearing_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/SupportedWordRationalCollision.actual_word_collision`
- Dependency: [D5/S3/VertexAlgebra/CollisionRationalExpansions](CollisionRationalExpansions.md)
- Dependency: [D5/S3/VertexAlgebra/LabelledRationalClearing](LabelledRationalClearing.md)
- Dependency: [D5/S3/VertexAlgebra/OrderedCollisionCoordinates](OrderedCollisionCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/RationalCollision](RationalCollision.md)
- Dependency: [D5/S3/VertexAlgebra/SupportedFieldWords](SupportedFieldWords.md)
- Dependency: [D5/S3/VertexAlgebra/UniformGradedLocalCorrelator](UniformGradedLocalCorrelator.md)
