# Weighted Local Correlators on Arbitrary Inputs

## Abstract

Pair-dependent locality gives a common array with finite signed total-exponent slices.

Let V be a complex vector space, v any vector, P any linear endomorphism, and A_i actual VertexOperator maps indexed by Fin N. For each labelled pair i<j choose its own natural locality order k_ij, so the k_ij-th coefficient difference annihilates the operator commutator of A_i and A_j. The labels and orientations stay fixed. Put Q=product over i<j of (z_i-z_j)^k_ij. For a labelled list l, F_l(e) is P applied to the word of modes A_i[-e_i-1] acting on v, where every exponent e_i is an integer. Multiplication by Q means the existing finite polynomial convolution on coefficient distributions.

The scalar field is fixed to the complex numbers and the coefficient-distribution and locality constructions are those of the existing complex VertexOperator infrastructure. This is an I-level ambient specialization; it asserts no scalar-field generalization. Within that setting V, the actual input vector, the endomorphism, the fields and their independent pairwise orders remain arbitrary.

**Theorem 1.1 (One cleared array, simultaneous lower bounds, and finite Laurent slices).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator.common_cleared_fields`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator.common_cleared_fields` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Suppose l has no repeated labels and contains every label. Then Q F_l equals Q F_r for every permutation r of l. To prove this, factor out the clearing polynomial of an adjacent pair. Locality kills the contextual commutator, including its arbitrary prefix and suffix. Induction on list permutations extends these adjacent exchanges to every ordering without cancelling Q in the full distribution space.

For each label i, let b_i be the Hahn order of the actual series A_i(v). Move i to the far right. Its mode then acts directly on v, and pointwise lower truncation makes the coefficient zero when e_i<b_i. Every clearing difference preserves this lower bound. Permutation invariance transfers the bound back to the common array, so all coordinate bounds hold simultaneously. This uses the truncation of A_i on this particular v, with no bound uniform over all vectors.

For any fixed integer total t, a nonzero coefficient has sum e_i=t and b_i<=e_i<=t-sum b_j+b_i. It therefore lies in a finite integer box. The conclusion is finite support on each total-exponent slice; it does not assert finite support of the entire array. Negative totals and negative coordinate bounds are included. When N is zero the exponent space has one element, the word is the identity and Q is one. No vacuum, creation law, energy grading, grade selector or uniform locality order is required.

The inherited contextual-clearing and weighted support argument comes from UniformGradedLocalCorrelator.lean at commit 7ea38704492b34d40607f307313e1224fbb5087e, lines 194-267 and 299-403: https://github.com/the-omega-institute/trureturing/blob/7ea38704492b34d40607f307313e1224fbb5087e/D5/S3/VertexAlgebra/UniformGradedLocalCorrelator.lean#L194-L267 and https://github.com/the-omega-institute/trureturing/blob/7ea38704492b34d40607f307313e1224fbb5087e/D5/S3/VertexAlgebra/UniformGradedLocalCorrelator.lean#L299-L403.

Prospective consumer integration is described by external research commit 6c8682a64921b8f8d2f059c80e395b2af30c9a13. Its source LatticeHalfFockNestedQReadout.lean defines sameNumeratorCollisionBridge at https://github.com/the-omega-institute/trureturing/blob/6c8682a64921b8f8d2f059c80e395b2af30c9a13/D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout.lean#L1796-L1841. The same commit's LatticeHalfFockLeftCurrentTransport.lean contains actual_three_field_numerator at https://github.com/the-omega-institute/trureturing/blob/6c8682a64921b8f8d2f059c80e395b2af30c9a13/D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport.lean#L624. These are external research declarations, not integrated consumers in this delivery or its dev baseline.

The proposed lattice half-Fock specialization uses N=3, V=ActualTensor D hu, A=threeFields D hu i a b gamma delta, v=x, P=1, orders=threeOrders D a b K and l=[0,1,2]. The fields are the current J and the two source slices A and B. Their three orders are vectorFrequencyBound D a+1, vectorFrequencyBound D b+1 and K. The locality premise is supplied by the two current/source identities and source/slice locality. The common array is exactly actualNumerator on the actual vector x; the permutation equality is reversed to identify each ordered cleared word with that array. The lower bounds and fixed-total finiteness clauses then apply directly, with arbitrary x and signed exponents. This parameter correspondence does not claim that the external consumer has been ported to common_cleared_fields.

These bounds allow finite homogeneous Laurent windows of the same numerator. They do not identify complete actual nested Q residues with finite Taylor readouts. The three equalities in sameNumeratorCollisionBridge, for the fused residue and the two differently ordered nested residues, remain additional obligations. Supported extraction, outer completion and collision balance alone do not supply them. No Monster carrier identification or string-theory reconstruction follows from this common-array theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator.common_cleared_fields`
- Dependency: [D5/S3/VertexAlgebra/SupportedWordRationalCollision](../SupportedWordRationalCollision.md)
