# Native Physical Differentiation

## Abstract

Native Physical Differentiation.

Physical differentiation uses z=x^2. Its integer-cover coefficient at E is (E+2)/2 times the original coefficient at E+2, not the bare cover derivative. The field constructor retains the original ActualTensor carrier and proves its lower truncation from the input field's support.

**Theorem 1.1 (Physical derivative of native normal insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalInsertion_physical_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalInsertion_physical_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every native field and every oscillator index (i,k), physical differentiation of its normal insertion equals (k+1) times insertion of (i,k+1), plus insertion of (i,k) into the physically differentiated field. The proof differentiates the actual jetScalar factorial product. Each negative and positive summand satisfies the product law before summation; the existing separate statewise finite-support theorems justify both sum interchanges. No assumed translation, Jacobi, positive signature, rank or occupation restriction is used.

**Theorem 1.2 (Physical product law for every finite normal word).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalSequence_physical_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalSequence_physical_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite word, including empty words and repeated indices, the derivative is the finite sum over labelled deletions of (k+1) times insertion of (i,k+1) into the remaining word, plus the unchanged word acting on the differentiated base field. Linearity of the original normalInsertion is proved using the unfiltered singleton flatTerm expansion and its genuine finite support, then the original insertion commutation permutes the replacement factor. No nested normal tail order is used to bound individual flattened summands.

The complete original all-state identity is addressed by LatticeHalfFockOriginalTranslation, which joins the actual charged differentiation and Corr recurrence. This insertion product law alone does not establish differentiation of the charged creation exponential, its finite translated polynomial, the chargeScalar prefactor or its actual ground operator. Locality and this product law alone do not prove twisted Jacobi or the full moonshine, string or AdS/CFT goals.

The Reg mirror proves the full dependent coefficient-readout equivalence for the insertion theorem and records a separate full-telescope word readout obligation. Neither is a declared_validated four-slot registration: enrolled-template variation, sensitivity, observational dependence and source selection still require evidence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalInsertion_physical_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalSequence_physical_derivative`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant](LatticeHalfFockFirstDescendant.md)
