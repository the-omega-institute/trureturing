# Joint mode support of native Fock-normal coefficients

## Abstract

Joint mode support of native Fock-normal coefficients

Let D be an arbitrary finite-rank integral symmetric lattice datum with even diagonal, and let hu assert that det(D.G) is a unit. The actual tensor module is the native oscillator polynomial algebra tensored with ActualGround(D,hu). A NativeField is any HVertexOperator on this module with integer cover exponents. No field identity, word cutoff, occupation restriction or definite Gram form is assumed. Empty words, repeated axes and zero states remain included.

For a labelled jet index (i,k), jetScalar(k,m) is the product over r from 0 to k-1 of (-m-3/2-r), divided by k!. jetCurrent is this scalar times the actual half-integer tensor current at m. Each insertion shifts the field exponent by 2m+2k+3. In flatCoefficient, negative modes act on the left, while nonnegative modes act on the right in reverse word order. These are the native half-integer currents and cover-variable exponents.

**Theorem 1.1 (Same-sign tensor currents commute).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.tensor_current_same_sign`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.tensor_current_same_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any two colours and integer modes, two negative modes or two nonnegative modes commute on every actual tensor state. In either case their sum plus one is nonzero, so the actual Heisenberg commutator vanishes. Tensor induction extends the polynomial current identity to arbitrary tensors. This identity propagates a current cutoff through every nonnegative jet.

**Theorem 1.2 (Separate the left and right current actions).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every NativeField, labelled word, dependent mode tuple and integer exponent e, flatCoefficient equals leftAction times field.coeff(e+2 modeSum+jetShift) times rightAction. Here modeSum is the sum of all selected integer modes and jetShift is the sum of 2k+3 along the word. Recursive multiplication preserves both action orders; associativity and the accumulated exponent shift give the factorization. It is used to turn a vanishing middle field coefficient into a vanishing flattened term.

**Theorem 1.3 (One finite box bounds the simultaneous mode support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Fix any NativeField, word w, integer exponent e and actual tensor vector v. Let R be a natural number such that every tensor current at any colour and every integer mode m at least R annihilates v. Put L=flatLower(D,hu,field,w,v,R), J=jetShift(D,w) and n=length(w). Then support(flatTerm(D,hu,field,w,e,v)) is contained in modeBox(D,w,min(L-e-J,0)-nR,R). Both endpoints are integer expressions, with R and n cast to integers. modeBox is the product of closed integer intervals along the full dependent tuple; for an empty word it contains the unique unit tuple.

First, a nonzero term has every mode strictly below R. Nonnegative right currents preserve the original current cutoff by same-sign commutation. Replacing each negative coordinate by -1 leaves rightAction unchanged. Every surviving code therefore belongs to the finite product of intervals [-1,R]. Evaluate the actual field on all right-action states in that product and take the minimum of their Hahn orders together with zero; this is exactly flatLower.

For a surviving tuple, its right-action state occurs in that finite image, so its field order is at least L. Factorization and Hahn coefficient vanishing imply L at most e+2 modeSum+J. Thus min(L-e-J,0) is at most modeSum. Combining this coupled sum bound with the coordinate upper bounds yields the lower endpoint min(L-e-J,0)-nR for every coordinate simultaneously. The construction precedes any exchange of sums and imposes no extra truncation hypothesis on the arbitrary field.

The native twisted lattice framework follows FLM. The simultaneous mode-box estimate is a repository derivation; no literature novelty or physical realization is asserted. It supplies the support control needed for finite flattened sums and subsequent normalSequence Fubini identities. Those identities, the original native normal-word and BPZ integration, twisted Jacobi, and the larger VOA/CFT, anomaly, fusion, string and AdS/CFT constructions remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.tensor_current_same_sign`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
