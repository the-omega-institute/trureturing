# Finite Twisted Correction

## Abstract

Finite singleton and pair correction on the full ordinary lattice oscillator algebra.

The source weight of (i,k) is k+1, not the native half-Fock weight 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.

**Theorem 1.1 (Symmetric differential insertions commute).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each insertion is multiplication by the retained variable plus its singleton correction, followed by the pair derivation. Pair derivations kill the shift variable and every singleton and pair coefficient. Their commutator vanishes on every polynomial generator; the mixed multiplication commutators cancel by Gram and pair-coefficient symmetry.

**Theorem 1.2 (Occurrence order does not change the correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The insertion algorithm terminates by word length. Adjacent swaps use the actual commuting insertions, and transitivity gives every occurrence permutation. Repeated variables remain separate list occurrences; differentiation supplies their multiplicities. The existing monomial basis extends the construction linearly to every finite oscillator polynomial.

**Theorem 1.3 (Every monomial enumeration gives the same finite correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual monomial-basis correction agrees with every permutation of its source occurrences, using the insertion commutation proof rather than a chosen enumeration as a premise. This is the finite coefficient family Corr consumed by correctedPolynomial and Ytw. The insertion of two occurrences expands into the full retained-plus-singleton product plus its pair derivative, including singleton-singleton contributions and repeated variables.

**Theorem 1.4 (Differentiation contracts one labelled occurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

labelledRemainders traverses positions recursively. Each entry retains every occurrence except the selected one, including other occurrences of the same variable. The derivation of an arbitrary correction word is the finite sum of its pair coefficient times the correction of each such remainder. The proof commutes the pair derivation through an insertion and inducts on the actual source word.

**Theorem 1.5 (Every word obeys the singleton and labelled-pair recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The active occurrence is either retained, removed as a singleton, or paired with exactly one labelled remaining occurrence. Recursive remainders shorten the word. Two occurrences therefore include retained factors, each singleton, the singleton-singleton term and the pair term, without erasing all equal variables.

**Theorem 1.6 (Word corrections never exceed the ordinary source weight).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Strong induction on occurrence count bounds the degree of the actual shift polynomial. A singleton spends the active source weight. A pair spends both removed weights, while the remainder has exactly the complementary weight. The bound applies without positivity, a charge norm bound or a rank hypothesis.

**Theorem 1.7 (The empty oscillator state has no correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The monomial basis sends the empty word to the unit at shift zero. This evaluation is consumed by exact charged-state recovery and is not counted as new mathematical content.

**Theorem 1.8 (A neutral single oscillator is unchanged).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_X_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_X_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

There is no pair partner and the charge pairing is zero. The actual correction is the same oscillator at shift zero. This evaluation is consumed by current recovery and has no new-content credit.

**Theorem 1.9 (Every supported shift of an arbitrary polynomial is bounded).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The unrestricted polynomial expands over its actual finite monomial support. Scalar multiplication cannot increase shift degree; every supported monomial weight is bounded by the ordinary weighted total degree. The resulting Corr support bound is consumed by the actual all-state lower-truncation estimate.

These are derived classical twisted-lattice corrections, not a literature-novelty claim or a twisted-Jacobi proof. The actual native-field constructor consumes Corr. Physical translation compatibility remains a separate obligation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_X_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_one`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
