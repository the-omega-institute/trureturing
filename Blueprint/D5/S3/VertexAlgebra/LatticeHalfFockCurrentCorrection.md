# The full charged correction commutes with source partial derivatives

## Abstract

The full charged correction commutes with source partial derivatives

LatticeData has arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degenerate and indefinite forms remain in scope. Every charge, oscillator index, finite oscillator polynomial and natural correction shift retains its original domain; there is no occupation or order cutoff.

The operator is exactly the original Corr. Its correctionWord has the original singletonPolynomial, pairPolynomial and pairDerivation; no neutral substitution or alternative correction map is used.

**Theorem 1.1 (The correction lift fixes scalar constants).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_C`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original constant lemma is public for direct reuse by correctedSource_oscillatorDerivation in CorrectionTranslation. It is consumed support, not additional mathematical content.

**Theorem 1.2 (Adding one exponent adds one labelled occurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.occurrences_cons`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.occurrences_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every lattice D, index i and finitely supported natural exponent e, the list i :: occurrences(D,e) permutes occurrences(D,e + single(i,1)). The multiset equality retains repeated occurrences. This enumeration identity supplies the monomial step of correctionLift_X_mul.

**Theorem 1.3 (Multiplication by a source variable becomes the original insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_X_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, charge a, index i and oscillator polynomial p, correctionLift(D,a)(p X_i) equals insertion(D,a,i)(correctionLift(D,a)(p)). The lift uses the monomial basis and the original correctionWord. Polynomial induction reduces multiplication to occurrence insertion, and correctionWord_permutation removes the dependence on occurrence order.

**Theorem 1.4 (Source partial derivatives commute with the polynomial correction lift).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_partial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, charge a, index i and oscillator polynomial p, partial_(some i)(correctionLift(D,a)(p)) equals correctionLift(D,a)(partial_i(p)). Ordinary source partials annihilate the singleton and pair coefficients, commute with pairDerivation, and differentiate insertion by its retained-variable term plus insertion of the derivative. Polynomial induction then gives the unrestricted lift identity.

**Theorem 1.5 (The full charged correction commutes with source partial derivatives).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source derivative at any ordinary index commutes coefficientwise through Corr for every charge, polynomial and correction shift. The proof establishes partial_pairDerivation and partial_insertion on the actual correction polynomial, retaining the charged singleton and pair constants, and then passes through optionEquivLeft.

The singleton coefficient at source weight one is the actual negative charge pairing divided by two. The pair coefficients retain pairScalar and both halfBinomial factors. They are constants for the source partial derivative, not deleted terms. Passing through optionEquivLeft and extracting each shift coefficient gives Corr_partial. The original frequency-weighted current law still requires the actual charge zero mode.

The five public identities each have a source-bound Contract.Registration with its complete original parameter and state telescope, an exact source-equivalence bridge, a lawful actual readout, a rejected whole-family intervention with variation and sensitivity, and actual observational dependence: correctionLift_C, occurrences_cons, correctionLift_X_mul, correctionLift_partial and Corr_partial. Finite roles impose no finiteness on parameters, states or outputs; whole-family variation retains zero and degenerate fibers. Each registration's unknown continuation records only the unresolved residual.

These are repository derivations of classical twisted lattice correction identities with FLM background, with no literature novelty claim. The next operator step is the original frequency-weighted Corr current identity with its charge zero mode. This unit does not establish arbitrary-ground closed scalar evaluation, native all-state BPZ integration, full twisted Jacobi, or the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_C`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_X_mul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_partial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.occurrences_cons`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
