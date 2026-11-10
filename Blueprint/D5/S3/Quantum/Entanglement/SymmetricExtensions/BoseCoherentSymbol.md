# Coherent symbols of Bose operators

## Abstract

Coherent symbols separate actual Bose-supported operators

This is the finite polynomial spanning argument used in Gulati-Nechita-Park, Theorem 8.9. It concerns actual computational tensor matrices and the repository's full symmetric projector. The GNP extension characterization is proved separately in BoseHierarchy using these coherent symbols.

**Definition 1.1 (Actual bihomogeneous entry polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each computational matrix entry multiplies the monomial with its row occupation in the first variable family and its column occupation in the second. Repeated occupations are summed with their actual multiplicities, without any normalization.

**Theorem 1.2 (Evaluation is the actual coherent quadratic form).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting conjugate z in the first family and z in the second gives exactly the quadratic form of the actual repeated tensor vector. This identity requires no support or positivity hypothesis.

**Theorem 1.3 (Coherent evaluations separate Bose operators).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tensor length and local dimension, a Hermitian matrix supported by the full symmetric-projector sandwich is zero if all its coherent quadratic forms vanish. An invertible Cartesian substitution and polynomial uniqueness prove vanishing of the independent-coordinate polynomial. The existing occupation-orbit theorem then identifies each coefficient with a matrix entry times two strictly positive occupation multiplicities. Empty and zero-dimensional boundaries are retained.

## Application: nonnegative occupation weights

For arbitrary natural numbers r and n, a positive semidefinite matrix E on words Fin r to Fin n, and every occupation a : Sym (Fin n) r, put w=representative a.val a.property. The occupation coefficient is the real natural multiplicity of a times the real part of E(w,w). Matrix.PosSemidef.diag_nonneg gives the complex-order inequality 0 <= E(w,w); the first component of Complex.nonneg_iff gives 0 <= real(E(w,w)). Nat.cast_nonneg and mul_nonneg then give a nonnegative occupation coefficient.

Expanding the actual occupation twirl entrywise from hE.isHermitian and full Bose support gives the actual finite sum of these nonnegative coefficients times the normalized occupation projectors vecMulVec (sectorVector r a.val) (star (sectorVector r a.val)). The equality itself holds for every Hermitian Bose-supported E with signed coefficients. This positivity application retains zero coefficients, zero and singular operators, r=0, n=0 whenever the stated data exist, n=1 and r=2; it imposes neither trace one nor a coefficient-sum normalization.

**Theorem 1.4 (Complex coherent form at every cut).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.partialTranspose_coherent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.partialTranspose_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual product-basis partial transpose acts on a coherent form by conjugating precisely the local vector entries at the selected sites. Empty and full cuts are retained.

**Theorem 1.5 (Rank-one cut amplitude).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.rankOne_partialTranspose_coherent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.rankOne_partialTranspose_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coherent form of a partially transposed rank-one PSD tensor is exactly the squared modulus of its cut amplitude.

**Definition 1.6 (Actual real coherent polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial sums the real parts of the original matrix entries with their total row and column occupations.

**Theorem 1.7 (PSD tensors give native SOS forms).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_posSemidef_sos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_posSemidef_sos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factoring the actual PSD matrix writes its real coherent polynomial as a finite sum of real and imaginary amplitude squares. The SOS predicate is the ordinary native real polynomial predicate.

**Theorem 1.8 (Exact real coherent evaluation).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_realSymbol`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_realSymbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real local vector evaluates the polynomial to the real part of the actual repeated-tensor quadratic form.

**Theorem 1.9 (Cut-invariant real polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_partialTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_partialTranspose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every product-basis partial transpose has the identical real coherent polynomial, for every cut.

**Theorem 1.10 (Closed native SOS preimage).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_sos_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_sos_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of Hermitian tensors whose actual real coherent polynomial is a native SOS is closed. The proof consumes the genuine homogeneous SOS coefficient-cone closedness; it does not remove closure from the DPS dual-sum identity.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_realSymbol`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.partialTranspose_coherent`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.rankOne_partialTranspose_coherent`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_posSemidef_sos`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.realSymbol_sos_closed`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol`
- Dependency: [D5/S3/QuadraticForms/HomogeneousSOSGram](../../../QuadraticForms/HomogeneousSOSGram.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT](../AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS](BoseDPS.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl](BoseOccupationTwirl.md)
