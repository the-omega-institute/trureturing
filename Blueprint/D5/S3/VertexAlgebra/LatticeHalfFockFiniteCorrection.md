# Finite Twisted Correction

## Abstract

Finite singleton and pair correction on the full ordinary lattice oscillator algebra.

LatticeData consists of an arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degeneracy and indefinite forms are allowed. The source weight of (i,k) is k+1; the native half-Fock weight is 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.

**Theorem 1.1 (The original half-binomial successor coefficient).**

$$\forall d\in \mathbb{N}, \operatorname{halfBinomial}\left(d+1\right)=\frac{(\frac{-1}{2}-d)\operatorname{halfBinomial}\left(d\right)}{d+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.half_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every natural d, halfBinomial(d+1) = ((-1/2-d) halfBinomial(d))/(d+1), over Complex. This factorial-product recurrence supplies the weighted binomial transform and the two-coordinate pair recurrence.

**Theorem 1.2 (Independent all-order reflection of the original pair coefficient).**

$$\forall m,n\in \mathbb{N}, \operatorname{pairScalar}\left(m+1, n+1\right)=\sum_{r=0}^{m} \sum_{s=0}^{n} ((-1)^{m+1}\operatorname{choose}\left(m+1, r+1\right))((-1)^{n+1}\operatorname{choose}\left(n+1, s+1\right))\operatorname{pairScalar}\left(r+1, s+1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairScalar_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every pair of natural orders m,n, pairScalar(m+1,n+1) is the sum over 0 <= r <= m and 0 <= s <= n of ((-1)^(m+1) choose(m+1,r+1)) ((-1)^(n+1) choose(n+1,s+1)) pairScalar(r+1,s+1). Both orders are independent and unbounded. The coefficients are exactly the original jetReflectionScalar coefficients. The definitions halfBinomial(d) = product over 0 <= j < d of (-1/2-j), divided by d!, and pairScalar(k,l) = k l halfBinomial(k) halfBinomial(l)/(k+l) are unchanged.

The finite binomial transform obeys an all-order inductive identity: its signed transform equals the original pairScalar, with zero auxiliary axis values. The proof derives a finite two-coordinate recurrence and identifies its unique solution by induction, using the positive cast of the sum of the two source weights. It assumes no covariance premise, rank, signature, occupation cutoff, determinant or lattice data.

In the actual pairPolynomial, the Gram entry stays unchanged. A reduced pair of orders r,s needs the extra shift power (m-r)+(n-s) to recover the original total source weight m+n+2. This scalar theorem alone does not prove correctionWord covariance or native all-state BPZ; labelled remainders, singleton contributions, and the operator transpose law remain required.

**Theorem 1.3 (Pair derivations annihilate every shift power).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every LatticeData, oscillator index and natural degree, pairDerivation sends X(none) raised to that degree to zero. The shift coordinate has derivative zero. This identity supplies the shift-generator case of commutation on arbitrary correction polynomials.

**Theorem 1.4 (Pair derivations annihilate every pair coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every LatticeData and every three oscillator indices, pairDerivation annihilates pairPolynomial. Its scalar coefficient is constant and its polynomial factor is a shift power. This identity supplies generator commutation and permits pair coefficients to pass through insertions.

**Theorem 1.5 (Symmetric differential insertions commute).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each insertion is the sum of multiplication by the retained variable plus its singleton correction and the pair derivation. Pair derivations kill the shift variable and every singleton and pair coefficient. Their commutator vanishes on every polynomial generator; the mixed multiplication commutators cancel by Gram and pair-coefficient symmetry.

**Theorem 1.6 (Occurrence order does not change the correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The insertion algorithm terminates by word length. Adjacent swaps use the actual commuting insertions, and transitivity gives every occurrence permutation. Repeated variables remain separate list occurrences; differentiation supplies their multiplicities. The existing monomial basis extends the construction linearly to every finite oscillator polynomial.

**Theorem 1.7 (Every monomial enumeration gives the same finite correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every word whose occurrences permute the canonical list, the monomial-basis correction equals its word correction. The proof uses insertion commutation to compare these enumerations. Corr records this finite coefficient family as a linear map on the original oscillator algebra. The insertion of two occurrences expands into the full retained-plus-singleton product plus its pair derivative, including singleton-singleton contributions and repeated variables.

**Theorem 1.8 (Differentiation contracts one labelled occurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

labelledRemainders traverses positions recursively. Each entry retains every occurrence except the selected one, including other occurrences of the same variable. The derivation of an arbitrary correction word is the finite sum of its pair coefficient times the correction of each such remainder. The proof commutes the pair derivation through an insertion and inducts on the actual source word.

**Theorem 1.9 (Every word obeys the singleton and labelled-pair recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The active occurrence is either retained, removed as a singleton, or paired with exactly one labelled remaining occurrence. Recursive remainders shorten the word. Two occurrences therefore include retained factors, each singleton, the singleton-singleton term and the pair term, without erasing all equal variables.

**Theorem 1.10 (Word corrections never exceed the ordinary source weight).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Strong induction on occurrence count bounds the degree of the actual shift polynomial. A singleton spends the active source weight. A pair spends both removed weights, while the remainder has exactly the complementary weight. The bound applies without positivity, a charge norm bound or a rank hypothesis.

**Theorem 1.11 (Every supported shift of an arbitrary polynomial is bounded).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The unrestricted polynomial expands over its actual finite monomial support. Scalar multiplication cannot increase shift degree; every supported monomial weight is bounded by the ordinary weighted total degree. The bound holds for the actual support of Corr, with no cutoff on the polynomial or the shift index.

These are derived classical twisted-lattice corrections, not a literature-novelty claim or a twisted-Jacobi proof. Native-field translation compatibility and arbitrary-word transpose remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.Corr_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_matching`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_permutation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.correctionWord_shift_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.half_successor`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.insertion_commute`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_matching`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_pair`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairDerivation_shift`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.pairScalar_reflection`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
