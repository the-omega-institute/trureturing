# Diagonal Kraus Instrument Factorization

## Abstract

Aggregate Kraus column orthogonality characterizes classical weight evolution of diagonal inputs.

Let I and O be finite input and output coordinate types, A a setting type, B a finite readable outcome type, and R a finite Kraus type. The complex rectangular matrices K(a,b,r) have rows O and columns I. No nonempty-domain assumption is needed. The complex vector p is arbitrary; interpreting it as a probability distribution additionally requires real nonnegative entries and total mass one. Real weights are embedded in the complex numbers in the matrix formulas.

Write Phi(a,b)(rho) for MatrixMap.of_kraus (K a b) (K a b) rho, the sum of K(a,b,r) rho K(a,b,r) adjoint over r. This is an unnormalized branch. The Gram condition below concerns distinct output coordinates within each fixed input column and is imposed only after summing over r. It permits cancellations between Kraus terms; it does not require each Kraus operator to preserve diagonal matrices individually.

**Definition 1.1 (Nonnegative branch weights).**

$$\forall I,O,A,B,R: Type, [\operatorname{Fintype}\left(R\right)], \forall K: A \to B \to R \to \operatorname{Matrix}\left(O, I, \mathbb{C}\right),\\{}\forall a: A, b: B, o: O, i: I, \operatorname{W}\left(a, b, o, i\right) = \sum_{r \in R} {\operatorname{normSq}\left(\operatorname{K}\left(a, b, r, o, i\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared complex amplitudes are summed over the discarded Kraus index. The outcome b is retained, so these weights need not sum to one within a branch.

**Theorem 1.2 (Entries of a Kraus map on a diagonal input).**

$$\forall I,O,R: Type, [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(R\right)], \forall K: R \to \operatorname{Matrix}\left(O, I, \mathbb{C}\right), \forall p: I \to \mathbb{C}, \forall o,q: O, \operatorname{MatrixMap.of_{kraus}}\left(K, K, \operatorname{Matrix.diagonal}\left(p\right), o, q\right) = \sum_{i \in I} {(\sum_{r \in R} {\operatorname{K}\left(r, o, i\right) \cdot \operatorname{starRingEnd}\left(\mathbb{C}, \operatorname{K}\left(r, q, i\right)\right)}) \cdot \operatorname{p}\left(i\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_entry_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each output entry is the input-weighted sum of the corresponding Kraus column Gram coefficients.

**Theorem 1.3 (Orthogonality, factorization, and stochastic normalization).**

$$\forall I,O,A,B,R: Type, [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(O\right)] [\operatorname{DecidableEq}\left(O\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{Fintype}\left(R\right)], \forall K: A \to B \to R \to \operatorname{Matrix}\left(O, I, \mathbb{C}\right),\\{}(\forall a \in A, \sum_{b \in B} {\sum_{r \in R} {{\operatorname{K}\left(a, b, r\right)}^{*} \operatorname{K}\left(a, b, r\right)}} = \operatorname{identity}\left(I\right)) \Rightarrow\\{}(\forall a,b,o,i, 0 \leq \operatorname{W}\left(a, b, o, i\right)) \land (\forall a,i, \sum_{b \in B} {\sum_{o \in O} {\operatorname{W}\left(a, b, o, i\right)}} = 1) \land\\{}((\forall a,b,i,o,q, o \neq q \Rightarrow \sum_{r \in R} {\operatorname{K}\left(a, b, r, o, i\right) \operatorname{conj}\left(\operatorname{K}\left(a, b, r, q, i\right)\right)} = 0) \iff (\forall p: I \to \mathbb{C}, \forall a,b, \operatorname{Phi}\left(a, b, \operatorname{diag}\left(p\right)\right) = \operatorname{diag}\left(o \mapsto \sum_{i \in I} {\operatorname{W}\left(a, b, o, i\right) \operatorname{p}\left(i\right)}\right))) \land\\{}(\forall a, \exists C: \operatorname{QuantumChannel}\left(I, O\right), \forall \rho: \operatorname{Matrix}\left(I, I, \mathbb{C}\right), \operatorname{matrixAction}\left(C, \rho\right) = \sum_{b \in B} {\operatorname{Phi}\left(a, b, \rho\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_instrument_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global completeness normalizes the sum over outcomes b and output coordinates o for every setting a and input i. Matrix multiplication against a diagonal input expands each entry into a weighted sum of column Gram coefficients. Vanishing off-diagonal Gram sums remove every off-diagonal output entry. On the diagonal, the same coefficients are squared amplitudes and hence give W. Conversely, testing p equal to each coordinate basis distribution isolates every Gram coefficient.

The total map is the sum of all outcome branches. Its canonical quantum channel is supplied by finite_kraus_quantum_channel applied to the product Kraus index B times R. Complete positivity and trace preservation use that existing theorem.

For a nonnegative probability input, the branch mass is the trace of its output, equal to the sum of its output diagonal coefficients. A conditional trace-one state is obtained by dividing by this real mass only when it is strictly positive. Zero-mass branches carry no conditional-state assignment. The equivalence and normalization are the formal claims here; conditioning is their probability interpretation under the stated positivity assumptions.

This finite-dimensional result supplies a mathematical criterion for a quantum bridge. Applying it to AURIC FIB requires an independently specified Kraus family and proofs of completeness and the Gram condition. FIB coordinates, source ancestry, physical implementation, observable precision, and resource costs are additional data; none is inferred from this factorization.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_entry_expansion`
- Truth anchor: `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_instrument_factorization`
- Truth anchor: `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.weight`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
