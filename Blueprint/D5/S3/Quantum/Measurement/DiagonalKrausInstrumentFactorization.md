# Diagonal Kraus Instrument Factorization

## Abstract

Aggregate Kraus column orthogonality characterizes classical weight evolution of diagonal inputs.

Let I and O be finite input and output coordinate types, A a setting type, B a finite readable outcome type, and R a finite Kraus type. The complex rectangular matrices K(a,b,r) have rows O and columns I. No nonempty-domain assumption is needed. The complex vector p is arbitrary; interpreting it as a probability distribution additionally requires real nonnegative entries and total mass one. Real weights are embedded in the complex numbers in the matrix formulas.

Write Phi(a,b)(rho) for MatrixMap.of_kraus (K a b) (K a b) rho, the sum of K(a,b,r) rho K(a,b,r) adjoint over r. This is an unnormalized branch. The Gram condition below concerns distinct output coordinates within each fixed input column and is imposed only after summing over r. It permits cancellations between Kraus terms; it does not require each Kraus operator to preserve diagonal matrices individually.

**Definition 1.1 (Nonnegative branch weights).**

$$\forall I,O,A,B,R: Type, [\operatorname{Fintype}(R)], \forall K: A \to B \to R \to \operatorname{Matrix}(O, I, \mathbb{C}),\\{}\forall a: A, b: B, o: O, i: I, \operatorname{W}(a, b, o, i) = \sum_{r \in R} {\operatorname{normSq}(\operatorname{K}(a, b, r, o, i))}$$

*Formalization.* `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared complex amplitudes are summed over the discarded Kraus index. The outcome b is retained, so these weights need not sum to one within a branch.

**Theorem 1.2 (Orthogonality, factorization, and stochastic normalization).**

$$\forall I,O,A,B,R: Type, [\operatorname{Fintype}(I)] [\operatorname{DecidableEq}(I)] [\operatorname{Fintype}(O)] [\operatorname{DecidableEq}(O)] [\operatorname{Fintype}(B)] [\operatorname{Fintype}(R)], \forall K: A \to B \to R \to \operatorname{Matrix}(O, I, \mathbb{C}),\\{}{\forall a \in A, \sum_{b \in B} {\sum_{r \in R} {{\operatorname{K}(a, b, r)}^{*} \operatorname{K}(a, b, r)}} = \operatorname{identity}(I)} \Rightarrow\\{}{\forall a,b,o,i, 0 \leq \operatorname{W}(a, b, o, i)} \land {\forall a,i, \sum_{b \in B} {\sum_{o \in O} {\operatorname{W}(a, b, o, i)}} = 1} \land\\{}{{\forall a,b,i,o,q, o \neq q \Rightarrow \sum_{r \in R} {\operatorname{K}(a, b, r, o, i) \operatorname{conj}(\operatorname{K}(a, b, r, q, i))} = 0} \iff {\forall p: I \to \mathbb{C}, \forall a,b, \operatorname{Phi}(a, b, \operatorname{diag}(p)) = \operatorname{diag}(o \mapsto \sum_{i \in I} {\operatorname{W}(a, b, o, i) \operatorname{p}(i)})}} \land\\{}{\forall a, \exists C: \operatorname{QuantumChannel}(I, O), \forall \rho: \operatorname{Matrix}(I, I, \mathbb{C}), \operatorname{matrixAction}(C, \rho) = \sum_{b \in B} {\operatorname{Phi}(a, b, \rho)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_instrument_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global completeness normalizes the sum over outcomes b and output coordinates o for every setting a and input i. Matrix multiplication against a diagonal input expands each entry into a weighted sum of column Gram coefficients. Vanishing off-diagonal Gram sums remove every off-diagonal output entry. On the diagonal, the same coefficients are squared amplitudes and hence give W. Conversely, testing p equal to each coordinate basis distribution isolates every Gram coefficient.

The total map is the sum of all outcome branches. Its canonical quantum channel is supplied by finite_kraus_quantum_channel applied to the product Kraus index B times R. Complete positivity and trace preservation use that existing theorem.

For a nonnegative probability input, the branch mass is the trace of its output, equal to the sum of its output diagonal coefficients. A conditional trace-one state is obtained by dividing by this real mass only when it is strictly positive. Zero-mass branches carry no conditional-state assignment. The equivalence and normalization are the formal claims here; conditioning is their probability interpretation under the stated positivity assumptions.

This finite-dimensional result supplies a mathematical criterion for a quantum bridge. Applying it to AURIC FIB requires an independently specified Kraus family and proofs of completeness and the Gram condition. FIB coordinates, source ancestry, physical implementation, observable precision, and resource costs are additional data; none is inferred from this factorization.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.diagonal_instrument_factorization`
- Truth anchor: `D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.weight`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
