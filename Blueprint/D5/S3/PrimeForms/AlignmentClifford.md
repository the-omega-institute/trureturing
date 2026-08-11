# The Generalized-Flow Identity of the Alignment Matrix

## Abstract

Every matrix on the alignment hyperplane sandwiches K to a determinant-scaled copy of K.

**Theorem 1.1 (Generalized-flow identity on the alignment hyperplane).**

$$K = \begin{pmatrix}1&-2\\2&-1\end{pmatrix}, K^2 = -3 I,\\\forall \beta \in V, \beta K \beta = (\operatorname{det} \beta) K$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/AlignmentClifford.generalized_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alignment matrix K = [[1,-2],[2,-1]] is an integer 2x2 matrix that squares to -3 times the identity, so it behaves as a square root of -3. Its alignment hyperplane is V = { X : tr(X K) = 0 }, the integer matrices X whose trace against K vanishes.

The generalized-flow identity states that every matrix on this hyperplane rescales K by its determinant: for all beta in V, beta K beta = (det beta) K. The identity holds for every beta on the hyperplane, with no unimodularity assumption; the unimodular case det beta = +-1, where beta sends K to +-K, is a special case. Moreover the hyperplane is closed under the sandwich map: if beta and gamma lie in V then so does beta gamma beta.

The flow identity is proved by reading off the single hyperplane constraint and applying it to each of the four entries of beta K beta - (det beta) K; closure is a trace-cyclicity corollary. Only these three clauses — the square identity, the generalized flow, and closure — are recorded here. The unimodular acts-by-plus-or-minus-one reading, the flow / self-insertion / even-texture unification, the paired-and-zero census certificate, and the phase-charge parity interpretation of the wider result are not covered by this statement.

## References

- Truth anchor: `D5/S3/PrimeForms/AlignmentClifford.generalized_flow`
